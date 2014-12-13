/**************************************************************************
 * @author Mahdi Eslamimehr
 * @version 0.1
 ***************************************************************************/

package ContractGen;
import java.util.HashMap;
import java.util.HashSet;
import java.io.File;
import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.FileReader;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.ArrayList;
import java.util.Iterator;

import soot.Scene;
import soot.PointsToSet;
import soot.Body;
import soot.Local;
import soot.SootMethod;
import soot.SootClass;
import soot.EntryPoints;
import soot.jimple.spark.SparkTransformer;
import soot.jimple.toolkits.annotation.purity.DirectedCallGraph;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.ExceptionalUnitGraph;


public class Analyzer {
    public MultiMap Globals;
    public String LibClassesFile;
    public HashMap LockGraphs;
    public String PackageName = "";
    public SootClass LibraryClass;
    public HashSet MethodStack;

    /****************************************************
     * Initializes data structures required for analysis.
     ***************************************************/
    public Analyzer(String fileName, String dirName) {
        LibClassesFile = fileName;
        outputDir      = dirName;
        Globals = new MultiMap();
        LockGraphs = new HashMap();
        LibClasses = new HashSet();
        MethodStack = new HashSet();
        processClassesFile();
    }

    public void doAnalysis() {
        LockGraph.populateFilterList();
        for (Iterator cit = LibClasses.iterator(); cit.hasNext(); ) {
            SootClass C = (SootClass) cit.next();
            E.pn("####################################################");
            E.pn(" Starting Analysis for Class ["+C+"]");
            E.pn("----------------------------------------------------");
            E.pn("(--- alias analysis ");
            PointerAnalysis(C);
            E.pn(" --- alias analysis)");
            E.pn("----------------------------------------------------");
            E.pn("(--- lockgraph creation ");
            GenerateLockGraphs();
            E.pn(" --- lockgraph creation)");
            E.pn("----------------------------------------------------");
            E.pn("(--- contract generation");
            GenerateContracts();
            E.pn(" --- contract generation)");
            E.pn("----------------------------------------------------");
            E.pn(" Finished Analysis for Class ["+C+"]");
            E.pn("####################################################");
        }
    }


    /******************************************************
     * This function performs SPARK-based pointer analysis.
     *****************************************************/
    public void PointerAnalysis (SootClass main) {
        Scene.v().setMainClass(main);
        LibraryClass = main;
        Scene.v().loadNecessaryClasses();
        Scene.v().setEntryPoints(EntryPoints.v().all());
        sparkPointerAnalysis();
        E.info("[spark] Done!");
    }

    /************************************************************************
     * This function computes the fix-point-based computation of lock-graphs
     ***********************************************************************/
    /**
      A corner case for when the LG is in cache.
      Consider this sequence:
      x1.f() -> x2.f() -> x3.f() -> ....
      Suppose x is different every time, then the fix-point computation will never
      converge! E.g. If we have something like:
      while (x.parent!=null) {
         x.f();
         x = x.parent;
      }

      Now WE know that this loop would terminate after as many iterations as number
      of nodes in the d.s. for which x is an iterator, but the analysis won't know
      that! It will keep recomputing and generating new lock-graphs with different
      'bases'. Hence, we fix a recursion-depth of MAX_RECUR_DEPTH. If the same 
      method is invoked on different bases more than MAX_RECUR_DEPTH times in the
      course of analyzing a single method, then we return an empty lock graph for
      that method. This might seem unsound for deadlock, but will not be as long as 
      the underlying data structure is acyclic. The empty lock graph helps break the
      cycle. 
    **/
    /*****************************************************
     * Fix-point Algorithm:
     * 
     * worklist += Library.allMethods
     *  
     * while (worklist != empty) { 
     *     M = worklist.first
     *     CLG ("", M, "");
     * }
     *
     * CLG(b, M, C) {
     *     M.callers += C;
     *     if (#calls of b.M from C > MAX_RECUR_DEPTH) 
     *          return empty;
     *     if (b.M on stack) 
     *          return empty; 
     *     push b.M on stack
     *     inc #calls of b.M from C
     *     if (l = cached(M)) return l;
     *     l' = compute(M) {
     *          if (M calls b1.S) {
     *                  CLG(b1, S, M);
     *          }
     *     }
     *     clear #calls map
     *     if (l = cached(M)) {
     *         if (l' = l) {
     *             cache(M')
     *             return l;
     *         } else {
     *             worklist += M.callers
     *             return l;
     *         }
     *     }
     *     pop b.M off stack
     * }     
     *****************************************************/
    // Maps method to its callers
    private MultiMap Callers = new MultiMap();
    // Maps (base, method) to the #calls from caller
    private HashMap  ContextCallers = new HashMap();
    // Stack of methods being currently computed
    private HashSet  ContextComputeStack = new HashSet();
    private ArrayList worklist = new ArrayList();
    public void GenerateLockGraphs() {
        for (Iterator mIt = LibraryClass.methodIterator(); mIt.hasNext(); ) {
            SootMethod m = (SootMethod) mIt.next();
            worklist.add(m);
        }

        while (!worklist.isEmpty()) {
            SootMethod m = (SootMethod) worklist.get(0);
            worklist.remove(0);
            ComputeMethodLockGraph(m,"", null);
        }
    }

    /********************************************************************
     * This function analyzes a given method and computes its lock-graph.
     *******************************************************************/
    private boolean tooManyCalls(String s) {
        if (!ContextCallers.containsKey(s)) return false;
        Integer I = (Integer) ContextCallers.get(s);
        return (I.intValue() > MAX_RECUR_DEPTH);
    }

    private void incrementCallCount(String s) {
        Integer I = Integer.valueOf(0);
        if (!ContextCallers.containsKey(s)) ContextCallers.put(s, I);
        I = (Integer) ContextCallers.get(s);
        ContextCallers.put(s, Integer.valueOf(I.intValue()+1));
    }

    private void clearContextCallers(String x) {
        for (Iterator it = ContextCallers.keySet().iterator(); it.hasNext(); ) {
            String key = (String) it.next();
            if (key.endsWith(x)) it.remove();
        }
    }

    private HashMap TimesComputed = new HashMap();
    public LockGraph ComputeMethodLockGraph(SootMethod m, String base, SootMethod caller) {
        announce(m, base, caller, true);
        String contextCallString = base+"."+m.getSignature();
        String fullCallString = null;
        if (caller!=null) {
            fullCallString = contextCallString+"<-"+caller.getSignature();
            if (tooManyCalls(fullCallString)) {
                if (verbose) E.warn ("Possible infinite loop in method "+caller+" that calls method "+m);
                announce (m, base, caller, false);
                return LockGraph.emptyLockGraph();
            }
        }
        if (ContextComputeStack.contains(contextCallString)) {
            if (verbose) E.warn ("Possible infinite loop in method "+m+", analyzing same context again.");
            announce (m, base, caller, false);
            return LockGraph.emptyLockGraph();
        }
        if (TimesComputed.containsKey(m)) {
            if (((Integer) TimesComputed.get(m)).intValue() > 2) {
                if (verbose) E.warn ("Possible recursive call sequence in method "+m+
                            ((caller==null)?"":","+caller));
                LockGraph lg = getLockGraphFromCache(m);
                announce (m, base, caller, false);
                if (lg != null) return lg;
                else            return LockGraph.emptyLockGraph();
            }
        }
        ContextComputeStack.add(contextCallString);
        if (caller!=null) {
            incrementCallCount(fullCallString);
            Callers.put(m.getSignature(),caller);
        }
        Integer C = Integer.valueOf(0);
        if (TimesComputed.containsKey(m)) {
            int c = ((Integer) TimesComputed.get(m)).intValue()+1;
            C = Integer.valueOf(c);
        }
        TimesComputed.put(m,C);
        LockGraph ret = clg(m,base);
        putLockGraphInCache(m, ret);
        ContextComputeStack.remove(contextCallString);
        announce(m, base, caller,false);
        return ret;
    }


    private void announce(SootMethod m, String base, SootMethod caller, boolean inout) {
        if (verbose) { 
            String s1 = "++++++++++ ComputeLG "+(inout?"start":"finis")+" "+m.getSignature()+" ++++\n";
            String s2 = ((caller!=null)?("+++        Called from "+caller):"");;
            s2 += (base.equals("")?"":("\n+++        Executed on "+base));
            E.pn(inout?("\n(\n"+s1+s2+"\n"):("\n"+s2+"\n"+s1+")\n"));
        }
    }

    private static int count = 0;
    private HashSet recompute = new HashSet();
    private LockGraph clg(SootMethod m, String base) {
        LockGraph lg = LockGraph.emptyLockGraph();
        if (!recompute.contains(m)) {
            lg = getLockGraphFromCache(m);
            if (lg!=null) {
                if (verbose) { E.debug("CACHED Lock Graph for "+m+" = "); lg.printCompact(); }
                return lg;
            } 
        }
        lg = LockGraph.emptyLockGraph();
        if (!m.isConcrete()) {
            E.warn("Skipping analysis for method: "+m+" (non-concrete method)");
            return lg;
        }
        SootClass C = m.getDeclaringClass();
        //if (C.getName().startsWith("sun") && isDontSkip(C.getName())) 
        if (!isDontSkip(C.getName())) {
            E.warn("Skipping analysis of method: "+m+" (declaring class was: "+C+")!");
            return lg;
        }
        if (verbose) E.info("Computing LockGraph for method: "+m);
        ExceptionalUnitGraph uga = new ExceptionalUnitGraph(m.retrieveActiveBody());
        lg = (new CreateLockGraph(this, uga, m, LibraryClass)).answer();
        if (!lg.emptyLockSet()) E.warn("In ["+m+"], lock-set not empty, force-emptying");
        recompute.remove(m);
        // Liberate all those whom I (m) was calling
        clearContextCallers(m.getSignature());
        LockGraph existingLG = getLockGraphFromCache(m);
        if (!((existingLG==null) || lg.equals(existingLG))) {
            HashSet cs = Callers.get(m.getSignature());
            if (cs!=null) {
                E.debug("Lock Graph for "+m+" changed! Re-computing Lock Graphs for callers : "+cs);
                Iterator c = cs.iterator();
                while(c.hasNext()) {
                    SootMethod cM = (SootMethod) c.next();
                    worklist.add(0, cM);
                    recompute.add(cM);
                }
            }
        }
        else if (verbose) { E.debug("COMPUTED Lock Graph for "+m+" = "); lg.printCompact(); }
        assert (lg!=null);
        return lg;
    }

    /****************************************************************
     * This function uses computed lock-graphs and global bindings to 
     * generate contracts for each method in the given library.  
     ***************************************************************/
    public void GenerateContracts() {
        new GenerateContracts(this, outputDir);
    }

    /********************
     * PRIVATE FUNCTIONS
     *******************/
    private HashSet LibClasses;
    private boolean verbose = E.isOpt("verboseAnalysis", "true");
    private boolean sanity  = E.isOpt("sanity", "true");
    private static int MAX_RECUR_DEPTH = 3;
    private DirectedCallGraph dg;
    private HashSet helperClasses = new HashSet(); 
    private boolean extraInitMethods;
    private String outputDir;
    private HashSet dontSkips = new HashSet();

    private void makeAllMethodsReachable(SootClass c) {
        HashSet ret = new HashSet(c.getMethods());
        Scene.v().addReachables(ret);
    }

    public void addUnskippable(String prefix) {
        dontSkips.add(prefix);
    }
    private SootClass loadClass(String qualifiedName) {
        if (verbose) E.info("Loading class: "+qualifiedName);
        dontSkips.add(qualifiedName);
        try { return Scene.v().loadClassAndSupport(qualifiedName); }
        catch (RuntimeException e) { E.crit(e.toString()); }
        return null;
    }

    private void processClassesFile() {
        if (LibClassesFile==null) return;
        try { 
            BufferedReader in = new BufferedReader(new FileReader(LibClassesFile));
            String line = null;
            for (int counter=0; (line = in.readLine())!=null; counter++ ) {
                line = line.trim(); String cName = null;
                if (Pattern.compile("^$").matcher(line).matches()) continue;
                Matcher m = Pattern.compile("^(\\S+)$").matcher(line);
                if (m.matches()) {
                    cName = m.group(1);
                    Matcher m1 = Pattern.compile("^(\\S+)\\.class$").matcher(cName); 
                    if (m1.matches()) cName = m1.group(1);
                    if (verbose) E.info("Loading class: "+cName);
                    SootClass c = loadClass(cName); 
                    LibClasses.add(c); 
                    makeAllMethodsReachable(c);
                }
            }
        } catch (FileNotFoundException f) { 
            E.FileNotFound(" "); 
        } catch (IOException e) { 
            E.crit(e.getMessage()); 
        }
        if (!dontSkips.isEmpty()) Scene.v().addJavaExcludes(dontSkips);
    }

    private void sparkPointerAnalysis() {
        HashMap sparkOpt = new HashMap();
        if (verbose) E.pn("[spark] Starting analysis ...");
        sparkOpt.put("enabled","true");
        sparkOpt.put("bdd", "true");
        sparkOpt.put("verbose","false");
        sparkOpt.put("ignore-types","false");
        sparkOpt.put("force-gc","false");            
        sparkOpt.put("pre-jimplify","false");          
        sparkOpt.put("vta","false");                   
        sparkOpt.put("rta","false");                   
        sparkOpt.put("field-based","false");           
        sparkOpt.put("types-for-sites","false");        
        sparkOpt.put("merge-stringbuffer","true");   
        sparkOpt.put("string-constants","false");     
        sparkOpt.put("simulate-natives","true");      
        sparkOpt.put("simple-edges-bidirectional","false");
        sparkOpt.put("on-fly-cg","true");            
        sparkOpt.put("simplify-offline","false");    
        sparkOpt.put("simplify-sccs","false");        
        sparkOpt.put("ignore-types-for-sccs","false");
        sparkOpt.put("propagator","worklist");
        sparkOpt.put("set-impl","double");
        sparkOpt.put("double-set-old","hybrid");         
        sparkOpt.put("double-set-new","hybrid");
        sparkOpt.put("dump-html","false");           
        sparkOpt.put("dump-pag","false");             
        sparkOpt.put("dump-solution","false");        
        sparkOpt.put("topo-sort","false");           
        sparkOpt.put("dump-types","false");             
        sparkOpt.put("class-method-var","false");     
        sparkOpt.put("dump-answer","false");          
        sparkOpt.put("add-tags","false");             
        sparkOpt.put("set-mass","false"); 		
        SparkTransformer.v().transform("",sparkOpt);
    }
    /*
       private static void paddlePointsToAnalysis() {
       System.out.println("[paddle] Starting pointer analysis with Paddle.");
       HashMap opt = new HashMap();
       opt.put("enabled","true");
       opt.put("verbose","false");
       opt.put("context-counts", "false");
       opt.put("bdd","true");
       opt.put("backend","cudd");
       opt.put("context","1cfa");
       opt.put("context-heap", "true");
       opt.put("propagator","auto");
       opt.put("conf","ofcg");
       opt.put("order","31");
       opt.put("q","auto");
       opt.put("set-impl","double");
       opt.put("double-set-old","hybrid");
       opt.put("double-set-new","hybrid");
       opt.put("pre-jimplify","false");
       PaddleTransformer pt = new PaddleTransformer();
       PaddleOptions paddle_opt = new PaddleOptions(opt);
       E.debug("Paddle Setup started.");
       pt.setup(paddle_opt);
       E.debug("Paddle Setup completed.");
       pt.solve(paddle_opt);
       E.debug("Paddle Solving completed.");
       soot.jimple.paddle.Results.v().makeStandardSootResults();
       E.pn("[paddle] Paddle Done!");
       }
       */
    public LockGraph getLockGraphFromCache(SootMethod m) {
        if (LockGraphs.containsKey(m.getSignature())) {
            LockGraph l = (LockGraph) LockGraphs.get(m.getSignature());
            if (!l.isEmpty()) {
                LockGraph lcopy = new LockGraph(l);
                if (verbose) {
                    E.pn("Found Lock Graph for Method: "+m.getSignature()+" in cache =");
                    l.printCompact();
                    // E.pn("copied and returning: ");
                    // lcopy.printCompact();
                }
                return lcopy;
            }
            return l;
        }
        return null;
    }
    public void removeLockGraphFromCache(SootMethod m) {
        LockGraphs.remove(m.getSignature());
    }
    public void putLockGraphInCache(SootMethod m, LockGraph l) {
        if (l==null) {
            E.error("Trying to cache null LockGraph in method "+m);
            return;
        }
        LockGraph putIn = new LockGraph(l);
        if (sanity) {
            E.pn("Putting Lock Graph in cache for method = "+m.getSignature());
            l.printCompact();
        }
        LockGraphs.put(m.getSignature(), putIn);
    }
    private boolean isDontSkip (String c) {
        for (Iterator it = dontSkips.iterator(); it.hasNext(); ) {
            String prefix = (String) it.next();
            if (c.startsWith(prefix)) return true;
        }
        return false;
    }
    public void PrintStats() {
        E.pn("++++++++++++++++++++++++++++++++++++++++++++++++++++++");
        E.pn("Contract Generation:");
        E.pn("Number of combinations considered: "+GenerateContracts.numCombos);
        E.pn("Number of combinations skipped: "+GenerateContracts.numAstro);
        E.pn("Number of constraints generated: "+GenerateContracts.totalWritten);
        E.pn("++++++++++++++++++++++++++++++++++++++++++++++++++++++");
    }
}
