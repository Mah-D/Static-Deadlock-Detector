/**************************************************************************
 * @author Mahdi Eslamimehr
 * @version 0.1
 ***************************************************************************/

package ContractGen;
import java.util.Iterator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;
import java.util.Stack;
import java.util.ArrayList;
import java.io.PrintStream;
import soot.Scene;
import soot.Local;
import soot.Value;
import soot.SootMethod;
import soot.jimple.ThisRef;
import soot.jimple.ParameterRef;
import java.util.Map;

/************************************
 * LockGraph for a given method M. 
 ************************************/

public class LockGraph {
    /* The this parameter and formal parameters for M */
    /* Golden rule: This/Parameters are immutable, though not marked
     * as such. No one should modify these explicitly!! */
    public Synonym This;
    public HashMap Parameters;

    /* LockGraph LG = (E, N, H, LS) */
    private MultiMap edges;            /* E = set of edges */
    private HashSet heads;             /* H = set of heads */
    private HashSet LS;                /* LS = current lock set */
    private HashSet notifyList;        /* N = current 'embedded' notifies */
    private HashSet rets;              /* rets = Return values */

    /* Witness for cycle within the graph */
    private ArrayList witness = null;
    private boolean debug = true;

    /* Tracker stuff */
    private MultiMap Tracker;
    private MultiMap EdgeTracker;

    /* Stuff for Tarjan's algorithm */
    private Stack stack;
    private ArrayList cycles;

    /* Verbosity flags */
    private boolean verboseLG = E.isOpt("verboseLG", "true");
    private boolean verboseLGSub = E.isOpt("verboseLGSub", "true");

    /************************* PUBLIC FUNCTIONS *********************************/
    /* Constructor for LockGraph */
    // No default no-arg constructor.
    private LockGraph() { }
    // Default Constructor
    public LockGraph(Synonym T, HashMap P) {
        init();
        this.This = T;
        this.Parameters = P;
    }
    // Copy Constructor
    public LockGraph(LockGraph other) {
        init();
        if (other!=null) deepCopy(other);
    }

    public boolean equals (Object o) {
        if (o==null) return false;
        LockGraph l = (LockGraph) o;
        return (((heads==null)      ? (l.heads==null)      : heads.equals(l.heads)) &&
                ((edges==null)      ? (l.edges==null)      : edges.equals(l.edges)) &&
                ((LS==null)         ? (l.LS==null)         : LS.equals(l.LS)) &&
                ((EdgeTracker==null)? (l.EdgeTracker==null): EdgeTracker.equals(l.EdgeTracker)) &&
                ((This==null)       ? (l.This==null)       : This.equals(l.This)) &&
                ((Parameters==null) ? (l.Parameters==null) : Parameters.equals(l.Parameters)) &&
                ((rets==null)       ? (l.rets==null)       : rets.equals(l.rets)));
    }

    public int hashCode() {
        int hash = 1;
        hash = hash *  1 + ((heads==null)      ? 73 : heads.hashCode());
        hash = hash * 37 + ((edges==null)      ? 19 : edges.hashCode());
        hash = hash * 29 + ((LS==null)         ? 97 : LS.hashCode());
        hash = hash * 61 + ((This==null)       ? 83 : This.hashCode());
        hash = hash * 79 + ((Parameters==null) ? 17 : Parameters.hashCode());
        hash = hash * 59 + ((rets==null)       ? 29 : rets.hashCode());
        return hash;
    }
    public boolean isEmpty() { 
        if (edges==null) return true;
        return edges.isEmpty() && ((rets==null) || rets.isEmpty()); 
    }
    public HashSet LockSet() { return LS; }
    public int size() { return edges.size(); }

    private static LockGraph empty = null;
    public static LockGraph emptyLockGraph() {
        empty = new LockGraph();
        empty.init();
        empty.This = null;
        empty.Parameters = null;
        empty.rets = null;
        return empty;
    }

    /* Shallow copy: This function should be used only when one is sure that the
     * copy will NOT be modified!!!! */
    public void copy(LockGraph other) {
        if (equals(other)) return;
        heads = other.heads;
        edges = other.edges;
        LS    = other.LS;
        This  = other.This;
        Parameters = other.Parameters;
        EdgeTracker = other.EdgeTracker;
    }

    /* Deep copy: This function should be used to make a -thorough- copy of the 
     * other LockGraph. Deep Copy assumes that init() has been run. */
    public void deepCopy(LockGraph other) {
        deepCopy(other,true);
    }
    public void deepCopy(LockGraph other, boolean flag) {
        if (equals(other)) return;
        if (other.heads!=null) heads = replicate(other.heads);
        if (other.edges!=null) edges = replicate(other.edges);
        if (other.LS !=null) LS = replicate(other.LS);
        This = other.This;
        Parameters = other.Parameters;
        if (other.EdgeTracker!=null) EdgeTracker = other.replicateEdgeTracker();
        if (flag) rets = (other.rets==null?null:new HashSet(other.rets));
    }
    /****************************************************************
     * Function to substitute all occurences of a given Synonym with
     * an aggregate in the entire LockGraph by repeated invocations
     * of replaceAll().
     * *************************************************************/
    public void sub(Synonym before, Aggregate after) {
        if (verboseLGSub) E.debug("Begin substitution of "+before+" by "+after);
        // substitute in lock-set
        replaceAll(LS, before, after, "LockSet");
        // substitute in edges
        MultiMap newEdges = new MultiMap();
        for (Iterator lit = edges.keySet().iterator(); lit.hasNext(); ) {
            LockNode ln = (LockNode) lit.next();
            HashSet succs = edges.get(ln);
            ln.replace(before, after);
            if (succs!=null) replaceAll(succs, before, after, "Successors");
            newEdges.putAll(ln, succs);
        }
        edges = newEdges;
        // substitute in heads
        replaceAll (heads, before, after, "Heads");
        rets = replaceAllSyns (rets, before, after);
        track(before, after);
    }
    /***********************************************
     * Adding edges to mimic lock acquisition
     ***********************************************/
    public void addLock(Aggregate lv, boolean synch, SootMethod m) {
        if (lv.isEmpty()) {
            E.warn("Did not add lock in method "+m+" as lock node was empty!");
            return;
        }
        LockNode ln = new LockNode(lv, synch);
        // Tracker.put(ln, trackString(m));
        if (verboseLG) E.debug("["+ln+"], hash value = "+ln.hashCode());
        if (LS.isEmpty()) {
            heads.add(ln);
            LS.add(ln);
            edges.put(ln,null);
        } else if (!LS.contains(ln)) {
            for (Iterator it = LS.iterator(); it.hasNext(); ) {
                LockNode from = (LockNode) it.next();
                if (!ln.equals(from)) addEdge(from, ln, m);
            }
            if (!synch) LS.add(ln);
        } else {
            E.warn("Lock-set already contains Lock:["+ln+"], skipping.");
        }
        if (verboseLG) E.debug("Current LockSet: "+LS.toString());
    }

    /***********************************************
     * Removing lock from Lockset
     ***********************************************/
    public void removeLock(Aggregate lv,boolean synch) {
        if (LS.isEmpty() || edges.isEmpty()) return;
        LockNode ln = new LockNode(lv, synch);
        if (verboseLG) {
            E.debug(" Called removeLock("+ln+") (hash "+ln.hashCode()+"). Lock-set = "+LS);
            if (LS.contains(ln)) E.debug("Removing Aggregate = "+ln);
            else                 E.debug("LockSet does not contain "+ln+"!");
        }
        LS.remove(ln);
        if (verboseLG) E.debug("After Removing "+ln+", lockSet = {"+LS.toString()+"}");
    }

    private void removeSelfLoops() {
        for (Iterator it = edges.keySet().iterator(); it.hasNext(); ) {
            LockNode ln = (LockNode) it.next();
            HashSet succ = (HashSet) edges.get(ln);
            if (succ.contains(ln)) succ.remove(ln);
        }
    }

    /********************************************
     * Add edges from the "waiting" lock to all
     * nodes in the current lockSet 
     ******************************************/
    public void addNotify (Aggregate lv, SootMethod m) {
        LockNode ln = new LockNode(lv, true);
        // Tracker.put(ln, trackString(m));
        if (verboseLG) E.debug("Caled addNotify("+ln+")");
        notifyList.add(ln);
        assert (!LS.isEmpty());
        if (LS.isEmpty()) {
            E.error("notify()/notifyAll() has to be called in a synchronized context!");
        }
        for (Iterator it = LS.iterator(); it.hasNext(); ) {
            LockNode to = (LockNode) it.next();
            heads.add(ln);
            addEdge(ln, to, m); // These edges are reverse!
        }
    }

    /***************************************
     * G1.merge(G2), merges G2 into G1.
     ****************************************/
    public void merge (LockGraph other) {
        if (equals(other)) return;
        if (verboseLG) {
            E.debug("Merging Lock Graphs:");
            E.debug("Passed to Merge: LG1 = "); printCompact(); 
            E.debug("Passed to Merge: LG2 = "); other.printCompact();
        }
        if (other.isEmpty()) {
            if (verboseLG) {E.debug("Merge Result: "); printCompact();}
            return;
        }
        if (isEmpty()) {
            deepCopy(other);
            if (verboseLG) {E.debug("Merge Result: "); printCompact();}
            return;
        } 
        if (other.rets!=null) {
            if (verboseLG) E.debug("Got non-empty rets in merge. Rets = "+rets);
            if (rets==null) rets = new HashSet(other.rets);
            else rets.addAll(other.rets);
        }
        LS.addAll(other.LS);
        edges.merge(other.edges);
        heads.addAll(other.heads);
        EdgeTracker.merge(other.EdgeTracker);
        // Tracker.merge(other.Tracker);
        if (verboseLG) {E.debug("Merge Result: "); printCompact();}
    } 

    private void makeHeads() {
        HashSet newHeads = new HashSet();
        for (Iterator it = edges.keySet().iterator(); it.hasNext(); ) {
            LockNode from = (LockNode) it.next();
            HashSet succ = (HashSet) edges.get(from);
            newHeads.add(from);
            newHeads.removeAll(succ);
        }
        heads = newHeads;
    }

    /*****************************************************************************
      Concatenate Graph2 to Graph1. 
      Add edges from everything in Graph1's LockSet to every node in Graph2. Make 
      Graph2's LockSet as the LockSet of the resultant graph.  
     ****************************************************************************/
    public void concat(SootMethod m, LockGraph other, SootMethod m2) {
        if (verboseLG) {
            E.debug("Concatener Graph1 = "); printCompact();
            E.debug("Concatenee Graph2 = "); other.printCompact();
        }
        if (other.edges.isEmpty()) {
            if (verboseLG) { E.debug("Concatenation result:"); printCompact(); }
            return;
        }
        if (edges.isEmpty()) {
            deepCopy(other, false);
            if (verboseLG) { E.debug("Concatenation result:"); printCompact(); }
            return;
        } 

        // Add edges from locks in my lock-set to every lock in sub-routine's map
        other.makeHeads();
        for (Iterator lit = LS.iterator(); lit.hasNext(); ) {
            LockNode pre = (LockNode) lit.next();
            for (Iterator hit = other.heads.iterator(); hit.hasNext(); ) {
                LockNode post  = (LockNode) hit.next();
                if (!LS.contains(post)) addEdge(pre, post, m);
            }
        }

        // Then merge every edge in sub-routine's lock graph with my edges
        edges.merge(other.edges);
        EdgeTracker.merge(other.EdgeTracker);
        if ((other.LS!=null) && (!other.LS.isEmpty())) E.error("In method: "+m+", second argument ("+m2+") of concatenation had non-empty lock-set!");
        if (verboseLG) {E.debug("Result:"); printCompact();}
    }

    private String ws(String x) {
        String ret = "";
        for (int i=0;i<x.length();i++) ret += " ";
        return ret;
    }

    /******************************
     * Print LockGraph compactly
     *****************************/
    public void printCompact() {
        if (edges.isEmpty()) { 
            E.pn("(--- { empty } "); 
            E.pn("     RetVals = "+rets);
            E.pn("---)");
            return; 
        }
        E.pn("(--- Lock Graph:");
        E.pn("\tThis = "+This);
        for (Iterator lit = edges.keySet().iterator(); lit.hasNext(); ) {
            LockNode lock = (LockNode) lit.next();
            HashSet succs = edges.get(lock);
            if ((succs!=null) && !succs.isEmpty()) {
                E.pn("\t{ <"+lock+"> -> (");
                for (Iterator sit = succs.iterator(); sit.hasNext(); ) {
                    LockNode succ = (LockNode) sit.next();
                    if (sit.hasNext()) E.pn("\t\t<"+succ+">, ");
                    else               E.pn("\t\t<"+succ+"> )");
                }
                E.pn("\t}");
            } else {
                E.pn("\t{ <"+lock+"> -> ( <null> ) }");
            }
        }
        E.pn("   Lock-set = "+LS.toString());
        E.pn("   RetVals  = "+rets);
        E.pn("---)");
    }

    public void printCompact(PrintStream p, SootMethod m) {
        if (edges.isEmpty()) { p.print("\t(--- { empty } ---)\n"); return; }
        p.print("\n\t(--- Lock Graph for method "+m.getSignature()+" :\n");
        for (Iterator lit = edges.keySet().iterator(); lit.hasNext(); ) {
            LockNode lock = (LockNode) lit.next();
            HashSet succs = edges.get(lock);
            p.print(" \t{ <"+lock+">");
            p.print(" -> ( ");
            if (succs!=null) {
                for (Iterator sit = succs.iterator(); sit.hasNext(); ) {
                    LockNode succ = (LockNode) sit.next();
                    p.print("<"+succ+">, ");
                }
                p.print(")");
            } else {
                p.print("[null] )");
            }
            p.print(" }\n");
        }
        p.println("\t---)");
    }

    public void print(PrintStream p, SootMethod m) {
        p.println("\n============ Lock Graph for Method = "+m.getSignature()+" =============");
        // E.pn(indent+"\tHeads = "+heads.toString());
        // E.pn(indent+"\t--------------------------------------------------------");
        for (Iterator lit = edges.keySet().iterator(); lit.hasNext(); ) {
            LockNode lock = (LockNode) lit.next();
            HashSet succs = edges.get(lock);
            if (succs!=null) {
                p.println("\t"+lock);
                for (Iterator sit = succs.iterator(); sit.hasNext(); ) {
                    LockNode succ = (LockNode) sit.next();
                    p.println("\t\t "+succ);
                }
            } else {
                p.println("\t "+lock+"  [LEAF]");
            }
        }
        p.println("============== End Lock Graph. ==============\n");
    }

    public void printDot(PrintStream p, SootMethod m) {
        p.println("digraph "+ m.getName() + "{");
        for (Iterator lit = edges.keySet().iterator(); lit.hasNext(); ) {
            LockNode ln = (LockNode) lit.next();
            HashSet succs = edges.get(ln);
            if ((succs==null) || succs.isEmpty()) continue;
            for (Iterator sit = succs.iterator(); sit.hasNext(); ) {
                LockNode sn = (LockNode) sit.next();
                p.println("\t\""+ln+"\" -> \""+sn+"\"");
            }
        }
        p.println("}");
    }

    public void print(String indent) {
        if (indent.equals("")) E.pn("\n==================== Printing Lock Graph. =====================");
        E.pn(indent+"\tHeads = "+heads.toString());
        // E.pn(indent+"\t--------------------------------------------------------");
        for (Iterator lit = edges.keySet().iterator(); lit.hasNext(); ) {
            LockNode lock = (LockNode) lit.next();
            HashSet succs = edges.get(lock);
            if (succs!=null) {
                E.pn(indent+"\t"+lock);
                for (Iterator sit = succs.iterator(); sit.hasNext(); ) {
                    LockNode succ = (LockNode) sit.next();
                    E.pn(indent+"\t\t "+succ);
                }
            } else {
                E.pn(indent+"\t "+lock+"  [LEAF]");
            }
        }
        E.pn(indent+"\t--------------------------------------------------------");
        E.pn(indent+"\tLock Set = "+LS);
        E.pn(indent+"\t--------------------------------------------------------");
        // E.pn(indent+"\tNotify Set = "+notifyList);
        // E.pn(indent+"\t--------------------------------------------------------");
        // E.pn(indent+"\tTracker Info = "+Tracker);
        // E.pn(indent+"\t--------------------------------------------------------");
        if (indent.equals("")) E.pn(indent+"==================== End Lock Graph. ===========================\n");
    }

    public void printTrackingInfo(PrintStream p) {
        p.println("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~");
        for (Iterator it = EdgeTracker.keySet().iterator(); it.hasNext(); ) {
            Edge e = (Edge) it.next();
            if (!edges.containsKey(e.from)) continue;
            HashSet f = (HashSet) edges.get(e.from);
            if ((f==null) || !f.contains(e.to)) continue;

            p.println("\t--------------------------------------------------------");
            p.println("\t\t #EDGE: "+e+" was added by: ");
            HashSet ms = (HashSet) EdgeTracker.get(e);
            if (ms==null || ms.isEmpty()) E.error("For EDGE:"+e+", no source found!");
            else for (Iterator mit = ms.iterator(); mit.hasNext(); ) {
                String str = (String) mit.next();
                p.println("\t\t\t\t METHOD: "+str);
            }
            p.println("\t--------------------------------------------------------");
        }
        p.println("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~");
    }
    public void printTrackingInfo() {
        E.pn("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~");
        for (Iterator it = EdgeTracker.keySet().iterator(); it.hasNext(); ) {
            Edge e = (Edge) it.next();
            E.pn("\t--------------------------------------------------------");
            E.pn("\t\t #EDGE: "+e+" was added by: ");
            HashSet ms = (HashSet) EdgeTracker.get(e);
            if (ms.isEmpty()) E.error("For EDGE:"+e+", no source found!");
            else for (Iterator mit = ms.iterator(); mit.hasNext(); ) {
                String str = (String) mit.next();
                E.pn("\t\t\t\t METHOD: "+str);
            }
            E.pn("\t--------------------------------------------------------");
        }
        E.pn("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~");
    }

    public void checkTrackingInfo(SootMethod m, SootMethod m2) {
        for (Iterator it = EdgeTracker.keySet().iterator(); it.hasNext(); ) {
            Edge e = (Edge) it.next();
            HashSet ms = (HashSet) EdgeTracker.get(e);
            if ((ms==null) || ms.isEmpty()) {
                E.error("In Method "+m+", while concatting method "+m2+", no tracking info found for edge "+e);
            }
        }
    }

    /************************** PRIVATE FUNCTIONS *********************************/

    /****************************************************************************
     * track(_old, _new) ensures that the lockNode values are kept up to date by
     * the sub() function, inside the Tracker.
     * *************************************************************************/
    private void track(Synonym _old, Aggregate _new) {
        MultiMap m = new MultiMap();
        for (Iterator it = EdgeTracker.keySet().iterator(); it.hasNext(); ) {
            Edge e = (Edge) it.next();
            HashSet h = (HashSet) EdgeTracker.get(e);
            Edge e1 = e.sub(_old, _new);
            m.putAll(e1, h);
            it.remove();
        }
        EdgeTracker.putMap(m);
    }

    /****************************************************************************
     * replaceAll(c, _old, _new, name) searches each LockNode in a given HashSet 
     * 'c' of LockNodes, for every LockNode containing an Aggregate with the 
     * Synonym _old, and if found, replaces that Synonym with the Aggregate 
     * '_new', and name is a debug string to identify the calling fn. 
     * *************************************************************************/
    private void replaceAll (HashSet c, Synonym _old, Aggregate _new, String name) {
        if (c.isEmpty()) return;
        for (Iterator it = c.iterator(); it.hasNext(); ) {
            LockNode ln = (LockNode) it.next();
            ln.replace(_old, _new);
            if (verboseLGSub) E.debug("["+name+"] Locknode "+_old+", substituted by "+_new);
        }
    }
    private HashSet replaceAllSyns (HashSet c, Synonym _old, Aggregate _new) {
        HashSet ret = new HashSet();
        if (c.isEmpty()) return ret;
        for (Iterator it = c.iterator(); it.hasNext(); ) {
            Synonym syn = (Synonym) it.next();
            InstField I = null;
            if (syn.equals(_old)) ret.addAll((HashSet) _new);
            else if (syn.isIfr() && (I = (InstField) syn.v()).base().equals(_old)) {
                for (Iterator nit = _new.iterator(); nit.hasNext(); ) {
                    Synonym newBase = (Synonym) nit.next();
                    Synonym newSyn = new Synonym(newBase, I.field());
                    ret.add(newSyn);
                }
            } else {
                ret.add(syn);
            }
        }
        if (verboseLGSub) E.debug("["+_old+"] was replaced by "+_new);
        return ret;
    }
    // private void addSuccs(Object node1, Object successors) { edges.putAll(node1, successors); }
    private void addEdge(Object node1, Object node2, SootMethod m) { 
        LockNode l1 = (LockNode) node1;
        LockNode l2 = (LockNode) node2;
        // Skip obvious self-loops
        if (l1.equals(l2)) return;
        edges.put(node1,node2); 
        Edge e = new Edge(l1, l2);
        EdgeTracker.put(e, trackString(m));
        // if (heads.contains(l2)) heads.remove(l2);
    }


    // private boolean existsEdge(Object node1, Object node2) { return edges.existsEdge(node1,node2); }
    /*********************************
      Recursive DFS to detect cycles.
     ********************************/
    private boolean cycleCheck(LockNode l) {
        if (l.visited==1) {
            if (verboseLG) E.pn("Cycle detected!");
            witness = new ArrayList();
            witness.add(l);
            return true;
        }
        HashSet succs = edges.get(l);
        if ((l.visited==2) || !edges.containsKey(l) || (succs==null)) {
            l.visited = 2;
            return false; 
        }
        l.visited = 1;
        for (Iterator sit = succs.iterator(); sit.hasNext(); ) {
            LockNode succ = (LockNode) sit.next();
            if (cycleCheck(succ)) {
                assert(witness!=null);
                if (witness==null) {
                    E.pn("ERROR: Unknown error in cycle detection. Quitting!");
                    System.exit(-1);
                }
                LockNode head = (LockNode) witness.get(0);
                if (l!=head) witness.add(l); 
                return true;
            }
        }
        l.visited = 2;
        return false;
    }
    private String trackString(SootMethod m) {
        String str = m.getDeclaringClass().getName();
        return str+"."+m.getName();
    }
    HashSet computedList;
    public void collapseHeads() {
        HashSet newHeads = new HashSet(heads);
        for (Iterator hIt = heads.iterator(); hIt.hasNext(); ) {
            LockNode h = (LockNode) hIt.next();
            if (!newHeads.contains(h)) continue;
            computedList = new HashSet();
            HashSet c = transitiveClosure(h);
            if ((c==null) || c.isEmpty()) continue;
            if (c.contains(h)) c.remove(h);
            newHeads.removeAll(c);
        }
        E.debug("Heads originally had "+heads.size()+" elemenets and was: "+heads);
        E.debug("Heads now has "+newHeads.size()+" elemenets and is: "+newHeads);
        heads = new HashSet(newHeads);
    }

    public HashSet transitiveClosure(LockNode n) {
        computedList.add(n);
        if (!edges.containsKey(n)) return null;
        HashSet s = (HashSet) edges.get(n);
        if ((s==null) || s.isEmpty()) return null;
        HashSet tc = new HashSet();
        for (Iterator succIt = s.iterator(); succIt.hasNext(); ) {
            LockNode succ = (LockNode) succIt.next();
            if (!computedList.contains(succ)) {
                HashSet succTc = transitiveClosure(succ);
                if (succTc!=null) tc.addAll(succTc);
            }
        }
        return tc;
    }
    public int numLocks() {
        return allLocks().size();
    }

    public int numEdges() {
        if (edges.isEmpty()) return 0;
        int sum = 0;
        for (Iterator it = edges.keySet().iterator(); it.hasNext();) {
            HashSet ss = (HashSet) edges.get((LockNode) it.next());
            if ((ss==null) || ss.isEmpty()) continue;
            sum++;
        }
        return sum;
    }

    public HashSet allLocks() {
        HashSet ret = new HashSet();
        if (edges.isEmpty()) return ret;
        for (Iterator it = edges.keySet().iterator(); it.hasNext(); ) {
            LockNode ln = (LockNode) it.next();
            ret.add(ln);
            HashSet succs = (HashSet) edges.get(ln);
            if ((succs==null) || succs.isEmpty()) continue;
            ret.addAll(succs);
        }
        return ret;
    }

    HashSet allUniqueTypes() {
        HashSet ret = new HashSet();
        for (Iterator it = allLocks().iterator(); it.hasNext(); ) 
                ret.add(((LockNode) it.next()).getFullType());
        return ret;
    }

    ArrayList allTypes() {
        ArrayList ret = new ArrayList();
        for (Iterator it = allLocks().iterator(); it.hasNext(); ) 
                ret.add(((LockNode) it.next()).getFullType());
        return ret;
    }

    Order createOrderedLocks(String prefix, ArrayList commonTypes) {
        Order ret = new Order(prefix+"_");
        if (edges.isEmpty()) return ret;
        ArrayList tempH = new ArrayList(commonTypes);
        ArrayList stack = new ArrayList();
        /* Push all nodes of common type to the front */
        for (Iterator it = allLocks().iterator(); it.hasNext(); )  {
            LockNode l = (LockNode) it.next();
            if (!tempH.remove(l.getFullType())) {
                stack.add(l);
                continue;
            }
            ret.add(l);
        }
        /* Non-common type nodes don't cause deadlocks due to aliasing. Push them to the end */
        for (Iterator it = stack.iterator(); it.hasNext(); ) ret.add((LockNode) it.next());
        return ret;
    }

    private String rsrcStr(int[] pattern, int idx) {
        String vrp = "VR"; /* vrp = virtual resource prefix */
        return vrp + (new Integer(pattern[idx])).toString();
    }

    private MultiMap replicateEdgeTracker() {
        if (EdgeTracker == null) return null;
        MultiMap m = new MultiMap();
        for (Iterator it = EdgeTracker.keySet().iterator(); it.hasNext();) {
            Edge e = (Edge) it.next();
            Edge newE = new Edge(e);
            m.putAll(newE, (HashSet) EdgeTracker.get(e));
        }
        return m;
    }

    /* Given pattern and an order, create the constraints */
    public String createConstraints(int [] pattern, Order o) {
        String constraints = "";
        // assert (o.size() <= pattern.length);
        for (Iterator it = allLocks().iterator(); it.hasNext(); ) {
            LockNode l = (LockNode) it.next();
            int myIndex = o.getIndex(l);
            /* Create the Aliasing (Equality) Constraint */
            constraints += (new YicesConstraint("=", o.getGenericName(l), rsrcStr(pattern, myIndex))).toString();

            /* Create the Ordering (Less Than) Constraints */
            HashSet succs = (HashSet) edges.get(l);
            if ((succs==null) || succs.isEmpty()) continue;
            for (Iterator sIt = succs.iterator(); sIt.hasNext(); ) {
                LockNode s = (LockNode) sIt.next();
                constraints += (new YicesConstraint("<", o.getGenericName(l), o.getGenericName(s))).toString();
            }
        }
        return constraints;
    }

    private HashSet replicate(HashSet o) {
        if (o==null) return null;
        HashSet ret = new HashSet();
        for (Iterator it = o.iterator(); it.hasNext(); ) {
            LockNode ln = (LockNode) it.next();
            LockNode copyLn = new LockNode(ln);
            ret.add(copyLn);
        }
        return ret;
    }

    private MultiMap replicate(MultiMap m) {
        if (m==null) return null;
        MultiMap ret = new MultiMap();
        for (Iterator it = m.keySet().iterator(); it.hasNext(); ) {
            LockNode ln = (LockNode) it.next();
            LockNode copyLn = new LockNode(ln);
            HashSet  succs = m.get(ln);
            HashSet copySuccs = replicate(succs);
            ret.putAll(copyLn, copySuccs);
        }
        return ret;
    }
    public boolean has(LockNode ln) {
        if (edges.containsKey(ln)) return true;
        for (Iterator it = edges.entrySet().iterator(); it.hasNext(); ) {
            Map.Entry e = (Map.Entry) it.next();
            if(((HashSet) e.getValue()).contains(ln)) return true;
        }
        return false;
    }

    private HashSet fromTypes() {
        HashSet ret = new HashSet();
        for (Iterator it = edges.keySet().iterator(); it.hasNext(); ) {
            LockNode ln = (LockNode) it.next();
            ret.add(ln.getFullType());
        }
        return ret;
    }

    public boolean prune(LockGraph other) {
        boolean ret = false;
        HashSet types = fromTypes();
        types.addAll(other.fromTypes());

        for (Iterator it = edges.entrySet().iterator(); it.hasNext(); ) {
            Map.Entry e = (Map.Entry) it.next();
            LockNode  l = (LockNode)  e.getKey();
            HashSet   s = (HashSet)   e.getValue();
            // Final locks cannot alias to anything.
            if (l.isFinal()) { it.remove(); ret = true; continue; }
            for (Iterator sit = s.iterator(); sit.hasNext(); ) {
                LockNode sn = (LockNode) sit.next();
                if (!types.contains(sn.getFullType())) {
                    sit.remove();
                    ret = true;
                }
            }
            if (s.isEmpty()) { it.remove(); ret = true; }
        }
        return ret;
    }
    public boolean emptyLockSet() {
        if (!LS.isEmpty()) {
            LS.clear();
            return false;
        }
        return true;
    }
    // Helper for constructors. 
    private void init() {
        edges = new MultiMap();
        heads = new HashSet();
        LS    = new HashSet();
        EdgeTracker = new MultiMap();
        rets = new HashSet();
    }

    public void trim() {
        removeSelfLoops();
        for (Iterator eit = edges.entrySet().iterator(); eit.hasNext(); ) {
            Map.Entry e = (Map.Entry) eit.next();
            LockNode l = (LockNode) e.getKey();
            HashSet v = (HashSet) e.getValue();
            if (filter(l) || (v==null) || v.isEmpty()) {
                eit.remove();
                continue;
            }
            for (Iterator sit = v.iterator(); sit.hasNext(); ) {
                LockNode s = (LockNode) sit.next();
                if (filter(s)) sit.remove();
            }
        }
    }

    public void lift(LockGraph L) {
        This = L.This;
        Parameters = L.Parameters;
    }

    public void addReturnValues(HashSet x) {
        rets.addAll(x);
    }
    public HashSet retVals() {
        return new HashSet(rets);
    }

    private static HashSet filterList = new HashSet();

    public static void populateFilterList() {
        filterList.add("java.util.ResourceBundle");
        filterList.add("java.security.Permissions");
        filterList.add("java.lang.ClassLoader");
        filterList.add("java.security.Policy");
    }

    private boolean filter(LockNode l) {
        for (Iterator it = LockGraph.filterList.iterator(); it.hasNext(); ) {
            String x = (String) it.next();
            if (l.toString().indexOf(x) != -1) return true;
        }
        return false;
    }

    public ArrayList partition() {
        ArrayList ret = new ArrayList();
        if (isEmpty()) return ret;
        for (Iterator hit = heads.iterator(); hit.hasNext(); ) {
            LockNode head = (LockNode) hit.next();
            LockGraph part = new LockGraph();
            part.init();
            part.heads.add(head);
            ArrayList worklist = new ArrayList();
            worklist.add(head);
            while (!worklist.isEmpty()) {
                LockNode l = (LockNode) worklist.get(0);
                worklist.remove(0);
                HashSet succs = (HashSet) edges.get(l);
                part.edges.putAll(l,succs);
                worklist.addAll(succs);
            }
            part.This = this.This;
            part.Parameters = this.Parameters;
            part.EdgeTracker = this.EdgeTracker;
            part.rets = this.rets;
            ret.add(part);
        }
        return ret;
    }
}
