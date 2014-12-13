/**************************************************************************
 * @author Mahdi Eslamimehr
 * @version 0.1
 ***************************************************************************/

package ContractGen;

import soot.SootClass;
import soot.SootMethod;
import soot.Type;
import java.util.Iterator;
import java.util.ArrayList;
import java.io.PrintStream;
import java.io.IOException;
import java.io.File;
import java.util.Arrays;
import java.util.HashSet;

public class GenerateContracts {
    private SootClass L;
    private int numWritten;
    public static int numAstro;
    public static int totalWritten;
    public static int numCombos;
    public static final int maxClassLimit = 20000;
    public static final int maxComboLimit = 50;
    public static final int partitionThreshold = 4;
    public Analyzer A;
    private String outDir;
    private boolean verboseConstGen;
    private boolean verbosePatGen;
    private boolean useTypeAliasing;
    private boolean partitionLG;
    public GenerateContracts (Analyzer A, String outDir) {
        verboseConstGen = E.isOpt("verboseConstGen", "true");
        verbosePatGen   = E.isOpt("verbosePatGen", "true");
        useTypeAliasing = E.isOpt("useTypeAliasing", "true");
        partitionLG     = E.isOpt("partitionLG", "true");
        populateSafelyAvoid();
        this.A = A;
        L = A.LibraryClass;
        this.outDir = outDir+"/"+L.getName()+".out/";
        doit();
    }

    int numCommonTypes(LockGraph l1, LockGraph l2) {
        return commonTypes(l1,l2).size();
    }

    int numCommonTypes(LockGraph l) {
        return commonTypes(l).size();
    }

    int numResources(LockGraph l1, LockGraph l2) {
        return l1.numLocks() + l2.numLocks() - numCommonTypes(l1,l2);
    }
    
    ArrayList commonTypes(LockGraph l) {
        ArrayList ret = new ArrayList();
        if (l.isEmpty()) return ret;
        ArrayList t = l.allTypes();
        if (verbosePatGen) E.pn("All types = "+t);
        if (t.isEmpty()) return ret;
        for (int i=0; i<t.size(); i++) {
            String type1 = (String) t.get(i);
            if (ret.contains(type1)) continue;
            int count = 0;
            for (int j=i+1; j<t.size(); j++) {
                String type2 = (String) t.get(j);
                if (type1.equals(type2)) {
                    count=((count==0)?2:(count+1));
                }
            }
            for (int k=0;k<count;k++) ret.add(type1);
        }
        // E.pn("Returning");
        return ret;
    }

    ArrayList commonTypes(LockGraph l1, LockGraph l2) {
        /* commonTypes({T,T,T1,T2}, {T,T1,T3}) = {T, T1};
         * commonTypes({T,T,T1}, {T, T, T2} = {T, T};
         * commonTypes({T,T1,T2}, {T, T2, T1} = {T,T1}; 
         * can't achieve this with sets since we want 
         * duplicated elements! */
        ArrayList ret = new ArrayList();
        if (l1.isEmpty() || l2.isEmpty()) return ret;
        ArrayList t1 = l1.allTypes();
        if (t1.isEmpty()) return ret;
        ArrayList t2 = new ArrayList(l2.allTypes());
        if (t2.isEmpty()) return ret;

        for (Iterator it = t1.iterator(); it.hasNext(); ) {
            String x = (String) it.next();
            if (t2.remove(x)) ret.add(x);
        }
        return ret;
    }

    private boolean skip(String name) {
        if (name.equals("main") ||
            name.equals("<clinit>")) return true;
        return false;
    }

    private void compose(SootMethod m1, SootMethod m2) {
        // main method is just a placeholder, skip it.
        if (skip(m1.getName()) || skip(m2.getName())) return;

        if (verbosePatGen) {
            E.pn("----------------------------------------------------------------");
            E.pn("Composing methods: ");
            E.pn("\t"+m1.getSignature()+"     and ");
            E.pn("\t"+m2.getSignature());
        }

        /* Private methods cannot be invoked by clients, or subclasses */
        if (m1.isPrivate() || m2.isPrivate()) {
            if (verboseConstGen) E.pn("Skipping CG ("+m1.getName()+","+m2.getName()+") (private methods)");
            return;
        }

        boolean sameMethod = m1.getSignature().equals(m2.getSignature());
        GenerateContracts.numCombos++;

        LockGraph lg1 = A.getLockGraphFromCache(m1); if (lg1==null) { E.crit("Null lock-graph found for "+m1); }
        LockGraph lg2 = A.getLockGraphFromCache(m2); if (lg2==null) { E.crit("Null lock-graph found for "+m2); }
        if (lg1.isEmpty() || lg2.isEmpty()) {
            if (verboseConstGen) E.pn("Skipping CG ("+m1.getName()+","+m2.getName()+") (empty lock-graphs)");
            return;
        }
        LockGraph lg1_preTrim = new LockGraph(lg1); lg1.trim();
        LockGraph lg2_preTrim = new LockGraph(lg2); lg2.trim();

        while (true) {
            boolean f1 = lg1.prune(lg2);
            boolean f2 = lg2.prune(lg1);
            if (!(f1 || f2)) break;
        }
        // E.pn("Done Pruning");
        if (lg1.isEmpty() || lg2.isEmpty()) {
            if (verboseConstGen) E.pn("Skipping CG ("+m1.getName()+","+m2.getName()+") (empty lock-graphs after trim/prune)");
            return;
        }

        int nP = (sameMethod?numCommonTypes(lg1):numCommonTypes(lg1,lg2));
        if (verboseConstGen) {
            E.pn("Method "+m1.getSignature()+" statistics: ");
            E.pn("\t\tNumber of locks = "+lg1.numLocks());
            E.pn("\t\tNumber of edges = "+lg1.numEdges());
            lg1.printCompact();
            if (!sameMethod) {
                E.pn("Method "+m2.getSignature()+" statistics: ");
                E.pn("\t\tNumber of locks = "+lg2.numLocks());
                E.pn("\t\tNumber of edges = "+lg2.numEdges());
                lg2.printCompact();
                E.pn("\tNumber of common types  = "+numCommonTypes(lg1,lg2));
            } else {
                E.pn("\tNumber of common types = "+numCommonTypes(lg1));
            }
            E.pn("----------------------------------------------------------------");
        }
        if ((lg1==null) || lg1.isEmpty() || 
            (lg2 == null) || lg2.isEmpty() ||
            (lg1.numLocks()<=1)  ||  (lg2.numLocks() <=1) ||
            (lg1.numEdges()< 1) ||  (lg2.numEdges() < 1) ||
            (nP<2)) {
            if (verboseConstGen) {
                E.pn("Skipping CG ("+m1.getName()+","+m2.getName()+") (deemed undeadlockable)");
                E.pn("----------------------------------------------------------------");
            }
            return;
        }

        ArrayList lgs1=null, lgs2=null;
        if ((lg1.numLocks()<GenerateContracts.partitionThreshold) || !partitionLG) {
            lgs1 = new ArrayList(); lgs1.add(lg1);
        } else {
            lgs1 = lg1.partition();
            for (Iterator lgit = lgs1.iterator(); lgit.hasNext(); ) {
                LockGraph li = (LockGraph) lgit.next();
                if (!intersects(li.allUniqueTypes(), (sameMethod?commonTypes(lg1):commonTypes(lg1, lg2)))) { 
                    lgit.remove();
                }

            }
        }
        if ((lg2.numLocks()<GenerateContracts.partitionThreshold) || !partitionLG) {
            lgs2 = new ArrayList(); lgs2.add(lg2);
        } else {
            lgs2 = lg2.partition();
            for (Iterator lgit = lgs2.iterator(); lgit.hasNext(); ) {
                LockGraph li = (LockGraph) lgit.next();
                if (!intersects(li.allUniqueTypes(), (sameMethod?commonTypes(lg1):commonTypes(lg1, lg2)))) { 
                    lgit.remove();
                }
            }
        }
        if (lgs1.isEmpty() || lgs2.isEmpty()) return;
        int k = 1;
        String mDirName = numCombos+"."+m1.getName()+"."+m2.getName();
        for (Iterator it1 = lgs1.iterator(); it1.hasNext(); ) {
            LockGraph l1 = (LockGraph) it1.next();
            for (Iterator it2 = lgs2.iterator(); it2.hasNext(); ) {
                LockGraph l2 = (LockGraph) it2.next(); 
                genConstraints(k, m1, m2, mDirName, sameMethod, l1, l2);
                k++;
            }
        }
        if (numWritten > 0) {
            dumpLockGraphs(0, m1, lg1_preTrim, m2, lg2_preTrim, mDirName);
        }
    }

    private void genConstraints (int idx, SootMethod m1, SootMethod m2, String mDirName, boolean sameMethod, LockGraph lg1, LockGraph lg2) {
        int nP = (sameMethod?numCommonTypes(lg1):numCommonTypes(lg1,lg2));
        if (nP>7) {
            E.pn("Skipping CG ("+m1.getName()+","+m2.getName()+") (too many combinations)");
            GenerateContracts.numAstro++;
            return;
        }
        Order o1 = lg1.createOrderedLocks(m1.getName(), 
                    (sameMethod?commonTypes(lg1):commonTypes(lg1, lg2)));
        String prefix = (sameMethod?"_2":"");
        Order o2 = lg2.createOrderedLocks(m2.getName()+prefix, 
                    (sameMethod?commonTypes(lg1):commonTypes(lg1, lg2)));

        if (verbosePatGen) { E.pn("\tOrder 1 = "+o1.toString()); }
        if (verbosePatGen) { E.pn("\tOrder 2 = "+o2.toString()); }

        numWritten=0; 
        PermutationGenerator pg1 = new PermutationGenerator(nP);
        boolean f1 = false, f2 = false;

        while (pg1.getNumLeft().longValue() >= (pg1.getTotal().longValue()/2)) {
            int[] pattern1 = pg1.nextPermutation();
            PermutationGenerator pg2 = new PermutationGenerator(nP);
            while (pg2.hasNext()) {
                int[] pattern2 = pg2.nextPermutation();
                if (GenerateContracts.totalWritten > GenerateContracts.maxClassLimit) {
                    E.pn ("Analysis limit for Class "+m1.getDeclaringClass().getName()+" exceeded.");
                    f2 = true; 
                    break;
                }
                if (numWritten > GenerateContracts.maxComboLimit) {
                    E.pn ("Analysis of ("+m1+"X"+m2+"), combo analysis limit exceeded, increase limit for further analysis.");
                    f1 = true;
                    break;
                }
                if (sameMethod && same(pattern1, pattern2)) continue;
                if (createConstraintFile(sameMethod, nP, mDirName, pattern1, lg1, o1, pattern2, lg2, o2)) {
                    numWritten++;
                    GenerateContracts.totalWritten++;
                }
            }
            if (f1 || f2) break;
        }
        if (numWritten==0) return;
        YicesConstraint.clearInits();
        dumpVarMapping(idx, m1, o1, m2, o2, mDirName);
        dumpLockGraphs(idx, m1, lg1, m2, lg2, mDirName);
        if (verboseConstGen) E.pn("----------------------------------------------------------------");
    }


    private boolean same(int[] p, int[] q) {
        assert(p.length == q.length);
        int i;
        for (i=0; (i<p.length) && (p[i]==q[i]);i++);
        return (i==p.length);
    }

    private void dumpLockGraphs(int prefix, SootMethod m1, LockGraph l1, SootMethod m2, LockGraph l2, String dirName) {
        File m = getConstraintDir(dirName);
        boolean sameMethod = m1.getSignature().equals(m2.getSignature());
        String name = prefix+".lgs";
        File f  = new File(m, name);
        File f1 = new File(m, m1.getName()+"."+prefix+".dot");
        File f2 = new File(m, m2.getName()+"."+prefix+".dot");
        try {
            PrintStream p = new PrintStream(f);
            PrintStream p1 = new PrintStream(f1);
            l1.print(p,m1);
            l1.printTrackingInfo(p);
            l1.printDot(p1,m1);
            p1.close();
            if (!sameMethod) {
                PrintStream p2 = new PrintStream(f2);
                l2.print(p,m2);
                l2.printTrackingInfo(p);
                l2.printDot(p2,m2);
                p2.close();
            }
            if (sameMethod) { p.println("\n Self-Composition"); }
            p.close();
        } catch (IOException e) {
            E.pn(e.getMessage());
            E.crit("Error writing to file.");
        }
    }

    private void doit() {
        ArrayList targets = (ArrayList) L.getMethods();
        int count;
        int k = 0;
        GenerateContracts.totalWritten = 0;
        GenerateContracts.numCombos = 0;
        for (int i = 0; i < targets.size(); i++) {
            for (int j = i; j < targets.size(); j++) {
                if (GenerateContracts.totalWritten > GenerateContracts.maxClassLimit) return;
                SootMethod m1 = (SootMethod) targets.get(i);
                SootMethod m2 = (SootMethod) targets.get(j);
                compose(m1,m2);
            }
        }
    }

    private void printAlias(int[] p, Order o) {
        for (int i=0;i<p.length;i++) {
            E.pn(o.getLockNode(i)+"("+o.makeGenericName(i)+") aliased to VR"+p[i]);
        }
    }

    /* Each of the pat.length = l1.numLocks() + l2.numLocks() - numCommon */
    /* Let pat1 = p1[0..numCommon-1, numCommon.. l1.numLocks()-1]
     * Let pat2 = p2[0..numCommon-1, numCommon+l1.numLocks()..p2.length] 
     * (Also, p1.length = p2.length) */
    private boolean createConstraintFile (boolean sameMethod, int nP, String dirName,
                int[] p1, LockGraph l1, Order o1, 
                int[] p2, LockGraph l2, Order o2) {
        int nl1 = l1.numLocks();
        int nl2 = l2.numLocks();
        int [] pat1 = new int[nl1];
        int [] pat2 = new int[nl2];
        int i;
        /* Initialize all commonTypes patterns */
        for (i=0;i<nP;i++) {
            pat1[i] = p1[i];
            pat2[i] = p2[i];
        }
        for (i=nP;i<nl1;i++) pat1[i] = i;
        for (i=nP;i<nl2;i++) pat2[i] = (i+(sameMethod?0:nl1));

        // printAlias(pat1, o1);
        // printAlias(pat2, o2);
        if (verbosePatGen) E.pn("Original Pattern1 = "+a2str(p1)+" Pattern1= "+a2str(pat1));
        if (verbosePatGen) E.pn("Original Pattern2 = "+a2str(p2)+" Pattern2= "+a2str(pat2));
        if (badAliasing(l1, pat1, o1, l2, pat2, o2)) {
            if (verbosePatGen) E.debug ("Bad aliasing, skipping alias pattern.");
            return false;
        }
        String str = "";
        str += l1.createConstraints(pat1, o1);
        str += l2.createConstraints(pat2, o2);
        str = YicesConstraint.initVars() + str;
        File methodDir = getConstraintDir(dirName);
        try { 
            String fName = GenerateContracts.totalWritten+".ys";
            PrintStream p = new PrintStream(new File(methodDir, fName)); 
            p.println(str);
            p.close();
            if (verbosePatGen) E.info("Written constraint file: "+methodDir.getName()+"/"+fName);
        } catch (Exception e) {
            E.crit("Error writing to file "+methodDir.getName()+str);
        }
        return true;
    }

    private int getAliasedIndex(int[] a, int x) {
        int i=0;
        for(;(i<a.length) && (a[i]!=x);i++);
        return ((i==a.length)?-1:i);
    }

    /*
       private boolean noAliasing(int[] p1, int[] p2) {
       int i;
       for (i=0;(i<p1.length) && (getAlias(p2,p1[i])!=-1);i++);
       if (i<p1.length) return false;
       for (i=0;(i<p2.length) && (getAlias(p1,p2[i])!=-1);i++);
       if (i<p2.length) return false;
       return true;
       }
       */

    private boolean badAliasing(LockGraph l1, int[] p1, Order o1, LockGraph l2, int[] p2, Order o2) {
        /* For every lock in both patterns, make sure that if two locsk alias to
         * the same VR, then they are of the same type */
        boolean [] hisChecked = new boolean[p2.length];
        for (int i=0;i<p2.length;i++) hisChecked[i] = false;
        for (int myIndex=0; myIndex<p1.length; myIndex++) {
            LockNode ln1 = o1.getLockNode(myIndex);
            int otherIndex = -1;
            if (ln1.isStatic()) {
                // Two statics with the same name cannot alias to 
                // two different things
                otherIndex = o2.getIndex(ln1);
                if (otherIndex!=-1) {
                    if (p1[myIndex] != p2[otherIndex]) return true;
                }
            }
            int hisIndex = getAliasedIndex(p2, p1[myIndex]);
            if (hisIndex == -1) continue;
            hisChecked[hisIndex] = true;
            LockNode ln2 = o2.getLockNode(hisIndex);
            // Locks that are not allowed to alias, cannot be aliased!
            if (!allowedToAlias(ln1, ln2)) return true;
        }
        for (int hisIndex=0; hisIndex<p2.length;hisIndex++) {
            if (hisChecked[hisIndex]) continue;
            LockNode ln2 = o2.getLockNode(hisIndex);
            int myIndex = getAliasedIndex(p1, p2[hisIndex]);
            if (myIndex == -1) continue;
            LockNode ln1 = o2.getLockNode(myIndex);
            // Locks that are not allowed to alias, cannot be aliased!
            if (!allowedToAlias(ln2, ln1)) return true;
        }
        return false;
    }
    
    private boolean allowedToAlias(LockNode ln1, LockNode ln2) { 
        // Private variables of some known famous classes just don't
        // alias. -I- the -oracle- tells you that! Defer to my power.
        if (ln1.isPrivateOf(privateAvoids)) return false;
        if (ln2.isPrivateOf(privateAvoids)) return false;
        boolean f = ln1.getFullType().equals(ln2.getFullType()); 
        if (verbosePatGen) E.pn("Ln1 = "+ln1+" Type = "+ln1.getType()+" && Ln2 = "+ln2+" Type  = "+ln2.getType());
        if (verbosePatGen && !f) E.pn("Not same type!");
        return f;
    }


    private String a2str(int [] a) { 
        if (a.length==0) return "";
        String str = "("+a[0];
        for (int i=1;i<a.length;i++) str+= (" "+a[i]);
        return str+")";
    }


    private void dumpVarMapping(int prefix, SootMethod m1, Order o1, SootMethod m2, Order o2, String dirName) {
        File m = getConstraintDir(dirName);
        String name = prefix + ".vmap";
        File f = new File(m, name);
        boolean sameMethod = m1.getSignature().equals(m2.getSignature());
        try {
            PrintStream p = new PrintStream(f);
            p.println("Variable map for "+(sameMethod?" first instance of ":"")+ " "+m1.getSignature()+":\n");
            p.println(o1.printVarMap());
            p.println("Variable map for "+(sameMethod?"second instance of ":"")+ " "+m2.getSignature()+":\n");
            p.println(o2.printVarMap());
            p.close();
        } catch (Exception e) {
            E.crit("Error writing to file "+f.getName());
        } 
    }

    private void checkTopDir() {
        File tmpDir = new File(outDir);
        if (tmpDir.isDirectory() && tmpDir.canWrite()) return;
        if (!tmpDir.mkdir()) E.crit("Cannot create directory "+tmpDir.getName());
    }
    private File getConstraintDir(String dir) {
        checkTopDir();
        File methodDir = new File(outDir, dir);
        if (methodDir.isDirectory() && methodDir.canWrite()) return methodDir;
        if (!methodDir.mkdir()) E.crit("Cannot create directory "+dir);
        return methodDir;
    }

    private HashSet dumped = new HashSet();
    private void dumpToFile(LockGraph l, SootMethod m) {
        if (dumped.contains(m.getSignature())) return;
        checkTopDir();
        File dump = new File(outDir, m.getName()+".dot");
        File dump1 = new File(outDir, m.getSignature()+".lg");
        int i = 0;
        while (dump.exists()) {
            i++;
            dump = new File(outDir, m.getName()+i+".dot");
        }
        try {
            PrintStream p = new PrintStream(dump);
            PrintStream p1 = new PrintStream(dump1);
            l.printDot(p, m);
            l.print(p1, m);
            l.printTrackingInfo(p1);
            p.close(); 
            p1.close();
        } catch (IOException e) {
            E.pn(e.getMessage());
            E.crit("Error writing to file.");
        }
        dumped.add(m.getSignature());
    }

    private HashSet privateAvoids = new HashSet();
    private void populateSafelyAvoid() {
        privateAvoids.add("java.io.PrintStream");
        privateAvoids.add("java.security.Policy");
        privateAvoids.add("java.security.UnresolvedPermissionCollection");
        privateAvoids.add("java.io.BufferedWriter");
        privateAvoids.add("java.io.BufferedReader");
        privateAvoids.add("java.security.Permissions");
        privateAvoids.add("java.lang.Thread");
    }
    private boolean intersects(HashSet s, ArrayList c) {
        for (Iterator it = s.iterator(); it.hasNext(); ) {
            String t = (String) it.next();
            if (c.contains(t)) return true;
        }
        return false;
    }
}
