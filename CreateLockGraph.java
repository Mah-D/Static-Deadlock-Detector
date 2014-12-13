/**************************************************************************
 * @author Mahdi Eslamimehr
 * @version 0.1
 ***************************************************************************/
package ContractGen;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.ArrayList;
import java.util.List;
import java.util.LinkedList;

import soot.toolkits.scalar.*;
import soot.Value;
import soot.Type;
import soot.ValueBox;
import soot.SootClass;
import soot.SootMethod;
import soot.toolkits.graph.*;
import soot.Unit;
import soot.Context;
import soot.Body;
import soot.Local;
import soot.util.Chain;
import soot.util.HashChain;
import soot.Scene;
import soot.PointsToSet;

import soot.jimple.AssignStmt;
import soot.jimple.DefinitionStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.IfStmt;
import soot.jimple.ThisRef;
import soot.jimple.MonitorStmt;
import soot.jimple.internal.JimpleLocal;
import soot.jimple.EnterMonitorStmt;
import soot.jimple.ExitMonitorStmt;
import soot.jimple.GotoStmt;
import soot.jimple.InvokeStmt;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.ReturnStmt;
import soot.jimple.RetStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.NewExpr;
import soot.jimple.NewArrayExpr;
import soot.jimple.NewMultiArrayExpr;
import soot.jimple.CaughtExceptionRef;
import soot.jimple.Constant;
import soot.PrimType;
import soot.jimple.ThrowStmt;

// public class CreateLockGraph extends ForwardBranchedFlowAnalysis {
public class CreateLockGraph extends ForwardFlowAnalysis {
    /***************************************************
     * Private fields
     **************************************************/
    private String dashes = "-----------------------------------------------------------------------------";
    private String line   = "=============================================================================";
    private String sep = "...........................................................";
    private Analyzer A;
    private UnitGraph g;
    private LockGraph initEntry = null;
    private LockGraph init = null;
    private LockGraph result;
    private Synonymizer Mizer;
    private SootMethod owner;
    private SootClass LibraryClass;
    private boolean verbose      = E.isOpt("verboseIntraP", "true");
    private boolean verboseLGSub = E.isOpt("verboseLGSub", "true");
    private boolean verboseIntraP = E.isOpt("verboseIntraP", "true");
    private boolean useRecursiveFP = E.isOpt("useRecursiveFP", "true");

    public CreateLockGraph (Analyzer A, UnitGraph g, SootMethod m, SootClass L) {
        super(g);
        this.A = A;
        this.g = g;
        this.owner = m;
        this.LibraryClass = L;
        Body b = m.retrieveActiveBody();
        Mizer = new Synonymizer(b);
        /*
        if (verboseIntraP) {
            for (Iterator i = b.getLocals().iterator(); i.hasNext(); ) {
                Local l1 = (Local) i.next();
                PointsToSet p1 = Scene.v().getPointsToAnalysis().reachingObjects(l1);
                E.pn ("\t\tType of "+l1+" = "+l1.getType()+" Possible types = "+p1.possibleTypes());
                for (Iterator j = b.getLocals().iterator(); j.hasNext(); ) {
                    Local l2 = (Local) j.next();
                    PointsToSet p2 = Scene.v().getPointsToAnalysis().reachingObjects(l2);
                    E.pn("\t\t\tType of "+l2+" = "+l2.getType()+" Possible types = "+p2.possibleTypes()+" Intersect? "+ p1.hasNonEmptyIntersection(p2));
                }
                E.pn(" ");
            }
        }
        */
        result = new LockGraph(Mizer.This, Mizer.Parameters);
        doAnalysis();
    }
    public LockGraph answer() { return result; }
    protected Object newInitialFlow() { 
        return new LockGraph(Mizer.This, Mizer.Parameters);
    }
    protected Object entryInitialFlow() { 
        initEntry = new LockGraph(Mizer.This, Mizer.Parameters);
        if (owner.isSynchronized()) {
            Aggregate tv=null;
            tv = new Aggregate(Mizer.This);
            initEntry.addLock(tv,false,owner);
        } 
        return initEntry;
    }
    public void merge (Object in1, Object in2, Object out) {
        LockGraph l1 = (LockGraph) in1;
        LockGraph l2 = (LockGraph) in2;
        LockGraph lout = (LockGraph) out;
        lout.deepCopy(l1);
        lout.merge(l2);
    }
    protected void copy (Object source, Object dest) {
        ((LockGraph) dest).deepCopy((LockGraph) source);
    }
    protected void flowThrough (Object in, Object u, Object out) { 
        copy (in, out);
        Unit un = (Unit) u;
        Stmt s = (Stmt) u;
        printFlow(un, (LockGraph) in, "in");
        if (s instanceof DefinitionStmt) {
            Value lOp = ((DefinitionStmt) s).getLeftOp();
            Value rOp = ((DefinitionStmt) s).getRightOp();
            if (rOp instanceof InvokeExpr) {
                processInvokeExpr(lOp, (InvokeExpr) rOp, (LockGraph) out);
            } else Mizer.makeSynonyms(lOp, rOp, owner);
        } else if (s instanceof MonitorStmt) { 
            processMonitorStmt((MonitorStmt) s, (LockGraph) out); 
        } else if (s instanceof InvokeStmt) {
            processInvokeExpr(null, ((InvokeStmt) s).getInvokeExpr(), (LockGraph) out); 
        } else if ((s instanceof ReturnStmt) || 
                    (s instanceof RetStmt)    || 
                    (s instanceof ReturnVoidStmt)) {
            processReturnStmt(s, (LockGraph) out); 
        } 
        printFlow(un, (LockGraph) out, "out");
    }
    public void printFlowFact(Object o) {
        LockGraph l = (LockGraph) o;
        l.printCompact();
    }
    private void printFlow(Unit u, LockGraph L, String inout) {
        if (verboseIntraP) {
            String pre  = (inout.equals("in")?line:dashes);
            String post = (inout.equals("in")?dashes:line);
            E.pn(pre);
            E.pn("Method      : ["+owner.getSignature()+"]");
            E.pn("Statement   : ["+((Stmt) u)+"]");
            E.pn("Succ of "+u+" = "+printSet(g.getSuccsOf(u)));
            E.pn("Pred of "+u+" = "+printSet(g.getPredsOf(u)));
            if(g.getPredsOf(u).size() == 1)  {
                E.pn("Unit to AF for pred = ");
                ((LockGraph) unitToAfterFlow.get(g.getPredsOf(u).get(0))).printCompact();
            }
            debugLG("LG-"+inout, owner, L);
            E.pn(post);
        }
    }
    private void processReturnStmt(Stmt s, LockGraph lout) {
        if (owner.isSynchronized()) {
            Aggregate tv = new Aggregate(lout.This);
            lout.removeLock(tv,false); 
        }
        if (s instanceof ReturnStmt) {
            Value retVal = ((ReturnStmt) s).getOp();
            if (retVal instanceof JimpleLocal) {
                Aggregate retSyns = getNames((JimpleLocal) retVal, false);
                lout.addReturnValues((HashSet) retSyns);
            } else {
                E.warn("In method: "+owner+", return value was not a local!");
            }
        }
        summarize(lout);
    }
    private void processMonitorStmt(MonitorStmt s, LockGraph lout) {
        JimpleLocal lockName = (JimpleLocal) s.getOp();
        Aggregate LockNames = getNames(lockName, true);
        if (s instanceof EnterMonitorStmt) lout.addLock(LockNames,false,owner );
        if (s instanceof ExitMonitorStmt)  lout.removeLock(LockNames,false);
    }
    private void processInvokeExpr (Value lhs, InvokeExpr expr, LockGraph lout) {
        LockGraph orig = new LockGraph(lout);
        List args = expr.getArgs();
        SootMethod callee = expr.getMethod();
        String b = "";
        JimpleLocal base = null;
        if (expr instanceof StaticInvokeExpr)
                b = callee.getDeclaringClass().getType().toString();
        else {
            base = (JimpleLocal) ((InstanceInvokeExpr) expr).getBase();
            b = base.toString();
        }

        A.putLockGraphInCache(owner, orig); 

        E.push();
        LockGraph sum = A.ComputeMethodLockGraph(callee,b,owner);
        E.pop();

        if ((sum==null) || sum.isEmpty()) return;
        if (expr instanceof StaticInvokeExpr)   addCallSiteInfo(sum, null, args, callee);
        else                                    addCallSiteInfo(sum, base, args, callee);

        debugLG("LG", owner, orig);
        debugLG("LG + call-site", callee, sum);

        sum.lift(orig);
        orig.concat(owner, sum, callee);
        processReturnValues(lhs, sum.retVals());

        debugLG("Caller + Callee", owner, orig);
        lout.deepCopy(orig);
    } 


    private void processReturnValues(Value lhs, HashSet syns) {
        if ((lhs==null) || (syns==null))return;
        if (!(lhs instanceof JimpleLocal)) {
            E.warn("Return value was not assigned to a local!");
            return;
        }
        Mizer.addPair((JimpleLocal) lhs, syns, owner);
    }

    private void debugLG(String s, SootMethod m, LockGraph l) {
        if (verboseIntraP) {
            E.pn(sep);
            E.pn(s+" ["+m.getName()+"]");
            l.printCompact();
            E.pn(sep);
        }
    }

    private void addCallSiteInfo(LockGraph in, JimpleLocal base, List args, SootMethod callee) {
        debugLG("LG", callee, in);
        mapBase(in, base);
        debugLG("LG+This", callee, in);
        mapArgs(in, args);
        debugLG("LG+Params", callee, in);
    }

    private void mapBase (LockGraph in, JimpleLocal b) {
        Aggregate Locks = null;
        if (b!=null) {
            Locks = getNames(b, false);
            if (verboseLGSub) E.pn("Substituting the value of "+in.This+" with the value "+Locks);
            in.sub(in.This, Locks);
        } else if (verboseLGSub) E.debug("No substitution for this, static method invocation."); 
        return;
    }

    private void mapArgs (LockGraph in, List args) {
        if (args==null) return;
        int i = 0;
        for (Iterator argIt = args.iterator(); argIt.hasNext(); i++) {
            Value arg = (Value) argIt.next();
            HashSet a = null;
            if (arg instanceof JimpleLocal) {
                Aggregate Locks = getNames((JimpleLocal) arg, false);
                Synonym paramRef = (Synonym) in.Parameters.get(Integer.valueOf(i));
                if (verboseLGSub) E.pn("Substituting the value of "+paramRef+"  with the value "+Locks);
                in.sub(paramRef, Locks);
            }
        }
    }
    private Aggregate getNames(JimpleLocal b, boolean lock) {
        Aggregate retSet = new Aggregate();
        retSet.addAll(Mizer.getSynonyms(b, owner));
        if(!retSet.isEmpty()) return retSet;
        if (verboseIntraP && 
                    (owner.getDeclaringClass().getName().equals(LibraryClass.getName()) || 
                     owner.getName().equals("main"))) 
                E.debug("Found a top-level local");
        else if (lock) E.warn("Lock: "+b+" in method "+owner+" had no 'good' synonyms, using 'bad' synonym.");
        retSet.add(new Synonym(b, owner));
        Mizer.addPair(b, (HashSet) retSet, owner);
        return retSet;
    }
    private void summarize(LockGraph l) { 
        if (l.isEmpty()) return;
        result.merge(l); 
    }
    private String printSet(Collection a) {
        String ret = "";
        for (Iterator it = a.iterator(); it.hasNext(); ) {
            ret += (it.next().toString()+"\n");
        }
        return ret;
    }
}
