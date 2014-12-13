
/**************************************************************************
 * @author Mahdi Eslamimehr
 * @version 0.1
 ***************************************************************************/


package ContractGen;

import java.util.HashSet;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.ArrayList;
import java.util.Map;
import java.util.Map.Entry;

import soot.Value;
import soot.PointsToSet;
import soot.PointsToAnalysis;
import soot.Scene;
import soot.Local;
import soot.SootMethod;
import soot.SootField;
import soot.Body;
import soot.SootClass;
import soot.PrimType;

import soot.jimple.ClassConstant;
import soot.jimple.AssignStmt;
import soot.jimple.DefinitionStmt;
import soot.jimple.ThisRef;
import soot.jimple.ArrayRef;
import soot.jimple.ParameterRef;
import soot.jimple.InstanceFieldRef;
import soot.jimple.internal.JimpleLocal;
import soot.jimple.StaticFieldRef;
import soot.jimple.CastExpr;
import soot.jimple.AnyNewExpr;
import soot.jimple.CaughtExceptionRef;
import soot.jimple.Constant;
import soot.PrimType;
import soot.jimple.LengthExpr;
import soot.Type;

/************************************************************
 * Synonymizer tracks and generates synonyms.
 * Synonyms of local variables are one of the following:
   - StaticFieldRef: Static Data Members of the Library
   - InstFieldRef:   Data Members of the Library
   - ThisRef:        This Parameter for a method
   - ParameterRef:   Method Parameter
 ***********************************************************/

class SynKey {
    public Value v;
    public SootMethod m;
    public SynKey(Value v, SootMethod m) {
        this.v = v;
        this.m = m;
    }
    public String toString() {
        return m.getSignature()+":"+v.toString();
    }
    public int hashCode() {
        return toString().hashCode();
    }
    public boolean equals(Object o) {
        if (o instanceof SynKey) {
            return ((SynKey) o).toString().equals(toString()); 
        }
        return false;
    }
    public String shortString() {
        return m.getName()+":"+v.toString();
    }
}

public class Synonymizer {
    private PointsToAnalysis PTA; 
    
    /* The Synonym Map */
    private MultiMap Syn;

    /* Method to which this synonymizer belongs */
    private Body MB;
    private SootMethod M;
    public Synonym This;
    public HashMap Parameters;

    private boolean verboseSyn  = E.isOpt("verboseSyn", "true");
    private boolean avoidLocals = E.isOpt("avoidLocals", "true");
    private boolean useSootPointerAnalysis = E.isOpt("useSpark", "true");

    public Synonymizer(Body MB) {
        this.MB = MB;   
        PTA = Scene.v().getPointsToAnalysis();
        M = MB.getMethod();
        Syn = new MultiMap();
        makeThis(); 
        makeParameters();
    }

    private HashSet getIFRSyns(InstanceFieldRef in, SootMethod m) {
        Value base = in.getBase();
        if (!(base instanceof JimpleLocal)) return new HashSet();
        HashSet baseSyns = getSynonyms((JimpleLocal) base,m);
        if (baseSyns.isEmpty()) return new HashSet();
        SootField field = in.getField();
        HashSet ret = new HashSet();
        for (Iterator it=baseSyns.iterator();it.hasNext();) {
            Synonym baseSyn = (Synonym) it.next();
            ret.add(new Synonym(baseSyn, field));
        }
        return ret;
    }

    private boolean dontMake(Type t) {
        if (t instanceof PrimType) return true;
        return false;
    }

    private boolean dontMake(Value r) {
        if( (r instanceof AnyNewExpr)        ||
            (r instanceof CaughtExceptionRef)||
            (r instanceof LengthExpr)        ||
            (r instanceof ThisRef)           ||
            (r instanceof ParameterRef))
                return true;
        return false;
    }

    public void makeSynonyms(Value lhs, Value rhs, SootMethod m) {
        Type rType = rhs.getType();
        Type lType = lhs.getType();
        if (dontMake(rType) || dontMake(lType)) {
            if (verboseSyn) E.pn("Skipping Synonymization. L = "+lhs+" LType = "+lType+" R = "+rhs+" RType = "+rType);
            return;
        }
        if (dontMake(rhs)) {
            if (verboseSyn) E.pn("Skipping Synonymization. R = "+rhs);
            return; 
        }
        if (!(lhs instanceof JimpleLocal)) {
            if (verboseSyn) E.pn("Skipping Synonymization. LHS "+lhs+" is not a Local.");
            return;
        }
        if (rhs instanceof JimpleLocal) {
            // This hack should never have to be put if PTA works as desired. BUT IT NEVER DOES. !@#!@$!
            if (lhs == rhs) return;
            HashSet rhsSyns = getSynonyms((JimpleLocal) rhs, m);
            if (!rhsSyns.isEmpty()) {
                SynKey sk = new SynKey(lhs,m);
                Syn.mergeMap(sk, rhsSyns);
            }
            return;
        }
        HashSet syns = new HashSet();
        HashSet a = null;
        if (rhs instanceof StaticFieldRef) {
            /* <Local> =  <Class: Field Name>; */
            syns.add(new Synonym(rhs));
        } else if (rhs instanceof ClassConstant) {
            String cslash = ((ClassConstant) rhs).getValue();
            String cname = cslash.replace('/','.');
            SootClass c = Scene.v().getSootClass(cname);
            if (verboseSyn) E.pn ("Adding synonym "+c.getType()+" for lhs = "+lhs);
            if (c!=null) syns.add(new Synonym(c.getType()));
        } else if (rhs instanceof InstanceFieldRef) {
            /* <Local> = <Local>.<Class: Field Name> */
            a = getIFRSyns((InstanceFieldRef) rhs, m);
            if (!a.isEmpty()) syns.addAll(a);
        } else if (rhs instanceof ArrayRef) {
            /* <Local> = Array */
            if (verboseSyn) E.debug("In "+m+", array-ref "+rhs+" was abstracted.");
            Value arrayBase = ((ArrayRef) rhs).getBase();
            if (dontMake(arrayBase) || dontMake(arrayBase.getType())) return; 
            a = getSynonyms((JimpleLocal) arrayBase, m);
            if (!a.isEmpty()) syns.addAll(a);
        } else if (rhs instanceof CastExpr) {
            /* <Local> = (Cast) <Local> */
            Value casted = ((CastExpr) rhs).getOp();
            if (dontMake(casted.getType()) || dontMake(casted) || !(casted instanceof JimpleLocal)) return;
            a = getSynonyms((JimpleLocal) casted, m);
            if (!a.isEmpty()) syns.addAll(a);
        }
        if (syns.isEmpty() && !(rhs instanceof JimpleLocal)) {
            E.warn("In "+m+", synonyms not found for LHS = "+lhs);
            return;
        }
        SynKey sk = new SynKey(lhs,m);
        Syn.mergeMap(sk, syns);
    }

    public HashSet getSynonyms(JimpleLocal x, SootMethod m) {
        if (verboseSyn) { 
            E.debug("Passed "+x+" to getSynonyms");
            E.debug ("Synonym map at this point was: "); 
            printSynMap(Syn); 
        }
        HashSet ret = new HashSet();
        Type xType = x.getType();
        if (xType instanceof PrimType) return ret;
        if (x instanceof ArrayRef) if (((ArrayRef) x).getBase().getType() instanceof PrimType) return ret;

        SynKey xKey = new SynKey(x,m);
        if (useSootPointerAnalysis) {
            // Find if any key (with known synonyms) and desired local intersect 
            for (Iterator it = Syn.keySet().iterator();it.hasNext();) {
                SynKey key = (SynKey) it.next();
                if (!key.m.getSignature().equals(m.getSignature())) continue;
                if (verboseSyn) E.pn("Passed: "+x+", Comparing with: "+key.v);
                PointsToSet p1 = PTA.reachingObjects((Local) (key.v));
                // E.pn("key types = "+p1.possibleTypes());
                PointsToSet p2 = PTA.reachingObjects((Local) x);
                // E.pn("x types = "+p2.possibleTypes());
                if (p1.hasNonEmptyIntersection(p2)) {
                    if (verboseSyn) E.debug("Found value "+x+" PT-aliased to {"+key.v+"}");
                    if (xType.toString().equals("java.lang.Object") || xType.equals(key.v.getType())) {
                        ret.addAll(Syn.get(key));
                    } else {
                        E.warn("JimpleLocal "+x+" (Type: "+xType+") found aliased to "+
                                    key.v+" (Type: "+key.v.getType()+")");
                    }
                }
            }
        }
        for (Iterator it = Syn.keySet().iterator();it.hasNext();) {
            SynKey key = (SynKey) it.next();
            if (key.equals(xKey)) {
                if (verboseSyn) E.debug("Found "+xKey+" same as {"+key+"}");
                ret.addAll(Syn.get(key));
            }
        }
        if (ret.isEmpty()) {
            E.warn("In "+m+", no synonyms found for local: ("+x+")");
            return ret;
        }
        return filterSynonyms(ret, (avoidLocals?1:0));
    }

    public void addPair (JimpleLocal x, HashSet syns, SootMethod m) {
        SynKey xKey = new SynKey(x, m);
        Syn.mergeMap(xKey, syns);
    }

    private HashSet filterSynonyms (HashSet c, int flag) {
        /* flag = 0 : no filtering.
         *      = 1 : avoid locals.
         *      = 2 : NO locals    */
        if (flag > 0) {
            if (c==null) return null;
            HashSet ret =  new HashSet();
            for (Iterator it = c.iterator(); it.hasNext();) {
                Synonym o = (Synonym) it.next();
                if (o.isGood()) ret.add(o);
            }
            if (!ret.isEmpty()) return ret;
            E.warn("Best synonyms not found, returning: "+c);
            if (flag==2) return ret;
        }
        return c;
    }

    public void makeParameters() {
        int numParams = M.getParameterCount();
        Parameters = new HashMap();
        for (Integer J=new Integer(0);J.intValue() < numParams;J=J+1) {
            int j = J.intValue();
            JimpleLocal P = (JimpleLocal) MB.getParameterLocal(j);
            ParameterRef PR = new ParameterRef(M.getParameterType(j), j);
            Synonym PS = new Synonym(PR);
            SynKey PK = new SynKey(P, M);
            Syn.put(PK, PS);
            Parameters.put(J, PS);
        }
    }
    public void makeThis() {
        if (M.isStatic()) {
            This = new Synonym(M.getDeclaringClass().getType());
        } else {
            JimpleLocal T = (JimpleLocal) MB.getThisLocal();
            ThisRef TR = new ThisRef(M.getDeclaringClass().getType());
            This = new Synonym(TR);
            SynKey TK = new SynKey(T, M);
            Syn.put(TK, This);
        }
        if (verboseSyn) E.pn("For method : "+M+" This = "+This);
    }
    public void printSynMap(MultiMap Syn) {
        for (Iterator it = Syn.keySet().iterator(); it.hasNext(); ) {
            SynKey s  = (SynKey) it.next();
            HashSet k = (HashSet) Syn.get(s);
            E.pn("\t"+s.shortString()+" = "+k);
        }
    }
}

