
/**************************************************************************
 * @author Mahdi Eslamimehr
 * @version 0.1
 ***************************************************************************/

package ContractGen;
import soot.SootField;
import soot.jimple.ThisRef;
import soot.jimple.ParameterRef;
import soot.jimple.StaticFieldRef;
import soot.Value;
import soot.Type;
import soot.SootMethod;

interface Syn {
    public String fullType();
    public Type   getType();
    public int hashCode();
    public boolean equals(Object o);
    public boolean isFinal();
    public boolean isStatic();
    public boolean canEscape();
}

class InstField implements Syn {
    private Synonym b;
    private SootField f;
    public InstField(Synonym b, SootField f) { this.b = b; this.f = f; }
    public boolean equals(Object o) {
        // E.pn("\nCalled instfield equals");
        if (!(o instanceof InstField)) return false;
        InstField oI = (InstField) o;
        return (oI.f.getName().equals(f.getName()) && oI.b.equals(b));
    }
    public int hashCode() { return (f.hashCode()*17 + b.hashCode() * 29); }
    public String toString() { return b.toString()+"."+f.toString(); }
    public String fullType() { 
        String ret = f.getType().toString();
        // This is a possibly unsound heuristic, but we invoke it only
        // when we know the java.lang.Object objects do not alias in the
        // application that we wish to analyze.
        if (f.getType().toString().equals("java.lang.Object")) {
            ret = b.fullType()+"."+ret;
        }
        return ret;
    }
    // return b.fullType().toString()+"."+f.getType().toString(); }
    public Type getType() { return f.getType(); }
    public boolean isFinal() { return f.isFinal(); }
    public boolean isStatic() { return false; }
    public Synonym base() { return b; }
    public SootField field() { return f; }
    public boolean canEscape() { return b.canEscape(); }
}

class StaticThisRef implements Syn {
    private Type t;
    public StaticThisRef(Type t) { this.t = t; }
    public String toString() { return t.toString(); }
    public String fullType() { return t.toString(); }
    public Type getType() { return t; }
    public int hashCode() { return t.hashCode(); }
    public boolean equals(Object o) {
        // E.pn("\nCalled STR equals");
        if (!(o instanceof StaticThisRef)) return false;
        return t.toString().equals(((StaticThisRef) o).t.toString());
    }
    public boolean isFinal() { return true; }
    public boolean isStatic() { return true; }
    public boolean canEscape() { return true; }
}

class ValueType implements Syn {
    private String vs;
    private Value v;
    private Type t;
    public ValueType(Value v) { 
        this.v = v;
        this.vs = v.toString();
        this.t = v.getType();
    }
    public boolean equals (Object o) {
        // E.pn("\nCalled value equals");
        if (!(o instanceof ValueType)) return false;
        ValueType ov = (ValueType) o;
        return vs.equals(ov.vs);
    }
    public String toString()  { return vs; }
    public int hashCode()     { return vs.hashCode(); }
    public Type getType()     { return t; }
    public String fullType()  { return t.toString(); }
    public boolean isFinal()  { 
        if (v instanceof StaticFieldRef) return ((StaticFieldRef) v).getField().isFinal();
        else return false;
    }
    public boolean isStatic() { return (v instanceof StaticFieldRef); }
    public boolean canEscape() { return true; }
}

class LocalType implements Syn {
    private String v;
    private String m;
    private Type t;
    private Type d;
    public LocalType (Value v, SootMethod m) { 
        this.v = v.toString(); 
        this.m = m.getDeclaringClass()+"."+m.getName();
        this.t = v.getType();
        this.d = m.getDeclaringClass().getType();
    }
    public boolean equals (Object o) {
        if (!(o instanceof LocalType)) return false;
        LocalType l = (LocalType) o;
        return (v.equals(l.v) && m.equals(l.m));
    }
    public String toString() { return m+":"+v; }
    public int hashCode() { return (v.hashCode() + 37*m.hashCode()); }
    public Type getType() { return t; }
    public String fullType() { return t.toString(); }
    public boolean isFinal() { return false; }
    public boolean isStatic() { return false; }
    // A local is a synonym only if any of the better ones were unavailable.
    // It is safe to assume that a local is thus not aliased to any of the
    // escapable synonyms.
    public boolean canEscape() { return false; }
}


public class Synonym {
    private Syn mv;
    public Syn v()  { return mv; }
    public Synonym (Value v)                { mv = new ValueType(v); }
    public Synonym (Value v, SootMethod m)  { mv = new LocalType(v, m); }
    public Synonym (Synonym b, SootField f) { mv = new InstField(b, f); }
    public Synonym (Type t)                 { mv = new StaticThisRef(t); }
    public Synonym (Synonym s)              { mv = s.mv; }
    public boolean equals(Object o) { 
        if (!(o instanceof Synonym)) return false;
        Synonym s = (Synonym) o;
        boolean f= mv.equals(s.mv);
        // E.pn("this = "+this+" passed = "+s+" equals = "+f);
        return f;
    }
    public int hashCode()    { return mv.hashCode(); }
    public String toString() { return mv.toString(); }
    public Type getType()    { return mv.getType(); }
    public String fullType() { return mv.fullType(); }
    public boolean isFinal() { return mv.isFinal(); }
    public boolean isStatic(){ return mv.isStatic(); }
    public boolean isGood()  { return (!(mv instanceof LocalType)); }
    public boolean isIfr()   { return (mv instanceof InstField); }
    public boolean canEscape() { return mv.canEscape(); }
}
