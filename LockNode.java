/**************************************************************************
 * @author Mahdi Eslamimehr
 * @version 0.1
 ***************************************************************************/

package ContractGen;

import java.util.HashSet;
import java.util.HashMap;
import java.util.Iterator;
import soot.Type;
import soot.VoidType;

/******************************************************
 * This class models a single node in the lock graph.
 * A node in the lock graph has two main fields:
 * - the 'l' field (Type: Aggregate),
 * - the 's' field (Type: Boolean).
 * The 'l' field is a collection of all synonymized
 * lock values for a given synchronizing, locking or
 * unlocking instance in the program.
 * The 's' field distinguishes monitors (wt/ntfy) 
 * from locks (synch(x))
 ****************************************************/

public class LockNode {
    private boolean s;   // True for wait/notify
    private Aggregate l; // The actual lock value

    // For simple cycle check
    public int visited = 0;

    // For Tarjan decomposition
    public int index;
    public int lowlink;

    /*****************************
     * Construct a new Locknode.
     ***************************/
    public LockNode(Aggregate l, boolean s) {
        this.l = l;
        this.s = s;
    }

    // Deep copy
    public LockNode(LockNode o) {
        s = o.s;
        l = new Aggregate(o.l);
    }
    /**************************************************
     * Returns the 'l' field of a lock node. 
     ************************************************/
    public Aggregate v() { return l; }
    /**************************************************
     * Returns the 's' field of a lock node. 
     ************************************************/
    public boolean isSynch() { return s; }
    public String toString() { return (s?"M":"L")+","+l; }
    /**************************************************
     * Replace the value _old in the Locknode with 
     * value _new.
     ************************************************/
    public void replace(Synonym _old, Aggregate _new) { 
        l.replace(_old, _new); 
    }
    public int hashCode() { return ((s?101:353)+l.hashCode()); }
    public boolean equals(Object o) {
        LockNode ln = (LockNode) o;
        // System.out.println("\nComparing >>"+L+"<< with >>"+toString()+"<<");
        // System.out.println("\t His hashCode = "+L.hashCode()+", my hashCode = "+hashCode()+".");
        // System.out.println("\t His LV's hashCode = "+L.l.hashCode()+", my LV's hashCode = "+l.hashCode()+".\n");
        return ((ln.s==s) && (ln.l.equals(l)));
    }
    private static HashMap lockNodes = null;
    public Type getType() {
        if (!l.iterator().hasNext()) {
            E.error("Empty lock node was found.");
            return VoidType.v();
        }
        return ((Synonym) l.iterator().next()).getType();
    }
    public String getFullType() {
        if (l.isEmpty() || !l.iterator().hasNext()) return VoidType.v().toString();
        return ((Synonym) l.iterator().next()).fullType();
    }
    public boolean isFinal() {
        if (l.isEmpty() || !l.iterator().hasNext()) return true;
        return ((Synonym) l.iterator().next()).isFinal();
    }
    public boolean isStatic() {
        if (l.isEmpty() || !l.iterator().hasNext()) return true;
        return ((Synonym) l.iterator().next()).isStatic();
    }

    public boolean isPrivateOf(HashSet c) {
        if (l.isEmpty() || !l.iterator().hasNext()) return false;
        Synonym syn = (Synonym) l.iterator().next();
        if (syn.isIfr()) {
            InstField I = (InstField) syn.v();
            String bType = I.base().fullType();
            if (c.contains(bType)) return true;
        }
        return false;
    }
}
