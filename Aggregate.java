/**************************************************************************
 * @author Mahdi Eslamimehr
 * @version 0.1
 ***************************************************************************/

package ContractGen;
import java.util.HashSet;
import java.util.Iterator;

public class Aggregate extends HashSet { 
    public Aggregate(HashSet c) { 
        super(c);
    }
    public Aggregate() { 
        super(); 
    }
    public Aggregate(Synonym c) {
        super();
        add(c);
    }
    public void replace(Synonym replaceThis, Aggregate withThis) {
        Aggregate iBecomeThis = new Aggregate();
        InstField I = null;
        Iterator it = iterator();
        while(it.hasNext()) {
            Synonym whatWas = (Synonym) it.next();
            if (whatWas.equals(replaceThis)) {
                iBecomeThis.addAll(withThis);
            } else if (whatWas.isIfr() && (I = (InstField) whatWas.v()).base().equals(replaceThis)) {
                    for (Iterator wit = withThis.iterator(); wit.hasNext(); ) {
                        Synonym newBase = (Synonym) wit.next();
                        Synonym syn = new Synonym(newBase, I.field());
                        iBecomeThis.add(syn);
                    }
            } else { 
                iBecomeThis.add(whatWas);
            }
        }
        clear();
        addAll(iBecomeThis);
    }
    public int hashCode() {
        return super.hashCode();
    }
    public boolean equals(Object o) {
        Aggregate a = (Aggregate) o;
        return super.equals((HashSet) a);
    }
}
