/**************************************************************************
 * @author Mahdi Eslamimehr
 * @version 0.1
 ***************************************************************************/


package ContractGen;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.HashMap;

public class Order {
    /* maps locknode to generic name */
    public HashMap mapping;
    /* maps int to generic name */
    public ArrayList order;
    /* maps locknode to int */
    private HashMap reverse;

    private String prefix;

    public Order(String prefix) {
        this.prefix = new String(prefix);
        mapping = new HashMap();
        order = new ArrayList();
        reverse = new HashMap();
    }

    public void add(LockNode ln) {
        int index = order.size();
        String str = makeGenericName(index);
        order.add(str);
        mapping.put(str, ln);
        reverse.put(ln, new Integer(index));
    }

    public LockNode getLockNode(int i) {
        String s = makeGenericName(i);
        // E.pn("Mapping was " +mapping+ " Searching for "+s+" for index "+i);
        if (mapping.containsKey(s)) {
            LockNode l = (LockNode) mapping.get(s);
            // E.pn("Found "+s+", returning "+l+" type = "+l.getType());
            return l;
        }
        return null;
    }

    public String getGenericName(LockNode l) {
        int index = getIndex(l); 
        return makeGenericName(index);
    }

    public String makeGenericName(int index) {
        return prefix + (new Integer(index)).toString();
    }
        
    public int getIndex(LockNode l) {
        if (!reverse.containsKey(l)) return -1;
        return ((Integer) reverse.get(l)).intValue();
    }

    public int size() {
        return order.size();
    }

    public String toString() {
        return "\nOrder = "+order+"\n" + 
               "Mapping = "+mapping+"\n"+
               "Reverse = "+reverse+"\n";
    }

    private String dashes = "------------------------------------------------------------------\n";
    public String printVarMap() {
        String str = "";
        for (Iterator it = mapping.keySet().iterator(); it.hasNext(); ) {
            String s = (String) it.next();
            LockNode l = (LockNode) mapping.get(s);
            str += dashes;
            str += ("Lock Node = "+l.toString()+"\n");
            str += ("Type = "+l.getFullType()+"\n");
            str += ("Aliased to "+s+"\n");
            str += dashes;
        }
        return str;
    }
}
