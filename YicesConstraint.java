

/**************************************************************************
 * @author Mahdi Eslamimehr
 * @version 0.1
 ***************************************************************************/


package ContractGen;
import java.util.HashSet;
import java.util.Iterator;

public class YicesConstraint {
    private String op;
    private String lhs;
    private String rhs;
    private static HashSet vars = new HashSet();

    public YicesConstraint(String op, String lhs, String rhs) {
        this.op = op;
        this.lhs = lhs;
        this.rhs = rhs;
        YicesConstraint.vars.add(lhs);
        YicesConstraint.vars.add(rhs);
    }

    public static void clearInits() {
        YicesConstraint.vars.clear();
    }

    public String toString() {
        return "(assert ("+op+" "+lhs+" "+rhs+"))\n";
    }
    public static String initVars() {
        String ret = new String();
        for(Iterator it = vars.iterator(); it.hasNext(); ) {
            String var = (String) it.next();
            ret = ret + "(define "+var+"::int)\n";
        }
        return ret;
    }

}
