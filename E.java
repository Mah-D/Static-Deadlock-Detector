/**************************************************************************
 * @author Mahdi Eslamimehr
 * @version 0.1
 ***************************************************************************/

package ContractGen;
import java.util.HashMap;

public final class E {
    private static String appName;
    private static String m;
    private static HashMap h;
    private static int tabStop = 0;
    public static void push() {
        E.tabStop++;
    }
    public static void pop() {
        if (E.tabStop==0) return;
        E.tabStop--;
    }
    private static String currentTab() {
        String ret = "";
        for (int i=0;i<(E.tabStop-1);i++) ret += (i+".");
        ret += (E.tabStop-1);
        return ret+" ";
    }
    public static void info(String s) {
        m = getMethod();
        System.out.println(currentTab()+"Info ["+m+"] : "+s);
    }
    public static void warn(String s) {
        m = getMethod();
        System.out.println("Warning ["+m+"] : "+s);
    }
    public static void error(String s) {
        m = getMethod();
        System.out.println("Error ["+m+"] : "+s);
    }
    public static void debug(String s) {
        m = getMethod();
        System.out.println(currentTab()+"Debug ["+m+"] : "+s);
    }
    public static void crit(String s) {
        m = getMethod();
        System.out.println(currentTab()+"Critical Error ["+m+"] : "+s);
        System.exit(-1);
    }
    public static void usage(String s) {
        System.out.println(currentTab()+"Usage: "+s);
        System.exit(1);
    }
    public static void FileNotFound(String s) {
        System.out.println(currentTab()+"File <"+s+"> not found. Enter java "+appName+" for usage.");
        System.exit(1);
    }
    public static String getMethod() {
        Throwable t = new Throwable();
        t.fillInStackTrace();
        StackTraceElement e = t.getStackTrace()[2];
        String s = e.getClassName()+"."+e.getMethodName();
        return s;
    }
    public static void p(String s) {
        System.out.print(s);
    }
    public static void pn(String s) {
        System.out.println(currentTab()+s);
    }
    public static void name(String s) { appName = new String(s); }
    public static boolean isOpt(String k, String v) {
        if (!h.containsKey(k)) return false;
        if (((String) h.get(k)).equals(v)) return true;
        return false;
    }
    public static void setOptions(HashMap o) {
        h = new HashMap(o);
    }
    public static void pt() {
        System.out.print(currentTab());
    }

    public static Object getOpt(String s) {
        if (!h.containsKey(s)) return null;
        return h.get(s);
    }
}
