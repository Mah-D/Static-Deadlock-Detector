/**************************************************************************
 * @author Mahdi Eslamimehr
 * @version 0.1
 ***************************************************************************/

package ContractGen;

public class Edge {
    public LockNode from;
    public LockNode to;
    public Edge(LockNode from, LockNode to) {
        this.from = from; this.to = to;
    }

    public Edge(Edge e) {
        this.from = new LockNode(e.from);
        this.to = new LockNode(e.to);
    }
    public Edge sub(Synonym before, Aggregate after) {
        LockNode nfrom=null, nto=null;
        if (from!=null) nfrom = new LockNode(from);
        if (to!=null)   nto   = new LockNode(to);
        nfrom.replace(before, after);
        nto.replace(before, after);
        return new Edge(nfrom, nto);
    }
    public int hashCode() {
        return ((from==null)? 131: from.hashCode()) + 
               (73*((to==null)? 233 : to.hashCode()));
    }
    public boolean equals(Object o) {
        Edge e = (Edge) o;
        boolean f1 = (from==null); boolean of1 = (e.from==null);
        boolean f2 = (to==null);   boolean of2 = (e.to==null);
        return ((f1&& f2) ? (of1&&of2)   
                          : (f1 ? (of1&&to.equals(e.to)) 
                                : (f2 ? (of2&&from.equals(e.from)) 
                                      : (from.equals(e.from)&&to.equals(e.to)) 
                                  )
                            )
                );
    }
    public String toString() {
        return "("+from+" , "+to+")";
    }
}
