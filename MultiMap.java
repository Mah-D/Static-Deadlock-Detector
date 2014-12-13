/**************************************************************************
 * @author Mahdi Eslamimehr
 * @version 0.1
 ***************************************************************************/


package ContractGen;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;
import java.util.Iterator;
import java.util.Map;

public class MultiMap {
    private HashMap _hash;
    public MultiMap() {
        _hash = new HashMap();
    }
    public MultiMap (MultiMap m) {
        _hash = new HashMap();
        _hash.putAll(m._hash);
    }
    public Set entrySet() {
        return _hash.entrySet();
    }
    /****************************************************
      * put(x, y): puts y into an existing set of values
      *            for the key 'x'
      **************************************************/
    public void put (Object key, Object value) {
        HashSet values = null;
        if (_hash.containsKey(key)) 
                values = (HashSet) _hash.get(key);
        if (values==null) values = new HashSet();
        if (value!=null) values.add(value);
        _hash.put(key,values);
    }
    /*****************************************************
      * putMap(o): Copies the entire multimap o into this.
      ***************************************************/
    public void putMap(MultiMap o) {
        _hash.putAll(o._hash);
    }
    
    /*****************************************************
      * merge(MultiMap o): Merges using mergeMap().
      * For all keys in 'this', add all values for corr.
      * keys in o to the respective keys.
      ***************************************************/
    public void merge(MultiMap o) {
        for (Iterator it = o._hash.keySet().iterator(); it.hasNext(); ) {
            Object hisKey = it.next();
            Object hisVals = o._hash.get(hisKey);
            mergeMap(hisKey, hisVals);
        }
    }
    /******************************************************
      * Returns the set of all values mapped to given key.
      ****************************************************/
    public HashSet get(Object key) {
        return (HashSet) _hash.get(key);
    }
    /********************************************************
      * Add all values from newValues into the set of values
      * associated with key.
      ******************************************************/
    public void mergeMap (Object key, Object newValues) {
        // System.out.println("Called mergeMap");
        HashSet values = null;
        if (_hash.containsKey(key)) {
            values = (HashSet) _hash.get(key);
            if (values==null) values = new HashSet();
        } else values = new HashSet();
        if (newValues!=null) values.addAll((HashSet) newValues);
        _hash.put (key, values);
    }
    /********************************************************
      * Add new mapping [key, values] to multi-map.
      ******************************************************/
    public void putAll(Object key, Object values) {
        _hash.put(key, values);
    }
    public boolean equals(Object o) {
        MultiMap m = (MultiMap) o;
        return (_hash.equals(m._hash));
    }
    public int hashCode() {
        return _hash.hashCode();
    }
    public Set keySet() {
        return (Set) _hash.keySet();
    }
    public boolean containsKey(Object x) {
        return _hash.containsKey(x);
    }
    public int size() {
        return _hash.size();
    }
    public boolean existsEdge(Object n1, Object n2) {
        return (containsKey(n1) && get(n1).contains(n2));
    }
    public boolean isEmpty() {
        return _hash.isEmpty();
    }
    public void clear() {
        _hash.clear();
    }
    public String toString() {
        return _hash.toString();
    }
    public void remove(Object key, Object value) {
        if (!_hash.containsKey(key)) return;
        HashSet vals = (HashSet) _hash.get(key);
        vals.remove(value);
        if (vals.isEmpty()) _hash.remove(key);
        else putAll(key, vals);
    }
}
