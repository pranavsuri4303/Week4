package ss.week4;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class MapUtil {
    //@ requires map != null;
    //@ ensures \result <==> (\forall K k1, k2 ; map.containsKey(k1) && map.containsKey(k2) && !k1.equals(k2) ==> !map.get(k1).equals(map.get(k2)));
    public static <K, V> boolean isOneOnOne(Map<K, V> map) {
        Set<V> seen = new HashSet<>();
        for (V value : map.values()) {
            if (!seen.add(value)) {
                return false;
            }
        }
        return true;
    }

    //@ requires map != null && range != null;
    //@ ensures \result <==> (\forall V value; range.contains(value); map.values().contains(value));
    public static <K, V> boolean isSurjectiveOnRange(Map<K, V> map, Set<V> range) {
        for (V value : range) { // every element in the output set is not left unused
            if (!map.values().contains(value)) {
                return false;
            }
        }
        return true;
    }

    //@ requires map != null;
    //@ ensures \result != null;
    //@ ensures (\forall K k; map.containsKey(k); \result.containsKey(map.get(k)) && \result.get(map.get(k)).contains(k));
    public static <K, V> Map<V, Set<K>> inverse(Map<K, V> map) {
        Map<V, Set<K>> result = new HashMap<>();
        for (K key : map.keySet()) {
            V value = map.get(key);
            if (!result.containsKey(value)) {
                Set<K> keys = new HashSet<>();
                keys.add(key);
                result.put(value, keys);
            } else {
                result.get(value).add(key);
            }
        }
        return result;
    }

    //@ requires map != null;
    //@ ensures (\result == null) <==> !isOneOnOne(map);
    //@ ensures (\result != null) ==> (\forall K k; map.containsKey(k); \result.get(map.get(k)).equals(k));
    public static <K, V> Map<V, K> inverseBijection(Map<K, V> map) { // no two inputs give the same output and every output is used
        if (!isOneOnOne(map)) {
            return null;
        }
        Map<V, K> result = new HashMap<>();
        for (Map.Entry<K, V> entry : map.entrySet()) {
            result.put(entry.getValue(), entry.getKey());
        }
        return result;
    }

    //@requires f != null && g != null;
    //@ ensures \result <==> g.keySet().containsAll(f.values());
    public static <K, V, W> boolean compatible(Map<K, V> f, Map<V, W> g) {
        return g.keySet().containsAll(f.values()); // you can compose g(f(x)) only if every output of f is a valid input for g
    }


    //@ ensures \result.keySet().equals(f.keySet());
    //@ ensures (\forall K k; f.containsKey(k); \result.get(k).equals(g.get(f.get(k))));
    public static <K, V, W> Map<K, W> compose(Map<K, V> f, Map<V, W> g) {
        // for each key k in f compute v=f.get(k), compute w=g.get(v) and store k->w in the result
        Map<K, W> result = new HashMap<>();
        for (K key : f.keySet()) {
            V mid = f.get(key);
            W out = g.get(mid);
            result.put(key, out);
        }
        return result;
    }
}