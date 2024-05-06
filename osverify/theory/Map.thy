// Map datatype
axiomtype Map<K, V>

// Map indom
axiomfunc indom<K, V> : K -> Map<K, V> -> bool

// Map get
axiomfunc get<K, V> : K -> Map<K, V> -> V

// Empty map
axiomfunc emptyMap<K, V> : Map<K, V>

// Update map
axiomfunc updateMap<K, V> : K -> V -> Map<K, V> -> Map<K, V>

// Map empty
predicate isEmpty(Map<K, V> m) {
    forall (K k) {
        !indom(k, m)
    }
}

// Map subseteq, represents m1 is a subset of m2
predicate subseteq<K, V>(Map<K, V> m1, Map<K, V> m2) {
    forall (K k) {
        indom(k, m1) -> indom(k, m2) && get(k, m1) == get(k, m2)
    }
}

// Map join
predicate join<K, V>(K key, V value, Map<K, V> map_ori, Map<K, V> map_new) {
    !indom(key, map_ori) && indom(key, map_new) && get(key, map_new) == value &&
    forall (K k) {
        k != key -> indom(k, map_ori) == indom(k, map_new) &&
                    (indom(k, map_ori) -> get(k, map_ori) == get(k, map_new))
    }
}

// mapUpdate, assume key is already in map
predicate mapUpdate<K, V>(K key, V value, Map<K,V> map_ori, Map<K, V> map_new) {
    indom(key, map_new) && get(key, map_new) == value &&
    forall (K k) {
        k != key -> indom(k, map_ori) == indom(k, map_new) &&
                    (indom(k, map_ori) -> get(k, map_ori) == get(k, map_new))
    }
}

// sigJoin, sigmap only contains one entry
predicate sigJoin<K, V>(K key, V value, Map<K, V> sigmap) {
    forall (K k) {
        (k != key -> !indom(k, sigmap)) &&
        (k == key -> indom(k, sigmap))
    }
}

// Map remove
predicate remove<K, V>(K key, Map<K, V> map_ori, Map<K, V> map_new) {
    forall (K k) {
        (k != key -> indom(k, map_ori) == indom(k, map_new) &&
                     (indom(k, map_ori) -> get(k, map_ori) == get(k, map_new))) &&
        (k == key -> indom(k, map_ori) && !indom(k, map_new))
    }
}

// MapEq
predicate mapEq<K, V>(Map<K, V> m1, Map<K, V> m2) {
    forall (K k) {
        indom(k, m1) == indom(k, m2) && 
        (indom(k, m1) -> get(k, m1) == get(k, m2))
    }
}

// Map disjoint
predicate disjoint<K, V>(Map<K, V> m1, Map<K, V> m2) {
    forall (K k) {
        !indom(k, m1) || !indom(k, m2)
    }
}

// Map merge
predicate merge<K, V>(Map<K, V> m1, Map<K, V> m2, Map<K, V> m_new) {
    forall (K k) {
        (indom(k, m1) || indom(k, m2) -> indom(k, m_new)) &&
        (indom(k, m_new) -> indom(k, m1) || indom(k, m2)) &&
        (indom(k, m1) -> get(k, m1) == get(k, m_new)) &&
        (indom(k, m2) -> get(k, m2) == get(k, m_new))
    }
}

// Map minus
predicate minus<K, V>(Map<K, V> m1, Map<K, V> m2, Map<K, V> m_new) {
    forall (K k) {
        (indom(k, m2) -> !indom(k, m_new)) &&
        (indom(k, m_new) -> !indom(k, m2) && indom(k, m1)) &&
        (indom(k, m1) && !indom(k, m2) -> indom(k, m_new) && get(k, m1) == get(k, m_new))
    }
}

del_attrib rewrite for isEmpty_def, subseteq_def, join_def, remove_def, mapEq_def,
                       disjoint_def, merge_def, minus_def, mapUpdate_def
