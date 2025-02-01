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

axiom map_equals {
    type K;
    type V;
    fixes m1: Map<K, V>;
    fixes m2: Map<K, V>;
    shows (m1 == m2) == (
        forall (K k) {
            indom(k, m1) == indom(k, m2)
         } &&
        forall (K k in m1) {
            (indom(k, m1) -> get(k, m1) == get(k, m2))
        }
    )
}

axiom indom_update {
    type K;
    type V;
    fixes k1: K;
    fixes k2: K;
    fixes v: V;
    fixes m: Map<K, V>;
    shows indom(k1, updateMap(k2, v, m)) == ((k1 == k2) || indom(k1, m))
}

axiom get_update {
    type K;
    type V;
    fixes k1: K;
    fixes k2: K;
    fixes v: V;
    fixes m: Map<K, V>;
    shows get(k1, updateMap(k2, v, m)) == (
        if (k1 == k2) {
            v
        } else {
            get(k1, m)
        })
}

axiom indom_ite {
    type K;
    type V;
    fixes cond: bool;
    fixes m1: Map<K, V>;
    fixes m2: Map<K, V>;
    fixes k: K;
    shows indom(k, if (cond) {m1} else {m2}) ==
        if (cond) {indom(k, m1)} else {indom(k, m2)}
}

axiom get_ite {
    type K;
    type V;
    fixes cond: bool;
    fixes m1: Map<K, V>;
    fixes m2: Map<K, V>;
    fixes k: K;
    shows get(k, if (cond) {m1} else {m2}) ==
        if (cond) {get(k, m1)} else {get(k, m2)}
}
