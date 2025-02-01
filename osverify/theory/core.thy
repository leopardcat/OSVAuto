// Type of pairs
enum Prod<U, V> =
    pair (U fst, V snd)

// Option datatype
enum Option<T> =
    none | some (T val)

axiomfunc max : int -> int -> int
axiomfunc min : int -> int -> int
