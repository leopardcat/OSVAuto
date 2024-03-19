// Type of pairs
datatype Prod<U, V> =
    pair (U fst, V snd)

// Type of natural numbers
datatype nat =
    zero
    | succ (nat n)

// List datatype
datatype List<E> =
    nil
    | cons (E ele, List<E> rest)

// Option datatype
datatype Option<T> =
    none
    | some (T val)
