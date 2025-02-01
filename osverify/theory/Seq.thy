imports core
imports Map

// Sequence datatype

/**
 * Each sequences of type Seq<T> is encoded in Z3 as a length
 * of type int, and an uninterpreted function int -> T.
 *
 * More precisely, for a sequence with name `a`, we associate
 * in Z3 an integer `_length_a`, and an uninterpreted function
 * `_seq_a` of type int -> T.
 *
 * For sequences for which each entry is also a sequence, we
 * define a sequence of lengths. For example, with `a` a sequence
 * of sequences, define a variable `_length_a`, so that:
 *
 *   |a|[i] = _length_a[i]
 */

axiomtype Seq<T>

// Length of a sequence
axiomfunc seq_length<T>: Seq<T> -> int

// Index access in a sequence
axiomfunc seq_index<T>: int -> Seq<T> -> T

// Repetition
axiomfunc seq_repeat<T>: T -> int -> Seq<T>

// Append
axiomfunc seq_append<T>: Seq<T> -> Seq<T> -> Seq<T>

// Slice
axiomfunc seq_slice<T>: int -> int -> Seq<T> -> Seq<T>

// Update of a sequence
axiomfunc seq_update<T>: int -> T -> Seq<T> -> Seq<T>

// Remove
axiomfunc seq_remove<T>: int -> Seq<T> -> Seq<T>

axiomfunc seq_cons<T>: T -> Seq<T> -> Seq<T>

// Reverse
axiomfunc seq_rev<T>: Seq<T> -> Seq<T>

axiom seq_equals {
    type T;
    fixes a: Seq<T>;
    fixes b: Seq<T>;
    shows (a == b) == (
         |a| == |b| &&
         forall (int i) {
              i >= 0 && i < |a| -> a[i] == b[i]
         }
    )
}

axiom seq_append_length {
    type T;
    fixes a: Seq<T>;
    fixes b: Seq<T>;
    shows |a ++ b| == |a| + |b|
}

axiom seq_append_index {
    type T;
    fixes a: Seq<T>;
    fixes b: Seq<T>;
    fixes i: int;
    shows (a ++ b)[i] ==
        if (0 <= i && i < |a|) {
            a[i]
        } else {
            if (|a| <= i && i < |a| + |b|) {
                b[i - |a|]
            } else {
                default
            }
        }
}

axiom seq_cons_length {
    type T;
    fixes x: T;
    fixes a: Seq<T>;
    shows |x :: a| == |a| + 1
}

axiom seq_cons_index {
    type T;
    fixes i: int;
    fixes x: T;
    fixes a: Seq<T>;
    shows (x :: a)[i]==
        if (i == 0) {
            x
        } else {
            if (1 <= i && i < |a| + 1) {
                a[i - 1]
            } else {
                default
            }
        }
}

axiom seq_repeat_length {
    type T;
    fixes t: T;
    fixes n: int;
    shows |seq_repeat(t, n)| == max(0, n)
}

axiom seq_repeat_index {
    type T;
    fixes t: T;
    fixes n: int;
    fixes i: int;
    shows (seq_repeat(t, n))[i] ==
        if (0 <= i && i < n) {
            t
        } else {
            default
        }
}

axiom seq_slice_length {
    type T;
    fixes i: int;
    fixes j: int;
    fixes a: Seq<T>;
    shows |a[i:j]| ==
        if (max(i, 0) < min(j, |a|)) {
            min(j, |a|) - max(i, 0)
        } else {
            0
        }
}

axiom seq_slice_index {
    type T;
    fixes i: int;
    fixes j: int;
    fixes k: int;
    fixes a: Seq<T>;
    shows a[j : k][i] ==
        if (0 <= i && i + max(j, 0) < min(k, |a|)) {
            a[i + max(j, 0)]
        } else {
            default
        }
}

axiom seq_update_length {
    type T;
    fixes i: int;
    fixes x: T;
    fixes a: Seq<T>;
    shows |seq_update(i, x, a)| == |a|
}

axiom seq_update_index {
    type T;
    fixes i: int;
    fixes j: int;
    fixes x: T;
    fixes a: Seq<T>;
    shows seq_update(j, x, a)[i] ==
        if (i == j) {
            x
        } else {
            a[i]
        }
}

axiom seq_remove_length {
    type T;
    fixes i: int;
    fixes xs: Seq<T>;
    shows |seq_remove(i, xs)| == max(0, |xs| - 1)
}

axiom seq_remove_index {
    type T;
    fixes i: int;
    fixes j: int;
    fixes xs: Seq<T>;
    shows seq_remove(i, xs)[j] ==
        if (0 <= j && j < i) {
            xs[j]
        } else {
            if (i <= j && j < |xs| - 1) {
                xs[j + 1]
            } else {
                default
            }
        }
}

axiom seq_rev_length {
    type T;
    fixes a: Seq<T>;
    shows |seq_rev(a)| == |a|
}

axiom seq_rev_index {
    type T;
    fixes i: int;
    fixes a: Seq<T>;
    shows seq_rev(a)[i] == a[|a| - 1 - i]
}

axiom seq_ite_index {
    type T;
    fixes cond: bool;
    fixes i: int;
    fixes s1: Seq<T>;
    fixes s2: Seq<T>;
    shows (if (cond) {s1} else {s2})[i] ==
        if (cond) {s1[i]} else {s2[i]}
}

axiom seq_ite_length {
    type T;
    fixes cond: bool;
    fixes s1: Seq<T>;
    fixes s2: Seq<T>;
    shows |if (cond) {s1} else {s2}| ==
        if (cond) { |s1| } else { |s2| }
}

// Range functions
axiomfunc range : int32u -> int32u -> Seq<int32u>
axiomfunc range8 : int8u -> int8u -> Seq<int8u>
