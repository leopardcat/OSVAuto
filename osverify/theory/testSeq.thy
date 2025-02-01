imports seq

query seq_append_assoc {
    type T;
    fixes xs: Seq<T>;
    fixes ys: Seq<T>;
    fixes zs: Seq<T>;
    shows forall (int i) {
        (xs ++ ys ++ zs)[i]==
        (xs ++ (ys ++ zs))[i]
    }
    proof { seq_auto }
}

query seq_append_assoc2 {
    type T;
    fixes xs: Seq<T>;
    fixes ys: Seq<T>;
    fixes zs: Seq<T>;
    shows xs ++ ys ++ zs ==
          xs ++ (ys ++ zs)
    proof { seq_auto }
}

query seq_append_repeat {
    type T;
    fixes x: T;
    fixes m: int;
    fixes n: int;
    assumes m >= 0;
    assumes n >= 0;
    shows seq_repeat(x, m + n) ==
          seq_repeat(x, m) ++ seq_repeat(x, n)
    proof { seq_auto }
}

axiomfunc P: int32u -> bool
/*
query seq_append_repeat_quantified {
    fixes x: int32u;
    fixes n: int;
    fixes m: int;
    fixes a: Seq<int32u>;
    assumes a == seq_repeat(x, n);
    assumes m <= n;
    assumes forall (int i) {
        i >= 0 && i < n -> P(seq_index(i, a))
    };
    shows forall (int k) {
        k >= 0 && k < m -> P(seq_index(k, a))
    }
    proof { seq_auto }
}
*/
query seq_append_slice {
    type T;
    fixes xs: Seq<T>;
    fixes i: int;
    fixes j: int;
    fixes k: int;
    assumes 0 <= i && i <= j && j <= k && k <= |xs|;
    shows xs[i : k] ==
          xs[i : j] ++  xs[j : k]
    proof { seq_auto }
}

query seq_append_slice_quantified {
    fixes xs: Seq<int32u>;
    fixes m: int;
    assumes m >= 0;
    assumes m <= |xs|;
    assumes forall (int i) {
        i >= 0 && i < m ->
        P(xs[0:m][i])
    };
    assumes forall (int i) {
        i >= 0 && i < |xs| - m ->
        P(xs[m:|xs|][i])
    };
    shows forall (int i) {
        i >= 0 && i < |xs| -> P(xs[i])
    }
    proof { seq_auto }
}

query seq_update_length_eq {
    type T;
    fixes xs: Seq<T>;
    fixes z: T;
    fixes i: int;
    fixes ys: Seq<T>;
    assumes ys == seq_update(i, z, xs);
    assumes i >= 0 && i < |xs|;
    shows |ys| == |xs|
    proof { seq_auto }
}

query seq_update_same {
    type T;
    fixes xs: Seq<T>;
    fixes z: T;
    fixes i: int;
    fixes ys: Seq<T>;
    assumes ys == seq_update(i, z, xs);
    assumes i >= 0 && i < |xs|;
    shows ys[i] == z
    proof { seq_auto }
}

query seq_update_diff {
    type T;
    fixes xs: Seq<T>;
    fixes z: T;
    fixes i: int;
    fixes j: int;
    fixes ys: Seq<T>;
    assumes ys == seq_update(i, z, xs);
    assumes i >= 0 && i < |xs|;
    assumes j >= 0 && j < |xs|;
    assumes i != j;
    shows ys[j] == xs[j]
    proof { seq_auto }
}

query seq_update_cover {
    type T;
    fixes xs: Seq<T>;
    fixes z1: T;
    fixes z2: T;
    fixes i: int;
    fixes ys: Seq<T>;
    fixes zs: Seq<T>;
    assumes ys == seq_update(i, z1, xs);
    assumes zs == seq_update(i, z2, ys);
    assumes i >= 0 && i < |xs|;
    shows zs == seq_update(i, z2, xs)
    proof { seq_auto }
}

query seq_update_disjoint {
    type T;
    fixes xs: Seq<T>;
    fixes z1: T;
    fixes z2: T;
    fixes i: int;
    fixes j: int;
    fixes ys: Seq<T>;
    fixes zs: Seq<T>;
    assumes ys == seq_update(i, z1, xs);
    assumes zs == seq_update(j, z2, ys);
    assumes i >= 0 && i < |xs|;
    assumes j >= 0 && j < |xs|;
    assumes i != j;
    shows zs == seq_update(i, z1, seq_update(j, z2, xs))
    proof { seq_auto }
}

query seq_length_remove {
    type T;
    fixes xs: Seq<T>;
    fixes i: int;
    assumes 0 <= i && i < |xs|;
    shows |seq_remove(i, xs)| == |xs| - 1
    proof { seq_auto }
}

query seq_inlist_remove {
    type T;
    fixes xs: Seq<T>;
    fixes ys: Seq<T>;
    assumes forall (int i, int j) {
        0 <= i && i < |xs| &&
        0 <= j && j < |xs| && i != j ->
        xs[i] != xs[j]
    };
    fixes k: int;
    assumes 0 <= k && k < |xs|;
    assumes ys == seq_remove(k, xs);
    shows forall (int j) {
        0 <= j && j < |ys| -> ys[j] != xs[k]
    }
    proof { seq_auto }
}

query seq_append_remove {
    type T;
    fixes xs: Seq<T>;
    fixes ys: Seq<T>;
    fixes i: int;
    assumes 0 <= i && i < |xs|;
    shows seq_remove(i, xs) ++ ys == seq_remove(i, xs ++ ys)
    proof { seq_auto }
}

query seq_append_remove2 {
    type T;
    fixes xs: Seq<T>;
    fixes ys: Seq<T>;
    fixes i: int;
    assumes 0 <= i && i < |ys|;
    shows xs ++ seq_remove(i, ys) == seq_remove(|xs| + i, xs ++ ys)
    proof { seq_auto }
}

query seq_append3_equals {
    type T;
    fixes l11: Seq<T>;
    fixes l12: Seq<T>;
    fixes v1: T;
    fixes l21: Seq<T>;
    fixes l22: Seq<T>;
    fixes v2: T;
    fixes l1: Seq<T>;
    fixes l2: Seq<T>;
    assumes l1 == l11 ++ v1 :: l12;
    assumes l2 == l21 ++ v2 :: l22;
    assumes |l11| == |l21|;
    assumes l1 == l2;
    shows l11 == l21 && v1 == v2 && l12 == l22
    proof { seq_auto }
}

query test_map_update {
    fixes m1: Map<int, int32u>;
    fixes m2: Map<int, int32u>;
    fixes b: bool;
    fixes x: int32u;
    assumes b -> m2 == updateMap(0, x, m1);
    assumes !b -> m2 == m1;
    assumes P(x);
    assumes forall (int k in m1) {
                P(get(k, m1))
            };
    shows forall (int k in m2) {
              P(get(k, m2))
          }
    proof { seq_auto }
}
