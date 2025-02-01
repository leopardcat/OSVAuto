imports basic

predicate unique(Seq<int> a) {
    forall (int i, int j) {
        0 <= i && i < |a| &&
        0 <= j && j < |a| && i != j -> a[i] != a[j]
    }
}

query inlist_remove {
    fixes a: Seq<int>;
    fixes b: Seq<int>;
    fixes k: int;
    assumes unique(a);
    assumes 0 <= k && k < |a|;
    assumes b == seq_remove(k, a);
    shows forall (int m) {
        0 <= m && m < |b| -> b[m] != a[k]
    }
    proof { seq_auto }
}
