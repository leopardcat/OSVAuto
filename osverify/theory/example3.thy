imports basic

predicate unique(Seq<int> a) {
    forall (int i, int j) {
        0 <= i && i < |a| &&
        0 <= j && j < |a| && i != j -> a[i] != a[j]
    }
}

predicate rows_unique(Seq<Seq<int> > a) {
    forall (int k) {
        0 <= k && k < |a| -> unique(a[k])
    }
}

query rows_unique_remove {
    fixes a : Seq<Seq<int> >;
    fixes b : Seq<Seq<int> >;
    fixes x : int;
    assumes 0 <= x && x < |a|;
    assumes |b| == |a|;
    assumes b[x] == seq_remove(0, a[x]);
    assumes forall (int y) {
                0 <= y && y < |a| -> y != x -> a[y] == b[y]
            };
    assumes rows_unique(a);
    shows rows_unique(b)
    proof {
        seq_auto
    }
}
