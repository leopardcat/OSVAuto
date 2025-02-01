imports basic

axiomfunc P: int32u -> bool

query example1 {
    fixes p: Map<int, Seq<int32u> >;
    assumes get(2, p) == get(0, p) ++  get(1, p);
    assumes get(3, p) == get(1, p) ++ get(0, p);
    assumes forall (int i) {
        i >= 0 && i < |get(0, p)| + |get(1, p)| -> P(get(2, p)[i])
    };
    shows forall (int k) {
        k >= 0 && k < |get(0, p)| + |get(1, p)| -> P(get(3, p)[k])
    }
    proof { seq_auto }
}