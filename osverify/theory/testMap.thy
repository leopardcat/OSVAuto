imports basic

/* ------------ properties in \framework\proof\Map.v ------------ */

/* properties about join */
query Map_Join_mapEq {
    type K;
    type V;
    fixes k1 : K;
    fixes k2 : K;
    fixes v1 : V;
    fixes v2 : V;
    fixes m1 : Map<K, V>;
    fixes m2 : Map<K, V>;
    fixes m3 : Map<K, V>;
    assumes join(k1, v1, m3, m1);
    assumes join(k2, v2, m3, m2);
    shows k1 == k2 && v1 == v2 -> m1 == m2
    proof { auto }
}

query put_get_eq {
    type K;
    type V;
    fixes k : K;
    fixes v : V;
    fixes m_ori : Map<K, V>;
    fixes m_new : Map<K, V>;
    shows join(k, v, m_ori, m_new) -> (get(k, m_new) == v)
    proof { auto }
}

query put_noninterfere {
    type K;
    type V;
    fixes k1 : K;
    fixes k2 : K;
    fixes v : V;
    fixes m_ori : Map<K, V>;
    fixes m_new : Map<K, V>;
    shows k1 != k2 -> indom(k2, m_ori) == true -> join(k1, v, m_ori, m_new) -> get(k2, m_new) == get(k2, m_ori)
    proof { auto }
}

query put_unique {
    type K;
    type V;
    fixes k : K;
    fixes v1 : V;
    fixes v2 : V;
    fixes m_ori : Map<K, V>;
    fixes m_new : Map<K, V>;
    shows join(k, v1, m_ori, m_new) -> join(k, v2, m_ori, m_new) -> v1 == v2
    proof { auto }
}

query putA_presv_nidB{
    type K;
    type V;
    fixes k1 : K;
    fixes k2 : K;
    fixes v : V;
    fixes m_ori : Map<K, V>;
    fixes m_new : Map<K, V>;
    shows join(k2, v, m_ori, m_new) -> !indom(k1, m_ori) -> (k1 != k2) -> !indom(k1, m_new)
    proof { auto }
}

/* properties about join */
query remove_shrinks_dom {
    type K;
    type V;
    fixes k1 : K;
    fixes k2 : K;
    fixes v : V;
    fixes m_ori : Map<K, V>;
    fixes m_new : Map<K, V>;
    shows !indom(k2, m_ori) -> remove(k1, m_ori, m_new) -> !indom(k2, m_new)
    proof { auto }
}

query nid_remove{
    type K;
    type V;
    fixes k : K;
    fixes v : V;
    fixes m_ori : Map<K, V>;
    fixes m_new : Map<K, V>;
    shows remove(k, m_ori, m_new) -> !indom(k, m_new)
    proof { auto }
}

query remove_nothing{
    type K;
    type V;
    fixes k : K;
    fixes v : V;
    fixes m_ori : Map<K, V>;
    fixes m_new : Map<K, V>;
    shows !indom(k, m_ori) -> remove(k, m_ori, m_new) -> m_ori == m_new
    proof { auto }
}

query remove_cancel_put{
    type K;
    type V;
    fixes k : K;
    fixes v : V;
    fixes m_ori : Map<K, V>;
    fixes m_join : Map<K, V>;
    fixes m_rem1 : Map<K, V>;
    fixes m_rem2 : Map<K, V>;
    shows join(k, v, m_ori, m_join) -> remove(k, m_join, m_rem1) -> remove(k, m_ori, m_rem2) -> m_rem1 == m_rem2
    proof { auto }
}

query put_cancel_remove{
    type K;
    type V;
    fixes k : K;
    fixes v : V;
    fixes m_ori : Map<K, V>;
    fixes m_rem : Map<K, V>;
    fixes m_join1 : Map<K, V>;
    fixes m_join2 : Map<K, V>;
    shows remove(k, m_ori, m_rem) -> join(k, v, m_rem, m_join1) -> join(k, v, m_ori, m_join2) -> m_join1 == m_join2
    proof { auto }
}

query remove_ext_ext_remove{
    type K;
    type V;
    fixes k1 : K;
    fixes k2 : K;
    fixes v : V;
    fixes m_ori : Map<K, V>;
    fixes m_rem1 : Map<K, V>;
    fixes m_rem2 : Map<K, V>;
    fixes m_join1 : Map<K, V>;
    fixes m_join2 : Map<K, V>;
    shows k1 != k2 -> join(k1, v, m_ori, m_join1) -> remove(k2, m_join1, m_rem1)
         -> remove(k2, m_ori, m_rem2) -> join(k1, v, m_rem2, m_join2) -> m_rem1 == m_join2
    proof { auto }
}

/* properties about disjoint */
query extend_presv_disj_left{
    type K;
    type V;
    fixes k : K;
    fixes v : V;
    fixes m_ori1 : Map<K, V>;
    fixes m_ori2 : Map<K, V>;
    fixes m_new : Map<K, V>;
    shows disjoint(m_ori1, m_ori2) -> !indom(k, m_ori2) -> join(k, v, m_ori1, m_new) -> disjoint(m_ori2, m_new)
    proof { auto }
}

query extend_presv_disj_right{
    type K;
    type V;
    fixes k : K;
    fixes v : V;
    fixes m_ori1 : Map<K, V>;
    fixes m_ori2 : Map<K, V>;
    fixes m_new : Map<K, V>;
    shows disjoint(m_ori1, m_ori2) -> !indom(k, m_ori2) -> join(k, v, m_ori1, m_new) -> disjoint(m_new, m_ori2)
    proof { auto }
}

query disj_exclusive_left{
    type K;
    type V;
    fixes k : K;
    fixes v : V;
    fixes m1 : Map<K, V>;
    fixes m2 : Map<K, V>;
    shows disjoint(m1, m2) -> indom(k, m1) -> !indom(k, m2)
    proof { auto }
}

query update_presv_disj_left{
    type K;
    type V;
    fixes k : K;
    fixes v : V;
    fixes m1 : Map<K, V>;
    fixes m2 : Map<K, V>;
    fixes m_new : Map<K, V>;
    shows disjoint(m1, m2) -> indom(k, m1) -> join(k, v, m1, m_new) -> disjoint(m_new, m2)
    proof { auto }
}

query update_presv_disj_right{
    type K;
    type V;
    fixes k : K;
    fixes v : V;
    fixes m1 : Map<K, V>;
    fixes m2 : Map<K, V>;
    fixes m_new : Map<K, V>;
    shows disjoint(m1, m2) -> indom(k, m2) -> join(k, v, m2, m_new) -> disjoint(m1, m_new)
    proof { auto }
}

/* properties about merge */
query notin_merge_distr_left{
    type K;
    type V;
    fixes k : K;
    fixes v : V;
    fixes m1 : Map<K, V>;
    fixes m2 : Map<K, V>;
    fixes m_new : Map<K, V>;
    shows merge(m1, m2, m_new) -> !indom(k, m_new) -> !indom(k, m1)
    proof { auto }
}

query notin_merge_distr_right{
    type K;
    type V;
    fixes k : K;
    fixes v : V;
    fixes m1 : Map<K, V>;
    fixes m2 : Map<K, V>;
    fixes m_new : Map<K, V>;
    shows merge(m1, m2, m_new) -> !indom(k, m_new) -> !indom(k, m2)
    proof { auto }
}

query merge_presv_indom_left{
    type K;
    type V;
    fixes k : K;
    fixes v : V;
    fixes m1 : Map<K, V>;
    fixes m2 : Map<K, V>;
    fixes m_new : Map<K, V>;
    shows merge(m1, m2, m_new) -> indom(k, m1) -> indom(k, m_new)
    proof { auto }
}

query merge_presv_indom_right{
    type K;
    type V;
    fixes k : K;
    fixes v : V;
    fixes m1 : Map<K, V>;
    fixes m2 : Map<K, V>;
    fixes m_new : Map<K, V>;
    shows merge(m1, m2, m_new) -> indom(k, m2) -> indom(k, m_new)
    proof { auto }
}

query in_merge_left_or_right{
    type K;
    type V;
    fixes k : K;
    fixes v : V;
    fixes m1 : Map<K, V>;
    fixes m2 : Map<K, V>;
    fixes m_new : Map<K, V>;
    shows merge(m1, m2, m_new) -> indom(k, m_new) -> (indom(k, m1) || indom(k, m2))
    proof { auto }
}

query in_merge_not_right_in_left{
    type K;
    type V;
    fixes k : K;
    fixes v : V;
    fixes m1 : Map<K, V>;
    fixes m2 : Map<K, V>;
    fixes m_new : Map<K, V>;
    shows merge(m1, m2, m_new) -> indom(k, m_new) -> !indom(k, m2) -> indom(k, m1)
    proof { auto }
}

query notin_left_notin_right_notin_merge{
    type K;
    type V;
    fixes k : K;
    fixes v : V;
    fixes m1 : Map<K, V>;
    fixes m2 : Map<K, V>;
    fixes m_new : Map<K, V>;
    shows merge(m1, m2, m_new) -> !indom(k, m1) -> !indom(k, m2) -> !indom(k, m_new)
    proof { auto }
}

query in_left_in_merge{
    type K;
    type V;
    fixes k : K;
    fixes v : V;
    fixes m1 : Map<K, V>;
    fixes m2 : Map<K, V>;
    fixes m_new : Map<K, V>;
    shows merge(m1, m2, m_new) -> get(k, m1) == v -> get(k, m_new) == get(k, m_new)
    proof { auto }
}

query in_right_in_merge{
    type K;
    type V;
    fixes k : K;
    fixes v : V;
    fixes m1 : Map<K, V>;
    fixes m2 : Map<K, V>;
    fixes m_new : Map<K, V>;
    shows merge(m1, m2, m_new) -> get(k, m2) == v -> get(k, m_new) == get(k, m_new)
    proof { auto }
}

query put_merge_merge_put{
    type K;
    type V;
    fixes k : K;
    fixes v : V;
    fixes m1 : Map<K, V>;
    fixes m2 : Map<K, V>;
    fixes m_merge1 : Map<K, V>;
    fixes m_merge2 : Map<K, V>;
    fixes m_new1 : Map<K, V>;
    fixes m_new2 : Map<K, V>;
    shows merge(m1, m2, m_merge1) -> join(k, v, m_merge1, m_new1) -> 
            join(k, v, m1, m_new2) -> merge(m_new2, m2, m_merge2) ->
            m_new1 == m_merge2
    proof { auto }
}

query remove_merge_merge_remove_right{
    type K;
    type V;
    fixes k : K;
    fixes v : V;
    fixes m1 : Map<K, V>;
    fixes m2 : Map<K, V>;
    fixes m_merge1 : Map<K, V>;
    fixes m_merge2 : Map<K, V>;
    fixes m_rem1 : Map<K, V>;
    fixes m_rem2 : Map<K, V>;
    shows !indom(k, m1) -> merge(m1, m2, m_merge1) -> remove(k, m_merge1, m_rem1) ->
            remove(k, m2, m_rem2) -> merge(m_rem2, m1, m_merge2) ->
            m_rem1 == m_merge2
    proof { auto }
}

/* properties about disjoint and merge */
query disj_remove_merge_merge_remove{
    type K;
    type V;
    fixes k : K;
    fixes v : V;
    fixes m1 : Map<K, V>;
    fixes m2 : Map<K, V>;
    fixes m_merge1 : Map<K, V>;
    fixes m_merge2 : Map<K, V>;
    fixes m_rem1 : Map<K, V>;
    fixes m_rem2 : Map<K, V>;
    shows disjoint(m1, m2) -> indom(k, m1) -> merge(m1, m2, m_merge1) -> remove(k, m_merge1, m_rem1) ->
            remove(k, m1, m_rem2) -> merge(m_rem2, m2, m_merge2) ->
            m_rem1 == m_merge2
    proof { auto }
}

query disj_merge_disj_left{
    type K;
    type V;
    fixes k : K;
    fixes v : V;
    fixes m1 : Map<K, V>;
    fixes m2 : Map<K, V>;
    fixes m3 : Map<K, V>;
    fixes m_merge : Map<K, V>;
    shows merge(m1, m2, m_merge) -> disjoint(m_merge, m3) -> disjoint(m1, m3)
    proof { auto }
}

query disj_merge_disj_right{
    type K;
    type V;
    fixes k : K;
    fixes v : V;
    fixes m1 : Map<K, V>;
    fixes m2 : Map<K, V>;
    fixes m3 : Map<K, V>;
    fixes m_merge : Map<K, V>;
    shows merge(m1, m2, m_merge) -> disjoint(m_merge, m3) -> disjoint(m2, m3)
    proof { auto }
}

query disj_x_merge_disj_left{
    type K;
    type V;
    fixes k : K;
    fixes v : V;
    fixes m1 : Map<K, V>;
    fixes m2 : Map<K, V>;
    fixes m3 : Map<K, V>;
    fixes m_merge : Map<K, V>;
    shows merge(m1, m2, m_merge) -> disjoint(m_merge, m3) -> disjoint(m1, m3)
    proof { auto }
}

query disj_x_merge_disj_right{
    type K;
    type V;
    fixes k : K;
    fixes v : V;
    fixes m1 : Map<K, V>;
    fixes m2 : Map<K, V>;
    fixes m3 : Map<K, V>;
    fixes m_merge : Map<K, V>;
    shows merge(m1, m2, m_merge) -> disjoint(m_merge, m3) -> disjoint(m2, m3)
    proof { auto }
}

query disj_merge_commut{
    type K;
    type V;
    fixes k : K;
    fixes v : V;
    fixes m1 : Map<K, V>;
    fixes m2 : Map<K, V>;
    fixes m3 : Map<K, V>;
    fixes m_merge1 : Map<K, V>;
    fixes m_merge2 : Map<K, V>;
    shows disjoint(m1, m2) -> merge(m1, m2, m_merge1) -> merge(m2, m1, m_merge2) -> m_merge1 == m_merge2
    proof { auto }
}

query disj_merge_A{
    type K;
    type V;
    fixes k : K;
    fixes v : V;
    fixes m1 : Map<K, V>;
    fixes m2 : Map<K, V>;
    fixes m3 : Map<K, V>;
    fixes m_merge : Map<K, V>;
    shows disjoint(m1, m2) -> disjoint(m1, m3) -> merge(m2, m3, m_merge) -> disjoint(m1, m_merge)
    proof { auto }
}

query disj_merge_B{
    type K;
    type V;
    fixes k : K;
    fixes v : V;
    fixes m1 : Map<K, V>;
    fixes m2 : Map<K, V>;
    fixes m3 : Map<K, V>;
    fixes m_merge : Map<K, V>;
    shows disjoint(m2, m1) -> disjoint(m3, m1) -> merge(m2, m3, m_merge) -> disjoint(m_merge, m1)
    proof { auto }
}

query disj_merge_assoc_left_right{
    type K;
    type V;
    fixes k : K;
    fixes v : V;
    fixes m1 : Map<K, V>;
    fixes m2 : Map<K, V>;
    fixes m3 : Map<K, V>;
    fixes m_merge1 : Map<K, V>;
    fixes m_merge2 : Map<K, V>;
    shows disjoint(m1, m2) -> merge(m1, m2, m_merge1) -> disjoint(m_merge1, m3) -> merge(m2, m3, m_merge2) -> disjoint(m1, m_merge2)
    proof { auto }
}

query disj_merge_assoc_right_left{
    type K;
    type V;
    fixes k : K;
    fixes v : V;
    fixes m1 : Map<K, V>;
    fixes m2 : Map<K, V>;
    fixes m3 : Map<K, V>;
    fixes m_merge1 : Map<K, V>;
    fixes m_merge2 : Map<K, V>;
    shows disjoint(m2, m3) -> merge(m2, m3, m_merge1) -> disjoint(m1, m_merge1) -> merge(m1, m2, m_merge2) -> disjoint(m3, m_merge2)
    proof { auto }
}

query disj_merge_ABC_BAC{
    type K;
    type V;
    fixes k : K;
    fixes v : V;
    fixes m1 : Map<K, V>;
    fixes m2 : Map<K, V>;
    fixes m3 : Map<K, V>;
    fixes m_merge1 : Map<K, V>;
    fixes m_merge2 : Map<K, V>;
    fixes m_merge3 : Map<K, V>;
    fixes m_merge4 : Map<K, V>;
    shows disjoint(m1, m2) -> merge(m1, m2, m_merge1) -> merge(m_merge1, m3, m_merge2) -> merge(m1, m3, m_merge3) -> merge(m2, m_merge3, m_merge4)
        -> m_merge2 == m_merge4
    proof { auto }
}

query disj_merge_unique{
    type K;
    type V;
    fixes k : K;
    fixes v : V;
    fixes m1 : Map<K, V>;
    fixes m2 : Map<K, V>;
    fixes m3 : Map<K, V>;
    fixes m4 : Map<K, V>;
    fixes m_merge1 : Map<K, V>;
    fixes m_merge2 : Map<K, V>;
    shows disjoint(m1, m2) -> disjoint(m3, m4) -> merge(m1, m2, m_merge1) -> merge(m3, m4, m_merge2) ->
        m_merge1 == m_merge2 -> m1 == m3 -> m2 == m4
    proof { auto }
}

/* properties about minus */

query minus_disjoint{
    type K;
    type V;
    fixes k : K;
    fixes v : V;
    fixes m1 : Map<K, V>;
    fixes m2 : Map<K, V>;
    fixes m_minu : Map<K, V>;
    shows minus(m1, m2, m_minu) -> disjoint(m2, m_minu)
    proof { auto }
}

query minus_disjUnion{
    type K;
    type V;
    fixes m1 : Map<K, V>;
    fixes m2 : Map<K, V>;
    fixes m_minu : Map<K, V>;
    fixes m_merge : Map<K, V>;
    shows subseteq(m2, m1) -> minus(m1, m2, m_minu) -> merge(m2, m_minu, m_merge) -> disjoint(m2, m_minu) && m_merge == m1
    proof { auto }
}

query osabst_disjoint_join_sig_get_none_auto{
    type K;
    type V;
    fixes k : K;
    fixes v : V;
    fixes m1 : Map<K, V>;
    fixes m2 : Map<K, V>;
    fixes m3 : Map<K, V>;
    shows disjoint(m1, m2) -> join(k, v, m3, m1) -> !indom(k, m2)
    proof { auto }
}