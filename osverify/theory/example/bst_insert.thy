imports basic
query test3_1 {
	fixes x_pre : int;
	fixes value_pre : int;
	fixes tr_free : tree;
	assumes int32_MIN <= x_pre;
	assumes x_pre <= int32_MAX;
	shows combine_tree(empty_partial_tree, tree_insert(x_pre, value_pre, tr_free)) == tree_insert(x_pre, value_pre, tr_free) && int32_MIN <= x_pre && x_pre <= int32_MAX
	proof { seq_auto }
}

