imports basic
query test19_1 {
	fixes v : int;
	fixes e0_free : expr;
	fixes op : binop;
	fixes e1 : expr;
	fixes e2 : expr;
	fixes e_value_t : int;
	fixes l_free : Seq<int>;
	assumes v == (11);
	assumes e0_free == EBinop(op, e1, e2);
	assumes v == BinOpID(op);
	assumes e_value_t == (2);
	assumes e_value_t != (1);
	assumes e_value_t != (0);
	assumes safe_eval(e0_free, l_free);
	shows safe_eval(e1, l_free)
	proof { seq_auto }
}