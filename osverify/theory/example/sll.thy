imports basic
query test9_2 {
	fixes l2 : Seq<int>;
	fixes p_value_data : int;
	fixes l3 : Seq<int>;
	fixes p_value : int;
	fixes l_free : Seq<int>;
	fixes l1 : Seq<int>;
	fixes n_value : int;
	assumes l2 == seq_append(seq_repeat(p_value_data, 1), l3);
	assumes p_value != (0);
	assumes l_free == seq_append(l1, l2);
	assumes n_value == seq_length(l1);
	assumes seq_length(l_free) <= (2147483647);
	shows (n_value + (1)) <= (2147483647) && (-(2147483648)) <= (n_value + (1))
	proof { seq_auto }
}
