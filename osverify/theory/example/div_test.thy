imports basic
query test4_1 {
	fixes c_pre : int;
	fixes a_pre : int;
	fixes b_pre : int;
	assumes c_pre != (0);
	assumes int32_MIN < a_pre;
	assumes a_pre <= int32_MAX;
	assumes int32_MIN < b_pre;
	assumes b_pre <= int32_MAX;
	assumes int32_MIN < c_pre;
	assumes c_pre <= int32_MAX;
	shows (a_pre * b_pre) <= (9223372036854775807) && (-(9223372036854775808)) <= (a_pre * b_pre)
	proof { seq_auto }
}

query test5_2 {
	fixes c_pre : int;
	fixes a_pre : int;
	fixes b_pre : int;
	assumes c_pre != (0);
	assumes int32_MIN < a_pre;
	assumes a_pre <= int32_MAX;
	assumes int32_MIN < b_pre;
	assumes b_pre <= int32_MAX;
	assumes int32_MIN < c_pre;
	assumes c_pre <= int32_MAX;
	shows (a_pre * b_pre) != (-(9223372036854775808)) || c_pre != (-(1)) && c_pre != (0)
	proof { seq_auto }
}

query test12_3 {
	fixes a_pre : int;
	fixes b_pre : int;
	fixes c_pre : int;
	assumes ((a_pre * b_pre) / c_pre) >= (0);
	assumes c_pre != (0);
	assumes int32_MIN < a_pre;
	assumes a_pre <= int32_MAX;
	assumes int32_MIN < b_pre;
	assumes b_pre <= int32_MAX;
	assumes int32_MIN < c_pre;
	assumes c_pre <= int32_MAX;
	shows ((a_pre * b_pre) / c_pre) == Pos_Div((a_pre * b_pre), c_pre, (0))
	proof { seq_auto }
}

query test14_4 {
	fixes a_pre : int;
	fixes b_pre : int;
	fixes c_pre : int;
	assumes ((a_pre * b_pre) / c_pre) < (0);
	assumes c_pre != (0);
	assumes int32_MIN < a_pre;
	assumes a_pre <= int32_MAX;
	assumes int32_MIN < b_pre;
	assumes b_pre <= int32_MAX;
	assumes int32_MIN < c_pre;
	assumes c_pre <= int32_MAX;
	shows (0) == Pos_Div((a_pre * b_pre), c_pre, (0))
	proof { seq_auto }
}

query test16_5 {
	fixes c_pre : int;
	fixes a_pre : int;
	fixes b_pre : int;
	assumes c_pre == (0);
	assumes int32_MIN < a_pre;
	assumes a_pre <= int32_MAX;
	assumes int32_MIN < b_pre;
	assumes b_pre <= int32_MAX;
	assumes int32_MIN < c_pre;
	assumes c_pre <= int32_MAX;
	shows (0) == Pos_Div((a_pre * b_pre), c_pre, (0))
	proof { seq_auto }
}

