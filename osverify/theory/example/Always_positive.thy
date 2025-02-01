imports basic
query test5_1 {
	fixes a_pre : int;
	fixes b_pre : int;
	fixes c_pre : int;
	assumes a_pre != (0);
	assumes int32_MIN < a_pre;
	assumes a_pre <= int32_MAX;
	assumes int32_MIN < b_pre;
	assumes b_pre <= int32_MAX;
	assumes int32_MIN < c_pre;
	assumes c_pre <= int32_MAX;
	shows (b_pre * b_pre) <= (9223372036854775807) && (-(9223372036854775808)) <= (b_pre * b_pre)
	proof { seq_auto }
}

query test7_2 {
	fixes a_pre : int;
	fixes b_pre : int;
	fixes c_pre : int;
	assumes a_pre != (0);
	assumes int32_MIN < a_pre;
	assumes a_pre <= int32_MAX;
	assumes int32_MIN < b_pre;
	assumes b_pre <= int32_MAX;
	assumes int32_MIN < c_pre;
	assumes c_pre <= int32_MAX;
	shows (a_pre * c_pre) <= (9223372036854775807) && (-(9223372036854775808)) <= (a_pre * c_pre)
	proof { seq_auto }
}

query test17_3 {
	fixes a_pre : int;
	fixes b_pre : int;
	fixes c_pre : int;
	assumes a_pre <= (0);
	assumes ((b_pre * b_pre) / (4)) < (a_pre * c_pre);
	assumes a_pre != (0);
	assumes int32_MIN < a_pre;
	assumes a_pre <= int32_MAX;
	assumes int32_MIN < b_pre;
	assumes b_pre <= int32_MAX;
	assumes int32_MIN < c_pre;
	assumes c_pre <= int32_MAX;
	shows (0) == Always_pos(a_pre, b_pre, c_pre)
	proof { seq_auto }
}

query test19_4 {
	fixes a_pre : int;
	fixes b_pre : int;
	fixes c_pre : int;
	assumes a_pre > (0);
	assumes ((b_pre * b_pre) / (4)) < (a_pre * c_pre);
	assumes a_pre != (0);
	assumes int32_MIN < a_pre;
	assumes a_pre <= int32_MAX;
	assumes int32_MIN < b_pre;
	assumes b_pre <= int32_MAX;
	assumes int32_MIN < c_pre;
	assumes c_pre <= int32_MAX;
	shows (1) == Always_pos(a_pre, b_pre, c_pre)
	proof { seq_auto }
}

query test21_5 {
	fixes b_pre : int;
	fixes a_pre : int;
	fixes c_pre : int;
	assumes ((b_pre * b_pre) / (4)) >= (a_pre * c_pre);
	assumes a_pre != (0);
	assumes int32_MIN < a_pre;
	assumes a_pre <= int32_MAX;
	assumes int32_MIN < b_pre;
	assumes b_pre <= int32_MAX;
	assumes int32_MIN < c_pre;
	assumes c_pre <= int32_MAX;
	shows (0) == Always_pos(a_pre, b_pre, c_pre)
	proof { seq_auto }
}

query test23_6 {
	fixes a_pre : int;
	fixes b_pre : int;
	fixes c_pre : int;
	assumes a_pre == (0);
	assumes int32_MIN < a_pre;
	assumes a_pre <= int32_MAX;
	assumes int32_MIN < b_pre;
	assumes b_pre <= int32_MAX;
	assumes int32_MIN < c_pre;
	assumes c_pre <= int32_MAX;
	shows (0) == Always_pos(a_pre, b_pre, c_pre)
	proof { seq_auto }
}

query test28_7 {
	fixes a_pre : int;
	fixes b_pre : int;
	fixes c_pre : int;
	assumes a_pre != (0);
	assumes int32_MIN < a_pre;
	assumes a_pre <= int32_MAX;
	assumes int32_MIN < b_pre;
	assumes b_pre <= int32_MAX;
	assumes int32_MIN < c_pre;
	assumes c_pre <= int32_MAX;
	shows (b_pre * b_pre) <= (9223372036854775807) && (-(9223372036854775808)) <= (b_pre * b_pre)
	proof { seq_auto }
}

query test29_8 {
	fixes a_pre : int;
	fixes b_pre : int;
	fixes c_pre : int;
	assumes a_pre != (0);
	assumes int32_MIN < a_pre;
	assumes a_pre <= int32_MAX;
	assumes int32_MIN < b_pre;
	assumes b_pre <= int32_MAX;
	assumes int32_MIN < c_pre;
	assumes c_pre <= int32_MAX;
	shows (a_pre * c_pre) <= (9223372036854775807) && (-(9223372036854775808)) <= (a_pre * c_pre)
	proof { seq_auto }
}

query test40_9 {
	fixes delta2_value : int;
	fixes delta1_value : int;
	fixes d_value : int;
	fixes delta0_value : int;
	fixes b_pre : int;
	fixes a_pre : int;
	fixes c_pre : int;
	assumes delta2_value <= delta1_value;
	assumes (0) < d_value;
	assumes d_value <= (4);
	assumes delta0_value == (b_pre * b_pre);
	assumes delta2_value == (a_pre * c_pre);
	assumes delta0_value == (delta1_value + (((4) - d_value) * delta2_value));
	assumes (a_pre * c_pre) > (0);
	assumes a_pre != (0);
	assumes int32_MIN < a_pre;
	assumes a_pre <= int32_MAX;
	assumes int32_MIN < b_pre;
	assumes b_pre <= int32_MAX;
	assumes int32_MIN < c_pre;
	assumes c_pre <= int32_MAX;
	shows (delta1_value - delta2_value) <= (9223372036854775807) && (-(9223372036854775808)) <= (delta1_value - delta2_value)
	proof { seq_auto }
}

query test53_10 {
	fixes d_value : int;
	fixes delta2_value : int;
	fixes delta1_value : int;
	fixes delta0_value : int;
	fixes b_pre : int;
	fixes a_pre : int;
	fixes c_pre : int;
	assumes (d_value - (1)) != (0);
	assumes delta2_value <= delta1_value;
	assumes (0) < d_value;
	assumes d_value <= (4);
	assumes delta0_value == (b_pre * b_pre);
	assumes delta2_value == (a_pre * c_pre);
	assumes delta0_value == (delta1_value + (((4) - d_value) * delta2_value));
	assumes (a_pre * c_pre) > (0);
	assumes a_pre != (0);
	assumes int32_MIN < a_pre;
	assumes a_pre <= int32_MAX;
	assumes int32_MIN < b_pre;
	assumes b_pre <= int32_MAX;
	assumes int32_MIN < c_pre;
	assumes c_pre <= int32_MAX;
	shows delta2_value == (a_pre * c_pre) && delta0_value == (b_pre * b_pre) && delta2_value == (a_pre * c_pre) && delta0_value == (b_pre * b_pre) && (0) < (d_value - (1)) && (d_value - (1)) <= (4) && (b_pre * b_pre) == ((delta1_value - delta2_value) + (((4) - (d_value - (1))) * (a_pre * c_pre))) && (a_pre * c_pre) > (0) && a_pre != (0) && int32_MIN < a_pre && a_pre <= int32_MAX && int32_MIN < b_pre && b_pre <= int32_MAX && int32_MIN < c_pre && c_pre <= int32_MAX
	proof { seq_auto }
}

query test74_11 {
	fixes a_pre : int;
	fixes d_value : int;
	fixes delta2_value : int;
	fixes delta1_value : int;
	fixes delta0_value : int;
	fixes b_pre : int;
	fixes c_pre : int;
	assumes a_pre <= (0);
	assumes d_value != (0);
	assumes delta2_value > delta1_value;
	assumes (0) < d_value;
	assumes d_value <= (4);
	assumes delta0_value == (b_pre * b_pre);
	assumes delta2_value == (a_pre * c_pre);
	assumes delta0_value == (delta1_value + (((4) - d_value) * delta2_value));
	assumes (a_pre * c_pre) > (0);
	assumes a_pre != (0);
	assumes int32_MIN < a_pre;
	assumes a_pre <= int32_MAX;
	assumes int32_MIN < b_pre;
	assumes b_pre <= int32_MAX;
	assumes int32_MIN < c_pre;
	assumes c_pre <= int32_MAX;
	shows (0) == Always_pos(a_pre, b_pre, c_pre)
	proof { seq_auto }
}

query test76_12 {
	fixes a_pre : int;
	fixes d_value : int;
	fixes delta2_value : int;
	fixes delta1_value : int;
	fixes delta0_value : int;
	fixes b_pre : int;
	fixes c_pre : int;
	assumes a_pre > (0);
	assumes d_value != (0);
	assumes delta2_value > delta1_value;
	assumes (0) < d_value;
	assumes d_value <= (4);
	assumes delta0_value == (b_pre * b_pre);
	assumes delta2_value == (a_pre * c_pre);
	assumes delta0_value == (delta1_value + (((4) - d_value) * delta2_value));
	assumes (a_pre * c_pre) > (0);
	assumes a_pre != (0);
	assumes int32_MIN < a_pre;
	assumes a_pre <= int32_MAX;
	assumes int32_MIN < b_pre;
	assumes b_pre <= int32_MAX;
	assumes int32_MIN < c_pre;
	assumes c_pre <= int32_MAX;
	shows (1) == Always_pos(a_pre, b_pre, c_pre)
	proof { seq_auto }
}

query test78_13 {
	fixes delta1_value : int;
	fixes delta2_value : int;
	fixes d_value : int;
	fixes delta0_value : int;
	fixes b_pre : int;
	fixes a_pre : int;
	fixes c_pre : int;
	assumes (delta1_value - delta2_value) >= (0);
	assumes (d_value - (1)) == (0);
	assumes delta2_value <= delta1_value;
	assumes (0) < d_value;
	assumes d_value <= (4);
	assumes delta0_value == (b_pre * b_pre);
	assumes delta2_value == (a_pre * c_pre);
	assumes delta0_value == (delta1_value + (((4) - d_value) * delta2_value));
	assumes (a_pre * c_pre) > (0);
	assumes a_pre != (0);
	assumes int32_MIN < a_pre;
	assumes a_pre <= int32_MAX;
	assumes int32_MIN < b_pre;
	assumes b_pre <= int32_MAX;
	assumes int32_MIN < c_pre;
	assumes c_pre <= int32_MAX;
	shows (0) == Always_pos(a_pre, b_pre, c_pre)
	proof { seq_auto }
}

query test80_14 {
	fixes a_pre : int;
	fixes c_pre : int;
	fixes b_pre : int;
	assumes (a_pre * c_pre) <= (0);
	assumes a_pre != (0);
	assumes int32_MIN < a_pre;
	assumes a_pre <= int32_MAX;
	assumes int32_MIN < b_pre;
	assumes b_pre <= int32_MAX;
	assumes int32_MIN < c_pre;
	assumes c_pre <= int32_MAX;
	shows (0) == Always_pos(a_pre, b_pre, c_pre)
	proof { seq_auto }
}

query test82_15 {
	fixes a_pre : int;
	fixes b_pre : int;
	fixes c_pre : int;
	assumes a_pre == (0);
	assumes int32_MIN < a_pre;
	assumes a_pre <= int32_MAX;
	assumes int32_MIN < b_pre;
	assumes b_pre <= int32_MAX;
	assumes int32_MIN < c_pre;
	assumes c_pre <= int32_MAX;
	shows (0) == Always_pos(a_pre, b_pre, c_pre)
	proof { seq_auto }
}

