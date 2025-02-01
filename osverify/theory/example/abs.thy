imports basic
query test5_1 {
	fixes x_pre : int;
	assumes x_pre >= (0);
	assumes int32_MIN < x_pre;
	assumes x_pre <= int32_MAX;
	shows x_pre == Zabs(x_pre)
	proof { seq_auto }
}

query test7_2 {
	fixes x_pre : int;
	assumes x_pre < (0);
	assumes int32_MIN < x_pre;
	assumes x_pre <= int32_MAX;
	shows (-x_pre) == Zabs(x_pre)
	proof { seq_auto }
}

