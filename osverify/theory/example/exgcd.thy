imports basic


query test31_3 {
	fixes retval : int;
	fixes b_pre : int;
	fixes a_pre : int;
	fixes x_pre_v : int;
	fixes y_pre_v : int;
	assumes retval == Zgcd(b_pre, (a_pre % b_pre));
	assumes ((b_pre * x_pre_v) + ((a_pre % b_pre) * y_pre_v)) == Zgcd(b_pre, (a_pre % b_pre));
	assumes (a_pre % b_pre) == (0);
	assumes Zabs(x_pre_v) <= (1);
	assumes y_pre_v == (0);
	assumes b_pre != (0);
	assumes int32_MIN < a_pre;
	assumes a_pre <= int32_MAX;
	assumes int32_MIN < b_pre;
	assumes b_pre <= int32_MAX;
	shows (x_pre_v - ((a_pre / b_pre) * y_pre_v)) <= (2147483647) && (-(2147483648)) <= (x_pre_v - ((a_pre / b_pre) * y_pre_v))
	proof { seq_auto }
}

query test33_4 {
	fixes retval : int;
	fixes b_pre : int;
	fixes a_pre : int;
	fixes x_pre_v : int;
	fixes y_pre_v : int;
	assumes retval == Zgcd(b_pre, (a_pre % b_pre));
	assumes ((b_pre * x_pre_v) + ((a_pre % b_pre) * y_pre_v)) == Zgcd(b_pre, (a_pre % b_pre));
	assumes (a_pre % b_pre) != (0);
	assumes (b_pre % (a_pre % b_pre)) == (0);
	assumes x_pre_v == (0);
	assumes Zabs(y_pre_v) <= (1);
	assumes b_pre != (0);
	assumes int32_MIN < a_pre;
	assumes a_pre <= int32_MAX;
	assumes int32_MIN < b_pre;
	assumes b_pre <= int32_MAX;
	shows ((a_pre / b_pre) * y_pre_v) <= (2147483647) && (-(2147483648)) <= ((a_pre / b_pre) * y_pre_v)
	proof { seq_auto }
}

query test34_5 {
	fixes retval : int;
	fixes b_pre : int;
	fixes a_pre : int;
	fixes x_pre_v : int;
	fixes y_pre_v : int;
	assumes retval == Zgcd(b_pre, (a_pre % b_pre));
	assumes ((b_pre * x_pre_v) + ((a_pre % b_pre) * y_pre_v)) == Zgcd(b_pre, (a_pre % b_pre));
	assumes (a_pre % b_pre) != (0);
	assumes (b_pre % (a_pre % b_pre)) == (0);
	assumes x_pre_v == (0);
	assumes Zabs(y_pre_v) <= (1);
	assumes b_pre != (0);
	assumes int32_MIN < a_pre;
	assumes a_pre <= int32_MAX;
	assumes int32_MIN < b_pre;
	assumes b_pre <= int32_MAX;
	shows (x_pre_v - ((a_pre / b_pre) * y_pre_v)) <= (2147483647) && (-(2147483648)) <= (x_pre_v - ((a_pre / b_pre) * y_pre_v))
	proof { seq_auto }
}

query test36_6 {
	fixes retval : int;
	fixes b_pre : int;
	fixes a_pre : int;
	fixes x_pre_v : int;
	fixes y_pre_v : int;
	assumes retval == Zgcd(b_pre, (a_pre % b_pre));
	assumes ((b_pre * x_pre_v) + ((a_pre % b_pre) * y_pre_v)) == Zgcd(b_pre, (a_pre % b_pre));
	assumes (a_pre % b_pre) != (0);
	assumes (b_pre % (a_pre % b_pre)) != (0);
	assumes Zabs(x_pre_v) <= (Zabs((a_pre % b_pre)) / Zgcd(b_pre, (a_pre % b_pre)));
	assumes Zabs(y_pre_v) <= (Zabs(b_pre) / Zgcd(b_pre, (a_pre % b_pre)));
	assumes b_pre != (0);
	assumes int32_MIN < a_pre;
	assumes a_pre <= int32_MAX;
	assumes int32_MIN < b_pre;
	assumes b_pre <= int32_MAX;
	shows ((a_pre / b_pre) * y_pre_v) <= (2147483647) && (-(2147483648)) <= ((a_pre / b_pre) * y_pre_v)
	proof { seq_auto }
}

query test37_7 {
	fixes retval : int;
	fixes b_pre : int;
	fixes a_pre : int;
	fixes x_pre_v : int;
	fixes y_pre_v : int;
	assumes retval == Zgcd(b_pre, (a_pre % b_pre));
	assumes ((b_pre * x_pre_v) + ((a_pre % b_pre) * y_pre_v)) == Zgcd(b_pre, (a_pre % b_pre));
	assumes (a_pre % b_pre) != (0);
	assumes (b_pre % (a_pre % b_pre)) != (0);
	assumes Zabs(x_pre_v) <= (Zabs((a_pre % b_pre)) / Zgcd(b_pre, (a_pre % b_pre)));
	assumes Zabs(y_pre_v) <= (Zabs(b_pre) / Zgcd(b_pre, (a_pre % b_pre)));
	assumes b_pre != (0);
	assumes int32_MIN < a_pre;
	assumes a_pre <= int32_MAX;
	assumes int32_MIN < b_pre;
	assumes b_pre <= int32_MAX;
	shows (x_pre_v - ((a_pre / b_pre) * y_pre_v)) <= (2147483647) && (-(2147483648)) <= (x_pre_v - ((a_pre / b_pre) * y_pre_v))
	proof { seq_auto }
}

query test41_8 {
	fixes retval : int;
	fixes b_pre : int;
	fixes a_pre : int;
	fixes x_pre_v : int;
	fixes y_pre_v : int;
	assumes retval == Zgcd(b_pre, (a_pre % b_pre));
	assumes ((b_pre * x_pre_v) + ((a_pre % b_pre) * y_pre_v)) == Zgcd(b_pre, (a_pre % b_pre));
	assumes (a_pre % b_pre) != (0);
	assumes (b_pre % (a_pre % b_pre)) != (0);
	assumes Zabs(x_pre_v) <= (Zabs((a_pre % b_pre)) / Zgcd(b_pre, (a_pre % b_pre)));
	assumes Zabs(y_pre_v) <= (Zabs(b_pre) / Zgcd(b_pre, (a_pre % b_pre)));
	assumes b_pre != (0);
	assumes int32_MIN < a_pre;
	assumes a_pre <= int32_MAX;
	assumes int32_MIN < b_pre;
	assumes b_pre <= int32_MAX;
	shows retval == Zgcd(a_pre, b_pre) && ((a_pre * y_pre_v) + (b_pre * (x_pre_v - ((a_pre / b_pre) * y_pre_v)))) == Zgcd(a_pre, b_pre) && b_pre != (0) && (a_pre % b_pre) != (0) && Zabs(y_pre_v) <= (Zabs(b_pre) / Zgcd(a_pre, b_pre)) && Zabs((x_pre_v - ((a_pre / b_pre) * y_pre_v))) <= (Zabs(a_pre) / Zgcd(a_pre, b_pre))
	proof { seq_auto }
}

query test45_9 {
	fixes retval : int;
	fixes b_pre : int;
	fixes a_pre : int;
	fixes x_pre_v : int;
	fixes y_pre_v : int;
	assumes retval == Zgcd(b_pre, (a_pre % b_pre));
	assumes ((b_pre * x_pre_v) + ((a_pre % b_pre) * y_pre_v)) == Zgcd(b_pre, (a_pre % b_pre));
	assumes (a_pre % b_pre) != (0);
	assumes (b_pre % (a_pre % b_pre)) == (0);
	assumes x_pre_v == (0);
	assumes Zabs(y_pre_v) <= (1);
	assumes b_pre != (0);
	assumes int32_MIN < a_pre;
	assumes a_pre <= int32_MAX;
	assumes int32_MIN < b_pre;
	assumes b_pre <= int32_MAX;
	shows retval == Zgcd(a_pre, b_pre) && ((a_pre * y_pre_v) + (b_pre * (x_pre_v - ((a_pre / b_pre) * y_pre_v)))) == Zgcd(a_pre, b_pre) && b_pre != (0) && (a_pre % b_pre) != (0) && Zabs(y_pre_v) <= (Zabs(b_pre) / Zgcd(a_pre, b_pre)) && Zabs((x_pre_v - ((a_pre / b_pre) * y_pre_v))) <= (Zabs(a_pre) / Zgcd(a_pre, b_pre))
	proof { seq_auto }
}

query test48_10 {
	fixes retval : int;
	fixes b_pre : int;
	fixes a_pre : int;
	fixes x_pre_v : int;
	fixes y_pre_v : int;
	assumes retval == Zgcd(b_pre, (a_pre % b_pre));
	assumes ((b_pre * x_pre_v) + ((a_pre % b_pre) * y_pre_v)) == Zgcd(b_pre, (a_pre % b_pre));
	assumes (a_pre % b_pre) == (0);
	assumes Zabs(x_pre_v) <= (1);
	assumes y_pre_v == (0);
	assumes b_pre != (0);
	assumes int32_MIN < a_pre;
	assumes a_pre <= int32_MAX;
	assumes int32_MIN < b_pre;
	assumes b_pre <= int32_MAX;
	shows y_pre_v == (0) && y_pre_v == (0) && retval == Zgcd(a_pre, b_pre) && ((a_pre * (0)) + (b_pre * (x_pre_v - ((a_pre / b_pre) * y_pre_v)))) == Zgcd(a_pre, b_pre) && b_pre != (0) && (a_pre % b_pre) == (0) && Zabs((x_pre_v - ((a_pre / b_pre) * y_pre_v))) <= (1)
	proof { seq_auto }
}

query test51_11 {
	fixes retval : int;
	fixes a_pre : int;
	fixes b_pre : int;
	assumes retval == Zabs(a_pre);
	assumes a_pre < (0);
	assumes b_pre == (0);
	assumes int32_MIN < a_pre;
	assumes a_pre <= int32_MAX;
	assumes int32_MIN < b_pre;
	assumes b_pre <= int32_MAX;
	shows retval == Zgcd(a_pre, b_pre) && ((a_pre * (-(1))) + (b_pre * (0))) == Zgcd(a_pre, b_pre) && b_pre == (0) && Zabs((-(1))) <= (1)
	proof { seq_auto }
}

query test55_12 {
	fixes retval : int;
	fixes a_pre : int;
	fixes b_pre : int;
	assumes retval == Zabs(a_pre);
	assumes a_pre == (0);
	assumes a_pre >= (0);
	assumes b_pre == (0);
	assumes int32_MIN < a_pre;
	assumes a_pre <= int32_MAX;
	assumes int32_MIN < b_pre;
	assumes b_pre <= int32_MAX;
	shows retval == Zgcd(a_pre, b_pre) && ((a_pre * (0)) + (b_pre * (0))) == Zgcd(a_pre, b_pre) && b_pre == (0) && Zabs((0)) <= (1)
	proof { seq_auto }
}

query test59_13 {
	fixes retval : int;
	fixes a_pre : int;
	fixes b_pre : int;
	assumes retval == Zabs(a_pre);
	assumes a_pre != (0);
	assumes a_pre >= (0);
	assumes b_pre == (0);
	assumes int32_MIN < a_pre;
	assumes a_pre <= int32_MAX;
	assumes int32_MIN < b_pre;
	assumes b_pre <= int32_MAX;
	shows retval == Zgcd(a_pre, b_pre) && ((a_pre * (1)) + (b_pre * (0))) == Zgcd(a_pre, b_pre) && b_pre == (0) && Zabs((1)) <= (1)
	proof { seq_auto }
}
