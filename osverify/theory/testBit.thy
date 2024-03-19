imports basic


query le255_and_le255 {
    fixes x: int32u;
    fixes y: int32u;
    assumes x <= 255;
    shows x & 0 <= 255
    proof { auto }
}

query zadd_rm_head {
    fixes n: int32u;
    fixes p: int32u;
    fixes q: int32u;
    assumes p == q;
    shows n + p == n + q
    proof { auto }
}

query zadd_rm_tail {
    fixes n: int32u;
    fixes p: int32u;
    fixes q: int32u;
    assumes p == q;
    shows p + n == q + n
    proof { auto }
}

query zdiv_range_le_lt {
    fixes a: int32u;
    fixes b: int32u;
    fixes c: int32u;
    fixes x: int32u;
    assumes a <= 0;
    assumes b > 0;
    assumes c > 0;
    assumes a <= x && x < b;
    shows a <= x / c && x / c < b
    proof { auto }
}


query zdiv_range_le_le {
    fixes a: int32u;
    fixes b: int32u;
    fixes c: int32u;
    fixes x: int32u;
    assumes a <= 0;
    assumes b > 0;
    assumes c > 0;
    assumes a <= x && x <= b;
    shows a <= x / c && x / c <= b
    proof { auto }
}

query Z_land_range_lo {
    fixes x: int32u;
    fixes y: int32u;
    assumes 0 <= x;
    shows 0 <= x & y
    proof { auto }
}

query Z_land_range_lo_r {
    fixes x: int32u;
    fixes y: int32u;
    assumes 0 <= y;
    shows 0 <= x & y
    proof { auto }
}

query Z_land_range_hi {
    fixes x: int32u;
    fixes y: int32u;
    assumes 0 <= x && x <= 4294967295;
    assumes 0 <= y && y <= 4294967295;
    shows x & y <= 4294967295
    proof { auto }
}

query Z_land_range {
    fixes x: int32u;
    fixes y: int32u;
    assumes 0 <= x && x <= 4294967295;
    assumes 0 <= y && y <= 4294967295;
    shows 0 <= x & y && x & y <= 4294967295
    proof { auto }
}

query Z_lor_range_hi {
    fixes x: int32u;
    fixes y: int32u;
    assumes 0 <= x && x <= 4294967295;
    assumes 0 <= y && y <= 4294967295;
    shows x | y <= 4294967295
    proof { auto }
}

query Z_lor_range {
    fixes x: int32u;
    fixes y: int32u;
    assumes 0 <= x && x <= 4294967295;
    assumes 0 <= y && y <= 4294967295;
    shows 0 <= x | y && x | y <= 4294967295
    proof { auto }
}

query Z_lxor_range {
    fixes x: int32u;
    fixes y: int32u;
    assumes 0 <= x && x <= 4294967295;
    assumes 0 <= y && y <= 4294967295;
    shows 0 <= x | y && x | y <= 4294967295
    proof { auto }
}

query Z_shiftl_16_range {
    fixes x: int32u;
    fixes y: int32u;
    assumes 0 <= x && x <= 65536;
    shows 0 <= x << 16 && x << 16 <= 4294967295
    proof { auto }
}

query Z_add_Arth_goal1 {
    fixes z1: int32u;
    fixes z2: int32u;
    assumes 0 <= z1 && z1 <= 4294967295;
    assumes 0 <= z2 && z2 <= 4294967295;
    shows (z1 + (z2 - z1)) - (z2 - z1) == z1
    proof { auto }
}