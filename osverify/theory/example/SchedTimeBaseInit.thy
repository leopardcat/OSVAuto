imports basic
function unsigned_last_nbits(int x, int n) -> int{
    x & ((1 << n ) - 1)
}
function signed_last_nbits(int x, int n) -> int{
   let v = (x & ((1 << n ) - 1)) in
   if (v  < 2 ** (n - 1)) {
        v
   } else {
        v - 2 ** n
   }
   end
}

query test6_1 {
	fixes sysClock_free : int;
	shows signed_last_nbits((unsigned_last_nbits((sysClock_free * (50)), (64)) / (1000000)), (32)) == ((sysClock_free * (50)) / (1000000)) &&
	signed_last_nbits((unsigned_last_nbits((sysClock_free * (20000)), (64)) / (1000000)), (32)) == ((sysClock_free * (20000)) / (1000000)) &&
	 (unsigned_last_nbits(((sysClock_free / (1000)) * (75)), (32)) / (100)) == (((sysClock_free / (1000)) * (75)) / (100)) &&
	 unsigned_last_nbits((-(1)), (64)) == (18446744073709551615)
	proof { seq_auto }
}

