imports basic
function unsigned_last_nbits(int x, int n) -> int{
    x % (2 ** n)
}
function signed_last_nbits(int x, int n) -> int{
   let v = x % (2 ** n) in
   if (v  < 2 ** (n - 1)) {
        v
   } else {
        v - 2 ** n
   }
   end
}
function OsSchedResetSchedResponseTime_update (int responseTime, int schedResponseTime)-> int{
    if (responseTime > schedResponseTime){
        schedResponseTime
    }
    else{
        18446744073709551615
    }
}
query test6_1 {
	fixes responseTime_pre : int;
	fixes schedResponseTime_free : int;
	assumes responseTime_pre > schedResponseTime_free;
	shows schedResponseTime_free == OsSchedResetSchedResponseTime_update(responseTime_pre, schedResponseTime_free)
	proof { seq_auto }
}

query test7_2 {
	fixes responseTime_pre : int;
	fixes schedResponseTime_free : int;
	assumes responseTime_pre <= schedResponseTime_free;
	shows unsigned_last_nbits((-(1)), (64)) == OsSchedResetSchedResponseTime_update(responseTime_pre, schedResponseTime_free)
	proof { seq_auto }
}
