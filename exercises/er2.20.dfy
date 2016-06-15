function pot(b : int, e : nat) : int {
	if e == 0 then 1 else b * pot(b, e-1)
}

method frm(n : int) returns (r : int)
	requires n >= 0
	ensures r == pot(3, n) - pot(2, n)
{
	if n == 0 {
		r := 0;
	}
	else if n == 1 {
		r := 1;
	}
	else {
		var mu := frm(n-1);
		var md := frm(n-2);

		r := 5 * mu - 6 * md;
	}
}
