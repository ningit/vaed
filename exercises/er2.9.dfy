function pot(b : int, e : nat) : int {
	if e == 0 then 1 else b * pot(b, e-1)
}

method pot2(n : int) returns (y : int)
	requires n >= 0
	ensures	 y == pot(2, n)
{
	var x := 0;

	y := 1;

	while x != n
		invariant 0 <= x <= n
		invariant y == pot(2, x)
	{
		x, y := x + 1, y + y;
	}
}
