method raiz(x : int) returns (r : int)
	requires x >= 0
	ensures	 r >= 0 && r * r <= x < (r + 1) * (r + 1)
{
	r := 0;

	while (r + 1) * (r + 1) <= x
		invariant r >= 0
		invariant r * r <= x
	{
		r := r + 1;
	}
}
