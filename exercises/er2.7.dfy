function Suma(v : seq<int>) : int {
	if v == [] then 0 else v[0] + Suma(v[1..])
}

method suma(v : array<int>) returns (x : int)
	requires v != null
	ensures x == Suma(v[..])
{
	var n := v.Length;

	x := 0;

	while n != 0
		invariant 0 <= n <= v.Length
		invariant x == Suma(v[n..])
	{
		x, n := x + v[n-1], n - 1;
	}
}
