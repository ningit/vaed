function Sum(s : seq<int>) : int {
	if s == [] then 0 else s[|s|-1] + Sum(s[..|s|-1])
}

predicate Gaspariforme(s : seq<int>) {
	forall i | 0 <= i <= |s| :: Sum(s[..i]) >= 0
	&& Sum(s) == 0
}

method es_gaspariforme(a : array<int>) returns (b : bool)
	requires a != null
	ensures b == Gaspariforme(a[..])
{
	var n, s := 0, 0;

	b := true;

	while n != a.Length
		invariant 0 <= n <= a.Length
		invariant s == Sum(a[..n])
		invariant b == forall i | 0 <= i <= n :: Sum(a[..i]) >= 0
	{
		// Lo de siempre
		assert a[..n+1][..n] == a[..n];

		s := s + a[n];
		b := b && (s >= 0);
		n := n + 1;
	}

	assert a[..n] == a[..];

	b := b && (s == 0);
}
