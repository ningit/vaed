// «El último elemento de la secuencia s es un pico en ella»
predicate EsPico(s : seq<int>)
	requires |s| > 0
{
	forall j : nat | j < |s|-1 :: s[|s|-1] >= s[j]
}

// Suma de los valores de los picos de la secuencia s
function SumaPicos(s : seq <int>) : int {
	if s == [] then 0 else SumaPicos(s[..|s|-1]) +
		if EsPico(s) then s[|s|-1] else 0
}

method suma_picos(v : array<int>) returns (s : int)
	requires v != null && v.Length > 0
	ensures s == SumaPicos(v[..])
{
	var n : nat, m : int;

	n, s, m := 1, v[0], v[0];

	while n != v.Length
		invariant 0 <= n <= v.Length
		invariant s == SumaPicos(v[..n])

		// m es el máximo de los elementos previos del array 
		invariant forall j | 0 <= j < n :: m >= v[j];
		invariant exists j | 0 <= j < n :: m == v[j];
	{
		// Imprescindible
		assert v[..n+1][..n] == v[..n];

		if v[n] >= m {
			assert EsPico(v[..n+1]);

			s := s + v[n];
		}


		m := if m > v[n] then m else v[n];
		n := n + 1;
	}

	assert v[..n] == v[..];
}
