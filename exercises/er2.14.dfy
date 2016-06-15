// «s es positivizado de r»
predicate Positivizado(s : seq<int>, r : seq<int>) {
	   |s| == |r|
	&& forall i : nat :: 0 <= i < |r| ==>
		s[i] == if r[i] < 0 then 0 else r[i]
}

method positivizar(v : array<int>)
	requires v != null
	ensures Positivizado(v[..], old(v[..]))

	modifies v
{
	var j := 0;

	/*
	 * Si en lugar de old(v[..]) se pone old(v)[..] el programa también
	 * verifica pero no dice nada pues old(v) == v (la referencia, el
	 * puntero al vector no cambia).
	 */
	while j < v.Length
		invariant 0 <= j <= v.Length

		// Se «positiviza» elemento a elemento de izquierda a derecha
		invariant Positivizado(v[..j], old(v[..j]))
		// Y el resto queda sin modificar por el momento
		invariant v[j..] == old(v[j..])
	{
		if v[j] < 0 { v[j] := 0; }

		j := j + 1;
	}
}
