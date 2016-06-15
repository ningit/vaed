/**
 * Se hace el cálculo del producto y de la cuenta descomponiendo
 * la secuencia por la derecha.
 *
 * Esto simplifica la definición de cuenta y la demostración de
 * la corrección.
 */

function Prod(s : seq<int>) : int {
	if s == [] then 1 else Prod(s[..|s|-1]) * s[|s|-1]
}

function CuentaProd(s : seq<int>) : nat {
	if s == [] then 0 else
		(if s[|s|-1] == Prod(s[..|s|-1]) then 1 else 0)
		+ CuentaProd(s[..|s|-1])
}

method num_prod(v : array<int>) returns (l : nat)
	requires v != null
	ensures l == CuentaProd(v[..])
{
	// La cuenta de índices productivos
	l := 0;

	var j, p := 0, 1;

	while j < v.Length
		invariant 0 <= j <= v.Length
		invariant p == Prod(v[..j])
		invariant l == CuentaProd(v[..j])
	{
		if p == v[j] { l := l + 1; }

		// Esto permite demostrar p == Prod(...)
		assert v[..j+1][..j] == v[..j];

		p := p * v[j];
		j := j + 1;
	}

	assert v[..v.Length] == v[..];
}
