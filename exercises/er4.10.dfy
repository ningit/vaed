function Fibo(n : nat) : nat {
	if 	n == 0	then 0
	else if n == 1	then 1
			else Fibo(n-1) + Fibo(n-2)
}

/* Cuenta el número de índice heroicos en la secuencia
 * (otra definición posible podría proceder por la izquierda
 * usando una función auxiliar que llevase un índice)
 */
function CuentaHeroicos(s : seq<int>) : nat {
	if s == [] then 0 else
		CuentaHeroicos(s[..|s|-1])
		+ if s[|s|-1] > Fibo(|s|-1) then 1 else 0
}

method cuantos_heroicos(x : array<int>) returns (h : nat)
	requires x != null
	ensures h == CuentaHeroicos(x[..])
{
	// Por defecto las variables son enteras
	var n : nat, f, g;

	n, h, f, g := 0, 0, 0, 1;

	while n != x.Length
		invariant 0 <= n <= x.Length
		invariant f == Fibo(n)
		invariant g == Fibo(n+1)
		invariant h == CuentaHeroicos(x[..n]);
	{
		// Lo mismo de siempre
		assert x[..n+1][..n] == x[..n];

		if x[n] > f {
			h := h + 1;
		}

		// Calcula los nuevos números de Fibonnaci
		f, g := g, f + g;

		n := n + 1;
	}

	assert x[..n] == x[..];
}
