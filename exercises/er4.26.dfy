/**
 * Como los vectores en Dafny comienzan obligatoriamente en 0
 * el valor de retorno f es un array de 7 elementos donde la
 * primera posición está desaprovechada.
 */

/*
 * En versiones anteriores de Dafny, las funciones genéricas dificultaban
 * la demostración al menos en este caso.
 *
 * Por ello fue necesario cambiar la función genérica de CuentaApariciones
 * por esta versión particular.
 *

function CuentaApariciones(s : seq<int>, k : int) : nat
	decreases s
{
	if s == []
		then 0
		else (if s[|s|-1] == k then 1 else 0)
			+ CuentaApariciones(s[..|s|-1], k)
}

 */

function CuentaApariciones<T(==)>(s : seq<T>, k : T) : nat
	decreases s
{
	if s == []
		then 0
		else (if s[|s|-1] == k then 1 else 0)
			+ CuentaApariciones(s[..|s|-1], k)
}

method calcular_frec(x : array<int>) returns (f : array<int>)
	requires x != null
	requires forall i | 0 <= i < x.Length :: 1 <= x[i] <= 6

	ensures f != null && f.Length == 7
	ensures forall i | 1 <= i <= 6 :: f[i] == CuentaApariciones(x[..], i)

{
	var n : nat, m : nat := 0, 1;

	f := new int[7];

	// Pone el vector f a 0

	while m != 7
		invariant 1 <= m <= 7

		invariant forall i | 1 <= i < m :: f[i] == 0;
	{
		f[m], m := 0, m + 1;
	}


	// Cuenta las apariciones de cada cara del dado

	while n != x.Length
		invariant 0 <= n <= x.Length

		invariant forall i | 1 <= i <= 6 ::
			f[i] == CuentaApariciones(x[..n], i)
	{
		// Lo normal
		assert x[..n] == x[..n+1][..n];

		f[x[n]], n := f[x[n]] + 1, n+1;
	}

	assert x[..n] == x[..];
}
