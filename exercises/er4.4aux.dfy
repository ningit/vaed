// Potencia (de números reales)
function Pot(x : real, n : nat) : real
	ensures x > 0.0 ==> Pot(x, n) > 0.0
{
	if n == 0 then 1.0 else x * Pot(x, n - 1)
}

// Factorial
function Fact(n : nat) : nat
	ensures Fact(n) > 0
{
	if n == 0 then 1 else n * Fact(n-1)
}

// Las potencias crecientes de base en (0, 0.5] convergen a 0
// (en realidad esto es cierto para todo (0, 1))
lemma AcotaPotencia(x : real, c : real) returns (n : nat)
	requires 0.0 < x <= 0.5
	requires c > 0.0

	ensures Pot(x, n) < c
{
	// Tomamos un entero por encima de 1/c
	var m := (1.0 / c).Floor + 1;

	n := AcotaPotenciaAux(x, m);

	// Entonces 1/m es menor que c
	calc <=
	{
		Pot(x, n);
		<
		1.0 / m as real;
		1.0 / ((1.0 / c).Floor + 1) as real;
		{ OrdenInversos(1.0, ((1.0 / c).Floor + 1) as real, 1.0 / c); }
		1.0 / (1.0 / c);
		c;
	}
}

// Lema auxiliar para demostrar por inducción el anterior lema
lemma AcotaPotenciaAux(x : real, m : nat) returns (n : nat)
		requires 0.0 < x <= 0.5
		requires m > 0

		ensures Pot(x, n) < 1.0 / m as real
{
	// Caso base
	if m == 1
	{
		n := 1;
	}
	// Caso inductivo
	else
	{
		var n0 := AcotaPotenciaAux(x, m-1);
		n := n0 + 1;

		calc <=
		{
			Pot(x, n);
			// Definición de potencia
			Pot(x, n0) * x;
			<
			(1.0 / (m-1) as real) * x;
			1.0 / (2 * (m-1)) as real;
			1.0 / m as real;
		}
	}
}

//
// Lemas sobre el cociente potencia/factorial
//

// Da un nombre al factor x^n / n!
function Pf(x : real, n : nat) : real
	ensures x > 0.0 ==> Pf(x, n) > 0.0
{
	Pot(x, n) / Fact(n) as real
}

// Pf advances by multiplication with a factor like this
lemma PfFactorLemma(x : real, n : nat)
	ensures Pf(x, n+1) == Pf(x, n) * (x / (n+1) as real)
{
}

// La función Pf decrece a partir de cierto índice
lemma PfDecrece(x : real, n : nat, m : nat)
	requires x > 0.0
	requires n >= m >= x.Floor + 1

	ensures Pf(x, n) <= Pf(x, m)
{
	var k := m;

	while k < n
		invariant m <= k <= n
		invariant Pf(x, k) <= Pf(x, m)
	{
		calc <= {
			Pf(x, k+1);
			{ PfFactorLemma(x, k); }
			Pf(x, k) * (x / (k+1) as real);
			{ assert x < (k + 1) as real; }
			Pf(x, k);
			// Loop invariant
			Pf(x, m);
		}

		k := k + 1;
	}
}

//
// Funciones auxiliares sobre el orden de productos y cocientes
//

lemma OrdenInversos(x : real, y : real, z : real)
	requires x >= 0.0
	requires y >= z > 0.0
	ensures x / y <= x / z
{
}

lemma OrdenProducto(x : real, y : real, z : real)
	requires x >= 0.0
	requires y >= z >= 0.0

	ensures x * y >= x * z
{
}

lemma OrdenEstrictoProducto(x : real, y : real, z : real)
	requires x > 0.0
	requires y > z >= 0.0

	ensures x * y > x * z
{
}

//
// Pf converge a 0
//

lemma FactVsPot(x : real, e : real) returns (k0 : nat)
	requires x > 0.0
	requires e > 0.0

	ensures forall k : nat :: k >= k0 ==> Pf(x, k) < e
{
	// Índice a partir del cual los factores de Pf son < 0.5
	// (para usar el lema AcotaPotencia)
	var k1 := 2 * (x.Floor + 1);
	var C := Pf(x, k1);

	// Como sabemos que las potencias de base en (0, 0.5] tienden a cero,
	// se pretende acotar Pf por un potencia de esas características.

	// Esto se puede hacer con C * (x / k1)^k pues los sucesivos factores
	// entre Pf(x, n+1) y Pf(x, n) son (x / n), menores que (x / k1).
	var factor := x / k1 as real;

	var k2 := AcotaPotencia(factor, e / C);

	k0 := k1 + k2;

	var n := 0;

	while n < k2
		invariant 0 <= n <= k2
		invariant Pf(x, k1 + n) <= C * Pot(factor, n)
	{
		var freal := x / (k1 + n + 1) as real;

		calc <=
		{
			Pf(x, k1 + n + 1);
			{ PfFactorLemma(x, k1 + n); }
			Pf(x, k1 + n) * freal;
			// Hipótesis de inducción
			{ OrdenProducto(freal, C * Pot(factor, n), Pf(x, k1 + n)); }
			C * Pot(factor, n) * freal;
			{ OrdenProducto(C * Pot(factor, n), factor, freal); }
			C * Pot(factor, n) * factor;
			C * Pot(factor, n + 1);
		}

		n := n + 1;
	}

	calc <=
	{
		Pf(x, k0);
		C * Pot(factor, k2);
		< { OrdenEstrictoProducto(C, e / C, Pot(factor, k2)); }
		C * (e / C);
		e;
	}

	forall k | k >= k0
		ensures Pf(x, k) < e
	{
		PfDecrece(x, k, k0);
	}
}
