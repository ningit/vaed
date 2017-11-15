/**
 * Cálculo aproximado del seno por Taylor.
 */

// Lo que aparece en los includes no se demuestra.
include "er4.4aux.dfy"

// Valor absoluto
// (es function-method para poder usarla en la implementación)
function method Abs(x : real) : real
	ensures Abs(x) >= 0.0
{
	if x < 0.0 then -x else x
}

// Término de orden 2k+1 de la serie de Taylor del seno en x
function TerminoSeno(x : real, k : nat) : real {
	Pot(-1.0, k) * Pot(x, 2*k + 1) / Fact(2 * k + 1) as real
}

// Polinomio de Taylor del seno de orden 2n-1 evaluado en x
function TaylorSeno(x : real, n : nat) : real {
	if n == 0
	then 0.0
	else TerminoSeno(x, n-1) + TaylorSeno(x, n-1)
}

// Factor entre un término de la serie y su siguiente
function method {:opaque} FactorCoef(k : nat) : real
{
	-1.0 / ((2 * k + 3) * (2 * k + 2)) as real
}

// Prueba que ciertos productos convierten un coeficiente en su siguiente
lemma AvanceTerm(x : real, k : nat)
	ensures FactorCoef(k) * TerminoSeno(x, k) * x * x
	  == TerminoSeno(x, k+1)
{
	calc
	{
		FactorCoef(k) * TerminoSeno(x, k) * x * x;
		calc
		{
			FactorCoef(k) * TerminoSeno(x, k);
			// Definición de TerminoSeno
			{ reveal FactorCoef(); }
			-1.0 / ((2 * k + 3) * (2 * k + 2)) as real * TerminoSeno(x, k);
			{ assert Fact(2 * k + 3) == Fact(2 * k + 1) * (2 * k + 3) * (2 * k + 2); }
			Pot(-1.0, k+1) * Pot(x, 2*k + 1) / Fact(2 * k + 3) as real;
		}
		Pot(-1.0, k+1) * Pot(x, 2*k + 1) / Fact(2 * k + 3) as real * x * x;
		Pot(-1.0, k+1) * Pot(x, 2*k + 3) / Fact(2 * k + 3) as real;
		// Definición de TerminoSeno
		TerminoSeno(x, k+1);
	}
}

lemma AbsPotAbs(x : real, k : nat)
	ensures Abs(Pot(x, k)) == Pot(Abs(x), k)
{
}

lemma PotUno(k : nat)
	ensures Pot(1.0, k) == 1.0
{
}

lemma AbsTerminoSeno(x : real, k : nat)
	ensures Abs(TerminoSeno(x, k)) == Pf(Abs(x), 2 * k + 1)
{
	calc ==
	{
		Abs(TerminoSeno(x, k));
		Abs(Pot(-1.0, k) * Pot(x, 2*k + 1) / Fact(2 * k + 1) as real);
		Abs(Pot(-1.0, k)) * Abs(Pot(x, 2*k+1) / Fact(2 * k + 1) as real);
		{ AbsPotAbs(-1.0, k); PotUno(k); }
		Abs(Pot(x, 2*k+1) / Fact(2 * k + 1) as real);
		Abs(Pot(x, 2*k+1)) / Abs(Fact(2 * k + 1) as real);
		{ AbsPotAbs(x, 2*k+1); }
		Pot(Abs(x), 2*k+1) / Abs(Fact(2 * k + 1) as real);
		{ assert Fact(2 * k + 1) >= 0; }
		Pot(Abs(x), 2*k+1) / Fact(2 * k + 1) as real;
		Pf(Abs(x), 2 * k + 1);
	}
}


lemma ExisteK0(x : real, e : real) returns (k : nat)
	requires e > 0.0
	ensures Abs(TerminoSeno(x, k)) < e
{
	// Supongamos en adelante que x > 0 pues tal
	// caso es inmediato
	if (x == 0.0)
	{
		k := 0; assert TerminoSeno(x, k) == 0.0;
		return;
	}

	var absx := Abs(x);
	k := FactVsPot(absx, e);

	var k' := 2 * k + 1;

	calc
	{
		Abs(TerminoSeno(x, k));
		{ AbsTerminoSeno(x, k); }
		Pf(absx, k');
		< { assert k' >= k; }
		e;
	}
}

method senoAprox(x : real, e : real) returns (k : nat, s : real)
	requires e > 0.0
	ensures s == TaylorSeno(x, k)
	ensures Abs(TerminoSeno(x, k)) < e
{
	// El término actual de la serie
	var t := x;

	k, s := 0, 0.0;

	// Esto ayuda a probar que TerminoSeno(x, 0) == x
	assert Pot(x, 1) == x;

	// Toma el k0 que existe porque el término seno es convergente
	var k0 := ExisteK0(x, e);

	while Abs(t) >= e
		invariant t == TerminoSeno(x, k)
		invariant s == TaylorSeno(x, k)

		invariant 0 <= k <= k0
		decreases k0 - k
	{
		s := s + t;

		t := FactorCoef(k) * t * x * x;

		// Demuestra el avance correcto de la variable t
		AvanceTerm(x, k);

		k := k + 1;
	}
}
