include "aritmnl.dfy"

function Pot(x : int, n : nat) : int
	ensures x > 0 ==> Pot(x, n) > 0

	decreases n
{
	if n == 0 then 1 else x * Pot(x, n-1)
}

// Lema muy particular
lemma PotPB(x : int, n : nat)
	ensures Pot(x * x, n) == Pot(x, 2 * n)
{
}

// Cualquier potencia positiva es 0 módulo la base
lemma PotModulo(x : nat, n : nat)
	requires x != 0
	requires n != 0

	ensures Pot(x, n) % x == 0
{
	// Pot(x, n) es por definición múltiplo de x (k = Pot(x, n-1)
	var k :| Pot(x, n) == x * k;

	AritmNL.DivPorFactor(x, k);
}

lemma AcotSup(n : nat, b : nat, m : nat)
	requires b > 0
	requires n / b < Pot(b, m+1)

	ensures n < Pot(b, m+2)
{
	/*
	 * El sentido de esta demostración está en ver que n, que es
	 * n/b * b + n % b, está entre nb * b y Pot(b, m+2).
	 *
	 * Esto se deduce del hecho de que tanto n/b * b como Pot(b, m+2)
	 * son 0 módulo b y Pot(b, m+2) es mayor, por lo que es por lo menos
	 * b unidades mayor. De esta forma sumar n % b (que es menor que b)
	 * a n/b * b no rompe la desigualdad.
	 *
	 */

	// Un alias brevedad
	var nb := n/b;

	// Es la desigualdad inicial multiplicada por b
	assert nb * b < Pot(b, m+2);

	// Probamos que (nb * b) % b == 0
	AritmNL.DivPorFactor(b, nb);

	assert (nb * b) % b == 0;

	// Probamos que Pot(b, m+2) % b == 0
	PotModulo(b, m+2);

	assert Pot(b, m+2) % b == 0;

	// La diferencia entre Pot(b, m+2) y nb * b es positiva
	// y 0 módulo b, luego es mayor o igual que b
	var dif := Pot(b, m+2) - nb * b;

	assert dif > 0;

	AritmNL.SumaMod0(Pot(b, m+2), nb*b, b);

	assert dif % b == 0;
	assert dif >= b;
}

// Primera solución (coste logarítmico)

method log_entero(b : nat, n : nat) returns (m : nat)
	requires b > 1 && n >= 1

	ensures Pot(b, m) <= n < Pot(b, m+1)

	decreases n
{
	if n < b {
		m := 0;
	}
	else {
		// Como b > 1, el parámetro n de la llamada recursiva
		// es menor (ambos asertos parecen necesarios)
		assert n < n * b;
		assert n / b < n;

		m := log_entero(b, n / b);

		ghost var nb := n / b;

		// La hipótesis de inducción
		// (dificultad: / es la división entera)
		assert Pot(b, m) <= nb < Pot(b, m + 1);

		// Acotación inferior de la potencia
		calc {
			   Pot(b, m+1);
			<= 			// (hip) * b
			   nb * b;
			<= 			// Se deduce de D = d * c + r
			   n;
		}

		assert nb < Pot(b, m+1);

		AcotSup(n, b, m);

		m := m + 1;
	}
}

// Segunda solución (coste doblemente logarítmico)

method glog_entero2(b : nat, n : nat) returns (m : nat, p : nat)
	requires b > 1 && n >= 1

	ensures Pot(b, m) <= n < Pot(b, m+1)
	ensures p == Pot(b, m)

	// No tiene porque ser no negativo
	// (cuando no se hace llamada recursiva)
	decreases n - b
{
	if n < b {
		m, p := 0, 1;
	}
	else {
		m, p := glog_entero2(b * b, n);

		PotPB(b, m);

		m := 2 * m;

		// No sabemos aún si es m o m + 1
		assert Pot(b, m) <= n < Pot(b, m + 2);

		if n >= p * b {
			// La condición del if (necesario)
			assert Pot(b, m+1) <= n;

			m := m + 1;
			p := p * b;
		}
	}
}
