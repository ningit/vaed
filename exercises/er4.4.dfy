/**
 * Cálculo aproximado del seno por Taylor.
 */

/*
 * Lo que aparece en los includes no se demuestra.
 */
include "er4.4aux.dfy"

// Valor absoluto
// (es function-method para poder usarla en la implementación)
function method Abs(x : real) : real
	ensures Abs(x) >= 0.0
{
	if x < 0.0 then -x else x
}

// «El valor absoluto del cociente es el cociente de los valores absolutos»
lemma AbsCociente(x : real, y : real)
	requires y != 0.0
	ensures Abs(x / y) == Abs(x) / Abs(y)
{
}

// Término de orden 2k+1 de la serie de Taylor del seno en x
function TerminoSeno(x : real, k : nat) : real {
	Pot(-1.0, k) * Pot(x, 2*k + 1) / real(Fact(2 * k + 1))
}

// Polinomio de Taylor del seno de orden 2n-1 evaluado en x
function TaylorSeno(x : real, n : nat) : real {
	if n == 0
	then 0.0
	else TerminoSeno(x, n-1) + TaylorSeno(x, n-1)
}

// Prueba que ciertos productos convierten un coeficiente en su siguiente
lemma AvanceTerm(x : real, k : nat)
	ensures ((-1.0) * TerminoSeno(x, k) * x * x) 
		/ real((2 * k + 3) * (2 * k + 2))
		== TerminoSeno(x, k+1)
{
	assert (-1.0) * Pot(-1.0, k) == Pot(-1.0, k+1);

	// Al hacer estos dos pasos juntos se daba un error de Z3
	// con versiones antiguas de Dafny
	assert Pot(x, 2*k + 1) * x * x == Pot(x, 2*k + 3);
	assert Pot(x, 2*(k+1) + 1) == Pot(x, 2*k + 3);

	assert real((2 * k + 3) * (2 * k + 2)) * real(Fact(2 * k + 1)) 
		== real(Fact(2 * k + 3));
}


/**
 * Demostración de la terminación.
 */

lemma PotAbs(x : real, k : nat)
	ensures Abs(Pot(x, k)) == Pot(Abs(x), k)
{
}

lemma PotUno(k : nat)
	ensures Pot(1.0, k) == 1.0
{
}

lemma PfTermino(x : real, k : nat)
	ensures Abs(TerminoSeno(x, k)) == Pf(Abs(x), 2 * k + 1)
{
	var dk1 := 2 * k + 1;

	calc == {
		Abs(TerminoSeno(x, k));
		// Definición de TerminoSeno (parece necesario explicitarla)
		{ assert TerminoSeno(x, k) == Pot(-1.0, k) * Pot(x, dk1)
			/ real(Fact(dk1)); }
		Abs(Pot(-1.0, k) * Pot(x, dk1) / real(Fact(dk1)));
		// Pasa el valor absoluto a los factores
		Abs(Pot(-1.0, k)) * Abs(Pot(x, dk1)) / Abs(real(Fact(dk1)));
		// Mete el valor absoluto dentro de la potencia (fase 1)
		{ PotAbs(-1.0, k); }
		Pot(1.0, k) * Abs(Pot(x, dk1)) / Abs(real(Fact(dk1)));
		// Quita la potencia de 1
		{ PotUno(k); }
		Abs(Pot(x, dk1)) / Abs(real(Fact(dk1)));
		// Quita el valor absoluto del denominador (es positivo)
		{ assert Fact(dk1) > 0; }
		Abs(Pot(x, dk1)) / real(Fact(dk1));
		// Vuelve a conmutar Abs y Pot (fase 2)
		{ PotAbs(x, dk1); }
		Pot(Abs(x), dk1) / real(Fact(dk1));
		// Definición de Pf
		Pf(Abs(x), dk1);
	}
}

/*
 * Adaptación de PotVsFact para tomar impar el n0
 *
 * Otras posibles alternativas:
 * - Cambiar la postcondición de FactVsPot a un existe-para todos
 *   los mayores (como la definición de límite).
 * - Añadir a la postcondición de FactVsPot que el x / k es menor
 *   que 1.
 *
 * Ambas opciones no parecen difíciles sobre el papel.
 */
lemma FactVsPotAdapt(x : real, e : real)
	requires x > 0.0
	requires e > 0.0

	ensures exists k : nat :: Pf(x, 2*k+1) < e
{
	var k : nat;

	if x <= 1.0 {
		FactVsPot(x, e);

		var dk : nat :| Pf(x, dk) < e;

		// En todos los casos vale la misma
		k := dk / 2;

		// Ya está, sólo hay que despejar k
		if dk % 2 == 1 {
			calc == {
				Pf(x, 2 * k + 1);
				{ assert dk == 2 * k + 1; }
				Pf(x, dk); < e; 
			}
		}
		// Como x < 1.0 el Pf siguiente es también menor que e
		else {
			calc == {
				Pf(x, 2*k+1);
				{ assert 2 * k == dk; }
				Pf(x, dk+1);
				// Definición de Pf
				Pf(x, dk) * (x / real(dk + 1));
				<=
				{ assert x / real(dk + 1) <= 1.0; }
				Pf(x, dk); < e;
			}
		}
	}

	else {
		// Se coge como épsilon e / x < e
		FactVsPot(x, e / x);

		var dk : nat :| Pf(x, dk) < e / x;

		// Valor común
		k := dk / 2;

		if dk % 2 == 1 {
			calc == {
				Pf(x, 2 * k + 1);
				{ assert dk == 2 * k + 1; }
				Pf(x, dk);
				< e / x;
				< e;
			}
		}
		else {
			calc == {
				Pf(x, 2 * k + 1);
				{ assert dk == 2 * k; }
				Pf(x, dk + 1);
				// Definicion de Pf
				Pf(x, dk) * x / real(dk + 1);
				<=
				{ assert real(dk + 1) >= 1.0; }
				Pf(x, dk) * x;
				// Pf(x, dk) < e / x;
				< (e / x) * x;
				e;
			}
		}
	}

}


/**
 * Cuidado se pide que exista uno menor que no que todos lo sean.
 */
lemma ExisteK0(x : real, e : real)
	requires e > 0.0
	ensures exists k : nat :: Abs(TerminoSeno(x, k)) < e
{
	if x == 0.0 {
		calc == {
			TerminoSeno(x, 0);
			// Definición
			-1.0 * Pot(x, 1) / real(Fact(1));
			// Simplificando
			-1.0 * x;
			0.0;
		}
	}
	else {
		// Utilizamos lo demostrado en el archivo auxiliar
		FactVsPotAdapt(Abs(x), e);

		var k : nat :| Pf(Abs(x), 2*k+1) < e;

		// Hay que hacer una pequeña adaptación
		PfTermino(x, k);
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

	// Toma el k0 que para e asegura la existencia del límite
	ExisteK0(x, e);

	// Si se quita la especificación de tipo hay fallos
	ghost var k0 : nat :| Abs(TerminoSeno(x, k0)) < e;

	while Abs(t) >= e
		invariant t == TerminoSeno(x, k)
		invariant s == TaylorSeno(x, k)

		invariant 0 <= k <= k0
		decreases k0 - k
	{
		// Guarda el valor inicial de t
		ghost var t0 := t;

		s := s + t;

		t :=	((-1.0) * t * x * x) /
			real((2 * k + 3) * (2 * k  + 2));

		// Demuestra el avance correcto de la variable t
		AvanceTerm(x, k);

		k := k + 1;
	}
}
