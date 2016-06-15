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


/* 
 * Lemas auxiliares relativos al orden de los números
 * reales.
 */

// Orden inverso de los inversos
lemma OrdenInversos(x : real, y : real)
	requires 0.0 < x < y
	ensures 1.0 / x > 1.0 / y
{

}

// Dividir respeta el orden
lemma AcotaFrac(x : real, y : real, c : real)
	requires c > 0.0
	requires 0.0 <= x <= y

	ensures x / c <= y / c
{
}

// Lema para acotar productos (orden no estricto)
lemma AcotacionProducto(x : real, y : real, s : real, t : real)
	requires 0.0 <= x <= y
	requires 0.0 <= s <= t

	ensures x * s <= y * t
{
	// ¿Por qué este lema se verifica solo en archivo aparte
	// y aquí no?

	calc <= { x * s; y * s; y * t; }
}

// Lema para acotar productos (orden estricto)
lemma AcotaProdEst(x : real, y : real, s : real, t : real)
	requires 0.0 < x < y
	requires 0.0 < s < t

	ensures 0.0 < x * s < y * t
{
	// ¿Por qué este lema se verifica solo en archivo aparte
	// y aquí no?

	calc < { x * s; y * s; y * t; }
}

// Las potencias de base en (0, 1) tienden a 0 (lema auxiliar)
lemma AcotaPotenciaAux(x : real, m : int)
	requires 0.0 < x <= 1.0 / 2.0
	requires m > 0

	ensures exists n : nat :: Pot(x, n) < 1.0 / real(m)
{
	// Demostración por inducción

	if m == 1 {
		assert Pot(x, 1) < 1.0 / real(1);
	}
	else {
		AcotaPotenciaAux(x, m-1);

		var n : nat :| Pot(x, n) < 1.0 / real(m-1);

		// n+1 vale como aquello que existe para m

		calc {
			Pot(x, n+1);
			== // Definición de Pot
			x * Pot(x, n);
			< // Hipótesis
			x / real(m-1);
			// Parece evidente pero funciona aleatoriamente
			<= { AcotaFrac(x, 1.0/2.0, real(m-1)); }
			(1.0 / 2.0) / real(m-1);
			== // Pasar al denominador
			1.0 / real(2 * (m-1));
			<= { assert m > 1; }
			1.0 / real(m);
		}
	}
}


// Las potencias de base en (0, 1) tienden a 0
lemma AcotaPotencia(x : real, c : real)
	requires 0.0 < x <= 1.0 / 2.0
	requires c > 0.0

	ensures exists n : nat :: Pot(x, n) < c
{
	var inv := 1.0 / c;

	// Un entero tal que 1/m < c
	var m : nat := inv.Trunc + 1;

	assert real(m) > inv;

	OrdenInversos(inv, real(m));

	assert 1.0 / real(m) < c;

	AcotaPotenciaAux(x, m);
}


// Da un nombre al factor x^n / n!
function Pf(x : real, n : nat) : real {
	Pot(x, n) / real(Fact(n))
}


// Prueba que el avance de Pf que se usa en FactVsPot es correcto
lemma AvancePf(x : real, k : nat, f : real)
	requires k > 0
	requires f == x / real(k)

	ensures Pf(x, k) == Pf(x, k-1) * f
{
	assert Pot(x, k) == Pot(x, k-1) * x;

	assert Fact(k) == k * Fact(k-1);
}

// PF converge a 0
lemma FactVsPot(x : real, e : real)
	requires x > 0.0
	requires e > 0.0

	ensures exists k : nat :: Pf(x, k) < e
{
	// Un n0 tal que a partir de entonces P/F
	// decrezca (divida entre dos) al aumentar n
	var n0 : nat := 2 * (x.Trunc + 1);

	var factor := x / real(n0);
	var origen := Pf(x, n0);

	// Demuestra que el n0 está bien escogido
	calc {
		factor;
		== // Definición de factor
		x / real(n0);
		== // Definición de n0
		x / (2.0 * real(x.Trunc + 1));
		< // x es menor que su parte entera más uno
		{
			assert real(x.Trunc + 1) > x;

			/* Descomentar el siguiente assert impide que se
			   demuestre este paso y provoca un error en el
			   calc de más abajo en ciertas versiones de Dafny.
			   En la última versión estable es imprescindible.
			 */
		//	assert 2.0 * real(x.Trunc + 1) > 2.0 * x;
		}
		x / (2.0 * x);
		== // Cancelan las x
		0.5;
	}

	// Acota el número máximo de iteraciones que hay que hacer
	// suponiendo que P/F decrece por el «factor» cuando en
	// realidad decrece más rápidamente
	AcotaPotencia(factor, e / origen);

	var itmax : nat :| origen * Pot(factor, itmax) < e;


	// Variables del bucle
	var pfreal, pfcota, k := origen, origen, n0;

	while pfreal >= e
		decreases itmax + n0 - k
		invariant n0 <= k <= n0 + itmax
		invariant k == n0 + itmax ==> pfreal < e

		invariant pfreal == Pf(x, k)
		invariant pfcota == origen * Pot(factor, k - n0)

		invariant pfreal <= pfcota

		invariant factor == x / real(n0)
	{
		// Aumenta el índice de Pf (el exponente de la cota)
		k := k + 1;

		// Guarda pfreal y pfcota para uso posterior
		var pfreal0, pfcota0 := pfreal, pfcota;

		// Factor real por el que cambia Pf
		var facreal := x / real(k);


		// Actualización de pfreal y pfcota y demostración de que
		// siguen cumpliendo sus invariantes definitorios

		// ** pfreal
		pfreal := pfreal * facreal;

		AvancePf(x, k, facreal);

		// ** pfcota
		pfcota := pfcota * factor;

		calc == {
			pfcota;
			// Asignación anterior
			pfcota0 * factor;
			// Invariante sobre pfcota0
			{ assert pfcota == origen * Pot(factor, k - n0); }
			origen * Pot(factor, k - 1 - n0) * factor;
			// Suma de exponentes
			origen * Pot(factor, k - n0);
		}

		// Prueba que pfcota acota a pfreal
		//FactorDecreciente(x, k, n0);

		assert k > n0;

		AcotacionProducto(pfreal0, pfcota0, facreal, factor);


		assert pfreal <= pfcota;

		// Demostración del primer y segundo invariante
		// (llegado al límite no se dan más vueltas)
		if k == n0 + itmax {
			calc {
				pfreal;
				// Acota por pfcota
				<= pfcota;
				// Invariante sobre pdfcota
				// Valor de k == n0 + itmax
				origen * Pot(factor, itmax);
				// Definición de itmax
				< e;
			}
		}
	}
}
