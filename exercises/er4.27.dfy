/**
 * En este ejercicio se hace uso de sintaxis de definición intensional
 * de conjuntos.
 * Véase: http://rise4fun.com/Dafny/tutorialcontent/Sets
 *
 * Los subtipos como 'nat' no se admiten como parámetros de arrays, secuencias
 * o similares.
 * En este ejercicio que los números sean no negativos es relevante así que se
 * indicará como precondición en sumas13 (aún así no es equivalente porque se
 * podrían asignar números negativos a posteriori).
 */

function Sumandos13(s : seq<int>) : set<(int, int)> {
	/*
	 * Si se permuta el orden de declaración de p y q en la expresión
	 * siguiente Dafny no será capaz (v1.9.5) de deducir la finitud del
	 * conjunto con 0 <= p < q < |s| (al parecer comprueba de izquierda
	 * a derecha que las variables libres toman un conjunto finito de
	 * valores y al procesar p no sabe nada de q ni ve la transitividad
	 * del orden).
	 *
	 * En cambio sí funciona si se separa como 0 <= p < |s| && p < q < |s|
	 */

	set q : nat, p : nat | 0 <= p < q < |s| && s[p] + s[q] == 13 :: (p, q)
}

function Sumas13(s : seq<int>) : nat {
	|Sumandos13(s)|

}

/**
 * Lema que permite calcular la suma de una secuencia recursivamente por la
 * derecha.
 */
lemma AvanceSumas13(s : seq<int>)
	// El dato de entrada es una lista no vacía de naturales
	requires s != []
	requires forall x | x in s :: x >= 0;

	// Si último valor es mayor que trece la suma se mantiene
	ensures s[|s|-1] > 13 ==> Sumas13(s) == Sumas13(s[..|s|-1])

	// En otro caso, la suma aumenta en el número de elementos
	// de valor complementario (13) al último en el resto del vector
	ensures s[|s|-1] <= 13 ==> Sumas13(s) == Sumas13(s[..|s|-1]) +
		|set i : nat | i < |s|-1 && s[i] == 13 - s[|s|-1]|
{
	var cola := s[|s|-1];

	if cola > 13 {
		// Los sumandos son los mismos porque un par (m, |s|-1)
		// no puede sumar 13
		var nuevo := set p : nat | 0 <= p < |s|-1 && s[p] + s[|s|-1] == 13 :: (p, |s|-1);

		assert Sumandos13(s) == Sumandos13(s[..|s|-1]) + nuevo;

		// Reducción al absurdo

		if nuevo != {} {
			var x : int :| (x, |s|-1) in nuevo;

			calc {
				s[x] + s[|s|-1];
				// Definición de cola
				s[x] + cola;
				// s[x] es no negativo
				>= calc ==> { s[x] in s; s[x] >= 0; }
				cola;
				// Condición del if
				> 13;
			}
		}
	}
	else {
		// Los nuevos pares
		var np := set i : nat | i < |s|-1 && s[i] == 13 - s[|s|-1] :: (i, |s|-1);

		// Por un lado...
		assert Sumandos13(s) == Sumandos13(s[..|s|-1]) + np;

		// Y por otro se intenta simplificar np
		var nps := set i : nat | i < |s|-1 && s[i] == 13 - s[|s|-1];

		assert np == set z : nat | z in nps :: (z, |s|-1);

		LemaProdS(nps, |s|-1, np);
	}
}

// Lema ad-hoc para la parte final de AvanceSumas13
lemma LemaProdS(s : set<int>, k : int, ts : set<(int, int)>)
	requires ts == set z : int | z in s :: (z, k)
	ensures |s| == |ts|

	decreases s
{
	// Inducción normal

	if s == {} {
		// Caso base
	}
	else {
		var x :| x in s;

		LemaProdS(s - {x}, k, ts - {(x, k)});
	}
}


method sumas13(v : array<int>) returns (r : nat)
	requires v != null
	// Los elementos del array son no negativos
	requires forall i | 0 <= i < v.Length :: v[i] >= 0

	ensures r == Sumas13(v[..])
{
	// Índice (dos distintos) para los bucles
	var n : nat, m : nat;

	// f[i] = «número de elementos en v con valor i» (en construcción)
	var f := new int[14];

	// «Número de elementos en v con valor i» (en construcción)
	ghost var f_elems : seq<set<int>> := [];

	m := 0;

	// Pone el array f a 0 como valor inicial
	while m != 14
		invariant 0 <= m <= 14
		invariant forall i | 0 <= i < m :: f[i] == 0;

		// Variables de verificación
		invariant |f_elems| == m
		invariant forall i | 0 <= i < m :: f_elems[i] == {};
	{
		f[m], m := 0, m + 1;

		f_elems := f_elems + [{}];
	}


	n, r := 0, 0;

	while n != v.Length
		invariant 0 <= n <= v.Length

		// El vector tiene valores no negativos
		invariant forall i | 0 <= i < v.Length :: v[i] >= 0

		// f_elems es una secuencia de tamaño fijo 14
		invariant |f_elems| == 14

		// f y f_elems sólo cuentan las primeras n entradas del vector
		invariant forall i | 0 <= i < 14 :: f_elems[i] ==
			set j : nat | j < n && v[j] == i

		invariant forall i | 0 <= i < 14 :: f[i] ==
			|f_elems[i]|

		invariant r == Sumas13(v[..n]);
	{
		// Parte de la demostración de los invariantes se hace en el
		// lema AvanceSumas13 (aparte)

		AvanceSumas13(v[..n+1]);

		assert v[..n+1][..n] == v[..n];

		if v[n] <= 13 {
			r := r + f[13 - v[n]];

			// El complementario a 13 de v[n]
			ghost var vnc := 13 - v[n];
			// Variable por legibilidad
			ghost var s := v[..n+1];

			calc {
				r;
				==
				Sumas13(v[..n]) + f[vnc];
				== { assert f[vnc] == |f_elems[vnc]|; }
				Sumas13(v[..n]) + |f_elems[vnc]|;
				// Por definición de f_elems
				== { assert f_elems[vnc] ==
					set i : nat | i < |s|-1 && s[i] == 13 - s[|s|-1]; }
				Sumas13(v[..n]) 
					+ |set i : nat | i < |s|-1 && s[i] == 13 - s[|s|-1]|;
				== // Por el lema
				Sumas13(v[..n+1]);
			}


			f[v[n]] := f[v[n]] + 1;

			// n es un índice donde hay un elemento que vale v[n]
			// por tanto hay que añadirlo a f_elems[v[n]]

			f_elems := f_elems[v[n] := f_elems[v[n]] + {n}];

			// Aserto necesario
			assert  f_elems[v[n]] == set j : nat | j < n+1 && v[j] == v[n];
		}

		// Los f_elems de valor distinto que v[n] no se ven alterados
		// en esta iteración
		assert forall i | 0 <= i < 14 && i != v[n] :: f_elems[i] ==
			set j : nat | j < n+1 && v[j] == i;

		n := n + 1;
	}

	assert v[..n] == v[..];
}
