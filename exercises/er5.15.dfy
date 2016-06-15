/*
 * Debido a que los vectores no pueden comenzar por 1 en Dafny se han
 * realizado algunos cambios:
 * - El rango de índices de los vectores es [0, .Length).
 * - El valor de i en caso de !b es a.Length.
 * - El límite f es exterior (como en el ejercicio 5.12 de la búsqueda
 *   binaria) (es más cómodo para la sintaxis .. de Dafny...).
 *
 */

// ¿Está la secuencia ordenada?
predicate Ord(s : seq<int>) {
	forall i | 0 <= i < |s|-1 :: s[i] <= s[i + 1]

	/* La definición de arriba, fiel al libro, es problemática porque
	   el disparador al que se infiere {s[i]} puede dar lugar a bucles
	   con s[i+1]. Aún así Dafny concluye que el programa es correcto.

	   La siguiente es más conveniente para el demostrador.
	 */

	// forall i, j | 0 <= i <= j < |s| :: s[i] <= s[j]
}

// ¿Los elementos de la secuencia son distintos?
predicate Distintos(s : seq<int>) {
	forall i, j | 0 <= i < j < |s| :: s[i] != s[j]
}

lemma LemaSubseq(s : seq<int>, a : nat, b : nat)
	requires 0 <= a <= b <= |s|

	ensures Ord(s) ==> Ord(s[a..b])
	ensures Distintos(s) ==> Distintos(s[a..b])
{

}


method indice(a : array<int>) returns (b : bool, i : nat)
	requires a != null
	requires Ord(a[..]) && Distintos(a[..])

	ensures  b ==> 0 <= i < a.Length && a[i] == i
	ensures !b ==> i == a.Length
		&& forall j | 0 <= j < a.Length :: a[j] != j
{
	b, i := gindice(a, 0, a.Length);
}

method gindice(a : array<int>, c : nat, f : nat) returns (b : bool, i : nat)
	requires a != null
	requires 0 <= c <= f <= a.Length
	requires Ord(a[c..f])
	requires Distintos(a[c..f])

	ensures  b ==> c <= i < f && a[i] == i
	ensures !b ==> i == a.Length
		&& forall j | c <= j < f :: a[j] != j

	decreases f - c
{
	var m : nat;

	if c == f {
		b, i := false, a.Length;
	}
	else /* c < f */ {
		m := (c + f) / 2;

		if m < a[m] {
			// Prueba que el subvector también está ordenado
			LemaSubseq(a[c..f], 0, m-c);
			assert a[c..f][0..m-c] == a[c..m];

			b, i := gindice(a, c, m);

			if !b {
				// Demuestra que todos los valores a la derecha
				// del pivote son distintos a su índice
				ghost var k := m+1;

				// Se refuerza el invariante: > en lugar de !=
				while k < f
					invariant m < k <= f
					invariant forall j | m <= j < k :: a[j] > j;
				{
					assert a[k] > a[k-1];

					k := k + 1;
				}
			}
		}
		else if m == a[m] {
			b, i := true, m;
		}
		else /* m > a[m] */ {
			b, i := gindice(a, m+1, f);

			if !b {
				// Demuestra que todos los valores a la izquierda
				// del pivote son distintos a su índice
				ghost var k := m;

				// Se refuerza el invariante: < en lugar de !=
				while c < k
					invariant c <= k <= m
					invariant forall j | k <= j < m+1 :: a[j] < j;
				{
					assert a[k-1] < a[k];

					k := k - 1;
				}
			}
		}
	}
}
