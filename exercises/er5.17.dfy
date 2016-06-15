/*
 * Una interpretación libre de la solución del ejercicio resuelto 5.17.
 *
 * Podría considerarse también que este archivo es el ejercicio propuesto 5.12.
 */


// Versión recursiva

method simetrica?<T(==)>(m : array2<T>) returns (b : bool)
	requires m != null && m.Length0 == m.Length1 >= 1

	ensures b == forall j, i | 0 <= j <= i < m.Length0 :: m[i, j] == m[j, i]
{
	b := simetrica_c?(m, 0);
}

// La matriz (a_{i, j})_{i, j \geq c} es simétrica
method simetrica_c?<T(==)>(m : array2<T>, c : nat) returns (b : bool)
	requires m != null && m.Length0 == m.Length1 >= 1
	requires 0 <= c < m.Length0

	ensures b == forall j, i | c <= j <= i < m.Length0 :: m[i, j] == m[j, i]

	decreases m.Length0 - c
{
	// Es simétrica hasta que se demuestre lo contrario
	b := true;

	// Comprueba la primera fila y columna
	var k := c+1;

	while b && k < m.Length0
		invariant c < k <= m.Length0
		invariant b == forall i | c <= i < k :: m[c, i] == m[i, c]
	{
		b := m[c, k] == m[k, c];

		k := k + 1;
	}

	// Comprueba la submatriz esquinera inferior derecha
	if b && c < m.Length0 - 1 {
		b := simetrica_c?(m, c+1);
	}
}


// Versión iterativa

method simetrica_it?<T(==)>(m : array2<T>) returns (b : bool)
	requires m != null && m.Length0 == m.Length1 >= 1

	ensures b == forall j, i | 0 <= j <= i < m.Length0 :: m[i, j] == m[j, i]
{
	// Es simétrica hasta que se demuestre lo contrario
	b := true;

	var c := m.Length0 - 1;

	while b && 0 < c
		invariant 0 <= c < m.Length0 
		invariant b == forall j, i | c <= j <= i < m.Length0 :: m[i, j] == m[j, i]
	{
		// Aumenta la submatriz cuadrada donde se ha comprobado
		// que es simétrica desde la esquina inferior derecha
		var k := c;

		c := c - 1;

		while b && k < m.Length0
			invariant c < k <= m.Length0
			invariant b == forall i | c <= i < k :: m[c, i] == m[i, c]
		{
			b := m[c, k] == m[k, c];

			k := k + 1;
		}
	}
}
