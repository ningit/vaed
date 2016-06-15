/**
 * Ejercicio hecho de forma diferente para probar los genéricos y los tipos
 * funcionales que ofrece el lenguaje Dafny.
 *
 * Información sobre los tipos funcionales y los genéricos se puede encontrar
 * en «Types in Dafny» [krml243] y ejemplos en la carpeta «Test» del
 * repositorio de Dafny.
 *
 * Observación: el código en C# generado por Dafny presenta errores de
 * compilación en versiones antiguas de Dafny.
 */

/**
 * Cuenta el número de elementos que cumplen el predicado p
 * en la secuencia s.
 *
 * La cuenta se hace desde la derecha para simplificar la prueba.
 */
function Cuenta<T>(s : seq<T>, p : T -> bool) : nat
	// La función Cuenta puede leer todo lo que pueda leer p
	// (para cualquier posible entrada)
	reads p.reads

	// Los elementos de la secuencia cumplen la precondición
	// del predicado
	requires forall i | 0 <= i < |s| :: p.requires(s[i])
{
	if s == [] then 0 else ( if p(s[|s|-1]) then 1 else 0 )
		+ Cuenta(s[..|s|-1], p)
}

method contar<T>(v : array<T>, p : T -> bool) returns (x : nat)
	requires v != null
	requires forall i | 0 <= i < v.Length :: p.requires(v[i])

	ensures x == Cuenta(v[..], p)
{
	// Índice para recorrer el array
	var n := 0;

	x := 0;

	while n != v.Length
		invariant 0 <= n <= v.Length
		invariant x == Cuenta(v[..n], p)
	{
		assert v[..n+1][..n] == v[..n];

		if p(v[n]) {
			x := x + 1;
		}

		n := n + 1;
	}

	assert v[..v.Length] == v[..];
}


//
// Caso del ejercicio 4.7
//

// Predicado «n es par»
predicate method par(n : int) {
	n % 2 == 0
}

method pares(v : array<int>) returns (x : nat)
	requires v != null
	ensures x == Cuenta(v[..], par)
{
	// En lugar de usar el predicado anterior se podría haber usado
	// una función lambda: «n => n % 2 == 0»
	x := contar(v, par);
}
