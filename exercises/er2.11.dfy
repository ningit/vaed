/**
 * En este ejercicio se prueba la corrección un algoritmo iterativo para el
 * cálculo del máximo común divisor por medio del algoritmo de Euclides.
 *
 * Por un lado se demuestra que el algoritmo iterativo da como resultado el
 * de la función Mcd, que es una versión funcional del algoritmo de Euclides.
 * Por otro, se prueba que Mcd es el máximo común divisor según su definición,
 * es decir, el mayor de todos los divisores comunes.
 *
 * Se ha utilizado (en LemaDivision) una notación específica para demostrar
 * para-todos. Se ha encontrado por casualidad en la siguiente página:
 * http://www.lexicalscope.com/blog/2014/07/31/dafny-proving-forall-x-px-qx/
 */

include "aritmnl.dfy"

// x divide a y
predicate Divide(x : nat, y : nat) {
	x != 0 && y % x == 0
}

// Mcd por el algoritmo de Euclides
function Mcd(x : nat, y : nat) : nat
	requires x != 0 || y != 0
{
	if x == 0 	then	y
	else if y == 0	then	x
	else if x > y 	then	Mcd(y, x % y)
			else	Mcd(x, y % x)
}

// m es el máximo común divisor de x e y
predicate EsMcd(x : nat, y : nat, m : nat)
	requires x != 0 || y != 0
{
	Divide(m, x) && Divide(m, y)
	&& forall d : nat | Divide(d, x) && Divide(d, y) :: Divide(d, m)
}

// Lema útil para demostrar McdEsMcd
lemma LemaDivision(x : nat, y : nat)
	requires y > 0
	ensures forall d : nat | Divide(d, y) :: x % d == (x % y) % d
{
	// Descomposición por división entera
	assert x == (x/y) * y + x % y;

	// Se utiliza la sintaxis específica para demostrar paratodos
	// Aquí d un natural cualquiera que divide a y
	forall d : nat | Divide(d, y)
		ensures x % d == (x % y) % d
	{
		// Eso permite la siguiente descomposición
		assert y == (y/d) * d;

		// Y se puede reescribir la descomposición
		var f := (x/y) * (y/d);

		assert x == f * d + x % y;

		AritmNL.ModMasMultiplo(x % y, d, f);

		// De la igualdad primera y el resultado del lema
		assert x % d == (x % y) % d;
	}
}

lemma McdEsMcd(x : nat, y : nat)
	requires x != 0 || y != 0
	ensures	 EsMcd(x, y, Mcd(x, y))

	decreases y, x
{
	// Dafny sabe que Mcd y EsMcd son conmutativos en las
	// dos primeras entradas

	// Supone sin pérdida de generalidad que x >= y
	if x < y {
		McdEsMcd(y, x);
	}
	else {
		if y == 0 {
			// Caso fácil

			// Curiosamente son necesarios
			assert Mcd(x, 0) == x;
			assert Divide(x, 0);
		}
		else {
			// Inducción
			McdEsMcd(y, x % y);

			// Por hipótesis y Mcd(x, y) == Mcd(y, x % y)
			assert EsMcd(y, x % y, Mcd(x, y));

			// Aplicando el lema de la división se obtiene que
			// d es divisor de x y x % y <==> es divisor de x e y
			LemaDivision(x, y);

			// Como conclusión, Mcd(x, y) | x

			// Y además todo divisor de x e y divide a Mcd(x, y)
		}
	}
}

method mcd(x0 : nat, y0 : nat) returns (x : nat)
	requires x0 > y0 >= 0
	ensures	x == Mcd(x0, y0)
{
	var y;

	x, y := x0, y0;

	while y != 0
		invariant 0 <= y < x
		invariant Mcd(x, y) == Mcd(x0, y0)
	{
		x, y := y, x % y;
	}
}
