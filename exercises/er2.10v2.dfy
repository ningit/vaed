/**
 * Esta versión demuestra propiedades generales de la función «pot» para luego
 * utilizarlas en la demostración de la corrección de los algoritmos.
 *
 * El problema de la inducción automática ocurre también en este caso.
 */


function pot(b : int, e : nat) : int {
	if e == 0 then 1 else b * pot(b, e-1)
}

/*
 * Propiedades útiles de las potencias
 */

lemma {:induction false} LemaSuma(b : int, e : nat, f : nat)
	ensures pot(b, e + f) == pot(b, e) * pot(b, f)

	decreases e

{
	if e > 0 { LemaSuma(b, e-1, f); }
}

lemma {:induction false} LemaProductoBases(b : int, c : int, e : nat)
	ensures pot(b, e) * pot(c, e) == pot(b * c, e)

	decreases e
{
	if e > 0 {
		LemaProductoBases(b, c, e - 1);
	}
}

lemma LemaPotUno(e : nat)
	ensures pot(1, e) == 1
{
	if e > 0 {
		LemaPotUno(e - 1);
	}
}

lemma {:induction false} LemaProducto(b : int, e : nat, f : nat)
	ensures pot(b, e * f) == pot(pot(b, e), f)

	decreases e
{
	if e > 0 {
		/*
		 * Algunos asertos que aparecen son superfluos para el
		 * demostrador.
		 * Se incluyen para seguir la pista a la prueba.
		 */

		// Obtiene la hipótesis de inducción
		LemaProducto(b, e-1, f);

		assert pot(b, e * f - f) == pot(pot(b, e-1), f);

		// Utiliza el lema de la suma para decomponer la parte
		// izquierda de la hipótesis en un cociente
		LemaSuma(b, e * f - f, f);

		assert pot(b, e * f) == pot(b, f) * pot(pot(b, e-1), f);

		// Hace el producto de las bases en el lado derecho.
		// En la base queda la definición recursiva de potencia
		LemaProductoBases(b, pot(b, e-1), f);

		assert pot(b, e * f) == pot(b * pot(b, e - 1), f);

		assert b * pot(b, e - 1) == pot(b, e);
	}
	else {
		LemaPotUno(f);
	}
}

method pot1(x : int, y : int) returns (p : int)
	requires y >= 0
	ensures p == pot(x, y)
{
	// Se introduce 'e' como variable auxiliar porque
	// las variables de entrada son inmutables
	var e;

	p, e := 1, y;

	while e != 0
		invariant 0 <= e <= y
		invariant p == pot(x, y - e);
	{
		p := p * x;
		e := e - 1;
	}
}

method pot2(x0 : int, y0 : int) returns (p : int)
	requires y0 >= 0
	ensures p == pot(x0, y0)
{
	var x, y := x0, y0;

	p := 1;

	while y > 0
		invariant 0 <= y
		invariant pot(x0, y0) == pot(x, y) * p;
	{
		if y % 2 == 0 {
			// Todo lo que sigue es imprescindible
			assert x == pot(x, 1);
			assert x * x == pot(x, 2);

			LemaProducto(x, 2, y / 2);

			y, x := y / 2, x * x;
		}
		else {
			y, p := y - 1, p * x;
		}
	}
}

method pot3(x0 : int, y0 : int) returns (p : int)
	requires y0 >= 0
	ensures p == pot(x0, y0)
{
	var x, y := x0, y0;

	p := 1;

	while y > 0
		invariant 0 <= y
		invariant pot(x0, y0) == pot(x, y) * p;
	{
		if y % 2 == 1 { p := p * x; }

		// Lo siguiente es imprescindible
		assert x == pot(x, 1);
		assert x * x == pot(x, 2);

		LemaProducto(x, 2, y / 2);

		// En el caso 'y' impar (y - 1) / 2 == y / 2

		y := y / 2;
		x := x * x;
	}
}
