/**
 * El LemaJusto tal cual está escrito no funciona con la inducción automática
 * activada. Para desactivarla se ha utilizado el atributo :induction. Sobre
 * este y la inducción automática se puede encontrar información en el artículo
 * «Automating Induction with an SMT Solver» [krml218].
 *
 * También se puede desactivar con la opción «/induction:1» (o 2) (incluso al
 * utilizar VisualStudio, modificando el archivo «DafnyOptions.txt» sito en la
 * carpeta donde se instala la extensión de Dafny).
 *
 * En caso contrario el demostrador se queda colgado en los lemas.
 *
 * Hay otra versión alternativa (demostrando propiedades más generales de
 * la función potencia) en «er2.10v2.dfy».
 */


function pot(b : int, e : nat) : int {
	if e == 0 then 1 else b * pot(b, e-1)
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

lemma {:induction false} LemaJusto(b : int, e : nat)
	requires e % 2 == 0
	ensures pot(b * b, e / 2) == pot(b, e)

	decreases e
{
	if e > 0 { LemaJusto(b, e - 2); }

	// Sin desactivar la inducción automática el siguiente
	// aserto es suficiente para hacer la demostración
	// assert pot(b * b, e / 2 - 1) == pot(b, e - 2);

	// Sin embargo la versión actual deja al demostrador
	// colgado
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
			LemaJusto(x, y);

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

		// Aplica el lema a 'y' si es par o 'y-1' si es impar
		// (pues la precondición exige que 'y' sea par)
		LemaJusto(x, if y % 2 == 0 then y else y - 1);

		// En el caso 'y' impar (y - 1) / 2 == y / 2

		y := y / 2;
		x := x * x;
	}
}
