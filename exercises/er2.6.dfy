method intercambia(a : int, b : int) returns (x : int, y : int)
	ensures	 x == b && y == a
{
	x, y := a, b;

	x := x - y;
	y := x + y;
	x := y - x;
}

class Celda {
	var valor : int;
}

method intercambia2(x : Celda, y : Celda)
	modifies x, y

	requires x != null && y != null && x != y

	ensures old(x.valor) == y.valor
	ensures x.valor == old(y.valor)
{
	x.valor := x.valor - y.valor;
	y.valor := x.valor + y.valor;
	x.valor := y.valor - x.valor;
}
