/**
 * ExprDecimal(a, b, x) <==> x es la expresión decimal de a en la base b
 *
 * Se comprueba que la cifra menos significativa en base 10 coincide
 * con el «término independiente» de la expresión en potencias de la
 * base y aplicamos recursión truncando por la derecha.
 */
predicate ExprDecimal(a : nat, b : nat, x : nat)
	requires 1 < b < 10
{
	if x == 0 == a
	then
		true
	else
		// La primera coordenada es el «término independiente»
		x % 10 == a % b &&
		// 'x' sin la última cifra es la expresión decimal de a/b
		ExprDecimal(a / b, b, x / 10)
}

method cambio_base(a : nat, b : nat) returns (x : nat)
	requires 1 < b < 10
	ensures ExprDecimal(a, b, x)

	decreases a
{
	if a < b {
		x := a;
	}
	else {
		x := cambio_base(a / b, b);

		x := 10 * x + a % b;
	}
}
