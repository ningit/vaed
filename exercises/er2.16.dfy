/**
 * Para este ejercicio se usa la definición de potencia de ejercicios
 * anteriores y dos lemas tomados de ambas versiones del ejercicio
 * resuelto 2.10.
 */

function pot(b : int, e : nat) : int {
	if e == 0 then 1 else b * pot(b, e-1)
}

lemma {:induction false} LemaJusto(b : int, e : nat)
	requires e % 2 == 0
	ensures pot(b * b, e / 2) == pot(b, e);

	decreases e
{
	if e > 0 { LemaJusto(b, e - 2); }

	// Sin desactivar la inducción automática el siguiente
	// aserto es suficiente para hacer la demostración
	// assert pot(b * b, e / 2 - 1) == pot(b, e - 2);

	// Sin embargo la versión actual deja al demostrador
	// colgado
}

lemma {:induction false} LemaProductoBases(b : int, c : int, e : nat)
	ensures pot(b, e) * pot(c, e) == pot(b * c, e)

	decreases e
{
	if e > 0 {
		LemaProductoBases(b, c, e - 1);
	}
}

method potencia(a : int, n : nat) returns (p : int)
	ensures p == pot(a, n)
{
	if n == 0 {
		p := 1;
	}
	else {
		p := potencia(a, n-1);
		p := p * a;
	}
}

method potencia_log(a : int, n : nat) returns (p : int)
	ensures p == pot(a, n)
{
	var p' : int;

	if n == 0 {
		p := 1;
	}
	else {
		p' := potencia_log(a, n / 2);
		p' := p' * p';

		// Aplicamos los lemas
		LemaProductoBases(a, a, n / 2);
		LemaJusto(a, n - n % 2);

		assert p' == pot(a, n - n % 2);

		if n % 2 == 0 {
			p := p';
		}
		else {
			p := p' * a;
		}
	}
}
