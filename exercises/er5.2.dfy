/**
 * Se utiliza la inducción automática para probar lemas sobre
 * el producto de potencias (que ya se demostraron manualmente).
 */

function Pot(x : int, n : nat) : int
	ensures x > 0 ==> Pot(x, n) > 0

	decreases n
{
	if n == 0 then 1 else x * Pot(x, n-1)
}

/**
 * Al cambiar a la versión 1.9.7. este lema dejó de demostrarse solo
 * en consola, aunque funcionaba en Visual Studio. Se podría escribir
 * la demostración por inducción pero he duplicado el tiempo.
 */
lemma {:induction n} {:timeLimitMultiplier 2} LemaPotProd(x : int, n : nat, m : nat)
	ensures Pot(x, n) * Pot(x, m) == Pot(x, n + m) 
{
}

lemma {:induction n} LemaPotBase(x : int, y : int, n : nat)
	ensures Pot(x, n) * Pot(y, n) == Pot(x * y, n) 
{
}


// Apartado (a)

method  torre(a : int, n : nat) returns (r : int)
	ensures r == Pot(a, Pot(2, n))

	decreases n
{
	if n == 0 {
		r := a;
	}
	else {
		r := torre(a, n-1);

		r := r * r;

		LemaPotProd(a, Pot(2, n-1), Pot(2, n-1));
	}
}


// Apartado (b)

method  torre_final(a : int, n : nat) returns (r : int)
	ensures r == Pot(a, Pot(2, n))
{
	r := ggtorre(a, n, 1, a);
}

// Dafny detecta que es recursiva final (tail recursive pone)
method  ggtorre(a : int, n : nat, v : nat, p : int) returns (r : int)
	requires p == Pot(a, v)
	ensures r == Pot(Pot(a, Pot(2, n)), v)

	decreases n
{
	if n == 0 {
		r := p;
	}
	else {
		LemaPotProd(a, v, v);

		r := ggtorre(a, n-1, 2*v, p*p);

		// Opera multiplicando bases con igual exponente y sumando
		// exponentes con misma base
		ghost var a2n := Pot(a, Pot(2, n-1));

		calc {
			r;
			== { LemaPotProd(a2n, v, v); }
			Pot(a2n, v) * Pot(a2n, v);
			== { LemaPotBase(a2n, a2n, v); }
			Pot(a2n * a2n, v);
			== { 	LemaPotProd(a, Pot(2, n-1), Pot(2, n-1)); 
				assert a2n * a2n == Pot(a, Pot(2, n-1) + Pot(2, n-1)); }
			Pot(Pot(a, Pot(2, n-1) + Pot(2, n-1)), v);
		}

		/*
		 * Se definió la variable 'a2n' porque si no se producía
		 * un error en el paso segundo del cálculo.
		 */
	}
}
