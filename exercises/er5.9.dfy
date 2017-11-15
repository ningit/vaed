// Evaluación de polinomios (algoritmo de Horner)
function Eval(p : seq<int>, v : int) : int {
	if p == [] then 0 else p[0] + v * Eval(p[1..], v)
}

// La evaluación de polinomios se puede hacer añadiendo monomios
// de grado creciente (se utilizará en algunas especificaciones)
lemma EvalMayores(p : seq<int>, v : int)
	requires |p| > 0
	ensures Eval(p, v) == Eval(p[..|p|-1], v) + p[|p|-1] * Pot(v, |p|-1)

	decreases p
{
	// Demostración recursiva añadiendo elementos por la izquierda

	if |p| <= 1 {
		// Caso base
	}
	else {
		calc
		{
			Eval(p, v);
			// definición
			p[0] + v * Eval(p[1..], v);
			// hipósis de inducción
			{ EvalMayores(p[1..], v); }
			p[0] + v * Eval(p[1..][..|p|-2], v) + p[|p|-1] * Pot(v, |p|-1);
			// asertos necesarios sobre secuencias
			{ assert p[1..][..|p|-2] == p[1..|p|-1]; assert p[1..|p|-1] == p[..|p|-1][1..]; }
			p[0] + v * Eval(p[..|p|-1][1..], v) + p[|p|-1] * Pot(v, |p|-1);
			// definición
			Eval(p[..|p|-1], v) + p[|p|-1] * Pot(v, |p|-1);
		}
	}
}

// Potencia (la misma definición de otras veces)
function Pot(x : int, n : nat) : int
	decreases n
{
	if n == 0 then 1 else x * Pot(x, n-1)
}


// Llamadas iniciales para todos los apartados recursivos

method eval(p : array<int>, v : int) returns (r : int)
	requires p != null && p.Length > 0
	ensures r == Eval(p[..], v)
{
	r := evalh(p, v, 0);
	r := gevalh(p, v, 0, 1, 0);
}


// Apartado (b)

method evalh(p : array<int>, v : int, n : nat) returns (r : int)
	requires p != null
	requires 0 <= n < p.Length
	ensures r == Eval(p[n..], v)

	decreases p.Length - n
{
	if n == p.Length-1 {
		r := p[p.Length-1];
	}
	else {
		r := evalh(p, v, n+1);
		r := r * v + p[n];
	}
}


// Apartado (c)

method eval_it1(p : array<int>, v : int) returns (r : int)
	requires p != null && p.Length > 0
	ensures r == Eval(p[..], v)
{
	var n : nat := p.Length - 1;

	r := p[n];

	while n != 0
		invariant 0 <= n
		invariant r == Eval(p[n..], v)
	{
		n := n - 1;
		r := r * v + p[n];
	}
}


// Apartado (d)

method gevalh(p : array<int>, v : int, n : nat, m : int, s: int) returns (r : int)
	requires p != null
	requires 0 <= n < p.Length

	// La suma que aparece en el libro (pág. 167) es
	// exactamente Eval(p[n..], v)
	ensures r == Eval(p[n..], v) * m + s

	decreases p.Length - n
{
	// Constante: el mayor índice válido del array
	var N := p.Length - 1;

	if n == N {
		r := p[N] * m + s;
	}
	else {
		r := gevalh(p, v, n+1, v*m, p[n] * m + s);
	}
}

// Apartado (e)

method eval_it2(p : array<int>, v : int) returns (r : int)
	requires p != null && p.Length > 0
	ensures r == Eval(p[..], v)
{
	// Es una constante: el último índice válido del vector
	var N := p.Length - 1;

	var n : nat, m : int, s : int := 0, 1, 0;

	while n != N
		invariant 0 <= n <= N
		invariant m == Pot(v, n)
		invariant s == Eval(p[..n], v)
	{
		EvalMayores(p[..n+1], v);

		assert p[..n+1][..n] == p[..n];

		s := p[n] * m + s;
		m := m * v;
		n := n + 1;
	}

	EvalMayores(p[..], v);

	r := p[N] * m + s;
}
