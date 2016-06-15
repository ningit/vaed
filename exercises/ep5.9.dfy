function Suma(s : seq<int>) : int {
	if s == [] then 0 else s[0] + Suma(s[1..])
}

predicate Separable(s : seq<int>) {
	exists p | 0 <= p < |s| :: Suma(s[..p]) == Suma(s[p..])
}

predicate Separable'(s : seq<int>) {
	Suma(s) % 2 == 0 && exists p | 0 <= p < |s| :: Suma(s[..p]) == Suma(s) / 2
}

lemma LemaSumaPrefijos(s : seq<int>, m : int)
	requires 0 <= m < |s|

	ensures Suma(s[..m]) + s[m] == Suma(s[..m+1])
{
	if m > 0 {
		calc == {
			Suma(s[..m+1]);

			// Definición de Suma y m > 0 ==> v != []
			s[0] + Suma(s[1..m+1]);

			{ assert s[1..m+1] == s[1..][..m]; }
			s[0] + Suma(s[1..][..m]);

			// Hipótesis de inducción porque s[1..] es menor que s
			{ LemaSumaPrefijos(s[1..], m-1); }
			s[0] + Suma(s[1..][..m-1]) + s[1..][m-1];

			// Él solo deduce s[1..][m-1] == s[m] y
			{ assert s[1..][..m-1] == s[1..m]; }
			s[0] + Suma(s[1..m]) + s[m];

			// Definición de Suma
			Suma(s[..m]) + s[m];
		}
	}
}

lemma SumaPorPartes(s : seq<int>, n : nat)
	requires n < |s|
	ensures Suma(s) == Suma(s[..n]) + Suma(s[n..])
{
	if n == 0 {
		// Caso base
	}
	else {
		calc {
			Suma(s);
			// Hipótesis de inducción
			{ SumaPorPartes(s, n-1); }
			Suma(s[..n-1]) + Suma(s[n-1..]);
			// Definición de Suma
			Suma(s[..n-1]) + s[n-1] + Suma(s[n..]);
			// Suma por prefijos
			{ LemaSumaPrefijos(s, n-1); }
			Suma(s[..n]) + Suma(s[n..]);
		}
	}
}

lemma Equivalencia(s : seq<int>)
	ensures Separable(s) <==> Separable'(s)
{
	forall n | 0 <= n < |s|
		ensures Suma(s) == Suma(s[..n]) + Suma(s[n..])
	{
		SumaPorPartes(s, n);
	}
}


/*
	2N sumas
	N comparaciones
*/
method separacion(v : array<int>) returns (b : bool)
	requires v != null

	ensures b == Separable(v[..])
{
	// Descartamos el caso v vector vacío

	if v.Length == 0
	{
		return false;
	}

	var n, mitad := 0, 0;

	while n < v.Length
		invariant 0 <= n <= v.Length
		invariant mitad == Suma(v[..n])
	{
		mitad := mitad + v[n];

		LemaSumaPrefijos(v[..], n);

		n := n + 1;
	}

	assert v[..n] == v[..];

	if mitad % 2 != 0 {
		Equivalencia(v[..]);

		return false;
	}

	assert Suma(v[..]) % 2 == 0;

	mitad := mitad / 2;

	var s := 0;

	n := 0;

	while n < v.Length-1 && s != mitad
		invariant 0 <= n < v.Length
		invariant s == Suma(v[..n])
		invariant forall p | 0 <= p < n :: Suma(v[..p]) != mitad
	{
		s := s + v[n];

		LemaSumaPrefijos(v[..], n);

		n := n + 1;
	}


	Equivalencia(v[..]);

	return s == mitad;
}
