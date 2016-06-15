function ProdEscalar(v : seq<int>, w : seq<int>) : int
	requires |v| == |w|
{
	if v == []
	then 0
	else v[0] * w[0] + ProdEscalar(v[1..], w[1..])
}

/**
 * Que el producto escalar se puede hacer también por la izquierda.
 */
lemma LemaProdEscalar(v : seq<int>, w : seq<int>)
	requires |v| == |w|
	requires v != []

	ensures ProdEscalar(v, w) == ProdEscalar(v[..|v|-1], w[..|v|-1]) + v[|v|-1] * w[|v|-1]
{
	if (|v| == 1) {
		// Caso base
	}
	else {
		// Anteriores en el orden
		var vr, wr := v[1..], w[1..];

		calc == {
			ProdEscalar(vr, wr);

			// Hipótesis de inducción
			{ LemaProdEscalar(vr, wr); }
			ProdEscalar(vr[..|vr|-1], wr[..|wr|-1]) + vr[|vr|-1] * wr[|wr|-1];

			// Simplificación de subsecuencias
			{ assert vr[..|vr|-1] == v[1..|v|-1]; assert wr[..|wr|-1] == w[1..|v|-1]; }
			ProdEscalar(v[1..|v|-1], w[1..|v|-1]) + vr[|vr|-1] * wr[|wr|-1];

			// Simplificación de elementos de subsecuencia
			{ assert vr[|vr|-1] == v[|v|-1]; assert wr[|vr|-1] == w[|v|-1]; }
			ProdEscalar(v[1..|v|-1], w[1..|v|-1]) + v[|v|-1] * w[|v|-1];
		}

		// Ya sólo que añadir el producto de la primera coordenada en cada término
	}
} 

method prod_escalar(x : array<int>, y : array<int>) returns (r : int)
	requires x != null && y != null
	requires x.Length == y.Length

	ensures r == ProdEscalar(x[..], y[..])
{
	// Se puede escoger cualquiera de las funciones recursivas

//	r := gprod_escalar(x, y, 0);
//	r := gfprod_escalar(x, y, x.Length, 0);
	r := ggprod_escalar(x, y, 0, 0);
}


// Apartado (a)

method gprod_escalar(x : array<int>, y : array<int>, n : nat) returns (r : int)
	requires x != null && y != null
	requires x.Length == y.Length

	requires n <= x.Length
	ensures r == ProdEscalar(x[n..], y[n..])

	decreases x.Length - n
{
	if n == x.Length {
		r := 0;
	}
	else {
		r := gprod_escalar(x, y, n+1);

		r := r + x[n] * y[n];
	}
}


// Apartado (b)

method gfprod_escalar(x : array<int>, y : array<int>, n : nat, a : int) returns (r : int)
	requires x != null && y != null
	requires x.Length == y.Length

	requires n <= x.Length
	requires a == ProdEscalar(x[n..], y[n..])

	ensures r == ProdEscalar(x[..], y[..])

	decreases n
{
	if n == 0 {
		r := a;
	}
	else {
		r := gfprod_escalar(x, y, n-1, x[n-1] * y[n-1] + a);
	}
}


// Apartado (c)

method ggprod_escalar(x : array<int>, y : array<int>, n : nat, s : int) returns (r : int)
	requires x != null && y != null
	requires x.Length == y.Length

	requires n <= x.Length
	requires s == ProdEscalar(x[..n], y[..n])

	ensures r == ProdEscalar(x[..], y[..])

	decreases x.Length - n
{
	if n == x.Length {
		assert x[..n] == x[..];
		assert y[..n] == y[..];

		r := s;
	}
	else {
		assert x[..n+1][..n] == x[..n];
		assert y[..n+1][..n] == y[..n];

		// Como el producto escalar se definió de izda a dcha
		// en este caso hay que recurrir a un lema
		LemaProdEscalar(x[..n+1], y[..n+1]);

		r := ggprod_escalar(x, y, n+1, x[n] * y[n] + s);
	}
}
