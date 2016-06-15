/**
 * La versión original exige que el tamaño de los vectores sea el mismo
 * pero aquí no se va a requerir.
 */

function Escalar(x : seq<int>, y : seq<int>) : int
	requires |x| == |y|
{
	if x == [] then 0 else x[0] * y[0] + Escalar(x[1..], y[1..])
}

method prod_escalar(v : array<int>, w : array<int>, j : nat) returns (r : int)
	requires v != null && w != null
	requires j <= v.Length && j <= w.Length

{
	if j == 0 {
		r := 0;
	}
	else {
		var s := prod_escalar(v, w, j-1);

		r := v[j - 1] * w[j - 1] + s;
	}
}
