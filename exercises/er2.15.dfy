// Nuevo tipo bit
newtype bit = x : int | (x == 0 || x == 1)

// Esta función es la misma que en ejercicios anteriores
function pot(b : int, e : nat) : int {
	if e == 0 then 1 else b * pot(b, e-1)
}

function Decimal(s : seq<bit>) : int
	requires |s| > 0
{
	if |s| == 1 then int(s[0]) else int(s[0]) + 2 * Decimal(s[1..])
}

function Decimal'(s : seq<bit>) : int
	requires |s| > 0
{
	int(s[|s|-1]) * pot(2, |s|-1) + if |s| == 1 then 0 else Decimal'(s[..|s|-1])
}

lemma Equival(s : seq<bit>)
	requires |s| > 0
	ensures Decimal'(s) == Decimal(s)
{
	if |s| > 1 {
		// Esto es suficiente con inducción automática activada
		assert s[1..][..|s[1..]|-1] == s[1..|s|-1];

		/**
		 * Sin inducción automática hay que añadir lo siguiente:
		 * (después de hacer inducción sobre el papel)

		Equival(s[1..]);

		if |s| > 2 {
			Equival(s[1..|s|-1]);

			Equival(s[..|s|-1]);
		}

		*/
	}
}

method binadec(v : array<bit>, n : nat) returns (d : int)
	requires v != null
	requires n < v.Length
	ensures d == Decimal(v[..n+1])
{
	// j es el índice en el vector
	// p es la potencia de 2 actual
	var j, p := 0, 2;

	d := int(v[0]);

	while j < n
		invariant 0 <= j <= n
		invariant p == pot(2, j+1)
		invariant d == Decimal(v[..j+1])
	{

		d := d + int(v[j+1]) * p;

		/* 
		 * Demuestra la conservación del invariante pasando
		 * por Decimal' que refleja la forma en que se calcula
		 * el resultado.
		 */
		Equival(v[..j+1]);

		assert v[..j+2][..j+1] == v[..j+1];

		Equival(v[..j+2]);

		p := p * 2;
		j := j + 1;
	}
}
