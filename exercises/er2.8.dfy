function Suma(v : seq<int>) : int {
	if v == [] then 0 else v[0] + Suma(v[1..])
}

lemma LemaSumaIzda(s : seq<int>, m : int)
	requires 0 <= m < |s|

	ensures Suma(s[..m]) + s[m] == Suma(s[..m+1])
{
	if m > 0 {
		LemaSumaIzda(s[1..], m-1);

		// Hipótesis de inducción (hecha explícita por claridad)
		assert Suma(s[1..][..m-1]) + s[1..][m-1] == Suma(s[1..][..m]);

		// Asertos necesarios
		assert s[1..][..m-1] == s[1..m];
		assert s[1..][..m] == s[1..m+1];

		// En cambio s[1..][m-1] == s[m] lo deduce solo

		// Substituyendo sale esto (se puede omitir)
		assert Suma(s[1..m]) + s[m] == Suma(s[1..m+1]);

		// El demostrador puede deducir la postcondición
		// sin ayuda a partir de la definición de Suma
	}
}

method otra_suma(v : array<int>) returns (x : int)
	requires v != null
	ensures x == Suma(v[..])
{
	var m : int;

	x, m := 0, 0;

	while m < v.Length
		invariant 0 <= m <= v.Length
		invariant x == Suma(v[..m])
	{

		x := x + v[m];
		m := m + 1;

		LemaSumaIzda(v[..], m-1);
	}

	// Es necesario
	assert v[..v.Length] == v[..];
}
