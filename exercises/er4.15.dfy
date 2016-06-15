/*
 * El ejercicio admite simplificaciones: como s >= 1, Max2(s * x[n], 1)
 * y Min2(s * x[n], 1) (x[n] < 0) se pueden substituir por su primer
 * argumento.
 */

/*
 * El producto se calcula de derecha a izquierda porque conviene
 * para la demostración de la conservación de los invariantes
 * sobre s y t
 */
function Prod(s : seq<int>) : int {
	if s == [] then 1 else s[|s|-1] * Prod(s[..|s|-1])
}

// Máximo entre dos números
function method Max2(a : int, b : int) : int {
	if a > b then a else b
}

// Mínimo entre dos números
function method Min2(a : int, b : int) : int {
	if a > b then b else a
}

// x es el máximo del conjunto s
predicate Max(x : int, s : set<int>) {
	x in s && forall y {:autotriggers false} | y in s :: x >= y
}

// x es el mínimo del conjunto s
predicate Min(x : int, s : set<int>) {
	x in s && forall y {:autotriggers false} | y in s :: x <= y
}

lemma LemaConPr(x : array<int>, s : int, n : nat)
	requires x != null
	requires 0 <= n < x.Length

	requires s in set p | 0 <= p <= n :: Prod(x[p..n])

	ensures s * x[n] in set p | 0 <= p <= n :: Prod(x[p..n+1])
{
	// Como s está en el conjunto es un producto
	assert exists k | 0 <= k <= n :: Prod(x[k..n]) == s;

	// Sea el k para el que lo es
	var k :| 0 <= k <= n && Prod(x[k..n]) == s;

	// Por la definición de Prod se cumple el segundo
	// aserto (que es prescindible para Dafny)
	assert x[k..n+1][..n-k] == x[k..n];
	assert s * x[n] == Prod(x[k..n+1]);
}


/*
 * Los cuatro lemas siguientes tratan los diferentes casos
 * de actualización de las variables s, t del bucle principal.
 *
 * Son copias más o menos exactas unos de otros.
 */

lemma MaxPos(x : array<int>, n : nat, s : int, s1 : int)
	requires x != null && n < x.Length
	requires x[n] > 0
	requires Max(s, set p | 0 <= p <= n :: Prod(x[p..n]))

	requires s1 == Max2(s * x[n], 1)

	ensures Max(s1, set p | 0 <= p <= n+1 :: Prod(x[p..n+1]))
{
	// (1) s * x[n] >= 1 por reducción al absurdo (por probar)

	if s * x[n] < 1 {
		// Como x[n] >= 1 necesariamente
		assert s < 1;
		// Pero s es máximo de un conjunto en el que hay un 1
		assert Prod(x[n..n]) == 1;
		// Absurdo
	}

	// (2) s * x[n] es cota superior del nuevo conjunto

	forall p | 0 <= p <= n
		ensures s * x[n] >= Prod(x[p..n+1])
	{
		// Aplicar definición de producto, cancelar x[n] e hipótesis
		assert x[p..n+1][..n-p] == x[p..n];
	}

	// (3) s * x[n] está en el nuevo conjunto

	LemaConPr(x, s, n);
}

lemma MinPos(x : array<int>, n : nat, t : int, t1 : int)
	requires x != null && n < x.Length
	requires x[n] > 0
	requires Min(t, set p | 0 <= p <= n :: Prod(x[p..n]))

	requires t1 == Min2(t * x[n], 1)

	ensures Min(t1, set p | 0 <= p <= n+1 :: Prod(x[p..n+1]))
{
	// (1) t * x[n] es el mínimo

	if t * x[n] <= 1 {

		// (1.1) Es cota inferior del nuevo conjunto

		forall p | 0 <= p <= n
			ensures t * x[n] <= Prod(x[p..n+1])
		{
			// Aplicar definición de producto, cancelar x[n] e hipótesis
			assert x[p..n+1][..n-p] == x[p..n];
		}

		// (1.2) Está en el nuevo conjunto

		LemaConPr(x, t, n);
	}

	// (2) El mínimo es 1

	else {
		assert t >= 1;

		// (2.1) Es cota inferior

		forall p | 0 <= p <= n
			ensures 1 <= Prod(x[p..n+1])
		{
			// Aplicar definición de producto, cancelar x[n] e hipótesis
			assert x[p..n+1][..n-p] == x[p..n];
		}

		// (2.2) Está en el conjunto

		assert Prod(x[n+1..n+1]) == 1;

	}
}

lemma MinNeg(x : array<int>, n : nat, s : int, t1 : int)
	requires x != null && n < x.Length
	requires x[n] < 0
	requires Max(s, set p | 0 <= p <= n :: Prod(x[p..n]))

	requires t1 == Min2(s * x[n], 1)

	ensures s * x[n] <= 1
	ensures Min(t1, set p | 0 <= p <= n+1 :: Prod(x[p..n+1]))
{
	// (1) s * x[n] <= 1 de forma directa sin RA

	/*
	 * La demostración directa hace que el lema tarde bastante más
	 * en verificarse, tal vez debido a que el aserto confunde al
	 * demostrador en las siguientes verificaciones y en la reducción
	 * al absurdo queda muy restringido su efecto.
	 *
	 * Para conseguir ese efecto sin usar RA, se ha puesto un condicional
	 * incondicional y funciona aunque en menor medida.
	 */

	if true {
		assert Prod(x[n..n]) == 1;
	}

	// (2) s * x[n] es cota inferior del nuevo conjunto

	forall p | 0 <= p <= n
		ensures s * x[n] <= Prod(x[p..n+1])
	{
		// Aplicar definición de producto,
		// cancelar x[n] con signo e hipótesis
		assert x[p..n+1][..n-p] == x[p..n];
	}

	// (3) s * x[n] está en el nuevo conjunto

	LemaConPr(x, s, n);
}

lemma MaxNeg(x : array<int>, n : nat, t : int, s1 : int)
	requires x != null && n < x.Length
	requires x[n] < 0
	requires Min(t, set p | 0 <= p <= n :: Prod(x[p..n]))

	requires s1 == Max2(t * x[n], 1)

	ensures Max(s1, set p | 0 <= p <= n+1 :: Prod(x[p..n+1]))
{
	// (1) t * x[n] es el máximo

	if t * x[n] >= 1 {

		// (1.1) Es cota superior del nuevo conjunto

		forall p | 0 <= p <= n
			ensures t * x[n] >= Prod(x[p..n+1])
		{
			// Aplicar definición de producto, cancelar x[n] e hipótesis
			assert x[p..n+1][..n-p] == x[p..n];
		}

		// (1.2) Está en el nuevo conjunto

		LemaConPr(x, t, n);
	}

	// (2) El máximo es 1

	else {
		assert t >= 0;

		// (2.1) Es cota superior

		forall p | 0 <= p <= n
			ensures 1 >= Prod(x[p..n+1])
		{
			// Aplicar definición de producto, cancelar x[n] e hipótesis
			assert x[p..n+1][..n-p] == x[p..n];
		}

		// (2.2) Está en el conjunto

		assert Prod(x[n+1..n+1]) == 1;

	}
}

method seg_prod_max(x : array<int>) returns (r : int)
	requires x != null

	ensures Max(r, set j : nat, i : nat | 0 <= i <= j <= x.Length ::
		Prod(x[i..j]))
{
	var n, s, t := 0, 1, 1;

	r := 1;

	// El producto vacío es 1 (las variables s,t tienen
	// un valor inicial correcto)
	assert Prod(x[0..0]) == 1;

	while n != x.Length
		invariant 0 <= n <= x.Length
		invariant Max(s, set p | 0 <= p <= n :: Prod(x[p..n]))
		invariant Min(t, set p | 0 <= p <= n :: Prod(x[p..n]))

		invariant Max(r, set j : nat, i : nat | 0 <= i <= j <= n ::
			Prod(x[i..j]))

		decreases x.Length - n
	{
		// Recuerda que hay producto de valor 1 en todo caso
		assert Prod(x[n+1..n+1]) == 1;

		// Esta igualdad se utilizará en múltiples ocasiones
		assert forall p | 0 <= p <= n :: x[p..n+1][..n-p] == x[p..n];

		if x[n] == 0 {
			s, t := 1, 0;

			// Justifica el valor dado a s y t
			assert forall p | 0 <= p <= n :: Prod(x[p..n+1]) == 0;
			assert Prod(x[0..n+1]) == 0;
		}

		else if x[n] > 0 {

			ghost var s0, t0 := s, t;

			s, t := Max2(s * x[n], 1), Min2(t * x[n], 1);

			MaxPos(x, n, s0, s);
			MinPos(x, n, t0, t);
		}

		else /* x[n] < 0 */ {

			ghost var s0, t0 := s, t;

			s, t := Max2(t * x[n], 1), Min2(s * x[n], 1);

			MinNeg(x, n, s0, t);
			MaxNeg(x, n, t0, s);
		}

		r := Max2(r, s);
		n := n + 1;
	}
}
