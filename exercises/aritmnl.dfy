/**
 * Este módulo incluye algunos resultados bastante elementales sobre la
 * división entera y el módulo que el demostrador no sabe por defecto.
 */

/**
 * La demostración de estos dos lemas resultó más difícil de lo esperado.
 * Muchos asertos son prescindibles pero se incluyen para seguir la idea
 * de la demostración. Tal vez haya demostraciones más directas sabiendo
 * cómo trata el demostrador la aritmética no lineal (hay una opción
 * «/noNLarith» para disminuir su conocimiento sobre el particular).
 *
 * Las demostraciones aquí utilizan que el módulo es positivo y menor que
 * el divisor y con ello hacen acotaciones en forma de sándwich.
 *
 * Ha sido necesario definir variables en las demostraciones. Sin ellas el
 * demostrador no era capaz de demostrar lo que está demostrado. Parece que
 * aunque dos términos compuestos sean sintácticamente iguales no los
 * considera el mismo y no puede aplicarles algo como
 * forall x :: P(x) ==> Q(x).
 */

module AritmNL {

lemma DivPorFactor(m : nat, k : int)
	requires m != 0
	ensures (k*m) / m == k
	ensures (k*m) % m == 0
{
	// Al divisor le llamo d
	var d := (k*m)/m;

	// Se toma lo siguiente como base
	assert k*m == d * m + (k*m) % m;
	assert 0 <= (k*m) % m < m;

	// Se substituye de acuerdo a la acotación
	assert k*m >= d * m;
	assert k*m < d * m + m;

	// Se cancelan factores comunes
	assert k >= d;

	// La otra desigualdad resulta más compleja
	assert k*m - d*m - m < 0;
	assert (k - d - 1) * m < 0;

	var dd := k - d - 1;

	assert dd >= 0 ==> dd * m >= 0;

	assert dd < 0;
	assert k - d - 1 < 0;

	// Con esta acotación sólo puede ser k
	assert k - 1 < d <= k;
}

lemma ModMasMultiplo(n : int, m : nat, k : int)
	requires m != 0
	ensures (n + k * m) % m == n % m
{
	// Partimos de los dos siguientes asertos
	assert n+k*m == (n+k*m)/m * m + (n+k*m)%m;
	assert n == n/m*m + n%m;

	// Substituyendo el segundo en el primero
	assert n/m*m + n%m + k*m == (n+k*m)/m * m + (n+k*m)%m;

	// Se pasan a la izda los múltiplos de m
	assert n/m*m + k*m - (n+k*m)/m * m == (n+k*m)%m - n%m;

	// Se saca factor común
	assert (n/m + k - (n+k*m)/m) * m == (n+k*m)%m - n%m;

	// Por la acotación de los módulos se sabe que la parte dcha
	// está entre -m y m exclusive.
	// De la parte izda se deduce que es múltiplo de m y el único
	// múltiplo de m en ese intervalo es 0.
	assert -m < (n+k*m)%m - n%m < m;

	// Hay que ayudarle para llegar a esa conclusión
	// t es la parte izquierda sin m
	var t := n/m + k - (n+k*m)/m;

	assert -m < t * m < m;

	// Aplicamos el lema demostrado anteriormente
	DivPorFactor(m, t);

	assert -1 < t < 1;

	// Luego t == 0 y eso implica lo buscado
}

lemma SumaMod0(a : int, b : int, m : nat)
	requires m != 0
	requires a % m == 0
	requires b % m == 0

	ensures (a + b) % m == 0
	ensures (a - b) % m == 0
{
		// Descompone en divisor * cociente + resto
		assert a == (a / m) * m;
		assert b == (b / m) * m;

		// Para luego sacar factor común
		assert a + b == (a/m + b/m) * m;
		assert a - b == (a/m - b/m) * m;

		DivPorFactor(m, a/m + b/m);
		DivPorFactor(m, a/m - b/m);
}

lemma SumaMod(a : int, b : int, m : nat)
	requires m != 0

	ensures (a + b) % m == (a % m + b % m) % m
	ensures (a - b) % m == (a % m - b % m) % m
{
		// Descompone en divisor * cociente + resto
	//	assert a == (a / m) * m + a % m;
	//	assert b == (b / m) * m + b % m;

		// Para luego sacar factor común
	//	assert a + b == (a/m + b/m) * m + (a % m + b % m);
	//	assert a - b == (a/m - b/m) * m + (a % m - b % m);

		ModMasMultiplo(a % m + b % m, m, a/m + b/m);
		ModMasMultiplo(a % m - b % m, m, a/m - b/m);
}

}
