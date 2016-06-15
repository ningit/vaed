/**
 * Versión que no continúa si no es estrictamente necesario.
 *
 * En Dafny las llamadas a método no pueden formar parte de expresiones,
 * por tanto es obligatoria la presencia del if. Otra alternativa es usar
 * function method.
 */

/**
 * En este ejemplo se utilizan anotaciones {:trigger a[i]} para indicar que
 * se escoja {a[i]} como disparador en los dos cuantificadores que aparecen.
 * Esto ocurre así por defecto pero Dafny se queja porque estos disparadores
 * pueden producir bucles en el demostrador.
 *
 * Dicho problema no se evita pero no tiene consecuencias en este caso.
 * La anotación evita la advertencia y hace explícito que se ha decidido
 * conscientemente usarlos.
 */

method capicua?<T(==)>(a : array<T>) returns (b : bool)
	requires a != null && a.Length > 0

	ensures b == forall i {:trigger a[i]} | 0 <= i < a.Length/2 :: a[i] == a[a.Length-1 - i]
{
	b := gcapicua?(a, (a.Length-1) / 2);
}

method gcapicua?<T(==)>(a : array<T>, n : nat) returns (b : bool)
	requires a != null
	requires 0 <= n < a.Length

	ensures b == forall i {:trigger a[i]} | 0 <= i <= n :: a[i] == a[a.Length-1 - i]
{
	if n == 0 {
		b := a[0] == a[a.Length-1];
	}

	else /* n > 0 */ {
		b := a[n] == a[a.Length-1 - n];

		if b {
			b := gcapicua?(a, n-1);
		}
	}
}
