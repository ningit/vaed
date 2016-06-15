/**
 * El demostrador se basta él solo para demostrar la correción.
 */

method mult_rusa(x : nat, y : nat) returns (p : nat)
	ensures p == x * y

	decreases y
{
	if y == 0 {
		p := 0;
	}
	else if y == 1 {
		p := x;
	}
	else {
		var m := mult_rusa(2 * x, y / 2);

		p := m + x * (y % 2);
	}
}
