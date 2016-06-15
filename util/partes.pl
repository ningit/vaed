#!/usr/bin/perl
#
# Programa para verificar archivos Dafny por partes.
#
# No considera constructores.

use Term::ANSIColor;

if (@ARGV != 1) {
	print "Command syntax: $0 file.dfy\n";

	exit 1
}

open(DFY, $ARGV[0]) or die "File not found";

my $errors = 0;

while(<DFY>) {
	# m/\w+(method|function\w+method|ghost\w+method|lemma|function)\w+(.*)/

	if ($_ =~ m/((method|function|ghost|lemma)\s+)+({.*}\s+)*([^\(\s\.]+)(\(|...).*/)
	{
		print colored("Verifying $4...\n", 'bold blue');

		@args = ("dafny", "/compile:0", "/timeLimit:10", "$ARGV[0]", "/proc:*.$4");

		system(@args);

		if ($? >> 8 == 0) {
			print colored("Correct\n", 'bold yellow');
		}
		else {
			print colored("Error\n", 'bold red');

			$errors += 1;
		}
	}
}

if ($errors == 0) {
	print colored("\n[] No errors.\n", 'bold yellow');
}
else {
	print colored("\n[] $errors errors.\n", 'bold red');
}
