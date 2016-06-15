#!/usr/bin/perl
#
# Programa para mejorar la legibilidad de la salida por consola de Dafny.
#
# Imita aproximadamente la salida del compilador de GNU en cuanto a los
# colores, los números de línea y la cita del código del error.

use Term::ANSIColor;

# Ejecuta Dafny

open(DAFNY, "dafny /compile:0 /timeLimit:10 @ARGV|");

my $desc = 0;
my %fuentes = ();

sub mostrarEnLinea {
	my $nlinea = $2;
	my $ncol = $3;

	$1 =~ m/^(.*\.dfy)(?:\[.*\]|)/;

	# Carga el archivo
	if ( !exists $fuentes{$1} ) {
		open(ARCH, $1);

		my @lineas = (<ARCH>);

		$fuentes{$1} = \@lineas;

		close(ARCH)
	}

	$linea = $fuentes{$1}[$nlinea - 1];

	{ 
		$linea =~ s/\t/ /g;

		# No cita las líneas con delimitadores
		if ( $linea =~ /^[ ]*[{}]$/ ) {
			return
		}
	}


	print "$linea";
	printf "%s%s\n", (' ' x $ncol), colored("^", 'bold green')
}

# Descomentar para quitar las citas
# sub mostrarEnLinea { }

while (<DAFNY>) {
	# Líneas con sangrado
	if ( $_ =~ m/^    / ) {
		$desc == 1 or print "$_";

		next;
	}
	elsif ( $desc == 1 ) {
		$desc = 0;
	}

	# Errores
	if ( $_ =~ m/^(.*)\((\d+),(\d+)\): Error([^:]*)?: (.*)/ ) {
		printf "%s %s $5\n", colored("$1:$2:$3:", 'bold'), colored("Error$4:", 'bold red');

		mostrarEnLinea($1, $2, $3)
	}
	# Falta de tiempo
	elsif ( $_ =~ m/^(.*)\((\d+),(\d+)\): Timed out on(.+)?: (.*)/ ) {
		printf "%s %s $5\n", colored("$1:$2:$3:", 'bold'), colored("Timed out on$4:", 'bold red');

		mostrarEnLinea($1, $2, $3)
	}
	# Advertencias
	elsif ( $_ =~ m/^(.*)\((\d+),(\d+)\): Warning: (.*)/ ) {
		printf "%s %s $4\n", colored("$1:$2:$3:", 'bold'), colored("Warning:", 'bold magenta')
	}
	# Ubicaciones relacionadas
	elsif ( $_ =~ m/^(.*)\((\d+),(\d+)\): Related location(.*)/ ) {
		printf "%s %s$4\n", colored("$1:$2:$3:", 'bold'), colored("Related location", 'bold cyan');

		mostrarEnLinea($1, $2, $3)
	}
	# Mensajes informativos
	elsif ( $_ =~ m/^(.*)\((\d+),(\d+)\): Info: (.*)/ ) {
		printf "%s %s $4\n", colored("$1:$2:$3:", 'bold'), colored("Info:", 'bold cyan')
	}
	# Otros mensajes de línea
	elsif ( $_ =~ m/^(.*)\((\d+),(\d+)\): (.*)/ ) {
		printf "%s $4\n", colored("$1:$2:$3:", 'bold')
	}
	# Mensajes incomprensibles
	elsif ( $_ =~ m/^Execution trace:/ ) {
		$desc = 1
	}
	# Resumen del final de la ejecución
	elsif ( $_ =~ m/Dafny program verifier finished with (\d+) verified, (\d+) error(s)?(, (\d+) time out(s)?)?$/ ) {

		$texto = sprintf "Dafny program verifier finished with %s verified, %s error$3",
			colored ("$1", 'bold green'), colored("$2", 'bold red');

		if ( defined $4 ) {
			$texto = $texto . sprintf ", %s time out$6", colored("$5", 'bold red')
		}

		printf "%s\n", $texto
	}
	else {
		print "$_"
	}
}
