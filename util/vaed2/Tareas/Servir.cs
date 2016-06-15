using System;
using System.Collections.Generic;

namespace vaed
{
	public class Servir : Tarea
	{
		public string Nombre { get { return "servir"; } }

		public string Descripción { get { return "establece un servidor web para verificar en Dafny"; } }

		public List<Parámetro> Parámetros { get { return new List<Parámetro> {
					new Parámetro("puerto", "Puerto del servidor web", 1, "8080"),
					new Parámetro("acceso",
						"Proteger con usuario y clave (dada como usuario:clave)", 1)
			};
		} }


		public void ejecutar(Caché caché, Explorador expl, Dictionary<string, List<string>> args)
		{
			int puerto = 0;

			if (!int.TryParse (args ["puerto"] [0], out puerto)) {
				AyudanteConsola.imprimirError ("«" + args ["puerto"] [0]
					+ "» no parece ser un número de puerto");

				return;
			}

			string credencial = null;

			if (args.ContainsKey("acceso")) {

				credencial = args ["acceso"] [0];

				if (!credencial.Contains (":")) {
					AyudanteConsola.imprimirError ("«" + credencial
					+ "» no sigue el formato usuario:clave");

					return;
				}
			}

			ServidorWeb sw = new ServidorWeb (args["dafnyexe"][0], puerto, credencial);

			sw.DCaché = caché;
			sw.DExplorador = expl;

			sw.Run ();

			Console.WriteLine ("Servidor funcionando en el puerto " + puerto + ".");
			Console.WriteLine ("Pulse una tecla para salir...");
			Console.ReadKey();

			sw.Stop();
		}
	}
}

