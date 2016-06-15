using System;
using System.Collections.Generic;

namespace vaed
{
	public class Revisar : Tarea
	{
		public void ejecutar(Caché caché, Explorador expl, Dictionary<string, List<string>> args) {

			// Crea una instancia de Dafny

			Dafny dafny = new Dafny (args["dafnyexe"][0]);

			if (!dafny.Accesible) {
				AyudanteConsola.imprimirError("no se encuentra el ejecutable «"
					+ args["dafnyexe"][0] + "»");

				return;
			}

			// Verifica los archivos
			int correctos = 0;
			int erroneos = 0;

			foreach (UnidadDafny dfy in expl.Unidades){
				InformeDafny informe = null;

				bool yaMostrado = false;

				if (!caché.Consulta (dfy.Uri, out informe)) {
					Console.WriteLine ("Verificando " + dfy.Uri + "...");

					informe = dafny.Verificar (dfy.Uri);

					caché [dfy.Uri] = informe;

					MostrarInforme (dfy, informe);

					yaMostrado = true;
				}

				if (informe.Resultado == InformeDafny.Result.CORRECTO) {
					correctos++;
				}
				else {
					erroneos++;

					if (!yaMostrado)
						MostrarInforme (dfy, informe);
				}
			}

			Console.WriteLine ();
			Console.WriteLine ("{0} verificados correctamente, {1} erróneos.", correctos, erroneos);
		}

		private void MostrarInforme(UnidadDafny dfy, InformeDafny inf) {

			// Sería interesante poner milisegundos pero no tiene tanta fidelidad

			Console.Write (String.Format("{0,-30} ({1,2}s): ", 
				dfy.Nombre.Length > 30 ? dfy.Nombre.Substring(0, 27) + "..." : dfy.Nombre,
				inf.Tiempo.TotalSeconds));


			ConsoleColor color = ConsoleColor.White;

			if (inf.Resultado == InformeDafny.Result.EVERIFICACION)
				color = ConsoleColor.Magenta;
			else if (inf.Resultado != InformeDafny.Result.CORRECTO)
				color = ConsoleColor.Red;

			Console.ForegroundColor = color;

			Console.WriteLine (inf.Resultado.Desc());

			Console.ResetColor();
		}

		public List<Parámetro> Parámetros {
			get { return new List<Parámetro>(); }
		}

		public string Descripción {
			get { return "prueba la corrección de los archivos bajo control"; }
		}

		public string Nombre {
			get { return "revisar"; }
		}
	}
}
