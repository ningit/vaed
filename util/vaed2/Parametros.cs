using System;
using System.Collections.Generic;
using System.Text;
using System.Linq;

namespace vaed
{
	// Parámetro de línea de comandos

	public class Parámetro
	{
		public Parámetro(string nom, string desc, int aridad = 0,
			List<string> defecto = null)
		{
			Nombre = nom;
			Descripción = desc;
			Aridad = aridad;

			PorDefecto = defecto;
		}

		public Parámetro(string nom, string desc, int aridad,
			string defecto)
		{
			Nombre = nom;
			Descripción = desc;
			Aridad = aridad;

			PorDefecto = defecto != null ? new List<string>{defecto}
				: null;
		}

		public string Nombre { get; set; }
		public string Descripción { get; set; }
		public int Aridad { get; set; }

		public List<string> PorDefecto { get; set; }
	}

	// Procesador de parámetros y otras opciones

	public class ParamPars
	{
		public ParamPars()
		{
			Tareas = new List<Tarea> ();
			Parámetros = new List<Parámetro> ();

			// Manejador de errores por defecto

			ManejadorErrores = delegate(string msj) {
				Console.ForegroundColor = ConsoleColor.Red;
				Console.WriteLine (msj);
				Console.ResetColor ();
				Console.WriteLine();
			};
		}

		// Delegado que trata los errores generados en el parseo

		public TipoManejadorErrores ManejadorErrores;

		public delegate void TipoManejadorErrores(string x);


		public bool Procesar(string[] args) {

			// Ineficiente en demasía

			var mparams = new Dictionary<String, Parámetro>();
			var mtareas = new Dictionary<String, Tarea>();

			var ltareas = new List<String> ();

			Valores = new Dictionary<string, List<string>> ();

			foreach (Parámetro par in Parámetros) {
				mparams.Add (par.Nombre, par);

				if (par.PorDefecto != null) {
					Valores[par.Nombre] = par.PorDefecto;
				}
			}

			foreach (Tarea tar in Tareas) {
				mtareas.Add(tar.Nombre, tar);

				ltareas.Add (tar.Nombre);
			}

			Tarea escogida = null;

			for (int i = 0; i < args.Length; i++) {

				if (args [i].StartsWith ("--")) {
					var arg = args [i].Substring (2);

					if (mparams.ContainsKey (arg)) {
						var par = mparams [arg];

						if (args.Length - i <= par.Aridad) {
							ManejadorErrores ("No hay suficientes parámetros para «" +
								par.Nombre + "» que espera " + par.Aridad + ".");

							return false;
						}

						// Esto funciona incluso con aridad 0 pues la
						// presencia en el diccionario es significativa
						// aunque no lo sea su valor

						Valores[par.Nombre] = new List<string> (
							new ArraySegment<string>(args, i+1, par.Aridad)
						);

						i += par.Aridad;

					} else {
						ManejadorErrores ("Parámetro desconocido: «" + arg + "».");

						return false;
					}

				} else if (escogida != null) {

					ManejadorErrores ("Parámetro inesperado: «" + args [i] + "».");

					return false;

				} else {

					var list = ltareas.Where (ta => ta.StartsWith(args[i])).ToList();

					if (list.Count == 0) {

						ManejadorErrores ("Ninguna tarea responde al nombre de «" + args [i] + "».");

						return false;

					} else if (list.Count > 1) {

						ManejadorErrores ("Varias tareas responden al nombre de «" + args [i]
							+ "»:\n\t" + list.Aggregate("", (s, a) => a + " " + s));

						return  false;

					} else {
						escogida = mtareas [list[0]];

						// Añade los parámetros particulares de la tarea

						foreach (Parámetro par in escogida.Parámetros) {
							mparams.Add (par.Nombre, par);

							if (par.PorDefecto != null) {
								Valores[par.Nombre] = par.PorDefecto;
							}
						}
					}
				}
			}

			// Tarea que queda como escogida
			Tarea = escogida == null ? Tareas [0] : escogida;

			return true;
		}

		public string MsgAyuda() {
			// TODO mostrar la documentación de los parámetros de subcomandos

			StringBuilder sb = new StringBuilder ();

			// Hacer bien
			sb.AppendFormat ("uso: {0} [-h] ...\n", System.AppDomain.CurrentDomain.FriendlyName);

			// Descripción general
			sb.AppendLine ();
			sb.AppendLine (Descripción);
			sb.AppendLine ();

			// Subcomandos
			sb.AppendLine ("Subcomandos:");
			sb.AppendLine ();

			foreach (Tarea tarea in Tareas) {
				sb.AppendFormat (" {0}\n", tarea.Nombre);
				sb.AppendFormat ("\t{0}\n", tarea.Descripción);
			}

			sb.AppendLine ();

			// Argumentos opcionales
			sb.AppendLine ("Argumentos opcionales:");
			sb.AppendLine ();

			foreach (Parámetro par in Parámetros) {
				sb.AppendFormat (" --{0}\t{1}\n", par.Nombre, par.Descripción);
			}

			return sb.ToString ();
		}

		// Descripción general del programa (para el mensaje de ayuda)

		public string Descripción { get; set; }

		// Tareas soportadas por el programa

		public List<Tarea> Tareas { get; private set; }

		// Parámetros generales del programa

		public List<Parámetro> Parámetros { get; private set; }

		// Valores dados a los parámetros

		public Dictionary<string, List<string>> Valores { get; private set; }

		// Tarea elegida (valor válido sólo tras el parseo)

		public Tarea Tarea { get; private set; }
	}
}
