using System;
using System.Diagnostics;
using System.IO;
using System.Text;
using System.ComponentModel;

namespace vaed
{

	[Serializable]
	public class InformeDafny {

		// TODO: contar número de errores

		public InformeDafny(string salida, int exitcode, TimeSpan tiempo) {
			Salida = salida;
			Tiempo = tiempo;

			/*
			 * Experimentalmente se ha llegado a la siguiente correspondencia
			 * entre códigos de retorno y las circunstancias que los motivan.
			 */
			switch (exitcode) {
			case 0:
				Resultado = InformeDafny.Result.CORRECTO;
				break;
			case 1:
				// Realmente puede tratarse de otro error como
				// que no se encuentra el archivo...

				Resultado = InformeDafny.Result.ESINTAXIS;
				break;
			case 2:
				Resultado = InformeDafny.Result.ETIPOS;
				break;
			case 3:
				Resultado = InformeDafny.Result.EVERIFICACION;
				break;
			default:
				Resultado = InformeDafny.Result.DESCONOCIDO;
				break;
			}
		}

		// Texto íntegro de la salida producida por Dafny
		public readonly string Salida;

		// Resumen del resultado
		public readonly InformeDafny.Result Resultado;

		public readonly TimeSpan Tiempo;

		public enum Result {
			// Dafny program verifier finished with X verified, 0 errors
			[Description("correcto")]
			CORRECTO,
			// X parse errors detected in F.dfy
			[Description("error de sintaxis")]
			ESINTAXIS,
			// X resolution/type errors detected in F.dfy
			[Description("error de tipos")]
			ETIPOS,
			// Dafny program verifier finished with X verified, Y errors
			[Description("error de verificación")]
			EVERIFICACION,
			// Pues eso
			[Description("error desconocido")]
			DESCONOCIDO
		}
	}

	// Extensión del enumerador Result para que sea más cómodo su uso

	public static class ResultExtension
	{
		public static string Desc(this InformeDafny.Result res)
		{
			var atribs = res.GetType ().GetMember(res.ToString())[0]
				.GetCustomAttributes(typeof(DescriptionAttribute), false);

			return (atribs[0] as DescriptionAttribute).Description;
		}

		public static bool EsError(this InformeDafny.Result res)
		{
			return res != InformeDafny.Result.CORRECTO;
		}
	}


	// Instancia del compilador/verificador de Dafny

	public class Dafny
	{
		public Dafny (string cmd = "dafny", string args = Dafny.ParamsDefecto)
		{
			if (cmd.Contains("/") || cmd.Contains("\\"))
				cmd = Path.GetFullPath (cmd);

			dafnypar = new ProcessStartInfo (cmd);

			Params = args;

			dafnypar.RedirectStandardOutput = true;
			dafnypar.UseShellExecute = false;
		}

		public bool Accesible {
			get {
				dafnypar.Arguments = "";

				try {
					Process.Start (dafnypar);

					return true;
				}
				catch (Exception e) {
					Console.Error.WriteLine (e.Message);
				}

				return false;
			}
		}

		public InformeDafny Verificar(string fio)
		{
			// Añade el nombre de archivo a los parámetros
			dafnypar.Arguments = Params + " " + fio;

			// Ejecuta el proceso y lee su salida estándar
			var proc = Process.Start (dafnypar);

			StreamReader sout = proc.StandardOutput;

			proc.Start ();

			// proc.BeginOutputReadLine

			// Espera a que acabe el proceso

			string res = sout.ReadToEnd ();

			proc.WaitForExit ();

			// Convendría poner TotalProcessorTime o algo semejante

			return new InformeDafny(res, proc.ExitCode, proc.ExitTime - proc.StartTime);
		}

		// Verifica un programa dado como cadena de texto

		public InformeDafny VerificarTexto(string txt)
		{
			// Es reentrante 100 nanosegundos mediante

			// Crea un archivo temporal en el directorio temporal con
			// la esperanza de que este repetido (usa la fecha)

			string nombreTemp = "dafnytmp-" + DateTime.Now.ToFileTimeUtc() + ".dfy";

			nombreTemp = Path.Combine (Path.GetTempPath (), nombreTemp);

			var arch = File.Open (nombreTemp, FileMode.Create);

			// Copia el texto txt en él y lo verifica

			arch.Write (Encoding.UTF8.GetBytes (txt), 0, txt.Length);

			arch.Close ();

			var inf = Verificar (nombreTemp);

			// Finalmente borra el archivo

			// TODO por seguridad sería conveniente borrar el
			// nombre del archivo de la salida

			File.Delete (nombreTemp);

			return inf;
		}

		private ProcessStartInfo dafnypar;

		// Parámetros pasados al compilador/verificador

		public string Params;

		// Parámetros por defecto (los de la extensión de VisualStudio)

		public const string ParamsDefecto = "/compile:0 /timeLimit:10 /autoTriggers:1";
	}
}

