using System;
using System.IO;
using System.Collections.Generic;
using System.Diagnostics;
using System.Reflection;

namespace vaed
{
	public class Maquetar : Tarea
	{
		public string Nombre { get { return "maquetar"; } }

		public string Descripción { get { return "presenta los algoritmos en un archivo pdf"; } }

		public List<Parámetro> Parámetros { get { return new List<Parámetro>(); } }


		public void ejecutar(Caché caché, Explorador expl, Dictionary<string, List<string>> args)
		{
			this.caché = caché;

			// Crea un directorio temporal

			var tmpdir = Path.Combine (
				                Path.GetTempPath (),
								"dafnytex-" + DateTime.Now.ToFileTimeUtc()
			                );

			Directory.CreateDirectory (tmpdir);

			// Copia el paquete Dafny de Rustan Leino

			using (var arch = File.Create (Path.Combine (tmpdir, "dafny.sty"))) {

				Assembly.GetExecutingAssembly ().GetManifestResourceStream ("vaed.aux.dafny.sty").
					CopyTo (arch);

			};

			// Crea un archivo temporal

			tex = File.CreateText (Path.Combine (tmpdir, "código.tex"));

			Prólogo.CopyTo (tex.BaseStream);

			tex.Write (@"\begin{document}");

			nord = 0;
			nivel = 0;

			// Escribe los archivos siguiendo la jerarquía

			foreach (NodoMapa nodo in expl.Raíz) {
				Imprimir (nodo);
			}

			tex.Write (@"\end{document}");

			tex.Close ();

			// Ejecuta lualatex para compilar el tex generado

			ProcessStartInfo psi = new ProcessStartInfo ("lualatex", "código.tex");

			psi.WorkingDirectory = tmpdir;

			try {
				var lualatex = Process.Start (psi);

				lualatex.WaitForExit ();

				if (lualatex.ExitCode == 0) {
					File.Copy (Path.Combine(tmpdir, "código.pdf"), "código.pdf", true);
				} else {
					Console.Write ("Error al compilar con lualatex.");
				}
			}

			catch (System.ComponentModel.Win32Exception) {
				AyudanteConsola.imprimirError("luatex no está instalado o no se encuentra");
			}

			// Borra el directorio temporal

			Directory.Delete (tmpdir, true);
		}

		// Funciones para el recorrido recursivo en profundidad de la jerarquia
		// del árbol de archivos (vinculación dinámica múltiple frustrada)

		public void Imprimir(Categoría cat)
		{
			// Admite varios niveles como secciones de LaTeX

			string sección = "subsubsection";

			switch (nivel) {
			case 0:
				sección = "section";
				break;
			case 1:
				sección = "subsection";
				break;
			}

			nivel++;

			tex.WriteLine (@"\" + sección + "{" + cat.Nombre + "}");

			// Imprime recursivamente

			foreach (var elem in cat.Elementos) {
				Imprimir (elem);
			}

			nivel--;

		}

		private void Imprimir(UnidadDafny dfy)
		{
			// Busca información de ejecución en la caché

			InformeDafny informe = null;

			bool está = caché.Consulta (dfy.Uri, out informe);

			string desc = está ? informe.Resultado.Desc () : "no hay datos";
			string color = está ? (informe.Resultado.EsError () ? "red" : "green") : "blue";

			// Escribe el título del archivo
			tex.Write(String.Format(Título,
				EscaparLaTeX(dfy.Nombre),
				color,
				desc
			));

			// Escribe un enlace para el pdf
			tex.Write(String.Format("\t\\pdfbookmark[{2}]{{{0}}}{{l{1}}}\n",
				EscaparLaTeX(dfy.Nombre),
				nord,
				Math.Min(nivel+1, 3)
			));

			// Añade el archivo en un entorno listing
			tex.Write(String.Format("\t\\lstinputlisting{{{0}}}\n",
				Path.GetFullPath(dfy.Uri)));

			// Imprime la salida de error en caso de error

			if (está && informe.Resultado.EsError()) {
				tex.Write (String.Format("\\medskip \\begin{{center}}Salida de Dafny ({0}s):\\end{{center}}",
					informe.Tiempo.TotalSeconds));

				tex.Write(String.Format("{{\\footnotesize \\begin{{verbatim}}{0}\\end{{verbatim}}}}",
					informe.Salida));
			}

			// Cada archivo en una página
			tex.Write (@"\eject");

			nord++;
		}

		private void Imprimir(NodoMapa nodo) {

			if (nodo is UnidadDafny)
				Imprimir (nodo as UnidadDafny);
			else
				Imprimir (nodo as Categoría);

			// Requiere Microsoft.CSharp.dll
			// Imprimir (nodo as dynamic);
		}

		private string EscaparLaTeX(string s) {
			return s.Replace("_", "\\_");
		}

		// Prólogo LaTeX del archivo resumen
		private Stream Prólogo = Assembly.GetExecutingAssembly().
			GetManifestResourceStream("vaed.aux.maquetar.tex");

		// Título de cada archivo en LaTeX
		public const string Título = @"\noindent {{{{\bfseries {0}}}}} \hfill {{\color{{{1}}}$\mdlgblkcircle$}} {2}
\bigskip";

		// Caché de verificaciones

		private Caché caché;

		// Número de orden (cosas de hyperref)

		private int nord;

		// Nivel de sección

		private int nivel;

		// Archivo tex

		private StreamWriter tex;
	}
}
