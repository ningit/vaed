using System;
using System.Collections.Generic;
using System.IO;
using System.Text.RegularExpressions;

namespace vaed
{
	public class Explorador
	{
		public Explorador()
		{
			// Categorías iniciales

			raíz = new [] {
				new CatDirectorio("exercises", "Ejercicios"),
				new CatDirectorio("algorithms", "Algoritmos"),
				new CatDirectorio("structures", "Estructuras de datos")
			};
		}

		public IEnumerable<UnidadDafny> Unidades
		{
			// Recorre el árbol (de directorios más o menos) en profundidad
			// devolviendo las unidades Dafny que encuentra

			get
			{
				// Pila que guarda listas de hijos sin terminar de recorrer y el
				// índice por el que se quedaron

				Stack<Tuple<NodoMapa[], int>> pila = new Stack<Tuple<NodoMapa[], int>> ();

				var acts = raíz;
				int ind = 0;

				while (true) {

					while (ind < acts.Length) {

						var nodo = acts [ind];

						if (nodo is UnidadDafny) {

							yield return acts [ind] as UnidadDafny;

							ind++;

						} else {

							// Apila el estado actual si más hijos
							// y pasa a explorar el hijo

							if (ind != acts.Length - 1)
								pila.Push (Tuple.Create(acts, ind+1));

							acts = (acts [ind] as CatDirectorio).Elementos;
							ind = 0;

							continue;
						}
					}

					// Se han acabado los hijos, rescata otra lista de la pila
					// o acaba si ya no hay más

					if (pila.Count == 0)
						break;

					var tup = pila.Pop ();

					acts = tup.Item1;
					ind = tup.Item2;
				}
			}
		}

		private NodoMapa[] raíz;

		// Elementos en la raíz de la jerarquía

		public NodoMapa[] Raíz {
			get { return raíz; }
		}
	}

	//
	// Clases en las que se organiza la jerarquía de archivos
	// para verificar
	//

	public interface NodoMapa : IComparable<NodoMapa>
	{
		// Identificador único
		// (en la posición actual del sistema de archivos)

		string Uri { get; }

		// Nombre amigable

		string Nombre { get;  }
	}

	// Clasificación cualquiera de archivos

	public interface Categoría : NodoMapa
	{
		NodoMapa[] Elementos { get; }
	}

	// Clasificación con soporte en un directorio

	public class CatDirectorio : Categoría
	{
		public CatDirectorio(string uri, string nom, bool rec = true) {
			Uri = uri;
			Nombre = Path.GetFileName(nom);

			if (!string.IsNullOrEmpty(nom))
				Nombre = char.ToUpper (Nombre [0]) + Nombre.Substring (1);

			recursivo = rec;
		}

		public virtual int CompareTo(NodoMapa nm)
		{
			return Uri.CompareTo (nm.Uri);
		}

		public NodoMapa[] Elementos {
			get {
				// Recorre el directorio buscando hijos

				if (elementos == null) {

					if (!Directory.Exists (Uri)) {
						elementos = new NodoMapa[0];

						return elementos;
					}

					// Omite archivos ocultos y los que empiecen con _
					Func<string, bool> omitible = delegate(string s) {
						s = Path.GetFileName(s);

						return s.StartsWith (".") || s.StartsWith ("_");
					};

					SortedSet<NodoMapa> nodos = new SortedSet<NodoMapa>();

					// Enumera los archivos

					foreach (var arch in Directory.GetFiles (Uri, "*.dfy")) {

						if (!omitible(arch))
							nodos.Add (FábricaNodoMapa.nuevoNodo(arch));

					}

					// Enumera las carpetas

					if (recursivo) {

						foreach (var dir in Directory.GetDirectories (Uri)) {

							if (!omitible (dir))
								nodos.Add (new CatDirectorio (dir, dir));
						}

					}

					elementos = new NodoMapa[nodos.Count];
					nodos.CopyTo (elementos);
				}

				return elementos;
			}
		}

		private NodoMapa[] elementos = null;

		public string Uri { get; private set; }

		public string Nombre { get; private set; }

		private bool recursivo;
	}

	// Programa de Dafny

	public class UnidadDafny : NodoMapa
	{
		public UnidadDafny(string uri, string nom) {
			this.Uri = uri;
			this.Nombre = nom;
		}

		public UnidadDafny(string uri)
		{
			this.Uri = uri;
			this.Nombre = uri;
		}

		public virtual int CompareTo(NodoMapa nm)
		{
			return Nombre.CompareTo(nm.Nombre);
		}

		public string Uri { get; private set; }

		public virtual string Nombre { get; private set; }
	}

	public class EjercicioDafny : UnidadDafny
	{

		public EjercicioDafny(string uri, int tema, int número, bool prop, string coms = "")
			: base (uri)
		{
			Tema = tema;
			Número = número;
			Propuesto = prop;
			coment = coms;
		}

		public override int CompareTo(NodoMapa nm)
		{
			if (nm is EjercicioDafny) {
				var ed = nm as EjercicioDafny;

				if (Tema < ed.Tema)
					return -1;
				else if (Tema > ed.Tema)
					return 1;

				if (Propuesto && !ed.Propuesto)
					return 1;
				else if (!Propuesto && ed.Propuesto)
					return -1;

				if (Número < ed.Número)
					return -1;
				else if (Número > ed.Número)
					return 1;

				return coment.CompareTo (ed.coment);
			} else {
				return -1;
			}

		}

		private string coment;

		public int Tema { get; private set; }
		public int Número { get; private set; }
		public bool Propuesto { get; private set; }

		public override string Nombre {
			get {
				return String.Format ("Ejercicio {0} {1}.{2}{3}",
					Propuesto ? "propuesto" : "resuelto",
					Tema,
					Número,
					coment
				);
			}
		}
	}

	class FábricaNodoMapa
	{
		public static NodoMapa nuevoNodo(string arch)
		{
			var nom = Path.GetFileNameWithoutExtension (arch);

			// Hace el nombre más legible

			var ma = regejer.Match (nom);

			if (ma.Success) {

				var prop = ma.Groups [1].Value == "p";
				var tema = int.Parse(ma.Groups [2].Value);
				var número = int.Parse(ma.Groups [3].Value);
				var coment = ma.Groups [4].Value != "" ? " (" + ma.Groups [4].Value + ")" : "";

				return new EjercicioDafny (arch, tema, número, prop, coment);

			} else {
				// Separa las palabras del nombre

				var tmp = nom;

				nom = Char.ToUpper (nom [0]).ToString();

				for (int i = 1; i < tmp.Length; i++)  {
					if (Char.IsUpper (tmp [i]))
						nom += " " + Char.ToLower(tmp[i]);
					else
						nom += tmp [i];
				}

				return new UnidadDafny (arch, nom);
			}
		}

		private static Regex regejer = new Regex(@"e(r|p)?(\d+).(\d+)(aux|v2)?");
	}
}

