using System;
using System.IO;
using System.Runtime.Serialization.Formatters.Binary;
using System.Collections.Generic;

namespace vaed
{
	/*
	 * Caché de verificaciones.
	 */
	public class Caché
	{
		public Caché ()
		{
			entradas = new Dictionary<string, EntradaCaché> ();
		}

		public void Insertar(string id, InformeDafny inf)
		{
			var ent = new EntradaCaché ();

			ent.inf = inf;
			ent.fmod = File.GetLastWriteTimeUtc(id);

			entradas [id] = ent;
		}

		public bool EnCaché(string id)
		{
			if (!entradas.ContainsKey (id))
				return false;

			return entradas [id].fmod < File.GetLastWriteTimeUtc(id);
		}

		public bool Consulta(string id, out InformeDafny inf)
		{
			EntradaCaché ent;

			entradas.TryGetValue (id, out ent);

			if (ent.fmod < File.GetLastWriteTimeUtc (id)) {
				inf = default(InformeDafny);

				return false;
			}

			inf = ent.inf;

			return true;
		}

		public InformeDafny this[string id]
		{
			get { return entradas [id].inf; }
			set { Insertar(id, value); }
		}

		public void Cargar(string narc) {

			Stream acach = File.OpenRead (narc);

			BinaryFormatter bf = new BinaryFormatter ();

			entradas = bf.Deserialize (acach) as Dictionary<string, EntradaCaché>;

			acach.Close ();
		}

		public void Guardar(string narc) {
			Stream acach = File.OpenWrite (narc);

			BinaryFormatter bf = new BinaryFormatter ();

			bf.Serialize (acach, entradas);

			acach.Close ();
		}

		/*
		 * Estructura de uso interno
		 */
		[Serializable]
		struct EntradaCaché
		{
			public InformeDafny inf;
			public DateTime fmod;
		}

		private Dictionary<string, EntradaCaché> entradas;
	}
}