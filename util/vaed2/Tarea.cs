using System;
using System.IO;
using System.Collections.Generic;

namespace vaed
{
	public interface Tarea
	{
		// Método que realiza la tarea

		void ejecutar(Caché caché, Explorador expl, Dictionary<string, List<string>> args);

		// Un nombre para nombrarla y mostrarla

		string Nombre { get; }

		// Una descripción que explique brevemente su cometido

		string Descripción { get; }

		// Listas de parámetros que admite

		List<Parámetro> Parámetros { get; }
	}

	public class AyudanteConsola
	{
		public static void imprimirError(string msj) {
			Console.ForegroundColor = ConsoleColor.Red;
			Console.WriteLine ("Error: " + msj + ".");
			Console.ResetColor ();
		}
	}
}

