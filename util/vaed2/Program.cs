using System;
using System.Diagnostics;
using System.IO;

namespace vaed
{
	class MainClass
	{
		public static int Main (string[] args)
		{
			// Usa el intérprete de parámetros de entrada
			ParamPars param = new ParamPars ();

			#region Tareas

			param.Descripción = "Verificador en serie y otras utilidades para Vaed";

			param.Parámetros.Add(new Parámetro(
				"dafnyexe",
				"Ubicación del ejecutable de Dafny",
				1,
				"dafny"
			));

			param.Parámetros.Add(new Parámetro(
				"caché",
				"Ubicación de la caché de resultados de verificación",
				1,
				"vaed.cache"
			));

			// Añade las tareas
			param.Tareas.Add (new Revisar());
			param.Tareas.Add (new Maquetar ());
			param.Tareas.Add (new Servir ());

			#endregion

			// Si hay un error en los parámetros de entrada falla
			// y muestra un mensaje de ayuda

			if (!param.Procesar (args)) {
				Console.Write (param.MsgAyuda ());

				return 3;
			}

			// Carga la caché y el explorador común a todas las tareas

			Caché caché = new Caché ();

			if (File.Exists (param.Valores["caché"][0])) {
				caché.Cargar (param.Valores["caché"][0]);
			}

			Explorador expl = new Explorador ();

			// Y ejecuta la tarea seleccionada

			param.Tarea.ejecutar (caché, expl, param.Valores);

			caché.Guardar (param.Valores["caché"][0]);

			return 0;
		}
	}
}
