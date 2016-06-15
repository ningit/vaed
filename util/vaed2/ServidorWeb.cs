using System;
using System.Net;
using System.Threading;
using System.Linq;
using System.Text;
using System.IO;
using System.Web;
using System.Text.RegularExpressions;

using System.Reflection;

// https://codehosting.net/blog/BlogEngine/post/Simple-C-Web-Server.aspx

namespace vaed
{
	public class ServidorWeb
	{
		private readonly HttpListener listener = new HttpListener();

		private readonly string DafnyExe;

		public ServidorWeb (string dafnyexe, int puerto, string creden = null)
		{
			if (!HttpListener.IsSupported)
				throw new NotSupportedException ("No soportado.");

			DCaché = null;
			DExplorador = null;
			DafnyExe = dafnyexe;

			CAcceso = creden;

			if (creden != null)
				listener.AuthenticationSchemes = AuthenticationSchemes.Basic;

			listener.Realm = "Servidor para Dafny";

			listener.Prefixes.Add ("http://+:" + puerto + "/");
			listener.Start ();
		}

		// Responde con un 404 (siempre que no se ajusta a lo
		// esperado)

		private void Responder404(HttpListenerContext ctx)
		{
			ctx.Response.StatusCode = 404;

			VolcarStream (Mens404, ctx.Response);

			ctx.Response.Close();
		}

		// Responde con la lista de los archivos

		private void ResponderLs(HttpListenerContext ctx)
		{
			if (DCaché == null || DExplorador == null) {
				Responder404 (ctx); return;
			}

			ctx.Response.StatusCode = 200;

			var wout = new StreamWriter(ctx.Response.OutputStream);

			// Parafernalia inicial

			wout.WriteLine (String.Format(Encabezado, "Lista de archivos"));

			wout.WriteLine (@"<style>table td, table th {
	border: 1px solid #98bf21;
	padding: 3px 7px 2px 7px;
}</style>");

			wout.WriteLine ("\t<h2>Lista de archivos</h2><table>");
			// Recorre los archivos listándolos

			nivel = 0;

			foreach (NodoMapa nodo in DExplorador.Raíz) {
				Enumerar (nodo, wout);
			}

			wout.WriteLine (@"</table></body></html>");

			wout.Flush ();

			ctx.Response.Close ();
		}

		private int nivel;

		private void Enumerar(Categoría cat, StreamWriter sw)
		{
			if (cat.Elementos.Length == 0)
				return;

			sw.WriteLine (String.Format(@"<tr><td colspan=""3"" style=""text-align: center;{0}font-weight: {1};"">{2}</td></tr>",
				nivel == 0 ? "font-variant: small-caps; " : (nivel == 2 ? "font-style: italic;" : ""),
				nivel > 1 ? "normal" : "bold",
				cat.Nombre
			));

			nivel++;

			foreach (NodoMapa nodo in cat.Elementos) {
				Enumerar (nodo, sw);
			}

			nivel--;
		}

		private void Enumerar(UnidadDafny dfy, StreamWriter sw)
		{
			sw.WriteLine ("<tr><td> " + "<a href=\"ver/" + dfy.Uri + "\">" + dfy.Nombre + "</a></td>");

			InformeDafny informe = null;

			if (DCaché.Consulta (dfy.Uri, out informe)) {
				sw.WriteLine (@"<td style=""text-align: center;"">" + informe.Tiempo.TotalSeconds + "s</td>");

				string color = "greenyellow";

				if (informe.Resultado.EsError ())
					color = "red";

				sw.WriteLine(@"<td style=""background-color: " + color + @";"">" + informe.Resultado.Desc() + "</td>");
			}

			sw.WriteLine ("</tr>");
		}

		private void Enumerar(NodoMapa nodo, StreamWriter sw) {

			if (nodo is UnidadDafny)
				Enumerar (nodo as UnidadDafny, sw);
			else
				Enumerar (nodo as Categoría, sw);

			// Requiere Microsoft.CSharp.dll
			// Imprimir (nodo as dynamic);
		}


		// Responde con la vista de un archivo

		public void ResponderVer(HttpListenerContext ctx, string archivo) {
			if (DCaché == null || DExplorador == null) {
				Responder404 (ctx); return;
			}

			StreamWriter wout = new StreamWriter (ctx.Response.OutputStream);

			ctx.Response.StatusCode = 200;

			wout.WriteLine (String.Format(Encabezado, "Archivo - " + archivo));

			// Color para indicar si es error

			string color = "blue";

			// Busca el informe en la caché

			InformeDafny informe = null;

			bool está = DCaché.Consulta (archivo, out informe);

			if (está) {
				if (informe.Resultado.EsError ())
					color = "red";
				else
					color = "greenyellow";
			}

			wout.WriteLine (String.Format(@"<header style=""background-color: {0};"">{1}</header>",
				color,
				archivo
			));

			if (está && informe.Resultado.EsError ()) {
				var salida = Lincol.Replace (informe.Salida, @"dfy<a href=""#l$1"">($1, $2)</a>:");

				wout.WriteLine (@"<pre style=""background-color: #faff5c;"">" + salida + "</pre>");

				wout.WriteLine ("<br />");
			}

			// Muy ineficiente

			var unis = DExplorador.Unidades.ToList();

			var elem = unis.Where (nodo => nodo.Uri == archivo).ToList()[0];

			var arch = File.OpenText (elem.Uri);

			int nlinea = 1;

			string lineas = "";

			wout.Write ("<style>.numlin { color: #999999; text-decoration: none; }</style>");

			wout.WriteLine ("\t<pre style=\"float: left; text-align: right; margin-right: 2ex;\">");

			// Recorre las líneas pintando números de línea

			while (arch.Peek() >= 0) {
				string line = arch.ReadLine ();

				wout.WriteLine (String.Format(@"<a class=""numlin"" id=""l{0}"">{0}</a>",
					nlinea++));

				lineas += line + "\n";
			}

			wout.WriteLine ("</pre>");

			wout.WriteLine ("\t<pre class=\"codi\">");
			wout.WriteLine (lineas);


			//arch.CopyTo (wout.BaseStream);

			wout.WriteLine ("\t</pre></body></html>");

			wout.Flush ();

			ctx.Response.Close ();
		}

		public void Run()
		{
			ThreadPool.QueueUserWorkItem((am) =>
				{
					Dafny dafny = new Dafny(DafnyExe);

					try {
						while (listener.IsListening)
						{
							ThreadPool.QueueUserWorkItem((c) =>
								{

									var ctx = c as HttpListenerContext;

									try {
										// Comprueba el usuario y contraseña
										// (rudimentariamente)

										if (CAcceso != null) {
											var id = (HttpListenerBasicIdentity) ctx.User.Identity;

											if (CAcceso != id.Name + ":" + id.Password) {

												Console.WriteLine("Intento de acceso con " + id.Name 
													+ ":" + id.Password );

												ctx.Response.StatusCode = 403;
												ctx.Response.Close();

												return;
											}
										}

										var path = ctx.Request.Url.LocalPath;

										if (path == "/webver.js")
										{
											VolcarStream(Js, ctx.Response);

											ctx.Response.Close();
										}
										else if (ctx.Request.Url.LocalPath == "/webver.css")
										{
											VolcarStream(Css, ctx.Response);

											ctx.Response.Close();
										}
										else if (ctx.Request.Url.LocalPath == "/ls")
										{
											ResponderLs(ctx);
										}
										else if (ctx.Request.Url.LocalPath.StartsWith("/ver/"))
										{
											ResponderVer(ctx, ctx.Request.Url.LocalPath.Substring(5));
										}
										else if (ctx.Request.Url.LocalPath != "/")
											Responder404(ctx);

										else {

											string msg = "";
											string code = "";

											if (ctx.Request.ContentLength64 != 0) { 

												StreamReader sr = new StreamReader(ctx.Request.InputStream);

												code = WebUtility.UrlDecode(sr.ReadToEnd());

												code = code.Substring(5);

												msg = dafny.VerificarTexto(code).Salida;

											}

											byte[] buf = Encoding.UTF8.GetBytes(String.Format(Interfaz, code, msg));

											ctx.Response.ContentLength64 = buf.Length;
											ctx.Response.OutputStream.Write(buf, 0, buf.Length);
										}
									}
									catch (Exception e) {
										Console.Error.WriteLine(e.Message);

									}
									finally {
										ctx.Response.OutputStream.Close();
									}
								}, listener.GetContext());
						}
					}
					catch { }
				});
		}

		private readonly string Encabezado = @"<!DOCTYPE html>
<html lang=""es"">
<head>
	<meta charset=""UTF-8"" />
	<title>{0}</title>
</head>
<body>";

		// Recursos diversos que se utilizan como archivos .html, .css y .js

		private string Interfaz = LeeRecurso("vaed.aux.interfaz.htm");

		private Stream Css = Assembly.GetExecutingAssembly().
			GetManifestResourceStream("vaed.aux.webver.css"); 

		private Stream Js = Assembly.GetExecutingAssembly().
			GetManifestResourceStream("vaed.aux.webver.js"); 

		private Stream Mens404 = Assembly.GetExecutingAssembly().
			GetManifestResourceStream("vaed.aux.404.htm");

		private static string LeeRecurso(string rec) {
			return new StreamReader (Assembly.GetExecutingAssembly ().
				GetManifestResourceStream (rec)).ReadToEnd ();
		}

		private readonly Regex Lincol = new Regex (@"dfy\((\d+),(\d+)\):");

		private static void VolcarStream(Stream fuente, HttpListenerResponse resp)
		{
			resp.ContentLength64 = fuente.Length;

			fuente.CopyTo(resp.OutputStream);

			fuente.Seek(0, SeekOrigin.Begin);
		}

		public void Stop()
		{
			listener.Stop ();
			listener.Close ();
		}

		private string CAcceso = null;

		public Explorador DExplorador { get; set; }

		public Caché DCaché { get; set; }
	}
}
