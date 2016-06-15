function makeTab(e) {
	// Si se pulsa el tabulador
	if (e.keyCode === 9) {
		// Obtiene la posición del cursor (o la selección)
		var start = this.selectionStart;
		var end = this.selectionEnd;

		var target = e.target;
		var value = target.value;

		target.value = value.substring(0, start)
			+ "\t"
			+ value.substring(end);

		this.selectionStart = this.selectionEnd = start + 1;

		// Previene que se pierda el foco
		e.preventDefault();
	}
}
