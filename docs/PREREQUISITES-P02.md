# P02 — Valor absoluto

Candidato posterior al PASS de P01. Cotejo con capítulo 4 v1.2.0, §4.2: TA-DEF-00071 (máximo de x y -x), TA-PRO-00071 (seis propiedades), TA-THM-00035 (triangular). Se conserva la semántica relacional de IsOrderedFieldFoundational; existencia y unicidad del valor absoluto, no selección de una función global. Se reutilizan la antitonía del opuesto, la cancelación aditiva y la ley del producto por un opuesto.

Se auditan todas las 21 declaraciones nuevas. TA-COR-00010 (triangular inversa) no se cuenta como certificado por este bloque. El alcance sigue siendo candidato hasta compilar y cotejar las huellas.

## Cierre de P02

PASS CI #9, commit `87c84a1f2a37ea99c49371b81521d4dde0e88221`, [ejecución 45435010462](https://github.com/lachenmann/tratado-analisis-lean/actions/runs/45435010462). 903 trabajos; 21/21 consultas con propext y Quot.sound. La referencia exacta queda en `certificates/v0.1.2/P02_AXIOMAS.txt` y se exige en las auditorías posteriores.
