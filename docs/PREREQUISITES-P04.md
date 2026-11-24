# P04 — Aritmética y orden de los numerales naturales

Candidato posterior al PASS P03. Cotejo con capítulo 4 v1.2.0, §4.1.6, TA-PRO-00069 (TA-PRF-00130), en sus cinco apartados: numeral de uno, suma, producto, orden estricto, inyectividad y preservación/reflexión de ≤.

Se conserva el grafo CanonicalNumeralGraphManual de TA-DEF-00068 y los grafos naturales de TA-DEF-00036/00037. Se reutilizan sus ecuaciones de recursión, las equivalencias de valores aritméticos de natEncode, el orden NatLETA, la tricotomía TA-PRO-00170 y las propiedades relacionales abstractas ya demostradas. Las inducciones para suma y producto usan códigos Nat como testigos locales; las firmas finales cuantifican sobre los naturales conjuntistas y los valores del grafo. No se escoge una función global ni se añade em al enunciado.

El paquete TA_PRO_00069_numeral_arithmetic_order reúne los cinco apartados. Se auditan 22 declaraciones. P01, P02 y P03 conservan sus huellas exactas. Pendiente de compilación y cotejo axiomático; no se crea una etiqueta nueva en este tramo.

## Cierre P04

PASS CI #11, commit `801b53e82cc2f85be612308be8bc2601d8f32e79`, [ejecución 45436849722](https://github.com/lachenmann/tratado-analisis-lean/actions/runs/45436849722). 905 trabajos; 22/22 consultas con propext y Quot.sound. Se fijan las huellas exactas en `certificates/v0.1.2/P04_AXIOMAS.txt`.
