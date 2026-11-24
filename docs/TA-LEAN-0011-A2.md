# TA-LEAN-0011 — A2: operaciones puntuales y sucesiones constantes

Candidato sobre A1 certificado por [CI #14](https://github.com/lachenmann/tratado-analisis-lean/actions/runs/45442938728), commit 5ae25c754b5d47a3bce66b1c5422c38ce8515b8b. A1: 907 trabajos, 20/20 consultas con propext y Quot.sound; 159/159 archivos v0.1.2 y 952/952 huellas preservados; clausura local de 14 módulos independiente de Dedekind. Las huellas de A1 quedan fijadas en A1_AXIOMAS.txt y sus tres archivos Lean se comprueban por identidad de blob Git.

Fuente: Capítulo 8 v1.1.0, §§8.1.3–8.1.5. Se desarrollan TA-DEF-00106 (cuatro operaciones término a término y sus grafos globales), TA-DEF-00107 (constantes y grafo de kappa) y TA-PRO-00108 (TA-PRF-00220, cuatro identidades de compatibilidad).

El módulo Foundations/RelationalFunctions.lean construye grafos por Separación dentro de ambientes de pares; total y unívoco se prueba sin elegir una familia de valores. SequenceOperations.lean especializa esa infraestructura a los racionales conjuntistas, con las operaciones RatAdd, RatNeg, RatMul y RatSub ya definidas. seqSub se define como seqAdd con seqNeg. Se preservan triples, dominio, codominio y la evaluación relacional.

La auditoría incluye 62 declaraciones nuevas, además de las 972 anteriores. Se amplía el control de importaciones locales a las dos nuevas fuentes. No se modifica ningún archivo Lean previamente certificado; el módulo raíz y la versión de Lake se reservan para la integración.

Estado: candidato pendiente de CI. Todavía no se abre la construcción del cociente ni se utiliza la completitud de Dedekind. El registro canónico de la bóveda sigue pendiente de actualización.

## Cierre de A2

PASS CI #15 (45450730341), commit 8e436cb1e7d1361cfcc7601eb889f86459c9e322. 909 trabajos, 62/62 huellas con propext y Quot.sound, 1034 acumuladas, clausura de 35 módulos independiente de Dedekind. Se fija A2_AXIOMAS.txt para controles posteriores. Sin nuevas dependencias de Choice ni sorryAx.
