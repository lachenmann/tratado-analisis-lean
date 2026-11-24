# TA-LEAN-0011 — A3: distancia racional (§8.2)

Base: A2 certificado por [CI #15](https://github.com/lachenmann/tratado-analisis-lean/actions/runs/45450730341), commit 8e436cb1e7d1361cfcc7601eb889f86459c9e322. 909 trabajos, 62/62 consultas con propext y Quot.sound; 972 previas y 159 archivos de v0.1.2 preservados. Huellas fijadas en A2_AXIOMAS.txt y los tres archivos Lean de A2 fijados por identidad de blob Git.

Fuente: capítulo 8 v1.1.0, §§8.2.1–8.2.3. Candidato de los tres nodos:
- TA-DEF-00108: distancia racional como función conjuntista con dominio Q×Q y codominio Q, grafo y valor d(x,y)=|x-y|.
- TA-PRO-00109 (TA-PRF-00221): no negatividad, separación, simetría, triangular y traslación.
- TA-PRO-00110 (TA-PRF-00222): equivalencias entre d(x,y)<ε, −ε<x−y<ε e y−ε<x<y+ε.

Decisión de arquitectura: el módulo abstracto AbsoluteValue de v0.1.2 tiene dependencias de importación posteriores a Q. Se desarrolla una especialización independiente en Rationals/AbsoluteValue.lean, con el mismo máximo de x y −x, y se certifica la equivalencia exacta de predicados en Bridges/RationalAbsoluteValue.lean. Ese puente importa ambas capas pero no es una dependencia de las fuentes de Cauchy. La independencia se exige por clausura de imports locales, incluidos Bridges como prefijo prohibido. El módulo especializado acredita las propiedades necesarias en §8.2; no vuelve a contabilizar TA-DEF-00071 ni afirma haber certificado allí todas las cláusulas de TA-PRO-00071 (en particular, la multiplicatividad no se desarrolla en A3). La generalidad del resultado de v0.1.2 no se modifica.

40 consultas nuevas, además de 1034 huellas previas. Se preservan las fuentes certificadas y no se altera la versión de Lake. Candidato pendiente de CI; el registro canónico de la bóveda sigue pendiente de actualización.
