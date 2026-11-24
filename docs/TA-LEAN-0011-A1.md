# TA-LEAN-0011 — Candidato A1

Base inmutable: v0.1.2, commit `6451cd0efbbdb9ed2fabd38a4b21483d7a88242e`, [CI de main #13](https://github.com/lachenmann/tratado-analisis-lean/actions/runs/45441592624): 905 trabajos, 159/159 archivos, 952/952 huellas exactas y 65 dependencias históricas de Choice. No se cambia el checkpoint canónico de la bóveda mediante este commit.

## Cotejo editorial

Fuente canónica: Capítulo 8, TA-0011, v1.1.0, §§8.1.1–8.1.2. Dependencias de capítulo 0: TA-DEF-00018, TA-PRO-00011 y TA-PRO-00014. La construcción de Dedekind no se utiliza.

| ID | Declaraciones candidatas | Alcance |
|---|---|---|
| TA-PRO-00014 | `TA_PRO_00014_mem_functionSpace_iff`; `TA_PRO_00014_functionSpace_exists_unique` | Conjunto B^A de triples de función por Separación en un ambiente de pares y potencias; construcción alternativa del ambiente. |
| TA-DEF-00105 | `rationalSequences`; `TA_DEF_00105_mem_rationalSequences_iff`; `TA_DEF_00105_rationalSequences_exists_unique` | Especialización N → Q como conjunto de triples. |
| TA-PRO-00107 (TA-PRF-00219) | `TA_PRO_00107_sequence_eq_iff_values` | Equivalencia extensional término a término, con evaluación relacional total y unívoca. |

El objeto función conserva su dominio y codominio. La evaluación no define una función externa mediante Choice. No se afirma computabilidad de todas las sucesiones. A1 no define todavía las operaciones puntuales de TA-DEF-00106 ni las sucesiones constantes de TA-DEF-00107.

## Controles

Se auditan 20 declaraciones nuevas (12 de infraestructura de funciones y 8 de sucesiones). Se conserva la huella de cada uno de los 159 archivos de v0.1.2, sin alterar el módulo raíz ni Lake; se exigen las 952 huellas previas y se verifica la clausura de imports locales de los nuevos módulos. La auditoría previa de publicación permanece intacta; este CI usa un verificador de extensión que admite exclusivamente los tres archivos Lean nuevos.

## Continuación

A2: TA-DEF-00106, operaciones puntuales con grafos de operaciones, TA-DEF-00107 y TA-PRO-00108. Después §8.2, distancia racional. La transición al cociente de Cauchy se reserva al capítulo 9.

Estado: CANDIDATO PENDIENTE DE CI. Registro canónico de publicaciones v0.1.0–v0.1.2 y checkpoint TA-LEAN-0011 pendiente de inscripción en la bóveda.
