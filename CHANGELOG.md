# Historial de versiones

## v0.2.0 — Sucesiones racionales y aproximación (2026-11-24, Chile)

- TA-LEAN-0011: núcleo conjuntista de §§8.1–8.7; 27 resultados numerados, una entrada de notación y TA-PRO-00014.
- Sucesiones racionales, operaciones puntuales, distancia, convergencia, condición de Cauchy, acotación y bisección racional; incompletitud secuencial de Q.
- 185 fuentes/configuraciones; 1230 consultas axiomáticas, incluidas las 952 históricas exactas y 278 nuevas con `propext, Quot.sound`.
- 65 dependencias históricas de `Classical.choice`, ninguna nueva; cero `sorryAx` en las consultas auditadas. Clausura independiente de 52 módulos locales.
- Auditoría unificada en `scripts/check_release_v020.py`: 17 grupos, regresión exacta, manifiestos y controles estrictos.
- [CI #18 del PR](https://github.com/lachenmann/tratado-analisis-lean/actions/runs/45501985381) y [CI #19 de main](https://github.com/lachenmann/tratado-analisis-lean/actions/runs/45512352728), PASS. [Release estable](https://github.com/lachenmann/tratado-analisis-lean/releases/tag/v0.2.0), commit `ada56f69a0b375b484193aaa912c93548067994e`.
- Se preserva `lakefile.toml` (versión interna 0.1.2) por identidad de los manifiestos certificados. No se afirma computabilidad global de la bisección ni los módulos.
- Próximo objetivo previsto, v0.3.0: capítulo 9, cuerpo de Cauchy.

## v0.1.2 — Prerrequisitos de Cauchy

- TA-THM-00016–00022, TA-PRO-00170, TA-PRO-00428 y TA-PRO-00077.
- TA-DEF-00071, TA-PRO-00071 y TA-THM-00035.
- TA-DEF-00075, TA-DEF-00076 y TA-THM-00038/00039.
- TA-PRO-00069, sus cinco apartados.
- Cuatro CI matemáticos conformes; 952 huellas acumuladas, 159 fuentes/configuraciones. Publicación certificada por [CI #13 de main](https://github.com/lachenmann/tratado-analisis-lean/actions/runs/45441592624).
- Conservación de la API y certificados previos. El núcleo de sucesiones racionales se incorporó en v0.2.0.

## v0.1.1 — Consolidación certificada

- Limpieza exclusivamente editorial y de diagnósticos de N05.
- 24 nombres públicos mediante alias; nombres históricos sin deprecación.
- Puente de positividad editorial por Iff.rfl.
- Las 833 huellas y el certificado de v0.1.0 se preservan; manifiesto nuevo y 25 consultas independientes de API.
- La versión siguiente, v0.1.2, incorporó prerrequisitos de Cauchy.

## v0.1.0 — Primera instantánea pública

- Base: TA-LEAN-0010, cierre canónico 2026-11-24.
- 142 fuentes Lean y tres archivos de configuración preservados byte a byte.
- Completitud del cuerpo de Dedekind, densidad racional, propiedad arquimediana, ínfimos y raíz positiva de dos.
- 833 consultas de auditoría. Las 71 nuevas de TA-LEAN-0010 no añaden Choice ni `sorryAx`.
- Infraestructura pública de documentación, contribuciones y CI; el éxito de CI debe comprobarse independientemente.
- Alcance parcial y pendientes documentados; no equivale a una formalización completa de todos los capítulos.
