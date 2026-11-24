# Certificado v0.1.2 — Prerrequisitos de Cauchy

Candidato de integración posterior a los cuatro CI matemáticos. La versión se publica únicamente tras el PASS del CI de integración y de main. La revisión v0.1.1 (716493225a4120c2c407015629235aae836d3042) y su certificado quedan intactos.

| Tramo | CI de certificación | Consultas |
|---|---|---:|
| Auditoría histórica v0.1.0 | [#1](https://github.com/lachenmann/tratado-analisis-lean/actions/runs/45330705764) | 833 |
| API v0.1.1 | [#4](https://github.com/lachenmann/tratado-analisis-lean/actions/runs/45429421360) | 25 |
| P01, naturales e incompletitud racional | [#8](https://github.com/lachenmann/tratado-analisis-lean/actions/runs/45433251695) | 22 |
| P02, valor absoluto | [#9](https://github.com/lachenmann/tratado-analisis-lean/actions/runs/45435010462) | 21 |
| P03, equivalencias de completitud | [#10](https://github.com/lachenmann/tratado-analisis-lean/actions/runs/45435934544) | 29 |
| P04, numerales | [#11](https://github.com/lachenmann/tratado-analisis-lean/actions/runs/45436849722) | 22 |
| **Total** | | **952** |

`AXIOMAS.txt` es la referencia acumulada de 952 nombres distintos y huellas exactas, normalizadas por orden lexicográfico de axiomas. Las referencias por tramo permanecen disponibles. `API_AXIOMAS.txt` deriva los 24 aliases de sus originales y fija la huella del puente de positividad, confirmada por CI #4.

| Huella | Consultas |
|---|---:|
| propext, Quot.sound | 872 |
| Classical.choice, propext, Quot.sound | 65 |
| Quot.sound | 6 |
| propext | 4 |
| Sin axiomas | 5 |

`SHA256SUMS` abarca 159 archivos: 156 fuentes Lean (incluidas pruebas y auxiliares históricos) y las tres configuraciones. De los 150 archivos de v0.1.1, 148 siguen idénticos; los únicos cambios son las cinco importaciones nuevas del módulo raíz y el número de versión en lakefile.toml. El manifiesto de v0.1.1 se verifica completo en su propia etiqueta y no se reescribe.

El script `scripts/check_release_v012.py` exige las seis auditorías exactas, la integridad de los tres manifiestos/referencias fijados en él, la cobertura de los archivos rastreados y la ausencia de dependencias axiomáticas nuevas no permitidas. No se afirma que todas las fuentes auxiliares históricas de la raíz hayan sido reelaboradas individualmente.

Los 18 nodos incorporados se describen en `docs/CORRESPONDENCIA.md` y los documentos P01–P04. La construcción de Cauchy aún no forma parte de la versión.
