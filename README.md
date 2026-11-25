# Tratado moderno de Análisis — Formalización en Lean

**Gustav A. Tacheck · [Matemática Abierta](https://matematicaabierta.cl/)**

[![CI](https://github.com/lachenmann/tratado-analisis-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/lachenmann/tratado-analisis-lean/actions/workflows/lean.yml)

Este proyecto formaliza resultados del *Tratado moderno de Análisis* en Lean 4. Su objetivo es reconstruir las estructuras numéricas desde fundamentos conjuntistas, con trazabilidad entre los resultados del manuscrito y sus declaraciones formales, en lugar de limitarse a invocar los tipos numéricos estándar de Mathlib.

## Sucesiones racionales y aproximación — v0.2.0

Corte TA-LEAN-0011 C08/R03, cerrado y publicado en [v0.2.0](https://github.com/lachenmann/tratado-analisis-lean/releases/tag/v0.2.0): 185 archivos fuente/configuración y 1230 consultas axiomáticas (278 adicionales). 27 resultados numerados del capítulo 8, la entrada de notación TA-NOT-00019 y el prerrequisito TA-PRO-00014 (29 nodos editoriales en total). Certificación local: 920 trabajos y 156 relecturas; cero nuevas dependencias de Choice y cero sorryAx. Verificación externa: [CI del PR #3, n.º 18](https://github.com/lachenmann/tratado-analisis-lean/actions/runs/45501985381) y [CI de main, n.º 19](https://github.com/lachenmann/tratado-analisis-lean/actions/runs/45512352728), ambas PASS (920 trabajos, 185/185 fuentes/configuraciones, 1230/1230 huellas exactas y 8 comprobaciones estrictas). Commit de la release: `ada56f69a0b375b484193aaa912c93548067994e`. No se afirma la construcción del cuerpo de Cauchy ni la certificación algorítmica global.

- [Alcance y correspondencia C08](docs/TA-LEAN-0011-C08.md)
- [Certificado v0.2.0](certificates/v0.2.0/README.md)

```sh
lake exe cache get
lake build
python3 scripts/check_release_v020.py
```

Se preservan todos los archivos certificados, incluido `lakefile.toml` (versión interna 0.1.2) y el agregador histórico. El número de release y `CITATION.cff` no requieren alterar la configuración de Lake: su contenido está fijado en los manifiestos históricos y la auditoría acumulativa exige su identidad byte a byte. Importar directamente `TratadoAnalisis.Cauchy.SequentialIncompleteness` u otros módulos. Las secciones siguientes conservan el historial de versiones anteriores.

## Hoja de ruta

| Versión | Alcance | Estado |
|---|---|---|
| v0.2.0 | Capítulo 8 — Sucesiones racionales y aproximación | Publicada; núcleo conjuntista certificado |
| v0.3.0 | Capítulo 9 — El cuerpo de Cauchy | Objetivo previsto; pendiente de formalización y certificación |

La efectividad de la bisección y la computabilidad de los módulos de convergencia y Cauchy quedan como tareas diferenciadas. La completitud del nuevo cuerpo y los isomorfismos de completaciones no se anticipan en la certificación del capítulo 9.

## Prerrequisitos de Cauchy: v0.1.2

Se incorporan 18 nodos editoriales (aritmética y orden natural, incompletitud de los racionales, valor absoluto, desigualdad triangular, equivalencias de completitud y numerales en cuerpos ordenados), con 94 consultas adicionales. Los módulos nuevos pueden importarse individualmente o mediante `import TratadoAnalisis`.

| Indicador | v0.1.2 |
|---|---:|
| Fuentes Lean, incluidas pruebas | 156 |
| Archivos de fuente y configuración | 159 |
| Consultas axiomáticas | 952 |
| Dependencias de Classical.choice históricas | 65 |
| Dependencias de sorryAx | 0 |

Los cuatro bloques matemáticos han superado sus CI. La certificación de la integración se consulta en GitHub Actions. Véanse [certificado](certificates/v0.1.2/README.md), [correspondencia](docs/CORRESPONDENCIA.md) y [alcance](docs/ALCANCE.md). El núcleo de sucesiones racionales se incorporó en v0.2.0; el cuerpo de Cauchy corresponde al capítulo 9.

Para reproducir desde la revisión de v0.1.2:

```sh
lake exe cache get
lake build
lake env lean TratadoAnalisis/Audit.lean > audit.log
lake env lean tests/PublicAPI.lean > public-api.log
lake env lean tests/Prerequisites.lean > prerequisites.log
lake env lean tests/AbsoluteValue.lean > absolute-value.log
lake env lean tests/CompletenessEquivalences.lean > completeness-equivalences.log
lake env lean tests/NumeralArithmetic.lean > numeral-arithmetic.log
python3 scripts/check_release_v012.py audit.log public-api.log prerequisites.log absolute-value.log completeness-equivalences.log numeral-arithmetic.log
```

## Consolidación histórica: v0.1.1

Interfaces estables en `TratadoAnalisis.Dedekind.Completeness`, `Density`, `SquareRoots` y `Arithmetic`, también disponibles al importar `TratadoAnalisis`. Se preservan los nombres originales y se ofrece [correspondencia de API](docs/CORRESPONDENCIA.md). La versión conserva íntegra la referencia axiomática de v0.1.0 y posee un [manifiesto propio](certificates/v0.1.1/README.md).

Para verificar esta consolidación, desde la etiqueta `v0.1.1` (no desde una versión posterior):

```sh
lake exe cache get
lake build
lake env lean TratadoAnalisis/Audit.lean > audit.log
lake env lean tests/PublicAPI.lean > public-api.log
python3 scripts/check_audit.py audit.log
python3 scripts/check_public_api.py audit.log public-api.log
sha256sum -c certificates/v0.1.1/SHA256SUMS
```

La etiqueta v0.1.0 conserva su significado histórico. Los comandos de reproducción de esa etiqueta se mantienen a continuación.

## Estado inicial: v0.1.0

Instantánea del checkpoint **TA-LEAN-0010**, cerrado el 24 de noviembre de 2026. La cadena fundamental alcanza la construcción de los reales de Dedekind como cuerpo ordenado completo y la existencia y unicidad de la raíz positiva de dos. Para esta última se formaliza una prueba alternativa basada en aproximaciones de Pell.

| Indicador del checkpoint | Valor |
|---|---:|
| Fuentes `.lean` en la instantánea | 142 |
| Consultas `#print axioms` en `TratadoAnalisis/Audit.lean` | 833 |
| Consultas con axiomas / sin axiomas | 829 / 4 |
| Consultas históricas con `Classical.choice` | 65 |
| Consultas con `sorryAx` | 0 |
| Nodos editoriales del último checkpoint | 12 |

Estas cifras no son un recuento de teoremas distintos del manuscrito ni una afirmación de que todo el tratado esté formalizado. La cobertura de los capítulos iniciales tiene distintos niveles; se mantienen resultados pendientes. Véase [alcance y límites](docs/ALCANCE.md).

## Reproducir

Instalar [elan](https://github.com/leanprover/elan) y Git. La versión del compilador se selecciona mediante `lean-toolchain`; las dependencias exactas se fijan en `lake-manifest.json`. No ejecutar `lake update` para reproducir esta versión.

```sh
git clone --branch v0.1.0 https://github.com/lachenmann/tratado-analisis-lean.git
cd tratado-analisis-lean
lean --version
lake exe cache get
lake build
lake env lean TratadoAnalisis/Audit.lean > audit.log
python scripts/check_audit.py audit.log
```

El último comando requiere Python 3. El caché de Mathlib reduce el trabajo de compilación; no sustituye la comprobación del código de este proyecto. El registro histórico de Windows documenta `lake build` con 896 trabajos y caché existente. La etiqueta v0.1.0 superó el CI #1 en Linux: 896 trabajos, 833/833 huellas preservadas, 65 dependencias históricas de Choice, cero sorryAx. [Ejecución verificable](https://github.com/lachenmann/tratado-analisis-lean/actions/runs/45330705764).

Para verificar los bytes de la instantánea inicial en sistemas con GNU coreutils:

```sh
sha256sum -c certificates/TA-LEAN-0010/SHA256SUMS
```

## Organización

- `TratadoAnalisis/Foundations`, `Chapter0`, `Naturals`, `Integers`, `Rationals`: fundamentos y sistemas numéricos.
- `TratadoAnalisis/Dedekind`, `Abstract`, `Chapter7_0010`: cortaduras, cuerpos ordenados, completitud y corolarios.
- `TratadoAnalisis/Audit.lean`: auditoría explícita de declaraciones.
- `certificates/TA-LEAN-0010/`: huellas de la instantánea original y de las consultas axiomáticas.
- `docs/`: correspondencia editorial, metodología, dependencias y límites.

Los certificados de cada versión identifican sus rutas y bytes correspondientes. Los archivos históricos se mantienen, salvo las modificaciones expresamente documentadas. Los archivos auxiliares históricos en la raíz se preservan; el build principal no acredita su reelaboración individual.

## Fundamentos y licencia

Se utiliza `ZFSet` de Mathlib como infraestructura de teoría de conjuntos en Lean. Se distinguen axiomas del metanivel de Lean, hipótesis explícitas de lógica clásica y usos del axioma de elección en la teoría objeto. No se reivindica una formalización enteramente constructiva ni un modelo independiente de la metateoría de Lean.

Código y documentación original de este repositorio: [Apache 2.0](LICENSE). Las dependencias externas conservan sus licencias. El manuscrito y sus ediciones conservan su régimen editorial independiente. Véanse [atribuciones y dependencias](docs/DEPENDENCIAS.md) y [contribuciones](CONTRIBUTING.md).

**Edición de lectura:** [Tratado moderno de Análisis](https://matematicaabierta.cl/libros/otros/tratado-de-analisis.html).
