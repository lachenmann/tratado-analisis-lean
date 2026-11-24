# v0.1.2 — P01: aritmética natural e incompletitud racional

Base inmutable: v0.1.1, commit 716493225a4120c2c407015629235aae836d3042. Este bloque es candidato hasta PASS de CI; no es un nuevo release.

| Nodos | Declaraciones candidatas | Alcance |
|---|---|---|
| TA-THM-00016/00017/00018 | `TA_THM_00016_mul_add`, `TA_THM_00017_mul_assoc`, `TA_THM_00018_mul_comm` | Leyes de los grafos conjuntistas; transporte de códigos Nat locales mediante las equivalencias de valores ya certificadas. |
| TA-THM-00019/00020 | `TA_THM_00019_nat_total`, `TA_THM_00020_nat_total_order` | Orden aritmético NatLETA, no orden de un portador estándar que sustituya a omegaTA. |
| TA-THM-00021 | `TA_THM_00021_strict_iff_mem` | Orden estricto editorial y pertenencia de von Neumann. |
| TA-PRO-00428 | `TA_PRO_00428_nat_subset_and_zero_mem_succ` | Reúne los lemas de transitividad y cero de PrimeGridLeastIndex0009 y Recursion. |
| TA-THM-00022 | `TA_THM_00022_nat_well_order` | Mínimo de un subconjunto no vacío; em explícito. Reutiliza omega_least_manual. |
| TA-PRO-00170 | `TA_PRO_00170_nat_trichotomy`, `TA_PRO_00170_compare_codes_spec` | Tricotomía exclusiva y algoritmo recursivo sobre códigos Nat suministrados; no se afirma extracción computable de códigos desde ZFSet. |
| TA-PRO-00077 | `TA_PRO_00077_rationals_not_complete` | Puente Iff.rfl entre supremos y contraejemplo S₂ ya certificado. |

Los enunciados se cotejaron con capítulo 1 v1.5.0 (§§1.5–1.6 y §1.2.2 bis), capítulo 4 v1.2.0 (§4.6.5), y las dependencias del capítulo 8 v1.1.0. Las tres leyes del producto conservan sus objetos y grafos, con prueba formal alternativa por transporte; la efectividad de TA-PRO-00170 se restringe a códigos explícitos.

Se preservan las 833 consultas históricas y las 25 de API. Se añade una sonda separada de 22 consultas, incluyendo tres auxiliares ya existentes. El nuevo manifiesto de versión y la integración de la API de v0.1.2 se reservan para el cierre del bloque completo. No se altera el manuscrito, la versión de Lake, ni las etiquetas previas.

Pendientes de P02: TA-THM-00035 (incluidos prerrequisitos de valor absoluto), TA-THM-00038, TA-THM-00039 y cotejo de TA-PRO-00069. TA-COR-00139 y TA-PRO-00427 siguen como pendientes explícitos; no se atribuye un cierre de todo el capítulo 1.
