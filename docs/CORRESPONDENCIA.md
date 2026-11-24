# Correspondencia vigente v0.2.0 (candidato)

Véase [C08](TA-LEAN-0011-C08.md). A continuación, correspondencia histórica.

# Correspondencia editorial — TA-LEAN-0010

Los nombres de módulos de esta tabla se sitúan bajo `TratadoAnalisis/Chapter7_0010/`. Las declaraciones de esta tabla comparten el namespace `TratadoAnalisis.Chapter7_0010`. Cada resultado se cotejó con el enunciado editorial; donde la prueba difiere se indica expresamente.

| ID | Prueba humana | Declaraciones Lean | Módulo |
|---|---|---|---|
| TA-PRO-00104 | TA-PRF-00208 | `TA_PRO_00104_upper_iff_subset_0010` | `Consequences0010.lean` |
| TA-DEF-00104 | — | `DedSupUnion0010`; `mem_dedSupUnion_iff_0010`; `TA_DEF_00104_union_eq_0010`; `TA_DEF_00104_union_subset_rationals_0010` | `Consequences0010.lean`, `I03EditorialBridges0010.lean` |
| TA-THM-00056 | TA-PRF-00211 | `TA_THM_00056_dedekind_complete_0010`; `supremum_iff_dedekind_lub_0010` | `Completeness0010.lean`, `SupremumBridge0010.lean` |
| TA-COR-00025 | TA-PRF-00212 | `TA_COR_00025_dedekind_infimum_0010` | `Consequences0010.lean` |
| TA-COR-00026 | TA-PRF-00213 | `TA_COR_00026_dedekind_archimedean_0010` | `Consequences0010.lean` |
| TA-PRO-00106 | TA-PRF-00214 | `IsOrderedCompletionRelational0010`; `TA_PRO_00106_dedekind_completion_0010` | `Completion0010.lean` |
| TA-COR-00027 | TA-PRF-00215 | `TA_COR_00027_rational_section_dense_0010`; `TA_COR_00027_rational_graph_image_dense_0010` | `Completion0010.lean`, `I03EditorialBridges0010.lean` |
| TA-LEM-00028 | TA-PRF-00216 | `TA_LEM_00028_cut_mem_iff_section_lt_0010` | `CutPosition0010.lean` |
| TA-THM-00057 | TA-PRF-00217 | `positive_square_two_exists_unique_0010` (prueba alternativa de Pell) | `N05PositiveSquareUniqueness.lean` |
| TA-COR-00028 | TA-PRF-00218 | `alphaTwo_positive_irrational_square_two_0010`; `positive_square_two_eq_alphaTwo_0010` (prueba alternativa) | `N05PositiveSquareUniqueness.lean` |
| TA-COR-00137 | TA-PRF-00908 | `TA_COR_00137_ded_neg_unique_0010` | `Chapter6Corollaries0010.lean` |
| TA-COR-00138 | TA-PRF-00909 | `TA_COR_00138_rational_division_0010`; `TA_COR_00138_division_exists_unique_0010` | `Chapter6Corollaries0010.lean`, `I03EditorialBridges0010.lean` |

TA-PRO-00105 y TA-THM-00055 ya pertenecían a TA-LEAN-0008; se reutilizan y no se cuentan de nuevo. La tabla cubre el último checkpoint, no todos los nodos de los checkpoints anteriores. Los identificadores editoriales se preservan en las declaraciones correspondientes y no se renumeran al ampliar la formalización.

## Positividad y API estable (v0.1.1)

`TratadoAnalisis.Dedekind.Positivity.TA_DEF_00091_isPositiveCut_iff` identifica `IsPositiveCut α` con `DedLT dedZero α`. La nueva declaración `TratadoAnalisis.Dedekind.isPositiveCut_iff_strictFromLe`, en `Dedekind/SquareRoots.lean`, prueba mediante `Iff.rfl` la equivalencia con `StrictFromLeManual DedLE dedZero α`. Por tanto, esta última es exactamente la condición editorial de positividad de TA-THM-00057 y TA-COR-00028, no una hipótesis adicional.

La interfaz pública emplea `alias` del módulo `Batteries.Tactic.Alias` (dependencia fijada en el manifiesto de Lake). No duplica las demostraciones ni elimina nombres anteriores. Los identificadores editoriales y las 833 huellas históricas se conservan.

| Módulo bajo `TratadoAnalisis/Dedekind/` | Nombre público bajo `TratadoAnalisis.Dedekind` | Nombre histórico bajo `TratadoAnalisis.Chapter7_0010` |
|---|---|---|
| `Completeness.lean` | `complete_ordered_field` | `TA_THM_00056_dedekind_complete_0010` |
| `Completeness.lean` | `supremum_iff_lub` | `supremum_iff_dedekind_lub_0010` |
| `Completeness.lean` | `upper_bound_iff_subset` | `TA_PRO_00104_upper_iff_subset_0010` |
| `Completeness.lean` | `supUnion` | `DedSupUnion0010` |
| `Completeness.lean` | `mem_supUnion_iff` | `mem_dedSupUnion_iff_0010` |
| `Completeness.lean` | `supUnion_eq_sUnion` | `TA_DEF_00104_union_eq_0010` |
| `Completeness.lean` | `supUnion_subset_rationals` | `TA_DEF_00104_union_subset_rationals_0010` |
| `Completeness.lean` | `infimum_exists` | `TA_COR_00025_dedekind_infimum_0010` |
| `Completeness.lean` | `archimedean` | `TA_COR_00026_dedekind_archimedean_0010` |
| `Completeness.lean` | `IsOrderedCompletionRelational` | `IsOrderedCompletionRelational0010` |
| `Completeness.lean` | `ordered_completion` | `TA_PRO_00106_dedekind_completion_0010` |
| `Density.lean` | `rational_section_dense` | `TA_COR_00027_rational_section_dense_0010` |
| `Density.lean` | `rational_graph_image_dense` | `TA_COR_00027_rational_graph_image_dense_0010` |
| `Density.lean` | `cut_mem_iff_section_lt` | `TA_LEM_00028_cut_mem_iff_section_lt_0010` |
| `SquareRoots.lean` | `quadratic_cofinality` | `quadratic_cofinality_proved_0010` |
| `SquareRoots.lean` | `alphaTwo_square_eq_section_two` | `alphaTwo_square_eq_section_two_0010` |
| `SquareRoots.lean` | `alphaTwo_positive_irrational_square_two` | `alphaTwo_positive_irrational_square_two_0010` |
| `SquareRoots.lean` | `positive_cut_mem_iff_square_mem` | `positive_cut_mem_iff_square_mem_0010` |
| `SquareRoots.lean` | `positive_cut_square_injective` | `positive_cut_square_injective_0010` |
| `SquareRoots.lean` | `positive_square_two_eq_alphaTwo` | `positive_square_two_eq_alphaTwo_0010` |
| `SquareRoots.lean` | `positive_square_two_exists_unique` | `positive_square_two_exists_unique_0010` |
| `Arithmetic.lean` | `additive_inverse_unique` | `TA_COR_00137_ded_neg_unique_0010` |
| `Arithmetic.lean` | `rational_division_compatible` | `TA_COR_00138_rational_division_0010` |
| `Arithmetic.lean` | `rational_division_exists_unique` | `TA_COR_00138_division_exists_unique_0010` |

No se introducen deprecaciones antes de v1.0.0. El fichero `certificates/v0.1.1/API_ALIASES.tsv` permite comparar automáticamente las huellas de los aliases con los originales.

## Prerrequisitos matemáticos de v0.1.2

Módulos bajo `TratadoAnalisis`. Los módulos abstractos tienen los namespaces `TratadoAnalisis.AbstractCompleteness.AbsoluteValue`, `TratadoAnalisis.AbstractCompleteness.Equivalences` y `TratadoAnalisis.AbstractCompleteness.NumeralArithmetic`. Los módulos Naturals y Rationals conservan su namespace homónimo. Los nombres públicos son estables y no contienen números de checkpoint.

| ID | Módulo | Declaraciones principales |
|---|---|---|
| TA-THM-00016 | `Naturals.OrderedArithmetic` | `TA_THM_00016_mul_add` |
| TA-THM-00017 | `Naturals.OrderedArithmetic` | `TA_THM_00017_mul_assoc` |
| TA-THM-00018 | `Naturals.OrderedArithmetic` | `TA_THM_00018_mul_comm` |
| TA-THM-00019 | `Naturals.OrderedArithmetic` | `TA_THM_00019_nat_total` |
| TA-THM-00020 | `Naturals.OrderedArithmetic` | `TA_THM_00020_nat_total_order` |
| TA-THM-00021 | `Naturals.OrderedArithmetic` | `TA_THM_00021_strict_iff_mem` |
| TA-THM-00022 | `Naturals.OrderedArithmetic` | `TA_THM_00022_nat_well_order` |
| TA-PRO-00170 | `Naturals.OrderedArithmetic` | `TA_PRO_00170_nat_trichotomy`; `TA_PRO_00170_compare_codes_spec (códigos explícitos)` |
| TA-PRO-00428 | `Naturals.OrderedArithmetic` | `TA_PRO_00428_nat_subset_and_zero_mem_succ` |
| TA-PRO-00077 | `Rationals.Incompleteness` | `TA_PRO_00077_rationals_not_complete` |
| TA-DEF-00071 | `Abstract.AbsoluteValue` | `IsAbsoluteValue`; `TA_DEF_00071_absolute_exists_unique` |
| TA-PRO-00071 | `Abstract.AbsoluteValue` | `absolute_nonnegative`; `absolute_zero_iff`; `absolute_opposite`; `absolute_bounds`; `absolute_mul`; `absolute_le_iff` |
| TA-THM-00035 | `Abstract.AbsoluteValue` | `TA_THM_00035_triangle` |
| TA-DEF-00075 | `Abstract.CompletenessEquivalences` | `HasSeparationProperty`; `HasSeparationPropertyPositive` |
| TA-THM-00038 | `Abstract.CompletenessEquivalences` | `TA_THM_00038_supremum_iff_separation`; `TA_THM_00038_supremum_iff_separation_positive` |
| TA-DEF-00076 | `Abstract.CompletenessEquivalences` | `HasClosedIntervalIntersectionProperty`; `HasClosedIntervalIntersectionPositive` |
| TA-THM-00039 | `Abstract.CompletenessEquivalences` | `TA_THM_00039_complete_iff_intersection`; `TA_THM_00039_supremum_iff_intersection_positive` |
| TA-PRO-00069 | `Abstract.NumeralArithmetic` | `TA_PRO_00069_numeral_arithmetic_order` |

Las leyes naturales y las leyes de suma/producto de numerales usan inducciones sobre códigos Nat locales y transporte a grafos conjuntistas, no la sustitución del portador. En TA-PRO-00170 la parte ejecutable exige códigos explícitos. El tercero excluido se recibe expresamente para buen orden y para los puentes de no vaciedad de las equivalencias de completitud. Las 94 consultas adicionales se fijan en el certificado v0.1.2; véanse [P01](PREREQUISITES-P01.md), [P02](PREREQUISITES-P02.md), [P03](PREREQUISITES-P03.md), [P04](PREREQUISITES-P04.md).
