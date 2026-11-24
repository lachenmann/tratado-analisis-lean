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
