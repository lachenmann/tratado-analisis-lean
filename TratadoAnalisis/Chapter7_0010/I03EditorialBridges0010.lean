import TratadoAnalisis.Chapter7_0010.Completion0010
import TratadoAnalisis.Chapter7_0010.Chapter6Corollaries0010

/-! TA-LEAN-0010 / I03. Explicit editorial bridges; no new mathematical axioms. -/
namespace TratadoAnalisis.Chapter7_0010
universe u
set_option autoImplicit false

open TratadoAnalisis.AbstractCompleteness.Manual0008
open TratadoAnalisis.AbstractCompleteness.Density0009
open TratadoAnalisis.Dedekind.Definition
open TratadoAnalisis.Dedekind.RationalSection
open TratadoAnalisis.Dedekind.Addition
open TratadoAnalisis.Dedekind.Embedding
open TratadoAnalisis.Dedekind.Division
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Field
open TratadoAnalisis.Rationals.Division

/-- TA-DEF-00104: the union is contained in the rational carrier. -/
theorem TA_DEF_00104_union_subset_rationals_0010
    (A : ZFSet.{u}) (hA : A ⊆ dedekindCutsTA) :
    DedSupUnion0010 A ⊆ rationalsTA := by
  intro q hq
  obtain ⟨a, ha, hqa⟩ := (mem_dedSupUnion_iff_0010 A q).mp hq
  exact (TA_PRO_00079_mem_dedekindCuts_iff.mp (hA ha)).1 hqa

/-- TA-COR-00027: density of the set-theoretic image, including carrier inclusion. -/
theorem TA_COR_00027_rational_graph_image_dense_0010
    (em : ∀ p : Prop, p ∨ ¬p) :
    IsOrderDenseSubsetManual (dedekindCutsTA : ZFSet.{u})
      (RationalImageByGraphManual rationalsTA dedekindCutsTA dedekindEmbeddingGraph)
      DedLE := by
  refine ⟨rationalImageByGraph_subset_manual rationalsTA dedekindCutsTA
    dedekindEmbeddingGraph, ?_⟩
  intro x y hx hy hxy
  obtain ⟨q, hq, hxq, hqy⟩ := TA_COR_00027_rational_section_dense_0010 em x y hx hy hxy
  have hcut : rationalSection q ∈ dedekindCutsTA := TA_PRO_00080_rationalSection_mem hq
  have hpair : ZFSet.pair q (rationalSection q) ∈ dedekindEmbeddingGraph :=
    TA_DEF_00084_mem_embeddingGraph_iff.mpr ⟨hq, hcut, rfl⟩
  refine ⟨rationalSection q, ?_, hxq, hqy⟩
  exact (mem_rationalImageByGraph_iff_manual rationalsTA dedekindCutsTA
    dedekindEmbeddingGraph (rationalSection q)).mpr ⟨hcut, q, hq, hpair⟩

/-- TA-COR-00138: total unique rational quotient with the editorial compatibility. -/
theorem TA_COR_00138_division_exists_unique_0010
    (em : ∀ p : Prop, p ∨ ¬p) (p q : ZFSet.{u})
    (hp : p ∈ rationalsTA) (hq : q ∈ rationalsTA) (hq0 : q ≠ ratZero) :
    ∃! d : ZFSet.{u}, d ∈ rationalsTA ∧ RatDiv p q d ∧
      rationalSection q ≠ dedZero ∧
      rationalSection d = dedDiv (rationalSection p) (rationalSection q) := by
  have hqn : q ∈ ratNonzeroTA := mem_ratNonzeroTA_iff.mpr ⟨hq, hq0⟩
  obtain ⟨d, hdQ, hd⟩ := ratDiv_exists hp hqn
  have hc := TA_COR_00138_rational_division_0010 em p q d hp hq hq0 hd
  refine ⟨d, ⟨hdQ, hd, hc.1, hc.2⟩, ?_⟩
  intro w hw
  exact RatDiv_unique hp hqn hw.2.1 hd

end TratadoAnalisis.Chapter7_0010
