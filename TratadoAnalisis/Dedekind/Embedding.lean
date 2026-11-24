import TratadoAnalisis.Dedekind.RationalSection
import TratadoAnalisis.Dedekind.AlphaTwo
import TratadoAnalisis.Dedekind.Order

namespace TratadoAnalisis.Dedekind.Embedding

universe u

open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.Trichotomy
open TratadoAnalisis.Rationals.NoSupremumSqrtTwo
open TratadoAnalisis.Dedekind.Definition
open TratadoAnalisis.Dedekind.RationalSection
open TratadoAnalisis.Dedekind.AlphaTwo
open TratadoAnalisis.Dedekind.Order

/-- TA-DEF-00084: grafo por Separación en el producto fundacional. -/
def dedekindEmbeddingGraph : ZFSet.{u} :=
  ZFSet.sep
    (fun z => ∃ q α : ZFSet.{u}, z = ZFSet.pair q α ∧ α = rationalSection q)
    (cartesianProductFoundational rationalsTA dedekindCutsTA)

theorem TA_DEF_00084_mem_embeddingGraph_iff {q α : ZFSet.{u}} :
    ZFSet.pair q α ∈ dedekindEmbeddingGraph ↔
      q ∈ rationalsTA ∧ α ∈ dedekindCutsTA ∧ α = rationalSection q := by
  constructor
  · intro h
    rcases ZFSet.mem_sep.mp h with ⟨hprod, q', α', he, hsection⟩
    have hcoords := ZFSet.pair_injective he
    rcases hcoords with ⟨rfl, rfl⟩
    exact ⟨(mem_cartesianProductFoundational.mp hprod).1,
      (mem_cartesianProductFoundational.mp hprod).2, hsection⟩
  · rintro ⟨hq, hα, he⟩
    exact ZFSet.mem_sep.mpr
      ⟨mem_cartesianProductFoundational.mpr ⟨hq, hα⟩, q, α, rfl, he⟩

theorem TA_DEF_00084_embeddingGraph_isFunc :
    IsFuncFoundational (rationalsTA : ZFSet.{u}) dedekindCutsTA dedekindEmbeddingGraph := by
  constructor
  · intro z hz
    rcases (ZFSet.mem_sep.mp hz).2 with ⟨q, α, he, _⟩
    rw [he] at hz
    rcases TA_DEF_00084_mem_embeddingGraph_iff.mp hz with ⟨hq, hα, _⟩
    exact ⟨q, hq, α, hα, he⟩
  · intro q hq
    have hsection := TA_PRO_00080_rationalSection_mem hq
    refine ⟨rationalSection q, ⟨hsection, ?_⟩, ?_⟩
    · exact TA_DEF_00084_mem_embeddingGraph_iff.mpr ⟨hq, hsection, rfl⟩
    · intro α hα
      exact (TA_DEF_00084_mem_embeddingGraph_iff.mp hα.2).2.2

/-- TA-PRO-00083, sin totalidad clásica del orden de cortaduras. -/
theorem TA_PRO_00083_ratLE_iff_sections_subset {p q : ZFSet.{u}}
    (hp : p ∈ rationalsTA) (hq : q ∈ rationalsTA) :
    RatLE p q ↔ rationalSection p ⊆ rationalSection q := by
  constructor
  · intro hpq r hr
    rcases TA_DEF_00081_mem_rationalSection_iff.mp hr with ⟨hrQ, hrp⟩
    exact TA_DEF_00081_mem_rationalSection_iff.mpr
      ⟨hrQ, ratLT_of_lt_of_le_local hrQ hp hq hrp hpq⟩
  · intro hsub
    rcases TA_PRO_00172_rational_trichotomy hp hq with hpq | he | hqp
    · exact hpq.1
    · rw [he]
      exact ratLE_refl hq
    · have hqP : q ∈ rationalSection p :=
        TA_DEF_00081_mem_rationalSection_iff.mpr ⟨hq, hqp⟩
      exact (rationalSection_self_not_mem q (hsub hqP)).elim

theorem TA_COR_00016_rationalSection_injective {p q : ZFSet.{u}}
    (hp : p ∈ rationalsTA) (hq : q ∈ rationalsTA)
    (he : rationalSection p = rationalSection q) : p = q := by
  apply ratLE_antisymm hp hq
  · exact (TA_PRO_00083_ratLE_iff_sections_subset hp hq).mpr (fun _ hr => he ▸ hr)
  · exact (TA_PRO_00083_ratLE_iff_sections_subset hq hp).mpr (fun _ hr => he.symm ▸ hr)

theorem TA_COR_00016_ratLT_iff_sections_dedLT {p q : ZFSet.{u}}
    (hp : p ∈ rationalsTA) (hq : q ∈ rationalsTA) :
    RatLT p q ↔ DedLT (rationalSection p) (rationalSection q) := by
  constructor
  · intro hpq
    refine ⟨⟨TA_PRO_00080_rationalSection_mem hp, TA_PRO_00080_rationalSection_mem hq,
      (TA_PRO_00083_ratLE_iff_sections_subset hp hq).mp hpq.1⟩, ?_⟩
    intro he
    exact hpq.2 (TA_COR_00016_rationalSection_injective hp hq he)
  · intro h
    refine ⟨(TA_PRO_00083_ratLE_iff_sections_subset hp hq).mpr h.1.2.2, ?_⟩
    intro he
    exact h.2 (congrArg rationalSection he)

/-- TA-COR-00017: no toda cortadura es una sección racional. -/
theorem TA_COR_00017_not_every_cut_is_section :
    ¬ (∀ α : ZFSet.{u}, α ∈ dedekindCutsTA →
      ∃ q : ZFSet.{u}, q ∈ rationalsTA ∧ rationalSection q = α) := by
  intro hall
  rcases hall alphaTwoCut TA_PRO_00081_alphaTwoCut_mem with ⟨q, hq, he⟩
  exact TA_PRO_00082_alphaTwoCut_ne_rationalSection hq he.symm

/-- TA-COR-00017: testigo explícito fuera de la imagen del grafo. -/
theorem TA_COR_00017_alphaTwo_outside_embedding_image :
    (alphaTwoCut : ZFSet.{u}) ∈ dedekindCutsTA ∧
      ¬ ∃ q : ZFSet.{u}, q ∈ rationalsTA ∧ ZFSet.pair q alphaTwoCut ∈ dedekindEmbeddingGraph := by
  refine ⟨TA_PRO_00081_alphaTwoCut_mem, ?_⟩
  rintro ⟨q, hq, hgraph⟩
  exact TA_PRO_00082_alphaTwoCut_ne_rationalSection hq
    (TA_DEF_00084_mem_embeddingGraph_iff.mp hgraph).2.2

end TratadoAnalisis.Dedekind.Embedding

