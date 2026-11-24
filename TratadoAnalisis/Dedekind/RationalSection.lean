import TratadoAnalisis.Dedekind.Definition
import TratadoAnalisis.Rationals.Density

namespace TratadoAnalisis.Dedekind.RationalSection

open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.Signs
open TratadoAnalisis.Rationals.Density
open TratadoAnalisis.Rationals.NoSupremumSqrtTwo
open TratadoAnalisis.Dedekind.Definition

/-- El testigo interior prescrito es q−1, mediante la interfaz RatSub. -/
theorem rationalSection_sub_one_mem {q : ZFSet}
    (hq : q ∈ rationalsTA) :
    ∃ d : ZFSet, RatSub q ratOne d ∧ d ∈ rationalSection q := by
  rcases ratSub_exists hq ratOne_mem_rationalsTA with ⟨d, hd, hsub⟩
  have hdone : RatAdd d ratOne q := ratSub_add_cancel hq ratOne_mem_rationalsTA hsub
  have honed := ratAdd_comm_rel hd ratOne_mem_rationalsTA hdone
  rcases ratAdd_exists ratZero_mem_rationalsTA hd with ⟨z, _, hz⟩
  have he : z = d := ratAdd_zero_left hd hz
  rw [he] at hz
  have hdq : RatLT d q :=
    (TA_LEM_00020_clause8_translate_iff ratZero_mem_rationalsTA
      ratOne_mem_rationalsTA hd hz honed).mp TA_LEM_00020_clause3_zero_lt_one
  exact ⟨d, hsub, TA_DEF_00081_mem_rationalSection_iff.mpr ⟨hd, hdq⟩⟩

/-- q es un testigo exterior explícito, sin lógica clásica. -/
theorem rationalSection_self_not_mem (q : ZFSet) :
    q ∉ rationalSection q := by
  intro h
  exact (TA_DEF_00081_mem_rationalSection_iff.mp h).2.2 rfl

theorem rationalSection_isDedekindCut {q : ZFSet}
    (hq : q ∈ rationalsTA) : IsDedekindCut (rationalSection q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    exact (TA_DEF_00081_mem_rationalSection_iff.mp hr).1
  · intro he
    rcases rationalSection_sub_one_mem hq with ⟨d, _, hd⟩
    rw [he] at hd
    exact ZFSet.notMem_empty d hd
  · intro he
    have hqSection : q ∈ rationalSection q := by
      rw [he]
      exact hq
    exact rationalSection_self_not_mem q hqSection
  · intro r hr s hs hsr
    rcases TA_DEF_00081_mem_rationalSection_iff.mp hr with ⟨hrQ, hrq⟩
    exact TA_DEF_00081_mem_rationalSection_iff.mpr
      ⟨hs, ratLT_of_lt_of_le_local hs hrQ hq hsr hrq.1⟩
  · intro r hr
    rcases TA_DEF_00081_mem_rationalSection_iff.mp hr with ⟨hrQ, hrq⟩
    rcases TA_THM_00034_rational_density hrQ hq hrq with ⟨s, hs, hrs, hsq⟩
    exact ⟨s, TA_DEF_00081_mem_rationalSection_iff.mpr ⟨hs, hsq⟩, hrs⟩

/-- TA-PRO-00080: toda sección racional pertenece al conjunto de cortaduras. -/
theorem TA_PRO_00080_rationalSection_mem {q : ZFSet}
    (hq : q ∈ rationalsTA) : rationalSection q ∈ dedekindCutsTA :=
  TA_PRO_00079_mem_dedekindCuts_iff.mpr (rationalSection_isDedekindCut hq)

end TratadoAnalisis.Dedekind.RationalSection

