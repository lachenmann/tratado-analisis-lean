import TratadoAnalisis.Dedekind.AlphaTwo
import TratadoAnalisis.Abstract.ArchimedeanEditorialBridge0008

/-! TA-LEAN-0010 / P04, independiente de P00--P03.
    TA-LEM-00028. La prueba usa tercero excluido explicito SOLO para
    extraer un testigo de la no-inclusion en la direccion reciproca. -/
namespace TratadoAnalisis.Chapter7_0010
universe u

open TratadoAnalisis.AbstractCompleteness.Manual0008
open TratadoAnalisis.Dedekind.Definition
open TratadoAnalisis.Dedekind.Order
open TratadoAnalisis.Dedekind.RationalSection
open TratadoAnalisis.Dedekind.AlphaTwo
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.Trichotomy

/-- TA-LEM-00028: q pertenece a la cortadura si y solo si
    su seccion racional esta estrictamente por debajo de ella. -/
theorem TA_LEM_00028_cut_mem_iff_section_lt_0010
    (em : ∀ p : Prop, p ∨ ¬p)
    (alpha q : ZFSet.{u})
    (halpha : alpha ∈ dedekindCutsTA)
    (hq : q ∈ rationalsTA) :
    q ∈ alpha ↔
      StrictFromLeManual DedLE (rationalSection q) alpha := by
  have hsection : rationalSection q ∈ dedekindCutsTA :=
    TA_PRO_00080_rationalSection_mem hq
  have hcut : IsDedekindCut alpha :=
    TA_PRO_00079_mem_dedekindCuts_iff.mp halpha
  constructor
  · intro hqa
    refine ⟨⟨hsection, halpha, ?_⟩, ?_⟩
    · intro r hr
      have hsec := TA_DEF_00081_mem_rationalSection_iff.mp hr
      exact hcut.2.2.2.1 q hqa r hsec.1 hsec.2
    · intro he
      have hqq : q ∈ rationalSection q := by
        rw [he]
        exact hqa
      exact (TA_DEF_00081_mem_rationalSection_iff.mp hqq).2.2 rfl
  · intro hstrict
    have hnsubset : ¬ alpha ⊆ rationalSection q := by
      intro hback
      exact hstrict.2 (TA_THM_00001_zfset_eq_iff_subset.mpr
        ⟨hstrict.1.2.2, hback⟩)
    obtain ⟨r, hr, hnot⟩ := subset_failure_witness em hnsubset
    have hrQ : r ∈ rationalsTA := hcut.1 hr
    rcases TA_PRO_00172_rational_trichotomy hrQ hq with hrq | he | hqr
    · exact (hnot (TA_DEF_00081_mem_rationalSection_iff.mpr
        ⟨hrQ, hrq⟩)).elim
    · simpa only [← he] using hr
    · exact hcut.2.2.2.1 r hr q hq hqr

/-- Certificado ya existente de la no racionalidad de alpha_2. -/
theorem alphaTwoCut_is_cut_0010 :
    (alphaTwoCut : ZFSet.{u}) ∈ dedekindCutsTA :=
  TA_PRO_00081_alphaTwoCut_mem

end TratadoAnalisis.Chapter7_0010
