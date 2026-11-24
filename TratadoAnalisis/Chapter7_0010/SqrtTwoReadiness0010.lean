import TratadoAnalisis.Chapter7_0010.CutPosition0010

/-! TA-LEAN-0010 / P06. Solo hitos existentes hacia TA-THM-00057
    y TA-COR-00028. No afirma ni supone que alphaTwoCut² = 2.
    La igualdad de cuadrados y la unicidad positiva permanecen como
    obligaciones ABIERTAS y se registran en el resumen del auditor. -/
namespace TratadoAnalisis.Chapter7_0010
universe u

open TratadoAnalisis.AbstractCompleteness.Manual0008
open TratadoAnalisis.Dedekind.Definition
open TratadoAnalisis.Dedekind.Addition
open TratadoAnalisis.Dedekind.Order
open TratadoAnalisis.Dedekind.AlphaTwo
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive

/-- alpha_2 se encuentra estrictamente por encima de la cortadura cero. -/
theorem alphaTwoCut_positive_0010
    (em : ∀ p : Prop, p ∨ ¬p) :
    StrictFromLeManual DedLE (dedZero : ZFSet.{u}) alphaTwoCut := by
  have h : StrictFromLeManual DedLE
      (rationalSection (ratZero : ZFSet.{u})) alphaTwoCut :=
    (TA_LEM_00028_cut_mem_iff_section_lt_0010
      em alphaTwoCut ratZero TA_PRO_00081_alphaTwoCut_mem
      ratZero_mem_rationalsTA).1 alphaTwoCut_zero_mem
  simpa only [dedZero] using h

/-- alpha_2 no coincide con ninguna seccion racional. -/
theorem alphaTwoCut_not_rational_0010
    (q : ZFSet.{u}) (hq : q ∈ rationalsTA) :
    alphaTwoCut ≠ rationalSection q := by
  exact TA_PRO_00082_alphaTwoCut_ne_rationalSection hq

end TratadoAnalisis.Chapter7_0010
