import TratadoAnalisis.Chapter7_0010.SqrtTwoReadiness0010
import TratadoAnalisis.Dedekind.AlphaTwo

/-! TA-LEAN-0010 / fase extendida N01.
    Relacion de orden entre la frontera alpha_2 y las secciones racionales.
    Ningun enunciado presupone que alpha_2 al cuadrado sea 2_D. -/
namespace TratadoAnalisis.Chapter7_0010
universe u

open TratadoAnalisis.AbstractCompleteness.Manual0008
open TratadoAnalisis.Dedekind.Definition
open TratadoAnalisis.Dedekind.Order
open TratadoAnalisis.Dedekind.RationalSection
open TratadoAnalisis.Dedekind.AlphaTwo
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.IrrationalitySqrtTwo
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.SqrtTwoSet
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.Algebra

/-- Todo racional exterior a alpha_2 es extremo superior de la cortadura. -/
theorem alphaTwo_le_section_of_exterior_0010
    (q : ZFSet.{u}) (hq : q ∈ rationalsTA) (hnot : q ∉ alphaTwoCut) :
    DedLE alphaTwoCut (rationalSection q) := by
  refine ⟨TA_PRO_00081_alphaTwoCut_mem,
    TA_PRO_00080_rationalSection_mem hq, ?_⟩
  intro r hr
  have hrq : RatLT r q :=
    cut_member_lt_nonmember alphaTwoCut_isDedekindCut hq hnot hr
  exact TA_DEF_00081_mem_rationalSection_iff.mpr
    ⟨(TA_DEF_00082_mem_alphaTwoCut_iff.mp hr).1, hrq⟩

/-- Si un racional es exterior a alpha_2, la desigualdad es estricta. -/
theorem alphaTwo_lt_section_of_exterior_0010
    (q : ZFSet.{u}) (hq : q ∈ rationalsTA) (hnot : q ∉ alphaTwoCut) :
    StrictFromLeManual DedLE alphaTwoCut (rationalSection q) := by
  exact ⟨alphaTwo_le_section_of_exterior_0010 q hq hnot,
    TA_PRO_00082_alphaTwoCut_ne_rationalSection hq⟩

/-- Si q>0 y q²>2, la seccion de q esta por encima de alpha_2. -/
theorem alphaTwo_lt_section_of_supercritical_square_0010
    (q qq : ZFSet.{u}) (hq : q ∈ rationalsTA)
    (h0q : RatLT ratZero q) (hqq : RatMul q q qq)
    (hTwoQQ : RatLT ratTwoTA qq) :
    StrictFromLeManual DedLE alphaTwoCut (rationalSection q) := by
  exact alphaTwo_lt_section_of_exterior_0010 q hq
    (alphaTwoCut_not_mem_of_square_above hq h0q hqq hTwoQQ)

/-- La cortadura alpha_2 se halla estrictamente por debajo de 2_D. -/
theorem alphaTwo_strict_below_section_two_0010 :
    StrictFromLeManual DedLE (alphaTwoCut : ZFSet.{u})
      (rationalSection ratTwoTA) := by
  exact alphaTwo_lt_section_of_exterior_0010 ratTwoTA
    ratTwoTA_mem_rationalsTA alphaTwoCut_two_not_mem

end TratadoAnalisis.Chapter7_0010
