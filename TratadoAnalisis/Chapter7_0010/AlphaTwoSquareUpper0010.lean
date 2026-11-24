import TratadoAnalisis.Chapter7_0010.AlphaTwoOrderBounds0010
import TratadoAnalisis.Dedekind.Multiplication
import TratadoAnalisis.Rationals.PositiveProducts

/-! TA-LEAN-0010 / N03. Prueba relacional de la cota alpha_2² ≤ 2_D.
    Solo usa comparaciones de cuadrados racionales y productos positivos. -/
namespace TratadoAnalisis.Chapter7_0010
universe u

open TratadoAnalisis.AbstractCompleteness.Manual0008
open TratadoAnalisis.Dedekind.Definition
open TratadoAnalisis.Dedekind.AlphaTwo
open TratadoAnalisis.Dedekind.RationalSection
open TratadoAnalisis.Dedekind.Positivity
open TratadoAnalisis.Dedekind.PositiveMultiplication
open TratadoAnalisis.Dedekind.Multiplication
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.IrrationalitySqrtTwo
open TratadoAnalisis.Rationals.Signs
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.OrderedFieldCompatibility
open TratadoAnalisis.Rationals.SqrtTwoSet
open TratadoAnalisis.Rationals.SquareMonotonicity
open TratadoAnalisis.Rationals.NoSupremumSqrtTwo
open TratadoAnalisis.Rationals.PositiveProducts

/-- Un miembro racional positivo de alpha_2 tiene cuadrado < 2_Q. -/
theorem alphaTwo_positive_member_square_lt_two_0010
    (a aa : ZFSet.{u}) (ha : a ∈ alphaTwoCut)
    (h0a : RatLT ratZero a) (haa : RatMul a a aa) :
    RatLT aa ratTwoTA := by
  rcases TA_DEF_00082_mem_alphaTwoCut_iff.mp ha with ⟨haQ, hneg | hset⟩
  · exact (ratLT_asymm_cut haQ ratZero_mem_rationalsTA hneg h0a).elim
  · rcases TA_DEF_00066_mem_sqrtTwoSet_iff.mp hset with
      ⟨_, _, z, hz, hzTwo⟩
    have hza : z = aa := RatMul_unique haQ haQ hz haa
    rw [hza] at hzTwo
    exact hzTwo

/-- Dos elementos positivos de alpha_2 tienen producto racional < 2_Q. -/
theorem alphaTwo_positive_members_product_lt_two_0010
    (a b ab : ZFSet.{u})
    (ha : a ∈ alphaTwoCut) (hb : b ∈ alphaTwoCut)
    (h0a : RatLT ratZero a) (h0b : RatLT ratZero b)
    (hab : RatMul a b ab) : RatLT ab ratTwoTA := by
  have haQ : a ∈ rationalsTA :=
    (TA_DEF_00082_mem_alphaTwoCut_iff.mp ha).1
  have hbQ : b ∈ rationalsTA :=
    (TA_DEF_00082_mem_alphaTwoCut_iff.mp hb).1
  have habQ : ab ∈ rationalsTA := ratMul_value_mem hab
  rcases ratMul_exists haQ haQ with ⟨aa, haaQ, haa⟩
  rcases ratMul_exists hbQ hbQ with ⟨bb, hbbQ, hbb⟩
  have haaTwo : RatLT aa ratTwoTA :=
    alphaTwo_positive_member_square_lt_two_0010 a aa ha h0a haa
  have hbbTwo : RatLT bb ratTwoTA :=
    alphaTwo_positive_member_square_lt_two_0010 b bb hb h0b hbb
  rcases ratLE_total haQ hbQ with habLe | hbaLe
  · have habBB : RatLE ab bb :=
      ratLE_mul_nonnegative_compat haQ hbQ hbQ
        habLe h0b.1 hab hbb
    exact ratLT_of_le_of_lt_local habQ hbbQ ratTwoTA_mem_rationalsTA
      habBB hbbTwo
  · have hba : RatMul b a ab := ratMul_comm_rel haQ hbQ hab
    have habAA : RatLE ab aa :=
      ratLE_mul_nonnegative_compat hbQ haQ haQ
        hbaLe h0a.1 hba haa
    exact ratLT_of_le_of_lt_local habQ haaQ ratTwoTA_mem_rationalsTA
      habAA haaTwo

/-- Inclusion del producto de cortaduras positivas en la seccion de 2_Q. -/
theorem alphaTwo_positive_product_subset_two_0010 :
    dedPositiveMul (alphaTwoCut : ZFSet.{u}) alphaTwoCut ⊆
      rationalSection ratTwoTA := by
  intro r hr
  rcases TA_DEF_00093_mem_positiveMul_iff.mp hr with
    ⟨hrQ, a, haPos, b, hbPos, ab, hab, hrab⟩
  rcases TA_DEF_00092_mem_positivePart_iff.mp haPos with ⟨ha, h0a⟩
  rcases TA_DEF_00092_mem_positivePart_iff.mp hbPos with ⟨hb, h0b⟩
  have habQ : ab ∈ rationalsTA := ratMul_value_mem hab
  have habTwo : RatLT ab ratTwoTA :=
    alphaTwo_positive_members_product_lt_two_0010 a b ab
      ha hb h0a h0b hab
  have hrTwo : RatLT r ratTwoTA :=
    ratLT_of_lt_of_le_local hrQ habQ ratTwoTA_mem_rationalsTA
      hrab habTwo.1
  exact TA_DEF_00081_mem_rationalSection_iff.mpr ⟨hrQ, hrTwo⟩

/-- Cota superior del cuadrado de alpha_2 en R_D: alpha_2² ≤ 2_D. -/
theorem alphaTwo_square_le_section_two_0010
    (em : ∀ p : Prop, p ∨ ¬p) :
    DedLE (dedMul (alphaTwoCut : ZFSet.{u}) alphaTwoCut)
      (rationalSection ratTwoTA) := by
  have hPos : IsPositiveCut (alphaTwoCut : ZFSet.{u}) :=
    alphaTwoCut_positive_0010 em
  have hmul : dedMul (alphaTwoCut : ZFSet.{u}) alphaTwoCut =
      dedPositiveMul alphaTwoCut alphaTwoCut :=
    TA_DEF_00096_of_pos_pos hPos hPos
  refine ⟨?_, TA_PRO_00080_rationalSection_mem ratTwoTA_mem_rationalsTA, ?_⟩
  · exact TA_PRO_00094_dedSignedMul_mem em
      TA_PRO_00081_alphaTwoCut_mem TA_PRO_00081_alphaTwoCut_mem
  · intro r hr
    rw [hmul] at hr
    exact alphaTwo_positive_product_subset_two_0010 hr

end TratadoAnalisis.Chapter7_0010
