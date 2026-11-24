import TratadoAnalisis.Chapter7_0010.AlphaTwoOrderBounds0010
import TratadoAnalisis.Dedekind.Multiplication
import TratadoAnalisis.Dedekind.Unit

/-! TA-LEAN-0010 / N02. Limite inferior estricto del cuadrado de alpha_2.
    La prueba usa testigos racionales positivos concretos de dedPositiveMul. -/
namespace TratadoAnalisis.Chapter7_0010
universe u

open TratadoAnalisis.AbstractCompleteness.Manual0008
open TratadoAnalisis.Dedekind.Definition
open TratadoAnalisis.Dedekind.AlphaTwo
open TratadoAnalisis.Dedekind.RationalSection
open TratadoAnalisis.Dedekind.Positivity
open TratadoAnalisis.Dedekind.PositiveMultiplication
open TratadoAnalisis.Dedekind.Multiplication
open TratadoAnalisis.Dedekind.Unit
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.StrictOrder
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.SqrtTwoSet
open TratadoAnalisis.Rationals.SquareMonotonicity
open TratadoAnalisis.Rationals.NoSupremumSqrtTwo
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.Algebra

/-- Dado em explicito, la rama positiva de la multiplicacion es exacta. -/
theorem alphaTwo_square_is_positive_product_0010
    (em : ∀ p : Prop, p ∨ ¬p) :
    dedMul (alphaTwoCut : ZFSet.{u}) alphaTwoCut =
      dedPositiveMul alphaTwoCut alphaTwoCut := by
  have hp : IsPositiveCut (alphaTwoCut : ZFSet.{u}) :=
    alphaTwoCut_positive_0010 em
  exact TA_DEF_00096_of_pos_pos hp hp

/-- Toda seccion racional menor que uno esta dentro del cuadrado. -/
theorem section_one_subset_alphaTwo_square_0010
    (em : ∀ p : Prop, p ∨ ¬p) :
    rationalSection (ratOne : ZFSet.{u}) ⊆ dedMul alphaTwoCut alphaTwoCut := by
  intro r hr
  rcases TA_DEF_00081_mem_rationalSection_iff.mp hr with ⟨hrQ, hrOne⟩
  have hprod : r ∈ dedPositiveMul alphaTwoCut alphaTwoCut :=
    mem_positiveMul_of_witness hrQ alphaTwoCut_one_mem ratZero_lt_one
      alphaTwoCut_one_mem ratZero_lt_one ratOne_square_local hrOne
  rw [alphaTwo_square_is_positive_product_0010 em]
  exact hprod

/-- Cota inferior estructural: 1_D ≤ alpha_2². -/
theorem section_one_le_alphaTwo_square_0010
    (em : ∀ p : Prop, p ∨ ¬p) :
    DedLE (dedOne : ZFSet.{u}) (dedMul alphaTwoCut alphaTwoCut) := by
  refine ⟨dedOne_mem, ?_, ?_⟩
  · exact TA_PRO_00094_dedSignedMul_mem em
      TA_PRO_00081_alphaTwoCut_mem TA_PRO_00081_alphaTwoCut_mem
  · exact section_one_subset_alphaTwo_square_0010 em

/-- La cota inferior es estricta, aprovechando la ausencia de maximo. -/
theorem section_one_lt_alphaTwo_square_0010
    (em : ∀ p : Prop, p ∨ ¬p) :
    StrictFromLeManual DedLE (dedOne : ZFSet.{u})
      (dedMul alphaTwoCut alphaTwoCut) := by
  have hle := section_one_le_alphaTwo_square_0010 em
  refine ⟨hle, ?_⟩
  rcases alphaTwoCut_no_maximum alphaTwoCut_one_mem with ⟨a, ha, hOneA⟩
  have haQ : a ∈ rationalsTA :=
    (TA_DEF_00082_mem_alphaTwoCut_iff.mp ha).1
  have h0a : RatLT ratZero a :=
    ratLT_of_lt_of_le_local ratZero_mem_rationalsTA
      ratOne_mem_rationalsTA haQ ratZero_lt_one hOneA.1
  rcases ratMul_exists haQ haQ with ⟨aa, _haaQ, haa⟩
  have hOneAA : RatLT ratOne aa :=
    TA_LEM_00018_square_strict_mono_nonnegative
      ratOne_mem_rationalsTA haQ ratZero_lt_one.1
      hOneA ratOne_square_local haa
  have hOneIn : ratOne ∈ dedPositiveMul alphaTwoCut alphaTwoCut :=
    mem_positiveMul_of_witness ratOne_mem_rationalsTA
      ha h0a ha h0a haa hOneAA
  have hOneInSq : ratOne ∈ dedMul alphaTwoCut alphaTwoCut := by
    rw [alphaTwo_square_is_positive_product_0010 em]
    exact hOneIn
  intro he
  have hOneInOne : (ratOne : ZFSet.{u}) ∈ dedOne := by
    rw [he]
    exact hOneInSq
  exact rationalSection_self_not_mem ratOne hOneInOne

end TratadoAnalisis.Chapter7_0010
