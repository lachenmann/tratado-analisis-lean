import TratadoAnalisis.Dedekind.AdditiveIdentities

namespace TratadoAnalisis.Dedekind.ProductSignLaws
universe u
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.Field
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.OrderedFieldCompatibility
open TratadoAnalisis.Rationals.StrictOrder
open TratadoAnalisis.Rationals.NoSupremumSqrtTwo
open TratadoAnalisis.Rationals.Signs
open TratadoAnalisis.Rationals.Division
open TratadoAnalisis.Rationals.PositiveProducts
open TratadoAnalisis.Rationals.Trichotomy
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.SquareMonotonicity
open TratadoAnalisis.Rationals.InverseOrder
open TratadoAnalisis.Rationals.DifferenceOrder
open TratadoAnalisis.Rationals.PositiveBounds
open TratadoAnalisis.Dedekind.Definition
open TratadoAnalisis.Dedekind.Order
open TratadoAnalisis.Dedekind.RationalSection
open TratadoAnalisis.Dedekind.Addition
open TratadoAnalisis.Dedekind.Negation
open TratadoAnalisis.Dedekind.AdditiveGroup
open TratadoAnalisis.Dedekind.Positivity
open TratadoAnalisis.Dedekind.PositiveMultiplication
open TratadoAnalisis.Dedekind.Signs
open TratadoAnalisis.Dedekind.Multiplication
open TratadoAnalisis.Dedekind.Unit
open TratadoAnalisis.Foundations.FunctionTriple

/-- TA-LEM-00027: tres identidades, sin usar conmutatividad posterior. -/
theorem TA_LEM_00027_product_signs (em : ∀ p : Prop, p ∨ ¬p)
    {α β : ZFSet.{u}} (hα : α ∈ dedekindCutsTA) (hβ : β ∈ dedekindCutsTA) :
    dedMul (dedNeg α) β = dedNeg (dedMul α β) ∧
      dedMul α (dedNeg β) = dedNeg (dedMul α β) ∧
      dedMul (dedNeg α) (dedNeg β) = dedMul α β := by
  rcases TA_PRO_00093_zero_sign_trichotomy em hα with hnα | heα | hpα
  · rcases TA_PRO_00093_zero_sign_trichotomy em hβ with hnβ | heβ | hpβ
    · have hppα := negative_implies_positive_neg em hα hnα
      have hppβ := negative_implies_positive_neg em hβ hnβ
      refine ⟨?_, ?_, ?_⟩ <;> simp only [dedMul, TA_DEF_00096_of_neg_neg hnα hnβ, TA_DEF_00096_of_pos_neg hppα hnβ, TA_DEF_00096_of_neg_pos hnα hppβ, TA_DEF_00096_of_pos_pos hppα hppβ, TA_LEM_00025_dedNeg_involutive em hα, TA_LEM_00025_dedNeg_involutive em hβ]
    · rw [heβ]
      refine ⟨?_, ?_, ?_⟩ <;> simp only [dedMul, TA_LEM_00024_dedNeg_zero, TA_DEF_00096_zero_left, TA_DEF_00096_zero_right]
    · have hppα := negative_implies_positive_neg em hα hnα
      have hnnβ := positive_implies_negative_neg em hβ hpβ
      have hprod := (TA_DEF_00091_mem_positiveCuts_iff.mp (TA_PRO_00090_positiveMul_mem em
        (TA_DEF_00091_mem_positiveCuts_iff.mpr hppα) (TA_DEF_00091_mem_positiveCuts_iff.mpr hpβ))).1.2.1
      refine ⟨?_, ?_, ?_⟩ <;> simp only [dedMul, TA_DEF_00096_of_neg_pos hnα hpβ, TA_DEF_00096_of_pos_pos hppα hpβ, TA_DEF_00096_of_neg_neg hnα hnnβ, TA_DEF_00096_of_pos_neg hppα hnnβ, TA_LEM_00025_dedNeg_involutive em hα, TA_LEM_00025_dedNeg_involutive em hβ, TA_LEM_00025_dedNeg_involutive em hprod]
  · rcases TA_PRO_00093_zero_sign_trichotomy em hβ with hnβ | heβ | hpβ
    · rw [heα]
      refine ⟨?_, ?_, ?_⟩ <;> simp only [dedMul, TA_LEM_00024_dedNeg_zero, TA_DEF_00096_zero_left, TA_DEF_00096_zero_right]
    · rw [heα]
      refine ⟨?_, ?_, ?_⟩ <;> simp only [dedMul, TA_LEM_00024_dedNeg_zero, TA_DEF_00096_zero_left, TA_DEF_00096_zero_right]
    · rw [heα]
      refine ⟨?_, ?_, ?_⟩ <;> simp only [dedMul, TA_LEM_00024_dedNeg_zero, TA_DEF_00096_zero_left, TA_DEF_00096_zero_right]
  · rcases TA_PRO_00093_zero_sign_trichotomy em hβ with hnβ | heβ | hpβ
    · have hnnα := positive_implies_negative_neg em hα hpα
      have hppβ := negative_implies_positive_neg em hβ hnβ
      have hprod := (TA_DEF_00091_mem_positiveCuts_iff.mp (TA_PRO_00090_positiveMul_mem em
        (TA_DEF_00091_mem_positiveCuts_iff.mpr hpα) (TA_DEF_00091_mem_positiveCuts_iff.mpr hppβ))).1.2.1
      refine ⟨?_, ?_, ?_⟩ <;> simp only [dedMul, TA_DEF_00096_of_pos_neg hpα hnβ, TA_DEF_00096_of_neg_neg hnnα hnβ, TA_DEF_00096_of_pos_pos hpα hppβ, TA_DEF_00096_of_neg_pos hnnα hppβ, TA_LEM_00025_dedNeg_involutive em hα, TA_LEM_00025_dedNeg_involutive em hβ, TA_LEM_00025_dedNeg_involutive em hprod]
    · rw [heβ]
      refine ⟨?_, ?_, ?_⟩ <;> simp only [dedMul, TA_LEM_00024_dedNeg_zero, TA_DEF_00096_zero_left, TA_DEF_00096_zero_right]
    · have hnnα := positive_implies_negative_neg em hα hpα
      have hnnβ := positive_implies_negative_neg em hβ hpβ
      refine ⟨?_, ?_, ?_⟩ <;> simp only [dedMul, TA_DEF_00096_of_pos_pos hpα hpβ, TA_DEF_00096_of_neg_pos hnnα hpβ, TA_DEF_00096_of_pos_neg hpα hnnβ, TA_DEF_00096_of_neg_neg hnnα hnnβ, TA_LEM_00025_dedNeg_involutive em hα, TA_LEM_00025_dedNeg_involutive em hβ]


theorem dedMul_zero_left {β : ZFSet.{u}} : dedMul dedZero β = dedZero := TA_DEF_00096_zero_left

theorem dedMul_zero_right {α : ZFSet.{u}} : dedMul α dedZero = dedZero := TA_DEF_00096_zero_right

theorem dedMul_neg_left (em : ∀ p : Prop, p ∨ ¬p) {α β : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) (hβ : β ∈ dedekindCutsTA) :
    dedMul (dedNeg α) β = dedNeg (dedMul α β) := (TA_LEM_00027_product_signs em hα hβ).1

theorem dedMul_neg_right (em : ∀ p : Prop, p ∨ ¬p) {α β : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) (hβ : β ∈ dedekindCutsTA) :
    dedMul α (dedNeg β) = dedNeg (dedMul α β) := (TA_LEM_00027_product_signs em hα hβ).2.1

theorem dedMul_neg_neg (em : ∀ p : Prop, p ∨ ¬p) {α β : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) (hβ : β ∈ dedekindCutsTA) :
    dedMul (dedNeg α) (dedNeg β) = dedMul α β := (TA_LEM_00027_product_signs em hα hβ).2.2


end TratadoAnalisis.Dedekind.ProductSignLaws
