import TratadoAnalisis.Dedekind.TranslationOrder

namespace TratadoAnalisis.Dedekind.MultiplicativeOrder
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
open TratadoAnalisis.Dedekind.TranslationOrder

/-- Núcleo de inclusión de los productos positivos, sin decidir signos. -/
theorem positiveMul_mono {α β γ δ : ZFSet.{u}}
    (hab : α ⊆ β) (hcd : γ ⊆ δ) :
    dedPositiveMul α γ ⊆ dedPositiveMul β δ := by
  intro r hr
  rcases TA_DEF_00093_mem_positiveMul_iff.mp hr with ⟨hrQ, a, ha, b, hb, p, hp, hrp⟩
  rcases TA_DEF_00092_mem_positivePart_iff.mp ha with ⟨ha, h0a⟩
  rcases TA_DEF_00092_mem_positivePart_iff.mp hb with ⟨hb, h0b⟩
  exact mem_positiveMul_of_witness hrQ (hab ha) h0a (hcd hb) h0b hp hrp

theorem nonnegative_mul (em : ∀ p : Prop, p ∨ ¬p)
    {α β : ZFSet.{u}} (hα : DedLE dedZero α) (hβ : DedLE dedZero β) :
    DedLE dedZero (dedMul α β) := by
  change DedLE dedZero (dedSignedMul α β)
  rcases TA_PRO_00093_zero_sign_trichotomy em hα.2.1 with hn | he | hp
  · exact (hn.2 (dedLE_antisymm hn.1 hα)).elim
  · rw [he, TA_DEF_00096_zero_left]
    exact dedLE_refl dedZero_mem
  · rcases TA_PRO_00093_zero_sign_trichotomy em hβ.2.1 with kn | ke | kp
    · exact (kn.2 (dedLE_antisymm kn.1 hβ)).elim
    · rw [ke, TA_DEF_00096_zero_right]
      exact dedLE_refl dedZero_mem
    · exact (signedMul_positive_of_pos_pos em hp kp).1

theorem TA_PRO_00103_order_compatible (em : ∀ p : Prop, p ∨ ¬p) :
    (∀ α β γ : ZFSet.{u}, α ∈ dedekindCutsTA → β ∈ dedekindCutsTA →
      γ ∈ dedekindCutsTA → DedLE α β →
      DedLE (dedAdd α γ) (dedAdd β γ)) ∧
    (∀ α β : ZFSet.{u}, DedLE dedZero α → DedLE dedZero β →
      DedLE dedZero (dedMul α β)) := by
  exact ⟨fun _ _ _ ha hb hc h =>
    (TA_PRO_00101_dedLE_translate em ha hb hc).mp h,
    fun _ _ ha hb => nonnegative_mul em ha hb⟩


end TratadoAnalisis.Dedekind.MultiplicativeOrder
