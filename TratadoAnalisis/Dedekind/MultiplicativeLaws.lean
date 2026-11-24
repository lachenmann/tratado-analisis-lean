import TratadoAnalisis.Dedekind.ProductSignLaws

namespace TratadoAnalisis.Dedekind.MultiplicativeLaws
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

open TratadoAnalisis.Dedekind.PositiveProductLaws
open TratadoAnalisis.Dedekind.ProductSignLaws

theorem signedMul_swap_subset {α β : ZFSet.{u}}
    (hα : α ⊆ rationalsTA) (hβ : β ⊆ rationalsTA) :
    dedSignedMul α β ⊆ dedSignedMul β α := by
  intro r hr
  rcases TA_DEF_00096_mem_dedSignedMul_iff.mp hr with ⟨hrQ, hr⟩
  apply TA_DEF_00096_mem_dedSignedMul_iff.mpr
  refine ⟨hrQ, ?_⟩
  rcases hr with h | h | h | h | h
  · exact Or.inl ⟨h.1.symm, h.2⟩
  · exact Or.inr (Or.inl ⟨h.2.1, h.1,
      (positiveMul_comm_of_subsets hα hβ) ▸ h.2.2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h.2.1, h.1,
      (positiveMul_comm_of_subsets (dedNeg_subset_rationals α) (dedNeg_subset_rationals β)) ▸ h.2.2⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h.2.1, h.1,
      congrArg dedNeg (positiveMul_comm_of_subsets hα (dedNeg_subset_rationals β)) ▸ h.2.2⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h.2.1, h.1,
      congrArg dedNeg (positiveMul_comm_of_subsets (dedNeg_subset_rationals α) hβ) ▸ h.2.2⟩)))

/-- Hallazgo constructivo: permutar los cinco disyuntos no decide el signo. -/
theorem TA_THM_00050_dedMul_comm {α β : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) (hβ : β ∈ dedekindCutsTA) :
    dedMul α β = dedMul β α := by
  have ca := (TA_PRO_00079_mem_dedekindCuts_iff.mp hα).1
  have cb := (TA_PRO_00079_mem_dedekindCuts_iff.mp hβ).1
  exact TA_THM_00001_zfset_eq_iff_subset.mpr
    ⟨signedMul_swap_subset ca cb, signedMul_swap_subset cb ca⟩

theorem positive_general_assoc (em : ∀ p : Prop, p ∨ ¬p)
    {α β γ : ZFSet.{u}} (ha : IsPositiveCut α) (hb : IsPositiveCut β) (hc : IsPositiveCut γ) :
    dedMul (dedMul α β) γ = dedMul α (dedMul β γ) := by
  have hab := signedMul_positive_of_pos_pos em ha hb
  have hbc := signedMul_positive_of_pos_pos em hb hc
  change dedSignedMul (dedSignedMul α β) γ = dedSignedMul α (dedSignedMul β γ)
  rw [TA_DEF_00096_of_pos_pos hab hc, TA_DEF_00096_of_pos_pos ha hbc,
    TA_DEF_00096_of_pos_pos ha hb, TA_DEF_00096_of_pos_pos hb hc]
  exact TA_THM_00048_positiveMul_assoc ha hb hc

theorem cut_zero_or_positive_magnitude (em : ∀ p : Prop, p ∨ ¬p)
    {α : ZFSet.{u}} (hα : α ∈ dedekindCutsTA) :
    α = dedZero ∨ ∃ a : ZFSet.{u}, IsPositiveCut a ∧ (α = a ∨ α = dedNeg a) := by
  rcases TA_PRO_00093_zero_sign_trichotomy em hα with hn | he | hp
  · exact Or.inr ⟨dedNeg α, negative_implies_positive_neg em hα hn,
      Or.inr (TA_LEM_00025_dedNeg_involutive em hα).symm⟩
  · exact Or.inl he
  · exact Or.inr ⟨α, hp, Or.inl rfl⟩

theorem TA_THM_00051_dedMul_assoc (em : ∀ p : Prop, p ∨ ¬p)
    {α β γ : ZFSet.{u}} (hα : α ∈ dedekindCutsTA)
    (hβ : β ∈ dedekindCutsTA) (hγ : γ ∈ dedekindCutsTA) :
    dedMul (dedMul α β) γ = dedMul α (dedMul β γ) := by
  rcases cut_zero_or_positive_magnitude em hα with he | ⟨a, pa, ea⟩
  · rw [he]
    simp only [dedMul_zero_left]
  rcases cut_zero_or_positive_magnitude em hβ with he | ⟨b, pb, eb⟩
  · rw [he]
    simp only [dedMul_zero_right, dedMul_zero_left]
  rcases cut_zero_or_positive_magnitude em hγ with he | ⟨c, pc, ec⟩
  · rw [he]
    simp only [dedMul_zero_right]
  have ha := pa.1.2.1
  have hb := pb.1.2.1
  have hc := pc.1.2.1
  have hab : dedMul a b ∈ dedekindCutsTA := TA_PRO_00094_dedSignedMul_mem em ha hb
  have hbc : dedMul b c ∈ dedekindCutsTA := TA_PRO_00094_dedSignedMul_mem em hb hc
  rcases ea with rfl | rfl <;> rcases eb with rfl | rfl <;> rcases ec with rfl | rfl
  all_goals
    simp only [dedMul_neg_neg em ha hb, dedMul_neg_neg em hb hc,
      dedMul_neg_neg em hab hc, dedMul_neg_neg em ha hbc,
      dedMul_neg_left em ha hb, dedMul_neg_right em ha hb,
      dedMul_neg_left em hb hc, dedMul_neg_right em hb hc,
      dedMul_neg_left em hab hc, dedMul_neg_right em hab hc,
      dedMul_neg_left em ha hbc, dedMul_neg_right em ha hbc,
      positive_general_assoc em pa pb pc]


end TratadoAnalisis.Dedekind.MultiplicativeLaws
