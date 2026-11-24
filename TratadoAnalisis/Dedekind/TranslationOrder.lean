import TratadoAnalisis.Dedekind.PositiveInverse

namespace TratadoAnalisis.Dedekind.TranslationOrder
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

/-- Transporte de inclusiones sin clausura ni em. -/
theorem dedAdd_mono_right {α β γ : ZFSet.{u}} (h : α ⊆ β) :
    dedAdd α γ ⊆ dedAdd β γ := by
  intro r hr
  rcases TA_DEF_00085_mem_dedAdd_iff.mp hr with ⟨hrQ, a, ha, c, hc, hs⟩
  exact TA_DEF_00085_mem_dedAdd_iff.mpr ⟨hrQ, a, h ha, c, hc, hs⟩

theorem dedAdd_mono_left {α β γ : ZFSet.{u}} (h : α ⊆ β) :
    dedAdd γ α ⊆ dedAdd γ β := by
  intro r hr
  rcases TA_DEF_00085_mem_dedAdd_iff.mp hr with ⟨hrQ, c, hc, a, ha, hs⟩
  exact TA_DEF_00085_mem_dedAdd_iff.mpr ⟨hrQ, c, hc, a, h ha, hs⟩

theorem dedAdd_translate_restore (em : ∀ p : Prop, p ∨ ¬p)
    {α γ : ZFSet.{u}} (hα : α ∈ dedekindCutsTA) (hγ : γ ∈ dedekindCutsTA) :
    dedAdd (dedAdd α γ) (dedNeg γ) = α := by
  rw [TA_THM_00041_dedAdd_assoc hα hγ (TA_PRO_00087_dedNeg_mem em hγ),
    TA_PRO_00088_dedAdd_neg em hγ, (TA_PRO_00086_dedZero_neutral hα).1]

theorem TA_PRO_00101_dedLE_translate (em : ∀ p : Prop, p ∨ ¬p)
    {α β γ : ZFSet.{u}} (hα : α ∈ dedekindCutsTA)
    (hβ : β ∈ dedekindCutsTA) (hγ : γ ∈ dedekindCutsTA) :
    DedLE α β ↔ DedLE (dedAdd α γ) (dedAdd β γ) := by
  constructor
  · intro h
    exact ⟨TA_PRO_00084_dedAdd_mem em hα hγ,
      TA_PRO_00084_dedAdd_mem em hβ hγ, dedAdd_mono_right h.2.2⟩
  · intro h
    have hs := dedAdd_mono_right (γ := dedNeg γ) h.2.2
    rw [dedAdd_translate_restore em hα hγ, dedAdd_translate_restore em hβ hγ] at hs
    exact ⟨hα, hβ, hs⟩

theorem TA_PRO_00101_dedLT_translate (em : ∀ p : Prop, p ∨ ¬p)
    {α β γ : ZFSet.{u}} (hα : α ∈ dedekindCutsTA)
    (hβ : β ∈ dedekindCutsTA) (hγ : γ ∈ dedekindCutsTA) :
    DedLT α β ↔ DedLT (dedAdd α γ) (dedAdd β γ) := by
  constructor
  · intro h
    exact ⟨(TA_PRO_00101_dedLE_translate em hα hβ hγ).mp h.1,
      fun he => h.2 (TA_PRO_00089_dedAdd_cancel_right em hα hβ hγ he)⟩
  · intro h
    refine ⟨(TA_PRO_00101_dedLE_translate em hα hβ hγ).mpr h.1, ?_⟩
    intro he
    exact h.2 (congrArg (fun z => dedAdd z γ) he)

theorem TA_PRO_00101_translation_package (em : ∀ p : Prop, p ∨ ¬p)
    {α β γ : ZFSet.{u}} (hα : α ∈ dedekindCutsTA)
    (hβ : β ∈ dedekindCutsTA) (hγ : γ ∈ dedekindCutsTA) :
    (DedLE α β ↔ DedLE (dedAdd α γ) (dedAdd β γ)) ∧
    (DedLT α β ↔ DedLT (dedAdd α γ) (dedAdd β γ)) :=
  ⟨TA_PRO_00101_dedLE_translate em hα hβ hγ,
    TA_PRO_00101_dedLT_translate em hα hβ hγ⟩

theorem TA_COR_00022_difference_positive_iff (em : ∀ p : Prop, p ∨ ¬p)
    {α β : ZFSet.{u}} (hα : α ∈ dedekindCutsTA) (hβ : β ∈ dedekindCutsTA) :
    DedLT α β ↔ DedLT dedZero (dedSub β α) := by
  have h := TA_PRO_00101_dedLT_translate em hα hβ (TA_PRO_00087_dedNeg_mem em hα)
  rw [TA_PRO_00088_dedAdd_neg em hα] at h
  exact h


end TratadoAnalisis.Dedekind.TranslationOrder
