import TratadoAnalisis.Dedekind.PositiveInverseLaw

namespace TratadoAnalisis.Dedekind.Inverse
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

open TratadoAnalisis.Dedekind.Nonzero
open TratadoAnalisis.Dedekind.PositiveInverse
open TratadoAnalisis.Dedekind.PositiveInverseLaw

/-- TA-DEF-00102: unión proposicional de las dos ramas, sin decidir el signo. -/
def dedSignedInv (α : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun r =>
    (IsPositiveCut α ∧ r ∈ dedPositiveInv α) ∨
    (IsNegativeCut α ∧ r ∈ dedNeg (dedPositiveInv (dedNeg α)))) rationalsTA

theorem TA_DEF_00102_mem_dedSignedInv_iff {α r : ZFSet.{u}} :
    r ∈ dedSignedInv α ↔ r ∈ rationalsTA ∧
      ((IsPositiveCut α ∧ r ∈ dedPositiveInv α) ∨
      (IsNegativeCut α ∧ r ∈ dedNeg (dedPositiveInv (dedNeg α)))) := ZFSet.mem_sep

theorem signedInv_subset_rationals (α : ZFSet.{u}) :
    dedSignedInv α ⊆ rationalsTA :=
  fun _ h => (TA_DEF_00102_mem_dedSignedInv_iff.mp h).1

theorem TA_DEF_00102_of_positive {α : ZFSet.{u}} (hp : IsPositiveCut α) :
    dedSignedInv α = dedPositiveInv α := by
  apply ZFSet.ext
  intro r
  rw [TA_DEF_00102_mem_dedSignedInv_iff]
  simp only [hp, cut_positive_not_negative hp, true_and, false_and, or_false]
  exact rational_guard_iff (positiveInv_subset_rationals α)

theorem TA_DEF_00102_of_negative {α : ZFSet.{u}} (hn : IsNegativeCut α) :
    dedSignedInv α = dedNeg (dedPositiveInv (dedNeg α)) := by
  apply ZFSet.ext
  intro r
  rw [TA_DEF_00102_mem_dedSignedInv_iff]
  simp only [hn, cut_negative_not_positive hn, true_and, false_and, false_or]
  exact rational_guard_iff (dedNeg_subset_rationals (dedPositiveInv (dedNeg α)))

theorem signedInv_positive (em : ∀ p : Prop, p ∨ ¬p)
    {α : ZFSet.{u}} (hp : IsPositiveCut α) : IsPositiveCut (dedSignedInv α) := by
  rw [TA_DEF_00102_of_positive hp]
  exact TA_DEF_00091_mem_positiveCuts_iff.mp
    (TA_PRO_00098_positiveInv_mem em (TA_DEF_00091_mem_positiveCuts_iff.mpr hp))

theorem signedInv_negative (em : ∀ p : Prop, p ∨ ¬p)
    {α : ZFSet.{u}} (hn : IsNegativeCut α) : IsNegativeCut (dedSignedInv α) := by
  rw [TA_DEF_00102_of_negative hn]
  have p := negative_implies_positive_neg em hn.1.1 hn
  have pi := TA_DEF_00091_mem_positiveCuts_iff.mp
    (TA_PRO_00098_positiveInv_mem em (TA_DEF_00091_mem_positiveCuts_iff.mpr p))
  exact positive_implies_negative_neg em pi.1.2.1 pi

theorem TA_PRO_00100_signedInv_mem (em : ∀ p : Prop, p ∨ ¬p)
    {α : ZFSet.{u}} (hα : α ∈ nonzeroCutsTA) : dedSignedInv α ∈ nonzeroCutsTA := by
  rcases TA_DEF_00101_mem_nonzeroCuts_iff.mp hα with ⟨hαD, hα0⟩
  apply TA_DEF_00101_mem_nonzeroCuts_iff.mpr
  rcases TA_PRO_00093_zero_sign_trichotomy em hαD with hn | he | hp
  · have h := signedInv_negative em hn
    exact ⟨h.1.1, cut_negative_ne_zero h⟩
  · exact (hα0 he).elim
  · have h := signedInv_positive em hp
    exact ⟨h.1.2.1, cut_positive_ne_zero h⟩

theorem TA_PRO_00100_sign_package (em : ∀ p : Prop, p ∨ ¬p)
    {α : ZFSet.{u}} (hα : α ∈ nonzeroCutsTA) :
    dedSignedInv α ∈ nonzeroCutsTA ∧
      (IsPositiveCut α → IsPositiveCut (dedSignedInv α)) ∧
      (IsNegativeCut α → IsNegativeCut (dedSignedInv α)) :=
  ⟨TA_PRO_00100_signedInv_mem em hα, signedInv_positive em, signedInv_negative em⟩

/-- TA-DEF-00103: valor sin decisión; el dominio del grafo excluye cero. -/
def dedInvValue (α : ZFSet.{u}) : ZFSet.{u} := dedSignedInv α

theorem TA_DEF_00103_dedInvValue_eq {α : ZFSet.{u}} :
    dedInvValue α = dedSignedInv α := rfl

def dedInvGraph : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ α β : ZFSet.{u},
    z = ZFSet.pair α β ∧ β = dedInvValue α)
    (cartesianProductFoundational nonzeroCutsTA nonzeroCutsTA)

theorem mem_dedInvGraph_iff {α β : ZFSet.{u}} :
    ZFSet.pair α β ∈ dedInvGraph ↔
      α ∈ nonzeroCutsTA ∧ β ∈ nonzeroCutsTA ∧ β = dedInvValue α := by
  constructor
  · intro h
    rcases ZFSet.mem_sep.mp h with ⟨hp, a, b, he, hb⟩
    rcases ZFSet.pair_injective he with ⟨rfl, rfl⟩
    exact ⟨(mem_cartesianProductFoundational.mp hp).1,
      (mem_cartesianProductFoundational.mp hp).2, hb⟩
  · rintro ⟨ha, hb, he⟩
    exact ZFSet.mem_sep.mpr
      ⟨mem_cartesianProductFoundational.mpr ⟨ha, hb⟩, α, β, rfl, he⟩

theorem TA_DEF_00103_dedInvGraph_isFunc (em : ∀ p : Prop, p ∨ ¬p) :
    IsFuncFoundational (nonzeroCutsTA : ZFSet.{u}) nonzeroCutsTA dedInvGraph := by
  constructor
  · intro z hz
    rcases (ZFSet.mem_sep.mp hz).2 with ⟨a, b, he, _⟩
    rw [he] at hz
    rcases mem_dedInvGraph_iff.mp hz with ⟨ha, hb, _⟩
    exact ⟨a, ha, b, hb, he⟩
  · intro a ha
    have hc := TA_PRO_00100_signedInv_mem em ha
    refine ⟨dedInvValue a, ⟨hc, mem_dedInvGraph_iff.mpr ⟨ha, hc, rfl⟩⟩, ?_⟩
    intro b hb
    exact (mem_dedInvGraph_iff.mp hb.2).2.2

def dedInvFunction : ZFSet.{u} := functionTriple nonzeroCutsTA nonzeroCutsTA dedInvGraph

theorem TA_DEF_00103_dedInvFunction_isTriple (em : ∀ p : Prop, p ∨ ¬p) :
    IsFunctionTriple (nonzeroCutsTA : ZFSet.{u}) nonzeroCutsTA dedInvFunction :=
  TA_DEF_00018_functionTriple_iff.mpr (TA_DEF_00103_dedInvGraph_isFunc em)

/-- TA-THM-00046: reducción a la ley positiva, sin leyes de cuerpo posteriores. -/
theorem TA_THM_00046_inverse_law (em : ∀ p : Prop, p ∨ ¬p)
    {α : ZFSet.{u}} (hα : α ∈ nonzeroCutsTA) :
    dedMul α (dedInvValue α) = dedOne ∧ dedMul (dedInvValue α) α = dedOne := by
  rcases TA_DEF_00101_mem_nonzeroCuts_iff.mp hα with ⟨hαD, hα0⟩
  change dedSignedMul α (dedSignedInv α) = dedOne ∧
    dedSignedMul (dedSignedInv α) α = dedOne
  rcases TA_PRO_00093_zero_sign_trichotomy em hαD with hn | he | hp
  · have hjn := signedInv_negative em hn
    have pn := negative_implies_positive_neg em hαD hn
    have pi := TA_DEF_00091_mem_positiveCuts_iff.mp
      (TA_PRO_00098_positiveInv_mem em (TA_DEF_00091_mem_positiveCuts_iff.mpr pn))
    rw [TA_DEF_00096_of_neg_neg hn hjn, TA_DEF_00096_of_neg_neg hjn hn,
      TA_DEF_00102_of_negative hn, TA_LEM_00025_dedNeg_involutive em pi.1.2.1]
    exact TA_THM_00045_positive_inverse_law em pn
  · exact (hα0 he).elim
  · have hjp := signedInv_positive em hp
    rw [TA_DEF_00096_of_pos_pos hp hjp, TA_DEF_00096_of_pos_pos hjp hp,
      TA_DEF_00102_of_positive hp]
    exact TA_THM_00045_positive_inverse_law em hp


end TratadoAnalisis.Dedekind.Inverse
