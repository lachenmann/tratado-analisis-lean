import TratadoAnalisis.Dedekind.Positivity
import TratadoAnalisis.Dedekind.Negation

namespace TratadoAnalisis.Dedekind.Signs
universe u
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.Signs
open TratadoAnalisis.Rationals.PositiveProducts
open TratadoAnalisis.Rationals.NoSupremumSqrtTwo
open TratadoAnalisis.Dedekind.Definition
open TratadoAnalisis.Dedekind.Order
open TratadoAnalisis.Dedekind.RationalSection
open TratadoAnalisis.Dedekind.Addition
open TratadoAnalisis.Dedekind.Negation
open TratadoAnalisis.Dedekind.Positivity

/-- TA-PRO-00093: sólo la exhaustividad recibe em. -/
theorem TA_PRO_00093_zero_sign_trichotomy
    (em : ∀ p : Prop, p ∨ ¬p) {α : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) :
    IsNegativeCut α ∨ α = dedZero ∨ IsPositiveCut α := by
  rcases em (α = dedZero) with he | hne
  · exact Or.inr (Or.inl he)
  · rcases TA_THM_00040_dedLE_total em hα dedZero_mem with hn | hp
    · exact Or.inl ⟨hn, hne⟩
    · exact Or.inr (Or.inr ⟨hp, fun he => hne he.symm⟩)

/-- La exclusión ya certificada en B se expone separada de la exhaustividad. -/
theorem TA_PRO_00093_zero_signs_exclusive {α : ZFSet.{u}} :
    ¬ (IsNegativeCut α ∧ α = dedZero) ∧
    ¬ (IsNegativeCut α ∧ IsPositiveCut α) ∧
    ¬ (α = (dedZero : ZFSet.{u}) ∧ IsPositiveCut α) :=
  TA_PRO_00093_zero_signs_pairwise_incompatible

theorem TA_PRO_00093_zero_sign_package
    (em : ∀ p : Prop, p ∨ ¬p) {α : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) :
    (IsNegativeCut α ∨ α = dedZero ∨ IsPositiveCut α) ∧
    ¬ (IsNegativeCut α ∧ α = dedZero) ∧
    ¬ (IsNegativeCut α ∧ IsPositiveCut α) ∧
    ¬ (α = (dedZero : ZFSet.{u}) ∧ IsPositiveCut α) :=
  ⟨TA_PRO_00093_zero_sign_trichotomy em hα, TA_PRO_00093_zero_signs_exclusive⟩

/-- Fragmento constructivo de TA-LEM-00024, por TA-COR-00019. -/
theorem TA_LEM_00024_dedNeg_zero :
    dedNeg (dedZero : ZFSet.{u}) = dedZero :=
  TA_COR_00019_rationalSection_neg ratZero_mem_rationalsTA zero_neg_rel

theorem negative_implies_positive_neg
    (em : ∀ p : Prop, p ∨ ¬p) {α : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) (hn : IsNegativeCut α) :
    IsPositiveCut (dedNeg α) := by
  have hnsub : ¬ (dedZero : ZFSet.{u}) ⊆ α := by
    intro hback
    exact hn.2 (TA_THM_00001_zfset_eq_iff_subset.mpr ⟨hn.1.2.2, hback⟩)
  rcases subset_failure_witness em hnsub with ⟨s, hs, hsOut⟩
  rcases TA_DEF_00081_mem_rationalSection_iff.mp hs with ⟨hsQ, hs0⟩
  rcases ratNeg_exists hsQ with ⟨ns, _, hns⟩
  have h0ns := (ratNeg_positive_iff hsQ hns).mpr hs0
  have h0 : (ratZero : ZFSet.{u}) ∈ dedNeg α :=
    TA_DEF_00088_mem_dedNeg_iff.mpr
      ⟨ratZero_mem_rationalsTA, s, hsQ, hsOut, ns, hns, h0ns⟩
  exact TA_LEM_00023_zero_mem_implies_positive (TA_PRO_00087_dedNeg_mem em hα) h0

theorem positive_implies_negative_neg
    (em : ∀ p : Prop, p ∨ ¬p) {α : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) (hp : IsPositiveCut α) :
    IsNegativeCut (dedNeg α) := by
  have ca := TA_PRO_00079_mem_dedekindCuts_iff.mp hα
  have h0 := TA_LEM_00023_positive_implies_zero_mem em hα hp
  rcases (TA_LEM_00023_zero_mem_iff_positive_member hα).mp h0 with ⟨a, ha, h0a⟩
  rcases ratNeg_exists (ca.1 ha) with ⟨na, hnaQ, hna⟩
  have hna0 := (ratNeg_negative_iff (ca.1 ha) hna).mpr h0a
  have hnaZero : na ∈ (dedZero : ZFSet.{u}) :=
    TA_DEF_00081_mem_rationalSection_iff.mpr ⟨hnaQ, hna0⟩
  refine ⟨⟨TA_PRO_00087_dedNeg_mem em hα, dedZero_mem, ?_⟩, ?_⟩
  · intro r hr
    rcases TA_DEF_00088_mem_dedNeg_iff.mp hr with ⟨hrQ, s, hs, hsOut, ns, hns, hrns⟩
    have h0s := cut_member_lt_nonmember ca hs hsOut h0
    have hns0 := (ratNeg_negative_iff hs hns).mpr h0s
    exact TA_DEF_00081_mem_rationalSection_iff.mpr
      ⟨hrQ, ratLT_of_lt_of_le_local hrQ
        (funcFoundational_value_mem ratNegGraph_isFunc hns)
        ratZero_mem_rationalsTA hrns hns0.1⟩
  · intro he
    have hnaNeg : na ∈ dedNeg α := he.symm ▸ hnaZero
    rcases TA_DEF_00088_mem_dedNeg_iff.mp hnaNeg with ⟨_, s, hs, hsOut, ns, hns, hlt⟩
    have hsa := (TA_LEM_00020_clause2_neg_lt_iff hs (ca.1 ha) hns hna).mpr hlt
    exact hsOut (ca.2.2.2.1 a ha s hs hsa)

/-- Recíproca por tricotomía, sin invocar la involución posterior. -/
theorem TA_LEM_00024_negative_iff_positive_neg
    (em : ∀ p : Prop, p ∨ ¬p) {α : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) :
    IsNegativeCut α ↔ IsPositiveCut (dedNeg α) := by
  constructor
  · exact negative_implies_positive_neg em hα
  · intro hpNeg
    rcases TA_PRO_00093_zero_sign_trichotomy em hα with hn | he | hp
    · exact hn
    · rw [he, TA_LEM_00024_dedNeg_zero] at hpNeg
      exact (hpNeg.2 rfl).elim
    · exact ((TA_PRO_00093_zero_signs_exclusive).2.1
        ⟨positive_implies_negative_neg em hα hp, hpNeg⟩).elim

theorem TA_LEM_00024_positive_iff_negative_neg
    (em : ∀ p : Prop, p ∨ ¬p) {α : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) :
    IsPositiveCut α ↔ IsNegativeCut (dedNeg α) := by
  constructor
  · exact positive_implies_negative_neg em hα
  · intro hnNeg
    rcases TA_PRO_00093_zero_sign_trichotomy em hα with hn | he | hp
    · exact ((TA_PRO_00093_zero_signs_exclusive).2.1
        ⟨hnNeg, negative_implies_positive_neg em hα hn⟩).elim
    · rw [he, TA_LEM_00024_dedNeg_zero] at hnNeg
      exact (hnNeg.2 rfl).elim
    · exact hp

theorem TA_LEM_00024_sign_negation_package
    (em : ∀ p : Prop, p ∨ ¬p) {α : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) :
    (IsNegativeCut α ↔ IsPositiveCut (dedNeg α)) ∧
    (IsPositiveCut α ↔ IsNegativeCut (dedNeg α)) ∧
    dedNeg (dedZero : ZFSet.{u}) = dedZero :=
  ⟨TA_LEM_00024_negative_iff_positive_neg em hα,
    TA_LEM_00024_positive_iff_negative_neg em hα, TA_LEM_00024_dedNeg_zero⟩

end TratadoAnalisis.Dedekind.Signs
