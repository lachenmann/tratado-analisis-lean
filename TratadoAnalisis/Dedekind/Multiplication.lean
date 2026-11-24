import TratadoAnalisis.Dedekind.Signs
import TratadoAnalisis.Dedekind.PositiveMultiplication

namespace TratadoAnalisis.Dedekind.Multiplication
universe u
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.Trichotomy
open TratadoAnalisis.Rationals.StrictOrder
open TratadoAnalisis.Rationals.Signs
open TratadoAnalisis.Rationals.PositiveProducts
open TratadoAnalisis.Dedekind.Definition
open TratadoAnalisis.Dedekind.Order
open TratadoAnalisis.Dedekind.RationalSection
open TratadoAnalisis.Dedekind.Embedding
open TratadoAnalisis.Dedekind.Addition
open TratadoAnalisis.Dedekind.Negation
open TratadoAnalisis.Dedekind.Positivity
open TratadoAnalisis.Dedekind.Signs
open TratadoAnalisis.Dedekind.PositiveMultiplication
open TratadoAnalisis.Foundations.FunctionTriple

/-- TA-DEF-00096: un único Sep con las cinco ramas del manuscrito. -/
def dedSignedMul (α β : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun r =>
    ((α = dedZero ∨ β = dedZero) ∧ r ∈ dedZero) ∨
    (IsPositiveCut α ∧ IsPositiveCut β ∧ r ∈ dedPositiveMul α β) ∨
    (IsNegativeCut α ∧ IsNegativeCut β ∧ r ∈ dedPositiveMul (dedNeg α) (dedNeg β)) ∨
    (IsPositiveCut α ∧ IsNegativeCut β ∧ r ∈ dedNeg (dedPositiveMul α (dedNeg β))) ∨
    (IsNegativeCut α ∧ IsPositiveCut β ∧ r ∈ dedNeg (dedPositiveMul (dedNeg α) β)))
    rationalsTA

theorem TA_DEF_00096_mem_dedSignedMul_iff {α β r : ZFSet.{u}} :
    r ∈ dedSignedMul α β ↔ r ∈ rationalsTA ∧
      (((α = dedZero ∨ β = dedZero) ∧ r ∈ dedZero) ∨
      (IsPositiveCut α ∧ IsPositiveCut β ∧ r ∈ dedPositiveMul α β) ∨
      (IsNegativeCut α ∧ IsNegativeCut β ∧ r ∈ dedPositiveMul (dedNeg α) (dedNeg β)) ∨
      (IsPositiveCut α ∧ IsNegativeCut β ∧ r ∈ dedNeg (dedPositiveMul α (dedNeg β))) ∨
      (IsNegativeCut α ∧ IsPositiveCut β ∧ r ∈ dedNeg (dedPositiveMul (dedNeg α) β))) :=
  ZFSet.mem_sep

theorem dedSignedMul_subset_rationals (α β : ZFSet.{u}) :
    dedSignedMul α β ⊆ rationalsTA :=
  fun _ h => (TA_DEF_00096_mem_dedSignedMul_iff.mp h).1

theorem cut_positive_ne_zero {α : ZFSet.{u}} (h : IsPositiveCut α) :
    α ≠ dedZero := fun he => h.2 he.symm

theorem cut_negative_ne_zero {α : ZFSet.{u}} (h : IsNegativeCut α) :
    α ≠ dedZero := h.2

theorem cut_positive_not_negative {α : ZFSet.{u}} (h : IsPositiveCut α) :
    ¬ IsNegativeCut α :=
  fun hn => TA_PRO_00093_zero_signs_exclusive.2.1 ⟨hn, h⟩

theorem cut_negative_not_positive {α : ZFSet.{u}} (h : IsNegativeCut α) :
    ¬ IsPositiveCut α :=
  fun hp => TA_PRO_00093_zero_signs_exclusive.2.1 ⟨h, hp⟩

theorem zero_not_positive : ¬ IsPositiveCut (dedZero : ZFSet.{u}) :=
  fun h => h.2 rfl

theorem zero_not_negative : ¬ IsNegativeCut (dedZero : ZFSet.{u}) :=
  fun h => h.2 rfl

theorem dedZero_subset_rationals : (dedZero : ZFSet.{u}) ⊆ rationalsTA :=
  (TA_PRO_00079_mem_dedekindCuts_iff.mp dedZero_mem).1

theorem rational_guard_iff {A r : ZFSet.{u}} (hA : A ⊆ rationalsTA) :
    (r ∈ rationalsTA ∧ r ∈ A) ↔ r ∈ A :=
  ⟨And.right, fun h => ⟨hA h, h⟩⟩

theorem TA_DEF_00096_zero_left {β : ZFSet.{u}} :
    dedSignedMul dedZero β = dedZero := by
  apply ZFSet.ext
  intro r
  constructor
  · intro hr
    rcases (TA_DEF_00096_mem_dedSignedMul_iff.mp hr).2 with h | h | h | h | h
    · exact h.2
    · exact (zero_not_positive h.1).elim
    · exact (zero_not_negative h.1).elim
    · exact (zero_not_positive h.1).elim
    · exact (zero_not_negative h.1).elim
  · intro hr
    exact TA_DEF_00096_mem_dedSignedMul_iff.mpr
      ⟨dedZero_subset_rationals hr, Or.inl ⟨Or.inl rfl, hr⟩⟩

theorem TA_DEF_00096_zero_right {α : ZFSet.{u}} :
    dedSignedMul α dedZero = dedZero := by
  apply ZFSet.ext
  intro r
  constructor
  · intro hr
    rcases (TA_DEF_00096_mem_dedSignedMul_iff.mp hr).2 with h | h | h | h | h
    · exact h.2
    · exact (zero_not_positive h.2.1).elim
    · exact (zero_not_negative h.2.1).elim
    · exact (zero_not_negative h.2.1).elim
    · exact (zero_not_positive h.2.1).elim
  · intro hr
    exact TA_DEF_00096_mem_dedSignedMul_iff.mpr
      ⟨dedZero_subset_rationals hr, Or.inl ⟨Or.inr rfl, hr⟩⟩

/-- Primera rama, incluidos los dos ceros simultáneos. -/
theorem TA_DEF_00096_of_zero {α β : ZFSet.{u}}
    (h : α = dedZero ∨ β = dedZero) : dedSignedMul α β = dedZero := by
  rcases h with rfl | rfl
  · exact TA_DEF_00096_zero_left
  · exact TA_DEF_00096_zero_right

theorem TA_DEF_00096_of_pos_pos {α β : ZFSet.{u}}
    (hα : IsPositiveCut α) (hβ : IsPositiveCut β) :
    dedSignedMul α β = dedPositiveMul α β := by
  apply ZFSet.ext
  intro r
  rw [TA_DEF_00096_mem_dedSignedMul_iff]
  simp only [hα, hβ, cut_positive_ne_zero hα, cut_positive_ne_zero hβ,
    cut_positive_not_negative hα, cut_positive_not_negative hβ,
    false_or, or_false, true_and, false_and, and_false]
  exact rational_guard_iff (dedPositiveMul_subset_rationals α β)

theorem TA_DEF_00096_of_neg_neg {α β : ZFSet.{u}}
    (hα : IsNegativeCut α) (hβ : IsNegativeCut β) :
    dedSignedMul α β = dedPositiveMul (dedNeg α) (dedNeg β) := by
  apply ZFSet.ext
  intro r
  rw [TA_DEF_00096_mem_dedSignedMul_iff]
  simp only [hα, hβ, cut_negative_ne_zero hα, cut_negative_ne_zero hβ,
    cut_negative_not_positive hα, cut_negative_not_positive hβ,
    false_or, or_false, true_and, false_and, and_false]
  exact rational_guard_iff (dedPositiveMul_subset_rationals (dedNeg α) (dedNeg β))

theorem TA_DEF_00096_of_pos_neg {α β : ZFSet.{u}}
    (hα : IsPositiveCut α) (hβ : IsNegativeCut β) :
    dedSignedMul α β = dedNeg (dedPositiveMul α (dedNeg β)) := by
  apply ZFSet.ext
  intro r
  rw [TA_DEF_00096_mem_dedSignedMul_iff]
  simp only [hα, hβ, cut_positive_ne_zero hα, cut_negative_ne_zero hβ,
    cut_positive_not_negative hα, cut_negative_not_positive hβ,
    false_or, or_false, true_and, false_and, and_false]
  exact rational_guard_iff (dedNeg_subset_rationals (dedPositiveMul α (dedNeg β)))

theorem TA_DEF_00096_of_neg_pos {α β : ZFSet.{u}}
    (hα : IsNegativeCut α) (hβ : IsPositiveCut β) :
    dedSignedMul α β = dedNeg (dedPositiveMul (dedNeg α) β) := by
  apply ZFSet.ext
  intro r
  rw [TA_DEF_00096_mem_dedSignedMul_iff]
  simp only [hα, hβ, cut_negative_ne_zero hα, cut_positive_ne_zero hβ,
    cut_negative_not_positive hα, cut_positive_not_negative hβ,
    false_or, or_false, true_and, false_and, and_false]
  exact rational_guard_iff (dedNeg_subset_rationals (dedPositiveMul (dedNeg α) β))

theorem signedMul_positive_of_pos_pos (em : ∀ p : Prop, p ∨ ¬p)
    {α β : ZFSet.{u}} (hα : IsPositiveCut α) (hβ : IsPositiveCut β) :
    IsPositiveCut (dedSignedMul α β) := by
  rw [TA_DEF_00096_of_pos_pos hα hβ]
  exact TA_DEF_00091_mem_positiveCuts_iff.mp (TA_PRO_00090_positiveMul_mem em
    (TA_DEF_00091_mem_positiveCuts_iff.mpr hα) (TA_DEF_00091_mem_positiveCuts_iff.mpr hβ))

theorem signedMul_positive_of_neg_neg (em : ∀ p : Prop, p ∨ ¬p)
    {α β : ZFSet.{u}} (hα : IsNegativeCut α) (hβ : IsNegativeCut β) :
    IsPositiveCut (dedSignedMul α β) := by
  rw [TA_DEF_00096_of_neg_neg hα hβ]
  exact TA_DEF_00091_mem_positiveCuts_iff.mp (TA_PRO_00090_positiveMul_mem em
    (TA_DEF_00091_mem_positiveCuts_iff.mpr (negative_implies_positive_neg em hα.1.1 hα))
    (TA_DEF_00091_mem_positiveCuts_iff.mpr (negative_implies_positive_neg em hβ.1.1 hβ)))

theorem signedMul_negative_of_pos_neg (em : ∀ p : Prop, p ∨ ¬p)
    {α β : ZFSet.{u}} (hα : IsPositiveCut α) (hβ : IsNegativeCut β) :
    IsNegativeCut (dedSignedMul α β) := by
  rw [TA_DEF_00096_of_pos_neg hα hβ]
  have hp := TA_DEF_00091_mem_positiveCuts_iff.mp (TA_PRO_00090_positiveMul_mem em
    (TA_DEF_00091_mem_positiveCuts_iff.mpr hα)
    (TA_DEF_00091_mem_positiveCuts_iff.mpr (negative_implies_positive_neg em hβ.1.1 hβ)))
  exact positive_implies_negative_neg em hp.1.2.1 hp

theorem signedMul_negative_of_neg_pos (em : ∀ p : Prop, p ∨ ¬p)
    {α β : ZFSet.{u}} (hα : IsNegativeCut α) (hβ : IsPositiveCut β) :
    IsNegativeCut (dedSignedMul α β) := by
  rw [TA_DEF_00096_of_neg_pos hα hβ]
  have hp := TA_DEF_00091_mem_positiveCuts_iff.mp (TA_PRO_00090_positiveMul_mem em
    (TA_DEF_00091_mem_positiveCuts_iff.mpr (negative_implies_positive_neg em hα.1.1 hα))
    (TA_DEF_00091_mem_positiveCuts_iff.mpr hβ))
  exact positive_implies_negative_neg em hp.1.2.1 hp

theorem TA_PRO_00094_dedSignedMul_mem (em : ∀ p : Prop, p ∨ ¬p)
    {α β : ZFSet.{u}} (hα : α ∈ dedekindCutsTA) (hβ : β ∈ dedekindCutsTA) :
    dedSignedMul α β ∈ dedekindCutsTA := by
  rcases TA_PRO_00093_zero_sign_trichotomy em hα with hnα | heα | hpα
  · rcases TA_PRO_00093_zero_sign_trichotomy em hβ with hnβ | heβ | hpβ
    · exact (signedMul_positive_of_neg_neg em hnα hnβ).1.2.1
    · rw [heβ, TA_DEF_00096_zero_right]
      exact dedZero_mem
    · exact (signedMul_negative_of_neg_pos em hnα hpβ).1.1
  · rw [heα, TA_DEF_00096_zero_left]
    exact dedZero_mem
  · rcases TA_PRO_00093_zero_sign_trichotomy em hβ with hnβ | heβ | hpβ
    · exact (signedMul_negative_of_pos_neg em hpα hnβ).1.1
    · rw [heβ, TA_DEF_00096_zero_right]
      exact dedZero_mem
    · exact (signedMul_positive_of_pos_pos em hpα hpβ).1.2.1

theorem TA_PRO_00094_closure_sign_package (em : ∀ p : Prop, p ∨ ¬p)
    {α β : ZFSet.{u}} (hα : α ∈ dedekindCutsTA) (hβ : β ∈ dedekindCutsTA) :
    dedSignedMul α β ∈ dedekindCutsTA ∧
    ((α = dedZero ∨ β = dedZero) → dedSignedMul α β = dedZero) ∧
    (((IsPositiveCut α ∧ IsPositiveCut β) ∨ (IsNegativeCut α ∧ IsNegativeCut β)) →
      IsPositiveCut (dedSignedMul α β)) ∧
    (((IsPositiveCut α ∧ IsNegativeCut β) ∨ (IsNegativeCut α ∧ IsPositiveCut β)) →
      IsNegativeCut (dedSignedMul α β)) := by
  refine ⟨TA_PRO_00094_dedSignedMul_mem em hα hβ, TA_DEF_00096_of_zero, ?_, ?_⟩
  · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
    · exact signedMul_positive_of_pos_pos em ha hb
    · exact signedMul_positive_of_neg_neg em ha hb
  · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
    · exact signedMul_negative_of_pos_neg em ha hb
    · exact signedMul_negative_of_neg_pos em ha hb

/-- TA-DEF-00097: el mismo valor, acompañado por grafo y triple. -/
def dedMul (α β : ZFSet.{u}) : ZFSet.{u} := dedSignedMul α β

theorem TA_DEF_00097_dedMul_eq {α β : ZFSet.{u}} :
    dedMul α β = dedSignedMul α β := rfl

def dedMulGraph : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ α β γ : ZFSet.{u},
    z = ZFSet.pair (ZFSet.pair α β) γ ∧ γ = dedMul α β)
    (cartesianProductFoundational
      (cartesianProductFoundational dedekindCutsTA dedekindCutsTA) dedekindCutsTA)

theorem mem_dedMulGraph_iff {α β γ : ZFSet.{u}} :
    ZFSet.pair (ZFSet.pair α β) γ ∈ dedMulGraph ↔
      α ∈ dedekindCutsTA ∧ β ∈ dedekindCutsTA ∧
      γ ∈ dedekindCutsTA ∧ γ = dedMul α β := by
  constructor
  · intro h
    rcases ZFSet.mem_sep.mp h with ⟨hp, a, b, c, he, hc⟩
    have hcoords := ZFSet.pair_injective he
    rcases ZFSet.pair_injective hcoords.1 with ⟨rfl, rfl⟩
    rcases hcoords.2 with rfl
    rcases mem_cartesianProductFoundational.mp hp with ⟨hab, hcD⟩
    exact ⟨(mem_cartesianProductFoundational.mp hab).1,
      (mem_cartesianProductFoundational.mp hab).2, hcD, hc⟩
  · rintro ⟨ha, hb, hc, he⟩
    exact ZFSet.mem_sep.mpr
      ⟨mem_cartesianProductFoundational.mpr
        ⟨mem_cartesianProductFoundational.mpr ⟨ha, hb⟩, hc⟩, α, β, γ, rfl, he⟩

theorem TA_DEF_00097_dedMulGraph_isFunc (em : ∀ p : Prop, p ∨ ¬p) :
    IsFuncFoundational
      (cartesianProductFoundational (dedekindCutsTA : ZFSet.{u}) dedekindCutsTA)
      dedekindCutsTA dedMulGraph := by
  constructor
  · intro z hz
    rcases (ZFSet.mem_sep.mp hz).2 with ⟨a, b, c, he, _⟩
    rw [he] at hz
    rcases mem_dedMulGraph_iff.mp hz with ⟨ha, hb, hc, _⟩
    exact ⟨ZFSet.pair a b, mem_cartesianProductFoundational.mpr ⟨ha, hb⟩, c, hc, he⟩
  · intro z hz
    rcases (ZFSet.mem_sep.mp hz).2 with ⟨a, ha, b, hb, he⟩
    subst z
    have hc : dedMul a b ∈ dedekindCutsTA := TA_PRO_00094_dedSignedMul_mem em ha hb
    refine ⟨dedMul a b, ⟨hc, mem_dedMulGraph_iff.mpr ⟨ha, hb, hc, rfl⟩⟩, ?_⟩
    intro c hc'
    exact (mem_dedMulGraph_iff.mp hc'.2).2.2.2

def dedMulFunction : ZFSet.{u} :=
  functionTriple (cartesianProductFoundational dedekindCutsTA dedekindCutsTA)
    dedekindCutsTA dedMulGraph

theorem TA_DEF_00097_dedMulFunction_isTriple (em : ∀ p : Prop, p ∨ ¬p) :
    IsFunctionTriple
      (cartesianProductFoundational (dedekindCutsTA : ZFSet.{u}) dedekindCutsTA)
      dedekindCutsTA dedMulFunction :=
  TA_DEF_00018_functionTriple_iff.mpr (TA_DEF_00097_dedMulGraph_isFunc em)

/-- Signo de una sección racional, obtenido sin tricotomía de cortaduras. -/
theorem section_positive_of_rational {p : ZFSet.{u}}
    (hp : p ∈ rationalsTA) (h0p : RatLT ratZero p) :
    IsPositiveCut (rationalSection p) :=
  TA_DEF_00091_mem_positiveCuts_iff.mp (TA_PRO_00091_rationalSection_positive hp h0p)

theorem section_negative_of_rational {p : ZFSet.{u}}
    (hp : p ∈ rationalsTA) (hp0 : RatLT p ratZero) :
    IsNegativeCut (rationalSection p) :=
  (TA_COR_00016_ratLT_iff_sections_dedLT hp ratZero_mem_rationalsTA).mp hp0

theorem section_mul_zero_left {q pq : ZFSet.{u}}
    (hq : q ∈ rationalsTA) (hpq : RatMul ratZero q pq) :
    rationalSection pq = dedSignedMul dedZero (rationalSection q) := by
  have he := RatMul_unique ratZero_mem_rationalsTA hq hpq (ratMul_zero_left hq)
  exact (congrArg rationalSection he).trans TA_DEF_00096_zero_left.symm

theorem section_mul_zero_right {p pq : ZFSet.{u}}
    (hp : p ∈ rationalsTA) (hpq : RatMul p ratZero pq) :
    rationalSection pq = dedSignedMul (rationalSection p) dedZero := by
  have he := RatMul_unique hp ratZero_mem_rationalsTA hpq (ratMul_zero_right hp)
  exact (congrArg rationalSection he).trans TA_DEF_00096_zero_right.symm

theorem section_mul_of_neg_neg {p q pq : ZFSet.{u}}
    (hp : p ∈ rationalsTA) (hq : q ∈ rationalsTA)
    (hp0 : RatLT p ratZero) (hq0 : RatLT q ratZero) (hpq : RatMul p q pq) :
    rationalSection pq = dedSignedMul (rationalSection p) (rationalSection q) := by
  rcases ratNeg_exists hp with ⟨np, hnpQ, hnp⟩
  rcases ratNeg_exists hq with ⟨nq, hnqQ, hnq⟩
  rcases ratMul_exists hnpQ hnqQ with ⟨nn, _, hnn⟩
  have he := ratMul_neg_neg_general hp hq hnp hnq hpq hnn
  calc
    rationalSection pq = dedPositiveMul (rationalSection np) (rationalSection nq) := by
      rw [← he]
      exact TA_PRO_00092_rationalSection_positiveMul hnpQ hnqQ
        ((ratNeg_positive_iff hp hnp).mpr hp0)
        ((ratNeg_positive_iff hq hnq).mpr hq0) hnn
    _ = dedPositiveMul (dedNeg (rationalSection p)) (dedNeg (rationalSection q)) := by
      rw [TA_COR_00019_rationalSection_neg hp hnp, TA_COR_00019_rationalSection_neg hq hnq]
    _ = dedSignedMul (rationalSection p) (rationalSection q) :=
      (TA_DEF_00096_of_neg_neg (section_negative_of_rational hp hp0)
        (section_negative_of_rational hq hq0)).symm

theorem section_mul_of_pos_neg {p q pq : ZFSet.{u}}
    (hp : p ∈ rationalsTA) (hq : q ∈ rationalsTA)
    (h0p : RatLT ratZero p) (hq0 : RatLT q ratZero) (hpq : RatMul p q pq) :
    rationalSection pq = dedSignedMul (rationalSection p) (rationalSection q) := by
  rcases ratNeg_exists hq with ⟨nq, hnqQ, hnq⟩
  rcases ratMul_exists hp hnqQ with ⟨pnq, hpnqQ, hpnq⟩
  have hnprod := ratMul_neg_right_rel hp hq hnq hpq hpnq
  calc
    rationalSection pq = dedNeg (rationalSection pnq) :=
      (TA_COR_00019_rationalSection_neg hpnqQ
        (ratNeg_symm_rel (ratMul_value_mem hpq) hnprod)).symm
    _ = dedNeg (dedPositiveMul (rationalSection p) (rationalSection nq)) :=
      congrArg dedNeg (TA_PRO_00092_rationalSection_positiveMul hp hnqQ h0p
        ((ratNeg_positive_iff hq hnq).mpr hq0) hpnq)
    _ = dedNeg (dedPositiveMul (rationalSection p) (dedNeg (rationalSection q))) := by
      rw [TA_COR_00019_rationalSection_neg hq hnq]
    _ = dedSignedMul (rationalSection p) (rationalSection q) :=
      (TA_DEF_00096_of_pos_neg (section_positive_of_rational hp h0p)
        (section_negative_of_rational hq hq0)).symm

theorem section_mul_of_neg_pos {p q pq : ZFSet.{u}}
    (hp : p ∈ rationalsTA) (hq : q ∈ rationalsTA)
    (hp0 : RatLT p ratZero) (h0q : RatLT ratZero q) (hpq : RatMul p q pq) :
    rationalSection pq = dedSignedMul (rationalSection p) (rationalSection q) := by
  rcases ratNeg_exists hp with ⟨np, hnpQ, hnp⟩
  rcases ratMul_exists hnpQ hq with ⟨npq, hnpqQ, hnpq⟩
  have hnprod := ratMul_neg_left_rel hp hq hnp hpq hnpq
  calc
    rationalSection pq = dedNeg (rationalSection npq) :=
      (TA_COR_00019_rationalSection_neg hnpqQ
        (ratNeg_symm_rel (ratMul_value_mem hpq) hnprod)).symm
    _ = dedNeg (dedPositiveMul (rationalSection np) (rationalSection q)) :=
      congrArg dedNeg (TA_PRO_00092_rationalSection_positiveMul hnpQ hq
        ((ratNeg_positive_iff hp hnp).mpr hp0) h0q hnpq)
    _ = dedNeg (dedPositiveMul (dedNeg (rationalSection p)) (rationalSection q)) := by
      rw [TA_COR_00019_rationalSection_neg hp hnp]
    _ = dedSignedMul (rationalSection p) (rationalSection q) :=
      (TA_DEF_00096_of_neg_pos (section_negative_of_rational hp hp0)
        (section_positive_of_rational hq h0q)).symm

/-- TA-PRO-00095: casos de signos racionales, sin em para cortaduras. -/
theorem TA_PRO_00095_rationalSection_mul {p q pq : ZFSet.{u}}
    (hp : p ∈ rationalsTA) (hq : q ∈ rationalsTA) (hpq : RatMul p q pq) :
    rationalSection pq = dedMul (rationalSection p) (rationalSection q) := by
  change rationalSection pq = dedSignedMul (rationalSection p) (rationalSection q)
  rcases TA_PRO_00172_rational_trichotomy hp ratZero_mem_rationalsTA with hp0 | he | h0p
  · rcases TA_PRO_00172_rational_trichotomy hq ratZero_mem_rationalsTA with hq0 | he | h0q
    · exact section_mul_of_neg_neg hp hq hp0 hq0 hpq
    · subst q
      exact section_mul_zero_right hp hpq
    · exact section_mul_of_neg_pos hp hq hp0 h0q hpq
  · subst p
    exact section_mul_zero_left hq hpq
  · rcases TA_PRO_00172_rational_trichotomy hq ratZero_mem_rationalsTA with hq0 | he | h0q
    · exact section_mul_of_pos_neg hp hq h0p hq0 hpq
    · subst q
      exact section_mul_zero_right hp hpq
    · exact (TA_PRO_00092_rationalSection_positiveMul hp hq h0p h0q hpq).trans
        (TA_DEF_00096_of_pos_pos (section_positive_of_rational hp h0p)
          (section_positive_of_rational hq h0q)).symm

end TratadoAnalisis.Dedekind.Multiplication
