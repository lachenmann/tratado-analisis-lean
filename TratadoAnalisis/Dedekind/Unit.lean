import TratadoAnalisis.Dedekind.Multiplication
import TratadoAnalisis.Dedekind.AdditiveGroup

namespace TratadoAnalisis.Dedekind.Unit
universe u
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.Field
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.Trichotomy
open TratadoAnalisis.Rationals.OrderedFieldCompatibility
open TratadoAnalisis.Rationals.StrictOrder
open TratadoAnalisis.Rationals.SquareMonotonicity
open TratadoAnalisis.Rationals.NoSupremumSqrtTwo
open TratadoAnalisis.Rationals.Signs
open TratadoAnalisis.Rationals.Division
open TratadoAnalisis.Rationals.PositiveProducts
open TratadoAnalisis.Dedekind.Definition
open TratadoAnalisis.Dedekind.Order
open TratadoAnalisis.Dedekind.RationalSection
open TratadoAnalisis.Dedekind.Embedding
open TratadoAnalisis.Dedekind.Addition
open TratadoAnalisis.Dedekind.Negation
open TratadoAnalisis.Dedekind.AdditiveGroup
open TratadoAnalisis.Dedekind.Positivity
open TratadoAnalisis.Dedekind.PositiveMultiplication
open TratadoAnalisis.Dedekind.Signs
open TratadoAnalisis.Dedekind.Multiplication

/-- TA-DEF-00098: la sección de uno, sin decisión del signo. -/
def dedOne : ZFSet.{u} := rationalSection ratOne

theorem TA_DEF_00098_dedOne_eq :
    (dedOne : ZFSet.{u}) = rationalSection ratOne := rfl

theorem dedOne_mem : (dedOne : ZFSet.{u}) ∈ dedekindCutsTA :=
  TA_PRO_00080_rationalSection_mem ratOne_mem_rationalsTA

/-- TA-PRO-00096: preservación del orden estricto, sin em. -/
theorem TA_PRO_00096_dedOne_positive : IsPositiveCut (dedOne : ZFSet.{u}) :=
  (TA_COR_00016_ratLT_iff_sections_dedLT ratZero_mem_rationalsTA
    ratOne_mem_rationalsTA).mp TA_LEM_00020_clause3_zero_lt_one

theorem TA_PRO_00096_zero_ne_one : (dedZero : ZFSet.{u}) ≠ dedOne :=
  TA_PRO_00096_dedOne_positive.2

theorem TA_PRO_00096_one_mem_positiveCuts :
    (dedOne : ZFSet.{u}) ∈ positiveCutsTA :=
  TA_DEF_00091_mem_positiveCuts_iff.mpr TA_PRO_00096_dedOne_positive

/-- TA-LEM-00025: unicidad del inverso por cancelación aditiva. -/
theorem TA_LEM_00025_dedNeg_involutive
    (em : ∀ p : Prop, p ∨ ¬p) {α : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) : dedNeg (dedNeg α) = α := by
  have hn := TA_PRO_00087_dedNeg_mem em hα
  have hnn := TA_PRO_00087_dedNeg_mem em hn
  exact TA_PRO_00089_dedAdd_cancel_right em hnn hα hn
    ((TA_COR_00020_dedAdd_neg_bilateral em hn).2.trans
      (TA_COR_00020_dedAdd_neg_bilateral em hα).1.symm)

/-- Primera inclusión de TA-PRO-00097, independiente de la positividad estricta. -/
theorem positiveMul_one_subset {α : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) : dedPositiveMul α dedOne ⊆ α := by
  have ca := TA_PRO_00079_mem_dedekindCuts_iff.mp hα
  intro x hx
  rcases TA_DEF_00093_mem_positiveMul_iff.mp hx with ⟨hxQ, a, ha, b, hb, p, hab, hxp⟩
  rcases TA_DEF_00092_mem_positivePart_iff.mp ha with ⟨ha, h0a⟩
  rcases TA_DEF_00092_mem_positivePart_iff.mp hb with ⟨hb, _⟩
  rcases TA_DEF_00081_mem_rationalSection_iff.mp hb with ⟨hbQ, hb1⟩
  have haQ := ca.1 ha
  have hpa := ratLT_mul_positive_left_local hbQ ratOne_mem_rationalsTA haQ
    hb1 h0a hab (ratMul_comm_rel ratOne_mem_rationalsTA haQ (ratMul_one_left_rel haQ))
  exact ca.2.2.2.1 a ha x hxQ
    (ratLT_of_lt_of_le_local hxQ (ratMul_value_mem hab) haQ hxp hpa.1)

theorem one_positiveMul_subset {α : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) : dedPositiveMul dedOne α ⊆ α := by
  have ca := TA_PRO_00079_mem_dedekindCuts_iff.mp hα
  intro x hx
  rcases TA_DEF_00093_mem_positiveMul_iff.mp hx with ⟨hxQ, b, hb, a, ha, p, hba, hxp⟩
  rcases TA_DEF_00092_mem_positivePart_iff.mp ha with ⟨ha, h0a⟩
  rcases TA_DEF_00092_mem_positivePart_iff.mp hb with ⟨hb, _⟩
  rcases TA_DEF_00081_mem_rationalSection_iff.mp hb with ⟨hbQ, hb1⟩
  have haQ := ca.1 ha
  have hpa := ratLT_mul_positive_right hbQ ratOne_mem_rationalsTA haQ
    hb1 h0a hba (ratMul_one_left_rel haQ)
  exact ca.2.2.2.1 a ha x hxQ
    (ratLT_of_lt_of_le_local hxQ (ratMul_value_mem hba) haQ hxp hpa.1)

/-- Testigos locales: la única hipótesis de positividad es el orden estricto. -/
theorem positive_one_witness
    (em : ∀ p : Prop, p ∨ ¬p) {α x : ZFSet.{u}}
    (hα : IsPositiveCut α) (hx : x ∈ α) :
    ∃ a b p : ZFSet.{u}, a ∈ α ∧ RatLT ratZero a ∧
      b ∈ dedOne ∧ RatLT ratZero b ∧ RatMul a b p ∧ RatLT x p := by
  have hαD := hα.1.2.1
  have ca := TA_PRO_00079_mem_dedekindCuts_iff.mp hαD
  have hxQ := ca.1 hx
  have nonpos (hx0 : RatLE x ratZero) :
      ∃ a b p : ZFSet.{u}, a ∈ α ∧ RatLT ratZero a ∧
        b ∈ dedOne ∧ RatLT ratZero b ∧ RatMul a b p ∧ RatLT x p := by
    have hzero := TA_LEM_00023_positive_implies_zero_mem em hαD hα
    rcases (TA_LEM_00023_zero_mem_iff_positive_member hαD).mp hzero with ⟨a, ha, h0a⟩
    rcases TA_THM_00030_rational_density ratZero_mem_rationalsTA
      ratOne_mem_rationalsTA TA_LEM_00020_clause3_zero_lt_one with ⟨b, hbQ, h0b, hb1⟩
    rcases ratMul_exists (ca.1 ha) hbQ with ⟨p, hpQ, hab⟩
    have h0p := TA_LEM_00020_clause5_positive_product (ca.1 ha) hbQ hab h0a h0b
    exact ⟨a, b, p, ha, h0a,
      TA_DEF_00081_mem_rationalSection_iff.mpr ⟨hbQ, hb1⟩, h0b, hab,
      ratLT_of_le_of_lt_local hxQ ratZero_mem_rationalsTA hpQ hx0 h0p⟩
  rcases TA_PRO_00172_rational_trichotomy hxQ ratZero_mem_rationalsTA with hx0 | he | h0x
  · exact nonpos hx0.1
  · apply nonpos
    rw [he]
    exact ratLE_refl ratZero_mem_rationalsTA
  · rcases ca.2.2.2.2 x hx with ⟨a, ha, hxa⟩
    have haQ := ca.1 ha
    have h0a := ratLT_of_lt_of_le_local ratZero_mem_rationalsTA hxQ haQ h0x hxa.1
    rcases ratDiv_exists hxQ (mem_ratNonzeroTA_iff.mpr ⟨haQ, fun he => h0a.2 he.symm⟩)
      with ⟨d, hdQ, hd⟩
    have h0d := ratDiv_positive hxQ haQ h0x h0a hd
    have hd1 := (ratDiv_lt_one_iff hxQ haQ h0a hd).mpr hxa
    rcases TA_THM_00030_rational_density hdQ ratOne_mem_rationalsTA hd1
      with ⟨b, hbQ, hdb, hb1⟩
    have h0b := ratLT_of_lt_of_le_local ratZero_mem_rationalsTA hdQ hbQ h0d hdb.1
    rcases ratMul_exists haQ hbQ with ⟨p, _, hab⟩
    have hxp := (ratDiv_lt_iff hxQ hbQ haQ h0a hd
      (ratMul_comm_rel haQ hbQ hab)).mp hdb
    exact ⟨a, b, p, ha, h0a,
      TA_DEF_00081_mem_rationalSection_iff.mpr ⟨hbQ, hb1⟩, h0b, hab, hxp⟩

/-- TA-PRO-00097: ambas identidades; no se añade habitabilidad como hipótesis. -/
theorem TA_PRO_00097_positiveMul_one
    (em : ∀ p : Prop, p ∨ ¬p) {α : ZFSet.{u}} (hα : IsPositiveCut α) :
    dedPositiveMul α dedOne = α ∧ dedPositiveMul dedOne α = α := by
  have hαD := hα.1.2.1
  have ca := TA_PRO_00079_mem_dedekindCuts_iff.mp hαD
  constructor
  · refine TA_THM_00001_zfset_eq_iff_subset.mpr ⟨positiveMul_one_subset hαD, ?_⟩
    intro x hx
    rcases positive_one_witness em hα hx with ⟨a, b, p, ha, h0a, hb, h0b, hab, hxp⟩
    exact mem_positiveMul_of_witness (ca.1 hx) ha h0a hb h0b hab hxp
  · refine TA_THM_00001_zfset_eq_iff_subset.mpr ⟨one_positiveMul_subset hαD, ?_⟩
    intro x hx
    rcases positive_one_witness em hα hx with ⟨a, b, p, ha, h0a, hb, h0b, hab, hxp⟩
    exact mem_positiveMul_of_witness (ca.1 hx) hb h0b ha h0a
      (ratMul_comm_rel (ca.1 ha) (TA_DEF_00081_mem_rationalSection_iff.mp hb).1 hab) hxp

/-- TA-THM-00044: casos de signo y evaluación del único constructor signado. -/
theorem TA_THM_00044_dedMul_one
    (em : ∀ p : Prop, p ∨ ¬p) {α : ZFSet.{u}} (hα : α ∈ dedekindCutsTA) :
    dedMul α dedOne = α ∧ dedMul dedOne α = α := by
  have h1 : IsPositiveCut (dedOne : ZFSet.{u}) := TA_PRO_00096_dedOne_positive
  rcases TA_PRO_00093_zero_sign_trichotomy em hα with hn | he | hp
  · have hpn := negative_implies_positive_neg em hα hn
    constructor
    · change dedSignedMul α dedOne = α
      rw [TA_DEF_00096_of_neg_pos hn h1, (TA_PRO_00097_positiveMul_one em hpn).1]
      exact TA_LEM_00025_dedNeg_involutive em hα
    · change dedSignedMul dedOne α = α
      rw [TA_DEF_00096_of_pos_neg h1 hn, (TA_PRO_00097_positiveMul_one em hpn).2]
      exact TA_LEM_00025_dedNeg_involutive em hα
  · subst α
    exact ⟨TA_DEF_00096_zero_left, TA_DEF_00096_zero_right⟩
  · exact ⟨(TA_DEF_00096_of_pos_pos hp h1).trans (TA_PRO_00097_positiveMul_one em hp).1,
      (TA_DEF_00096_of_pos_pos h1 hp).trans (TA_PRO_00097_positiveMul_one em hp).2⟩

end TratadoAnalisis.Dedekind.Unit
