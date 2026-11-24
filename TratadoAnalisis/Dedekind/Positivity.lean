import TratadoAnalisis.Dedekind.Addition
import TratadoAnalisis.Rationals.PositiveProducts

namespace TratadoAnalisis.Dedekind.Positivity
universe u
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.Trichotomy
open TratadoAnalisis.Rationals.NoSupremumSqrtTwo
open TratadoAnalisis.Dedekind.Definition
open TratadoAnalisis.Dedekind.Order
open TratadoAnalisis.Dedekind.RationalSection
open TratadoAnalisis.Dedekind.Addition

/-- TA-DEF-00091: la positividad estricta original, no habitabilidad. -/
def IsPositiveCut (α : ZFSet.{u}) : Prop := DedLT dedZero α

def positiveCutsTA : ZFSet.{u} := ZFSet.sep IsPositiveCut dedekindCutsTA

theorem TA_DEF_00091_isPositiveCut_iff {α : ZFSet.{u}} :
    IsPositiveCut α ↔ DedLT dedZero α := Iff.rfl

theorem TA_DEF_00091_mem_positiveCuts_iff {α : ZFSet.{u}} :
    α ∈ positiveCutsTA ↔ IsPositiveCut α := by
  constructor
  · intro h
    exact (ZFSet.mem_sep.mp h).2
  · intro h
    exact ZFSet.mem_sep.mpr ⟨h.1.2.1, h⟩

/-- TA-DEF-00095. -/
def IsNegativeCut (α : ZFSet.{u}) : Prop := DedLT α dedZero

def negativeCutsTA : ZFSet.{u} := ZFSet.sep IsNegativeCut dedekindCutsTA

theorem TA_DEF_00095_isNegativeCut_iff {α : ZFSet.{u}} :
    IsNegativeCut α ↔ DedLT α dedZero := Iff.rfl

theorem TA_DEF_00095_mem_negativeCuts_iff {α : ZFSet.{u}} :
    α ∈ negativeCutsTA ↔ IsNegativeCut α := by
  constructor
  · intro h
    exact (ZFSet.mem_sep.mp h).2
  · intro h
    exact ZFSet.mem_sep.mpr ⟨h.1.1, h⟩

/-- TA-DEF-00092. -/
def positivePart (α : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun a => RatLT ratZero a) α

theorem TA_DEF_00092_mem_positivePart_iff {α a : ZFSet.{u}} :
    a ∈ positivePart α ↔ a ∈ α ∧ RatLT ratZero a := ZFSet.mem_sep

/-- TA-DEF-00093: candidato total como conjunto, sin selección de testigos. -/
def dedPositiveMul (α β : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun r => ∃ a : ZFSet.{u}, a ∈ positivePart α ∧
    ∃ b : ZFSet.{u}, b ∈ positivePart β ∧
      ∃ p : ZFSet.{u}, RatMul a b p ∧ RatLT r p) rationalsTA

theorem TA_DEF_00093_mem_positiveMul_iff {α β r : ZFSet.{u}} :
    r ∈ dedPositiveMul α β ↔ r ∈ rationalsTA ∧
      ∃ a : ZFSet.{u}, a ∈ positivePart α ∧
        ∃ b : ZFSet.{u}, b ∈ positivePart β ∧
          ∃ p : ZFSet.{u}, RatMul a b p ∧ RatLT r p := ZFSet.mem_sep

theorem dedPositiveMul_subset_rationals (α β : ZFSet.{u}) :
    dedPositiveMul α β ⊆ rationalsTA :=
  fun _ h => (TA_DEF_00093_mem_positiveMul_iff.mp h).1

theorem mem_positiveMul_of_witness {α β a b p r : ZFSet.{u}}
    (hr : r ∈ rationalsTA) (ha : a ∈ α) (h0a : RatLT ratZero a)
    (hb : b ∈ β) (h0b : RatLT ratZero b)
    (hab : RatMul a b p) (hrp : RatLT r p) : r ∈ dedPositiveMul α β :=
  TA_DEF_00093_mem_positiveMul_iff.mpr
    ⟨hr, a, TA_DEF_00092_mem_positivePart_iff.mpr ⟨ha, h0a⟩,
      b, TA_DEF_00092_mem_positivePart_iff.mpr ⟨hb, h0b⟩, p, hab, hrp⟩

/-- (2) iff (3), sin em. -/
theorem TA_LEM_00023_zero_mem_iff_positive_member {α : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) :
    (ratZero : ZFSet.{u}) ∈ α ↔
      ∃ a : ZFSet.{u}, a ∈ α ∧ RatLT ratZero a := by
  have ca := TA_PRO_00079_mem_dedekindCuts_iff.mp hα
  constructor
  · intro h0
    exact ca.2.2.2.2 ratZero h0
  · rintro ⟨a, ha, h0a⟩
    exact ca.2.2.2.1 a ha ratZero ratZero_mem_rationalsTA h0a

/-- (2) implies (1), sin em. -/
theorem TA_LEM_00023_zero_mem_implies_positive {α : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) (h0 : (ratZero : ZFSet.{u}) ∈ α) :
    IsPositiveCut α := by
  have ca := TA_PRO_00079_mem_dedekindCuts_iff.mp hα
  refine ⟨⟨dedZero_mem, hα, ?_⟩, ?_⟩
  · intro r hr
    have hm := TA_DEF_00081_mem_rationalSection_iff.mp hr
    exact ca.2.2.2.1 ratZero h0 r hm.1 hm.2
  · intro he
    have hz : (ratZero : ZFSet.{u}) ∈ dedZero := he.symm ▸ h0
    exact rationalSection_self_not_mem ratZero hz

/-- (3) implies (1), sin em. -/
theorem TA_LEM_00023_positive_member_implies_positive {α a : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) (ha : a ∈ α) (h0a : RatLT ratZero a) :
    IsPositiveCut α :=
  TA_LEM_00023_zero_mem_implies_positive hα
    ((TA_LEM_00023_zero_mem_iff_positive_member hα).mpr ⟨a, ha, h0a⟩)

/-- (1) implies (2): sólo la extracción del testigo recibe em. -/
theorem TA_LEM_00023_positive_implies_zero_mem
    (em : ∀ p : Prop, p ∨ ¬p) {α : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) (hpos : IsPositiveCut α) :
    (ratZero : ZFSet.{u}) ∈ α := by
  have ca := TA_PRO_00079_mem_dedekindCuts_iff.mp hα
  have hnback : ¬ α ⊆ dedZero := by
    intro hback
    exact hpos.2 (TA_THM_00001_zfset_eq_iff_subset.mpr ⟨hpos.1.2.2, hback⟩)
  rcases subset_failure_witness em hnback with ⟨x, hx, hxOut⟩
  rcases TA_PRO_00172_rational_trichotomy (ca.1 hx) ratZero_mem_rationalsTA
    with hx0 | he | h0x
  · exact (hxOut (TA_DEF_00081_mem_rationalSection_iff.mpr ⟨ca.1 hx, hx0⟩)).elim
  · exact he ▸ hx
  · exact ca.2.2.2.1 x hx ratZero ratZero_mem_rationalsTA h0x

theorem TA_LEM_00023_positive_iff_zero_mem
    (em : ∀ p : Prop, p ∨ ¬p) {α : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) :
    IsPositiveCut α ↔ (ratZero : ZFSet.{u}) ∈ α :=
  ⟨TA_LEM_00023_positive_implies_zero_mem em hα,
    TA_LEM_00023_zero_mem_implies_positive hα⟩

/-- Paquete de las tres caracterizaciones del manuscrito. -/
theorem TA_LEM_00023_characterizations
    (em : ∀ p : Prop, p ∨ ¬p) {α : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) :
    (IsPositiveCut α ↔ (ratZero : ZFSet.{u}) ∈ α) ∧
    ((ratZero : ZFSet.{u}) ∈ α ↔
      ∃ a : ZFSet.{u}, a ∈ α ∧ RatLT ratZero a) ∧
    (IsPositiveCut α ↔
      ∃ a : ZFSet.{u}, a ∈ α ∧ RatLT ratZero a) :=
  ⟨TA_LEM_00023_positive_iff_zero_mem em hα,
    TA_LEM_00023_zero_mem_iff_positive_member hα,
    (TA_LEM_00023_positive_iff_zero_mem em hα).trans
      (TA_LEM_00023_zero_mem_iff_positive_member hα)⟩

/-- Sólo exclusión; la exhaustividad de TA-PRO-00093 corresponde a D. -/
theorem TA_PRO_00093_zero_signs_pairwise_incompatible {α : ZFSet.{u}} :
    ¬ (IsNegativeCut α ∧ α = dedZero) ∧
    ¬ (IsNegativeCut α ∧ IsPositiveCut α) ∧
    ¬ (α = (dedZero : ZFSet.{u}) ∧ IsPositiveCut α) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hn, he⟩
    exact hn.2 he
  · rintro ⟨hn, hp⟩
    exact hn.2 (dedLE_antisymm hn.1 hp.1)
  · rintro ⟨he, hp⟩
    exact hp.2 he.symm

end TratadoAnalisis.Dedekind.Positivity
