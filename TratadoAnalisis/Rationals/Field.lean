import TratadoAnalisis.Rationals.Algebra

namespace TratadoAnalisis.Rationals.Field

open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Integers.Construction
open TratadoAnalisis.Integers.Operations
open TratadoAnalisis.Integers.Multiplication
open TratadoAnalisis.Integers.Algebra
open TratadoAnalisis.Rationals.IntegerPrep
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.Algebra

theorem TA_PRO_00061_ratClass_eq_zero_iff
    {a b : ZFSet}
    (ha : a ∈ integersTA) (hb : b ∈ intNonzeroTA) :
    ratClass (ZFSet.pair a b) = ratZero ↔ a = intZero := by
  change ratClass (ZFSet.pair a b) =
    ratClass (ZFSet.pair intZero intOne) ↔ a = intZero
  rw [TA_PRO_00053_ratClass_pairs_eq_iff ha hb
    intZero_mem_integersTA intOne_mem_intNonzeroTA]
  constructor
  · rintro ⟨u, v, hu, hv, huv⟩
    exact (intMul_one_right ha hu).symm.trans
      (huv.trans (intMul_zero_right (mem_intNonzeroTA_iff.mp hb).1 hv))
  · intro ha0
    rcases intMul_exists ha intOne_mem_integersTA with ⟨u, _, hu⟩
    rcases intMul_exists (mem_intNonzeroTA_iff.mp hb).1
      intZero_mem_integersTA with ⟨v, _, hv⟩
    exact ⟨u, v, hu, hv, (intMul_one_right ha hu).trans
      (ha0.trans (intMul_zero_right (mem_intNonzeroTA_iff.mp hb).1 hv).symm)⟩

theorem TA_PRO_00061_ratClass_ne_zero_iff
    {a b : ZFSet} (ha : a ∈ integersTA) (hb : b ∈ intNonzeroTA) :
    ratClass (ZFSet.pair a b) ≠ ratZero ↔ a ≠ intZero := by
  exact not_congr (TA_PRO_00061_ratClass_eq_zero_iff ha hb)

def ratNonzeroTA : ZFSet :=
  ZFSet.sep
    (fun q => q ≠ ratZero)
    rationalsTA

theorem mem_ratNonzeroTA_iff {q : ZFSet} :
    q ∈ ratNonzeroTA ↔ q ∈ rationalsTA ∧ q ≠ ratZero := by
  exact ZFSet.mem_sep

theorem exists_nonzero_ratClass_pair_of_mem
    {q : ZFSet} (hq : q ∈ ratNonzeroTA) :
    ∃ a b : ZFSet, a ∈ intNonzeroTA ∧ b ∈ intNonzeroTA ∧
      q = ratClass (ZFSet.pair a b) := by
  rcases mem_ratNonzeroTA_iff.mp hq with ⟨hq, hq0⟩
  rcases exists_ratClass_pair_of_mem hq with ⟨a, b, ha, hb, rfl⟩
  exact ⟨a, b, mem_intNonzeroTA_iff.mpr
    ⟨ha, (TA_PRO_00061_ratClass_ne_zero_iff ha hb).mp hq0⟩, hb, rfl⟩

def ratRepInv (p r : ZFSet) : Prop :=
  ∃ a b : ZFSet,
    a ∈ intNonzeroTA ∧ b ∈ intNonzeroTA ∧
    p = ZFSet.pair a b ∧ r = ZFSet.pair b a

theorem ratRepInv_exists_unique
    {p : ZFSet}
    (hp : ∃ a b : ZFSet, a ∈ intNonzeroTA ∧ b ∈ intNonzeroTA ∧
      p = ZFSet.pair a b) :
    ∃! r : ZFSet, r ∈ ratDomain ∧ ratRepInv p r := by
  rcases hp with ⟨a, b, ha, hb, rfl⟩
  refine ⟨ZFSet.pair b a, ⟨mem_ratDomain_iff.mpr
    ⟨b, a, (mem_intNonzeroTA_iff.mp hb).1, ha, rfl⟩,
    a, b, ha, hb, rfl, rfl⟩, ?_⟩
  intro r hr
  rcases hr.2 with ⟨c, d, _, _, hp, hr⟩
  rcases ZFSet.pair_injective hp with ⟨hac, hbd⟩
  subst c
  subst d
  exact hr

theorem TA_PRO_00062_ratRepInv_well_defined
    {p q ip iq : ZFSet}
    (hpq : ratRel p q) (hip : ratRepInv p ip) (hiq : ratRepInv q iq) :
    ratRel ip iq := by
  rcases hip with ⟨a, b, ha, hb, rfl, rfl⟩
  rcases hiq with ⟨c, d, hc, hd, rfl, rfl⟩
  apply (ratRel_pairs_iff (mem_intNonzeroTA_iff.mp hb).1 ha
    (mem_intNonzeroTA_iff.mp hd).1 hc).mpr
  exact intProductEq_symm ((ratRel_pairs_iff
    (mem_intNonzeroTA_iff.mp ha).1 hb (mem_intNonzeroTA_iff.mp hc).1 hd).mp hpq)

def RatInvValue (x y : ZFSet) : Prop :=
  ∃ p r : ZFSet,
    p ∈ ratDomain ∧ r ∈ ratDomain ∧
    x = ratClass p ∧ y = ratClass r ∧ ratRepInv p r

theorem ratClass_swapped_mem_ratNonzeroTA
    {a b : ZFSet} (ha : a ∈ intNonzeroTA) (hb : b ∈ intNonzeroTA) :
    ratClass (ZFSet.pair b a) ∈ ratNonzeroTA := by
  apply mem_ratNonzeroTA_iff.mpr
  exact ⟨ratClass_mem_rationalsTA (mem_ratDomain_iff.mpr
    ⟨b, a, (mem_intNonzeroTA_iff.mp hb).1, ha, rfl⟩),
    (TA_PRO_00061_ratClass_ne_zero_iff (mem_intNonzeroTA_iff.mp hb).1 ha).mpr
      (mem_intNonzeroTA_iff.mp hb).2⟩

def ratInvGraph : ZFSet :=
  ZFSet.sep
    (fun t =>
      ∃ x y : ZFSet,
        x ∈ ratNonzeroTA ∧ y ∈ ratNonzeroTA ∧
        t = ZFSet.pair x y ∧ RatInvValue x y)
    (pairAmbient ratNonzeroTA ratNonzeroTA)

theorem mem_ratInvGraph {x y : ZFSet} :
    ZFSet.pair x y ∈ ratInvGraph ↔
    x ∈ ratNonzeroTA ∧ y ∈ ratNonzeroTA ∧ RatInvValue x y := by
  constructor
  · intro h
    rcases (ZFSet.mem_sep.mp h).2 with ⟨x', y', hx, hy, hp, hv⟩
    rcases ZFSet.pair_injective hp with ⟨hxx, hyy⟩
    subst x'
    subst y'
    exact ⟨hx, hy, hv⟩
  · rintro ⟨hx, hy, hv⟩
    exact ZFSet.mem_sep.mpr
      ⟨pair_mem_pairAmbient hx hy, x, y, hx, hy, rfl, hv⟩

theorem ratInvGraph_isFunc :
    IsFuncFoundational ratNonzeroTA ratNonzeroTA ratInvGraph := by
  constructor
  · intro t ht
    rcases (ZFSet.mem_sep.mp ht).2 with ⟨x, y, hx, hy, rfl, _⟩
    exact ⟨x, hx, y, hy, rfl⟩
  · intro x hx
    rcases exists_nonzero_ratClass_pair_of_mem hx with ⟨a, b, ha, hb, hxClass⟩
    have hp : ZFSet.pair a b ∈ ratDomain := mem_ratDomain_iff.mpr
      ⟨a, b, (mem_intNonzeroTA_iff.mp ha).1, hb, rfl⟩
    have hr : ZFSet.pair b a ∈ ratDomain := mem_ratDomain_iff.mpr
      ⟨b, a, (mem_intNonzeroTA_iff.mp hb).1, ha, rfl⟩
    have hy := ratClass_swapped_mem_ratNonzeroTA ha hb
    have hi : ratRepInv (ZFSet.pair a b) (ZFSet.pair b a) :=
      ⟨a, b, ha, hb, rfl, rfl⟩
    refine ⟨ratClass (ZFSet.pair b a), ⟨hy, mem_ratInvGraph.mpr
      ⟨hx, hy, ZFSet.pair a b, ZFSet.pair b a, hp, hr, hxClass, rfl, hi⟩⟩, ?_⟩
    intro y' hy'
    rcases (mem_ratInvGraph.mp hy'.2).2.2 with ⟨p', r', hp', hr', hx', hy', hi'⟩
    have hRel := (TA_PRO_00053_ratClass_eq_iff hp hp').mp (hxClass.symm.trans hx')
    have hInvRel := TA_PRO_00062_ratRepInv_well_defined hRel hi hi'
    exact hy'.trans ((TA_PRO_00053_ratClass_eq_iff hr hr').mpr hInvRel).symm

def RatInv (x y : ZFSet) : Prop :=
  ZFSet.pair x y ∈ ratInvGraph

theorem RatInv_unique {x y₁ y₂ : ZFSet}
    (hx : x ∈ ratNonzeroTA) (h₁ : RatInv x y₁) (h₂ : RatInv x y₂) : y₁ = y₂ := by
  rcases ratInvGraph_isFunc.2 x hx with ⟨y, _, hUnique⟩
  exact (hUnique y₁ ⟨funcFoundational_value_mem ratInvGraph_isFunc h₁, h₁⟩).trans
    (hUnique y₂ ⟨funcFoundational_value_mem ratInvGraph_isFunc h₂, h₂⟩).symm

theorem ratInvGraph_classes
    {a b : ZFSet} (ha : a ∈ intNonzeroTA) (hb : b ∈ intNonzeroTA) :
    ZFSet.pair (ratClass (ZFSet.pair a b))
      (ratClass (ZFSet.pair b a)) ∈ ratInvGraph := by
  apply mem_ratInvGraph.mpr
  exact ⟨ratClass_swapped_mem_ratNonzeroTA hb ha,
    ratClass_swapped_mem_ratNonzeroTA ha hb,
    ZFSet.pair a b, ZFSet.pair b a,
    mem_ratDomain_iff.mpr ⟨a, b, (mem_intNonzeroTA_iff.mp ha).1, hb, rfl⟩,
    mem_ratDomain_iff.mpr ⟨b, a, (mem_intNonzeroTA_iff.mp hb).1, ha, rfl⟩,
    rfl, rfl, a, b, ha, hb, rfl, rfl⟩

theorem ratInvGraph_classes_value_iff
    {a b y : ZFSet} (ha : a ∈ intNonzeroTA) (hb : b ∈ intNonzeroTA) :
    ZFSet.pair (ratClass (ZFSet.pair a b)) y ∈ ratInvGraph ↔
      y = ratClass (ZFSet.pair b a) := by
  constructor
  · intro h
    exact RatInv_unique (ratClass_swapped_mem_ratNonzeroTA hb ha) h
      (ratInvGraph_classes ha hb)
  · rintro rfl
    exact ratInvGraph_classes ha hb

theorem TA_PRO_00063_inverse_law
    {q qi : ZFSet} (hq : q ∈ ratNonzeroTA) (hInv : RatInv q qi) :
    RatMul q qi ratOne ∧ RatMul qi q ratOne := by
  have hqi := (mem_ratNonzeroTA_iff.mp
    (funcFoundational_value_mem ratInvGraph_isFunc hInv)).1
  have hqM := (mem_ratNonzeroTA_iff.mp hq).1
  have hLeft : RatMul q qi ratOne := by
    rcases exists_nonzero_ratClass_pair_of_mem hq with ⟨a, b, ha, hb, rfl⟩
    have hqiEq := (ratInvGraph_classes_value_iff ha hb).mp hInv
    rw [hqiEq]
    have haM := (mem_intNonzeroTA_iff.mp ha).1
    have hbM := (mem_intNonzeroTA_iff.mp hb).1
    rcases intMul_exists haM hbM with ⟨ab, habM, hab⟩
    rcases intMul_exists hbM haM with ⟨ba, hbaM, hba⟩
    have hbaNZ := intNonzero_mul_closed hb ha hba
    have hClass : ratClass (ZFSet.pair ab ba) = ratOne := by
      apply (TA_PRO_00053_ratClass_pairs_eq_iff habM hbaNZ
        intOne_mem_integersTA intOne_mem_intNonzeroTA).mpr
      rcases intMul_exists habM intOne_mem_integersTA with ⟨u, _, hu⟩
      rcases intMul_exists hbaM intOne_mem_integersTA with ⟨v, _, hv⟩
      exact ⟨u, v, hu, hv, (intMul_one_right habM hu).trans
        ((intMul_comm haM hbM hab hba).trans (intMul_one_right hbaM hv).symm)⟩
    have hFormula := ratMulGraph_classes haM hb hbM ha hab hba
    rw [hClass] at hFormula
    exact hFormula
  refine ⟨hLeft, ?_⟩
  rcases ratMul_exists hqi hqM with ⟨z, _, hz⟩
  have hzOne : ratOne = z := ratMul_comm hqM hqi hLeft hz
  rw [← hzOne] at hz
  exact hz

theorem exists_inverse_of_mem_ratNonzeroTA
    {q : ZFSet} (hq : q ∈ ratNonzeroTA) :
    ∃ qi : ZFSet, qi ∈ ratNonzeroTA ∧ RatInv q qi ∧
      RatMul q qi ratOne ∧ RatMul qi q ratOne := by
  rcases ratInvGraph_isFunc.2 q hq with ⟨qi, hqi, _⟩
  exact ⟨qi, hqi.1, hqi.2, TA_PRO_00063_inverse_law hq hqi.2⟩

theorem TA_THM_00028_field_package :
    ((∀ {x y z xy lhs yz rhs : ZFSet},
      x ∈ rationalsTA → y ∈ rationalsTA → z ∈ rationalsTA →
      RatAdd x y xy → RatAdd xy z lhs → RatAdd y z yz →
      RatAdd x yz rhs → lhs = rhs) ∧
    (∀ {x y xy yx : ZFSet}, x ∈ rationalsTA → y ∈ rationalsTA →
      RatAdd x y xy → RatAdd y x yx → xy = yx) ∧
    (∀ {x z : ZFSet}, x ∈ rationalsTA → RatAdd ratZero x z → z = x) ∧
    (∀ {x z : ZFSet}, x ∈ rationalsTA → RatAdd x ratZero z → z = x) ∧
    (∀ {x nx z : ZFSet}, x ∈ rationalsTA → RatNeg x nx →
      RatAdd nx x z → z = ratZero) ∧
    (∀ {x nx z : ZFSet}, x ∈ rationalsTA → RatNeg x nx →
      RatAdd x nx z → z = ratZero)) ∧
    ((∀ {x y z xy lhs yz rhs : ZFSet},
      x ∈ rationalsTA → y ∈ rationalsTA → z ∈ rationalsTA →
      RatMul x y xy → RatMul xy z lhs → RatMul y z yz →
      RatMul x yz rhs → lhs = rhs) ∧
    (∀ {x y xy yx : ZFSet}, x ∈ rationalsTA → y ∈ rationalsTA →
      RatMul x y xy → RatMul y x yx → xy = yx) ∧
    (∀ {x z : ZFSet}, x ∈ rationalsTA → RatMul ratOne x z → z = x) ∧
    (∀ {x z : ZFSet}, x ∈ rationalsTA → RatMul x ratOne z → z = x) ∧
    (∀ {x y z yz lhs xy xz rhs : ZFSet},
      x ∈ rationalsTA → y ∈ rationalsTA → z ∈ rationalsTA →
      RatAdd y z yz → RatMul x yz lhs → RatMul x y xy →
      RatMul x z xz → RatAdd xy xz rhs → lhs = rhs) ∧
    (∀ {x y z xy lhs xz yz rhs : ZFSet},
      x ∈ rationalsTA → y ∈ rationalsTA → z ∈ rationalsTA →
      RatAdd x y xy → RatMul xy z lhs → RatMul x z xz →
      RatMul y z yz → RatAdd xz yz rhs → lhs = rhs)) ∧
    ratZero ≠ ratOne ∧
    (∀ q : ZFSet, q ∈ ratNonzeroTA →
      ∃ qi : ZFSet, qi ∈ ratNonzeroTA ∧
        RatMul q qi ratOne ∧ RatMul qi q ratOne) := by
  refine ⟨TA_PRO_00056_additive_group_laws, TA_PRO_00058_mul_distrib_laws,
    TA_PRO_00059_ratZero_ne_one, ?_⟩
  intro q hq
  rcases exists_inverse_of_mem_ratNonzeroTA hq with ⟨qi, hqi, _, hLeft, hRight⟩
  exact ⟨qi, hqi, hLeft, hRight⟩

end TratadoAnalisis.Rationals.Field
