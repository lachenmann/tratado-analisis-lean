import TratadoAnalisis.Rationals.AbsoluteValue
import TratadoAnalisis.Foundations.RelationalFunctions

/-!
# TA-LEAN-0011 A3 — Distancia racional (§8.2)

Se construye el grafo de d_Q(x,y)=|x-y| con codominio Q.
Las cinco propiedades y la caracterización epsilon-local se
formulan relacionalmente. Ningún resultado depende de Dedekind.
-/

namespace TratadoAnalisis.Cauchy.RationalDistance

universe u

open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Foundations.RelationalFunctions
open TratadoAnalisis.Foundations.FunctionTriple
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.NoSupremumSqrtTwo
open TratadoAnalisis.Rationals.Signs
open TratadoAnalisis.Rationals.DifferenceOrder
open TratadoAnalisis.Rationals.AbsoluteValue

theorem ratSub_value_mem {x y t : ZFSet.{u}} (h : RatSub x y t) :
    t ∈ rationalsTA := by
  obtain ⟨_, _, hs⟩ := h
  exact funcFoundational_value_mem ratAddGraph_isFunc hs

theorem ratSub_iff_add {x y t : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA) (ht : t ∈ rationalsTA) :
    RatSub x y t ↔ RatAdd t y x := by
  constructor
  · exact ratSub_add_cancel hx hy
  · intro h
    obtain ⟨s, hsQ, hs⟩ := ratSub_exists hx hy
    have e := ratAdd_cancel_right_local ht hsQ hy h (ratSub_add_cancel hx hy hs) rfl
    rw [e]
    exact hs

theorem ratSub_zero_iff {x y t : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA) (h : RatSub x y t) :
    t = ratZero ↔ x = y := by
  constructor
  · intro e
    subst t
    exact ratAdd_zero_left hy (ratSub_add_cancel hx hy h)
  · intro e
    subst y
    exact ratAdd_cancel_right_local (ratSub_value_mem h) ratZero_mem_rationalsTA hx
      (ratSub_add_cancel hx hx h) (zero_add_rel hx) rfl

theorem ratSub_reverse_neg {x y t s : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (ht : RatSub x y t) (hs : RatSub y x s) : RatNeg t s := by
  have htQ := ratSub_value_mem ht
  have hsQ := ratSub_value_mem hs
  obtain ⟨r, hrQ, hst⟩ := ratAdd_exists hsQ htQ
  obtain ⟨v, _, hv⟩ := ratAdd_exists hrQ hy
  have e := ratAdd_assoc hsQ htQ hy hst hv
    (ratSub_add_cancel hx hy ht) (ratSub_add_cancel hy hx hs)
  rw [e] at hv
  have er := ratAdd_cancel_right_local hrQ ratZero_mem_rationalsTA hy hv (zero_add_rel hy) rfl
  rw [er] at hst
  exact ratNeg_symm_rel hsQ (ratNeg_of_add_zero hsQ htQ hst)

theorem ratSub_chain_add {x y z t s w : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA) (hz : z ∈ rationalsTA)
    (ht : RatSub x y t) (hs : RatSub y z s) (hw : RatSub x z w) :
    RatAdd t s w := by
  have htQ := ratSub_value_mem ht
  have hsQ := ratSub_value_mem hs
  obtain ⟨r, hrQ, hr⟩ := ratAdd_exists htQ hsQ
  obtain ⟨v, _, hv⟩ := ratAdd_exists hrQ hz
  have e := ratAdd_assoc htQ hsQ hz hr hv
    (ratSub_add_cancel hy hz hs) (ratSub_add_cancel hx hy ht)
  rw [e] at hv
  have er := ratAdd_cancel_right_local hrQ (ratSub_value_mem hw) hz
    hv (ratSub_add_cancel hx hz hw) rfl
  rw [er] at hr
  exact hr

theorem ratSub_translate {x y z xz yz t : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA) (hz : z ∈ rationalsTA)
    (hxz : RatAdd x z xz) (hyz : RatAdd y z yz) (ht : RatSub x y t) :
    RatSub xz yz t := by
  have htQ := ratSub_value_mem ht
  have hxzQ := funcFoundational_value_mem ratAddGraph_isFunc hxz
  have hyzQ := funcFoundational_value_mem ratAddGraph_isFunc hyz
  obtain ⟨v, _, hv⟩ := ratAdd_exists htQ hyzQ
  have e := ratAdd_assoc htQ hy hz (ratSub_add_cancel hx hy ht) hxz hyz hv
  rw [← e] at hv
  exact (ratSub_iff_add hxzQ hyzQ htQ).mpr hv

/-- TA-DEF-00108: valor relacional de la distancia racional. -/
def RatDistance (x y r : ZFSet.{u}) : Prop :=
  ∃ t : ZFSet.{u}, RatSub x y t ∧ RatAbs t r

theorem distance_mem {x y r : ZFSet.{u}} (hd : RatDistance x y r) :
    r ∈ rationalsTA := by
  obtain ⟨_, _, ha⟩ := hd
  exact (ratAbs_mem ha).2

theorem distance_exists_unique {x y : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA) :
    ∃! r : ZFSet.{u}, RatDistance x y r := by
  obtain ⟨t, htQ, ht⟩ := ratSub_exists hx hy
  obtain ⟨r, ha, _⟩ := ratAbs_exists_unique htQ
  refine ⟨r, ⟨t, ht, ha⟩, ?_⟩
  intro s hs
  obtain ⟨w, hw, hb⟩ := hs
  have e := RatSub_unique hx hy hw ht
  subst w
  exact ratAbs_unique hb ha

theorem distance_unique {x y r s : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (hr : RatDistance x y r) (hs : RatDistance x y s) : r = s := by
  obtain ⟨t, ht, ha⟩ := hr
  obtain ⟨w, hw, hb⟩ := hs
  have e := RatSub_unique hx hy hw ht
  subst w
  exact ratAbs_unique ha hb

def rationalDistanceGraph : ZFSet.{u} :=
  relationGraph (cartesianProductFoundational rationalsTA rationalsTA) rationalsTA
    (fun p r => ∃ x : ZFSet.{u}, x ∈ rationalsTA ∧ ∃ y : ZFSet.{u},
      y ∈ rationalsTA ∧ p = ZFSet.pair x y ∧ RatDistance x y r)

theorem mem_rationalDistanceGraph_iff {x y r : ZFSet.{u}} :
    ZFSet.pair (ZFSet.pair x y) r ∈ rationalDistanceGraph ↔
      x ∈ rationalsTA ∧ y ∈ rationalsTA ∧ RatDistance x y r := by
  constructor
  · intro h
    obtain ⟨_, _, a, ha, b, hb, he, hd⟩ := mem_relationGraph_iff.mp h
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective he
    exact ⟨ha, hb, hd⟩
  · rintro ⟨hx, hy, hd⟩
    exact mem_relationGraph_iff.mpr ⟨mem_cartesianProductFoundational.mpr ⟨hx, hy⟩,
      distance_mem hd, x, hx, y, hy, rfl, hd⟩

theorem rationalDistanceGraph_isFunc :
    IsFuncFoundational (cartesianProductFoundational rationalsTA rationalsTA)
      rationalsTA (rationalDistanceGraph : ZFSet.{u}) := by
  apply relationGraph_isFunc
  intro p hp
  obtain ⟨x, hx, y, hy, rfl⟩ := (ZFSet.mem_sep.mp hp).2
  obtain ⟨r, hr, _⟩ := distance_exists_unique hx hy
  refine ⟨r, ⟨distance_mem hr, x, hx, y, hy, rfl, hr⟩, ?_⟩
  intro s hs
  obtain ⟨a, _, b, _, he, hd⟩ := hs.2
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective he
  exact distance_unique hx hy hd hr

def rationalDistance : ZFSet.{u} :=
  functionTriple (cartesianProductFoundational rationalsTA rationalsTA)
    rationalsTA rationalDistanceGraph

theorem TA_DEF_00108_rationalDistance_isFunction :
    IsFunctionTriple (cartesianProductFoundational rationalsTA rationalsTA)
      rationalsTA (rationalDistance : ZFSet.{u}) :=
  ⟨rationalDistanceGraph, rfl, rationalDistanceGraph_isFunc⟩

/-- TA-PRO-00109(1). -/
theorem distance_nonnegative {x y r : ZFSet.{u}} (h : RatDistance x y r) :
    RatLE ratZero r := by
  obtain ⟨_, _, ha⟩ := h
  exact ratAbs_nonnegative ha

/-- TA-PRO-00109(2). -/
theorem distance_zero_iff {x y r : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA) (h : RatDistance x y r) :
    r = ratZero ↔ x = y := by
  obtain ⟨t, ht, ha⟩ := h
  exact (ratAbs_zero_iff ha).trans (ratSub_zero_iff hx hy ht)

/-- TA-PRO-00109(3). -/
theorem distance_symm {x y r s : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (hr : RatDistance x y r) (hs : RatDistance y x s) : r = s := by
  obtain ⟨t, ht, ha⟩ := hr
  obtain ⟨w, hw, hb⟩ := hs
  exact (ratAbs_neg (ratSub_reverse_neg hx hy ht hw) ha hb).symm

/-- TA-PRO-00109(4). -/
theorem distance_triangle {x y z a b c s : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA) (hz : z ∈ rationalsTA)
    (ha : RatDistance x y a) (hb : RatDistance y z b)
    (hc : RatDistance x z c) (hs : RatAdd a b s) : RatLE c s := by
  obtain ⟨t, ht, ha'⟩ := ha
  obtain ⟨w, hw, hb'⟩ := hb
  obtain ⟨v, hv, hc'⟩ := hc
  exact ratAbs_triangle ha' hb' hc' (ratSub_chain_add hx hy hz ht hw hv) hs

/-- TA-PRO-00109(5). -/
theorem distance_translate {x y z xz yz r s : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA) (hz : z ∈ rationalsTA)
    (hxz : RatAdd x z xz) (hyz : RatAdd y z yz)
    (hr : RatDistance x y r) (hs : RatDistance xz yz s) : s = r := by
  obtain ⟨t, ht, ha⟩ := hr
  have ht' := ratSub_translate hx hy hz hxz hyz ht
  exact distance_unique (funcFoundational_value_mem ratAddGraph_isFunc hxz)
    (funcFoundational_value_mem ratAddGraph_isFunc hyz) hs ⟨t, ht', ha⟩

/-- TA-PRO-00110: equivalencias epsilon-locales con extremos racionales. -/
theorem TA_PRO_00110_distance_local
    {x y e ne t r lo hi : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (he : e ∈ rationalsTA) (_hepos : RatLT ratZero e)
    (hne : RatNeg e ne) (ht : RatSub x y t) (hr : RatDistance x y r)
    (hlo : RatSub y e lo) (hhi : RatAdd y e hi) :
    (RatLT r e ↔ RatLT ne t ∧ RatLT t e) ∧
    ((RatLT ne t ∧ RatLT t e) ↔ RatLT lo x ∧ RatLT x hi) := by
  obtain ⟨w, hw, ha⟩ := hr
  have ew := RatSub_unique hx hy hw ht
  subst w
  refine ⟨ratAbs_lt_iff_symmetric ha hne, ?_⟩
  have hneQ := funcFoundational_value_mem ratNegGraph_isFunc hne
  have htQ := ratSub_value_mem ht
  have hty := ratSub_add_cancel hx hy ht
  obtain ⟨ne', hne', hlow⟩ := hlo
  have en := RatNeg_unique he hne' hne
  rw [en] at hlow
  have h1 := TA_LEM_00020_clause8_translate_iff hneQ htQ hy
    (ratAdd_comm_rel hy hneQ hlow) hty
  have h2 := TA_LEM_00020_clause8_translate_iff htQ he hy hty
    (ratAdd_comm_rel hy he hhi)
  exact ⟨fun h => ⟨h1.mp h.1, h2.mp h.2⟩,
    fun h => ⟨h1.mpr h.1, h2.mpr h.2⟩⟩

end TratadoAnalisis.Cauchy.RationalDistance
