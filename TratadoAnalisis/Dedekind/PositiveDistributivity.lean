import TratadoAnalisis.Dedekind.PositiveProductLaws

namespace TratadoAnalisis.Dedekind.PositiveDistributivity
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

theorem positive_add {a b s : ZFSet.{u}}
    (ha : a ∈ rationalsTA) (hb : b ∈ rationalsTA)
    (h0a : RatLT ratZero a) (h0b : RatLT ratZero b) (hs : RatAdd a b s) :
    RatLT ratZero s := by
  have hbs := ratLT_add_right_local ratZero_mem_rationalsTA ha hb h0a (zero_add_rel hb) hs
  exact ratLT_of_lt_of_le_local ratZero_mem_rationalsTA hb
    (funcFoundational_value_mem ratAddGraph_isFunc hs) h0b hbs.1

theorem positive_sum_repair_left {β γ b0 c0 u0 : ZFSet.{u}}
    (cb : IsDedekindCut β) (cc : IsDedekindCut γ)
    (h0β : (ratZero : ZFSet.{u}) ∈ β)
    (hb0 : b0 ∈ β) (hc0 : c0 ∈ γ) (hs : RatAdd b0 c0 u0)
    (h0u : RatLT ratZero u0) (hb00 : RatLE b0 ratZero) :
    ∃ b c : ZFSet.{u}, b ∈ β ∧ RatLT ratZero b ∧
      c ∈ γ ∧ RatLT ratZero c ∧ RatAdd b c u0 := by
  have hb0Q := cb.1 hb0
  have hc0Q := cc.1 hc0
  have huQ := funcFoundational_value_mem ratAddGraph_isFunc hs
  rcases cb.2.2.2.2 ratZero h0β with ⟨d, hd, h0d⟩
  have hdQ := cb.1 hd
  rcases rational_min_witness huQ hdQ with ⟨m, hm, he, hmu, hmd⟩
  have h0m : RatLT ratZero m := by
    rcases he with rfl | rfl
    · exact h0u
    · exact h0d
  rcases TA_THM_00030_rational_density ratZero_mem_rationalsTA hm h0m with ⟨b, hbQ, h0b, hbm⟩
  have hbu := ratLT_of_lt_of_le_local hbQ hm huQ hbm hmu
  have hbd := ratLT_of_lt_of_le_local hbQ hm hdQ hbm hmd
  have hb := cb.2.2.2.1 d hd b hbQ hbd
  rcases ratSub_exists huQ hbQ with ⟨c, hcQ, hc⟩
  have h0c := ratSub_positive huQ hbQ hbu hc
  have hcb := ratSub_add_cancel huQ hbQ hc
  have hbc := ratAdd_comm_rel hcQ hbQ hcb
  have hb0b := ratLT_of_le_of_lt_local hb0Q ratZero_mem_rationalsTA hbQ hb00 h0b
  rcases ratAdd_exists hb0Q hcQ with ⟨v, hvQ, hv⟩
  have hvu := ratLT_add_right_local hb0Q hbQ hcQ hb0b hv hbc
  have hcc0 := ratLT_add_cancel_right_local hcQ hc0Q hb0Q
    (ratAdd_comm_rel hb0Q hcQ hv) (ratAdd_comm_rel hb0Q hc0Q hs) hvu
  exact ⟨b, c, hb, h0b, cc.2.2.2.1 c0 hc0 c hcQ hcc0, h0c, hbc⟩

theorem positive_sum_witnesses {β γ u0 : ZFSet.{u}}
    (cb : IsDedekindCut β) (cc : IsDedekindCut γ)
    (h0β : (ratZero : ZFSet.{u}) ∈ β) (h0γ : (ratZero : ZFSet.{u}) ∈ γ)
    (hu : u0 ∈ dedAdd β γ) (h0u : RatLT ratZero u0) :
    ∃ b c : ZFSet.{u}, b ∈ β ∧ RatLT ratZero b ∧
      c ∈ γ ∧ RatLT ratZero c ∧ RatAdd b c u0 := by
  rcases TA_DEF_00085_mem_dedAdd_iff.mp hu with ⟨_, b0, hb0, c0, hc0, hs⟩
  have left := positive_sum_repair_left cb cc h0β hb0 hc0 hs h0u
  have right := positive_sum_repair_left cc cb h0γ hc0 hb0
    (ratAdd_comm_rel (cb.1 hb0) (cc.1 hc0) hs) h0u
  have finishRight : RatLE c0 ratZero →
      ∃ b c : ZFSet.{u}, b ∈ β ∧ RatLT ratZero b ∧
        c ∈ γ ∧ RatLT ratZero c ∧ RatAdd b c u0 := by
    intro hc00
    rcases right hc00 with ⟨c, b, hc, h0c, hb, h0b, hcb⟩
    exact ⟨b, c, hb, h0b, hc, h0c, ratAdd_comm_rel (cc.1 hc) (cb.1 hb) hcb⟩
  rcases TA_PRO_00172_rational_trichotomy (cb.1 hb0) ratZero_mem_rationalsTA with hn | he | hp
  · exact left hn.1
  · apply left
    rw [he]; exact ratLE_refl ratZero_mem_rationalsTA
  · rcases TA_PRO_00172_rational_trichotomy (cc.1 hc0) ratZero_mem_rationalsTA with kn | ke | kp
    · exact finishRight kn.1
    · apply finishRight
      rw [ke]; exact ratLE_refl ratZero_mem_rationalsTA
    · exact ⟨b0, c0, hb0, hp, hc0, kp, hs⟩

theorem strict_sum_split {x a b s : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (ha : a ∈ rationalsTA) (hb : b ∈ rationalsTA)
    (hs : RatAdd a b s) (hxs : RatLT x s) :
    ∃ y z : ZFSet.{u}, y ∈ rationalsTA ∧ z ∈ rationalsTA ∧
      RatLT y a ∧ RatLT z b ∧ RatAdd y z x := by
  rcases ratSub_exists hx hb with ⟨d, hd, hsub⟩
  have hdb := ratSub_add_cancel hx hb hsub
  have hda := ratLT_add_cancel_right_local hd ha hb hdb hs hxs
  rcases TA_THM_00030_rational_density hd ha hda with ⟨y, hy, hdy, hya⟩
  rcases ratSub_exists hx hy with ⟨z, hz, hsz⟩
  have hzy := ratSub_add_cancel hx hy hsz
  rcases ratAdd_exists hy hb with ⟨yb, hybQ, hyb⟩
  have hxyb := ratLT_add_right_local hd hy hb hdy hdb hyb
  have hzb := ratLT_add_cancel_right_local hz hb hy hzy
    (ratAdd_comm_rel hy hb hyb) hxyb
  exact ⟨y, z, hy, hz, hya, hzb, ratAdd_comm_rel hz hy hzy⟩

/-- Núcleo constructivo: los datos interiores se reciben explícitamente. -/
theorem positiveMul_distrib_of_zero_mem {α β γ : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) (hβ : β ∈ dedekindCutsTA) (hγ : γ ∈ dedekindCutsTA)
    (h0β : (ratZero : ZFSet.{u}) ∈ β) (h0γ : (ratZero : ZFSet.{u}) ∈ γ) :
    dedPositiveMul α (dedAdd β γ) = dedAdd (dedPositiveMul α β) (dedPositiveMul α γ) := by
  have ca := TA_PRO_00079_mem_dedekindCuts_iff.mp hα
  have cb := TA_PRO_00079_mem_dedekindCuts_iff.mp hβ
  have cc := TA_PRO_00079_mem_dedekindCuts_iff.mp hγ
  apply ZFSet.ext
  intro x
  constructor
  · intro hx
    rcases TA_DEF_00093_mem_positiveMul_iff.mp hx with ⟨hxQ, a, ha, u0, hu, au, hau, hxau⟩
    rcases TA_DEF_00092_mem_positivePart_iff.mp ha with ⟨ha, h0a⟩
    rcases TA_DEF_00092_mem_positivePart_iff.mp hu with ⟨hu, h0u⟩
    rcases positive_sum_witnesses cb cc h0β h0γ hu h0u with ⟨b, c, hb, h0b, hc, h0c, hbc⟩
    rcases ratMul_exists (ca.1 ha) (cb.1 hb) with ⟨ab, habQ, hab⟩
    rcases ratMul_exists (ca.1 ha) (cc.1 hc) with ⟨ac, hacQ, hac⟩
    rcases ratAdd_exists habQ hacQ with ⟨s, _, hs⟩
    have he := ratMul_add_left (ca.1 ha) (cb.1 hb) (cc.1 hc) hbc hau hab hac hs
    rw [he] at hxau
    rcases strict_sum_split hxQ habQ hacQ hs hxau with ⟨y, z, hy, hz, hyab, hzac, hyz⟩
    exact mem_dedAdd_of_add hy hz
      (mem_positiveMul_of_witness hy ha h0a hb h0b hab hyab)
      (mem_positiveMul_of_witness hz ha h0a hc h0c hac hzac) hyz
  · intro hx
    rcases TA_DEF_00085_mem_dedAdd_iff.mp hx with ⟨hxQ, y, hy, z, hz, hyz⟩
    rcases TA_DEF_00093_mem_positiveMul_iff.mp hy with ⟨hyQ, a1, ha1, b, hb, a1b, ha1b, hya1b⟩
    rcases TA_DEF_00093_mem_positiveMul_iff.mp hz with ⟨hzQ, a2, ha2, c, hc, a2c, ha2c, hza2c⟩
    rcases TA_DEF_00092_mem_positivePart_iff.mp ha1 with ⟨ha1, h0a1⟩
    rcases TA_DEF_00092_mem_positivePart_iff.mp ha2 with ⟨ha2, _⟩
    rcases TA_DEF_00092_mem_positivePart_iff.mp hb with ⟨hb, h0b⟩
    rcases TA_DEF_00092_mem_positivePart_iff.mp hc with ⟨hc, h0c⟩
    have ha1Q := ca.1 ha1
    have ha2Q := ca.1 ha2
    rcases rational_max_witness ha1Q ha2Q with ⟨m, hmQ, he, ha1m, ha2m⟩
    have hm : m ∈ α := by
      rcases he with rfl | rfl
      · exact ha1
      · exact ha2
    rcases ca.2.2.2.2 m hm with ⟨a, ha, hma⟩
    have haQ := ca.1 ha
    have ha1a := ratLT_of_le_of_lt_local ha1Q hmQ haQ ha1m hma
    have ha2a := ratLT_of_le_of_lt_local ha2Q hmQ haQ ha2m hma
    have h0a := ratLT_of_lt_of_le_local ratZero_mem_rationalsTA ha1Q haQ h0a1 ha1a.1
    rcases ratMul_exists haQ (cb.1 hb) with ⟨ab, habQ, hab⟩
    rcases ratMul_exists haQ (cc.1 hc) with ⟨ac, hacQ, hac⟩
    have hyab := ratLT_of_lt_of_le_local hyQ (ratMul_value_mem ha1b) habQ hya1b
      (ratLT_mul_positive_right ha1Q haQ (cb.1 hb) ha1a h0b ha1b hab).1
    have hzac := ratLT_of_lt_of_le_local hzQ (ratMul_value_mem ha2c) hacQ hza2c
      (ratLT_mul_positive_right ha2Q haQ (cc.1 hc) ha2a h0c ha2c hac).1
    rcases ratAdd_exists habQ hzQ with ⟨v, hvQ, hv⟩
    rcases ratAdd_exists habQ hacQ with ⟨s, hsQ, hs⟩
    have hxv := ratLT_add_right_local hyQ habQ hzQ hyab hyz hv
    have hvs := ratLT_add_left_local hzQ hacQ habQ hzac hv hs
    have hxs := ratLT_of_lt_of_le_local hxQ hvQ hsQ hxv hvs.1
    rcases ratAdd_exists (cb.1 hb) (cc.1 hc) with ⟨u0, huQ, hbc⟩
    rcases ratMul_exists haQ huQ with ⟨au, _, hau⟩
    have he := ratMul_add_left haQ (cb.1 hb) (cc.1 hc) hbc hau hab hac hs
    rw [← he] at hxs
    exact mem_positiveMul_of_witness hxQ ha h0a
      (mem_dedAdd_of_add (cb.1 hb) (cc.1 hc) hb hc hbc)
      (positive_add (cb.1 hb) (cc.1 hc) h0b h0c hbc) hau hxs

theorem TA_THM_00049_positiveMul_distrib (em : ∀ p : Prop, p ∨ ¬p)
    {α β γ : ZFSet.{u}} (hα : IsPositiveCut α) (hβ : IsPositiveCut β) (hγ : IsPositiveCut γ) :
    dedPositiveMul α (dedAdd β γ) = dedAdd (dedPositiveMul α β) (dedPositiveMul α γ) :=
  positiveMul_distrib_of_zero_mem hα.1.2.1 hβ.1.2.1 hγ.1.2.1
    (TA_LEM_00023_positive_implies_zero_mem em hβ.1.2.1 hβ)
    (TA_LEM_00023_positive_implies_zero_mem em hγ.1.2.1 hγ)


end TratadoAnalisis.Dedekind.PositiveDistributivity
