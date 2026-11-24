import TratadoAnalisis.Dedekind.MultiplicativeLaws

namespace TratadoAnalisis.Dedekind.Distributivity
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

open TratadoAnalisis.Dedekind.PositiveDistributivity
open TratadoAnalisis.Dedekind.AdditiveIdentities
open TratadoAnalisis.Dedekind.ProductSignLaws
open TratadoAnalisis.Dedekind.MultiplicativeLaws
open TratadoAnalisis.Dedekind.TranslationOrder

theorem add_left_neg_cancel (em : ∀ p : Prop, p ∨ ¬p)
    {a b : ZFSet.{u}} (ha : a ∈ dedekindCutsTA) (hb : b ∈ dedekindCutsTA) :
    dedAdd a (dedAdd (dedNeg a) b) = b := by
  rw [← TA_THM_00041_dedAdd_assoc ha (TA_PRO_00087_dedNeg_mem em ha) hb,
    TA_PRO_00088_dedAdd_neg em ha, (TA_PRO_00086_dedZero_neutral hb).2]

theorem solve_add_left (em : ∀ p : Prop, p ∨ ¬p)
    {z x y : ZFSet.{u}} (hz : z ∈ dedekindCutsTA) (hx : x ∈ dedekindCutsTA)
    (_hy : y ∈ dedekindCutsTA) (he : dedAdd z x = y) :
    x = dedAdd y (dedNeg z) := by
  calc
    x = dedAdd (dedAdd x z) (dedNeg z) := (dedAdd_translate_restore em hx hz).symm
    _ = dedAdd (dedAdd z x) (dedNeg z) := congrArg (fun t => dedAdd t (dedNeg z)) (TA_THM_00042_dedAdd_comm hx hz)
    _ = _ := congrArg (fun t => dedAdd t (dedNeg z)) he

theorem solve_add_neg_right (em : ∀ p : Prop, p ∨ ¬p)
    {x d y : ZFSet.{u}} (hx : x ∈ dedekindCutsTA) (hd : d ∈ dedekindCutsTA)
    (_hy : y ∈ dedekindCutsTA) (he : y = dedAdd x (dedNeg d)) :
    d = dedAdd x (dedNeg y) := by
  have hn := congrArg dedNeg he
  rw [TA_LEM_00026_neg_add em hx (TA_PRO_00087_dedNeg_mem em hd),
    TA_LEM_00025_dedNeg_involutive em hd] at hn
  calc
    d = dedAdd x (dedAdd (dedNeg x) d) := (add_left_neg_cancel em hx hd).symm
    _ = _ := congrArg (dedAdd x) hn.symm

theorem neg_add_sum_cancel (em : ∀ p : Prop, p ∨ ¬p)
    {b c : ZFSet.{u}} (hb : b ∈ dedekindCutsTA) (hc : c ∈ dedekindCutsTA) :
    dedAdd (dedNeg c) (dedAdd b c) = b := by
  have hn := TA_PRO_00087_dedNeg_mem em hc
  rw [← TA_THM_00041_dedAdd_assoc hn hb hc,
    TA_THM_00042_dedAdd_comm hn hb, TA_THM_00041_dedAdd_assoc hb hn hc,
    (TA_COR_00020_dedAdd_neg_bilateral em hc).2, (TA_PRO_00086_dedZero_neutral hb).1]

theorem add_neg_sum_eq (em : ∀ p : Prop, p ∨ ¬p)
    {b c : ZFSet.{u}} (hb : b ∈ dedekindCutsTA) (hc : c ∈ dedekindCutsTA) :
    dedAdd b (dedNeg (dedAdd b c)) = dedNeg c := by
  rw [TA_LEM_00026_neg_add em hb hc]
  exact add_left_neg_cancel em hb (TA_PRO_00087_dedNeg_mem em hc)

theorem positive_add_cut (em : ∀ p : Prop, p ∨ ¬p)
    {β γ : ZFSet.{u}} (hb : IsPositiveCut β) (hc : IsPositiveCut γ) :
    IsPositiveCut (dedAdd β γ) := by
  exact TA_LEM_00023_zero_mem_implies_positive
    (TA_PRO_00084_dedAdd_mem em hb.1.2.1 hc.1.2.1)
    (mem_dedAdd_of_add ratZero_mem_rationalsTA ratZero_mem_rationalsTA
      (TA_LEM_00023_positive_implies_zero_mem em hb.1.2.1 hb)
      (TA_LEM_00023_positive_implies_zero_mem em hc.1.2.1 hc)
      (zero_add_rel ratZero_mem_rationalsTA))

theorem positive_general_distrib (em : ∀ p : Prop, p ∨ ¬p)
    {α β γ : ZFSet.{u}} (ha : IsPositiveCut α) (hb : IsPositiveCut β) (hc : IsPositiveCut γ) :
    dedMul α (dedAdd β γ) = dedAdd (dedMul α β) (dedMul α γ) := by
  change dedSignedMul α (dedAdd β γ) = dedAdd (dedSignedMul α β) (dedSignedMul α γ)
  rw [TA_DEF_00096_of_pos_pos ha (positive_add_cut em hb hc),
    TA_DEF_00096_of_pos_pos ha hb, TA_DEF_00096_of_pos_pos ha hc]
  exact TA_THM_00049_positiveMul_distrib em ha hb hc

theorem positive_factor_distrib_mixed (em : ∀ p : Prop, p ∨ ¬p)
    {α β γ : ZFSet.{u}} (ha : IsPositiveCut α) (hb : IsPositiveCut β) (hc : IsNegativeCut γ) :
    dedMul α (dedAdd β γ) = dedAdd (dedMul α β) (dedMul α γ) := by
  have hα := ha.1.2.1
  have hβ := hb.1.2.1
  have hγ := hc.1.1
  have hC := TA_PRO_00087_dedNeg_mem em hγ
  have pC := negative_implies_positive_neg em hγ hc
  let d : ZFSet.{u} := dedAdd β γ
  have hd : d ∈ dedekindCutsTA := TA_PRO_00084_dedAdd_mem em hβ hγ
  have hCd : dedAdd (dedNeg γ) d = β := neg_add_sum_cancel em hβ hγ
  have hBnd : dedAdd β (dedNeg d) = dedNeg γ := add_neg_sum_eq em hβ hγ
  have fB : dedMul α β ∈ dedekindCutsTA := TA_PRO_00094_dedSignedMul_mem em hα hβ
  have fC : dedMul α (dedNeg γ) ∈ dedekindCutsTA := TA_PRO_00094_dedSignedMul_mem em hα hC
  have fD : dedMul α d ∈ dedekindCutsTA := TA_PRO_00094_dedSignedMul_mem em hα hd
  have fg : dedMul α γ ∈ dedekindCutsTA := TA_PRO_00094_dedSignedMul_mem em hα hγ
  have heγ : dedMul α γ = dedNeg (dedMul α (dedNeg γ)) :=
    ((congrArg dedNeg (dedMul_neg_right em hα hγ)).trans
      (TA_LEM_00025_dedNeg_involutive em fg)).symm
  change dedMul α d = dedAdd (dedMul α β) (dedMul α γ)
  rw [heγ]
  rcases TA_PRO_00093_zero_sign_trichotomy em hd with hn | he | hp
  · have pnd := negative_implies_positive_neg em hd hn
    have eqn := positive_general_distrib em ha hb pnd
    rw [hBnd, dedMul_neg_right em hα hd] at eqn
    exact solve_add_neg_right em fB fD fC eqn
  · have heCB : dedNeg γ = β := by
      simpa only [he, (TA_PRO_00086_dedZero_neutral hC).1] using hCd
    rw [he, dedMul_zero_right, ← heCB]
    exact (TA_PRO_00088_dedAdd_neg em fC).symm
  · have eqn := positive_general_distrib em ha pC hp
    rw [hCd] at eqn
    exact solve_add_left em fC fD fB eqn.symm

theorem positive_factor_distrib_negative_pair (em : ∀ p : Prop, p ∨ ¬p)
    {α β γ : ZFSet.{u}} (ha : IsPositiveCut α) (hb : IsNegativeCut β) (hc : IsNegativeCut γ) :
    dedMul α (dedAdd β γ) = dedAdd (dedMul α β) (dedMul α γ) := by
  have hα := ha.1.2.1
  have hβ := hb.1.1
  have hγ := hc.1.1
  have hnβ := TA_PRO_00087_dedNeg_mem em hβ
  have hnγ := TA_PRO_00087_dedNeg_mem em hγ
  have hnbnc := TA_PRO_00084_dedAdd_mem em hnβ hnγ
  have fB : dedMul α β ∈ dedekindCutsTA := TA_PRO_00094_dedSignedMul_mem em hα hβ
  have fC : dedMul α γ ∈ dedekindCutsTA := TA_PRO_00094_dedSignedMul_mem em hα hγ
  have fnB : dedMul α (dedNeg β) ∈ dedekindCutsTA := TA_PRO_00094_dedSignedMul_mem em hα hnβ
  have fnC : dedMul α (dedNeg γ) ∈ dedekindCutsTA := TA_PRO_00094_dedSignedMul_mem em hα hnγ
  have sumEq : dedNeg (dedAdd (dedNeg β) (dedNeg γ)) = dedAdd β γ := by
    rw [TA_LEM_00026_neg_add em hnβ hnγ, TA_LEM_00025_dedNeg_involutive em hβ,
      TA_LEM_00025_dedNeg_involutive em hγ]
  calc
    _ = dedMul α (dedNeg (dedAdd (dedNeg β) (dedNeg γ))) := congrArg (dedMul α) sumEq.symm
    _ = dedNeg (dedMul α (dedAdd (dedNeg β) (dedNeg γ))) := dedMul_neg_right em hα hnbnc
    _ = dedNeg (dedAdd (dedMul α (dedNeg β)) (dedMul α (dedNeg γ))) := congrArg dedNeg
      (positive_general_distrib em ha (negative_implies_positive_neg em hβ hb) (negative_implies_positive_neg em hγ hc))
    _ = dedAdd (dedNeg (dedMul α (dedNeg β))) (dedNeg (dedMul α (dedNeg γ))) := TA_LEM_00026_neg_add em fnB fnC
    _ = _ := by rw [dedMul_neg_right em hα hβ, dedMul_neg_right em hα hγ,
        TA_LEM_00025_dedNeg_involutive em fB, TA_LEM_00025_dedNeg_involutive em fC]

theorem TA_PRO_00102_positive_factor_distrib (em : ∀ p : Prop, p ∨ ¬p)
    {α β γ : ZFSet.{u}} (ha : IsPositiveCut α)
    (hb : β ∈ dedekindCutsTA) (hc : γ ∈ dedekindCutsTA) :
    dedMul α (dedAdd β γ) = dedAdd (dedMul α β) (dedMul α γ) := by
  have hα := ha.1.2.1
  have fb : dedMul α β ∈ dedekindCutsTA := TA_PRO_00094_dedSignedMul_mem em hα hb
  have fc : dedMul α γ ∈ dedekindCutsTA := TA_PRO_00094_dedSignedMul_mem em hα hc
  rcases TA_PRO_00093_zero_sign_trichotomy em hb with bn | bz | bp
  · rcases TA_PRO_00093_zero_sign_trichotomy em hc with cn | cz | cp
    · exact positive_factor_distrib_negative_pair em ha bn cn
    · rw [cz, (TA_PRO_00086_dedZero_neutral hb).1, dedMul_zero_right,
        (TA_PRO_00086_dedZero_neutral fb).1]
    · calc
        _ = dedMul α (dedAdd γ β) := congrArg (dedMul α) (TA_THM_00042_dedAdd_comm hb hc)
        _ = dedAdd (dedMul α γ) (dedMul α β) := positive_factor_distrib_mixed em ha cp bn
        _ = _ := TA_THM_00042_dedAdd_comm fc fb
  · rw [bz, (TA_PRO_00086_dedZero_neutral hc).2, dedMul_zero_right,
      (TA_PRO_00086_dedZero_neutral fc).2]
  · rcases TA_PRO_00093_zero_sign_trichotomy em hc with cn | cz | cp
    · exact positive_factor_distrib_mixed em ha bp cn
    · rw [cz, (TA_PRO_00086_dedZero_neutral hb).1, dedMul_zero_right,
        (TA_PRO_00086_dedZero_neutral fb).1]
    · exact positive_general_distrib em ha bp cp

theorem dedMul_distrib_left (em : ∀ p : Prop, p ∨ ¬p)
    {α β γ : ZFSet.{u}} (ha : α ∈ dedekindCutsTA)
    (hb : β ∈ dedekindCutsTA) (hc : γ ∈ dedekindCutsTA) :
    dedMul α (dedAdd β γ) = dedAdd (dedMul α β) (dedMul α γ) := by
  have hs := TA_PRO_00084_dedAdd_mem em hb hc
  have fb : dedMul α β ∈ dedekindCutsTA := TA_PRO_00094_dedSignedMul_mem em ha hb
  have fc : dedMul α γ ∈ dedekindCutsTA := TA_PRO_00094_dedSignedMul_mem em ha hc
  rcases TA_PRO_00093_zero_sign_trichotomy em ha with hn | he | hp
  · have hna := TA_PRO_00087_dedNeg_mem em ha
    have fnb : dedMul (dedNeg α) β ∈ dedekindCutsTA := TA_PRO_00094_dedSignedMul_mem em hna hb
    have fnc : dedMul (dedNeg α) γ ∈ dedekindCutsTA := TA_PRO_00094_dedSignedMul_mem em hna hc
    calc
      _ = dedMul (dedNeg (dedNeg α)) (dedAdd β γ) := congrArg (fun a => dedMul a (dedAdd β γ)) (TA_LEM_00025_dedNeg_involutive em ha).symm
      _ = dedNeg (dedMul (dedNeg α) (dedAdd β γ)) := dedMul_neg_left em hna hs
      _ = dedNeg (dedAdd (dedMul (dedNeg α) β) (dedMul (dedNeg α) γ)) := congrArg dedNeg
        (TA_PRO_00102_positive_factor_distrib em (negative_implies_positive_neg em ha hn) hb hc)
      _ = dedAdd (dedNeg (dedMul (dedNeg α) β)) (dedNeg (dedMul (dedNeg α) γ)) := TA_LEM_00026_neg_add em fnb fnc
      _ = _ := by
        rw [dedMul_neg_left em ha hb, dedMul_neg_left em ha hc,
          TA_LEM_00025_dedNeg_involutive em fb,
          TA_LEM_00025_dedNeg_involutive em fc]
  · rw [he]
    simp only [dedMul_zero_left, (TA_PRO_00086_dedZero_neutral dedZero_mem).1]
  · exact TA_PRO_00102_positive_factor_distrib em hp hb hc

theorem TA_THM_00052_dedMul_distrib (em : ∀ p : Prop, p ∨ ¬p)
    {α β γ : ZFSet.{u}} (ha : α ∈ dedekindCutsTA)
    (hb : β ∈ dedekindCutsTA) (hc : γ ∈ dedekindCutsTA) :
    dedMul α (dedAdd β γ) = dedAdd (dedMul α β) (dedMul α γ) ∧
      dedMul (dedAdd β γ) α = dedAdd (dedMul β α) (dedMul γ α) := by
  refine ⟨dedMul_distrib_left em ha hb hc, ?_⟩
  rw [TA_THM_00050_dedMul_comm (TA_PRO_00084_dedAdd_mem em hb hc) ha,
    dedMul_distrib_left em ha hb hc,
    TA_THM_00050_dedMul_comm ha hb, TA_THM_00050_dedMul_comm ha hc]


end TratadoAnalisis.Dedekind.Distributivity
