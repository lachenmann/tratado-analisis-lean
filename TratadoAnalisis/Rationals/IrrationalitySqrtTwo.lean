import TratadoAnalisis.Rationals.IrrationalityPrep

namespace TratadoAnalisis.Rationals.IrrationalitySqrtTwo

universe u

open TratadoAnalisis.Naturals.Foundational
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Naturals.ArithmeticBridge
open TratadoAnalisis.Integers.Construction
open TratadoAnalisis.Integers.Operations
open TratadoAnalisis.Integers.Multiplication
open TratadoAnalisis.Integers.Algebra
open TratadoAnalisis.Integers.Domain
open TratadoAnalisis.Rationals.IntegerPrep
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.Field
open TratadoAnalisis.Rationals.OrderPrep
open TratadoAnalisis.Rationals.PositiveDenominator
open TratadoAnalisis.Rationals.OrderWellDefined
open TratadoAnalisis.Rationals.IrrationalityPrep

/-! # E1b — inexistencia de una raíz cuadrada racional de 2 -/

def natTwoTA : ZFSet :=
  natEncode 2

def intTwoTA : ZFSet :=
  intPositiveForm 2

def ratTwoTA : ZFSet :=
  ratClass (ZFSet.pair intTwoTA intOne)

theorem natTwoTA_mem_omegaTA : natTwoTA ∈ omegaTA := by
  exact natEncode_mem_omegaTA 2

theorem intTwoTA_mem_integersTA : intTwoTA ∈ integersTA := by
  exact intPositiveForm_mem_integersTA 2

theorem ratTwoTA_mem_rationalsTA : ratTwoTA ∈ rationalsTA := by
  apply ratClass_mem_rationalsTA
  exact mem_ratDomain_iff.mpr
    ⟨intTwoTA, intOne, intTwoTA_mem_integersTA,
      intOne_mem_intNonzeroTA, rfl⟩

theorem natTwoTA_intEmbed :
    ZFSet.pair natTwoTA intTwoTA ∈ intEmbedGraph := by
  simpa [natTwoTA, intTwoTA, intPositiveForm] using
    intEmbedGraph_natEncode 2

theorem intTwoTA_ratEmbed :
    ZFSet.pair intTwoTA ratTwoTA ∈ ratEmbedGraph := by
  simpa [ratTwoTA] using ratEmbedGraph_value intTwoTA_mem_integersTA

theorem ratTwoTA_ne_zero : ratTwoTA ≠ ratZero := by
  apply (TA_PRO_00061_ratClass_ne_zero_iff
    intTwoTA_mem_integersTA intOne_mem_intNonzeroTA).mpr
  exact intPositiveForm_ne_zero (by decide)

def SqrtTwoDenominatorWitness (s : Nat) : Prop :=
  s ≠ 0 ∧ ∃ r : Nat, r ≠ 0 ∧ r * r = 2 * (s * s)

theorem nat_two_mul (n : Nat) : 2 * n = n + n := by
  calc
    2 * n = (1 + 1) * n := by rfl
    _ = 1 * n + 1 * n := Nat.add_mul 1 1 n
    _ = n + n := by simp only [Nat.one_mul]

theorem sqrtTwoWitness_descends
    {n : Nat}
    (h : SqrtTwoDenominatorWitness n) :
    ∃ s : Nat, s < n ∧ SqrtTwoDenominatorWitness s := by
  rcases h with ⟨hn, m, hm, hSquare⟩
  have hmSquareEven : EvenTA (m * m) := ⟨n * n, hSquare⟩
  rcases TA_LEM_00017_even_square_implies_even hmSquareEven with ⟨r, hmForm⟩
  have hr : r ≠ 0 := by
    intro hrZero
    apply hm
    rw [hmForm, hrZero]
  have hCancelM : 2 * (r * r) = n * n := by
    apply Nat.mul_left_cancel (by decide : 0 < 2)
    calc
      2 * (2 * (r * r)) = (2 * r) * (2 * r) := by ac_rfl
      _ = m * m := by rw [hmForm]
      _ = 2 * (n * n) := hSquare
  have hnSquareEven : EvenTA (n * n) :=
    ⟨r * r, hCancelM.symm⟩
  rcases TA_LEM_00017_even_square_implies_even hnSquareEven with ⟨s, hnForm⟩
  have hs : s ≠ 0 := by
    intro hsZero
    apply hn
    rw [hnForm, hsZero]
  have hReduced : r * r = 2 * (s * s) := by
    apply Eq.symm
    apply Nat.mul_left_cancel (by decide : 0 < 2)
    calc
      2 * (2 * (s * s)) = (2 * s) * (2 * s) := by ac_rfl
      _ = n * n := by rw [hnForm]
      _ = 2 * (r * r) := hCancelM.symm
  have hsPos : 0 < s := Nat.pos_of_ne_zero hs
  have hsLtN : s < n := by
    calc
      s < s + s := Nat.lt_add_of_pos_right hsPos
      _ = 2 * s := (nat_two_mul s).symm
      _ = n := hnForm.symm
  exact ⟨s, hsLtN, hs, r, hr, hReduced⟩

theorem sqrtTwoWitness_wellFounded_empty :
    ∀ n : Nat, ¬ SqrtTwoDenominatorWitness n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      rcases sqrtTwoWitness_descends hn with ⟨s, hsLt, hs⟩
      exact ih s hsLt hs

theorem square_fraction_cross_eq
    {q qq a : ZFSet.{u}} {n : Nat}
    (ha : a ∈ integersTA)
    (hn : n ≠ 0)
    (hbPos : IntLT (intZero : ZFSet.{u})
      (intPositiveForm n : ZFSet.{u}))
    (hqClass : q = ratClass (ZFSet.pair a (intPositiveForm n)))
    (hqq : RatMul q q qq)
    (hqqTwo : qq = ratTwoTA) :
    ∃ m : Nat, m ≠ 0 ∧ m * m = 2 * (n * n) := by
  have hbI := intPositiveForm_mem_integersTA n
  have hbNZ : intPositiveForm n ∈ intNonzeroTA :=
    mem_intNonzeroTA_of_positive hbI hbPos
  rcases intMul_exists ha ha with ⟨aa, haaI, haa⟩
  rcases intMul_exists hbI hbI with ⟨bb, hbbI, hbb⟩
  have hbbNZ := intNonzero_mul_closed hbNZ hbNZ hbb
  rw [hqClass] at hqq
  have hqqValue :=
    (ratMulGraph_classes_value_iff ha hbNZ ha hbNZ haa hbb).mp hqq
  have hClassEq : ratClass (ZFSet.pair aa bb) = ratTwoTA :=
    hqqValue.symm.trans hqqTwo
  have hCross :=
    (TA_PRO_00053_ratClass_pairs_eq_iff haaI hbbNZ
      intTwoTA_mem_integersTA intOne_mem_intNonzeroTA).mp
      (by simpa [ratTwoTA] using hClassEq)
  rcases hCross with ⟨u, v, hu, hv, huv⟩
  have huValue : u = aa := intMul_one_right haaI hu
  have hbbValue : bb = intPositiveForm (n * n) :=
    intMul_positive_positive hbb
  have hv' : IntMul (intPositiveForm (n * n)) intTwoTA v := by
    rw [← hbbValue]
    exact hv
  have hvValue : v = intPositiveForm ((n * n) * 2) :=
    intMul_positive_positive hv'
  have haaValue : aa = intPositiveForm (2 * (n * n)) := by
    calc
      aa = u := huValue.symm
      _ = v := huv
      _ = intPositiveForm ((n * n) * 2) := hvValue
      _ = intPositiveForm (2 * (n * n)) := by rw [Nat.mul_comm]
  have haNZ : a ≠ intZero := by
    intro haZero
    have haaZero : aa = intZero := by
      rw [haZero] at haa
      exact intMul_zero_left intZero_mem_integersTA haa
    have hNatNZ : 2 * (n * n) ≠ 0 :=
      Nat.mul_ne_zero (by decide) (Nat.mul_ne_zero hn hn)
    exact intPositiveForm_ne_zero hNatNZ (haaValue.symm.trans haaZero)
  rcases int_sign_normal_exists ha with haZero | haPositive | haNegative
  · exact False.elim (haNZ haZero)
  · rcases haPositive with ⟨m, hm, haForm⟩
    have haa' : IntMul (intPositiveForm m) (intPositiveForm m) aa := by
      rw [← haForm]
      exact haa
    have haaForm : aa = intPositiveForm (m * m) :=
      intMul_positive_positive haa'
    exact ⟨m, hm, (intPositiveForm_eq_iff _ _).mp
      (haaForm.symm.trans haaValue)⟩
  · rcases haNegative with ⟨m, hm, haForm⟩
    have haa' : IntMul (intNegativeForm m) (intNegativeForm m) aa := by
      rw [← haForm]
      exact haa
    have haaForm : aa = intPositiveForm (m * m) :=
      intMul_negative_negative haa'
    exact ⟨m, hm, (intPositiveForm_eq_iff _ _).mp
      (haaForm.symm.trans haaValue)⟩

theorem TA_THM_00032_no_rational_square_two :
    ¬ ∃ q qq : ZFSet.{u},
      q ∈ rationalsTA ∧
      RatMul q q qq ∧
      qq = ratTwoTA := by
  rintro ⟨q, qq, hq, hqq, hqqTwo⟩
  rcases TA_LEM_00013_positive_denominator hq with
    ⟨a, n, ha, hn, hbPos, hqClass⟩
  rcases square_fraction_cross_eq ha hn hbPos hqClass hqq hqqTwo with
    ⟨m, hm, hSquare⟩
  exact sqrtTwoWitness_wellFounded_empty n ⟨hn, m, hm, hSquare⟩

end TratadoAnalisis.Rationals.IrrationalitySqrtTwo
