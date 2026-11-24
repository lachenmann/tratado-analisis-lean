import TratadoAnalisis.Rationals.OrderPrep

namespace TratadoAnalisis.Rationals.PositiveDenominator

open TratadoAnalisis.Naturals.ArithmeticBridge
open TratadoAnalisis.Integers.Construction
open TratadoAnalisis.Integers.Operations
open TratadoAnalisis.Integers.Multiplication
open TratadoAnalisis.Integers.Algebra
open TratadoAnalisis.Integers.Domain
open TratadoAnalisis.Integers.Order
open TratadoAnalisis.Rationals.IntegerPrep
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.OrderPrep

/-!
# TA-LEAN-0003 — D1a

Existencia local de representantes racionales con denominador positivo.

No se define una selección global de representantes ni el orden racional.
-/

theorem intPositiveForm_pos
    {n : Nat} (hn : n ≠ 0) :
    IntLT intZero (intPositiveForm n) := by
  constructor
  · have h :=
      (intEmbed_order_nat_iff 0 n).mp (Nat.zero_le n)
    simpa [intPositiveForm, intZero] using h
  · intro h
    exact intPositiveForm_ne_zero hn h.symm

theorem intNeg_symm_local
    {x nx : ZFSet}
    (hx : x ∈ integersTA)
    (hNeg : IntNeg x nx) :
    IntNeg nx x := by
  rcases exists_natEncode_intClass_of_mem hx with ⟨A, B, rfl⟩
  have hnx := intNegGraph_natEncode_class_value_iff.mp hNeg
  rw [hnx]
  simpa [IntNeg] using intNegGraph_natEncode_class B A

theorem TA_LEM_00013_positive_denominator
    {q : ZFSet} (hq : q ∈ rationalsTA) :
    ∃ a : ZFSet, ∃ n : Nat,
      a ∈ integersTA ∧
      n ≠ 0 ∧
      IntLT intZero (intPositiveForm n) ∧
      q = ratClass (ZFSet.pair a (intPositiveForm n)) := by
  rcases exists_ratClass_pair_of_mem hq with
    ⟨a, b, ha, hb, hqClass⟩
  have hbI : b ∈ integersTA :=
    (mem_intNonzeroTA_iff.mp hb).1
  have hbNe : b ≠ intZero :=
    (mem_intNonzeroTA_iff.mp hb).2

  rcases int_sign_normal_exists hbI with hbZero | hbSigns
  · exact (hbNe hbZero).elim

  · rcases hbSigns with hbPos | hbNeg
    · rcases hbPos with ⟨n, hn, hbForm⟩
      refine ⟨a, n, ha, hn, intPositiveForm_pos hn, ?_⟩
      rw [← hbForm]
      exact hqClass

    · rcases hbNeg with ⟨n, hn, hbForm⟩
      rcases intNeg_exists_local ha with ⟨na, hna, hNegA⟩

      have hPosI : intPositiveForm n ∈ integersTA :=
        intPositiveForm_mem_integersTA n
      have hPosNZ : intPositiveForm n ∈ intNonzeroTA :=
        mem_intNonzeroTA_iff.mpr
          ⟨hPosI, intPositiveForm_ne_zero hn⟩

      have hNegDen : IntNeg (intPositiveForm n) b := by
        rw [hbForm]
        exact intNeg_positive_negative n

      have hClasses :
          ratClass (ZFSet.pair a b) =
            ratClass (ZFSet.pair na (intPositiveForm n)) := by
        apply (TA_PRO_00053_ratClass_pairs_eq_iff
          ha hb hna hPosNZ).mpr

        rcases intMul_exists ha hPosI with
          ⟨ap, hapI, hAP⟩
        rcases intMul_exists hbI hna with
          ⟨bna, _hbnaI, hBNA⟩
        rcases intMul_exists hna hPosI with
          ⟨nap, hnapI, hNAP⟩
        rcases intMul_exists hPosI hna with
          ⟨pna, _hpnaI, hPNA⟩

        have hNegAPNAP : IntNeg ap nap :=
          intMul_neg_left ha hna hPosI hNegA hAP hNAP

        have hNapPna : nap = pna :=
          intMul_comm hna hPosI hNAP hPNA

        have hNegPNABNA : IntNeg pna bna :=
          intMul_neg_left hPosI hbI hna hNegDen hPNA hBNA

        have hNegNAPBNA : IntNeg nap bna := by
          rw [hNapPna]
          exact hNegPNABNA

        have hNegNAPAP : IntNeg nap ap :=
          intNeg_symm_local hapI hNegAPNAP

        have hAPBNA : ap = bna :=
          IntNeg_unique hnapI hNegNAPAP hNegNAPBNA

        exact ⟨ap, bna, hAP, hBNA, hAPBNA⟩

      refine ⟨na, n, hna, hn, intPositiveForm_pos hn, ?_⟩
      exact hqClass.trans hClasses

end TratadoAnalisis.Rationals.PositiveDenominator

