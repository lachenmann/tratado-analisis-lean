import TratadoAnalisis.Rationals.Field

namespace TratadoAnalisis.Rationals.NoZeroDivisors

open TratadoAnalisis.Naturals.Recursion
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

/-! # TA-COR-00007 — ausencia de divisores de cero en Q -/

theorem TA_COR_00007_no_zero_divisors
    {x y xy : ZFSet}
    (hx : x ∈ rationalsTA)
    (hy : y ∈ rationalsTA)
    (hxy : RatMul x y xy)
    (hxyZero : xy = ratZero) :
    x = ratZero ∨ y = ratZero := by
  rcases exists_ratClass_pair_of_mem hx with ⟨a, b, ha, hb, rfl⟩
  rcases exists_ratClass_pair_of_mem hy with ⟨c, d, hc, hd, rfl⟩
  have hbI := (mem_intNonzeroTA_iff.mp hb).1
  have hdI := (mem_intNonzeroTA_iff.mp hd).1
  rcases intMul_exists ha hc with ⟨ac, hacI, hac⟩
  rcases intMul_exists hbI hdI with ⟨bd, _hbdI, hbd⟩
  have hbdNZ := intNonzero_mul_closed hb hd hbd
  have hxyValue :=
    (ratMulGraph_classes_value_iff ha hb hc hd hac hbd).mp hxy
  have hacZero : ac = intZero :=
    (TA_PRO_00061_ratClass_eq_zero_iff hacI hbdNZ).mp
      (hxyValue.symm.trans hxyZero)
  have hacAtZero : IntMul a c intZero := by
    rw [← hacZero]
    exact hac
  rcases TA_PRO_00047_no_zero_divisors ha hc hacAtZero with haZero | hcZero
  · exact Or.inl ((TA_PRO_00061_ratClass_eq_zero_iff ha hb).mpr haZero)
  · exact Or.inr ((TA_PRO_00061_ratClass_eq_zero_iff hc hd).mpr hcZero)

end TratadoAnalisis.Rationals.NoZeroDivisors
