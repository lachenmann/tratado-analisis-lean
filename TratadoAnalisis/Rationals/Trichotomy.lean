import TratadoAnalisis.Rationals.Signs

namespace TratadoAnalisis.Rationals.Trichotomy

open TratadoAnalisis.Naturals.Recursion
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
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.Field
open TratadoAnalisis.Rationals.OrderPrep
open TratadoAnalisis.Rationals.PositiveDenominator
open TratadoAnalisis.Rationals.OrderWellDefined
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.OrderedFieldCompatibility


/-- Tricotomía proposicional de enteros por representantes naturales.
No proporciona un decisor sobre el portador ZFSet. -/
theorem intLT_trichotomy_local {x y : ZFSet}
    (hx : x ∈ integersTA) (hy : y ∈ integersTA) :
    IntLT x y ∨ x = y ∨ IntLT y x := by
  rcases exists_natEncode_intClass_of_mem hx with ⟨A, B, rfl⟩
  rcases exists_natEncode_intClass_of_mem hy with ⟨C, D, rfl⟩
  rcases Nat.lt_trichotomy (A + D) (C + B) with h | h | h
  · left
    refine ⟨(TA_PRO_00048_intLE_natEncode_classes_iff A B C D).mpr
      (Nat.le_of_lt h), ?_⟩
    intro he
    have hn := (TA_PRO_00038_natEncode_class_eq_iff A B C D).mp he
    exact (Nat.ne_of_lt h) (hn.trans (Nat.add_comm B C))
  · right; left
    exact (TA_PRO_00038_natEncode_class_eq_iff A B C D).mpr
      (h.trans (Nat.add_comm C B))
  · right; right
    refine ⟨(TA_PRO_00048_intLE_natEncode_classes_iff C D A B).mpr
      (Nat.le_of_lt h), ?_⟩
    intro he
    have hn := (TA_PRO_00038_natEncode_class_eq_iff C D A B).mp he
    exact (Nat.ne_of_lt h) (hn.trans (Nat.add_comm D A))

/-- TA-PRO-00172: solo tricotomía proposicional, sin lectura efectiva
ni instancia de decidibilidad para la igualdad de racionales. -/
theorem TA_PRO_00172_rational_trichotomy {x y : ZFSet}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA) :
    RatLT x y ∨ x = y ∨ RatLT y x := by
  rcases TA_LEM_00013_positive_denominator hx with ⟨a, m, ha, _, hbPos, rfl⟩
  rcases TA_LEM_00013_positive_denominator hy with ⟨c, n, hc, _, hdPos, rfl⟩
  have hbI := intPositiveForm_mem_integersTA m
  have hdI := intPositiveForm_mem_integersTA n
  have hb := mem_intNonzeroTA_of_positive hbI hbPos
  have hd := mem_intNonzeroTA_of_positive hdI hdPos
  rcases intMul_exists ha hdI with ⟨ad, hadI, had⟩
  rcases intMul_exists hbI hc with ⟨bc, hbcI, hbc⟩
  rcases intLT_trichotomy_local hadI hbcI with h | h | h
  · exact Or.inl ((TA_COR_00009_ratLT_classes_iff ha hb hc hd
      hbPos hdPos had hbc).mpr h)
  · exact Or.inr (Or.inl ((TA_PRO_00053_ratClass_pairs_eq_iff ha hb hc hd).mpr
      ⟨ad, bc, had, hbc, h⟩))
  · rcases intMul_exists hc hbI with ⟨cb, _, hcb⟩
    rcases intMul_exists hdI ha with ⟨da, _, hda⟩
    have heBC : bc = cb := intMul_comm hbI hc hbc hcb
    have heAD : ad = da := intMul_comm ha hdI had hda
    rw [heBC, heAD] at h
    exact Or.inr (Or.inr ((TA_COR_00009_ratLT_classes_iff hc hd ha hb
      hdPos hbPos hcb hda).mpr h))

end TratadoAnalisis.Rationals.Trichotomy

