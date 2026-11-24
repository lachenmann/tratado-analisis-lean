import TratadoAnalisis.Integers.Algebra

namespace TratadoAnalisis.Integers.Domain

open TratadoAnalisis.Naturals.Foundational
open TratadoAnalisis.Naturals.ArithmeticBridge
open TratadoAnalisis.Integers.Construction
open TratadoAnalisis.Integers.Operations
open TratadoAnalisis.Integers.Multiplication
open TratadoAnalisis.Integers.Algebra

/-! # Forma normal con signo y dominio de integridad -/

/-! ## Formas positiva y negativa -/

def intPositiveForm (n : Nat) : ZFSet :=
  intClass (ZFSet.pair (natEncode n) (natEncode 0))

def intNegativeForm (n : Nat) : ZFSet :=
  intClass (ZFSet.pair (natEncode 0) (natEncode n))

theorem intPositiveForm_mem_integersTA (n : Nat) :
    intPositiveForm n ∈ integersTA := by
  apply intClass_mem_integersTA
  exact mem_intDomain_iff.mpr
    ⟨natEncode n, natEncode 0, natEncode_mem_omegaTA n,
      natEncode_mem_omegaTA 0, rfl⟩

theorem intNegativeForm_mem_integersTA (n : Nat) :
    intNegativeForm n ∈ integersTA := by
  apply intClass_mem_integersTA
  exact mem_intDomain_iff.mpr
    ⟨natEncode 0, natEncode n, natEncode_mem_omegaTA 0,
      natEncode_mem_omegaTA n, rfl⟩

theorem intNeg_positive_negative (n : Nat) :
    IntNeg (intPositiveForm n) (intNegativeForm n) := by
  simpa [IntNeg, intPositiveForm, intNegativeForm] using
    intNegGraph_natEncode_class n 0

/-! ## Igualdad y exclusión de formas -/

theorem intPositiveForm_eq_iff (m n : Nat) :
    intPositiveForm m = intPositiveForm n ↔ m = n := by
  rw [intPositiveForm, intPositiveForm]
  constructor
  · intro h
    have hEq :=
      (TA_PRO_00038_natEncode_class_eq_iff m 0 n 0).mp h
    omega
  · rintro rfl
    rfl

theorem intNegativeForm_eq_iff (m n : Nat) :
    intNegativeForm m = intNegativeForm n ↔ m = n := by
  rw [intNegativeForm, intNegativeForm]
  constructor
  · intro h
    have hEq :=
      (TA_PRO_00038_natEncode_class_eq_iff 0 m 0 n).mp h
    omega
  · rintro rfl
    rfl

theorem intPositiveForm_eq_zero_iff (n : Nat) :
    intPositiveForm n = intZero ↔ n = 0 := by
  rw [intPositiveForm, intZero]
  constructor
  · intro h
    have hEq :=
      (TA_PRO_00038_natEncode_class_eq_iff n 0 0 0).mp h
    omega
  · rintro rfl
    rfl

theorem intNegativeForm_eq_zero_iff (n : Nat) :
    intNegativeForm n = intZero ↔ n = 0 := by
  rw [intNegativeForm, intZero]
  constructor
  · intro h
    have hEq :=
      (TA_PRO_00038_natEncode_class_eq_iff 0 n 0 0).mp h
    omega
  · rintro rfl
    rfl

theorem intPositiveForm_eq_negativeForm_iff (m n : Nat) :
    intPositiveForm m = intNegativeForm n ↔ m + n = 0 := by
  rw [intPositiveForm, intNegativeForm]
  constructor
  · intro h
    have hEq :=
      (TA_PRO_00038_natEncode_class_eq_iff m 0 0 n).mp h
    omega
  · intro h
    apply (TA_PRO_00038_natEncode_class_eq_iff m 0 0 n).mpr
    omega

theorem intPositiveForm_ne_negativeForm
    {m n : Nat}
    (hm : m ≠ 0)
    (hn : n ≠ 0) :
    intPositiveForm m ≠ intNegativeForm n := by
  intro h
  have hmn := (intPositiveForm_eq_negativeForm_iff m n).mp h
  have hm0 : m = 0 := by omega
  have hn0 : n = 0 := by omega
  have hBoth : False ∧ False := ⟨hm hm0, hn hn0⟩
  exact hBoth.1.elim

/-! ## Existencia y unicidad de la forma normal -/

theorem int_sign_normal_exists
    {x : ZFSet}
    (hx : x ∈ integersTA) :
    x = intZero ∨
    (∃ n : Nat, n ≠ 0 ∧ x = intPositiveForm n) ∨
    (∃ n : Nat, n ≠ 0 ∧ x = intNegativeForm n) := by
  rcases exists_natEncode_intClass_of_mem hx with ⟨A, B, hxAB⟩
  rcases Nat.le_total B A with hBA | hAB
  · rcases Nat.exists_eq_add_of_le hBA with ⟨n, hA⟩
    have hClass :
        intClass (ZFSet.pair (natEncode A) (natEncode B)) =
          intPositiveForm n := by
      rw [intPositiveForm]
      apply (TA_PRO_00038_natEncode_class_eq_iff A B n 0).mpr
      omega
    by_cases hn : n = 0
    · left
      rw [hxAB, hClass, hn]
      rfl
    · right
      left
      exact ⟨n, hn, hxAB.trans hClass⟩
  · rcases Nat.exists_eq_add_of_le hAB with ⟨n, hB⟩
    have hClass :
        intClass (ZFSet.pair (natEncode A) (natEncode B)) =
          intNegativeForm n := by
      rw [intNegativeForm]
      apply (TA_PRO_00038_natEncode_class_eq_iff A B 0 n).mpr
      omega
    by_cases hn : n = 0
    · left
      rw [hxAB, hClass, hn]
      rfl
    · right
      right
      exact ⟨n, hn, hxAB.trans hClass⟩

theorem int_sign_normal_positive_unique
    {x : ZFSet} {m n : Nat}
    (hm : x = intPositiveForm m)
    (hn : x = intPositiveForm n) :
    m = n := by
  exact (intPositiveForm_eq_iff m n).mp (hm.symm.trans hn)

theorem int_sign_normal_negative_unique
    {x : ZFSet} {m n : Nat}
    (hm : x = intNegativeForm m)
    (hn : x = intNegativeForm n) :
    m = n := by
  exact (intNegativeForm_eq_iff m n).mp (hm.symm.trans hn)

theorem intPositiveForm_ne_zero
    {n : Nat} (hn : n ≠ 0) :
    intPositiveForm n ≠ intZero := by
  intro h
  exact hn ((intPositiveForm_eq_zero_iff n).mp h)

theorem intNegativeForm_ne_zero
    {n : Nat} (hn : n ≠ 0) :
    intNegativeForm n ≠ intZero := by
  intro h
  exact hn ((intNegativeForm_eq_zero_iff n).mp h)

/-- TA-THM-00025 — existencia local de exactamente una forma: cero,
positiva no nula o negativa no nula. -/
theorem TA_THM_00025_sign_normal_form :
    (∀ x : ZFSet,
      x ∈ integersTA →
      x = intZero ∨
      (∃ n : Nat, n ≠ 0 ∧ x = intPositiveForm n) ∨
      (∃ n : Nat, n ≠ 0 ∧ x = intNegativeForm n)) ∧
    (∀ x : ZFSet, ∀ m n : Nat,
      x = intPositiveForm m → x = intPositiveForm n → m = n) ∧
    (∀ x : ZFSet, ∀ m n : Nat,
      x = intNegativeForm m → x = intNegativeForm n → m = n) ∧
    (∀ n : Nat, n ≠ 0 → intPositiveForm n ≠ intZero) ∧
    (∀ n : Nat, n ≠ 0 → intNegativeForm n ≠ intZero) ∧
    (∀ m n : Nat, m ≠ 0 → n ≠ 0 →
      intPositiveForm m ≠ intNegativeForm n) := by
  exact ⟨fun _ => int_sign_normal_exists,
    fun _ _ _ => int_sign_normal_positive_unique,
    fun _ _ _ => int_sign_normal_negative_unique,
    fun _ => intPositiveForm_ne_zero,
    fun _ => intNegativeForm_ne_zero,
    fun _ _ => intPositiveForm_ne_negativeForm⟩

/-! ## Distinción de cero y uno -/

theorem TA_PRO_00046_zero_ne_one : intZero ≠ intOne := by
  intro h
  have hEq :
      intClass (ZFSet.pair (natEncode 0) (natEncode 0)) =
        intClass (ZFSet.pair (natEncode 1) (natEncode 0)) := by
    simpa [intZero, intOne] using h
  have := (TA_PRO_00038_natEncode_class_eq_iff 0 0 1 0).mp hEq
  omega

/-! ## Productos de formas con signo -/

theorem intMul_positive_positive
    {m n : Nat} {z : ZFSet}
    (hMul : IntMul (intPositiveForm m) (intPositiveForm n) z) :
    z = intPositiveForm (m * n) := by
  have hz :=
    (intMulGraph_natEncode_classes_value_iff
      (A := m) (B := 0) (C := n) (D := 0)).mp hMul
  simpa [intPositiveForm] using hz

theorem intMul_positive_negative
    {m n : Nat} {z : ZFSet}
    (hMul : IntMul (intPositiveForm m) (intNegativeForm n) z) :
    z = intNegativeForm (m * n) := by
  have hz :=
    (intMulGraph_natEncode_classes_value_iff
      (A := m) (B := 0) (C := 0) (D := n)).mp hMul
  simpa [intPositiveForm, intNegativeForm] using hz

theorem intMul_negative_positive
    {m n : Nat} {z : ZFSet}
    (hMul : IntMul (intNegativeForm m) (intPositiveForm n) z) :
    z = intNegativeForm (m * n) := by
  have hz :=
    (intMulGraph_natEncode_classes_value_iff
      (A := 0) (B := m) (C := n) (D := 0)).mp hMul
  simpa [intPositiveForm, intNegativeForm] using hz

theorem intMul_negative_negative
    {m n : Nat} {z : ZFSet}
    (hMul : IntMul (intNegativeForm m) (intNegativeForm n) z) :
    z = intPositiveForm (m * n) := by
  have hz :=
    (intMulGraph_natEncode_classes_value_iff
      (A := 0) (B := m) (C := 0) (D := n)).mp hMul
  simpa [intPositiveForm, intNegativeForm] using hz

theorem nat_mul_ne_zero_for_sign
    {m n : Nat}
    (hm : m ≠ 0)
    (hn : n ≠ 0) :
    m * n ≠ 0 := by
  exact Nat.mul_ne_zero hm hn

/-! ## TA-PRO-00047 — ausencia de divisores de cero -/

theorem TA_PRO_00047_no_zero_divisors
    {x y : ZFSet}
    (hx : x ∈ integersTA)
    (hy : y ∈ integersTA)
    (hMul : IntMul x y intZero) :
    x = intZero ∨ y = intZero := by
  rcases int_sign_normal_exists hx with hxZero | hxSigns
  · exact Or.inl hxZero
  · rcases int_sign_normal_exists hy with hyZero | hySigns
    · exact Or.inr hyZero
    · rcases hxSigns with hxPos | hxNeg
      · rcases hxPos with ⟨m, hm, hxForm⟩
        rcases hySigns with hyPos | hyNeg
        · rcases hyPos with ⟨n, hn, hyForm⟩
          rw [hxForm, hyForm] at hMul
          have hValue := intMul_positive_positive hMul
          have hmn := nat_mul_ne_zero_for_sign hm hn
          exfalso
          exact intPositiveForm_ne_zero hmn hValue.symm
        · rcases hyNeg with ⟨n, hn, hyForm⟩
          rw [hxForm, hyForm] at hMul
          have hValue := intMul_positive_negative hMul
          have hmn := nat_mul_ne_zero_for_sign hm hn
          exfalso
          exact intNegativeForm_ne_zero hmn hValue.symm
      · rcases hxNeg with ⟨m, hm, hxForm⟩
        rcases hySigns with hyPos | hyNeg
        · rcases hyPos with ⟨n, hn, hyForm⟩
          rw [hxForm, hyForm] at hMul
          have hValue := intMul_negative_positive hMul
          have hmn := nat_mul_ne_zero_for_sign hm hn
          exfalso
          exact intNegativeForm_ne_zero hmn hValue.symm
        · rcases hyNeg with ⟨n, hn, hyForm⟩
          rw [hxForm, hyForm] at hMul
          have hValue := intMul_negative_negative hMul
          have hmn := nat_mul_ne_zero_for_sign hm hn
          exfalso
          exact intPositiveForm_ne_zero hmn hValue.symm

theorem intMul_ne_zero_of_ne_zero
    {x y z : ZFSet}
    (hx : x ∈ integersTA)
    (hy : y ∈ integersTA)
    (hx0 : x ≠ intZero)
    (hy0 : y ≠ intZero)
    (hMul : IntMul x y z) :
    z ≠ intZero := by
  intro hz
  have hMulZero : IntMul x y intZero := by
    simpa [hz] using hMul
  have _hFunctional : z = intZero :=
    IntMul_unique hx hy hMul hMulZero
  rcases TA_PRO_00047_no_zero_divisors hx hy hMulZero with hxZero | hyZero
  · exact hx0 hxZero
  · exact hy0 hyZero

/-! ## TA-THM-00026 — paquete de dominio de integridad -/

/-- El paquete de anillo ya está certificado por
`TA_THM_00024_commutative_ring_package`; este resumen añade exactamente la
distinción `0 ≠ 1` y la ausencia de divisores de cero. -/
theorem TA_THM_00026_integral_domain_package :
    intZero ≠ intOne ∧
    (∀ x y : ZFSet,
      x ∈ integersTA → y ∈ integersTA →
      IntMul x y intZero → x = intZero ∨ y = intZero) := by
  exact ⟨TA_PRO_00046_zero_ne_one,
    fun _ _ => TA_PRO_00047_no_zero_divisors⟩

end TratadoAnalisis.Integers.Domain
