import TratadoAnalisis.Integers.Order
import TratadoAnalisis.Abstract.PrimeGridLeastIndex0009
import TratadoAnalisis.Abstract.ArchimedeanEditorialBridge0008

/-!
# Aritmética y orden de los naturales conjuntistas

Los grafos fundacionales de suma y producto permanecen intactos.
Los códigos Nat se utilizan como testigos locales y no como sustitución
del portador omegaTA. No se construye una inversa global de natEncode.
-/

namespace TratadoAnalisis.Naturals.OrderedArithmetic

universe u

open TratadoAnalisis.Naturals.Foundational
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Naturals.ArithmeticBridge
open TratadoAnalisis.Integers.Order
open TratadoAnalisis.Dedekind.FieldPredicates
open TratadoAnalisis.AbstractCompleteness.Manual0008
open TratadoAnalisis.AbstractCompleteness.Density0009

/-- Lectura relacional del grafo canónico de suma. -/
abbrev NatAddRel (a b c : ZFSet.{u}) : Prop :=
  ZFSet.pair (ZFSet.pair a b) c ∈ natAddGraph

/-- Lectura relacional del grafo canónico de producto. -/
abbrev NatMulRel (a b c : ZFSet.{u}) : Prop :=
  ZFSet.pair (ZFSet.pair a b) c ∈ natMulGraph

/-- TA-THM-00016: distributividad del producto en el segundo factor.
    Los valores de todas las operaciones están fijados por los grafos. -/
theorem TA_THM_00016_mul_add
    {a b c bc ab ac lhs rhs : ZFSet.{u}}
    (ha : a ∈ omegaTA) (hb : b ∈ omegaTA) (hc : c ∈ omegaTA)
    (hbc : NatAddRel b c bc)
    (hab : NatMulRel a b ab) (hac : NatMulRel a c ac)
    (hl : NatMulRel a bc lhs) (hr : NatAddRel ab ac rhs) :
    lhs = rhs := by
  obtain ⟨A, rfl⟩ := exists_natEncode_eq_of_mem ha
  obtain ⟨B, rfl⟩ := exists_natEncode_eq_of_mem hb
  obtain ⟨C, rfl⟩ := exists_natEncode_eq_of_mem hc
  have ebc := natAddGraph_natEncode_value_iff.mp hbc
  have eab := natMulGraph_natEncode_value_iff.mp hab
  have eac := natMulGraph_natEncode_value_iff.mp hac
  subst bc
  subst ab
  subst ac
  have el := natMulGraph_natEncode_value_iff.mp hl
  have er := natAddGraph_natEncode_value_iff.mp hr
  exact el.trans ((congrArg (fun n : Nat => (natEncode n : ZFSet.{u}))
    (Nat.mul_add A B C)).trans er.symm)

/-- TA-THM-00017: asociatividad del producto conjuntista. -/
theorem TA_THM_00017_mul_assoc
    {a b c ab bc lhs rhs : ZFSet.{u}}
    (ha : a ∈ omegaTA) (hb : b ∈ omegaTA) (hc : c ∈ omegaTA)
    (hab : NatMulRel a b ab) (hbc : NatMulRel b c bc)
    (hl : NatMulRel ab c lhs) (hr : NatMulRel a bc rhs) :
    lhs = rhs := by
  obtain ⟨A, rfl⟩ := exists_natEncode_eq_of_mem ha
  obtain ⟨B, rfl⟩ := exists_natEncode_eq_of_mem hb
  obtain ⟨C, rfl⟩ := exists_natEncode_eq_of_mem hc
  have eab := natMulGraph_natEncode_value_iff.mp hab
  have ebc := natMulGraph_natEncode_value_iff.mp hbc
  subst ab
  subst bc
  have el := natMulGraph_natEncode_value_iff.mp hl
  have er := natMulGraph_natEncode_value_iff.mp hr
  exact el.trans ((congrArg (fun n : Nat => (natEncode n : ZFSet.{u}))
    (Nat.mul_assoc A B C)).trans er.symm)

/-- TA-THM-00018: conmutatividad del producto conjuntista. -/
theorem TA_THM_00018_mul_comm
    {a b ab ba : ZFSet.{u}}
    (ha : a ∈ omegaTA) (hb : b ∈ omegaTA)
    (hab : NatMulRel a b ab) (hba : NatMulRel b a ba) :
    ab = ba := by
  obtain ⟨A, rfl⟩ := exists_natEncode_eq_of_mem ha
  obtain ⟨B, rfl⟩ := exists_natEncode_eq_of_mem hb
  have el := natMulGraph_natEncode_value_iff.mp hab
  have er := natMulGraph_natEncode_value_iff.mp hba
  exact el.trans ((congrArg (fun n : Nat => (natEncode n : ZFSet.{u}))
    (Nat.mul_comm A B)).trans er.symm)

/-- TA-THM-00019: totalidad del orden aritmético de TA-DEF-00038. -/
theorem TA_THM_00019_nat_total
    {a b : ZFSet.{u}} (ha : a ∈ omegaTA) (hb : b ∈ omegaTA) :
    NatLETA a b ∨ NatLETA b a := by
  obtain ⟨A, rfl⟩ := exists_natEncode_eq_of_mem ha
  obtain ⟨B, rfl⟩ := exists_natEncode_eq_of_mem hb
  rcases Nat.le_total A B with h | h
  · exact Or.inl ((NatLETA_natEncode_iff A B).mpr h)
  · exact Or.inr ((NatLETA_natEncode_iff B A).mpr h)

/-- TA-THM-00020: orden total en el portador conjuntista de naturales. -/
theorem TA_THM_00020_nat_total_order :
    IsTotalOrderFoundational (omegaTA : ZFSet.{u}) NatLETA := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨A, rfl⟩ := exists_natEncode_eq_of_mem ha
    exact (NatLETA_natEncode_iff A A).mpr (Nat.le_refl A)
  · intro a b ha hb hab hba
    obtain ⟨A, rfl⟩ := exists_natEncode_eq_of_mem ha
    obtain ⟨B, rfl⟩ := exists_natEncode_eq_of_mem hb
    exact congrArg (fun n : Nat => (natEncode n : ZFSet.{u}))
      (Nat.le_antisymm ((NatLETA_natEncode_iff A B).mp hab)
        ((NatLETA_natEncode_iff B A).mp hba))
  · intro a b c ha hb hc hab hbc
    obtain ⟨A, rfl⟩ := exists_natEncode_eq_of_mem ha
    obtain ⟨B, rfl⟩ := exists_natEncode_eq_of_mem hb
    obtain ⟨C, rfl⟩ := exists_natEncode_eq_of_mem hc
    exact (NatLETA_natEncode_iff A C).mpr
      (Nat.le_trans ((NatLETA_natEncode_iff A B).mp hab)
        ((NatLETA_natEncode_iff B C).mp hbc))
  · intro a b ha hb
    exact TA_THM_00019_nat_total ha hb

/-- El orden estricto de códigos corresponde a la pertenencia de sus
    representaciones de von Neumann. -/
theorem natEncode_mem_natEncode_iff (a b : Nat) :
    (natEncode a : ZFSet.{u}) ∈ natEncode b ↔ a < b := by
  induction b with
  | zero =>
      constructor
      · intro h
        exact (ZFSet.notMem_empty (natEncode a) h).elim
      · intro h
        omega
  | succ b ih =>
      change (natEncode a : ZFSet.{u}) ∈ insert (natEncode b) (natEncode b) ↔
        a < b.succ
      rw [ZFSet.mem_insert_iff, ih]
      constructor
      · rintro (h | h)
        · have he := natEncode_injective h
          omega
        · omega
      · intro h
        by_cases he : a = b
        · exact Or.inl (congrArg (fun n : Nat => (natEncode n : ZFSet.{u})) he)
        · exact Or.inr (by omega)

/-- El orden estricto editorial es exactamente el estricto de los códigos. -/
theorem natEncode_strict_iff (a b : Nat) :
    StrictFromLeManual NatLETA (natEncode a : ZFSet.{u}) (natEncode b) ↔
      a < b := by
  constructor
  · rintro ⟨hle, hne⟩
    have h := (NatLETA_natEncode_iff a b).mp hle
    have he : a ≠ b := fun e => hne
      (congrArg (fun n : Nat => (natEncode n : ZFSet.{u})) e)
    omega
  · intro h
    exact ⟨(NatLETA_natEncode_iff a b).mpr (by omega),
      fun e => (Nat.ne_of_lt h) (natEncode_injective e)⟩

/-- TA-THM-00021: m < n si y solo si m pertenece a n. -/
theorem TA_THM_00021_strict_iff_mem
    {a b : ZFSet.{u}} (ha : a ∈ omegaTA) (hb : b ∈ omegaTA) :
    StrictFromLeManual NatLETA a b ↔ a ∈ b := by
  obtain ⟨A, rfl⟩ := exists_natEncode_eq_of_mem ha
  obtain ⟨B, rfl⟩ := exists_natEncode_eq_of_mem hb
  exact (natEncode_strict_iff A B).trans (natEncode_mem_natEncode_iff A B).symm

/-- TA-PRO-00428: se reúnen las dos pruebas previamente disponibles.
    No se repite la inducción. -/
theorem TA_PRO_00428_nat_subset_and_zero_mem_succ
    {n : ZFSet.{u}} (hn : n ∈ omegaTA) :
    n ⊆ omegaTA ∧ (∅ : ZFSet.{u}) ∈ succ n :=
  ⟨fun k hk => omega_member_of_member_nat_manual n hn k hk,
    zero_mem_succ_of_nat hn⟩

/-- TA-THM-00022: buen orden para subconjuntos conjuntistas no vacíos.
    El tercero excluido es explícito; se reutiliza el mínimo por pertenencia. -/
theorem TA_THM_00022_nat_well_order
    (em : ∀ p : Prop, p ∨ ¬p)
    (A : ZFSet.{u}) (hA : A ⊆ omegaTA) (hne : A ≠ ∅) :
    ∃ m : ZFSet.{u}, m ∈ A ∧ ∀ x : ZFSet.{u}, x ∈ A → NatLETA m x := by
  have hExists : ∃ x : ZFSet.{u}, x ∈ A := by
    rcases em (∃ x : ZFSet.{u}, x ∈ A) with h | h
    · exact h
    · exfalso
      apply hne
      apply ZFSet.ext
      intro x
      exact ⟨fun hx => (h ⟨x, hx⟩).elim,
        fun hx => (ZFSet.notMem_empty x hx).elim⟩
  obtain ⟨n, hn⟩ := hExists
  obtain ⟨m, hmNat, hm, hmin⟩ :=
    omega_least_manual em (fun x => x ∈ A) ⟨n, hA hn, hn⟩
  refine ⟨m, hm, ?_⟩
  intro x hx
  have hxNat := hA hx
  rcases TA_THM_00019_nat_total hmNat hxNat with h | h
  · exact h
  · rcases em (x = m) with he | he
    · rw [he]
      exact TA_THM_00020_nat_total_order.1 m hmNat
    · have hmem := (TA_THM_00021_strict_iff_mem hxNat hmNat).mp ⟨h, he⟩
      exact (hmin x hmem hx).elim

/-- TA-PRO-00170: tricotomía proposicional con exclusión mutua.
    No se afirma una instancia DecidableEq sobre ZFSet arbitrarios. -/
theorem TA_PRO_00170_nat_trichotomy
    {a b : ZFSet.{u}} (ha : a ∈ omegaTA) (hb : b ∈ omegaTA) :
    (StrictFromLeManual NatLETA a b ∨ a = b ∨ StrictFromLeManual NatLETA b a) ∧
    ¬ (StrictFromLeManual NatLETA a b ∧ a = b) ∧
    ¬ (StrictFromLeManual NatLETA a b ∧ StrictFromLeManual NatLETA b a) ∧
    ¬ (a = b ∧ StrictFromLeManual NatLETA b a) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨A, rfl⟩ := exists_natEncode_eq_of_mem ha
    obtain ⟨B, rfl⟩ := exists_natEncode_eq_of_mem hb
    rcases Nat.lt_trichotomy A B with h | h | h
    · exact Or.inl ((natEncode_strict_iff A B).mpr h)
    · exact Or.inr (Or.inl (congrArg (fun n : Nat => (natEncode n : ZFSet.{u})) h))
    · exact Or.inr (Or.inr ((natEncode_strict_iff B A).mpr h))
  · rintro ⟨h, he⟩
    exact h.2 he
  · rintro ⟨h, h'⟩
    exact h.2 (TA_THM_00020_nat_total_order.2.1 a b ha hb h.1 h'.1)
  · rintro ⟨he, h⟩
    exact h.2 he.symm

/-- Comparación recursiva ejecutable sobre códigos naturales suministrados. -/
def compareNatCodes : Nat → Nat → Ordering
  | 0, 0 => .eq
  | 0, _ + 1 => .lt
  | _ + 1, 0 => .gt
  | a + 1, b + 1 => compareNatCodes a b

/-- Corrección de la comparación recursiva, antes del transporte. -/
theorem compareNatCodes_spec (a b : Nat) :
    (compareNatCodes a b = .lt ↔ a < b) ∧
    (compareNatCodes a b = .eq ↔ a = b) ∧
    (compareNatCodes a b = .gt ↔ b < a) := by
  induction a generalizing b with
  | zero => cases b <;> simp [compareNatCodes]
  | succ a ih =>
      cases b with
      | zero => simp [compareNatCodes]
      | succ b => simpa [compareNatCodes] using ih b

/-- TA-PRO-00170: el algoritmo de códigos clasifica exactamente el orden
    de los naturales conjuntistas codificados. No extrae códigos de ZFSet. -/
theorem TA_PRO_00170_compare_codes_spec (a b : Nat) :
    (compareNatCodes a b = .lt ↔
      StrictFromLeManual NatLETA (natEncode a : ZFSet.{u}) (natEncode b)) ∧
    (compareNatCodes a b = .eq ↔ (natEncode a : ZFSet.{u}) = natEncode b) ∧
    (compareNatCodes a b = .gt ↔
      StrictFromLeManual NatLETA (natEncode b : ZFSet.{u}) (natEncode a)) := by
  have h := compareNatCodes_spec a b
  refine ⟨h.1.trans (natEncode_strict_iff a b).symm, ?_,
    h.2.2.trans (natEncode_strict_iff b a).symm⟩
  exact h.2.1.trans ⟨fun e =>
    congrArg (fun n : Nat => (natEncode n : ZFSet.{u})) e,
    fun e => natEncode_injective e⟩

end TratadoAnalisis.Naturals.OrderedArithmetic
