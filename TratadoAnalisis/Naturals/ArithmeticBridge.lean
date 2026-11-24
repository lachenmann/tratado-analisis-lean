import TratadoAnalisis.Naturals.Recursion

namespace TratadoAnalisis.Naturals.ArithmeticBridge

open TratadoAnalisis.Naturals.Foundational
open TratadoAnalisis.Naturals.Recursion

/-! # Puente aritmético natural mínimo

`Nat` se usa sólo como sistema externo de índices. La codificación en
`omegaTA` no define una inversa global, y las correspondencias aritméticas
evalúan los grafos fundacionales ya construidos sin redefinirlos.
-/

/-- Codificación recursiva de los naturales de Lean en los naturales
conjuntistas del tratado. -/
def natEncode : Nat → ZFSet
  | 0 => ∅
  | n + 1 => succ (natEncode n)

@[simp]
theorem natEncode_zero :
    natEncode 0 = (∅ : ZFSet) := rfl

@[simp]
theorem natEncode_succ (n : Nat) :
    natEncode (n + 1) = succ (natEncode n) := rfl

/-- Toda codificación externa pertenece a `omegaTA`. -/
theorem natEncode_mem_omegaTA (n : Nat) :
    natEncode n ∈ omegaTA := by
  induction n with
  | zero =>
      exact omegaTA_isInductive.1
  | succ n ih =>
      exact TA_PRO_00022_succ_closed ih

/-- La codificación externa es inyectiva. -/
theorem natEncode_injective :
    Function.Injective natEncode := by
  intro m
  induction m with
  | zero =>
      intro n h
      cases n with
      | zero => rfl
      | succ n =>
          have hne : succ (natEncode n) ≠ (∅ : ZFSet) :=
            TA_PRO_00023_succ_ne_zero (natEncode n)
          exact (hne h.symm).elim
  | succ m ih =>
      intro n h
      cases n with
      | zero =>
          have hne : succ (natEncode m) ≠ (∅ : ZFSet) :=
            TA_PRO_00023_succ_ne_zero (natEncode m)
          exact (hne h).elim
      | succ n =>
          have hmnEncode : natEncode m = natEncode n :=
            TA_THM_00009_succ_injective
              (natEncode_mem_omegaTA m)
              (natEncode_mem_omegaTA n)
              h
          exact congrArg Nat.succ (ih hmnEncode)

/-- Cada elemento de `omegaTA` admite localmente un código `Nat`.
No se seleccionan simultáneamente códigos ni se define una inversa global. -/
theorem exists_natEncode_eq_of_mem
    {x : ZFSet}
    (hx : x ∈ omegaTA) :
    ∃ n : Nat, natEncode n = x := by
  let P : ZFSet → Prop := fun y =>
    ∃ n : Nat, natEncode n = y

  have h0 : P (∅ : ZFSet) := by
    exact ⟨0, rfl⟩

  have hs :
      ∀ y : ZFSet,
        y ∈ omegaTA →
        P y →
        P (succ y) := by
    intro y _hy ⟨n, hn⟩
    refine ⟨n + 1, ?_⟩
    rw [natEncode_succ, hn]

  exact TA_THM_00008_induction P h0 hs x hx

/-- Evaluación del grafo fundacional de suma sobre códigos externos.
La recursión es sobre `n`; `Nat.add` sólo normaliza el lado externo. -/
theorem natAddGraph_natEncode (m n : Nat) :
    ZFSet.pair
      (ZFSet.pair (natEncode m) (natEncode n))
      (natEncode (m + n)) ∈ natAddGraph := by
  induction n with
  | zero =>
      simpa using natAddGraph_zero (natEncode_mem_omegaTA m)
  | succ n ih =>
      have hSucc :=
        natAddGraph_succ
          (natEncode_mem_omegaTA m)
          (natEncode_mem_omegaTA n)
          ih
      simpa only [Nat.add_succ, natEncode_succ] using hSucc

/-- Un valor del grafo de suma sobre entradas codificadas es exactamente
el código de la suma externa correspondiente. -/
theorem natAddGraph_natEncode_value_iff
    {m n : Nat} {z : ZFSet} :
    ZFSet.pair
      (ZFSet.pair (natEncode m) (natEncode n))
      z ∈ natAddGraph ↔
    z = natEncode (m + n) := by
  constructor
  · intro hAdd
    have hmnDom :
        ZFSet.pair (natEncode m) (natEncode n) ∈
          cartesianProductFoundational omegaTA omegaTA :=
      mem_cartesianProductFoundational.mpr
        ⟨natEncode_mem_omegaTA m, natEncode_mem_omegaTA n⟩
    exact funcFoundational_pair_value_unique
      natAddGraph_isFunc hmnDom hAdd (natAddGraph_natEncode m n)
  · intro hz
    rw [hz]
    exact natAddGraph_natEncode m n

/-- Evaluación del grafo fundacional de multiplicación sobre códigos
externos. El paso usa `(m*n)+m`, en el orden requerido por `natMulGraph`. -/
theorem natMulGraph_natEncode (m n : Nat) :
    ZFSet.pair
      (ZFSet.pair (natEncode m) (natEncode n))
      (natEncode (m * n)) ∈ natMulGraph := by
  induction n with
  | zero =>
      simpa using natMulGraph_zero (natEncode_mem_omegaTA m)
  | succ n ih =>
      have hAdd :
          ZFSet.pair
            (ZFSet.pair (natEncode (m * n)) (natEncode m))
            (natEncode ((m * n) + m)) ∈ natAddGraph :=
        natAddGraph_natEncode (m * n) m
      have hSucc :=
        natMulGraph_succ
          (natEncode_mem_omegaTA m)
          (natEncode_mem_omegaTA n)
          ih
          hAdd
      simpa only [Nat.mul_succ, natEncode_succ] using hSucc

/-- Un valor del grafo de multiplicación sobre entradas codificadas es
exactamente el código del producto externo correspondiente. -/
theorem natMulGraph_natEncode_value_iff
    {m n : Nat} {z : ZFSet} :
    ZFSet.pair
      (ZFSet.pair (natEncode m) (natEncode n))
      z ∈ natMulGraph ↔
    z = natEncode (m * n) := by
  constructor
  · intro hMul
    have hmnDom :
        ZFSet.pair (natEncode m) (natEncode n) ∈
          cartesianProductFoundational omegaTA omegaTA :=
      mem_cartesianProductFoundational.mpr
        ⟨natEncode_mem_omegaTA m, natEncode_mem_omegaTA n⟩
    exact funcFoundational_pair_value_unique
      natMulGraph_isFunc hmnDom hMul (natMulGraph_natEncode m n)
  · intro hz
    rw [hz]
    exact natMulGraph_natEncode m n

end TratadoAnalisis.Naturals.ArithmeticBridge
