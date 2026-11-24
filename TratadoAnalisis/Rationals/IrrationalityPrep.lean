import TratadoAnalisis.Rationals.StrictOrder
import TratadoAnalisis.Naturals.ArithmeticBridge

namespace TratadoAnalisis.Rationals.IrrationalityPrep

open TratadoAnalisis.Naturals.Foundational
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Naturals.ArithmeticBridge

/-! # E1a — infraestructura de paridad natural

`Nat` se usa sólo como coordenada del puente certificado `natEncode`. Los
predicados `EvenOmegaTA` y `OddOmegaTA` registran explícitamente su transporte
a los naturales conjuntistas del tratado.
-/

/-! ## TA-DEF-00065 — paridad -/

def EvenTA (n : Nat) : Prop :=
  ∃ k : Nat, n = 2 * k

def OddTA (n : Nat) : Prop :=
  ∃ k : Nat, n = 2 * k + 1

def EvenOmegaTA (x : ZFSet) : Prop :=
  ∃ k : Nat, x = natEncode (2 * k)

def OddOmegaTA (x : ZFSet) : Prop :=
  ∃ k : Nat, x = natEncode (2 * k + 1)

theorem evenOmegaTA_natEncode_iff (n : Nat) :
    EvenOmegaTA (natEncode n) ↔ EvenTA n := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, natEncode_injective hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, congrArg natEncode hk⟩

theorem oddOmegaTA_natEncode_iff (n : Nat) :
    OddOmegaTA (natEncode n) ↔ OddTA n := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, natEncode_injective hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, congrArg natEncode hk⟩

theorem evenTA_not_oddTA {n : Nat}
    (he : EvenTA n) (ho : OddTA n) : False := by
  rcases he with ⟨k, hk⟩
  rcases ho with ⟨l, hl⟩
  omega

theorem parity_cover : ∀ n : Nat, EvenTA n ∨ OddTA n
  | 0 => Or.inl ⟨0, rfl⟩
  | n + 1 => by
      rcases parity_cover n with hn | hn
      · right
        rcases hn with ⟨k, hk⟩
        exact ⟨k, congrArg (fun t : Nat => t + 1) hk⟩
      · left
        rcases hn with ⟨k, hk⟩
        refine ⟨k + 1, ?_⟩
        calc
          n + 1 = (2 * k + 1) + 1 := congrArg (fun t : Nat => t + 1) hk
          _ = 2 * (k + 1) := by
            simp [Nat.mul_succ, Nat.add_assoc]

/-! ## TA-LEM-00016 — dicotomía exclusiva de paridad -/

theorem TA_LEM_00016_parity_dichotomy (n : Nat) :
    (EvenTA n ∨ OddTA n) ∧ ¬ (EvenTA n ∧ OddTA n) := by
  refine ⟨parity_cover n, ?_⟩
  rintro ⟨he, ho⟩
  exact evenTA_not_oddTA he ho

theorem oddTA_square {n : Nat} (h : OddTA n) : OddTA (n * n) := by
  rcases h with ⟨k, rfl⟩
  refine ⟨2 * k * k + 2 * k, ?_⟩
  have hTwoMul (a : Nat) : 2 * a = a + a := by
    calc
      2 * a = (1 + 1) * a := by rfl
      _ = 1 * a + 1 * a := Nat.add_mul 1 1 a
      _ = a + a := by simp only [Nat.one_mul]
  have hSquare : (2 * k) * (2 * k) = 2 * (2 * k * k) := by
    ac_rfl
  calc
    (2 * k + 1) * (2 * k + 1) =
        (2 * k) * (2 * k) + 2 * k + 2 * k + 1 := by
      rw [Nat.add_mul, Nat.mul_add]
      simp only [Nat.mul_one, Nat.one_mul]
      ac_rfl
    _ = 2 * (2 * k * k) + 2 * (2 * k) + 1 := by
      rw [hSquare, hTwoMul (2 * k)]
      ac_rfl
    _ = 2 * (2 * k * k + 2 * k) + 1 := by
      rw [Nat.mul_add]

/-! ## TA-LEM-00017 — cuadrado par implica raíz par -/

theorem TA_LEM_00017_even_square_implies_even
    {n : Nat}
    (h : EvenTA (n * n)) :
    EvenTA n := by
  rcases TA_LEM_00016_parity_dichotomy n with ⟨hn, _⟩
  rcases hn with hnEven | hnOdd
  · exact hnEven
  · have hnSquareOdd : OddTA (n * n) := oddTA_square hnOdd
    have hExclusive := (TA_LEM_00016_parity_dichotomy (n * n)).2
    exact False.elim (hExclusive ⟨h, hnSquareOdd⟩)

end TratadoAnalisis.Rationals.IrrationalityPrep
