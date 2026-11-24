/-!
# TA-LEAN-0001 — Verificación estructural de TA-0004

Esta capa NO identifica `TANat` con los naturales conjuntistas del tratado.
Sirve para certificar la forma recursiva y las pruebas algebraicas de TA-0004
sin reutilizar los teoremas aritméticos de `Nat`/mathlib.
-/

namespace TratadoAnalisis.Naturals.Structural

inductive TANat where
  | zero : TANat
  | succ : TANat → TANat
  deriving DecidableEq, Repr

open TANat

/-- Correspondencia estructural con TA-DEF-00036. Recursión en el segundo argumento. -/
def add : TANat → TANat → TANat
  | m, zero => m
  | m, succ n => succ (add m n)

/-- TA-PRO-00025 — Cero neutro por la izquierda. -/
theorem TA_PRO_00025_zero_left (n : TANat) : add zero n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [add, ih]

/-- TA-LEM-00006 — Sucesor en el primer argumento. -/
theorem TA_LEM_00006_succ_left (m n : TANat) :
    add (succ m) n = succ (add m n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [add, ih]

/-- TA-THM-00014 — Asociatividad de la suma. -/
theorem TA_THM_00014_add_assoc (a b c : TANat) :
    add (add a b) c = add a (add b c) := by
  induction c with
  | zero => rfl
  | succ c ih =>
      simp [add, ih]

/-- TA-THM-00015 — Conmutatividad de la suma. -/
theorem TA_THM_00015_add_comm (a b : TANat) : add a b = add b a := by
  induction b with
  | zero =>
      simpa [add] using (TA_PRO_00025_zero_left a).symm
  | succ b ih =>
      calc
        add a (succ b) = succ (add a b) := rfl
        _ = succ (add b a) := congrArg succ ih
        _ = add (succ b) a := (TA_LEM_00006_succ_left b a).symm

end TratadoAnalisis.Naturals.Structural
