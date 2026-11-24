import Mathlib.Data.Nat.Basic

/-!
# TA-LEAN-0001 — Control de enunciados contra `Nat`

Esta capa es `lean-check`: verifica que enunciados seleccionados de TA-0004
coinciden con propiedades del objeto estándar `Nat`. No certifica la
construcción `ℕ = ω` del tratado.
-/

namespace TratadoAnalisis.Naturals.MathlibCheck

/-- Control del enunciado TA-THM-00014 sobre `Nat`. -/
theorem TA_THM_00014_mathlib_check (a b c : Nat) :
    (a + b) + c = a + (b + c) := by
  exact Nat.add_assoc a b c

/-- Control del enunciado TA-THM-00015 sobre `Nat`. -/
theorem TA_THM_00015_mathlib_check (a b : Nat) : a + b = b + a := by
  exact Nat.add_comm a b

end TratadoAnalisis.Naturals.MathlibCheck
