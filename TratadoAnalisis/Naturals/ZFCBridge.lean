import Mathlib.SetTheory.ZFC.Basic

/-!
# TA-LEAN-0001 — Puente inicial hacia ZFC

Esta capa usa el modelo `ZFSet` de mathlib. Es un puente fundacional:
certifica que el `ω` disponible en `Mathlib.SetTheory.ZFC.Basic` contiene
el vacío y es cerrado bajo el sucesor de von Neumann `x ↦ x ∪ {x}`.

No sustituye todavía nuestra construcción completa de TA-0004: en
TA-LEAN-0001 reutilizamos `ZFSet.omega` de mathlib en vez de reconstruirlo
mediante la intersección/núcleo de todos los inductivos pertinentes.
-/

namespace TratadoAnalisis.Naturals.ZFCBridge

open ZFSet

/-- Correspondencia con TA-DEF-00030: sucesor de von Neumann. -/
def zfcSucc (x : ZFSet) : ZFSet := insert x x

/-- Versión ZFC de la propiedad «ser inductivo». -/
def IsInductive (I : ZFSet) : Prop :=
  (∅ : ZFSet) ∈ I ∧ ∀ x : ZFSet, x ∈ I → zfcSucc x ∈ I

/-- Puente para TA-PRO-00019/TA-NOT-00007: `ZFSet.omega` es inductivo. -/
theorem TA_LEAN_OMEGA_isInductive : IsInductive ZFSet.omega := by
  constructor
  · exact ZFSet.omega_zero
  · intro x hx
    exact ZFSet.omega_succ hx

/-- Componente de cero del puente ZFC. -/
theorem TA_NOT_00006_zero_mem_omega : (∅ : ZFSet) ∈ ZFSet.omega := by
  exact ZFSet.omega_zero

/-- Componente de sucesor del puente ZFC. -/
theorem TA_DEF_00030_succ_mem_omega {n : ZFSet} (hn : n ∈ ZFSet.omega) :
    zfcSucc n ∈ ZFSet.omega := by
  exact ZFSet.omega_succ hn

end TratadoAnalisis.Naturals.ZFCBridge
