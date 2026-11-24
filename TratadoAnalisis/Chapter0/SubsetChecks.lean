/-
  MA-Lean v0.1: borrador de correspondencias para TA-0003.
  Propuesta NO compilada ni cotejada semánticamente en esta entrega.
  Este archivo trabaja con Set α de Lean, NO demuestra aún los axiomas
  ni la construcción ZF exacta descrita en el tratado.
  No se añade al proyecto canónico ni al registro LEAN_VERIFICATION_REGISTRY.md.
-/
import Mathlib.Data.Set.Defs

namespace MALean.Chapter0

-- TA-PRO-00001 — reflexividad de la inclusión (solo lean-check propuesto)
theorem TA_PRO_00001_subset_refl {α : Type*} (A : Set α) : A ⊆ A := by
  intro x hx
  exact hx

-- TA-PRO-00002 — transitividad de la inclusión (solo lean-check propuesto)
theorem TA_PRO_00002_subset_trans {α : Type*} (A B C : Set α)
    (hab : A ⊆ B) (hbc : B ⊆ C) : A ⊆ C := by
  intro x hx
  exact hbc (hab hx)

-- TA-THM-00001 — criterio de igualdad por doble inclusión (lean-check propuesto)
theorem TA_THM_00001_subset_antisymm {α : Type*} (A B : Set α) :
    (A = B ↔ A ⊆ B ∧ B ⊆ A) := by
  constructor
  · intro h
    subst B
    exact ⟨(fun _ hx => hx), (fun _ hx => hx)⟩
  · intro h
    apply Set.ext
    intro x
    exact ⟨(fun hx => h.1 hx), (fun hx => h.2 hx)⟩

#print axioms MALean.Chapter0.TA_PRO_00001_subset_refl
#print axioms MALean.Chapter0.TA_PRO_00002_subset_trans
#print axioms MALean.Chapter0.TA_THM_00001_subset_antisymm

end MALean.Chapter0
