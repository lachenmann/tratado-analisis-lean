import Mathlib.Data.Set.Defs
import Mathlib.Logic.ExistsUnique

/-!
MA-Lean v0.3 — TA-0003, formalizaciones candidatas sobre Set α.
Nivel: lean-check. NO reconstruye el vacío de ZF desde infinito,
separación y extensionalidad; utiliza el vacío ya definido en Lean.
Revisión semántica y axiomática: pendientes hasta aprobación expresa.
-/

namespace MALean.Chapter0

-- TA-PRO-00003: existe un único subconjunto sin elementos de α.
theorem TA_PRO_00003_empty_exists_unique {α : Type*} :
    ∃! E : Set α, ∀ x : α, x ∉ E := by
  refine ⟨∅, ?_, ?_⟩
  · intro x hx
    exact hx
  · intro E hE
    apply Set.ext
    intro x
    constructor
    · intro hx
      exact False.elim (hE x hx)
    · intro hx
      exact False.elim hx

-- TA-PRO-00004: el subconjunto vacío de α está contenido en cualquiera.
theorem TA_PRO_00004_empty_subset {α : Type*} (A : Set α) :
    (∅ : Set α) ⊆ A := by
  intro x hx
  exact False.elim hx

end MALean.Chapter0
