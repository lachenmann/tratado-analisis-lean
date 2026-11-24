import TratadoAnalisis.Dedekind.Order

namespace TratadoAnalisis.Dedekind.ClassicalWrappers

open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Dedekind.Definition

/-!
# Envoltorios clásicos de TA-LEAN-0004 F

Solo esta capa instancia em. Classical.choice en su footprint es metateórico
(Diaconescu); set-theoretic-choice: none.
Los capítulos posteriores deben importar Order y usar las versiones con em.
-/

/-- Envoltorio de la extracción clásica de un testigo de diferencia. -/
theorem subset_failure_witness {A B : ZFSet} (h : ¬ A ⊆ B) :
    ∃ a : ZFSet, a ∈ A ∧ a ∉ B :=
  Order.subset_failure_witness Classical.em h

/-- TA-THM-00040, versión clásica sin hipótesis em. -/
theorem TA_THM_00040_dedLE_total_classical {α β : ZFSet}
    (hα : α ∈ dedekindCutsTA) (hβ : β ∈ dedekindCutsTA) :
    DedLE α β ∨ DedLE β α :=
  Order.TA_THM_00040_dedLE_total Classical.em hα hβ

/-- TA-THM-00040, paquete clásico sin hipótesis em. -/
theorem TA_THM_00040_total_order_package_classical :
    (∀ α : ZFSet, α ∈ dedekindCutsTA → DedLE α α) ∧
    (∀ α β : ZFSet, α ∈ dedekindCutsTA → β ∈ dedekindCutsTA →
      DedLE α β → DedLE β α → α = β) ∧
    (∀ α β γ : ZFSet, α ∈ dedekindCutsTA → β ∈ dedekindCutsTA →
      γ ∈ dedekindCutsTA → DedLE α β → DedLE β γ → DedLE α γ) ∧
    (∀ α β : ZFSet, α ∈ dedekindCutsTA → β ∈ dedekindCutsTA →
      DedLE α β ∨ DedLE β α) :=
  Order.TA_THM_00040_total_order_package Classical.em

theorem cut_inhabited {α : ZFSet}
    (hα : IsDedekindCut α) : ∃ r : ZFSet, r ∈ α :=
  Order.cut_inhabited Classical.em hα

theorem cut_exterior_inhabited {α : ZFSet}
    (hα : IsDedekindCut α) :
    ∃ r : ZFSet, r ∈ rationalsTA ∧ r ∉ α :=
  Order.cut_exterior_inhabited Classical.em hα

end TratadoAnalisis.Dedekind.ClassicalWrappers

