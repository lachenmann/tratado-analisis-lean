import TratadoAnalisis.Abstract.CompletenessManual0008

/-!
TA-LEAN-0008 — Etapa preparatoria para TA-PRO-00076.
Archivo experimental, independiente de los módulos canónicos.
Objetivo de este lote: certificar que la imagen por opuestos es un
subconjunto del cuerpo y que es no vacía cuando A lo es.

No afirma todavía la existencia del ínfimo.
El parámetro `em` declara explícitamente tercero excluido; no es Choice.
-/

namespace TratadoAnalisis.AbstractCompleteness.Manual0008

open TratadoAnalisis.Dedekind.FieldPredicates

/-- Los elementos de la imagen por opuestos pertenecen al portador. -/
theorem negativeImage_subset_manual
    (F zero A : ZFSet)
    (add : ZFSet → ZFSet → ZFSet → Prop) :
    NegativeImage F zero A add ⊆ F := by
  intro y hy
  have hyF := (mem_negativeImage_iff F zero A add y).mp hy
  exact hyF.1

/-- El opuesto local de un elemento de A pertenece a su imagen. -/
theorem opposite_mem_negativeImage_manual
    (F zero A : ZFSet)
    (add : ZFSet → ZFSet → ZFSet → Prop)
    (x nx : ZFSet)
    (hx : x ∈ A)
    (hneg : IsAdditiveOpposite F zero add x nx) :
    nx ∈ NegativeImage F zero A add := by
  exact (mem_negativeImage_iff F zero A add nx).mpr
    ⟨hneg.2.1, x, hx, hneg⟩

/-- Si A no es vacío y el cuerpo tiene inversos aditivos, -A no es vacío.
    La conversión de `A ≠ ∅` en testigo usa el parámetro explícito `em`.
    No se construye una función global que seleccione opuestos. -/
theorem negativeImage_ne_empty_manual
    (em : ∀ p : Prop, p ∨ ¬p)
    (F zero A : ZFSet)
    (add : ZFSet → ZFSet → ZFSet → Prop)
    (hA : A ⊆ F)
    (hne : A ≠ ∅)
    (hgroup : IsAbelianGroupFoundational F zero add) :
    NegativeImage F zero A add ≠ ∅ := by
  have hex : ∃ x : ZFSet, x ∈ A := by
    rcases em (∃ x : ZFSet, x ∈ A) with hx | hnot
    · exact hx
    · have hzero : A = ∅ := by
        apply (ZFSet.eq_empty A).mpr
        intro x hx
        exact hnot ⟨x, hx⟩
      exact False.elim (hne hzero)
  obtain ⟨x, hx⟩ := hex
  have hxF : x ∈ F := hA hx
  obtain ⟨_, _, _, _, _, hinv⟩ := hgroup
  obtain ⟨nx, hnxF, hxn, hnx⟩ := hinv x hxF
  have hneg : IsAdditiveOpposite F zero add x nx :=
    ⟨hxF, hnxF, hxn, hnx⟩
  have hnxA : nx ∈ NegativeImage F zero A add :=
    opposite_mem_negativeImage_manual F zero A add x nx hx hneg
  intro hzero
  rw [hzero] at hnxA
  exact ZFSet.notMem_empty nx hnxA

#check negativeImage_subset_manual
#print axioms negativeImage_subset_manual
#check opposite_mem_negativeImage_manual
#print axioms opposite_mem_negativeImage_manual
#check negativeImage_ne_empty_manual
#print axioms negativeImage_ne_empty_manual

end TratadoAnalisis.AbstractCompleteness.Manual0008
