import TratadoAnalisis.Abstract.NumeralImageCore0008
import TratadoAnalisis.Naturals.Recursion

/-!
# TA-LEAN-0008 — Etapa 5A (candidato, no compilado)

Construcción por Separación del grafo del operador x ↦ x + 1 dentro de F.
Los resultados son relacionales: no se escoge un valor global ni se usa `Field`.
-/

namespace TratadoAnalisis.AbstractCompleteness.Manual0008

open TratadoAnalisis.Dedekind.FieldPredicates
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Naturals.Foundational

/-- Grafo del paso de numerales: sobre F, y es x + 1. -/
def NumeralStepGraphManual (F one : ZFSet)
    (add : ZFSet → ZFSet → ZFSet → Prop) : ZFSet :=
  ZFSet.sep
    (fun z => ∃ x : ZFSet, x ∈ F ∧
      ∃ y : ZFSet, y ∈ F ∧ z = ZFSet.pair x y ∧ add x one y)
    (pairAmbient F F)

/-- Condición exacta de pertenencia al grafo de la traslación por uno. -/
theorem numeralStepGraph_mem_iff_manual
    (F one : ZFSet)
    (add : ZFSet → ZFSet → ZFSet → Prop)
    (x y : ZFSet) :
    ZFSet.pair x y ∈ NumeralStepGraphManual F one add ↔
      x ∈ F ∧ y ∈ F ∧ add x one y := by
  constructor
  · intro h
    rcases (ZFSet.mem_sep.mp h).2 with
      ⟨x', hx', y', hy', hp, hadd⟩
    rcases ZFSet.pair_injective hp with ⟨rfl, rfl⟩
    exact ⟨hx', hy', hadd⟩
  · rintro ⟨hx, hy, hadd⟩
    apply ZFSet.mem_sep.mpr
    exact ⟨pair_mem_pairAmbient hx hy, x, hx, y, hy, rfl, hadd⟩

/-- La suma relacional total y unívoca hace funcional el paso x ↦ x+1. -/
theorem numeralStepGraph_isFunc_manual
    (F one : ZFSet)
    (add : ZFSet → ZFSet → ZFSet → Prop)
    (hadd : IsBinaryOperationFoundational F add)
    (hone : one ∈ F) :
    IsFuncFoundational F F (NumeralStepGraphManual F one add) := by
  constructor
  · intro z hz
    rcases (ZFSet.mem_sep.mp hz).2 with
      ⟨x, hx, y, hy, hp, _⟩
    exact ⟨x, hx, y, hy, hp⟩
  · intro x hx
    obtain ⟨y, ⟨hy, hxy⟩, hu⟩ := hadd x hx one hone
    refine ⟨y, ⟨hy, ?_⟩, ?_⟩
    · exact (numeralStepGraph_mem_iff_manual F one add x y).mpr
        ⟨hx, hy, hxy⟩
    · intro z hz
      have hxyz : add x one z :=
        ((numeralStepGraph_mem_iff_manual F one add x z).mp hz.2).2.2
      exact hu z ⟨hz.1, hxyz⟩

#check NumeralStepGraphManual
#check numeralStepGraph_isFunc_manual
#print axioms numeralStepGraph_isFunc_manual

end TratadoAnalisis.AbstractCompleteness.Manual0008
