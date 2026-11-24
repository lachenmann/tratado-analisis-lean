import TratadoAnalisis.Abstract.ArchimedeanClosed0008

/-!
TA-LEAN-0008 — Etapa 7A. CANDIDATO PENDIENTE DE COMPILACION EN LEAN.
Puente con TA-DEF-00068: existencia y unicidad del grafo de numerales
sin recurrir a una funcion externa ni a Classical.choice.
El paso relacional exige y ∈ F: IsBinaryOperationFoundational garantiza
unicidad de resultados DENTRO del portador, no fuera de el.
-/

namespace TratadoAnalisis.AbstractCompleteness.Manual0008

open TratadoAnalisis.Dedekind.FieldPredicates
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Naturals.Foundational

universe u

/-- Ecuaciones de la aplicacion canonica de numerales, expresadas como un
    unico grafo funcional conjuntista omegaTA → F. -/
def IsCanonicalNumeralGraphManual
    (F zero one : ZFSet.{u})
    (add : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (f : ZFSet.{u}) : Prop :=
  IsFuncFoundational omegaTA F f ∧
  ZFSet.pair (∅ : ZFSet.{u}) zero ∈ f ∧
  ∀ n x y : ZFSet.{u},
    n ∈ omegaTA →
    ZFSet.pair n x ∈ f →
    x ∈ F → y ∈ F → add x one y →
    ZFSet.pair (succ n) y ∈ f

/-- El grafo construido por recursividad satisface las ecuaciones. -/
theorem canonicalNumeralGraph_satisfies_manual
    (F zero one : ZFSet)
    (add : ZFSet → ZFSet → ZFSet → Prop)
    (hzero : zero ∈ F) (hone : one ∈ F)
    (hadd : IsBinaryOperationFoundational F add) :
    IsCanonicalNumeralGraphManual F zero one add
      (CanonicalNumeralGraphManual F zero one add) := by
  refine ⟨canonicalNumeralGraph_isFunc_manual F zero one add hzero hone hadd,
    canonicalNumeralGraph_zero_manual F zero one add hzero, ?_⟩
  intro n x y hn hnx hxF hyF hxy
  exact canonicalNumeralGraph_succ_manual
    F zero one add hzero hone hadd hn hnx hxF hyF hxy

/-- Unicidad: otra funcion omegaTA → F con las mismas ecuaciones
    coincide extensionalmente con el grafo construido. -/
theorem canonicalNumeralGraph_unique_manual
    (F zero one : ZFSet)
    (add : ZFSet → ZFSet → ZFSet → Prop)
    (hzero : zero ∈ F) (hone : one ∈ F)
    (hadd : IsBinaryOperationFoundational F add)
    (f : ZFSet)
    (hf : IsCanonicalNumeralGraphManual F zero one add f) :
    f = CanonicalNumeralGraphManual F zero one add := by
  rcases hf with ⟨hfunc, h0, hsucc⟩
  unfold CanonicalNumeralGraphManual
  apply globalRecursionGraph_unique hzero
    (numeralStepGraph_isFunc_manual F one add hadd hone) hfunc h0
  intro n x y hn hnx hxy
  rcases (numeralStepGraph_mem_iff_manual F one add x y).mp hxy with
    ⟨hxF, hyF, haddxy⟩
  exact hsucc n x y hn hnx hxF hyF haddxy

/-- TA-DEF-00068: EXISTENCIA Y UNICIDAD de la funcion canonica de
    numerales, expresada en el lenguaje de funciones como grafos de pares. -/
theorem TA_DEF_00068_exists_unique_graph_manual
    (F zero one : ZFSet)
    (add : ZFSet → ZFSet → ZFSet → Prop)
    (hzero : zero ∈ F) (hone : one ∈ F)
    (hadd : IsBinaryOperationFoundational F add) :
    ∃! f : ZFSet, IsCanonicalNumeralGraphManual F zero one add f := by
  refine ⟨CanonicalNumeralGraphManual F zero one add,
    canonicalNumeralGraph_satisfies_manual F zero one add hzero hone hadd, ?_⟩
  intro f hf
  exact canonicalNumeralGraph_unique_manual F zero one add hzero hone hadd f hf

#check IsCanonicalNumeralGraphManual
#check canonicalNumeralGraph_satisfies_manual
#print axioms canonicalNumeralGraph_satisfies_manual
#check canonicalNumeralGraph_unique_manual
#print axioms canonicalNumeralGraph_unique_manual
#check TA_DEF_00068_exists_unique_graph_manual
#print axioms TA_DEF_00068_exists_unique_graph_manual

end TratadoAnalisis.AbstractCompleteness.Manual0008
