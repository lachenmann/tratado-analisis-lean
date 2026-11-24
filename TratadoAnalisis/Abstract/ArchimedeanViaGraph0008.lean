import TratadoAnalisis.Abstract.NumeralRecursionGraph0008

/-!
# TA-LEAN-0008 — Etapa 5C (candidato, no compilado)

Resultado arquimediano en lenguaje conjuntista-relacional. No se utiliza
ninguna función numérica nativa ni una elección global de valores.

PENDIENTE: deducir `¬ le one zero` de `IsOrderedFieldFoundational`
y conectar esta especificación con TA-DEF-00068 de la bóveda.
-/

namespace TratadoAnalisis.AbstractCompleteness.Manual0008

open TratadoAnalisis.Dedekind.FieldPredicates
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Naturals.Foundational

/-- La imagen del grafo de numerales no tiene cota superior. -/
theorem numeralGraphImage_unbounded_manual
    (em : ∀ p : Prop, p ∨ ¬p)
    (F zero one : ZFSet)
    (add mul : ZFSet → ZFSet → ZFSet → Prop)
    (le : ZFSet → ZFSet → Prop)
    (hcomplete : IsCompleteOrderedFieldFoundational F zero one add mul le)
    (hOneNotLeZero : ¬ le one zero) :
    ¬ ∃ b : ZFSet, IsUpperBound F
      (NumeralGraphImageManual F (CanonicalNumeralGraphManual F zero one add)) le b := by
  have hgroup : IsAbelianGroupFoundational F zero add := hcomplete.1.1.1
  have hzero : zero ∈ F := hgroup.2.1
  have hadd : IsBinaryOperationFoundational F add := hgroup.1
  have hone : one ∈ F := hcomplete.1.1.2.2.1
  let G : ZFSet := CanonicalNumeralGraphManual F zero one add
  let N : ZFSet := NumeralGraphImageManual F G
  have hNsub : N ⊆ F := numeralGraphImage_subset_manual F G
  have hNne : N ≠ ∅ := by
    intro he
    have h0 : zero ∈ N := numeralGraphImage_zero_manual F zero one add hzero
    rw [he] at h0
    exact ZFSet.notMem_empty zero h0
  have hNclosed : ∀ x : ZFSet, x ∈ N → ∃ y : ZFSet, y ∈ N ∧ add x one y :=
    numeralGraphImage_successor_closed_manual F zero one add hzero hone hadd
  exact successor_closed_not_bounded_manual
    em F zero one N add mul le hcomplete hNsub hNne hOneNotLeZero hNclosed

/-- Candidato a TA-THM-00037 en lenguaje exacto de grafos.
    Existencia del grafo se prueba, no se postula `nu`. -/
theorem archimedean_via_graph_manual
    (em : ∀ p : Prop, p ∨ ¬p)
    (F zero one : ZFSet)
    (add mul : ZFSet → ZFSet → ZFSet → Prop)
    (le : ZFSet → ZFSet → Prop)
    (hcomplete : IsCompleteOrderedFieldFoundational F zero one add mul le)
    (hOneNotLeZero : ¬ le one zero)
    (x : ZFSet) (hxF : x ∈ F) :
    ∃ n : ZFSet, n ∈ omegaTA ∧
      ∃ y : ZFSet,
        ZFSet.pair n y ∈ CanonicalNumeralGraphManual F zero one add ∧
        le x y ∧ ¬ le y x := by
  let G : ZFSet := CanonicalNumeralGraphManual F zero one add
  let N : ZFSet := NumeralGraphImageManual F G
  have hnoBound : ¬ ∃ b : ZFSet, IsUpperBound F N le b :=
    numeralGraphImage_unbounded_manual em F zero one add mul le hcomplete hOneNotLeZero
  have hxNotUpper : ¬ IsUpperBound F N le x := by
    intro hxUpper
    exact hnoBound ⟨x, hxUpper⟩
  obtain ⟨y, hyN, hnotYleX⟩ :=
    not_upper_has_non_le_member_manual em F N le x hxF hxNotUpper
  rcases (mem_numeralGraphImage_iff_manual F G y).mp hyN with
    ⟨hyF, n, hn, hny⟩
  have htotal : IsTotalOrderFoundational F le := hcomplete.1.2.1
  have hxleY : le x y := by
    rcases htotal.2.2.2 x y hxF hyF with hxy | hyx
    · exact hxy
    · exact False.elim (hnotYleX hyx)
  exact ⟨n, hn, y, hny, hxleY, hnotYleX⟩

#check numeralGraphImage_unbounded_manual
#print axioms numeralGraphImage_unbounded_manual
#check archimedean_via_graph_manual
#print axioms archimedean_via_graph_manual

end TratadoAnalisis.AbstractCompleteness.Manual0008
