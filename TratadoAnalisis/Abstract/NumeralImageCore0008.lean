import TratadoAnalisis.Abstract.SuccessorUnbounded0008
import TratadoAnalisis.Naturals.Foundational

/-!
TA-LEAN-0008 — Etapa 4C, prototipo experimental.

Se usa el omegaTA (conjunto de naturales de von Neumann) del tratado.
La aplicacion ν : ZFSet → ZFSet se recibe expresamente como PARAMETRO
con sus ecuaciones de cero y sucesor. Su existencia como funcion
conjuntista en el sentido de TA-DEF-00068 AUN NO SE CERTIFICA AQUI.

Objetivo: demostrar la forma estricta de arquimedianidad una vez
construida esa aplicacion y demostrada la desigualdad 1 > 0.
No se utilizan los reales o cuerpos preconstruidos de Mathlib.

PENDIENTE DE COMPILACION LOCAL.
-/

namespace TratadoAnalisis.AbstractCompleteness.Manual0008

open TratadoAnalisis.Dedekind.FieldPredicates
open TratadoAnalisis.Naturals.Foundational

/-- Imagen de los naturales del tratado en F, obtenida por Separacion.
    No presupone que ν provenga todavia de un grafo conjuntista. -/
def NumeralImageManual (F : ZFSet) (nu : ZFSet → ZFSet) : ZFSet :=
  ZFSet.sep (fun y => ∃ n : ZFSet, n ∈ omegaTA ∧ nu n = y) F

theorem numeral_image_subset_manual (F : ZFSet)
    (nu : ZFSet → ZFSet) :
    NumeralImageManual F nu ⊆ F := by
  intro y hy
  exact (ZFSet.mem_sep.mp hy).1

theorem numeral_zero_mem_manual (F zero : ZFSet)
    (nu : ZFSet → ZFSet)
    (hzeroF : zero ∈ F)
    (hnu0 : nu (∅ : ZFSet) = zero) :
    zero ∈ NumeralImageManual F nu := by
  exact ZFSet.mem_sep.mpr
    ⟨hzeroF, (∅ : ZFSet), omegaTA_isInductive.1, hnu0⟩

/-- La imagen de numerales es cerrada por suma de 1
    si ν satisface la ecuacion de recursión apropiada. -/
theorem numeral_image_successor_closed_manual
    (F one : ZFSet)
    (add : ZFSet → ZFSet → ZFSet → Prop)
    (nu : ZFSet → ZFSet)
    (hnumF : ∀ n : ZFSet, n ∈ omegaTA → nu n ∈ F)
    (hnumSucc : ∀ n : ZFSet, n ∈ omegaTA →
      add (nu n) one (nu (succ n))) :
    ∀ y : ZFSet, y ∈ NumeralImageManual F nu →
      ∃ ys : ZFSet, ys ∈ NumeralImageManual F nu ∧ add y one ys := by
  intro y hy
  rcases ZFSet.mem_sep.mp hy with ⟨_, n, hn, hnu⟩
  have hnSucc : succ n ∈ omegaTA := TA_PRO_00022_succ_closed hn
  refine ⟨nu (succ n), ?_, ?_⟩
  · exact ZFSet.mem_sep.mpr
      ⟨hnumF (succ n) hnSucc, succ n, hnSucc, rfl⟩
  · rw [← hnu]
    exact hnumSucc n hn

/-- La imagen de numerales no esta acotada, siempre que
    las hipotesis recursivas y de positividad de 1 sean ciertas. -/
theorem numeral_image_unbounded_manual
    (em : ∀ p : Prop, p ∨ ¬p)
    (F zero one : ZFSet)
    (add mul : ZFSet → ZFSet → ZFSet → Prop)
    (le : ZFSet → ZFSet → Prop)
    (nu : ZFSet → ZFSet)
    (hcomplete : IsCompleteOrderedFieldFoundational F zero one add mul le)
    (hOneNotLeZero : ¬ le one zero)
    (hnumF : ∀ n : ZFSet, n ∈ omegaTA → nu n ∈ F)
    (hnu0 : nu (∅ : ZFSet) = zero)
    (hnumSucc : ∀ n : ZFSet, n ∈ omegaTA →
      add (nu n) one (nu (succ n))) :
    ¬ ∃ b : ZFSet,
      IsUpperBound F (NumeralImageManual F nu) le b := by
  have hgroup : IsAbelianGroupFoundational F zero add := hcomplete.1.1.1
  have hzeroF : zero ∈ F := hgroup.2.1
  have hNne : NumeralImageManual F nu ≠ ∅ := by
    intro he
    have hz : zero ∈ NumeralImageManual F nu :=
      numeral_zero_mem_manual F zero nu hzeroF hnu0
    rw [he] at hz
    exact ZFSet.notMem_empty zero hz
  exact successor_closed_not_bounded_manual
    em F zero one (NumeralImageManual F nu) add mul le
    hcomplete (numeral_image_subset_manual F nu) hNne hOneNotLeZero
    (numeral_image_successor_closed_manual F one add nu hnumF hnumSucc)

/-- Nucleo CONDICIONAL de TA-THM-00037.
    Por cada x∈F aparece un numeral del omegaTA propio estrictamente
    mayor que x, interpretando < como ≤ y desigualdad en sentido inverso.
    Aun se debe construir nu_F y obtener 0<1 de la interfaz abstracta. -/
theorem archimedean_given_numerals_manual
    (em : ∀ p : Prop, p ∨ ¬p)
    (F zero one : ZFSet)
    (add mul : ZFSet → ZFSet → ZFSet → Prop)
    (le : ZFSet → ZFSet → Prop)
    (nu : ZFSet → ZFSet)
    (hcomplete : IsCompleteOrderedFieldFoundational F zero one add mul le)
    (hOneNotLeZero : ¬ le one zero)
    (hnumF : ∀ n : ZFSet, n ∈ omegaTA → nu n ∈ F)
    (hnu0 : nu (∅ : ZFSet) = zero)
    (hnumSucc : ∀ n : ZFSet, n ∈ omegaTA →
      add (nu n) one (nu (succ n)))
    (x : ZFSet) (hxF : x ∈ F) :
    ∃ n : ZFSet, n ∈ omegaTA ∧ le x (nu n) ∧ ¬ le (nu n) x := by
  let N : ZFSet := NumeralImageManual F nu
  have hnoUpper : ¬ ∃ b : ZFSet, IsUpperBound F N le b :=
    numeral_image_unbounded_manual
      em F zero one add mul le nu
      hcomplete hOneNotLeZero hnumF hnu0 hnumSucc
  have hxNotUpper : ¬ IsUpperBound F N le x := by
    intro hxUpper
    exact hnoUpper ⟨x, hxUpper⟩
  obtain ⟨a, haN, hnot_a_le_x⟩ :=
    not_upper_has_non_le_member_manual em F N le x hxF hxNotUpper
  rcases ZFSet.mem_sep.mp haN with ⟨_, n, hn, hnu⟩
  have hn_not_le_x : ¬ le (nu n) x := by
    simpa only [hnu] using hnot_a_le_x
  have htotal : IsTotalOrderFoundational F le := hcomplete.1.2.1
  obtain ⟨_, _, _, hcompare⟩ := htotal
  have hx_le_n : le x (nu n) := by
    rcases hcompare x (nu n) hxF (hnumF n hn) with h | h
    · exact h
    · exact False.elim (hn_not_le_x h)
  exact ⟨n, hn, hx_le_n, hn_not_le_x⟩

#check NumeralImageManual
#check numeral_image_successor_closed_manual
#print axioms numeral_image_successor_closed_manual
#check numeral_image_unbounded_manual
#print axioms numeral_image_unbounded_manual
#check archimedean_given_numerals_manual
#print axioms archimedean_given_numerals_manual

end TratadoAnalisis.AbstractCompleteness.Manual0008
