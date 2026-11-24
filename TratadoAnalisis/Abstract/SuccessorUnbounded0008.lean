import TratadoAnalisis.Abstract.AddOrderReflection0008

/-!
TA-LEAN-0008 — Etapa 4B, prototipo experimental.

Resultado principal: en un cuerpo ordenado completo, si 1 NO es ≤ 0,
un conjunto N no vacio de elementos del cuerpo y cerrado por suma
relacional de 1 no puede tener cota superior.

Esta es la contradiccion matematica central de TA-THM-00037.
La positividad de 1 se recibe como hipotesis: queda por enlazar
con la teoria abstracta de signos de TA-LEM-00020.

PENDIENTE DE COMPILACION LOCAL. No prueba aun la existencia de ν_F.
-/

namespace TratadoAnalisis.AbstractCompleteness.Manual0008

open TratadoAnalisis.Dedekind.FieldPredicates

/-- Ningun subconjunto no vacio de F, cerrado por agregar 1,
    puede estar acotado superiormente si F tiene supremos. -/
theorem successor_closed_not_bounded_manual
    (em : ∀ p : Prop, p ∨ ¬p)
    (F zero one N : ZFSet)
    (add mul : ZFSet → ZFSet → ZFSet → Prop)
    (le : ZFSet → ZFSet → Prop)
    (hcomplete : IsCompleteOrderedFieldFoundational F zero one add mul le)
    (hN : N ⊆ F) (hne : N ≠ ∅)
    (hOneNotLeZero : ¬ le one zero)
    (hclosed : ∀ n : ZFSet, n ∈ N →
      ∃ ns : ZFSet, ns ∈ N ∧ add n one ns) :
    ¬ ∃ b : ZFSet, IsUpperBound F N le b := by
  intro hbounded
  rcases hcomplete with ⟨hordered, hsupProp⟩
  have htotal : IsTotalOrderFoundational F le := hordered.2.1
  have hfield : IsFieldFoundational F zero one add mul := hordered.1
  rcases hfield with ⟨hgroup, _, honeF, _, _, _, _, _, _⟩
  rcases hgroup with ⟨hbin, hzeroF, hassoc, hcomm, hunit, hinv⟩

  -- s = sup N (supuesto que N estuviera acotado).
  obtain ⟨s, hs⟩ := hsupProp N hN hne hbounded
  have hsF : s ∈ F := hs.1.1

  -- t = s - 1, construido RELACIONALMENTE a partir del opuesto de 1.
  obtain ⟨nOne, hnOneF, _, hnOne_one_zero⟩ := hinv one honeF
  obtain ⟨t, ⟨htF, h_s_nOne_t⟩, _⟩ := hbin s hsF nOne hnOneF
  obtain ⟨u, ⟨_, h_t_one_u⟩, _⟩ := hbin t htF one honeF
  have hu_eq_s : u = s :=
    hassoc s nOne one t u zero s hsF hnOneF honeF
      h_s_nOne_t h_t_one_u hnOne_one_zero (hunit s hsF).1
  have h_t_one_s : add t one s := by
    simpa only [hu_eq_s] using h_t_one_u

  -- 1 + t = s por conmutatividad; ello da s ≰ t usando 1 ≰ 0.
  obtain ⟨v, ⟨_, h_one_t_v⟩, _⟩ := hbin one honeF t htF
  have hv_eq_s : v = s :=
    hcomm one t v s honeF htF h_one_t_v h_t_one_s
  have h_one_t_s : add one t s := by
    simpa only [hv_eq_s] using h_one_t_v
  have hnot_s_le_t : ¬ le s t := by
    intro hs_le_t
    have h_one_le_zero : le one zero :=
      rel_add_reflect_le_manual F zero one add mul le
        one zero t s t hordered
        honeF hzeroF htF hsF htF
        h_one_t_s (hunit t htF).2 hs_le_t
    exact hOneNotLeZero h_one_le_zero

  -- Como t < s, existe n ∈ N situado estrictamente sobre t.
  obtain ⟨n, hnN, _, hnot_n_le_t⟩ :=
    below_supremum_has_strictly_above_member_manual
      em F N le s t hN htotal hs htF hnot_s_le_t
  obtain ⟨ns, hnsN, h_n_one_ns⟩ := hclosed n hnN

  -- Por ser s cota superior, n+1 ≤ s = t+1.
  -- Cancelar la traslacion por 1 daria n ≤ t: contradiccion.
  have h_ns_le_s : le ns s := hs.1.2 ns hnsN
  have h_n_le_t : le n t :=
    rel_add_reflect_le_manual F zero one add mul le
      n t one ns s hordered
      (hN hnN) htF honeF (hN hnsN) hsF
      h_n_one_ns h_t_one_s h_ns_le_s
  exact hnot_n_le_t h_n_le_t

#check successor_closed_not_bounded_manual
#print axioms successor_closed_not_bounded_manual

end TratadoAnalisis.AbstractCompleteness.Manual0008
