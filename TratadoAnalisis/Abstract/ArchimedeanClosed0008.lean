import TratadoAnalisis.Abstract.NegOneSquare0008

/-!
TA-LEAN-0008 — Etapa 6C (CANDIDATO, NO COMPILADO LOCALMENTE).
Cierre del parametro de positividad de 1 y prueba arquimediana en
lenguaje de grafo de numerales. Falta auditoria de cotejo editorial
con TA-DEF-00068/73 antes de afirmar cierre CANONICO.
-/

namespace TratadoAnalisis.AbstractCompleteness.Manual0008

open TratadoAnalisis.Dedekind.FieldPredicates
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Naturals.Foundational

/-- La unidad de todo cuerpo ordenado fundacional es estrictamente positiva.
    En orden no estricto, esto dice `¬ le one zero`.
    La demostracion no introduce ni presupone el axioma como parametro. -/
theorem one_not_le_zero_manual
    (F zero one : ZFSet)
    (add mul : ZFSet → ZFSet → ZFSet → Prop)
    (le : ZFSet → ZFSet → Prop)
    (hordered : IsOrderedFieldFoundational F zero one add mul le) :
    ¬ le one zero := by
  intro h_one_le_zero
  have hfieldCopy : IsFieldFoundational F zero one add mul := hordered.1
  rcases hordered with ⟨hfield, horder, htranslate, hmulPos⟩
  rcases hfield with ⟨hgroup, hmulBin, honeF, _, _, _, _, hzeroNeOne, _⟩
  rcases hgroup with ⟨_, hzeroF, _, _, hunit, hinv⟩

  obtain ⟨m, hmF, h_one_m_zero, h_m_one_zero⟩ := hinv one honeF
  have hneg : IsAdditiveOpposite F zero add one m :=
    ⟨honeF, hmF, h_one_m_zero, h_m_one_zero⟩
  have hzero_le_m : le zero m :=
    htranslate one zero m zero m honeF hzeroF hmF
      h_one_le_zero h_one_m_zero (hunit m hmF).2

  obtain ⟨p, ⟨hpF, h_m_m_p⟩, _⟩ := hmulBin m hmF m hmF
  have hp_eq_one : p = one :=
    rel_neg_one_square_manual F zero one add mul hfieldCopy
      m p hneg hpF h_m_m_p
  have hzero_le_p : le zero p :=
    hmulPos m m p hmF hmF hzero_le_m hzero_le_m h_m_m_p
  have hzero_le_one : le zero one := by
    simpa only [hp_eq_one] using hzero_le_p
  have hzero_eq_one : zero = one :=
    horder.2.1 zero one hzeroF honeF hzero_le_one h_one_le_zero
  exact hzeroNeOne hzero_eq_one

/-- TA-THM-00037, version prototipo en lenguaje fundacional de grafos.
    No contiene la antigua hipotesis `hOneNotLeZero`.
    Cada numeral esta en el grafo canonico construido por recursividad
    sobre omegaTA. -/
theorem TA_THM_00037_archimedean_graph_manual
    (em : ∀ p : Prop, p ∨ ¬p)
    (F zero one : ZFSet)
    (add mul : ZFSet → ZFSet → ZFSet → Prop)
    (le : ZFSet → ZFSet → Prop)
    (hcomplete : IsCompleteOrderedFieldFoundational F zero one add mul le)
    (x : ZFSet) (hxF : x ∈ F) :
    ∃ n : ZFSet, n ∈ omegaTA ∧
      ∃ y : ZFSet,
        ZFSet.pair n y ∈ CanonicalNumeralGraphManual F zero one add ∧
          le x y ∧ ¬ le y x := by
  have hOnePos : ¬ le one zero :=
    one_not_le_zero_manual F zero one add mul le hcomplete.1
  exact archimedean_via_graph_manual
    em F zero one add mul le hcomplete hOnePos x hxF

#check one_not_le_zero_manual
#print axioms one_not_le_zero_manual
#check TA_THM_00037_archimedean_graph_manual
#print axioms TA_THM_00037_archimedean_graph_manual

end TratadoAnalisis.AbstractCompleteness.Manual0008
