import TratadoAnalisis.Abstract.InfimumManual0008

/-!
TA-LEAN-0008 / etapa experimental siguiente a TA-PRO-00076.

Objetivo: aislar el paso logico del argumento de TA-THM-00037:
si t es estrictamente menor que el supremo s de A, existe un miembro
  a ∈ A que NO satisface a ≤ t.

Se conserva la formulacion relacional sobre ZFSet. El tercero excluido
entra SOLO como argumento explicito `em`. No se usa Classical.choice,
ni un cuerpo preconstruido de mathlib. NO ES AUN TA-THM-00037.

Este archivo no esta compilado con el kernel en el entorno de creacion;
se requiere `lake build` en el proyecto del usuario.
-/

namespace TratadoAnalisis.AbstractCompleteness.Manual0008

open TratadoAnalisis.Dedekind.FieldPredicates

/-- Un elemento situado estrictamente bajo el supremo no puede
    ser una cota superior. No usa tercero excluido. -/
theorem below_supremum_not_upper_manual
    (F A : ZFSet)
    (le : ZFSet → ZFSet → Prop)
    (s t : ZFSet)
    (hs : IsSupremum F A le s)
    (hnot : ¬ le s t) :
    ¬ IsUpperBound F A le t := by
  intro ht
  exact hnot (hs.2 t ht)

/-- De que t no sea cota superior se extrae un elemento de A que
    no satisface a ≤ t. La negacion de un cuantificador es clasica;
    se justifica mediante `em` explicito, no mediante Classical.em. -/
theorem not_upper_has_non_le_member_manual
    (em : ∀ p : Prop, p ∨ ¬p)
    (F A : ZFSet)
    (le : ZFSet → ZFSet → Prop)
    (t : ZFSet)
    (htF : t ∈ F)
    (hnotUpper : ¬ IsUpperBound F A le t) :
    ∃ a : ZFSet, a ∈ A ∧ ¬ le a t := by
  rcases em (∃ a : ZFSet, a ∈ A ∧ ¬ le a t) with hex | hno
  · exact hex
  · exfalso
    apply hnotUpper
    constructor
    · exact htF
    · intro a ha
      rcases em (le a t) with hle | hnle
      · exact hle
      · exact False.elim (hno ⟨a, ha, hnle⟩)

/-- Variante estricta del paso anterior. La totalidad del orden
    convierte ¬(a ≤ t) en t ≤ a; se conserva ademas ¬(a ≤ t).
    La nocion estricta es, por tanto, t ≤ a ∧ ¬(a ≤ t). -/
theorem below_supremum_has_strictly_above_member_manual
    (em : ∀ p : Prop, p ∨ ¬p)
    (F A : ZFSet)
    (le : ZFSet → ZFSet → Prop)
    (s t : ZFSet)
    (hsub : A ⊆ F)
    (horder : IsTotalOrderFoundational F le)
    (hs : IsSupremum F A le s)
    (htF : t ∈ F)
    (hnot : ¬ le s t) :
    ∃ a : ZFSet, a ∈ A ∧ le t a ∧ ¬ le a t := by
  have hnotUpper : ¬ IsUpperBound F A le t :=
    below_supremum_not_upper_manual F A le s t hs hnot
  obtain ⟨a, ha, hnotAt⟩ :=
    not_upper_has_non_le_member_manual em F A le t htF hnotUpper
  have haF : a ∈ F := hsub ha
  obtain ⟨_, _, _, htotal⟩ := horder
  have htA : le t a := by
    rcases htotal t a htF haF with hta | hat
    · exact hta
    · exact False.elim (hnotAt hat)
  exact ⟨a, ha, htA, hnotAt⟩

#check below_supremum_not_upper_manual
#print axioms below_supremum_not_upper_manual
#check not_upper_has_non_le_member_manual
#print axioms not_upper_has_non_le_member_manual
#check below_supremum_has_strictly_above_member_manual
#print axioms below_supremum_has_strictly_above_member_manual

end TratadoAnalisis.AbstractCompleteness.Manual0008
