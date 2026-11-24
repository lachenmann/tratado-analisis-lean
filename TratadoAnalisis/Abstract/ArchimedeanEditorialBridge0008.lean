import TratadoAnalisis.Abstract.NumeralCanonicalBridge0008

/-!
TA-LEAN-0008 — Etapa 7B. CANDIDATO PENDIENTE DE COMPILACION EN LEAN.
Puente con TA-DEF-00073 y TA-THM-00037 en su formulacion positiva.
Se usa exclusivamente la construccion conjuntista del proyecto y
un orden total relacional sobre F.
-/

namespace TratadoAnalisis.AbstractCompleteness.Manual0008

open TratadoAnalisis.Dedekind.FieldPredicates
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Naturals.Foundational

universe u

/-- Orden estricto derivado del orden no estricto en un conjunto ordenado.
    Se pide por separado pertenencia a F cuando se usa el orden total. -/
def StrictFromLeManual
    (le : ZFSet → ZFSet → Prop) (x y : ZFSet) : Prop :=
  le x y ∧ x ≠ y

/-- En un orden parcial, x < y equivale a x ≤ y y no(y ≤ x). -/
theorem strictFromLe_iff_no_reverse_manual
    (F : ZFSet) (le : ZFSet → ZFSet → Prop)
    (horder : IsTotalOrderFoundational F le)
    (x y : ZFSet) (hxF : x ∈ F) (hyF : y ∈ F) :
    StrictFromLeManual le x y ↔ (le x y ∧ ¬ le y x) := by
  constructor
  · rintro ⟨hxy, hneq⟩
    refine ⟨hxy, ?_⟩
    intro hyx
    exact hneq (horder.2.1 x y hxF hyF hxy hyx)
  · rintro ⟨hxy, hnreverse⟩
    refine ⟨hxy, ?_⟩
    intro heq
    apply hnreverse
    simpa only [heq] using hxy

/-- TA-DEF-00073: formulacion POSITIVA de arquimedianidad para la
    funcion de numerales como grafo canonico unico (TA-DEF-00068). -/
def IsArchimedeanGraphEditorialManual
    (F zero one : ZFSet.{u})
    (add : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop) : Prop :=
  ∀ x : ZFSet.{u}, x ∈ F →
    ∃ n : ZFSet.{u}, n ∈ omegaTA ∧
      ∃ y : ZFSet.{u},
        ZFSet.pair n y ∈ CanonicalNumeralGraphManual F zero one add ∧
        StrictFromLeManual le x y

/-- TA-THM-00037, en la formulacion editorial estricta x < nu_F(n),
    sin hipotesis adicional de positividad ni funcion nu escogida. -/
theorem TA_THM_00037_archimedean_editorial_manual
    (em : ∀ p : Prop, p ∨ ¬p)
    (F zero one : ZFSet)
    (add mul : ZFSet → ZFSet → ZFSet → Prop)
    (le : ZFSet → ZFSet → Prop)
    (hcomplete : IsCompleteOrderedFieldFoundational F zero one add mul le) :
    IsArchimedeanGraphEditorialManual F zero one add le := by
  intro x hxF
  obtain ⟨n, hn, y, hny, hxy, hnot_yx⟩ :=
    TA_THM_00037_archimedean_graph_manual
      em F zero one add mul le hcomplete x hxF
  have hneq : x ≠ y := by
    intro heq
    apply hnot_yx
    simpa only [heq] using hxy
  exact ⟨n, hn, y, hny, hxy, hneq⟩

#check StrictFromLeManual
#check strictFromLe_iff_no_reverse_manual
#print axioms strictFromLe_iff_no_reverse_manual
#check IsArchimedeanGraphEditorialManual
#check TA_THM_00037_archimedean_editorial_manual
#print axioms TA_THM_00037_archimedean_editorial_manual

end TratadoAnalisis.AbstractCompleteness.Manual0008
