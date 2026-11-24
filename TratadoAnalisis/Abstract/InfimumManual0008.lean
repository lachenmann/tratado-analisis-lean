import TratadoAnalisis.Abstract.BoundsViaNegation0008

/-!
TA-LEAN-0008 / prototipo de TA-PRO-00076.
Propiedad del supremo -> propiedad del infimo en cuerpo ordenado completo.
Este modulo es CANDIDATO NO COMPILADO en el entorno de creacion.
No integrarlo a la auditoria canonica antes de compilar y cotejar firmas.
-/

namespace TratadoAnalisis.AbstractCompleteness.Manual0008

open TratadoAnalisis.Dedekind.FieldPredicates

/-- TA-PRO-00076: un subconjunto no vacio de un cuerpo ordenado completo
    que posee una cota inferior posee infimo.

    La lectura de no vaciedad es clasica por el parametro explicito `em`.
    No se elige una funcion global de opuestos ni se usa Field de mathlib. -/
theorem TA_PRO_00076_infimum_from_supremum_manual
    (em : ∀ p : Prop, p ∨ ¬p)
    (F zero one A : ZFSet)
    (add mul : ZFSet → ZFSet → ZFSet → Prop)
    (le : ZFSet → ZFSet → Prop)
    (hcomplete : IsCompleteOrderedFieldFoundational F zero one add mul le)
    (hA : A ⊆ F)
    (hne : A ≠ ∅)
    (hbelow : ∃ b : ZFSet, IsLowerBound F A le b) :
    ∃ i : ZFSet, IsInfimum F A le i := by
  rcases hcomplete with ⟨hordered, hsup⟩
  have hgroup : IsAbelianGroupFoundational F zero add := hordered.1.1
  have hinv : ∀ x : ZFSet, x ∈ F →
      ∃ nx : ZFSet, nx ∈ F ∧ add x nx zero ∧ add nx x zero := by
    obtain ⟨_, _, _, _, _, hinvG⟩ := hgroup
    exact hinvG

  let negA : ZFSet := NegativeImage F zero A add
  have hnegA_subset : negA ⊆ F :=
    negativeImage_subset_manual F zero A add
  have hnegA_ne : negA ≠ ∅ :=
    negativeImage_ne_empty_manual em F zero A add hA hne hgroup

  obtain ⟨b, hb⟩ := hbelow
  obtain ⟨nb, hnbF, hbn, hnb⟩ := hinv b hb.1
  have hnegB : IsAdditiveOpposite F zero add b nb :=
    ⟨hb.1, hnbF, hbn, hnb⟩
  have hnegA_upper : ∃ ub : ZFSet, IsUpperBound F negA le ub :=
    ⟨nb, negativeImage_upper_of_lower_manual
      F zero one A add mul le b nb hordered hb hnegB⟩

  obtain ⟨s, hs⟩ := hsup negA hnegA_subset hnegA_ne hnegA_upper
  obtain ⟨ns, hnsF, hsn, hns⟩ := hinv s hs.1.1
  have hnegS : IsAdditiveOpposite F zero add s ns :=
    ⟨hs.1.1, hnsF, hsn, hns⟩

  refine ⟨ns, ?_⟩
  constructor
  · exact negativeImage_lower_of_upper_manual
      F zero one A add mul le s ns hA hordered hs.1 hnegS
  · intro c hc
    obtain ⟨nc, hncF, hcn, hnc⟩ := hinv c hc.1
    have hnegC : IsAdditiveOpposite F zero add c nc :=
      ⟨hc.1, hncF, hcn, hnc⟩
    have hncUpper : IsUpperBound F negA le nc :=
      negativeImage_upper_of_lower_manual
        F zero one A add mul le c nc hordered hc hnegC
    have hs_le_nc : le s nc := hs.2 nc hncUpper
    have hnegNC : IsAdditiveOpposite F zero add nc c :=
      opposite_symm_manual F zero add c nc hnegC
    exact opposite_reverses_le_manual F zero one add mul le s nc ns c
      hordered hs_le_nc hnegS hnegNC

#check TA_PRO_00076_infimum_from_supremum_manual
#print axioms TA_PRO_00076_infimum_from_supremum_manual

end TratadoAnalisis.AbstractCompleteness.Manual0008
