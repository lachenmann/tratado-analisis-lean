import TratadoAnalisis.Abstract.OppositeOrderPrep0008

/-!
TA-LEAN-0008 / prototipo manual: transferencia de cotas por la imagen
conjuntista de los opuestos. No emplea funciones elegidas globalmente.
-/

namespace TratadoAnalisis.AbstractCompleteness.Manual0008

open TratadoAnalisis.Dedekind.FieldPredicates

/-- Una cota inferior b de A se convierte en la cota superior -b de -A. -/
theorem negativeImage_upper_of_lower_manual
    (F zero one A : ZFSet)
    (add mul : ZFSet → ZFSet → ZFSet → Prop)
    (le : ZFSet → ZFSet → Prop)
    (b nb : ZFSet)
    (hordered : IsOrderedFieldFoundational F zero one add mul le)
    (hb : IsLowerBound F A le b)
    (hbn : IsAdditiveOpposite F zero add b nb) :
    IsUpperBound F (NegativeImage F zero A add) le nb := by
  constructor
  · exact hbn.2.1
  · intro y hy
    rcases (mem_negativeImage_iff F zero A add y).mp hy with
      ⟨_, x, hx, hxyNeg⟩
    exact opposite_reverses_le_manual F zero one add mul le b x nb y
      hordered (hb.2 x hx) hbn hxyNeg

/-- Una cota superior s de -A se convierte en la cota inferior -s de A. -/
theorem negativeImage_lower_of_upper_manual
    (F zero one A : ZFSet)
    (add mul : ZFSet → ZFSet → ZFSet → Prop)
    (le : ZFSet → ZFSet → Prop)
    (s ns : ZFSet)
    (hA : A ⊆ F)
    (hordered : IsOrderedFieldFoundational F zero one add mul le)
    (hs : IsUpperBound F (NegativeImage F zero A add) le s)
    (hsns : IsAdditiveOpposite F zero add s ns) :
    IsLowerBound F A le ns := by
  constructor
  · exact hsns.2.1
  · intro x hx
    have hxF : x ∈ F := hA hx
    have hgroup : IsAbelianGroupFoundational F zero add := hordered.1.1
    obtain ⟨_, _, _, _, _, hinv⟩ := hgroup
    obtain ⟨nx, hnxF, hxn, hnx⟩ := hinv x hxF
    have hnegX : IsAdditiveOpposite F zero add x nx :=
      ⟨hxF, hnxF, hxn, hnx⟩
    have hnxIn : nx ∈ NegativeImage F zero A add :=
      opposite_mem_negativeImage_manual F zero A add x nx hx hnegX
    have hnx_le_s : le nx s := hs.2 nx hnxIn
    have hnegNX : IsAdditiveOpposite F zero add nx x :=
      opposite_symm_manual F zero add x nx hnegX
    exact opposite_reverses_le_manual F zero one add mul le nx s x ns
      hordered hnx_le_s hnegNX hsns

#check negativeImage_upper_of_lower_manual
#print axioms negativeImage_upper_of_lower_manual
#check negativeImage_lower_of_upper_manual
#print axioms negativeImage_lower_of_upper_manual

end TratadoAnalisis.AbstractCompleteness.Manual0008
