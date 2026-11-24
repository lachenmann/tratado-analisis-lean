import TratadoAnalisis.Abstract.RelAddCancel0008

/-!
TA-LEAN-0008 — Etapa 6B (CANDIDATO, NO COMPILADO LOCALMENTE).
Pruebas algebraicas sin la operacion nativa Field de mathlib:
  x * 0 = 0 y (-1) * (-1) = 1.
-/

namespace TratadoAnalisis.AbstractCompleteness.Manual0008

open TratadoAnalisis.Dedekind.FieldPredicates

/-- El producto relacional por cero es cero en cualquier cuerpo fundacional.
    La pertenencia del resultado a F es explicita. -/
theorem rel_mul_zero_manual
    (F zero one : ZFSet)
    (add mul : ZFSet → ZFSet → ZFSet → Prop)
    (hfield : IsFieldFoundational F zero one add mul)
    (x p : ZFSet) (hxF : x ∈ F) (hpF : p ∈ F)
    (hxp : mul x zero p) : p = zero := by
  rcases hfield with ⟨hgroup, _, _, _, _, _, hdistrib, _, _⟩
  have hcancel := rel_add_cancel_left_manual F zero add hgroup
  rcases hgroup with ⟨hbin, hzeroF, _, _, hunit, _⟩
  obtain ⟨q, ⟨_, hp_p_q⟩, _⟩ := hbin p hpF p hpF
  have hp_eq_q : p = q :=
    hdistrib.1 x zero zero zero p p p q
      hxF hzeroF hzeroF (hunit zero hzeroF).1
      hxp hxp hxp hp_p_q
  have hp_p_p : add p p p := by
    simpa only [← hp_eq_q] using hp_p_q
  exact hcancel p p zero p hpF hpF hzeroF hpF
    hp_p_p (hunit p hpF).1

/-- El cuadrado del opuesto aditivo de uno es uno (formulacion relacional).
    Sigue exclusivamente de los axiomas de cuerpo; no usa le. -/
theorem rel_neg_one_square_manual
    (F zero one : ZFSet)
    (add mul : ZFSet → ZFSet → ZFSet → Prop)
    (hfield : IsFieldFoundational F zero one add mul)
    (nOne p : ZFSet)
    (hnOne : IsAdditiveOpposite F zero add one nOne)
    (hpF : p ∈ F) (hmm : mul nOne nOne p) : p = one := by
  have hcancel := rel_add_cancel_left_manual F zero add hfield.1
  have hfieldForMul : IsFieldFoundational F zero one add mul := hfield
  rcases hfield with ⟨hgroup, hmulBin, _, _, _, hmulUnit, hdistrib, _, _⟩
  rcases hgroup with ⟨haddBin, hzeroF, _, _, _, _⟩
  rcases hnOne with ⟨honeF, hnOneF, h_one_nOne_zero, h_nOne_one_zero⟩

  obtain ⟨r, ⟨hrF, h_m_zero_r⟩, _⟩ := hmulBin nOne hnOneF zero hzeroF
  have hr_eq_zero : r = zero :=
    rel_mul_zero_manual F zero one add mul hfieldForMul
      nOne r hnOneF hrF h_m_zero_r

  obtain ⟨t, ⟨_, h_m_p_t⟩, _⟩ := haddBin nOne hnOneF p hpF
  have hr_eq_t : r = t :=
    hdistrib.1 nOne one nOne zero r nOne p t
      hnOneF honeF hnOneF h_one_nOne_zero
      h_m_zero_r (hmulUnit nOne hnOneF).1 hmm h_m_p_t
  have ht_eq_zero : t = zero := hr_eq_t.symm.trans hr_eq_zero
  have h_m_p_zero : add nOne p zero := by
    simpa only [ht_eq_zero] using h_m_p_t
  exact hcancel nOne p one zero hnOneF hpF honeF hzeroF
    h_m_p_zero h_nOne_one_zero

#check rel_mul_zero_manual
#print axioms rel_mul_zero_manual
#check rel_neg_one_square_manual
#print axioms rel_neg_one_square_manual

end TratadoAnalisis.AbstractCompleteness.Manual0008
