import TratadoAnalisis.Abstract.NegativeImagePrep0008

/-!
TA-LEAN-0008 / prototipo manual: antitonia del opuesto aditivo.
Solo usa la interfaz relacional propia y los lemas previamente certificados.
No se altera el modulo canonico ni se importa una instancia de Field de mathlib.
-/

namespace TratadoAnalisis.AbstractCompleteness.Manual0008

open TratadoAnalisis.Dedekind.FieldPredicates

/-- La relacion de opuesto aditivo es simetrica por sus dos identidades de suma. -/
theorem opposite_symm_manual
    (F zero : ZFSet)
    (add : ZFSet → ZFSet → ZFSet → Prop)
    (x nx : ZFSet)
    (h : IsAdditiveOpposite F zero add x nx) :
    IsAdditiveOpposite F zero add nx x := by
  rcases h with ⟨hxF, hnxF, hxn, hnx⟩
  exact ⟨hnxF, hxF, hnx, hxn⟩

/-- En un cuerpo ordenado con operacion aditiva RELACIONAL, la negacion
    invierte el orden. La prueba solo requiere las leyes del grupo
    aditivo y la monotonia de las traslaciones. -/
theorem opposite_reverses_le_manual
    (F zero one : ZFSet)
    (add mul : ZFSet → ZFSet → ZFSet → Prop)
    (le : ZFSet → ZFSet → Prop)
    (x y nx ny : ZFSet)
    (hordered : IsOrderedFieldFoundational F zero one add mul le)
    (hxy : le x y)
    (hnx : IsAdditiveOpposite F zero add x nx)
    (hny : IsAdditiveOpposite F zero add y ny) :
    le ny nx := by
  rcases hnx with ⟨hxF, hnxF, hxn, _⟩
  rcases hny with ⟨hyF, hnyF, hyn, _⟩
  rcases hordered with ⟨hfield, _, htranslate, _⟩
  rcases hfield with ⟨hgroup, _, _, _, _, _, _, _, _⟩
  rcases hgroup with ⟨hbin, hzeroF, hassoc, hcomm, hunit, _⟩

  obtain ⟨z, ⟨hzF, hy_nx_z⟩, _⟩ := hbin y hyF nx hnxF
  obtain ⟨w, ⟨_, hnx_y_w⟩, _⟩ := hbin nx hnxF y hyF
  have hz_eq_w : z = w := hcomm y nx z w hyF hnxF hy_nx_z hnx_y_w
  have hnx_y_z : add nx y z := by
    rw [hz_eq_w]
    exact hnx_y_w

  have hzero_le_z : le zero z :=
    htranslate x y nx zero z hxF hyF hnxF hxy hxn hy_nx_z

  obtain ⟨t, ⟨_, hz_ny_t⟩, _⟩ := hbin z hzF ny hnyF
  have ht_eq_nx : t = nx :=
    hassoc nx y ny z t zero nx hnxF hyF hnyF
      hnx_y_z hz_ny_t hyn (hunit nx hnxF).1
  have hny_le_t : le ny t :=
    htranslate zero z ny ny t hzeroF hzF hnyF
      hzero_le_z (hunit ny hnyF).2 hz_ny_t
  simpa only [ht_eq_nx] using hny_le_t

#check opposite_symm_manual
#print axioms opposite_symm_manual
#check opposite_reverses_le_manual
#print axioms opposite_reverses_le_manual

end TratadoAnalisis.AbstractCompleteness.Manual0008
