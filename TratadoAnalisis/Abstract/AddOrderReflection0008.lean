import TratadoAnalisis.Abstract.ArchimedeanSupPrep0008

/-!
TA-LEAN-0008 — Etapa 4A, prototipo experimental.

La monotonia de la traslacion es parte de IsOrderedFieldFoundational.
Aqui probamos su recíproca empleando un opuesto ADITIVO LOCAL.
Se requieren expresamente los resultados de la suma dentro de F:
no se presupone que una relacion arbitraria carezca de valores externos.

PENDIENTE DE COMPILACION LOCAL. No modifica el modulo canonico.
-/

namespace TratadoAnalisis.AbstractCompleteness.Manual0008

open TratadoAnalisis.Dedekind.FieldPredicates

/-- Cancelacion de orden para la traslacion relacional:
    (x+z) ≤ (y+z) implica x ≤ y.
    Las pertenencias de xz e yz al portador son hipotesis explicitas. -/
theorem rel_add_reflect_le_manual
    (F zero one : ZFSet)
    (add mul : ZFSet → ZFSet → ZFSet → Prop)
    (le : ZFSet → ZFSet → Prop)
    (x y z xz yz : ZFSet)
    (hordered : IsOrderedFieldFoundational F zero one add mul le)
    (hxF : x ∈ F) (hyF : y ∈ F) (hzF : z ∈ F)
    (hxzF : xz ∈ F) (hyzF : yz ∈ F)
    (haddX : add x z xz) (haddY : add y z yz)
    (hxyz : le xz yz) : le x y := by
  rcases hordered with ⟨hfield, _, htranslate, _⟩
  rcases hfield with ⟨hgroup, _, _, _, _, _, _, _, _⟩
  rcases hgroup with ⟨hbin, _, hassoc, _, hunit, hinv⟩

  obtain ⟨nz, hnzF, hznz, _⟩ := hinv z hzF
  obtain ⟨xx, ⟨_, h_xz_nz_xx⟩, _⟩ := hbin xz hxzF nz hnzF
  obtain ⟨yy, ⟨_, h_yz_nz_yy⟩, _⟩ := hbin yz hyzF nz hnzF

  have hxx_eq_x : xx = x :=
    hassoc x z nz xz xx zero x hxF hzF hnzF
      haddX h_xz_nz_xx hznz (hunit x hxF).1
  have hyy_eq_y : yy = y :=
    hassoc y z nz yz yy zero y hyF hzF hnzF
      haddY h_yz_nz_yy hznz (hunit y hyF).1
  have hxx_le_yy : le xx yy :=
    htranslate xz yz nz xx yy hxzF hyzF hnzF
      hxyz h_xz_nz_xx h_yz_nz_yy
  rw [hxx_eq_x, hyy_eq_y] at hxx_le_yy
  exact hxx_le_yy

#check rel_add_reflect_le_manual
#print axioms rel_add_reflect_le_manual

end TratadoAnalisis.AbstractCompleteness.Manual0008
