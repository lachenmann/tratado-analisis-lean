import TratadoAnalisis.Abstract.ArchimedeanViaGraph0008

/-!
TA-LEAN-0008 — Etapa 6A (CANDIDATO, NO COMPILADO LOCALMENTE).
Cancelacion algebraica para la suma fundacional relacional.
No modifica definiciones ni teoremas canonicos.
-/

namespace TratadoAnalisis.AbstractCompleteness.Manual0008

open TratadoAnalisis.Dedekind.FieldPredicates

/-- Si x+y = x+v en el grupo abeliano relacional, entonces y=v.
    Las operaciones se mantienen relacionales; no se escoge una suma total. -/
theorem rel_add_cancel_left_manual
    (F zero : ZFSet)
    (add : ZFSet → ZFSet → ZFSet → Prop)
    (hgroup : IsAbelianGroupFoundational F zero add)
    (x y v z : ZFSet)
    (hxF : x ∈ F) (hyF : y ∈ F) (hvF : v ∈ F) (hzF : z ∈ F)
    (hxy : add x y z) (hxv : add x v z) : y = v := by
  rcases hgroup with ⟨hbin, _, hassoc, _, hunit, hinv⟩
  obtain ⟨nx, hnxF, _, hnx_x_zero⟩ := hinv x hxF
  obtain ⟨w, ⟨_, hnx_z_w⟩, _⟩ := hbin nx hnxF z hzF
  have hy_eq_w : y = w :=
    hassoc nx x y zero y z w hnxF hxF hyF
      hnx_x_zero (hunit y hyF).2 hxy hnx_z_w
  have hv_eq_w : v = w :=
    hassoc nx x v zero v z w hnxF hxF hvF
      hnx_x_zero (hunit v hvF).2 hxv hnx_z_w
  exact hy_eq_w.trans hv_eq_w.symm

#check rel_add_cancel_left_manual
#print axioms rel_add_cancel_left_manual

end TratadoAnalisis.AbstractCompleteness.Manual0008
