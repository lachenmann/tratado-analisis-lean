import TratadoAnalisis.Chapter7_0010.SupremumBridge0010
import TratadoAnalisis.Dedekind.UnionManual0008
import TratadoAnalisis.Dedekind.OrderedField

/-! TA-LEAN-0010 / P01. Ensamblaje del cuerpo ordenado con el
    teorema de union como supremo, despues del puente P00. -/
namespace TratadoAnalisis.Chapter7_0010
universe u

open TratadoAnalisis.AbstractCompleteness.Manual0008
open TratadoAnalisis.Dedekind.Definition
open TratadoAnalisis.Dedekind.Addition
open TratadoAnalisis.Dedekind.Unit
open TratadoAnalisis.Dedekind.Field
open TratadoAnalisis.Dedekind.OrderedField
open TratadoAnalisis.Dedekind.Manual0008

/-- TA-THM-00056: el conjunto de cortaduras es un cuerpo ordenado completo. -/
theorem TA_THM_00056_dedekind_complete_0010
    (em : ∀ p : Prop, p ∨ ¬p) :
    IsCompleteOrderedFieldFoundational (dedekindCutsTA : ZFSet.{u})
      dedZero dedOne CutAdd CutMul DedLE := by
  refine ⟨TA_THM_00054_dedekind_orderedField em, ?_⟩
  intro A hfamily hnonempty hbound
  rcases hbound with ⟨b, hb⟩
  have hbounded : ∃ b : ZFSet.{u}, b ∈ dedekindCutsTA ∧
      ∀ a : ZFSet.{u}, a ∈ A → DedLE a b :=
    ⟨b, hb.1, hb.2⟩
  refine ⟨ZFSet.sUnion A, ?_⟩
  exact (supremum_iff_dedekind_lub_0010 A (ZFSet.sUnion A)).2
    (TA_THM_00055_union_is_lub_manual em A hfamily hnonempty hbounded)

end TratadoAnalisis.Chapter7_0010
