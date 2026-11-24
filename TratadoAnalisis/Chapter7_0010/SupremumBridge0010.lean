import TratadoAnalisis.Abstract.CompletenessManual0008
import TratadoAnalisis.Dedekind.UnionManual0008

/-! TA-LEAN-0010 / P00. Puente necesario entre las dos definiciones
    de supremo. No crea otra nocion de orden ni introduce eleccion. -/
namespace TratadoAnalisis.Chapter7_0010
universe u

open TratadoAnalisis.AbstractCompleteness.Manual0008
open TratadoAnalisis.Dedekind.Definition
open TratadoAnalisis.Dedekind.Manual0008

/-- En el modelo de cortaduras, IsSupremum e IsLeastUpperBoundDedekind
    tienen exactamente los mismos testigos; solo difieren en como
    agrupan las conjunciones y el antecedente de la minimalidad. -/
theorem supremum_iff_dedekind_lub_0010
    (A s : ZFSet.{u}) :
    IsSupremum dedekindCutsTA A DedLE s ↔
      IsLeastUpperBoundDedekind A s := by
  constructor
  · intro h
    exact ⟨h.1.1, h.1.2,
      fun b hb hupper => h.2 b ⟨hb, hupper⟩⟩
  · intro h
    exact ⟨⟨h.1, h.2.1⟩,
      fun b hb => h.2.2 b hb.1 hb.2⟩

end TratadoAnalisis.Chapter7_0010
