import TratadoAnalisis.Chapter7_0010.Completeness0010
import TratadoAnalisis.Abstract.InfimumManual0008
import TratadoAnalisis.Abstract.ArchimedeanEditorialBridge0008

/-! TA-LEAN-0010 / P02. TA-PRO-00104 y TA-DEF-00104. -/
namespace TratadoAnalisis.Chapter7_0010
universe u

open TratadoAnalisis.AbstractCompleteness.Manual0008
open TratadoAnalisis.Dedekind.Definition
open TratadoAnalisis.Dedekind.Addition
open TratadoAnalisis.Dedekind.Unit
open TratadoAnalisis.Dedekind.Field

/-- TA-PRO-00104: en una familia de cortaduras, una cota superior es
    exactamente una cortadura que contiene a cada miembro. -/
theorem TA_PRO_00104_upper_iff_subset_0010
    (A beta : ZFSet.{u})
    (hfamily : A ⊆ dedekindCutsTA)
    (hbeta : beta ∈ dedekindCutsTA) :
    IsUpperBound dedekindCutsTA A DedLE beta ↔
      (∀ alpha : ZFSet.{u}, alpha ∈ A → alpha ⊆ beta) := by
  constructor
  · intro h alpha ha
    exact (h.2 alpha ha).2.2
  · intro h
    exact ⟨hbeta, fun alpha ha => ⟨hfamily ha, hbeta, h alpha ha⟩⟩

/-- TA-DEF-00104: union conjuntista de la familia. -/
def DedSupUnion0010 (A : ZFSet.{u}) : ZFSet.{u} := ZFSet.sUnion A

/-- Lectura extensional de la union, independiente de acotacion. -/
theorem mem_dedSupUnion_iff_0010
    (A q : ZFSet.{u}) :
    q ∈ DedSupUnion0010 A ↔
      ∃ alpha : ZFSet.{u}, alpha ∈ A ∧ q ∈ alpha := by
  exact ZFSet.mem_sUnion

/-- Identidad exacta con la construccion del capitulo 7. -/
theorem TA_DEF_00104_union_eq_0010
    (A : ZFSet.{u}) : DedSupUnion0010 A = ZFSet.sUnion A := rfl

/-- TA-COR-00025: propiedad del infimo en el cuerpo de Dedekind. -/
theorem TA_COR_00025_dedekind_infimum_0010
    (em : ∀ p : Prop, p ∨ ¬p)
    (A : ZFSet.{u})
    (hA : A ⊆ dedekindCutsTA)
    (hne : A ≠ ∅)
    (hbelow : ∃ b : ZFSet.{u},
      IsLowerBound dedekindCutsTA A DedLE b) :
    ∃ i : ZFSet.{u}, IsInfimum dedekindCutsTA A DedLE i := by
  exact TA_PRO_00076_infimum_from_supremum_manual em
    dedekindCutsTA dedZero dedOne A CutAdd CutMul DedLE
    (TA_THM_00056_dedekind_complete_0010 em) hA hne hbelow

/-- TA-COR-00026: los reales de Dedekind son arquimedianos. -/
theorem TA_COR_00026_dedekind_archimedean_0010
    (em : ∀ p : Prop, p ∨ ¬p) :
    IsArchimedeanGraphEditorialManual
      (dedekindCutsTA : ZFSet.{u}) dedZero dedOne CutAdd DedLE := by
  exact TA_THM_00037_archimedean_editorial_manual
    em dedekindCutsTA dedZero dedOne CutAdd CutMul DedLE
    (TA_THM_00056_dedekind_complete_0010 em)

end TratadoAnalisis.Chapter7_0010
