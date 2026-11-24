import TratadoAnalisis.Abstract.CompletenessManual0008
import TratadoAnalisis.Rationals.NoSupremumSqrtTwo

/-! TA-PRO-00077: incompletitud racional en la interfaz del capítulo 4. -/

namespace TratadoAnalisis.Rationals.Incompleteness

universe u

open TratadoAnalisis.AbstractCompleteness.Manual0008
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.SqrtTwoSet
open TratadoAnalisis.Rationals.IrrationalitySqrtTwo
open TratadoAnalisis.Rationals.NoSupremumSqrtTwo

/-- Las dos definiciones relacionales de supremo coinciden en Q. -/
theorem isSupremum_iff_ratSupremum (A s : ZFSet.{u}) :
    IsSupremum rationalsTA A RatLE s ↔ RatSupremum A s :=
  Iff.rfl

/-- El contraejemplo S₂ satisface exactamente las hipótesis del supremo. -/
theorem sqrtTwoSet_supremum_hypotheses :
    (sqrtTwoSet : ZFSet.{u}) ⊆ rationalsTA ∧
    (sqrtTwoSet : ZFSet.{u}) ≠ ∅ ∧
    ∃ b : ZFSet.{u}, IsUpperBound rationalsTA sqrtTwoSet RatLE b := by
  have h := TA_PRO_00067_sqrtTwoSet_nonempty_bounded.{u, u, u}
  refine ⟨?_, ?_, (ratTwoTA : ZFSet.{u}), h.2⟩
  · intro q hq
    exact (TA_DEF_00066_mem_sqrtTwoSet_iff.mp hq).1
  · intro he
    have hOne : (ratOne : ZFSet.{u}) ∈ sqrtTwoSet := h.1
    rw [he] at hOne
    exact ZFSet.notMem_empty ratOne hOne

/-- TA-PRO-00077: Q no tiene la propiedad del supremo.
    Se reutiliza la demostración de TA-THM-00033. -/
theorem TA_PRO_00077_rationals_not_complete :
    ¬ HasSupremumProperty (rationalsTA : ZFSet.{u}) RatLE := by
  intro hComplete
  have h := sqrtTwoSet_supremum_hypotheses.{u}
  obtain ⟨s, hs⟩ := hComplete sqrtTwoSet h.1 h.2.1 h.2.2
  exact TA_THM_00033_sqrtTwoSet_no_rational_supremum
    ⟨s, (isSupremum_iff_ratSupremum sqrtTwoSet s).mp hs⟩

end TratadoAnalisis.Rationals.Incompleteness
