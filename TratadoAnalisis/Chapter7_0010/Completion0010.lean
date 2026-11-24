import TratadoAnalisis.Chapter7_0010.Consequences0010
import TratadoAnalisis.Abstract.PrimeDensityClosure0009
import TratadoAnalisis.Dedekind.EmbeddingField

/-! TA-LEAN-0010 / P03. Completacion ordenada y densidad de la
    imagen de la incrustacion, sin nueva prueba de densidad. -/
namespace TratadoAnalisis.Chapter7_0010
universe u

open TratadoAnalisis.AbstractCompleteness.Manual0008
open TratadoAnalisis.AbstractCompleteness.Density0009
open TratadoAnalisis.Dedekind.Definition
open TratadoAnalisis.Dedekind.Addition
open TratadoAnalisis.Dedekind.Unit
open TratadoAnalisis.Dedekind.Field
open TratadoAnalisis.Dedekind.Embedding
open TratadoAnalisis.Dedekind.EmbeddingTriple
open TratadoAnalisis.Dedekind.EmbeddingField
open TratadoAnalisis.Dedekind.FieldPredicates
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.OrderDefinition

/-- Transcripcion exacta de TA-DEF-00078: completitud del codominio
    e incrustacion ordenada. NO se exige densidad como premisa. -/
def IsOrderedCompletionRelational0010
    (Q E zeroQ oneQ zeroE oneE : ZFSet.{u})
    (addQ mulQ addE mulE : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (leQ leE : ZFSet.{u} → ZFSet.{u} → Prop)
    (iota : ZFSet.{u} → ZFSet.{u}) (G f : ZFSet.{u}) : Prop :=
  IsCompleteOrderedFieldFoundational E zeroE oneE addE mulE leE ∧
  IsOrderedFieldEmbeddingFoundational Q E
    zeroQ oneQ zeroE oneE addQ mulQ addE mulE leQ leE iota G f

/-- TA-PRO-00106: Dedekind con su seccion racional es una completacion. -/
theorem TA_PRO_00106_dedekind_completion_0010
    (em : ∀ p : Prop, p ∨ ¬p) :
    IsOrderedCompletionRelational0010
      (rationalsTA : ZFSet.{u}) dedekindCutsTA
      ratZero ratOne dedZero dedOne
      RatAdd RatMul CutAdd CutMul RatLE DedLE
      rationalSection dedekindEmbeddingGraph dedekindEmbeddingFunction := by
  exact ⟨TA_THM_00056_dedekind_complete_0010 em,
    TA_COR_00023_orderedField_embedding em⟩

/-- TA-COR-00027: densidad sin repetir la demostracion de 0009. -/
theorem TA_COR_00027_rational_section_dense_0010
    (em : ∀ p : Prop, p ∨ ¬p)
    (x y : ZFSet.{u})
    (hx : x ∈ dedekindCutsTA) (hy : y ∈ dedekindCutsTA)
    (hxy : StrictFromLeManual DedLE x y) :
    ∃ q : ZFSet.{u}, q ∈ rationalsTA ∧
      StrictFromLeManual DedLE x (rationalSection q) ∧
      StrictFromLeManual DedLE (rationalSection q) y := by
  have hCompletion := TA_PRO_00106_dedekind_completion_0010 em
  exact TA_PRO_00078_rational_between_graph_manual em
    rationalsTA dedekindCutsTA
    ratZero ratOne dedZero dedOne
    RatAdd RatMul CutAdd CutMul RatLE DedLE
    rationalSection dedekindEmbeddingGraph dedekindEmbeddingFunction
    hCompletion.1 hCompletion.2 x y hx hy hxy

end TratadoAnalisis.Chapter7_0010
