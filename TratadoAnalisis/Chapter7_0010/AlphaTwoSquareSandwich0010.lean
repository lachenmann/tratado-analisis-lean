import TratadoAnalisis.Chapter7_0010.AlphaTwoSquareLower0010
import TratadoAnalisis.Chapter7_0010.AlphaTwoSquareUpper0010

/-! TA-LEAN-0010 / N04. Cotas del cuadrado de alpha_2.
    NO afirma alpha_2² = 2_D ni existencia/unicidad de la raiz. -/
namespace TratadoAnalisis.Chapter7_0010
universe u

open TratadoAnalisis.AbstractCompleteness.Manual0008
open TratadoAnalisis.Dedekind.Definition
open TratadoAnalisis.Dedekind.Addition
open TratadoAnalisis.Dedekind.Multiplication
open TratadoAnalisis.Dedekind.Unit
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.IrrationalitySqrtTwo

/-- Cota estricta inferior y cota no estricta superior del cuadrado. -/
theorem alphaTwo_square_bounds_0010
    (em : ∀ p : Prop, p ∨ ¬p) :
    StrictFromLeManual DedLE (dedOne : ZFSet.{u})
      (dedMul alphaTwoCut alphaTwoCut) ∧
    DedLE (dedMul (alphaTwoCut : ZFSet.{u}) alphaTwoCut)
      (rationalSection ratTwoTA) := by
  exact ⟨section_one_lt_alphaTwo_square_0010 em,
    alphaTwo_square_le_section_two_0010 em⟩

/-- La cota superior se relee como inclusion de cortaduras, sin presupuestos. -/
theorem alphaTwo_square_subset_section_two_0010
    (em : ∀ p : Prop, p ∨ ¬p) :
    (dedMul (alphaTwoCut : ZFSet.{u}) alphaTwoCut) ⊆
      rationalSection ratTwoTA := by
  exact (alphaTwo_square_le_section_two_0010 em).2.2

end TratadoAnalisis.Chapter7_0010
