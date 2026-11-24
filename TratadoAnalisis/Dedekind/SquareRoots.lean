import Batteries.Tactic.Alias
import TratadoAnalisis.Chapter7_0010.N05PositiveSquareUniqueness
import TratadoAnalisis.Abstract.ArchimedeanEditorialBridge0008
import TratadoAnalisis.Dedekind.Positivity

/-! Interfaz pública estable: los nombres históricos se conservan. -/
namespace TratadoAnalisis.Dedekind

universe u

open TratadoAnalisis.Dedekind.Definition
open TratadoAnalisis.Dedekind.Addition
open TratadoAnalisis.Dedekind.Positivity
open TratadoAnalisis.AbstractCompleteness.Manual0008

/-- La positividad estricta de TA-THM-00057 es el orden estricto editorial. -/
theorem isPositiveCut_iff_strictFromLe {α : ZFSet.{u}} :
    IsPositiveCut α ↔ StrictFromLeManual DedLE dedZero α :=
  Iff.rfl

alias quadratic_cofinality := TratadoAnalisis.Chapter7_0010.quadratic_cofinality_proved_0010
alias alphaTwo_square_eq_section_two := TratadoAnalisis.Chapter7_0010.alphaTwo_square_eq_section_two_0010
alias alphaTwo_positive_irrational_square_two := TratadoAnalisis.Chapter7_0010.alphaTwo_positive_irrational_square_two_0010
alias positive_cut_mem_iff_square_mem := TratadoAnalisis.Chapter7_0010.positive_cut_mem_iff_square_mem_0010
alias positive_cut_square_injective := TratadoAnalisis.Chapter7_0010.positive_cut_square_injective_0010
alias positive_square_two_eq_alphaTwo := TratadoAnalisis.Chapter7_0010.positive_square_two_eq_alphaTwo_0010
alias positive_square_two_exists_unique := TratadoAnalisis.Chapter7_0010.positive_square_two_exists_unique_0010

end TratadoAnalisis.Dedekind
