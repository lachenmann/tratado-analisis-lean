import TratadoAnalisis.Dedekind.Unit
import TratadoAnalisis.Rationals.InverseOrder
import TratadoAnalisis.Rationals.DifferenceOrder
import TratadoAnalisis.Rationals.PositiveBounds

namespace TratadoAnalisis.Dedekind.Nonzero
universe u
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.Field
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.OrderedFieldCompatibility
open TratadoAnalisis.Rationals.StrictOrder
open TratadoAnalisis.Rationals.NoSupremumSqrtTwo
open TratadoAnalisis.Rationals.Signs
open TratadoAnalisis.Rationals.Division
open TratadoAnalisis.Rationals.PositiveProducts
open TratadoAnalisis.Rationals.Trichotomy
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.SquareMonotonicity
open TratadoAnalisis.Rationals.InverseOrder
open TratadoAnalisis.Rationals.DifferenceOrder
open TratadoAnalisis.Rationals.PositiveBounds
open TratadoAnalisis.Dedekind.Definition
open TratadoAnalisis.Dedekind.Order
open TratadoAnalisis.Dedekind.RationalSection
open TratadoAnalisis.Dedekind.Addition
open TratadoAnalisis.Dedekind.Negation
open TratadoAnalisis.Dedekind.AdditiveGroup
open TratadoAnalisis.Dedekind.Positivity
open TratadoAnalisis.Dedekind.PositiveMultiplication
open TratadoAnalisis.Dedekind.Signs
open TratadoAnalisis.Dedekind.Multiplication
open TratadoAnalisis.Dedekind.Unit
open TratadoAnalisis.Foundations.FunctionTriple

/-- TA-DEF-00101: dominio negativo, sin decisión del signo. -/
def nonzeroCutsTA : ZFSet.{u} :=
  ZFSet.sep (fun α => α ≠ dedZero) dedekindCutsTA

theorem TA_DEF_00101_mem_nonzeroCuts_iff {α : ZFSet.{u}} :
    α ∈ nonzeroCutsTA ↔ α ∈ dedekindCutsTA ∧ α ≠ dedZero := ZFSet.mem_sep

theorem nonzeroCuts_subset : (nonzeroCutsTA : ZFSet.{u}) ⊆ dedekindCutsTA :=
  fun _ h => (TA_DEF_00101_mem_nonzeroCuts_iff.mp h).1

theorem zero_not_mem_nonzeroCuts : (dedZero : ZFSet.{u}) ∉ nonzeroCutsTA :=
  fun h => (TA_DEF_00101_mem_nonzeroCuts_iff.mp h).2 rfl

end TratadoAnalisis.Dedekind.Nonzero
