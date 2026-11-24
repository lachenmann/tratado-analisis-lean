import TratadoAnalisis.Dedekind.Unit

namespace TratadoAnalisis.Dedekind.ClassicalWrappersMul
universe u
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.Field
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.Trichotomy
open TratadoAnalisis.Rationals.OrderedFieldCompatibility
open TratadoAnalisis.Rationals.StrictOrder
open TratadoAnalisis.Rationals.SquareMonotonicity
open TratadoAnalisis.Rationals.NoSupremumSqrtTwo
open TratadoAnalisis.Rationals.Signs
open TratadoAnalisis.Rationals.Division
open TratadoAnalisis.Rationals.PositiveProducts
open TratadoAnalisis.Dedekind.Definition
open TratadoAnalisis.Dedekind.Order
open TratadoAnalisis.Dedekind.RationalSection
open TratadoAnalisis.Dedekind.Embedding
open TratadoAnalisis.Dedekind.Addition
open TratadoAnalisis.Dedekind.Negation
open TratadoAnalisis.Dedekind.AdditiveGroup
open TratadoAnalisis.Dedekind.Positivity
open TratadoAnalisis.Dedekind.PositiveMultiplication
open TratadoAnalisis.Dedekind.Signs
open TratadoAnalisis.Dedekind.Multiplication
open TratadoAnalisis.Dedekind.Unit
open TratadoAnalisis.Foundations.FunctionTriple

-- Única frontera clásica nueva de TA-LEAN-0006; elección metateórica de Classical.em.
/-- Versión clásica de TratadoAnalisis.Dedekind.Positivity.TA_LEM_00023_positive_implies_zero_mem. -/
theorem TA_LEM_00023_positive_implies_zero_mem
    {α : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) (hpos : IsPositiveCut α) :
    (ratZero : ZFSet.{u}) ∈ α :=
  TratadoAnalisis.Dedekind.Positivity.TA_LEM_00023_positive_implies_zero_mem Classical.em hα hpos

/-- Versión clásica de TratadoAnalisis.Dedekind.Positivity.TA_LEM_00023_positive_iff_zero_mem. -/
theorem TA_LEM_00023_positive_iff_zero_mem
    {α : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) :
    IsPositiveCut α ↔ (ratZero : ZFSet.{u}) ∈ α :=
  TratadoAnalisis.Dedekind.Positivity.TA_LEM_00023_positive_iff_zero_mem Classical.em hα

/-- Versión clásica de TratadoAnalisis.Dedekind.Positivity.TA_LEM_00023_characterizations. -/
theorem TA_LEM_00023_characterizations
    {α : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) :
    (IsPositiveCut α ↔ (ratZero : ZFSet.{u}) ∈ α) ∧
    ((ratZero : ZFSet.{u}) ∈ α ↔
      ∃ a : ZFSet.{u}, a ∈ α ∧ RatLT ratZero a) ∧
    (IsPositiveCut α ↔
      ∃ a : ZFSet.{u}, a ∈ α ∧ RatLT ratZero a) :=
  TratadoAnalisis.Dedekind.Positivity.TA_LEM_00023_characterizations Classical.em hα

/-- Versión clásica de TratadoAnalisis.Dedekind.PositiveMultiplication.TA_PRO_00090_positiveMul_mem. -/
theorem TA_PRO_00090_positiveMul_mem {α β : ZFSet.{u}} (hα : α ∈ positiveCutsTA) (hβ : β ∈ positiveCutsTA) :
    dedPositiveMul α β ∈ positiveCutsTA :=
  TratadoAnalisis.Dedekind.PositiveMultiplication.TA_PRO_00090_positiveMul_mem Classical.em hα hβ

/-- Versión clásica de TratadoAnalisis.Dedekind.PositiveMultiplication.TA_DEF_00094_positiveMulGraph_isFunc. -/
theorem TA_DEF_00094_positiveMulGraph_isFunc :
    IsFuncFoundational
      (cartesianProductFoundational (positiveCutsTA : ZFSet.{u}) positiveCutsTA)
      positiveCutsTA positiveMulGraph :=
  TratadoAnalisis.Dedekind.PositiveMultiplication.TA_DEF_00094_positiveMulGraph_isFunc Classical.em

/-- Versión clásica de TratadoAnalisis.Dedekind.PositiveMultiplication.TA_DEF_00094_positiveMulFunction_isTriple. -/
theorem TA_DEF_00094_positiveMulFunction_isTriple :
    IsFunctionTriple
      (cartesianProductFoundational (positiveCutsTA : ZFSet.{u}) positiveCutsTA)
      positiveCutsTA positiveMulFunction :=
  TratadoAnalisis.Dedekind.PositiveMultiplication.TA_DEF_00094_positiveMulFunction_isTriple Classical.em

/-- Versión clásica de TratadoAnalisis.Dedekind.Signs.TA_PRO_00093_zero_sign_trichotomy. -/
theorem TA_PRO_00093_zero_sign_trichotomy
    {α : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) :
    IsNegativeCut α ∨ α = dedZero ∨ IsPositiveCut α :=
  TratadoAnalisis.Dedekind.Signs.TA_PRO_00093_zero_sign_trichotomy Classical.em hα

/-- Versión clásica de TratadoAnalisis.Dedekind.Signs.TA_PRO_00093_zero_sign_package. -/
theorem TA_PRO_00093_zero_sign_package
    {α : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) :
    (IsNegativeCut α ∨ α = dedZero ∨ IsPositiveCut α) ∧
    ¬ (IsNegativeCut α ∧ α = dedZero) ∧
    ¬ (IsNegativeCut α ∧ IsPositiveCut α) ∧
    ¬ (α = (dedZero : ZFSet.{u}) ∧ IsPositiveCut α) :=
  TratadoAnalisis.Dedekind.Signs.TA_PRO_00093_zero_sign_package Classical.em hα

/-- Versión clásica de TratadoAnalisis.Dedekind.Signs.TA_LEM_00024_negative_iff_positive_neg. -/
theorem TA_LEM_00024_negative_iff_positive_neg
    {α : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) :
    IsNegativeCut α ↔ IsPositiveCut (dedNeg α) :=
  TratadoAnalisis.Dedekind.Signs.TA_LEM_00024_negative_iff_positive_neg Classical.em hα

/-- Versión clásica de TratadoAnalisis.Dedekind.Signs.TA_LEM_00024_positive_iff_negative_neg. -/
theorem TA_LEM_00024_positive_iff_negative_neg
    {α : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) :
    IsPositiveCut α ↔ IsNegativeCut (dedNeg α) :=
  TratadoAnalisis.Dedekind.Signs.TA_LEM_00024_positive_iff_negative_neg Classical.em hα

/-- Versión clásica de TratadoAnalisis.Dedekind.Signs.TA_LEM_00024_sign_negation_package. -/
theorem TA_LEM_00024_sign_negation_package
    {α : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) :
    (IsNegativeCut α ↔ IsPositiveCut (dedNeg α)) ∧
    (IsPositiveCut α ↔ IsNegativeCut (dedNeg α)) ∧
    dedNeg (dedZero : ZFSet.{u}) = dedZero :=
  TratadoAnalisis.Dedekind.Signs.TA_LEM_00024_sign_negation_package Classical.em hα

/-- Versión clásica de TratadoAnalisis.Dedekind.Multiplication.TA_PRO_00094_dedSignedMul_mem. -/
theorem TA_PRO_00094_dedSignedMul_mem {α β : ZFSet.{u}} (hα : α ∈ dedekindCutsTA) (hβ : β ∈ dedekindCutsTA) :
    dedSignedMul α β ∈ dedekindCutsTA :=
  TratadoAnalisis.Dedekind.Multiplication.TA_PRO_00094_dedSignedMul_mem Classical.em hα hβ

/-- Versión clásica de TratadoAnalisis.Dedekind.Multiplication.TA_PRO_00094_closure_sign_package. -/
theorem TA_PRO_00094_closure_sign_package {α β : ZFSet.{u}} (hα : α ∈ dedekindCutsTA) (hβ : β ∈ dedekindCutsTA) :
    dedSignedMul α β ∈ dedekindCutsTA ∧
    ((α = dedZero ∨ β = dedZero) → dedSignedMul α β = dedZero) ∧
    (((IsPositiveCut α ∧ IsPositiveCut β) ∨ (IsNegativeCut α ∧ IsNegativeCut β)) →
      IsPositiveCut (dedSignedMul α β)) ∧
    (((IsPositiveCut α ∧ IsNegativeCut β) ∨ (IsNegativeCut α ∧ IsPositiveCut β)) →
      IsNegativeCut (dedSignedMul α β)) :=
  TratadoAnalisis.Dedekind.Multiplication.TA_PRO_00094_closure_sign_package Classical.em hα hβ

/-- Versión clásica de TratadoAnalisis.Dedekind.Multiplication.TA_DEF_00097_dedMulGraph_isFunc. -/
theorem TA_DEF_00097_dedMulGraph_isFunc :
    IsFuncFoundational
      (cartesianProductFoundational (dedekindCutsTA : ZFSet.{u}) dedekindCutsTA)
      dedekindCutsTA dedMulGraph :=
  TratadoAnalisis.Dedekind.Multiplication.TA_DEF_00097_dedMulGraph_isFunc Classical.em

/-- Versión clásica de TratadoAnalisis.Dedekind.Multiplication.TA_DEF_00097_dedMulFunction_isTriple. -/
theorem TA_DEF_00097_dedMulFunction_isTriple :
    IsFunctionTriple
      (cartesianProductFoundational (dedekindCutsTA : ZFSet.{u}) dedekindCutsTA)
      dedekindCutsTA dedMulFunction :=
  TratadoAnalisis.Dedekind.Multiplication.TA_DEF_00097_dedMulFunction_isTriple Classical.em

/-- Versión clásica de TratadoAnalisis.Dedekind.Unit.TA_LEM_00025_dedNeg_involutive. -/
theorem TA_LEM_00025_dedNeg_involutive
    {α : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) : dedNeg (dedNeg α) = α :=
  TratadoAnalisis.Dedekind.Unit.TA_LEM_00025_dedNeg_involutive Classical.em hα

/-- Versión clásica de TratadoAnalisis.Dedekind.Unit.TA_PRO_00097_positiveMul_one. -/
theorem TA_PRO_00097_positiveMul_one
    {α : ZFSet.{u}} (hα : IsPositiveCut α) :
    dedPositiveMul α dedOne = α ∧ dedPositiveMul dedOne α = α :=
  TratadoAnalisis.Dedekind.Unit.TA_PRO_00097_positiveMul_one Classical.em hα

/-- Versión clásica de TratadoAnalisis.Dedekind.Unit.TA_THM_00044_dedMul_one. -/
theorem TA_THM_00044_dedMul_one
    {α : ZFSet.{u}} (hα : α ∈ dedekindCutsTA) :
    dedMul α dedOne = α ∧ dedMul dedOne α = α :=
  TratadoAnalisis.Dedekind.Unit.TA_THM_00044_dedMul_one Classical.em hα

end TratadoAnalisis.Dedekind.ClassicalWrappersMul
