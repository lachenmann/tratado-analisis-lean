import TratadoAnalisis.Dedekind.EmbeddingField

namespace TratadoAnalisis.Dedekind.ClassicalWrappersField
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
open TratadoAnalisis.Dedekind.PositiveDistributivity
open TratadoAnalisis.Dedekind.AdditiveIdentities
open TratadoAnalisis.Dedekind.ProductSignLaws
open TratadoAnalisis.Dedekind.MultiplicativeLaws
open TratadoAnalisis.Dedekind.Distributivity
open TratadoAnalisis.Dedekind.FieldPredicates
open TratadoAnalisis.Dedekind.Field
open TratadoAnalisis.Dedekind.OrderedField
open TratadoAnalisis.Dedekind.EmbeddingField
open TratadoAnalisis.Dedekind.Nonzero
open TratadoAnalisis.Dedekind.Inverse
open TratadoAnalisis.Dedekind.Division
open TratadoAnalisis.Dedekind.Embedding
open TratadoAnalisis.Dedekind.EmbeddingTriple

/-- Envoltorios autorizados por la regla 17; ningún módulo matemático los importa. -/
theorem TA_THM_00049_positiveMul_distrib 
    {α β γ : ZFSet.{u}} (hα : IsPositiveCut α) (hβ : IsPositiveCut β) (hγ : IsPositiveCut γ) :
    dedPositiveMul α (dedAdd β γ) = dedAdd (dedPositiveMul α β) (dedPositiveMul α γ) :=
  TratadoAnalisis.Dedekind.PositiveDistributivity.TA_THM_00049_positiveMul_distrib Classical.em hα hβ hγ

theorem TA_LEM_00026_neg_add 
    {α β : ZFSet.{u}} (hα : α ∈ dedekindCutsTA) (hβ : β ∈ dedekindCutsTA) :
    dedNeg (dedAdd α β) = dedAdd (dedNeg α) (dedNeg β) :=
  TratadoAnalisis.Dedekind.AdditiveIdentities.TA_LEM_00026_neg_add Classical.em hα hβ

theorem TA_LEM_00027_product_signs 
    {α β : ZFSet.{u}} (hα : α ∈ dedekindCutsTA) (hβ : β ∈ dedekindCutsTA) :
    dedMul (dedNeg α) β = dedNeg (dedMul α β) ∧
      dedMul α (dedNeg β) = dedNeg (dedMul α β) ∧
      dedMul (dedNeg α) (dedNeg β) = dedMul α β :=
  TratadoAnalisis.Dedekind.ProductSignLaws.TA_LEM_00027_product_signs Classical.em hα hβ

theorem TA_THM_00051_dedMul_assoc 
    {α β γ : ZFSet.{u}} (hα : α ∈ dedekindCutsTA)
    (hβ : β ∈ dedekindCutsTA) (hγ : γ ∈ dedekindCutsTA) :
    dedMul (dedMul α β) γ = dedMul α (dedMul β γ) :=
  TratadoAnalisis.Dedekind.MultiplicativeLaws.TA_THM_00051_dedMul_assoc Classical.em hα hβ hγ

theorem TA_PRO_00102_positive_factor_distrib 
    {α β γ : ZFSet.{u}} (ha : IsPositiveCut α)
    (hb : β ∈ dedekindCutsTA) (hc : γ ∈ dedekindCutsTA) :
    dedMul α (dedAdd β γ) = dedAdd (dedMul α β) (dedMul α γ) :=
  TratadoAnalisis.Dedekind.Distributivity.TA_PRO_00102_positive_factor_distrib Classical.em ha hb hc

theorem TA_THM_00052_dedMul_distrib 
    {α β γ : ZFSet.{u}} (ha : α ∈ dedekindCutsTA)
    (hb : β ∈ dedekindCutsTA) (hc : γ ∈ dedekindCutsTA) :
    dedMul α (dedAdd β γ) = dedAdd (dedMul α β) (dedMul α γ) ∧
      dedMul (dedAdd β γ) α = dedAdd (dedMul β α) (dedMul γ α) :=
  TratadoAnalisis.Dedekind.Distributivity.TA_THM_00052_dedMul_distrib Classical.em ha hb hc

theorem TA_THM_00053_dedekind_field  :
    IsFieldFoundational (dedekindCutsTA : ZFSet.{u}) dedZero dedOne CutAdd CutMul :=
  TratadoAnalisis.Dedekind.Field.TA_THM_00053_dedekind_field Classical.em 

theorem TA_THM_00054_dedekind_orderedField  :
    IsOrderedFieldFoundational (dedekindCutsTA : ZFSet.{u}) dedZero dedOne CutAdd CutMul DedLE :=
  TratadoAnalisis.Dedekind.OrderedField.TA_THM_00054_dedekind_orderedField Classical.em 

theorem TA_COR_00023_orderedField_embedding  :
    IsOrderedFieldEmbeddingFoundational (rationalsTA : ZFSet.{u}) dedekindCutsTA
      ratZero ratOne dedZero dedOne RatAdd RatMul CutAdd CutMul RatLE DedLE
      rationalSection dedekindEmbeddingGraph dedekindEmbeddingFunction :=
  TratadoAnalisis.Dedekind.EmbeddingField.TA_COR_00023_orderedField_embedding Classical.em 

theorem TA_COR_00024_rationalSection_inv 
    {p pi : ZFSet.{u}} (hp : p ∈ rationalsTA) (hp0 : p ≠ ratZero) (hi : RatInv p pi) :
    rationalSection pi = dedInvValue (rationalSection p) :=
  TratadoAnalisis.Dedekind.EmbeddingField.TA_COR_00024_rationalSection_inv Classical.em hp hp0 hi



end TratadoAnalisis.Dedekind.ClassicalWrappersField
