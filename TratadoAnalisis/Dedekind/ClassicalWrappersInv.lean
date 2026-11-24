import TratadoAnalisis.Dedekind.Division
import TratadoAnalisis.Dedekind.MultiplicativeOrder

namespace TratadoAnalisis.Dedekind.ClassicalWrappersInv
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
open TratadoAnalisis.Dedekind.Nonzero
open TratadoAnalisis.Dedekind.PositiveInverse
open TratadoAnalisis.Dedekind.TranslationOrder
open TratadoAnalisis.Dedekind.MultiplicativeOrder
open TratadoAnalisis.Dedekind.PositiveInverseLaw
open TratadoAnalisis.Dedekind.Inverse
open TratadoAnalisis.Dedekind.Division

/-- Instanciaciones clásicas autorizadas por la regla 17. -/
theorem TA_PRO_00098_positiveInv_mem 
    {α : ZFSet.{u}} (hα : α ∈ positiveCutsTA) :
    dedPositiveInv α ∈ positiveCutsTA :=
  TratadoAnalisis.Dedekind.PositiveInverse.TA_PRO_00098_positiveInv_mem Classical.em hα

theorem TA_DEF_00100_positiveInvGraph_isFunc  :
    IsFuncFoundational (positiveCutsTA : ZFSet.{u}) positiveCutsTA positiveInvGraph :=
  TratadoAnalisis.Dedekind.PositiveInverse.TA_DEF_00100_positiveInvGraph_isFunc Classical.em 

theorem TA_DEF_00100_positiveInvFunction_isTriple  :
    IsFunctionTriple (positiveCutsTA : ZFSet.{u}) positiveCutsTA positiveInvFunction :=
  TratadoAnalisis.Dedekind.PositiveInverse.TA_DEF_00100_positiveInvFunction_isTriple Classical.em 

theorem TA_PRO_00101_dedLE_translate 
    {α β γ : ZFSet.{u}} (hα : α ∈ dedekindCutsTA)
    (hβ : β ∈ dedekindCutsTA) (hγ : γ ∈ dedekindCutsTA) :
    DedLE α β ↔ DedLE (dedAdd α γ) (dedAdd β γ) :=
  TratadoAnalisis.Dedekind.TranslationOrder.TA_PRO_00101_dedLE_translate Classical.em hα hβ hγ

theorem TA_PRO_00101_dedLT_translate 
    {α β γ : ZFSet.{u}} (hα : α ∈ dedekindCutsTA)
    (hβ : β ∈ dedekindCutsTA) (hγ : γ ∈ dedekindCutsTA) :
    DedLT α β ↔ DedLT (dedAdd α γ) (dedAdd β γ) :=
  TratadoAnalisis.Dedekind.TranslationOrder.TA_PRO_00101_dedLT_translate Classical.em hα hβ hγ

theorem TA_PRO_00101_translation_package 
    {α β γ : ZFSet.{u}} (hα : α ∈ dedekindCutsTA)
    (hβ : β ∈ dedekindCutsTA) (hγ : γ ∈ dedekindCutsTA) :
    (DedLE α β ↔ DedLE (dedAdd α γ) (dedAdd β γ)) ∧
    (DedLT α β ↔ DedLT (dedAdd α γ) (dedAdd β γ)) :=
  TratadoAnalisis.Dedekind.TranslationOrder.TA_PRO_00101_translation_package Classical.em hα hβ hγ

theorem TA_COR_00022_difference_positive_iff 
    {α β : ZFSet.{u}} (hα : α ∈ dedekindCutsTA) (hβ : β ∈ dedekindCutsTA) :
    DedLT α β ↔ DedLT dedZero (dedSub β α) :=
  TratadoAnalisis.Dedekind.TranslationOrder.TA_COR_00022_difference_positive_iff Classical.em hα hβ

theorem TA_PRO_00103_order_compatible  :
    (∀ α β γ : ZFSet.{u}, α ∈ dedekindCutsTA → β ∈ dedekindCutsTA →
      γ ∈ dedekindCutsTA → DedLE α β →
      DedLE (dedAdd α γ) (dedAdd β γ)) ∧
    (∀ α β : ZFSet.{u}, DedLE dedZero α → DedLE dedZero β →
      DedLE dedZero (dedMul α β)) :=
  TratadoAnalisis.Dedekind.MultiplicativeOrder.TA_PRO_00103_order_compatible Classical.em 

theorem TA_THM_00045_positive_inverse_law 
    {α : ZFSet.{u}} (hp : IsPositiveCut α) :
    dedPositiveMul α (dedPositiveInv α) = dedOne ∧
      dedPositiveMul (dedPositiveInv α) α = dedOne :=
  TratadoAnalisis.Dedekind.PositiveInverseLaw.TA_THM_00045_positive_inverse_law Classical.em hp

theorem TA_PRO_00100_signedInv_mem 
    {α : ZFSet.{u}} (hα : α ∈ nonzeroCutsTA) : dedSignedInv α ∈ nonzeroCutsTA :=
  TratadoAnalisis.Dedekind.Inverse.TA_PRO_00100_signedInv_mem Classical.em hα

theorem TA_PRO_00100_sign_package 
    {α : ZFSet.{u}} (hα : α ∈ nonzeroCutsTA) :
    dedSignedInv α ∈ nonzeroCutsTA ∧
      (IsPositiveCut α → IsPositiveCut (dedSignedInv α)) ∧
      (IsNegativeCut α → IsNegativeCut (dedSignedInv α)) :=
  TratadoAnalisis.Dedekind.Inverse.TA_PRO_00100_sign_package Classical.em hα

theorem TA_DEF_00103_dedInvGraph_isFunc  :
    IsFuncFoundational (nonzeroCutsTA : ZFSet.{u}) nonzeroCutsTA dedInvGraph :=
  TratadoAnalisis.Dedekind.Inverse.TA_DEF_00103_dedInvGraph_isFunc Classical.em 

theorem TA_DEF_00103_dedInvFunction_isTriple  :
    IsFunctionTriple (nonzeroCutsTA : ZFSet.{u}) nonzeroCutsTA dedInvFunction :=
  TratadoAnalisis.Dedekind.Inverse.TA_DEF_00103_dedInvFunction_isTriple Classical.em 

theorem TA_THM_00046_inverse_law 
    {α : ZFSet.{u}} (hα : α ∈ nonzeroCutsTA) :
    dedMul α (dedInvValue α) = dedOne ∧ dedMul (dedInvValue α) α = dedOne :=
  TratadoAnalisis.Dedekind.Inverse.TA_THM_00046_inverse_law Classical.em hα

theorem TA_DEF_00251_dedDivGraph_isFunc  :
    IsFuncFoundational
      (cartesianProductFoundational (dedekindCutsTA : ZFSet.{u}) nonzeroCutsTA)
      dedekindCutsTA dedDivGraph :=
  TratadoAnalisis.Dedekind.Division.TA_DEF_00251_dedDivGraph_isFunc Classical.em 

theorem TA_DEF_00251_dedDivFunction_isTriple  :
    IsFunctionTriple
      (cartesianProductFoundational (dedekindCutsTA : ZFSet.{u}) nonzeroCutsTA)
      dedekindCutsTA dedDivFunction :=
  TratadoAnalisis.Dedekind.Division.TA_DEF_00251_dedDivFunction_isTriple Classical.em 



end TratadoAnalisis.Dedekind.ClassicalWrappersInv
