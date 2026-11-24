import TratadoAnalisis.Dedekind.PositiveDistributivity
import TratadoAnalisis.Dedekind.TranslationOrder

namespace TratadoAnalisis.Dedekind.AdditiveIdentities
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

theorem dedAdd_interchange (em : ∀ p : Prop, p ∨ ¬p)
    {α β γ δ : ZFSet.{u}} (ha : α ∈ dedekindCutsTA) (hb : β ∈ dedekindCutsTA)
    (hc : γ ∈ dedekindCutsTA) (hd : δ ∈ dedekindCutsTA) :
    dedAdd (dedAdd α β) (dedAdd γ δ) = dedAdd (dedAdd α γ) (dedAdd β δ) := by
  calc
    _ = dedAdd α (dedAdd β (dedAdd γ δ)) := TA_THM_00041_dedAdd_assoc ha hb (TA_PRO_00084_dedAdd_mem em hc hd)
    _ = dedAdd α (dedAdd (dedAdd β γ) δ) := congrArg (dedAdd α) (TA_THM_00041_dedAdd_assoc hb hc hd).symm
    _ = dedAdd α (dedAdd (dedAdd γ β) δ) := congrArg (fun z => dedAdd α (dedAdd z δ)) (TA_THM_00042_dedAdd_comm hb hc)
    _ = dedAdd α (dedAdd γ (dedAdd β δ)) := congrArg (dedAdd α) (TA_THM_00041_dedAdd_assoc hc hb hd)
    _ = _ := (TA_THM_00041_dedAdd_assoc ha hc (TA_PRO_00084_dedAdd_mem em hb hd)).symm

theorem TA_LEM_00026_neg_add (em : ∀ p : Prop, p ∨ ¬p)
    {α β : ZFSet.{u}} (hα : α ∈ dedekindCutsTA) (hβ : β ∈ dedekindCutsTA) :
    dedNeg (dedAdd α β) = dedAdd (dedNeg α) (dedNeg β) := by
  have hs := TA_PRO_00084_dedAdd_mem em hα hβ
  have hnα := TA_PRO_00087_dedNeg_mem em hα
  have hnβ := TA_PRO_00087_dedNeg_mem em hβ
  apply TA_PRO_00089_dedAdd_cancel_left em (TA_PRO_00087_dedNeg_mem em hs)
    (TA_PRO_00084_dedAdd_mem em hnα hnβ) hs
  rw [(TA_COR_00020_dedAdd_neg_bilateral em hs).1,
    dedAdd_interchange em hα hβ hnα hnβ,
    (TA_COR_00020_dedAdd_neg_bilateral em hα).1,
    (TA_COR_00020_dedAdd_neg_bilateral em hβ).1,
    (TA_PRO_00086_dedZero_neutral dedZero_mem).1]


end TratadoAnalisis.Dedekind.AdditiveIdentities
