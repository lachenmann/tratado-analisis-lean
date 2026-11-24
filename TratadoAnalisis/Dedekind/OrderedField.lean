import TratadoAnalisis.Dedekind.Field
import TratadoAnalisis.Dedekind.MultiplicativeOrder

namespace TratadoAnalisis.Dedekind.OrderedField
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

open TratadoAnalisis.Dedekind.FieldPredicates
open TratadoAnalisis.Dedekind.Field
open TratadoAnalisis.Dedekind.MultiplicativeOrder

theorem TA_THM_00054_dedekind_orderedField (em : ∀ p : Prop, p ∨ ¬p) :
    IsOrderedFieldFoundational (dedekindCutsTA : ZFSet.{u}) dedZero dedOne CutAdd CutMul DedLE := by
  refine ⟨TA_THM_00053_dedekind_field em, ?_, ?_, ?_⟩
  · exact ⟨fun _ hx => dedLE_refl hx,
      fun _ _ _ _ hxy hyx => dedLE_antisymm hxy hyx,
      fun _ _ _ _ _ _ hxy hyz => dedLE_trans hxy hyz,
      fun _ _ hx hy => TA_THM_00040_dedLE_total em hx hy⟩
  · rintro x y z xz yz hx hy hz hxy rfl rfl
    exact (TA_PRO_00103_order_compatible em).1 x y z hx hy hz hxy
  · rintro x y xy _ _ h0x h0y rfl
    exact (TA_PRO_00103_order_compatible em).2 x y h0x h0y


end TratadoAnalisis.Dedekind.OrderedField
