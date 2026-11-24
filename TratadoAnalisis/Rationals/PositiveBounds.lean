import TratadoAnalisis.Rationals.PositiveProducts
import TratadoAnalisis.Rationals.Trichotomy

namespace TratadoAnalisis.Rationals.PositiveBounds
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

theorem rational_min_witness {x y : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA) :
    ∃ m : ZFSet.{u}, m ∈ rationalsTA ∧ (m = x ∨ m = y) ∧ RatLE m x ∧ RatLE m y := by
  rcases TA_PRO_00172_rational_trichotomy hx hy with h | he | h
  · exact ⟨x, hx, Or.inl rfl, ratLE_refl hx, h.1⟩
  · exact ⟨x, hx, Or.inl rfl, ratLE_refl hx, he ▸ ratLE_refl hx⟩
  · exact ⟨y, hy, Or.inr rfl, h.1, ratLE_refl hy⟩

theorem rational_max_witness {x y : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA) :
    ∃ m : ZFSet.{u}, m ∈ rationalsTA ∧ (m = x ∨ m = y) ∧ RatLE x m ∧ RatLE y m := by
  rcases TA_PRO_00172_rational_trichotomy hx hy with h | he | h
  · exact ⟨y, hy, Or.inr rfl, h.1, ratLE_refl hy⟩
  · exact ⟨x, hx, Or.inl rfl, ratLE_refl hx, he ▸ ratLE_refl hx⟩
  · exact ⟨x, hx, Or.inl rfl, ratLE_refl hx, h.1⟩

end TratadoAnalisis.Rationals.PositiveBounds
