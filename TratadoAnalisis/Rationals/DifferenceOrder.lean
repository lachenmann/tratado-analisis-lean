import TratadoAnalisis.Rationals.PositiveProducts
import TratadoAnalisis.Rationals.Trichotomy

namespace TratadoAnalisis.Rationals.DifferenceOrder
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

theorem zero_add_rel {x : ZFSet.{u}} (hx : x ∈ rationalsTA) :
    RatAdd ratZero x x := by
  rcases ratAdd_exists ratZero_mem_rationalsTA hx with ⟨z, _, hz⟩
  have he := ratAdd_zero_left hx hz
  rw [he] at hz
  exact hz

theorem TA_LEM_00020_clause1_sub_le_iff {x y d : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA) (hd : RatSub y x d) :
    RatLE x y ↔ RatLE ratZero d := by
  have hm := ratSub_add_cancel hy hx hd
  have hdQ : d ∈ rationalsTA := by
    rcases hd with ⟨nx, hn, hs⟩
    exact funcFoundational_value_mem ratAddGraph_isFunc hs
  constructor
  · intro h
    exact ratLE_add_cancel_right_local ratZero_mem_rationalsTA hdQ hx
      (zero_add_rel hx) hm h
  · intro h
    exact ratLE_add_compat ratZero_mem_rationalsTA hdQ hx h (zero_add_rel hx) hm

theorem ratSub_lt_iff {x y d : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA) (hd : RatSub y x d) :
    RatLT x y ↔ RatLT ratZero d := by
  have hm := ratSub_add_cancel hy hx hd
  have hdQ : d ∈ rationalsTA := by
    rcases hd with ⟨nx, hn, hs⟩
    exact funcFoundational_value_mem ratAddGraph_isFunc hs
  exact (TA_LEM_00020_clause8_translate_iff ratZero_mem_rationalsTA hdQ hx
    (zero_add_rel hx) hm).symm

end TratadoAnalisis.Rationals.DifferenceOrder
