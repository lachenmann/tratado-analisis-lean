import TratadoAnalisis.Rationals.PositiveProducts
import TratadoAnalisis.Rationals.Trichotomy

namespace TratadoAnalisis.Rationals.InverseOrder
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

theorem positive_inv_le_iff {x y ix iy : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (h0x : RatLT ratZero x) (h0y : RatLT ratZero y)
    (hix : RatInv x ix) (hiy : RatInv y iy) :
    RatLE iy ix ↔ RatLE x y := by
  have hixQ := (mem_ratNonzeroTA_iff.mp (funcFoundational_value_mem ratInvGraph_isFunc hix)).1
  have hiyQ := (mem_ratNonzeroTA_iff.mp (funcFoundational_value_mem ratInvGraph_isFunc hiy)).1
  have lx := TA_PRO_00063_inverse_law (mem_ratNonzeroTA_iff.mpr ⟨hx, fun h => h0x.2 h.symm⟩) hix
  have ly := TA_PRO_00063_inverse_law (mem_ratNonzeroTA_iff.mpr ⟨hy, fun h => h0y.2 h.symm⟩) hiy
  rcases ratMul_exists hx hiyQ with ⟨t, _, ht⟩
  exact (ratLE_mul_positive_iff hiyQ hixQ hx h0x
    (ratMul_comm_rel hx hiyQ ht) lx.2).trans
    (ratLE_mul_positive_iff hx hy hiyQ
      (TA_LEM_00020_clause6_positive_inverse hy hiy h0y) ht ly.1).symm

theorem positive_inv_lt_iff {x y ix iy : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (h0x : RatLT ratZero x) (h0y : RatLT ratZero y)
    (hix : RatInv x ix) (hiy : RatInv y iy) :
    RatLT iy ix ↔ RatLT x y := by
  have hixQ := (mem_ratNonzeroTA_iff.mp (funcFoundational_value_mem ratInvGraph_isFunc hix)).1
  have hiyQ := (mem_ratNonzeroTA_iff.mp (funcFoundational_value_mem ratInvGraph_isFunc hiy)).1
  have lx := TA_PRO_00063_inverse_law (mem_ratNonzeroTA_iff.mpr ⟨hx, fun h => h0x.2 h.symm⟩) hix
  have ly := TA_PRO_00063_inverse_law (mem_ratNonzeroTA_iff.mpr ⟨hy, fun h => h0y.2 h.symm⟩) hiy
  rcases ratMul_exists hx hiyQ with ⟨t, _, ht⟩
  exact (TA_LEM_00020_clause9_scale_iff hiyQ hixQ hx h0x
    (ratMul_comm_rel hx hiyQ ht) lx.2).trans
    (TA_LEM_00020_clause9_scale_iff hx hy hiyQ
      (TA_LEM_00020_clause6_positive_inverse hy hiy h0y) ht ly.1).symm

theorem TA_LEM_00020_clause7_positive_inv_order {x y ix iy : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (h0x : RatLT ratZero x) (hxy : RatLT x y)
    (hix : RatInv x ix) (hiy : RatInv y iy) :
    RatLT ratZero iy ∧ RatLT iy ix := by
  have h0y := ratLT_of_lt_of_le_local ratZero_mem_rationalsTA hx hy h0x hxy.1
  exact ⟨TA_LEM_00020_clause6_positive_inverse hy hiy h0y,
    (positive_inv_lt_iff hx hy h0x h0y hix hiy).mpr hxy⟩

theorem TA_LEM_00020_clause7_positive_inv_le {x y ix iy : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (h0x : RatLT ratZero x) (h0y : RatLT ratZero y)
    (hix : RatInv x ix) (hiy : RatInv y iy) :
    RatLE x y ↔ RatLE iy ix :=
  (positive_inv_le_iff hx hy h0x h0y hix hiy).symm

end TratadoAnalisis.Rationals.InverseOrder
