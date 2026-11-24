import TratadoAnalisis.Rationals.Division

namespace TratadoAnalisis.Rationals.PositiveProducts
universe u
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.Field
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.OrderedFieldCompatibility
open TratadoAnalisis.Rationals.StrictOrder
open TratadoAnalisis.Rationals.NoSupremumSqrtTwo
open TratadoAnalisis.Rationals.Signs
open TratadoAnalisis.Rationals.Division

theorem ratMul_value_mem {x y z : ZFSet.{u}} (h : RatMul x y z) :
    z ∈ rationalsTA :=
  funcFoundational_value_mem ratMulGraph_isFunc h

theorem ratDiv_value_mem {x y d : ZFSet.{u}} (h : RatDiv x y d) :
    d ∈ rationalsTA := by
  rcases h with ⟨iy, _, hm⟩
  exact ratMul_value_mem hm

theorem ratMul_one_left_rel {x : ZFSet.{u}} (hx : x ∈ rationalsTA) :
    RatMul ratOne x x := by
  rcases ratMul_exists ratOne_mem_rationalsTA hx with ⟨z, _, hm⟩
  have he := ratMul_one_left hx hm
  rw [he] at hm
  exact hm

theorem ratDiv_mul_denominator {x y d : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (h0y : RatLT ratZero y) (hd : RatDiv x y d) : RatMul d y x := by
  rcases hd with ⟨iy, hi, hm⟩
  exact ratQuotient_mul_denominator_local hx hy h0y hi hm

theorem ratDiv_positive {x y d : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (h0x : RatLT ratZero x) (h0y : RatLT ratZero y)
    (hd : RatDiv x y d) : RatLT ratZero d := by
  rcases hd with ⟨iy, hi, hm⟩
  have hiy := (mem_ratNonzeroTA_iff.mp
    (funcFoundational_value_mem ratInvGraph_isFunc hi)).1
  exact TA_LEM_00020_clause5_positive_product hx hiy hm h0x
    (TA_LEM_00020_clause6_positive_inverse hy hi h0y)

theorem ratDiv_lt_iff {x y b d yb : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (hb : b ∈ rationalsTA) (h0b : RatLT ratZero b)
    (hd : RatDiv x b d) (hyb : RatMul y b yb) :
    RatLT d y ↔ RatLT x yb :=
  TA_LEM_00020_clause9_scale_iff (ratDiv_value_mem hd) hy hb h0b
    (ratDiv_mul_denominator hx hb h0b hd) hyb

theorem ratLT_div_iff {x y b d yb : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (hb : b ∈ rationalsTA) (h0b : RatLT ratZero b)
    (hd : RatDiv x b d) (hyb : RatMul y b yb) :
    RatLT y d ↔ RatLT yb x :=
  TA_LEM_00020_clause9_scale_iff hy (ratDiv_value_mem hd) hb h0b
    hyb (ratDiv_mul_denominator hx hb h0b hd)

theorem ratDiv_le_iff {x y b d yb : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (hb : b ∈ rationalsTA) (h0b : RatLT ratZero b)
    (hd : RatDiv x b d) (hyb : RatMul y b yb) :
    RatLE d y ↔ RatLE x yb :=
  ratLE_mul_positive_iff (ratDiv_value_mem hd) hy hb h0b
    (ratDiv_mul_denominator hx hb h0b hd) hyb

theorem ratLE_div_iff {x y b d yb : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (hb : b ∈ rationalsTA) (h0b : RatLT ratZero b)
    (hd : RatDiv x b d) (hyb : RatMul y b yb) :
    RatLE y d ↔ RatLE yb x :=
  ratLE_mul_positive_iff hy (ratDiv_value_mem hd) hb h0b
    hyb (ratDiv_mul_denominator hx hb h0b hd)

theorem ratDiv_lt_one_iff {x b d : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hb : b ∈ rationalsTA)
    (h0b : RatLT ratZero b) (hd : RatDiv x b d) :
    RatLT d ratOne ↔ RatLT x b :=
  ratDiv_lt_iff hx ratOne_mem_rationalsTA hb h0b hd (ratMul_one_left_rel hb)

theorem ratNeg_zero_rel : RatNeg (ratZero : ZFSet.{u}) ratZero := by
  rcases ratNeg_exists (ratZero_mem_rationalsTA : (ratZero : ZFSet.{u}) ∈ rationalsTA)
    with ⟨z, hz, hn⟩
  have hs := ratAdd_neg_right_rel ratZero_mem_rationalsTA hn
  have he := ratAdd_zero_left hz hs
  rw [← he] at hn
  exact hn

theorem ratNeg_positive_iff {x nx : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hn : RatNeg x nx) :
    RatLT ratZero nx ↔ RatLT x ratZero :=
  (TA_LEM_00020_clause2_neg_lt_iff hx ratZero_mem_rationalsTA
    hn ratNeg_zero_rel).symm

theorem ratNeg_negative_iff {x nx : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hn : RatNeg x nx) :
    RatLT nx ratZero ↔ RatLT ratZero x :=
  (TA_LEM_00020_clause2_neg_lt_iff ratZero_mem_rationalsTA hx
    ratNeg_zero_rel hn).symm

theorem ratMul_neg_left_rel {x y nx xy nxy : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (hn : RatNeg x nx) (hxy : RatMul x y xy)
    (hnxy : RatMul nx y nxy) : RatNeg xy nxy :=
  ratMul_neg_right_rel hy hx hn (ratMul_comm_rel hx hy hxy)
    (ratMul_comm_rel (funcFoundational_value_mem ratNegGraph_isFunc hn) hy hnxy)

theorem ratMul_neg_neg_general {x y nx ny xy nn : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (hnx : RatNeg x nx) (hny : RatNeg y ny)
    (hxy : RatMul x y xy) (hnn : RatMul nx ny nn) : nn = xy := by
  have hnxQ := funcFoundational_value_mem ratNegGraph_isFunc hnx
  rcases ratMul_exists hnxQ hy with ⟨nxy, hnxyQ, hnxy⟩
  have hfirst := ratMul_neg_left_rel hx hy hnx hxy hnxy
  have hsecond := ratMul_neg_right_rel hnxQ hy hny hnxy hnn
  exact RatNeg_unique hnxyQ hsecond (ratNeg_symm_rel (ratMul_value_mem hxy) hfirst)

theorem ratMul_negative_positive {x y xy : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (hxy : RatMul x y xy) (hx0 : RatLT x ratZero)
    (h0y : RatLT ratZero y) : RatLT xy ratZero :=
  ratLT_mul_positive_right hx ratZero_mem_rationalsTA hy hx0 h0y hxy
    (ratMul_zero_left hy)

theorem ratMul_positive_negative {x y xy : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (hxy : RatMul x y xy) (h0x : RatLT ratZero x)
    (hy0 : RatLT y ratZero) : RatLT xy ratZero :=
  ratMul_negative_positive hy hx (ratMul_comm_rel hx hy hxy) hy0 h0x

theorem ratMul_negative_negative {x y xy : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (hxy : RatMul x y xy) (hx0 : RatLT x ratZero)
    (hy0 : RatLT y ratZero) : RatLT ratZero xy := by
  rcases ratNeg_exists hx with ⟨nx, hnxQ, hnx⟩
  rcases ratNeg_exists hy with ⟨ny, hnyQ, hny⟩
  rcases ratMul_exists hnxQ hnyQ with ⟨nn, _, hnn⟩
  have hp := TA_LEM_00020_clause5_positive_product hnxQ hnyQ hnn
    ((ratNeg_positive_iff hx hnx).mpr hx0) ((ratNeg_positive_iff hy hny).mpr hy0)
  rw [ratMul_neg_neg_general hx hy hnx hny hxy hnn] at hp
  exact hp

end TratadoAnalisis.Rationals.PositiveProducts
