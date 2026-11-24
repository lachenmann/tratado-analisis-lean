import TratadoAnalisis.Rationals.OrderedField
import TratadoAnalisis.Rationals.NoSupremumSqrtTwo

namespace TratadoAnalisis.Rationals.Signs

universe u

open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Naturals.ArithmeticBridge
open TratadoAnalisis.Integers.Construction
open TratadoAnalisis.Integers.Operations
open TratadoAnalisis.Integers.Multiplication
open TratadoAnalisis.Integers.Algebra
open TratadoAnalisis.Integers.Domain
open TratadoAnalisis.Integers.Order
open TratadoAnalisis.Rationals.IntegerPrep
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.Field
open TratadoAnalisis.Rationals.OrderPrep
open TratadoAnalisis.Rationals.PositiveDenominator
open TratadoAnalisis.Rationals.OrderWellDefined
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.OrderedFieldCompatibility

open TratadoAnalisis.Rationals.StrictOrder
open TratadoAnalisis.Rationals.NoSupremumSqrtTwo

/-- TA-DEF-00056: resta como composición relacional de opuesto y suma. -/
def RatSub (x y z : ZFSet) : Prop :=
  ∃ ny : ZFSet, RatNeg y ny ∧ RatAdd x ny z

theorem TA_DEF_00056_ratSub_iff {x y z : ZFSet} :
    RatSub x y z ↔ ∃ ny : ZFSet, RatNeg y ny ∧ RatAdd x ny z := Iff.rfl

theorem ratSub_exists {x y : ZFSet}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA) :
    ∃ z, z ∈ rationalsTA ∧ RatSub x y z := by
  rcases ratNeg_exists hy with ⟨ny, hny, hn⟩
  rcases ratAdd_exists hx hny with ⟨z, hz, hs⟩
  exact ⟨z, hz, ny, hn, hs⟩

theorem RatSub_unique {x y z w : ZFSet}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (hz : RatSub x y z) (hw : RatSub x y w) : z = w := by
  rcases hz with ⟨ny, hn, hs⟩
  rcases hw with ⟨ny', hn', hs'⟩
  have he : ny' = ny := RatNeg_unique hy hn' hn
  subst ny'
  exact RatAdd_unique hx (funcFoundational_value_mem ratNegGraph_isFunc hn) hs hs'

theorem ratSub_add_cancel {x y z : ZFSet}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (h : RatSub x y z) : RatAdd z y x := by
  rcases h with ⟨ny, hn, hs⟩
  exact ratSub_add_cancel_local hx hy hn hs

theorem ratSub_positive {x y z : ZFSet}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (hyx : RatLT y x) (h : RatSub x y z) : RatLT ratZero z := by
  rcases h with ⟨ny, hn, hs⟩
  exact ratSub_positive_local hx hy hyx hn hs

theorem ratAdd_comm_rel {x y z : ZFSet}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (h : RatAdd x y z) : RatAdd y x z := by
  rcases ratAdd_exists hy hx with ⟨w, _, hw⟩
  have he := ratAdd_comm hx hy h hw
  rw [he]
  exact hw

theorem ratMul_comm_rel {x y z : ZFSet}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (h : RatMul x y z) : RatMul y x z := by
  rcases ratMul_exists hy hx with ⟨w, _, hw⟩
  have he := ratMul_comm hx hy h hw
  rw [he]
  exact hw

theorem ratAdd_neg_right_rel {x nx : ZFSet}
    (hx : x ∈ rationalsTA) (hn : RatNeg x nx) : RatAdd x nx ratZero := by
  have hnx := funcFoundational_value_mem ratNegGraph_isFunc hn
  rcases ratAdd_exists hx hnx with ⟨z, _, hs⟩
  have he := ratAdd_neg_right hx hn hs
  rw [he] at hs
  exact hs

theorem ratNeg_of_add_zero {x y : ZFSet}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (h : RatAdd x y ratZero) : RatNeg x y := by
  rcases ratNeg_exists hx with ⟨nx, hnx, hn⟩
  have hnxSum := ratAdd_neg_right_rel hx hn
  have he : y = nx := ratAdd_cancel_right_local hy hnx hx
    (ratAdd_comm_rel hx hy h) (ratAdd_comm_rel hx hnx hnxSum) rfl
  rw [he]
  exact hn

theorem ratNeg_symm_rel {x nx : ZFSet}
    (hx : x ∈ rationalsTA) (hn : RatNeg x nx) : RatNeg nx x := by
  have hnx := funcFoundational_value_mem ratNegGraph_isFunc hn
  exact ratNeg_of_add_zero hnx hx
    (ratAdd_comm_rel hx hnx (ratAdd_neg_right_rel hx hn))

theorem ratMul_neg_right_rel {x y ny xy xny : ZFSet}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (hn : RatNeg y ny) (hxy : RatMul x y xy)
    (hxny : RatMul x ny xny) : RatNeg xy xny := by
  have hny := funcFoundational_value_mem ratNegGraph_isFunc hn
  have hxyMem := funcFoundational_value_mem ratMulGraph_isFunc hxy
  have hxnyMem := funcFoundational_value_mem ratMulGraph_isFunc hxny
  rcases ratAdd_exists hxyMem hxnyMem with ⟨s, _, hs⟩
  have he : ratZero = s := ratMul_add_left hx hy hny
    (ratAdd_neg_right_rel hy hn) (ratMul_zero_right hx) hxy hxny hs
  rw [← he] at hs
  exact ratNeg_of_add_zero hxyMem hxnyMem hs

theorem ratMul_neg_neg_eq {x nx xx nn : ZFSet}
    (hx : x ∈ rationalsTA) (hn : RatNeg x nx)
    (hxx : RatMul x x xx) (hnn : RatMul nx nx nn) : nn = xx := by
  have hnx := funcFoundational_value_mem ratNegGraph_isFunc hn
  have hxxMem := funcFoundational_value_mem ratMulGraph_isFunc hxx
  rcases ratMul_exists hnx hx with ⟨p, hp, hpx⟩
  have hxp := ratMul_comm_rel hnx hx hpx
  have hneg := ratMul_neg_right_rel hx hx hn hxx hxp
  have hneg' := ratMul_neg_right_rel hnx hx hn hpx hnn
  exact RatNeg_unique hp hneg' (ratNeg_symm_rel hxxMem hneg)

/-- TA-LEM-00020, cláusula 3. -/
theorem TA_LEM_00020_clause3_zero_lt_one :
    RatLT (ratZero : ZFSet.{u}) ratOne := ratZero_lt_one

/-- TA-LEM-00020, cláusula 4: cuadrado no negativo. -/
theorem TA_LEM_00020_clause4_square_nonnegative {x xx : ZFSet}
    (hx : x ∈ rationalsTA) (hxx : RatMul x x xx) : RatLE ratZero xx := by
  rcases ratLE_total ratZero_mem_rationalsTA hx with h0x | hx0
  · exact ratLE_mul_nonnegative_compat ratZero_mem_rationalsTA hx hx h0x h0x
      (ratMul_zero_left hx) hxx
  · rcases ratNeg_exists hx with ⟨nx, hnx, hn⟩
    have hxnx := ratAdd_neg_right_rel hx hn
    rcases ratAdd_exists ratZero_mem_rationalsTA hnx with ⟨z, _, hz⟩
    have he := ratAdd_zero_left hnx hz
    rw [he] at hz
    have h0nx : RatLE ratZero nx := ratLE_add_compat hx ratZero_mem_rationalsTA
      hnx hx0 hxnx hz
    rcases ratMul_exists hnx hnx with ⟨nn, _, hnn⟩
    have h0nn := ratLE_mul_nonnegative_compat ratZero_mem_rationalsTA hnx hnx
      h0nx h0nx (ratMul_zero_left hnx) hnn
    rw [ratMul_neg_neg_eq hx hn hxx hnn] at h0nn
    exact h0nn

/-- TA-LEM-00020, cláusula 5. -/
theorem TA_LEM_00020_clause5_positive_product {x y xy : ZFSet}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (hm : RatMul x y xy) (h0x : RatLT ratZero x) (h0y : RatLT ratZero y) :
    RatLT ratZero xy := ratPositive_mul hx hy hm h0x h0y

/-- TA-LEM-00020, cláusula 6. -/
theorem TA_LEM_00020_clause6_positive_inverse {x ix : ZFSet}
    (hx : x ∈ rationalsTA) (hi : RatInv x ix) (h0x : RatLT ratZero x) :
    RatLT ratZero ix := ratInv_positive hx hi h0x

/-- TA-LEM-00020, cláusula 8: traducción estricta en ambos sentidos. -/
theorem TA_LEM_00020_clause8_translate_iff {x y r xr yr : ZFSet}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA) (hr : r ∈ rationalsTA)
    (hxr : RatAdd x r xr) (hyr : RatAdd y r yr) :
    RatLT x y ↔ RatLT xr yr :=
  ⟨fun h => ratLT_add_right_local hx hy hr h hxr hyr,
   fun h => ratLT_add_cancel_right_local hx hy hr hxr hyr h⟩

theorem ratLE_mul_positive_iff {x y r xr yr : ZFSet}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA) (hr : r ∈ rationalsTA)
    (h0r : RatLT ratZero r) (hxr : RatMul x r xr) (hyr : RatMul y r yr) :
    RatLE x y ↔ RatLE xr yr := by
  constructor
  · intro h
    exact ratLE_mul_nonnegative_compat hx hy hr h h0r.1 hxr hyr
  · intro h
    rcases ratLE_total hx hy with hxy | hyx
    · exact hxy
    · have hrev := ratLE_mul_nonnegative_compat hy hx hr hyx h0r.1 hyr hxr
      have he := ratLE_antisymm
        (funcFoundational_value_mem ratMulGraph_isFunc hxr)
        (funcFoundational_value_mem ratMulGraph_isFunc hyr) h hrev
      have hxy := ratMul_cancel_right_of_nonzero hx hy hr
        (fun e => h0r.2 e.symm) hxr hyr he
      rw [hxy]
      exact ratLE_refl hy

/-- TA-LEM-00020, cláusula 9: multiplicación por positivo en ambos sentidos. -/
theorem TA_LEM_00020_clause9_scale_iff {x y r xr yr : ZFSet}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA) (hr : r ∈ rationalsTA)
    (h0r : RatLT ratZero r) (hxr : RatMul x r xr) (hyr : RatMul y r yr) :
    RatLT x y ↔ RatLT xr yr := by
  constructor
  · intro h
    exact ratLT_mul_positive_right hx hy hr h h0r hxr hyr
  · intro h
    refine ⟨(ratLE_mul_positive_iff hx hy hr h0r hxr hyr).mpr h.1, ?_⟩
    intro he
    apply h.2
    apply RatMul_unique hx hr hxr
    rw [he]
    exact hyr

end TratadoAnalisis.Rationals.Signs


namespace TratadoAnalisis.Rationals.Signs
universe u
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.OrderedFieldCompatibility
open TratadoAnalisis.Rationals.NoSupremumSqrtTwo

theorem ratNeg_le_reverse {x y nx ny : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (hnx : RatNeg x nx) (hny : RatNeg y ny)
    (hxy : RatLE x y) : RatLE ny nx := by
  have hnxQ := funcFoundational_value_mem ratNegGraph_isFunc hnx
  have hnyQ := funcFoundational_value_mem ratNegGraph_isFunc hny
  rcases ratAdd_exists hx hnyQ with ⟨t, _, ht⟩
  have ht0 : RatLE t ratZero :=
    ratLE_add_compat hx hy hnyQ hxy ht (ratAdd_neg_right_rel hy hny)
  have hnyx : RatAdd ny x t := ratAdd_comm_rel hx hnyQ ht
  have hnxx : RatAdd nx x ratZero :=
    ratAdd_comm_rel hx hnxQ (ratAdd_neg_right_rel hx hnx)
  exact ratLE_add_cancel_right_local hnyQ hnxQ hx hnyx hnxx ht0

/-- TA-LEM-00020(2), forma no estricta, especializada a Q. -/
theorem TA_LEM_00020_clause2_neg_le_iff {x y nx ny : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (hnx : RatNeg x nx) (hny : RatNeg y ny) :
    RatLE x y ↔ RatLE ny nx := by
  constructor
  · exact ratNeg_le_reverse hx hy hnx hny
  · intro h
    exact ratNeg_le_reverse
      (funcFoundational_value_mem ratNegGraph_isFunc hny)
      (funcFoundational_value_mem ratNegGraph_isFunc hnx)
      (ratNeg_symm_rel hy hny) (ratNeg_symm_rel hx hnx) h

/-- TA-LEM-00020(2), consecuencia estricta, sin em. -/
theorem TA_LEM_00020_clause2_neg_lt_iff {x y nx ny : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (hnx : RatNeg x nx) (hny : RatNeg y ny) :
    RatLT x y ↔ RatLT ny nx := by
  constructor
  · intro h
    refine ⟨(TA_LEM_00020_clause2_neg_le_iff hx hy hnx hny).mp h.1, ?_⟩
    intro he
    apply h.2
    apply RatNeg_unique (funcFoundational_value_mem ratNegGraph_isFunc hnx)
      (ratNeg_symm_rel hx hnx)
    rw [← he]
    exact ratNeg_symm_rel hy hny
  · intro h
    refine ⟨(TA_LEM_00020_clause2_neg_le_iff hx hy hnx hny).mpr h.1, ?_⟩
    intro he
    apply h.2
    exact RatNeg_unique hy hny (he ▸ hnx)

end TratadoAnalisis.Rationals.Signs
