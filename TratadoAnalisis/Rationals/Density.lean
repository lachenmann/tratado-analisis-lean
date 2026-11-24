import TratadoAnalisis.Rationals.Trichotomy

namespace TratadoAnalisis.Rationals.Density

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

open TratadoAnalisis.Rationals.Signs
open TratadoAnalisis.Rationals.NoSupremumSqrtTwo
open TratadoAnalisis.Rationals.IrrationalitySqrtTwo
open TratadoAnalisis.Rationals.SqrtTwoSet

/-- El producto de la suma por el inverso de dos queda entre los extremos. -/
theorem rational_midpoint_between {x y s i2 m : ZFSet}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (hxy : RatLT x y) (hs : RatAdd x y s)
    (hi : RatInv ratTwoTA i2) (hm : RatMul s i2 m) :
    RatLT x m ∧ RatLT m y := by
  have hsMem := funcFoundational_value_mem ratAddGraph_isFunc hs
  have hmMem := funcFoundational_value_mem ratMulGraph_isFunc hm
  have hmTwo : RatMul m ratTwoTA s := ratQuotient_mul_denominator_local
    hsMem ratTwoTA_mem_rationalsTA ratZero_lt_two_local hi hm
  rcases ratMul_exists hx ratTwoTA_mem_rationalsTA with ⟨x2, _, hx2⟩
  rcases ratMul_exists hy ratTwoTA_mem_rationalsTA with ⟨y2, _, hy2⟩
  have hxx := ratTwo_mul_as_add_local hx
    (ratMul_comm_rel hx ratTwoTA_mem_rationalsTA hx2)
  have hyy := ratTwo_mul_as_add_local hy
    (ratMul_comm_rel hy ratTwoTA_mem_rationalsTA hy2)
  have hx2s : RatLT x2 s := ratLT_add_left_local hx hy hx hxy hxx hs
  have hsy2 : RatLT s y2 := ratLT_add_right_local hx hy hy hxy hs hyy
  exact ⟨(TA_LEM_00020_clause9_scale_iff hx hmMem ratTwoTA_mem_rationalsTA
      ratZero_lt_two_local hx2 hmTwo).mpr hx2s,
    (TA_LEM_00020_clause9_scale_iff hmMem hy ratTwoTA_mem_rationalsTA
      ratZero_lt_two_local hmTwo hy2).mpr hsy2⟩

/-- Testigo relacional explícito (x+y)(1+1)⁻¹, sin elegir una función global. -/
theorem rational_midpoint_exists {x y : ZFSet}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA) (hxy : RatLT x y) :
    ∃ s t it m : ZFSet,
      RatAdd x y s ∧ RatAdd ratOne ratOne t ∧ RatInv t it ∧ RatMul s it m ∧
      m ∈ rationalsTA ∧ RatLT x m ∧ RatLT m y := by
  rcases ratAdd_exists hx hy with ⟨s, hsMem, hs⟩
  have hTwoNZ : ratTwoTA ∈ ratNonzeroTA :=
    mem_ratNonzeroTA_iff.mpr ⟨ratTwoTA_mem_rationalsTA, ratTwoTA_ne_zero⟩
  rcases exists_inverse_of_mem_ratNonzeroTA hTwoNZ with ⟨i2, hi2NZ, hi, _, _⟩
  have hi2Mem := (mem_ratNonzeroTA_iff.mp hi2NZ).1
  rcases ratMul_exists hsMem hi2Mem with ⟨m, hmMem, hm⟩
  exact ⟨s, ratTwoTA, i2, m, hs, ratOne_add_one_two_local, hi, hm, hmMem,
    rational_midpoint_between hx hy hxy hs hi hm⟩

/-- TA-THM-00034 especializado al cuerpo ordenado concreto rationalsTA. -/
theorem TA_THM_00034_rational_density {x y : ZFSet}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA) (hxy : RatLT x y) :
    ∃ m : ZFSet, m ∈ rationalsTA ∧ RatLT x m ∧ RatLT m y := by
  rcases rational_midpoint_exists hx hy hxy with
    ⟨_, _, _, m, _, _, _, _, hm, hxm, hmy⟩
  exact ⟨m, hm, hxm, hmy⟩

end TratadoAnalisis.Rationals.Density

