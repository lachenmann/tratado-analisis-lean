import TratadoAnalisis.Rationals.IrrationalitySqrtTwo

namespace TratadoAnalisis.Rationals.SqrtTwoSet

universe u

open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Naturals.ArithmeticBridge
open TratadoAnalisis.Integers.Construction
open TratadoAnalisis.Integers.Multiplication
open TratadoAnalisis.Integers.Algebra
open TratadoAnalisis.Integers.Domain
open TratadoAnalisis.Integers.Order
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.OrderPrep
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.OrderedFieldCompatibility
open TratadoAnalisis.Rationals.StrictOrder
open TratadoAnalisis.Rationals.IrrationalitySqrtTwo

/-!
# E2b — el conjunto racional asociado a q² < 2

Certificación Lean de TA-DEF-00066 y TA-PRO-00067.

El cuadrado permanece expresado mediante la relación `RatMul`: no se
introduce una operación funcional global.
-/

/--
TA-DEF-00066 — subconjunto de los racionales no negativos cuyo cuadrado
relacional es estrictamente menor que `2_Q`.
-/
def sqrtTwoSet : ZFSet :=
  ZFSet.sep
    (fun q =>
      RatLE ratZero q ∧
      ∃ qq : ZFSet, RatMul q q qq ∧ RatLT qq ratTwoTA)
    rationalsTA

/-- Especificación literal de TA-DEF-00066. -/
theorem TA_DEF_00066_mem_sqrtTwoSet_iff {q : ZFSet} :
    q ∈ sqrtTwoSet ↔
      q ∈ rationalsTA ∧
      RatLE ratZero q ∧
      ∃ qq : ZFSet, RatMul q q qq ∧ RatLT qq ratTwoTA := by
  exact ZFSet.mem_sep

/-! ## Infraestructura técnica local para los numerales 1 y 2 -/

/-- `1_Q < 2_Q`, transportado por los embeddings canónicos. -/
theorem ratOne_lt_two_local :
    RatLT (ratOne : ZFSet.{u}) (ratTwoTA : ZFSet.{u}) := by
  have hIntLE :
      IntLE (intOne : ZFSet.{u}) (intTwoTA : ZFSet.{u}) := by
    simpa [intOne, intTwoTA, intPositiveForm] using
      (intEmbed_order_nat_iff.{u} 1 2).mp (by decide)
  have hRatLE : RatLE ratOne ratTwoTA :=
    (TA_PRO_00066_ratEmbed_order_iff
      intOne_mem_integersTA intTwoTA_mem_integersTA
      ratEmbedGraph_one intTwoTA_ratEmbed).mp hIntLE
  refine ⟨hRatLE, ?_⟩
  intro hEq
  have hTwoAtOne : ZFSet.pair intTwoTA ratOne ∈ ratEmbedGraph := by
    rw [hEq]
    exact intTwoTA_ratEmbed
  have hIntEq : intOne = intTwoTA :=
    ratEmbedGraph_injective ratEmbedGraph_one hTwoAtOne
  have hForms : intPositiveForm 1 = intPositiveForm 2 := by
    simpa [intOne, intTwoTA, intPositiveForm] using hIntEq
  have hNatEq : (1 : Nat) = 2 :=
    (intPositiveForm_eq_iff 1 2).mp hForms
  exact (by decide : (1 : Nat) ≠ 2) hNatEq

/-- `0_Q < 2_Q`, por `0_Q < 1_Q < 2_Q`. -/
theorem ratZero_lt_two_local :
    RatLT (ratZero : ZFSet.{u}) (ratTwoTA : ZFSet.{u}) := by
  have hLE : RatLE ratZero ratTwoTA :=
    ratLE_trans
      ratZero_mem_rationalsTA ratOne_mem_rationalsTA
      ratTwoTA_mem_rationalsTA
      ratZero_lt_one.1 ratOne_lt_two_local.1
  exact ⟨hLE, fun h => ratTwoTA_ne_zero h.symm⟩

/-- La relación multiplicativa evalúa `1_Q * 1_Q` en `1_Q`. -/
theorem ratOne_square_local :
    RatMul (ratOne : ZFSet.{u}) ratOne ratOne := by
  rcases ratMul_exists ratOne_mem_rationalsTA ratOne_mem_rationalsTA with
    ⟨z, _hz, hz⟩
  have hzEq : z = ratOne :=
    ratMul_one_left ratOne_mem_rationalsTA hz
  simpa [hzEq] using hz

/-- La relación multiplicativa evalúa `1_Q * 2_Q` en `2_Q`. -/
theorem ratOne_mul_two_local :
    RatMul (ratOne : ZFSet.{u}) ratTwoTA ratTwoTA := by
  rcases ratMul_exists ratOne_mem_rationalsTA ratTwoTA_mem_rationalsTA with
    ⟨z, _hz, hz⟩
  have hzEq : z = ratTwoTA :=
    ratMul_one_left ratTwoTA_mem_rationalsTA hz
  simpa [hzEq] using hz

/-!
## TA-PRO-00067

`1_Q` pertenece a `sqrtTwoSet` y `2_Q` es una cota superior racional.
-/
theorem TA_PRO_00067_sqrtTwoSet_nonempty_bounded :
    ratOne ∈ sqrtTwoSet ∧
    (ratTwoTA ∈ rationalsTA ∧
      ∀ q : ZFSet, q ∈ sqrtTwoSet → RatLE q ratTwoTA) := by
  constructor
  · apply TA_DEF_00066_mem_sqrtTwoSet_iff.mpr
    exact ⟨ratOne_mem_rationalsTA, ratZero_lt_one.1,
      ratOne, ratOne_square_local, ratOne_lt_two_local⟩
  · refine ⟨ratTwoTA_mem_rationalsTA, ?_⟩
    intro q hq
    rcases TA_DEF_00066_mem_sqrtTwoSet_iff.mp hq with
      ⟨hqMem, h0q, qq, hqq, hqqLTTwo⟩
    rcases ratLE_total hqMem ratTwoTA_mem_rationalsTA with hqTwo | hTwoQ
    · exact hqTwo
    · exfalso

      -- Productos de la cadena 2² ≤ q·2 = 2·q ≤ q².
      rcases ratMul_exists
          ratTwoTA_mem_rationalsTA ratTwoTA_mem_rationalsTA with
        ⟨twoSq, hTwoSqMem, hTwoSq⟩
      rcases ratMul_exists hqMem ratTwoTA_mem_rationalsTA with
        ⟨qTwo, _hqTwoMem, hqTwoMul⟩
      rcases ratMul_exists ratTwoTA_mem_rationalsTA hqMem with
        ⟨twoQ, hTwoQMem, hTwoQMul⟩

      have hTwoSqLEQTwo : RatLE twoSq qTwo :=
        ratLE_mul_nonnegative_compat
          ratTwoTA_mem_rationalsTA hqMem ratTwoTA_mem_rationalsTA
          hTwoQ ratZero_lt_two_local.1
          hTwoSq hqTwoMul

      have hQTwoEqTwoQ : qTwo = twoQ :=
        ratMul_comm
          hqMem ratTwoTA_mem_rationalsTA
          hqTwoMul hTwoQMul

      have hTwoSqLETwoQ : RatLE twoSq twoQ := by
        rw [← hQTwoEqTwoQ]
        exact hTwoSqLEQTwo

      have hTwoQLEQQ : RatLE twoQ qq :=
        ratLE_mul_nonnegative_compat
          ratTwoTA_mem_rationalsTA hqMem hqMem
          hTwoQ h0q
          hTwoQMul hqq

      have hTwoSqLEQQ : RatLE twoSq qq :=
        ratLE_trans
          hTwoSqMem hTwoQMem
          (funcFoundational_value_mem ratMulGraph_isFunc hqq)
          hTwoSqLETwoQ hTwoQLEQQ

      -- 2 = 1·2 < 2·2 = 2².
      have hTwoLTTwoSq : RatLT ratTwoTA twoSq :=
        ratLT_mul_positive_right
          ratOne_mem_rationalsTA ratTwoTA_mem_rationalsTA
          ratTwoTA_mem_rationalsTA
          ratOne_lt_two_local ratZero_lt_two_local
          ratOne_mul_two_local hTwoSq

      have hTwoLEQQ : RatLE ratTwoTA qq :=
        ratLE_trans
          ratTwoTA_mem_rationalsTA hTwoSqMem
          (funcFoundational_value_mem ratMulGraph_isFunc hqq)
          hTwoLTTwoSq.1 hTwoSqLEQQ

      have hEq : qq = ratTwoTA :=
        ratLE_antisymm
          (funcFoundational_value_mem ratMulGraph_isFunc hqq)
          ratTwoTA_mem_rationalsTA
          hqqLTTwo.1 hTwoLEQQ
      exact hqqLTTwo.2 hEq

end TratadoAnalisis.Rationals.SqrtTwoSet
