import TratadoAnalisis.Rationals.Field

namespace TratadoAnalisis.Rationals.OrderPrep

open TratadoAnalisis.Naturals.Recursion
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

/-!
# TA-LEAN-0003 — D0

Prerrequisitos enteros para construir el orden racional:

* TA-LEM-00010 — invariancia por traslación;
* TA-LEM-00011 — escalamiento por un entero positivo;
* TA-LEM-00012 — producto de enteros positivos.

No se define todavía el orden racional.
-/

/-! ## Helpers existenciales locales -/

theorem intAdd_exists_local
    {x y : ZFSet}
    (hx : x ∈ integersTA)
    (hy : y ∈ integersTA) :
    ∃ z : ZFSet, z ∈ integersTA ∧ IntAdd x y z := by
  have hxy :
      ZFSet.pair x y ∈
        cartesianProductFoundational integersTA integersTA :=
    mem_cartesianProductFoundational.mpr ⟨hx, hy⟩
  rcases intAddGraph_isFunc.2 (ZFSet.pair x y) hxy with
    ⟨z, hz, _hUnique⟩
  exact ⟨z, hz.1, hz.2⟩

theorem intMul_exists_local
    {x y : ZFSet}
    (hx : x ∈ integersTA)
    (hy : y ∈ integersTA) :
    ∃ z : ZFSet, z ∈ integersTA ∧ IntMul x y z := by
  have hxy :
      ZFSet.pair x y ∈
        cartesianProductFoundational integersTA integersTA :=
    mem_cartesianProductFoundational.mpr ⟨hx, hy⟩
  rcases intMulGraph_isFunc.2 (ZFSet.pair x y) hxy with
    ⟨z, hz, _hUnique⟩
  exact ⟨z, hz.1, hz.2⟩

theorem intNeg_exists_local
    {x : ZFSet}
    (hx : x ∈ integersTA) :
    ∃ nx : ZFSet, nx ∈ integersTA ∧ IntNeg x nx := by
  rcases intNegGraph_isFunc.2 x hx with
    ⟨nx, hnx, _hUnique⟩
  exact ⟨nx, hnx.1, hnx.2⟩

/-! ## Orden estricto asociado -/

def IntLT (x y : ZFSet) : Prop :=
  IntLE x y ∧ x ≠ y

/-! ## TA-LEM-00010 — invariancia por traslación -/

theorem TA_LEM_00010_intLE_translation_iff
    {x y z xz yz : ZFSet}
    (hx : x ∈ integersTA)
    (hy : y ∈ integersTA)
    (hz : z ∈ integersTA)
    (hxz : IntAdd x z xz)
    (hyz : IntAdd y z yz) :
    IntLE x y ↔ IntLE xz yz := by
  constructor
  · intro hxy
    exact intLE_add_compat hx hy hz hxy hxz hyz

  · intro hxySum

    have hxzMem : xz ∈ integersTA :=
      funcFoundational_value_mem intAddGraph_isFunc hxz

    have hyzMem : yz ∈ integersTA :=
      funcFoundational_value_mem intAddGraph_isFunc hyz

    rcases intNeg_exists_local hz with
      ⟨nz, hnz, hNegZ⟩

    rcases intAdd_exists_local hz hnz with
      ⟨zz, hzz, hZNegZ⟩

    have hzzZero : zz = intZero :=
      intAdd_neg_right hz hNegZ hZNegZ

    rcases intAdd_exists_local hxzMem hnz with
      ⟨lhs, hlhs, hLhs⟩

    rcases intAdd_exists_local hyzMem hnz with
      ⟨rhs, hrhs, hRhs⟩

    have hLR : IntLE lhs rhs :=
      intLE_add_compat
        hxzMem hyzMem hnz
        hxySum hLhs hRhs

    rcases intAdd_exists_local hx hzz with
      ⟨xzz, hxzz, hXZZ⟩

    have hAssocX : lhs = xzz :=
      intAdd_assoc
        hx hz hnz
        hxz hLhs hZNegZ hXZZ

    have hxzzEq : xzz = x := by
      rw [hzzZero] at hXZZ
      exact intAdd_zero_right hx hXZZ

    have hlhsEq : lhs = x :=
      hAssocX.trans hxzzEq

    rcases intAdd_exists_local hy hzz with
      ⟨yzz, hyzz, hYZZ⟩

    have hAssocY : rhs = yzz :=
      intAdd_assoc
        hy hz hnz
        hyz hRhs hZNegZ hYZZ

    have hyzzEq : yzz = y := by
      rw [hzzZero] at hYZZ
      exact intAdd_zero_right hy hYZZ

    have hrhsEq : rhs = y :=
      hAssocY.trans hyzzEq

    rw [hlhsEq, hrhsEq] at hLR
    exact hLR

/-! ## TA-LEM-00011 — escalamiento por factor positivo -/

theorem TA_LEM_00011_intLE_mul_positive_iff
    {x y r xr yr : ZFSet}
    (hx : x ∈ integersTA)
    (hy : y ∈ integersTA)
    (hr : r ∈ integersTA)
    (hrPos : IntLT intZero r)
    (hxr : IntMul x r xr)
    (hyr : IntMul y r yr) :
    IntLE x y ↔ IntLE xr yr := by

  rcases hrPos with ⟨hrNonnegative, hrNe⟩

  have hr0 : r ≠ intZero := by
    intro h
    exact hrNe h.symm

  constructor

  · intro hxy
    exact intLE_mul_nonnegative_compat
      hx hy hr
      hxy hrNonnegative
      hxr hyr

  · intro hProducts

    have hxrMem : xr ∈ integersTA :=
      funcFoundational_value_mem intMulGraph_isFunc hxr

    have hyrMem : yr ∈ integersTA :=
      funcFoundational_value_mem intMulGraph_isFunc hyr

    rcases intLE_total hx hy with hxy | hyx

    · exact hxy

    · have hReverseProducts : IntLE yr xr :=
        intLE_mul_nonnegative_compat
          hy hx hr
          hyx hrNonnegative
          hyr hxr

      have hProductsEq : xr = yr :=
        intLE_antisymm
          hxrMem hyrMem
          hProducts hReverseProducts

      rcases intMul_exists_local hr hx with
        ⟨rx, _hrxMem, hrx⟩

      rcases intMul_exists_local hr hy with
        ⟨ry, _hryMem, hry⟩

      have hXrRx : xr = rx :=
        intMul_comm hx hr hxr hrx

      have hYrRy : yr = ry :=
        intMul_comm hy hr hyr hry

      have hRxRy : rx = ry :=
        hXrRx.symm.trans
          (hProductsEq.trans hYrRy)

      have hrx' : IntMul r x ry := by
        rw [← hRxRy]
        exact hrx

      have hxyEq : x = y :=
        TA_LEM_00009_intMul_cancel_left
          hr hx hy hr0
          hrx' hry

      rw [hxyEq]
      exact intLE_refl hy

/-! ## TA-LEM-00012 — producto de positivos -/

theorem TA_LEM_00012_positive_mul
    {x y xy : ZFSet}
    (hx : x ∈ integersTA)
    (hy : y ∈ integersTA)
    (hxPos : IntLT intZero x)
    (hyPos : IntLT intZero y)
    (hxy : IntMul x y xy) :
    IntLT intZero xy := by

  rcases hxPos with ⟨hxNonnegative, hxNe⟩
  rcases hyPos with ⟨hyNonnegative, hyNe⟩

  have hx0 : x ≠ intZero := by
    intro h
    exact hxNe h.symm

  have hy0 : y ≠ intZero := by
    intro h
    exact hyNe h.symm

  have hxyMem : xy ∈ integersTA :=
    funcFoundational_value_mem intMulGraph_isFunc hxy

  rcases intMul_exists_local intZero_mem_integersTA hy with
    ⟨zeroY, _hzeroYMem, hZeroY⟩

  have hZeroYLeXY : IntLE zeroY xy :=
    intLE_mul_nonnegative_compat
      intZero_mem_integersTA
      hx
      hy
      hxNonnegative
      hyNonnegative
      hZeroY
      hxy

  have hZeroYEq : zeroY = intZero :=
    intMul_zero_left hy hZeroY

  have hZeroLeXY : IntLE intZero xy := by
    rw [hZeroYEq] at hZeroYLeXY
    exact hZeroYLeXY

  have hxy0 : xy ≠ intZero :=
    intMul_ne_zero_of_ne_zero
      hx hy hx0 hy0 hxy

  exact ⟨hZeroLeXY, fun h => hxy0 h.symm⟩

end TratadoAnalisis.Rationals.OrderPrep