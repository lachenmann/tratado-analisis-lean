import TratadoAnalisis.Integers.Order

/-!
# TA-LEAN-0003 — C1a

Cancelación multiplicativa entera y dominio conjuntista de representantes
racionales. En este módulo todavía no se construyen la relación racional, sus
clases ni el cociente.
-/

namespace TratadoAnalisis.Rationals.IntegerPrep

open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Integers.Construction
open TratadoAnalisis.Integers.Operations
open TratadoAnalisis.Integers.Multiplication
open TratadoAnalisis.Integers.Algebra
open TratadoAnalisis.Integers.Domain

/-! ## TA-LEM-00009 — cancelación multiplicativa entera -/

/-- Predicado relacional mínimo para la diferencia `x - y`: primero se obtiene
el opuesto de `y` y después se suma a `x`. -/
def IntSubValue (x y d : ZFSet) : Prop :=
  ∃ ny : ZFSet,
    IntNeg y ny ∧
    IntAdd x ny d

theorem intSubValue_exists_unique
    {x y : ZFSet}
    (hx : x ∈ integersTA)
    (hy : y ∈ integersTA) :
    ∃ d : ZFSet,
      d ∈ integersTA ∧
      IntSubValue x y d ∧
      ∀ e : ZFSet, e ∈ integersTA → IntSubValue x y e → e = d := by
  rcases intNegGraph_isFunc.2 y hy with ⟨ny, hny, _hnyUnique⟩
  have hInput :
      ZFSet.pair x ny ∈
        cartesianProductFoundational integersTA integersTA :=
    mem_cartesianProductFoundational.mpr ⟨hx, hny.1⟩
  rcases intAddGraph_isFunc.2 (ZFSet.pair x ny) hInput with
    ⟨d, hd, _hdUnique⟩
  refine ⟨d, hd.1, ⟨ny, hny.2, hd.2⟩, ?_⟩
  intro e _he hSubE
  rcases hSubE with ⟨ney, hNegE, hAddE⟩
  have hney : ney = ny := IntNeg_unique hy hNegE hny.2
  subst ney
  exact IntAdd_unique hx hny.1 hAddE hd.2

theorem intSubValue_eq_zero_iff
    {x y : ZFSet}
    (hx : x ∈ integersTA)
    (hy : y ∈ integersTA) :
    IntSubValue x y intZero ↔ x = y := by
  constructor
  · rintro ⟨ny, hNeg, hAdd⟩
    rcases exists_natEncode_intClass_of_mem hx with ⟨A, B, rfl⟩
    rcases exists_natEncode_intClass_of_mem hy with ⟨C, D, rfl⟩
    have hnyEq := intNegGraph_natEncode_class_value_iff.mp hNeg
    rw [hnyEq] at hAdd
    have hzeroEq :=
      (intAddGraph_natEncode_classes_value_iff
        (A := A) (B := B) (C := D) (D := C)).mp hAdd
    have hCross :=
      (TA_PRO_00038_natEncode_class_eq_iff
        0 0 (A + D) (B + C)).mp (by
          simpa [intZero] using hzeroEq)
    apply (TA_PRO_00038_natEncode_class_eq_iff A B C D).mpr
    omega
  · intro hxy
    subst y
    rcases intNegGraph_isFunc.2 x hx with ⟨nx, hnx, _hnxUnique⟩
    have hInput :
        ZFSet.pair x nx ∈
          cartesianProductFoundational integersTA integersTA :=
      mem_cartesianProductFoundational.mpr ⟨hx, hnx.1⟩
    rcases intAddGraph_isFunc.2 (ZFSet.pair x nx) hInput with
      ⟨s, hs, _hsUnique⟩
    have hsZero : s = intZero := intAdd_neg_right hx hnx.2 hs.2
    refine ⟨nx, hnx.2, ?_⟩
    simpa [IntAdd, hsZero] using hs.2

theorem intMul_zero_right
    {x z : ZFSet}
    (hx : x ∈ integersTA)
    (hMul : IntMul x intZero z) :
    z = intZero := by
  rcases exists_natEncode_intClass_of_mem hx with ⟨A, B, rfl⟩
  have hz :=
    (intMulGraph_natEncode_classes_value_iff
      (A := A) (B := B) (C := 0) (D := 0)).mp (by
        simpa [IntMul, intZero] using hMul)
  simpa [intZero] using hz

/-- La distributividad muestra que el producto por una suma de opuestos tiene
como suma de productos el cero. -/
theorem intMul_neg_sum_zero
    {r y ny ry rny s : ZFSet}
    (hr : r ∈ integersTA)
    (hy : y ∈ integersTA)
    (hny : ny ∈ integersTA)
    (hNeg : IntNeg y ny)
    (hry : IntMul r y ry)
    (hrny : IntMul r ny rny)
    (hSum : IntAdd ry rny s) :
    s = intZero := by
  have hAddInput :
      ZFSet.pair y ny ∈
        cartesianProductFoundational integersTA integersTA :=
    mem_cartesianProductFoundational.mpr ⟨hy, hny⟩
  rcases intAddGraph_isFunc.2 (ZFSet.pair y ny) hAddInput with
    ⟨u, hu, _huUnique⟩
  have huZero : u = intZero := intAdd_neg_right hy hNeg hu.2
  have hMulInput :
      ZFSet.pair r u ∈
        cartesianProductFoundational integersTA integersTA :=
    mem_cartesianProductFoundational.mpr ⟨hr, hu.1⟩
  rcases intMulGraph_isFunc.2 (ZFSet.pair r u) hMulInput with
    ⟨ru, hru, _hruUnique⟩
  have hruZero : ru = intZero :=
    intMul_zero_right hr (by simpa [IntMul, huZero] using hru.2)
  have hDistrib : ru = s :=
    intMul_add_left hr hy hny hu.2 hru.2 hry hrny hSum
  exact hDistrib.symm.trans hruZero

theorem TA_LEM_00009_intMul_cancel_left
    {r x y z : ZFSet}
    (hr : r ∈ integersTA)
    (hx : x ∈ integersTA)
    (hy : y ∈ integersTA)
    (hr0 : r ≠ intZero)
    (hrx : IntMul r x z)
    (hry : IntMul r y z) :
    x = y := by
  rcases intSubValue_exists_unique hx hy with
    ⟨d, hd, hSub, _hSubUnique⟩
  rcases hSub with ⟨ny, hNeg, hAdd⟩
  have hny : ny ∈ integersTA :=
    funcFoundational_value_mem intNegGraph_isFunc hNeg
  have hMulDInput :
      ZFSet.pair r d ∈
        cartesianProductFoundational integersTA integersTA :=
    mem_cartesianProductFoundational.mpr ⟨hr, hd⟩
  rcases intMulGraph_isFunc.2 (ZFSet.pair r d) hMulDInput with
    ⟨rd, hrd, _hrdUnique⟩
  have hMulNyInput :
      ZFSet.pair r ny ∈
        cartesianProductFoundational integersTA integersTA :=
    mem_cartesianProductFoundational.mpr ⟨hr, hny⟩
  rcases intMulGraph_isFunc.2 (ZFSet.pair r ny) hMulNyInput with
    ⟨rny, hrny, _hrnyUnique⟩
  have hz : z ∈ integersTA :=
    funcFoundational_value_mem intMulGraph_isFunc hrx
  have hAddInput :
      ZFSet.pair z rny ∈
        cartesianProductFoundational integersTA integersTA :=
    mem_cartesianProductFoundational.mpr ⟨hz, hrny.1⟩
  rcases intAddGraph_isFunc.2 (ZFSet.pair z rny) hAddInput with
    ⟨s, hs, _hsUnique⟩
  have hsZero : s = intZero :=
    intMul_neg_sum_zero hr hy hny hNeg hry hrny.2 hs.2
  have hDistrib : rd = s :=
    intMul_add_left hr hx hny hAdd hrd.2 hrx hrny.2 hs.2
  have hrdZero : rd = intZero := hDistrib.trans hsZero
  have hMulZero : IntMul r d intZero := by
    simpa [IntMul, hrdZero] using hrd.2
  rcases TA_PRO_00047_no_zero_divisors hr hd hMulZero with hrZero | hdZero
  · exact False.elim (hr0 hrZero)
  · apply (intSubValue_eq_zero_iff hx hy).mp
    rw [hdZero] at hAdd
    exact ⟨ny, hNeg, hAdd⟩

/-! ## TA-NOT-00012 — enteros no nulos -/

def intNonzeroTA : ZFSet :=
  ZFSet.sep
    (fun z => z ≠ intZero)
    integersTA

theorem mem_intNonzeroTA_iff {z : ZFSet} :
    z ∈ intNonzeroTA ↔
    z ∈ integersTA ∧ z ≠ intZero := by
  exact ZFSet.mem_sep

theorem intNonzero_mul_closed
    {x y z : ZFSet}
    (hx : x ∈ intNonzeroTA)
    (hy : y ∈ intNonzeroTA)
    (hMul : IntMul x y z) :
    z ∈ intNonzeroTA := by
  rw [mem_intNonzeroTA_iff] at hx hy ⊢
  exact ⟨funcFoundational_value_mem intMulGraph_isFunc hMul,
    intMul_ne_zero_of_ne_zero hx.1 hy.1 hx.2 hy.2 hMul⟩

/-! ## TA-DEF-00049 — dominio de representantes racionales -/

def ratDomain : ZFSet :=
  cartesianProductFoundational integersTA intNonzeroTA

theorem mem_ratDomain_iff {p : ZFSet} :
    p ∈ ratDomain ↔
    ∃ a b : ZFSet,
      a ∈ integersTA ∧
      b ∈ intNonzeroTA ∧
      p = ZFSet.pair a b := by
  constructor
  · intro hp
    rcases mem_cartesianProductFoundational_iff.mp hp with
      ⟨a, ha, b, hb, hpPair⟩
    exact ⟨a, b, ha, hb, hpPair⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact mem_cartesianProductFoundational.mpr ⟨ha, hb⟩

end TratadoAnalisis.Rationals.IntegerPrep
