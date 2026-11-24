import TratadoAnalisis.Dedekind.Definition
import TratadoAnalisis.Rationals.Density
import TratadoAnalisis.Dedekind.AlphaTwoPrep

namespace TratadoAnalisis.Dedekind.AlphaTwo

universe u

open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.StrictOrder
open TratadoAnalisis.Rationals.IrrationalitySqrtTwo
open TratadoAnalisis.Rationals.SqrtTwoSet
open TratadoAnalisis.Rationals.SquareMonotonicity
open TratadoAnalisis.Rationals.NoSupremumSqrtTwo
open TratadoAnalisis.Rationals.Trichotomy
open TratadoAnalisis.Rationals.Density
open TratadoAnalisis.Dedekind.Definition

theorem ratLT_asymm_cut {x y : ZFSet}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (hxy : RatLT x y) (hyx : RatLT y x) : False :=
  hxy.2 (ratLE_antisymm hx hy hxy.1 hyx.1)

theorem alphaTwoCut_mem_of_negative {q : ZFSet}
    (hq : q ∈ rationalsTA) (hneg : RatLT q ratZero) : q ∈ alphaTwoCut :=
  TA_DEF_00082_mem_alphaTwoCut_iff.mpr ⟨hq, Or.inl hneg⟩

theorem alphaTwoCut_zero_mem : (ratZero : ZFSet.{u}) ∈ alphaTwoCut := by
  apply TA_DEF_00082_mem_alphaTwoCut_iff.mpr
  exact ⟨ratZero_mem_rationalsTA, Or.inr
    (TA_DEF_00066_mem_sqrtTwoSet_iff.mpr
      ⟨ratZero_mem_rationalsTA, ratLE_refl ratZero_mem_rationalsTA,
       ratZero, ratMul_zero_left ratZero_mem_rationalsTA, ratZero_lt_two_local⟩)⟩

theorem alphaTwoCut_one_mem : (ratOne : ZFSet.{u}) ∈ alphaTwoCut :=
  TA_DEF_00082_mem_alphaTwoCut_iff.mpr
    ⟨ratOne_mem_rationalsTA, Or.inr TA_PRO_00067_sqrtTwoSet_nonempty_bounded.{u, u, u}.1⟩

/-- Interfaz local reutilizable: un positivo cuyo cuadrado supera 2 es exterior. -/
theorem alphaTwoCut_not_mem_of_square_above {q qq : ZFSet}
    (hq : q ∈ rationalsTA) (h0q : RatLT ratZero q)
    (hqq : RatMul q q qq) (hTwoQQ : RatLT ratTwoTA qq) : q ∉ alphaTwoCut := by
  intro h
  rcases (TA_DEF_00082_mem_alphaTwoCut_iff.mp h).2 with hneg | hset
  · exact ratLT_asymm_cut hq ratZero_mem_rationalsTA hneg h0q
  · rcases TA_DEF_00066_mem_sqrtTwoSet_iff.mp hset with ⟨_, _, v, hv, hvTwo⟩
    have he : v = qq := RatMul_unique hq hq hv hqq
    rw [he] at hvTwo
    exact ratLT_asymm_cut
      (funcFoundational_value_mem ratMulGraph_isFunc hqq)
      ratTwoTA_mem_rationalsTA hvTwo hTwoQQ

theorem alphaTwoCut_two_not_mem : (ratTwoTA : ZFSet.{u}) ∉ alphaTwoCut := by
  rcases ratMul_exists ratTwoTA_mem_rationalsTA ratTwoTA_mem_rationalsTA with
    ⟨tt, _, htt⟩
  have hTwoTT : RatLT ratTwoTA tt :=
    ratLT_mul_positive_right ratOne_mem_rationalsTA ratTwoTA_mem_rationalsTA
      ratTwoTA_mem_rationalsTA ratOne_lt_two_local ratZero_lt_two_local
      ratOne_mul_two_local htt
  exact alphaTwoCut_not_mem_of_square_above ratTwoTA_mem_rationalsTA
    ratZero_lt_two_local htt hTwoTT

theorem alphaTwoCut_lower_closed {q r : ZFSet}
    (hq : q ∈ alphaTwoCut) (hr : r ∈ rationalsTA) (hrq : RatLT r q) :
    r ∈ alphaTwoCut := by
  rcases TA_DEF_00082_mem_alphaTwoCut_iff.mp hq with ⟨hqQ, hneg | hset⟩
  · exact alphaTwoCut_mem_of_negative hr
      (ratLT_of_lt_of_le_local hr hqQ ratZero_mem_rationalsTA hrq hneg.1)
  · rcases TA_DEF_00066_mem_sqrtTwoSet_iff.mp hset with ⟨_, _, qq, hqq, hqqTwo⟩
    rcases TA_PRO_00172_rational_trichotomy hr ratZero_mem_rationalsTA with
      hr0 | he | h0r
    · exact alphaTwoCut_mem_of_negative hr hr0
    · rw [he]
      exact alphaTwoCut_zero_mem
    · rcases ratMul_exists hr hr with ⟨rr, hrrQ, hrr⟩
      have hrrqq := TA_LEM_00018_square_strict_mono_nonnegative hr hqQ h0r.1 hrq hrr hqq
      have hrrTwo := ratLT_of_lt_of_le_local hrrQ
        (funcFoundational_value_mem ratMulGraph_isFunc hqq)
        ratTwoTA_mem_rationalsTA hrrqq hqqTwo.1
      exact TA_DEF_00082_mem_alphaTwoCut_iff.mpr ⟨hr, Or.inr
        (TA_DEF_00066_mem_sqrtTwoSet_iff.mpr ⟨hr, h0r.1, rr, hrr, hrrTwo⟩)⟩

/-- Negativo por densidad, cero con 1, positivo por perturbación local.
El auxiliar positivo usa denominador 2(q+1), distinto del manuscrito. -/
theorem alphaTwoCut_no_maximum {q : ZFSet} (hq : q ∈ alphaTwoCut) :
    ∃ r : ZFSet, r ∈ alphaTwoCut ∧ RatLT q r := by
  rcases TA_DEF_00082_mem_alphaTwoCut_iff.mp hq with ⟨hqQ, hcases⟩
  rcases TA_PRO_00172_rational_trichotomy hqQ ratZero_mem_rationalsTA with
    hq0 | he | h0q
  · rcases TA_THM_00034_rational_density hqQ ratZero_mem_rationalsTA hq0 with
      ⟨r, hr, hqr, hr0⟩
    exact ⟨r, alphaTwoCut_mem_of_negative hr hr0, hqr⟩
  · rw [he]
    exact ⟨ratOne, alphaTwoCut_one_mem, ratZero_lt_one⟩
  · rcases hcases with hneg | hset
    · exact (ratLT_asymm_cut hqQ ratZero_mem_rationalsTA hneg h0q).elim
    · rcases TA_DEF_00066_mem_sqrtTwoSet_iff.mp hset with ⟨_, _, qq, hqq, hqqTwo⟩
      rcases square_lt_two_gives_larger_member_local hqQ h0q hqq hqqTwo with
        ⟨r, hrSet, hqr⟩
      exact ⟨r, TA_DEF_00082_mem_alphaTwoCut_iff.mpr
        ⟨(TA_DEF_00066_mem_sqrtTwoSet_iff.mp hrSet).1, Or.inr hrSet⟩, hqr⟩

theorem alphaTwoCut_isDedekindCut : IsDedekindCut (alphaTwoCut : ZFSet.{u}) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    exact (TA_DEF_00082_mem_alphaTwoCut_iff.mp hq).1
  · intro he
    have hz := alphaTwoCut_zero_mem.{u}
    rw [he] at hz
    exact ZFSet.notMem_empty ratZero hz
  · intro he
    apply alphaTwoCut_two_not_mem
    rw [he]
    exact ratTwoTA_mem_rationalsTA
  · intro q hq r hr hrq
    exact alphaTwoCut_lower_closed hq hr hrq
  · intro q hq
    exact alphaTwoCut_no_maximum hq

/-- TA-PRO-00081, sin teoría de supremos ni hipótesis de lógica clásica. -/
theorem TA_PRO_00081_alphaTwoCut_mem : (alphaTwoCut : ZFSet.{u}) ∈ dedekindCutsTA :=
  TA_PRO_00079_mem_dedekindCuts_iff.mpr alphaTwoCut_isDedekindCut

/-- El testigo 0 distingue la cortadura cuando a≤0. -/
theorem alphaTwoCut_ne_section_of_nonpositive {a : ZFSet}
    (ha : a ∈ rationalsTA) (ha0 : RatLE a ratZero) :
    alphaTwoCut ≠ rationalSection a := by
  intro he
  have hz : ratZero ∈ rationalSection a := by
    rw [← he]
    exact alphaTwoCut_zero_mem
  have h0a := (TA_DEF_00081_mem_rationalSection_iff.mp hz).2
  exact h0a.2 (ratLE_antisymm ratZero_mem_rationalsTA ha h0a.1 ha0)

/-- TA-PRO-00082: separación local de toda sección racional, sin supremos. -/
theorem TA_PRO_00082_alphaTwoCut_ne_rationalSection {a : ZFSet}
    (ha : a ∈ rationalsTA) : alphaTwoCut ≠ rationalSection a := by
  rcases TA_PRO_00172_rational_trichotomy ha ratZero_mem_rationalsTA with
    ha0 | he0 | h0a
  · exact alphaTwoCut_ne_section_of_nonpositive ha ha0.1
  · rw [he0]
    exact alphaTwoCut_ne_section_of_nonpositive ratZero_mem_rationalsTA
      (ratLE_refl ratZero_mem_rationalsTA)
  · rcases ratMul_exists ha ha with ⟨aa, haaQ, haa⟩
    rcases TA_PRO_00172_rational_trichotomy haaQ ratTwoTA_mem_rationalsTA with
      haaTwo | heTwo | hTwoAA
    · intro he
      have haCut : a ∈ alphaTwoCut :=
        TA_DEF_00082_mem_alphaTwoCut_iff.mpr ⟨ha, Or.inr
          (TA_DEF_00066_mem_sqrtTwoSet_iff.mpr ⟨ha, h0a.1, aa, haa, haaTwo⟩)⟩
      have haSection : a ∈ rationalSection a := by
        rw [← he]
        exact haCut
      exact (TA_DEF_00081_mem_rationalSection_iff.mp haSection).2.2 rfl
    · exact (TA_THM_00032_no_rational_square_two ⟨a, aa, ha, haa, heTwo⟩).elim
    · rcases TratadoAnalisis.Dedekind.AlphaTwoPrep.positive_square_two_separator
        ha h0a haa hTwoAA with ⟨b, hbQ, h0b, hba, bb, hbb, hTwoBB⟩
      intro he
      have hbSection : b ∈ rationalSection a :=
        TA_DEF_00081_mem_rationalSection_iff.mpr ⟨hbQ, hba⟩
      rw [← he] at hbSection
      exact alphaTwoCut_not_mem_of_square_above hbQ h0b hbb hTwoBB hbSection

end TratadoAnalisis.Dedekind.AlphaTwo

