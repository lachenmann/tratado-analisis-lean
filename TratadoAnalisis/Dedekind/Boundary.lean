import TratadoAnalisis.Dedekind.Addition
import TratadoAnalisis.Rationals.Archimedean

namespace TratadoAnalisis.Dedekind.Boundary
universe u
open TratadoAnalisis.Naturals.Foundational
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Rationals.IntegerPrep
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.Field
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.StrictOrder
open TratadoAnalisis.Rationals.Signs
open TratadoAnalisis.Rationals.Division
open TratadoAnalisis.Rationals.NatEmbedding
open TratadoAnalisis.Rationals.Archimedean
open TratadoAnalisis.Rationals.NoSupremumSqrtTwo
open TratadoAnalisis.Dedekind.Definition
open TratadoAnalisis.Dedekind.Order
open TratadoAnalisis.Dedekind.Addition

theorem mul_one_left_rel {h : ZFSet.{u}} (hh : h ∈ rationalsTA) :
    RatMul ratOne h h := by
  rcases ratMul_exists ratOne_mem_rationalsTA hh with ⟨r, _, hr⟩
  rw [ratMul_one_left hh hr] at hr
  exact hr

/-- Núcleo inductivo constructivo sobre omegaTA, sin em. -/
theorem translated_natural_multiple_mem {α a0 h : ZFSet.{u}}
    (ha0 : a0 ∈ α) (ha0Q : a0 ∈ rationalsTA) (hh : h ∈ rationalsTA)
    (hclosed : ∀ a : ZFSet.{u}, a ∈ α →
      ∀ ah : ZFSet.{u}, RatAdd a h ah → ah ∈ α) :
    ∀ n : ZFSet.{u}, n ∈ omegaTA →
      ∃ nh a : ZFSet.{u}, RatMul (natRational n) h nh ∧
        RatAdd a0 nh a ∧ a ∈ α := by
  let P : ZFSet.{u} → Prop := fun n =>
    ∃ nh a : ZFSet.{u}, RatMul (natRational n) h nh ∧
      RatAdd a0 nh a ∧ a ∈ α
  have hz : P ∅ := by
    refine ⟨ratZero, a0, ?_, add_zero_right_rel ha0Q, ha0⟩
    rw [TA_COR_00008_natRational_zero]
    exact ratMul_zero_left hh
  have hs : ∀ n : ZFSet.{u}, n ∈ omegaTA → P n → P (succ n) := by
    intro n hn hp
    rcases hp with ⟨nh, a, hnh, ha, haα⟩
    have hnhQ := funcFoundational_value_mem ratMulGraph_isFunc hnh
    have haQ := funcFoundational_value_mem ratAddGraph_isFunc ha
    rcases ratAdd_exists haQ hh with ⟨ah, _, hah⟩
    rcases ratMul_exists (natRational_mem (TA_PRO_00022_succ_closed hn)) hh with
      ⟨nsh, hnshQ, hnsh⟩
    rcases ratAdd_exists hnhQ hh with ⟨v, _, hv⟩
    have hdist : nsh = v := ratAdd_mul_right (natRational_mem hn)
      ratOne_mem_rationalsTA hh (TA_COR_00008_natRational_succ hn)
      hnsh hnh (mul_one_left_rel hh) hv
    rw [← hdist] at hv
    rcases ratAdd_exists ha0Q hnshQ with ⟨b, _, hb⟩
    have he : ah = b := ratAdd_assoc ha0Q hnhQ hh ha hah hv hb
    rw [← he] at hb
    exact ⟨nsh, ah, hnsh, hb, hclosed a haα ah hah⟩
  exact TA_THM_00008_induction P hz hs

/-- TA-LEM-00022: habitabilidad, inducción fundacional, cota arquimediana
del cociente (u-a0)/h, y extracción final con em explícita. -/
theorem TA_LEM_00022_boundary_approximation (em : ∀ p : Prop, p ∨ ¬p)
    {α h : ZFSet.{u}} (hα : α ∈ dedekindCutsTA)
    (hh : h ∈ rationalsTA) (hpos : RatLT ratZero h) :
    ∃ a : ZFSet.{u}, a ∈ α ∧
      ∃ ah : ZFSet.{u}, RatAdd a h ah ∧ ah ∉ α := by
  have ca := TA_PRO_00079_mem_dedekindCuts_iff.mp hα
  rcases em (∃ a : ZFSet.{u}, a ∈ α ∧
    ∃ ah : ZFSet.{u}, RatAdd a h ah ∧ ah ∉ α) with hw | hno
  · exact hw
  · apply False.elim
    have hclosed : ∀ a : ZFSet.{u}, a ∈ α →
        ∀ ah : ZFSet.{u}, RatAdd a h ah → ah ∈ α := by
      intro a ha ah hah
      rcases em (ah ∈ α) with hi | ho
      · exact hi
      · exact (hno ⟨a, ha, ah, hah, ho⟩).elim
    rcases cut_inhabited em ca with ⟨a0, ha0⟩
    rcases cut_exterior_inhabited em ca with ⟨u0, hu0, huOut⟩
    rcases ratSub_exists hu0 (ca.1 ha0) with ⟨d, hd, hsub⟩
    have hhNZ : h ∈ ratNonzeroTA :=
      mem_ratNonzeroTA_iff.mpr ⟨hh, fun he => hpos.2 he.symm⟩
    rcases ratDiv_exists hd hhNZ with ⟨q, hq, hdiv⟩
    rcases hdiv with ⟨ih, hih, hdih⟩
    have hqh : RatMul q h d :=
      ratQuotient_mul_denominator_local hd hh hpos hih hdih
    rcases TA_THM_00031_rational_archimedean hq with ⟨n, hn, hqn⟩
    rcases translated_natural_multiple_mem ha0 (ca.1 ha0) hh hclosed n hn with
      ⟨nh, a, hnh, ha, haα⟩
    have hnhQ := funcFoundational_value_mem ratMulGraph_isFunc hnh
    have hdnh := (TA_LEM_00020_clause9_scale_iff hq (natRational_mem hn)
      hh hpos hqh hnh).mp hqn
    have hda0 : RatAdd d a0 u0 := ratSub_add_cancel hu0 (ca.1 ha0) hsub
    have ha0d := ratAdd_comm_rel hd (ca.1 ha0) hda0
    have hua := ratLT_add_left_local hd hnhQ (ca.1 ha0) hdnh ha0d ha
    exact huOut (ca.2.2.2.1 a haα u0 hu0 hua)

end TratadoAnalisis.Dedekind.Boundary
