import TratadoAnalisis.Cauchy.CauchySequences

/-!
# TA-LEAN-0011 A6 — Convergencia implica Cauchy (§8.5)

Se reutiliza la mitad racional positiva y la estimación triangular de A4.
El módulo inducido es el triple de la composición mu(e / 2_Q), formado
por una relación total y unívoca. No se introduce elección ni em.
-/

namespace TratadoAnalisis.Cauchy.ConvergentIsCauchy

universe u

open TratadoAnalisis.Naturals.Foundational
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Foundations.FunctionSpace
open TratadoAnalisis.Foundations.RelationalFunctions
open TratadoAnalisis.Cauchy.RationalSequences
open TratadoAnalisis.Cauchy.RationalConvergence
open TratadoAnalisis.Cauchy.CauchySequences
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.Field
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.StrictOrder
open TratadoAnalisis.Rationals.Signs
open TratadoAnalisis.Rationals.Division
open TratadoAnalisis.Rationals.PositiveProducts
open TratadoAnalisis.Rationals.IrrationalitySqrtTwo
open TratadoAnalisis.Rationals.SqrtTwoSet
open TratadoAnalisis.Rationals.NoSupremumSqrtTwo

/-- Una cola alrededor de l con radio eta tiene diámetro menor que 2 eta. -/
theorem pairTail_of_convergenceTail {q l N eta e : ZFSet.{u}}
    (hq : q ∈ rationalSequences) (hl : l ∈ rationalsTA)
    (heta : eta ∈ rationalsTA) (hd : RatAdd eta eta e)
    (ht : TailProperty q N (fun x => WithinDistance x l eta)) :
    PairTailProperty q N (fun x y => WithinDistance x y e) := by
  intro m n hm hn hNm hNn x y hx hy
  have hxQ := sequenceValue_mem hq hx
  have hyQ := sequenceValue_mem hq hy
  exact withinDistance_triangle hxQ hl hyQ heta hd
    (ht m hm hNm x hx) (withinDistance_symm hyQ hl (ht n hn hNn y hy))

/-- TA-THM-00059, sin hipótesis de completitud ni de módulo. -/
theorem rationalConverges_isCauchy {q l : ZFSet.{u}}
    (h : RationalConverges q l) : RationalCauchy q := by
  refine ⟨h.1, ?_⟩
  intro e he hp
  obtain ⟨eta, heta, hetap, hd⟩ := positive_half he hp
  obtain ⟨N, hN, ht⟩ := h.2.2 eta heta hetap
  exact ⟨N, hN, pairTail_of_convergenceTail h.1 h.2.1 heta hd ht⟩

theorem TA_THM_00059_convergent_mem_cauchySequences {q l : ZFSet.{u}}
    (h : RationalConverges q l) : q ∈ cauchySequences :=
  TA_DEF_00111_mem_cauchySequences_iff.mpr (rationalConverges_isCauchy h)

theorem rationalConvergent_mem_cauchySequences {q : ZFSet.{u}}
    (h : RationalConvergent q) : q ∈ cauchySequences := by
  obtain ⟨l, hl⟩ := h
  exact TA_THM_00059_convergent_mem_cauchySequences hl

/-- La mitad de e, caracterizada por la división racional ya construida. -/
theorem halfPrecision_exists_unique {e : ZFSet.{u}} (he : e ∈ positiveRationals) :
    ∃! eta : ZFSet.{u}, eta ∈ positiveRationals ∧ RatDiv e ratTwoTA eta := by
  have he' := mem_positiveRationals_iff.mp he
  have htwo : (ratTwoTA : ZFSet.{u}) ∈ ratNonzeroTA :=
    mem_ratNonzeroTA_iff.mpr ⟨ratTwoTA_mem_rationalsTA, ratTwoTA_ne_zero⟩
  obtain ⟨eta, heta, hdiv⟩ := ratDiv_exists he'.1 htwo
  have hp := ratDiv_positive he'.1 ratTwoTA_mem_rationalsTA he'.2 ratZero_lt_two_local hdiv
  refine ⟨eta, ⟨mem_positiveRationals_iff.mpr ⟨heta, hp⟩, hdiv⟩, ?_⟩
  intro t ht
  exact RatDiv_unique he'.1 htwo ht.2 hdiv

theorem halfPrecision_double {e eta : ZFSet.{u}}
    (he : e ∈ positiveRationals) (heta : eta ∈ positiveRationals)
    (hdiv : RatDiv e ratTwoTA eta) : RatAdd eta eta e := by
  have heQ := (mem_positiveRationals_iff.mp he).1
  have hetaQ := (mem_positiveRationals_iff.mp heta).1
  have hm := ratDiv_mul_denominator heQ ratTwoTA_mem_rationalsTA ratZero_lt_two_local hdiv
  exact ratTwo_mul_as_add_local hetaQ (ratMul_comm_rel hetaQ ratTwoTA_mem_rationalsTA hm)

/-- Relación de composición mu(e/2_Q), con todos los dominios explícitos. -/
def HalfModulusValue (mu e N : ZFSet.{u}) : Prop :=
  ∃ eta : ZFSet.{u}, eta ∈ positiveRationals ∧ RatDiv e ratTwoTA eta ∧
    FunctionValue positiveRationals omegaTA mu eta N

theorem halfModulusValue_exists_unique {mu e : ZFSet.{u}}
    (hmu : mu ∈ functionSpace positiveRationals omegaTA) (he : e ∈ positiveRationals) :
    ∃! N : ZFSet.{u}, N ∈ omegaTA ∧ HalfModulusValue mu e N := by
  obtain ⟨eta, hhalf, hu⟩ := halfPrecision_exists_unique he
  obtain ⟨N, ⟨hN, hv⟩, _⟩ := functionValue_exists_unique hmu hhalf.1
  refine ⟨N, ⟨hN, eta, hhalf.1, hhalf.2, hv⟩, ?_⟩
  intro M hM
  obtain ⟨t, ht, hdiv, hw⟩ := hM.2
  have eq := hu t ⟨ht, hdiv⟩
  subst t
  exact functionValue_unique hmu hhalf.1 hw hv

/-- Constructor conjuntista del módulo inducido. -/
def cauchyModulusOfConvergence (mu : ZFSet.{u}) : ZFSet.{u} :=
  functionOfRelation positiveRationals omegaTA (HalfModulusValue mu)

theorem cauchyModulusOfConvergence_mem {mu : ZFSet.{u}}
    (hmu : mu ∈ functionSpace positiveRationals omegaTA) :
    cauchyModulusOfConvergence mu ∈ functionSpace positiveRationals omegaTA :=
  functionOfRelation_mem (fun _ he => halfModulusValue_exists_unique hmu he)

/-- Identidad de evaluación exacta del módulo inducido. -/
theorem cauchyModulusOfConvergence_value_iff {mu e eta N : ZFSet.{u}}
    (hmu : mu ∈ functionSpace positiveRationals omegaTA)
    (he : e ∈ positiveRationals) (heta : eta ∈ positiveRationals)
    (hdiv : RatDiv e ratTwoTA eta) :
    FunctionValue positiveRationals omegaTA (cauchyModulusOfConvergence mu) e N ↔
      FunctionValue positiveRationals omegaTA mu eta N := by
  change FunctionValue positiveRationals omegaTA
    (functionOfRelation positiveRationals omegaTA (HalfModulusValue mu)) e N ↔
      FunctionValue positiveRationals omegaTA mu eta N
  rw [functionOfRelation_value_iff]
  constructor
  · rintro ⟨_, _, t, ht, hd, hv⟩
    have htwo : (ratTwoTA : ZFSet.{u}) ∈ ratNonzeroTA :=
      mem_ratNonzeroTA_iff.mpr ⟨ratTwoTA_mem_rationalsTA, ratTwoTA_ne_zero⟩
    have eq := RatDiv_unique (mem_positiveRationals_iff.mp he).1 htwo hd hdiv
    subst t
    exact hv
  · intro hv
    exact ⟨he, functionValue_mem hmu hv, eta, heta, hdiv, hv⟩

/-- Contenido del módulo en TA-THM-00059: mu_C(e)=mu(e/2_Q).
    Es un objeto conjuntista y su evaluación, no un decisor de Cauchy. -/
theorem TA_THM_00059_induced_cauchy_modulus {q l mu : ZFSet.{u}}
    (h : IsConvergenceModulus q l mu) :
    IsCauchyModulus q (cauchyModulusOfConvergence mu) := by
  refine ⟨h.1, cauchyModulusOfConvergence_mem h.2.2.1, ?_⟩
  intro e N he hv
  obtain ⟨eta, hhalf, _⟩ := halfPrecision_exists_unique he
  have hval := (cauchyModulusOfConvergence_value_iff h.2.2.1 he hhalf.1 hhalf.2).mp hv
  have ht := h.2.2.2 eta N hhalf.1 hval
  exact pairTail_of_convergenceTail h.1 h.2.1 (mem_positiveRationals_iff.mp hhalf.1).1
    (halfPrecision_double he hhalf.1 hhalf.2) ht

end TratadoAnalisis.Cauchy.ConvergentIsCauchy
