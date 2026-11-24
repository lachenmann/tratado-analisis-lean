import TratadoAnalisis.Cauchy.RationalConvergence

/-!
# TA-LEAN-0011 A5 — Sucesiones racionales de Cauchy (§8.4)

La condición compara dos términos de una misma cola, sin límite externo.
Los objetos son triples conjuntistas de dominio omegaTA y codominio rationalsTA.
El conjunto de Cauchy se forma por Separación. El módulo mínimo se construye
separadamente con em explícito; no se afirma computabilidad.
-/

namespace TratadoAnalisis.Cauchy.CauchySequences

universe u

open TratadoAnalisis.Naturals.Foundational
open TratadoAnalisis.Integers.Order
open TratadoAnalisis.Foundations.FunctionSpace
open TratadoAnalisis.Foundations.RelationalFunctions
open TratadoAnalisis.Cauchy.RationalSequences
open TratadoAnalisis.Cauchy.SequenceOperations
open TratadoAnalisis.Cauchy.RationalConvergence
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.StrictOrder

/-- Propiedad de todos los pares de valores de una cola común. -/
def PairTailProperty (q N : ZFSet.{u})
    (P : ZFSet.{u} → ZFSet.{u} → Prop) : Prop :=
  ∀ m n : ZFSet.{u}, m ∈ omegaTA → n ∈ omegaTA →
    NatLETA N m → NatLETA N n →
    ∀ x y : ZFSet.{u}, SequenceValue q m x → SequenceValue q n y → P x y

theorem pairTailProperty_iff {q N : ZFSet.{u}}
    {P R : ZFSet.{u} → ZFSet.{u} → Prop}
    (hq : q ∈ rationalSequences)
    (h : ∀ x y : ZFSet.{u}, x ∈ rationalsTA → y ∈ rationalsTA → (P x y ↔ R x y)) :
    PairTailProperty q N P ↔ PairTailProperty q N R := by
  constructor
  · intro hp m n hm hn hNm hNn x y hx hy
    exact (h x y (sequenceValue_mem hq hx) (sequenceValue_mem hq hy)).mp
      (hp m n hm hn hNm hNn x y hx hy)
  · intro hr m n hm hn hNm hNn x y hx hy
    exact (h x y (sequenceValue_mem hq hx) (sequenceValue_mem hq hy)).mpr
      (hr m n hm hn hNm hNn x y hx hy)

def CauchyBy (R : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (q : ZFSet.{u}) : Prop :=
  q ∈ rationalSequences ∧
    ∀ e : ZFSet.{u}, e ∈ rationalsTA → RatLT ratZero e →
      ∃ N : ZFSet.{u}, N ∈ omegaTA ∧ PairTailProperty q N (fun x y => R x y e)

/-- TA-DEF-00110, condición de Cauchy sin referencia a un límite. -/
def RationalCauchy (q : ZFSet.{u}) : Prop :=
  CauchyBy WithinDistance q

theorem TA_DEF_00110_cauchy_iff {q : ZFSet.{u}} :
    RationalCauchy q ↔ q ∈ rationalSequences ∧
      ∀ e : ZFSet.{u}, e ∈ rationalsTA → RatLT ratZero e →
        ∃ N : ZFSet.{u}, N ∈ omegaTA ∧
          ∀ m n : ZFSet.{u}, m ∈ omegaTA → n ∈ omegaTA →
            NatLETA N m → NatLETA N n →
            ∀ x y : ZFSet.{u}, SequenceValue q m x → SequenceValue q n y →
              WithinDistance x y e := Iff.rfl

/-- TA-DEF-00111: conjunto C_Q por Separación. -/
def cauchySequences : ZFSet.{u} :=
  ZFSet.sep RationalCauchy rationalSequences

theorem TA_DEF_00111_mem_cauchySequences_iff {q : ZFSet.{u}} :
    q ∈ cauchySequences ↔ RationalCauchy q := by
  constructor
  · intro h
    exact (ZFSet.mem_sep.mp h).2
  · intro h
    exact ZFSet.mem_sep.mpr ⟨h.1, h⟩

theorem cauchySequences_subset : (cauchySequences : ZFSet.{u}) ⊆ rationalSequences := by
  intro q hq
  exact (TA_DEF_00111_mem_cauchySequences_iff.mp hq).1

theorem TA_DEF_00111_cauchySequences_exists_unique :
    ∃! S : ZFSet.{u}, ∀ q : ZFSet.{u}, q ∈ S ↔ RationalCauchy q := by
  refine ⟨cauchySequences, fun _ => TA_DEF_00111_mem_cauchySequences_iff, ?_⟩
  intro S hS
  apply ZFSet.ext
  intro q
  exact (hS q).trans TA_DEF_00111_mem_cauchySequences_iff.symm

def CauchyAbsolute (q : ZFSet.{u}) : Prop :=
  CauchyBy WithinAbsolute q

def CauchyWindow (q : ZFSet.{u}) : Prop :=
  CauchyBy WithinWindow q

theorem cauchyBy_iff {q : ZFSet.{u}}
    {R S : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop}
    (h : ∀ x y e : ZFSet.{u}, x ∈ rationalsTA → y ∈ rationalsTA →
      e ∈ rationalsTA → RatLT ratZero e → (R x y e ↔ S x y e)) :
    CauchyBy R q ↔ CauchyBy S q := by
  constructor
  · rintro ⟨hq, hc⟩
    refine ⟨hq, ?_⟩
    intro e he hp
    obtain ⟨N, hN, ht⟩ := hc e he hp
    exact ⟨N, hN, (pairTailProperty_iff hq (fun x y hx hy => h x y e hx hy he hp)).mp ht⟩
  · rintro ⟨hq, hc⟩
    refine ⟨hq, ?_⟩
    intro e he hp
    obtain ⟨N, hN, ht⟩ := hc e he hp
    exact ⟨N, hN, (pairTailProperty_iff hq (fun x y hx hy => h x y e hx hy he hp)).mpr ht⟩

/-- TA-PRO-00113: las equivalencias no cambian el índice N. -/
theorem TA_PRO_00113_cauchy_equivalences {q : ZFSet.{u}} :
    (RationalCauchy q ↔ CauchyAbsolute q) ∧
    (RationalCauchy q ↔ CauchyWindow q) :=
  ⟨cauchyBy_iff (fun _ _ _ _ _ _ _ => withinDistance_iff_absolute),
    cauchyBy_iff (fun _ _ _ hx hy he hp => withinDistance_iff_window hx hy he hp)⟩

/-- TA-PRO-00114: prueba directa de la condición para una constante, N=0. -/
theorem constant_is_cauchy {c : ZFSet.{u}} (hc : c ∈ rationalsTA) :
    RationalCauchy (constantSequence c) := by
  refine ⟨constantSequence_mem hc, ?_⟩
  intro e _he hp
  refine ⟨(∅ : ZFSet.{u}), omegaTA_isInductive.1, ?_⟩
  intro m n hm hn _ _ x y hx hy
  have ex := (constantSequence_value_iff hc hm).mp hx
  have ey := (constantSequence_value_iff hc hn).mp hy
  subst x
  subst y
  exact withinDistance_self hc hp

theorem TA_PRO_00114_constant_mem_cauchySequences {c : ZFSet.{u}}
    (hc : c ∈ rationalsTA) : constantSequence c ∈ cauchySequences :=
  TA_DEF_00111_mem_cauchySequences_iff.mpr (constant_is_cauchy hc)

theorem cauchySequences_inhabited :
    ∃ q : ZFSet.{u}, q ∈ cauchySequences :=
  ⟨constantSequence ratZero, TA_PRO_00114_constant_mem_cauchySequences ratZero_mem_rationalsTA⟩

theorem cauchySequences_ne_empty : (cauchySequences : ZFSet.{u}) ≠ ∅ := by
  intro h
  obtain ⟨q, hq⟩ := (cauchySequences_inhabited : ∃ q : ZFSet.{u}, q ∈ cauchySequences)
  rw [h] at hq
  exact ZFSet.notMem_empty q hq

/-- Módulo de Cauchy como triple de función Q_{>0} → N. -/
def IsCauchyModulus (q mu : ZFSet.{u}) : Prop :=
  q ∈ rationalSequences ∧ mu ∈ functionSpace positiveRationals omegaTA ∧
    ∀ e N : ZFSet.{u}, e ∈ positiveRationals →
      FunctionValue positiveRationals omegaTA mu e N →
      PairTailProperty q N (fun x y => WithinDistance x y e)

theorem cauchy_of_modulus {q mu : ZFSet.{u}} (h : IsCauchyModulus q mu) :
    RationalCauchy q := by
  refine ⟨h.1, ?_⟩
  intro e he hp
  have he' := mem_positiveRationals_iff.mpr ⟨he, hp⟩
  obtain ⟨N, ⟨hN, hv⟩, _⟩ := functionValue_exists_unique h.2.1 he'
  exact ⟨N, hN, h.2.2 e N he' hv⟩

/-- Minimalidad para una precisión fija, sin exigir decidibilidad de la cola. -/
def MinimalCauchyIndex (q e N : ZFSet.{u}) : Prop :=
  PairTailProperty q N (fun x y => WithinDistance x y e) ∧
    ∀ M : ZFSet.{u}, M ∈ omegaTA →
      PairTailProperty q M (fun x y => WithinDistance x y e) → NatLETA N M

theorem minimalCauchyIndex_exists_unique
    (em : ∀ p : Prop, p ∨ ¬p)
    {q e : ZFSet.{u}} (h : RationalCauchy q) (he : e ∈ positiveRationals) :
    ∃! N : ZFSet.{u}, N ∈ omegaTA ∧ MinimalCauchyIndex q e N := by
  have he' := mem_positiveRationals_iff.mp he
  obtain ⟨N, hN, ht, hmin⟩ := least_natural_index em
    (fun k => PairTailProperty q k (fun x y => WithinDistance x y e))
    (h.2 e he'.1 he'.2)
  refine ⟨N, ⟨hN, ht, hmin⟩, ?_⟩
  intro M hM
  exact natLE_antisymm_local hM.1 hN
    (hM.2.2 N hN ht) (hmin M hM.1 hM.2.1)

/-- Constructor por Separación: su totalización sólo usa em explícito. -/
def minimalCauchyModulus (q : ZFSet.{u}) : ZFSet.{u} :=
  functionOfRelation positiveRationals omegaTA (MinimalCauchyIndex q)

theorem minimalCauchyModulus_mem
    (em : ∀ p : Prop, p ∨ ¬p) {q : ZFSet.{u}} (h : RationalCauchy q) :
    minimalCauchyModulus q ∈ functionSpace positiveRationals omegaTA :=
  functionOfRelation_mem (fun _ he => minimalCauchyIndex_exists_unique em h he)

theorem minimalCauchyModulus_isModulus
    (em : ∀ p : Prop, p ∨ ¬p) {q : ZFSet.{u}} (h : RationalCauchy q) :
    IsCauchyModulus q (minimalCauchyModulus q) := by
  refine ⟨h.1, minimalCauchyModulus_mem em h, ?_⟩
  intro e N _he hv
  exact ((functionOfRelation_value_iff (R := MinimalCauchyIndex q)).mp hv).2.2.1

theorem minimalCauchyModulus_le {q mu e N M : ZFSet.{u}}
    (hmu : IsCauchyModulus q mu) (he : e ∈ positiveRationals)
    (hN : FunctionValue positiveRationals omegaTA (minimalCauchyModulus q) e N)
    (hM : FunctionValue positiveRationals omegaTA mu e M) : NatLETA N M :=
  ((functionOfRelation_value_iff (R := MinimalCauchyIndex q)).mp hN).2.2.2 M
    (functionValue_mem hmu.2.1 hM) (hmu.2.2 e M he hM)

theorem minimalCauchyModulus_exists_unique
    (em : ∀ p : Prop, p ∨ ¬p) {q : ZFSet.{u}} (h : RationalCauchy q) :
    ∃! mu : ZFSet.{u}, mu ∈ functionSpace positiveRationals omegaTA ∧
      ∀ e N : ZFSet.{u}, e ∈ positiveRationals →
        FunctionValue positiveRationals omegaTA mu e N → MinimalCauchyIndex q e N := by
  have hf := minimalCauchyModulus_mem em h
  refine ⟨minimalCauchyModulus q, ⟨hf, ?_⟩, ?_⟩
  · intro e N _he hN
    exact ((functionOfRelation_value_iff (R := MinimalCauchyIndex q)).mp hN).2.2
  · intro mu hmu
    apply (function_eq_iff_values hmu.1 hf).mpr
    intro e he M N hM hN
    have hm := hmu.2 e M he hM
    have hn := ((functionOfRelation_value_iff (R := MinimalCauchyIndex q)).mp hN).2.2
    have hmNat := functionValue_mem hmu.1 hM
    have hnNat := functionValue_mem hf hN
    exact natLE_antisymm_local hmNat hnNat
      (hm.2 N hnNat hn.1) (hn.2 M hmNat hm.1)

end TratadoAnalisis.Cauchy.CauchySequences
