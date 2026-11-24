import TratadoAnalisis.Dedekind.Inverse

namespace TratadoAnalisis.Dedekind.Division
universe u
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.Field
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.OrderedFieldCompatibility
open TratadoAnalisis.Rationals.StrictOrder
open TratadoAnalisis.Rationals.NoSupremumSqrtTwo
open TratadoAnalisis.Rationals.Signs
open TratadoAnalisis.Rationals.Division
open TratadoAnalisis.Rationals.PositiveProducts
open TratadoAnalisis.Rationals.Trichotomy
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.SquareMonotonicity
open TratadoAnalisis.Rationals.InverseOrder
open TratadoAnalisis.Rationals.DifferenceOrder
open TratadoAnalisis.Rationals.PositiveBounds
open TratadoAnalisis.Dedekind.Definition
open TratadoAnalisis.Dedekind.Order
open TratadoAnalisis.Dedekind.RationalSection
open TratadoAnalisis.Dedekind.Addition
open TratadoAnalisis.Dedekind.Negation
open TratadoAnalisis.Dedekind.AdditiveGroup
open TratadoAnalisis.Dedekind.Positivity
open TratadoAnalisis.Dedekind.PositiveMultiplication
open TratadoAnalisis.Dedekind.Signs
open TratadoAnalisis.Dedekind.Multiplication
open TratadoAnalisis.Dedekind.Unit
open TratadoAnalisis.Foundations.FunctionTriple

open TratadoAnalisis.Dedekind.Nonzero
open TratadoAnalisis.Dedekind.Inverse

/-- TA-DEF-00251: composición; los enunciados restringen el denominador al dominio. -/
def dedDiv (α β : ZFSet.{u}) : ZFSet.{u} := dedMul α (dedInvValue β)

theorem TA_DEF_00251_dedDiv_eq {α β : ZFSet.{u}} :
    dedDiv α β = dedMul α (dedInvValue β) := rfl

theorem dedDiv_mem (em : ∀ p : Prop, p ∨ ¬p)
    {α β : ZFSet.{u}} (hα : α ∈ dedekindCutsTA) (hβ : β ∈ nonzeroCutsTA) :
    dedDiv α β ∈ dedekindCutsTA :=
  TA_PRO_00094_dedSignedMul_mem em hα
    (TA_DEF_00101_mem_nonzeroCuts_iff.mp (TA_PRO_00100_signedInv_mem em hβ)).1

def dedDivGraph : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ α β γ : ZFSet.{u},
    z = ZFSet.pair (ZFSet.pair α β) γ ∧ γ = dedDiv α β)
    (cartesianProductFoundational
      (cartesianProductFoundational dedekindCutsTA nonzeroCutsTA) dedekindCutsTA)

theorem mem_dedDivGraph_iff {α β γ : ZFSet.{u}} :
    ZFSet.pair (ZFSet.pair α β) γ ∈ dedDivGraph ↔
      α ∈ dedekindCutsTA ∧ β ∈ nonzeroCutsTA ∧
      γ ∈ dedekindCutsTA ∧ γ = dedDiv α β := by
  constructor
  · intro h
    rcases ZFSet.mem_sep.mp h with ⟨hp, a, b, c, he, hc⟩
    have hcoords := ZFSet.pair_injective he
    rcases ZFSet.pair_injective hcoords.1 with ⟨rfl, rfl⟩
    rcases hcoords.2 with rfl
    rcases mem_cartesianProductFoundational.mp hp with ⟨hab, hcD⟩
    exact ⟨(mem_cartesianProductFoundational.mp hab).1,
      (mem_cartesianProductFoundational.mp hab).2, hcD, hc⟩
  · rintro ⟨ha, hb, hc, he⟩
    exact ZFSet.mem_sep.mpr
      ⟨mem_cartesianProductFoundational.mpr
        ⟨mem_cartesianProductFoundational.mpr ⟨ha, hb⟩, hc⟩, α, β, γ, rfl, he⟩

theorem TA_DEF_00251_dedDivGraph_isFunc (em : ∀ p : Prop, p ∨ ¬p) :
    IsFuncFoundational
      (cartesianProductFoundational (dedekindCutsTA : ZFSet.{u}) nonzeroCutsTA)
      dedekindCutsTA dedDivGraph := by
  constructor
  · intro z hz
    rcases (ZFSet.mem_sep.mp hz).2 with ⟨a, b, c, he, _⟩
    rw [he] at hz
    have h := mem_dedDivGraph_iff.mp hz
    exact ⟨ZFSet.pair a b, mem_cartesianProductFoundational.mpr ⟨h.1, h.2.1⟩,
      c, h.2.2.1, he⟩
  · intro z hz
    rcases (ZFSet.mem_sep.mp hz).2 with ⟨a, ha, b, hb, he⟩
    subst z
    have hc := dedDiv_mem em ha hb
    refine ⟨dedDiv a b, ⟨hc, mem_dedDivGraph_iff.mpr ⟨ha, hb, hc, rfl⟩⟩, ?_⟩
    intro c hc'
    exact (mem_dedDivGraph_iff.mp hc'.2).2.2.2

def dedDivFunction : ZFSet.{u} :=
  functionTriple (cartesianProductFoundational dedekindCutsTA nonzeroCutsTA)
    dedekindCutsTA dedDivGraph

theorem TA_DEF_00251_dedDivFunction_isTriple (em : ∀ p : Prop, p ∨ ¬p) :
    IsFunctionTriple
      (cartesianProductFoundational (dedekindCutsTA : ZFSet.{u}) nonzeroCutsTA)
      dedekindCutsTA dedDivFunction :=
  TA_DEF_00018_functionTriple_iff.mpr (TA_DEF_00251_dedDivGraph_isFunc em)



end TratadoAnalisis.Dedekind.Division
