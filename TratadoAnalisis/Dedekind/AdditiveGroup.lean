import TratadoAnalisis.Dedekind.Negation

namespace TratadoAnalisis.Dedekind.AdditiveGroup
universe u
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.Signs
open TratadoAnalisis.Dedekind.Definition
open TratadoAnalisis.Dedekind.Addition
open TratadoAnalisis.Dedekind.Negation
open TratadoAnalisis.Foundations.FunctionTriple

theorem TA_COR_00020_dedAdd_neg_bilateral (em : ∀ p : Prop, p ∨ ¬p)
    {α : ZFSet.{u}} (hα : α ∈ dedekindCutsTA) :
    dedAdd α (dedNeg α) = dedZero ∧ dedAdd (dedNeg α) α = dedZero := by
  have h := TA_PRO_00088_dedAdd_neg em hα
  exact ⟨h, (dedAdd_comm_of_subsets (dedNeg_subset_rationals α)
    (TA_PRO_00079_mem_dedekindCuts_iff.mp hα).1).trans h⟩

/-- TA-THM-00043: las leyes sobre el portador concreto, no una instancia
de grupo de mathlib ni un cambio de representación. -/
theorem TA_THM_00043_additive_group_package (em : ∀ p : Prop, p ∨ ¬p) :
    (∀ α β : ZFSet.{u}, α ∈ dedekindCutsTA → β ∈ dedekindCutsTA →
      dedAdd α β ∈ dedekindCutsTA) ∧
    (dedZero : ZFSet.{u}) ∈ dedekindCutsTA ∧
    (∀ α : ZFSet.{u}, α ∈ dedekindCutsTA →
      dedNeg α ∈ dedekindCutsTA ∧
      dedAdd α (dedNeg α) = dedZero ∧ dedAdd (dedNeg α) α = dedZero) ∧
    (∀ α β γ : ZFSet.{u}, α ∈ dedekindCutsTA → β ∈ dedekindCutsTA →
      γ ∈ dedekindCutsTA →
      dedAdd (dedAdd α β) γ = dedAdd α (dedAdd β γ)) ∧
    (∀ α : ZFSet.{u}, α ∈ dedekindCutsTA →
      dedAdd α dedZero = α ∧ dedAdd dedZero α = α) ∧
    (∀ α β : ZFSet.{u}, α ∈ dedekindCutsTA → β ∈ dedekindCutsTA →
      dedAdd α β = dedAdd β α) := by
  exact ⟨fun _ _ ha hb => TA_PRO_00084_dedAdd_mem em ha hb,
    dedZero_mem,
    fun _ ha => ⟨TA_PRO_00087_dedNeg_mem em ha, TA_COR_00020_dedAdd_neg_bilateral em ha⟩,
    fun _ _ _ ha hb hc => TA_THM_00041_dedAdd_assoc ha hb hc,
    fun _ ha => TA_PRO_00086_dedZero_neutral ha,
    fun _ _ ha hb => TA_THM_00042_dedAdd_comm ha hb⟩

theorem TA_PRO_00089_dedAdd_cancel_right (em : ∀ p : Prop, p ∨ ¬p)
    {α β γ : ZFSet.{u}} (hα : α ∈ dedekindCutsTA)
    (hβ : β ∈ dedekindCutsTA) (hγ : γ ∈ dedekindCutsTA)
    (he : dedAdd α γ = dedAdd β γ) : α = β := by
  have hnγ := TA_PRO_00087_dedNeg_mem em hγ
  have hγneg := TA_PRO_00088_dedAdd_neg em hγ
  calc
    α = dedAdd α dedZero := (TA_PRO_00086_dedZero_neutral hα).1.symm
    _ = dedAdd α (dedAdd γ (dedNeg γ)) := congrArg (dedAdd α) hγneg.symm
    _ = dedAdd (dedAdd α γ) (dedNeg γ) := (TA_THM_00041_dedAdd_assoc hα hγ hnγ).symm
    _ = dedAdd (dedAdd β γ) (dedNeg γ) := congrArg (fun z => dedAdd z (dedNeg γ)) he
    _ = dedAdd β (dedAdd γ (dedNeg γ)) := TA_THM_00041_dedAdd_assoc hβ hγ hnγ
    _ = dedAdd β dedZero := congrArg (dedAdd β) hγneg
    _ = β := (TA_PRO_00086_dedZero_neutral hβ).1

theorem TA_PRO_00089_dedAdd_cancel_left (em : ∀ p : Prop, p ∨ ¬p)
    {α β γ : ZFSet.{u}} (hα : α ∈ dedekindCutsTA)
    (hβ : β ∈ dedekindCutsTA) (hγ : γ ∈ dedekindCutsTA)
    (he : dedAdd γ α = dedAdd γ β) : α = β := by
  apply TA_PRO_00089_dedAdd_cancel_right em hα hβ hγ
  exact (TA_THM_00042_dedAdd_comm hα hγ).trans
    (he.trans (TA_THM_00042_dedAdd_comm hγ hβ))

/-- TA-DEF-00090: sustracción como composición de constructores. -/
def dedSub (α β : ZFSet.{u}) : ZFSet.{u} := dedAdd α (dedNeg β)

theorem TA_DEF_00090_dedSub_eq {α β : ZFSet.{u}} :
    dedSub α β = dedAdd α (dedNeg β) := rfl

theorem mem_dedSub_iff {α β r : ZFSet.{u}} :
    r ∈ dedSub α β ↔ r ∈ rationalsTA ∧
      ∃ a : ZFSet.{u}, a ∈ α ∧ ∃ b : ZFSet.{u},
        b ∈ dedNeg β ∧ RatAdd a b r :=
  TA_DEF_00085_mem_dedAdd_iff

theorem dedSub_mem (em : ∀ p : Prop, p ∨ ¬p)
    {α β : ZFSet.{u}} (hα : α ∈ dedekindCutsTA)
    (hβ : β ∈ dedekindCutsTA) : dedSub α β ∈ dedekindCutsTA :=
  TA_PRO_00084_dedAdd_mem em hα (TA_PRO_00087_dedNeg_mem em hβ)

/-- Grafo derivado de la sustracción, no una operación racional elegida. -/
def dedSubGraph : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ α β γ : ZFSet.{u},
    z = ZFSet.pair (ZFSet.pair α β) γ ∧ γ = dedSub α β)
    (cartesianProductFoundational
      (cartesianProductFoundational dedekindCutsTA dedekindCutsTA) dedekindCutsTA)

theorem mem_dedSubGraph_iff {α β γ : ZFSet.{u}} :
    ZFSet.pair (ZFSet.pair α β) γ ∈ dedSubGraph ↔
      α ∈ dedekindCutsTA ∧ β ∈ dedekindCutsTA ∧
      γ ∈ dedekindCutsTA ∧ γ = dedSub α β := by
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

theorem dedSubGraph_isFunc (em : ∀ p : Prop, p ∨ ¬p) :
    IsFuncFoundational
      (cartesianProductFoundational (dedekindCutsTA : ZFSet.{u}) dedekindCutsTA)
      dedekindCutsTA dedSubGraph := by
  constructor
  · intro z hz
    rcases (ZFSet.mem_sep.mp hz).2 with ⟨a, b, c, he, _⟩
    rw [he] at hz
    have h := mem_dedSubGraph_iff.mp hz
    exact ⟨ZFSet.pair a b, mem_cartesianProductFoundational.mpr ⟨h.1, h.2.1⟩,
      c, h.2.2.1, he⟩
  · intro z hz
    rcases (ZFSet.mem_sep.mp hz).2 with ⟨a, ha, b, hb, he⟩
    subst z
    have hc := dedSub_mem em ha hb
    refine ⟨dedSub a b, ⟨hc, mem_dedSubGraph_iff.mpr ⟨ha, hb, hc, rfl⟩⟩, ?_⟩
    intro c hc'
    exact (mem_dedSubGraph_iff.mp hc'.2).2.2.2

def dedSubFunction : ZFSet.{u} :=
  functionTriple (cartesianProductFoundational dedekindCutsTA dedekindCutsTA)
    dedekindCutsTA dedSubGraph

theorem dedSubFunction_isTriple (em : ∀ p : Prop, p ∨ ¬p) :
    IsFunctionTriple
      (cartesianProductFoundational (dedekindCutsTA : ZFSet.{u}) dedekindCutsTA)
      dedekindCutsTA dedSubFunction :=
  TA_DEF_00018_functionTriple_iff.mpr (dedSubGraph_isFunc em)

/-- TA-COR-00021: identidad de constructores, sin em. -/
theorem TA_COR_00021_rationalSection_sub {p q r : ZFSet.{u}}
    (hp : p ∈ rationalsTA) (hq : q ∈ rationalsTA) (hs : RatSub p q r) :
    rationalSection r = dedSub (rationalSection p) (rationalSection q) := by
  rcases hs with ⟨nq, hnq, hsum⟩
  have hnqQ := funcFoundational_value_mem TratadoAnalisis.Rationals.Additive.ratNegGraph_isFunc hnq
  change rationalSection r = dedAdd (rationalSection p) (dedNeg (rationalSection q))
  rw [TA_COR_00019_rationalSection_neg hq hnq]
  exact TA_PRO_00085_rationalSection_add hp hnqQ hsum

end TratadoAnalisis.Dedekind.AdditiveGroup
