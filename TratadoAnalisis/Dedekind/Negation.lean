import TratadoAnalisis.Dedekind.Boundary

namespace TratadoAnalisis.Dedekind.Negation
universe u
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.Trichotomy
open TratadoAnalisis.Rationals.Signs
open TratadoAnalisis.Rationals.Division
open TratadoAnalisis.Rationals.NoSupremumSqrtTwo
open TratadoAnalisis.Dedekind.Definition
open TratadoAnalisis.Dedekind.Order
open TratadoAnalisis.Dedekind.RationalSection
open TratadoAnalisis.Dedekind.Addition
open TratadoAnalisis.Dedekind.Boundary
open TratadoAnalisis.Foundations.FunctionTriple

/-- TA-DEF-00088: ningún opuesto racional se escoge al separar. -/
def dedNeg (α : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun r => ∃ s : ZFSet.{u}, s ∈ rationalsTA ∧ s ∉ α ∧
    ∃ ns : ZFSet.{u}, RatNeg s ns ∧ RatLT r ns) rationalsTA

theorem TA_DEF_00088_mem_dedNeg_iff {α r : ZFSet.{u}} :
    r ∈ dedNeg α ↔ r ∈ rationalsTA ∧
      ∃ s : ZFSet.{u}, s ∈ rationalsTA ∧ s ∉ α ∧
        ∃ ns : ZFSet.{u}, RatNeg s ns ∧ RatLT r ns :=
  ZFSet.mem_sep

theorem dedNeg_subset_rationals (α : ZFSet.{u}) : dedNeg α ⊆ rationalsTA :=
  fun _ h => (TA_DEF_00088_mem_dedNeg_iff.mp h).1

/-- TA-PRO-00087: em sólo obtiene testigos interior y exterior. -/
theorem TA_PRO_00087_dedNeg_mem (em : ∀ p : Prop, p ∨ ¬p)
    {α : ZFSet.{u}} (hα : α ∈ dedekindCutsTA) : dedNeg α ∈ dedekindCutsTA := by
  have ca := TA_PRO_00079_mem_dedekindCuts_iff.mp hα
  apply TA_PRO_00079_mem_dedekindCuts_iff.mpr
  refine ⟨dedNeg_subset_rationals α, ?_, ?_, ?_, ?_⟩
  · rcases cut_exterior_inhabited em ca with ⟨s, hs, hso⟩
    rcases ratNeg_exists hs with ⟨ns, hns, hn⟩
    rcases rationalSection_sub_one_mem hns with ⟨r, _, hr⟩
    rcases TA_DEF_00081_mem_rationalSection_iff.mp hr with ⟨hrQ, hrlt⟩
    intro he
    have hm : r ∈ dedNeg α :=
      TA_DEF_00088_mem_dedNeg_iff.mpr ⟨hrQ, s, hs, hso, ns, hn, hrlt⟩
    rw [he] at hm
    exact ZFSet.notMem_empty r hm
  · rcases cut_inhabited em ca with ⟨a, ha⟩
    rcases ratNeg_exists (ca.1 ha) with ⟨na, hna, hneg⟩
    intro he
    have hm : na ∈ dedNeg α := he.symm ▸ hna
    rcases TA_DEF_00088_mem_dedNeg_iff.mp hm with ⟨_, s, hs, hso, ns, hns, hlt⟩
    have hsa := (TA_LEM_00020_clause2_neg_lt_iff hs (ca.1 ha) hns hneg).mpr hlt
    exact hso (ca.2.2.2.1 a ha s hs hsa)
  · intro r hr q hq hqr
    rcases TA_DEF_00088_mem_dedNeg_iff.mp hr with ⟨hrQ, s, hs, hso, ns, hn, hrns⟩
    have hnsQ := funcFoundational_value_mem ratNegGraph_isFunc hn
    exact TA_DEF_00088_mem_dedNeg_iff.mpr
      ⟨hq, s, hs, hso, ns, hn, ratLT_of_lt_of_le_local hq hrQ hnsQ hqr hrns.1⟩
  · intro r hr
    rcases TA_DEF_00088_mem_dedNeg_iff.mp hr with ⟨hrQ, s, hs, hso, ns, hn, hrns⟩
    have hnsQ := funcFoundational_value_mem ratNegGraph_isFunc hn
    rcases TA_THM_00030_rational_density hrQ hnsQ hrns with ⟨q, hq, hrq, hqns⟩
    exact ⟨q, TA_DEF_00088_mem_dedNeg_iff.mpr ⟨hq, s, hs, hso, ns, hn, hqns⟩, hrq⟩

/-- TA-DEF-00089: grafo y objeto función del opuesto. -/
def dedNegGraph : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ α β : ZFSet.{u},
    z = ZFSet.pair α β ∧ β = dedNeg α)
    (cartesianProductFoundational dedekindCutsTA dedekindCutsTA)

theorem mem_dedNegGraph_iff {α β : ZFSet.{u}} :
    ZFSet.pair α β ∈ dedNegGraph ↔
      α ∈ dedekindCutsTA ∧ β ∈ dedekindCutsTA ∧ β = dedNeg α := by
  constructor
  · intro h
    rcases ZFSet.mem_sep.mp h with ⟨hp, a, b, he, hb⟩
    rcases ZFSet.pair_injective he with ⟨rfl, rfl⟩
    exact ⟨(mem_cartesianProductFoundational.mp hp).1,
      (mem_cartesianProductFoundational.mp hp).2, hb⟩
  · rintro ⟨ha, hb, he⟩
    exact ZFSet.mem_sep.mpr
      ⟨mem_cartesianProductFoundational.mpr ⟨ha, hb⟩, α, β, rfl, he⟩

theorem TA_DEF_00089_dedNegGraph_isFunc (em : ∀ p : Prop, p ∨ ¬p) :
    IsFuncFoundational (dedekindCutsTA : ZFSet.{u}) dedekindCutsTA dedNegGraph := by
  constructor
  · intro z hz
    rcases (ZFSet.mem_sep.mp hz).2 with ⟨a, b, he, _⟩
    rw [he] at hz
    have hab := mem_dedNegGraph_iff.mp hz
    exact ⟨a, hab.1, b, hab.2.1, he⟩
  · intro a ha
    have hb := TA_PRO_00087_dedNeg_mem em ha
    refine ⟨dedNeg a, ⟨hb, mem_dedNegGraph_iff.mpr ⟨ha, hb, rfl⟩⟩, ?_⟩
    intro b hb'
    exact (mem_dedNegGraph_iff.mp hb'.2).2.2

def dedNegFunction : ZFSet.{u} :=
  functionTriple dedekindCutsTA dedekindCutsTA dedNegGraph

theorem TA_DEF_00089_dedNegFunction_isTriple (em : ∀ p : Prop, p ∨ ¬p) :
    IsFunctionTriple (dedekindCutsTA : ZFSet.{u}) dedekindCutsTA dedNegFunction :=
  TA_DEF_00018_functionTriple_iff.mpr (TA_DEF_00089_dedNegGraph_isFunc em)

theorem zero_neg_rel : RatNeg (ratZero : ZFSet.{u}) ratZero :=
  ratNeg_of_add_zero ratZero_mem_rationalsTA ratZero_mem_rationalsTA
    (add_zero_right_rel ratZero_mem_rationalsTA)

/-- TA-PRO-00088: ley del opuesto por frontera; no usa teoría de supremos. -/
theorem TA_PRO_00088_dedAdd_neg (em : ∀ p : Prop, p ∨ ¬p)
    {α : ZFSet.{u}} (hα : α ∈ dedekindCutsTA) :
    dedAdd α (dedNeg α) = dedZero := by
  have ca := TA_PRO_00079_mem_dedekindCuts_iff.mp hα
  apply ZFSet.ext
  intro x
  constructor
  · intro hx
    rcases TA_DEF_00085_mem_dedAdd_iff.mp hx with ⟨hxQ, a, ha, b, hb, hab⟩
    rcases TA_DEF_00088_mem_dedNeg_iff.mp hb with ⟨hbQ, s, hs, hso, ns, hn, hblt⟩
    have hns := funcFoundational_value_mem ratNegGraph_isFunc hn
    rcases ratAdd_exists (ca.1 ha) hns with ⟨z, hz, haz⟩
    have hxz := ratLT_add_left_local hbQ hns (ca.1 ha) hblt hab haz
    have hz0 := ratLT_add_right_local (ca.1 ha) hs hns
      (cut_member_lt_nonmember ca hs hso ha) haz (ratAdd_neg_right_rel hs hn)
    exact TA_DEF_00081_mem_rationalSection_iff.mpr
      ⟨hxQ, ratLT_of_lt_of_le_local hxQ hz ratZero_mem_rationalsTA hxz hz0.1⟩
  · intro hx
    rcases TA_DEF_00081_mem_rationalSection_iff.mp hx with ⟨hxQ, hx0⟩
    rcases ratNeg_exists hxQ with ⟨nx, hnxQ, hnx⟩
    have h0nx := (TA_LEM_00020_clause2_neg_lt_iff hxQ ratZero_mem_rationalsTA
      hnx zero_neg_rel).mp hx0
    rcases TA_THM_00030_rational_density ratZero_mem_rationalsTA hnxQ h0nx with
      ⟨h, hh, h0h, hhnx⟩
    rcases TA_LEM_00022_boundary_approximation em hα hh h0h with ⟨a, ha, s, has, hso⟩
    have haQ := ca.1 ha
    have hs := funcFoundational_value_mem ratAddGraph_isFunc has
    rcases ratNeg_exists hs with ⟨ns, hnsQ, hns⟩
    rcases ratSub_exists hxQ haQ with ⟨b, hbQ, hbsub⟩
    have hba := ratSub_add_cancel hxQ haQ hbsub
    rcases ratAdd_exists hxQ hh with ⟨xh, hxh, hxAdd⟩
    have hxh0 := ratLT_add_left_local hh hnxQ hxQ hhnx hxAdd
      (ratAdd_neg_right_rel hxQ hnx)
    rcases ratAdd_exists hbQ hs with ⟨bs, _, hbs⟩
    have he : xh = bs := ratAdd_assoc hbQ haQ hh hba hxAdd has hbs
    rw [← he] at hbs
    have hnss := ratAdd_comm_rel hs hnsQ (ratAdd_neg_right_rel hs hns)
    have hblt := ratLT_add_cancel_right_local hbQ hnsQ hs hbs hnss hxh0
    have hbNeg : b ∈ dedNeg α :=
      TA_DEF_00088_mem_dedNeg_iff.mpr ⟨hbQ, s, hs, hso, ns, hns, hblt⟩
    exact mem_dedAdd_of_add haQ hbQ ha hbNeg (ratAdd_comm_rel hbQ haQ hba)

/-- TA-COR-00019: compatibilidad con secciones racionales, sin em. -/
theorem TA_COR_00019_rationalSection_neg {p np : ZFSet.{u}}
    (hp : p ∈ rationalsTA) (hnp : RatNeg p np) :
    dedNeg (rationalSection p) = rationalSection np := by
  have hnpQ := funcFoundational_value_mem ratNegGraph_isFunc hnp
  apply ZFSet.ext
  intro q
  constructor
  · intro hq
    rcases TA_DEF_00088_mem_dedNeg_iff.mp hq with ⟨hqQ, s, hs, hso, ns, hns, hqns⟩
    have hps : RatLE p s := by
      rcases TA_PRO_00172_rational_trichotomy hp hs with h | he | h
      · exact h.1
      · rw [he]
        exact ratLE_refl hs
      · exact (hso (TA_DEF_00081_mem_rationalSection_iff.mpr ⟨hs, h⟩)).elim
    have hnsQ := funcFoundational_value_mem ratNegGraph_isFunc hns
    have hnsnp := (TA_LEM_00020_clause2_neg_le_iff hp hs hnp hns).mp hps
    exact TA_DEF_00081_mem_rationalSection_iff.mpr
      ⟨hqQ, ratLT_of_lt_of_le_local hqQ hnsQ hnpQ hqns hnsnp⟩
  · intro hq
    rcases TA_DEF_00081_mem_rationalSection_iff.mp hq with ⟨hqQ, hqnp⟩
    exact TA_DEF_00088_mem_dedNeg_iff.mpr
      ⟨hqQ, p, hp, rationalSection_self_not_mem p, np, hnp, hqnp⟩

end TratadoAnalisis.Dedekind.Negation
