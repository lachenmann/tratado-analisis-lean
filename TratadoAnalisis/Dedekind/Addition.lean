import TratadoAnalisis.Dedekind.EmbeddingTriple
import TratadoAnalisis.Rationals.Division

namespace TratadoAnalisis.Dedekind.Addition
universe u
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.OrderedFieldCompatibility
open TratadoAnalisis.Rationals.NoSupremumSqrtTwo
open TratadoAnalisis.Rationals.Signs
open TratadoAnalisis.Rationals.Division
open TratadoAnalisis.Dedekind.Definition
open TratadoAnalisis.Dedekind.Order
open TratadoAnalisis.Dedekind.RationalSection
open TratadoAnalisis.Foundations.FunctionTriple

/-- TA-LEM-00021: certificado del lema exterior ya disponible en Order. -/
theorem TA_LEM_00021_member_lt_exterior {α a r : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) (hr : r ∈ rationalsTA)
    (hout : r ∉ α) (ha : a ∈ α) : RatLT a r :=
  cut_member_lt_nonmember (TA_PRO_00079_mem_dedekindCuts_iff.mp hα) hr hout ha

/-- TA-DEF-00085: candidato definido por Separación sin elegir sumandos. -/
def dedAdd (α β : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun r => ∃ a : ZFSet.{u}, a ∈ α ∧
    ∃ b : ZFSet.{u}, b ∈ β ∧ RatAdd a b r) rationalsTA

theorem TA_DEF_00085_mem_dedAdd_iff {α β r : ZFSet.{u}} :
    r ∈ dedAdd α β ↔ r ∈ rationalsTA ∧
      ∃ a : ZFSet.{u}, a ∈ α ∧
        ∃ b : ZFSet.{u}, b ∈ β ∧ RatAdd a b r :=
  ZFSet.mem_sep

theorem dedAdd_subset_rationals (α β : ZFSet.{u}) :
    dedAdd α β ⊆ rationalsTA :=
  fun _ h => (TA_DEF_00085_mem_dedAdd_iff.mp h).1

theorem mem_dedAdd_of_add {α β a b r : ZFSet.{u}}
    (_haQ : a ∈ rationalsTA) (_hbQ : b ∈ rationalsTA)
    (ha : a ∈ α) (hb : b ∈ β) (hs : RatAdd a b r) :
    r ∈ dedAdd α β :=
  TA_DEF_00085_mem_dedAdd_iff.mpr
    ⟨funcFoundational_value_mem ratAddGraph_isFunc hs, a, ha, b, hb, hs⟩

/-- TA-PRO-00084: sólo la obtención de habitantes recibe em. -/
theorem TA_PRO_00084_dedAdd_mem (em : ∀ p : Prop, p ∨ ¬p)
    {α β : ZFSet.{u}} (hα : α ∈ dedekindCutsTA)
    (hβ : β ∈ dedekindCutsTA) : dedAdd α β ∈ dedekindCutsTA := by
  have ca := TA_PRO_00079_mem_dedekindCuts_iff.mp hα
  have cb := TA_PRO_00079_mem_dedekindCuts_iff.mp hβ
  apply TA_PRO_00079_mem_dedekindCuts_iff.mpr
  refine ⟨dedAdd_subset_rationals α β, ?_, ?_, ?_, ?_⟩
  · rcases cut_inhabited em ca with ⟨a, ha⟩
    rcases cut_inhabited em cb with ⟨b, hb⟩
    rcases ratAdd_exists (ca.1 ha) (cb.1 hb) with ⟨r, _, hs⟩
    intro he
    have hm := mem_dedAdd_of_add (ca.1 ha) (cb.1 hb) ha hb hs
    rw [he] at hm
    exact ZFSet.notMem_empty r hm
  · rcases cut_exterior_inhabited em ca with ⟨a, ha, hao⟩
    rcases cut_exterior_inhabited em cb with ⟨b, hb, hbo⟩
    rcases ratAdd_exists ha hb with ⟨r, hr, hs⟩
    intro he
    have hm : r ∈ dedAdd α β := he.symm ▸ hr
    rcases TA_DEF_00085_mem_dedAdd_iff.mp hm with ⟨_, x, hx, y, hy, hxy⟩
    have hxQ := ca.1 hx
    have hyQ := cb.1 hy
    rcases ratAdd_exists ha hyQ with ⟨ay, hay, hayRel⟩
    have hfirst := ratLT_add_right_local hxQ ha hyQ
      (cut_member_lt_nonmember ca ha hao hx) hxy hayRel
    have hsecond := ratLT_add_left_local hyQ hb ha
      (cut_member_lt_nonmember cb hb hbo hy) hayRel hs
    have hrr := ratLT_of_lt_of_le_local hr hay hr hfirst hsecond.1
    exact hrr.2 rfl
  · intro x hx r hr hrx
    rcases TA_DEF_00085_mem_dedAdd_iff.mp hx with ⟨hxQ, a, ha, b, hb, hab⟩
    have haQ := ca.1 ha
    have hbQ := cb.1 hb
    rcases ratSub_exists hr hbQ with ⟨d, hd, hsub⟩
    have hdb := ratSub_add_cancel hr hbQ hsub
    have hda := ratLT_add_cancel_right_local hd haQ hbQ hdb hab hrx
    have hdin := ca.2.2.2.1 a ha d hd hda
    exact mem_dedAdd_of_add hd hbQ hdin hb hdb
  · intro x hx
    rcases TA_DEF_00085_mem_dedAdd_iff.mp hx with ⟨_, a, ha, b, hb, hab⟩
    rcases ca.2.2.2.2 a ha with ⟨a', ha', haa'⟩
    rcases ratAdd_exists (ca.1 ha') (cb.1 hb) with ⟨y, _, hy⟩
    exact ⟨y, mem_dedAdd_of_add (ca.1 ha') (cb.1 hb) ha' hb hy,
      ratLT_add_right_local (ca.1 ha) (ca.1 ha') (cb.1 hb) haa' hab hy⟩

/-- TA-DEF-00086: grafo de la suma sobre el producto fundacional. -/
def dedAddGraph : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ α β γ : ZFSet.{u},
    z = ZFSet.pair (ZFSet.pair α β) γ ∧ γ = dedAdd α β)
    (cartesianProductFoundational
      (cartesianProductFoundational dedekindCutsTA dedekindCutsTA) dedekindCutsTA)

theorem mem_dedAddGraph_iff {α β γ : ZFSet.{u}} :
    ZFSet.pair (ZFSet.pair α β) γ ∈ dedAddGraph ↔
      α ∈ dedekindCutsTA ∧ β ∈ dedekindCutsTA ∧
      γ ∈ dedekindCutsTA ∧ γ = dedAdd α β := by
  constructor
  · intro h
    rcases ZFSet.mem_sep.mp h with ⟨hp, a, b, c, he, hc⟩
    have hc' := ZFSet.pair_injective he
    have hab := ZFSet.pair_injective hc'.1
    rcases hab with ⟨rfl, rfl⟩
    rcases hc'.2 with rfl
    rcases mem_cartesianProductFoundational.mp hp with ⟨hab, hcD⟩
    exact ⟨(mem_cartesianProductFoundational.mp hab).1,
      (mem_cartesianProductFoundational.mp hab).2, hcD, hc⟩
  · rintro ⟨ha, hb, hc, he⟩
    exact ZFSet.mem_sep.mpr
      ⟨mem_cartesianProductFoundational.mpr
        ⟨mem_cartesianProductFoundational.mpr ⟨ha, hb⟩, hc⟩, α, β, γ, rfl, he⟩

theorem TA_DEF_00086_dedAddGraph_isFunc (em : ∀ p : Prop, p ∨ ¬p) :
    IsFuncFoundational
      (cartesianProductFoundational (dedekindCutsTA : ZFSet.{u}) dedekindCutsTA)
      dedekindCutsTA dedAddGraph := by
  constructor
  · intro z hz
    rcases (ZFSet.mem_sep.mp hz).2 with ⟨a, b, c, he, _⟩
    rw [he] at hz
    rcases mem_dedAddGraph_iff.mp hz with ⟨ha, hb, hc, _⟩
    exact ⟨ZFSet.pair a b, mem_cartesianProductFoundational.mpr ⟨ha, hb⟩, c, hc, he⟩
  · intro z hz
    rcases (ZFSet.mem_sep.mp hz).2 with ⟨a, ha, b, hb, he⟩
    subst z
    have hc := TA_PRO_00084_dedAdd_mem em ha hb
    refine ⟨dedAdd a b, ⟨hc, mem_dedAddGraph_iff.mpr ⟨ha, hb, hc, rfl⟩⟩, ?_⟩
    intro c hc'
    exact (mem_dedAddGraph_iff.mp hc'.2).2.2.2

def dedAddFunction : ZFSet.{u} :=
  functionTriple (cartesianProductFoundational dedekindCutsTA dedekindCutsTA)
    dedekindCutsTA dedAddGraph

theorem TA_DEF_00086_dedAddFunction_isTriple (em : ∀ p : Prop, p ∨ ¬p) :
    IsFunctionTriple
      (cartesianProductFoundational (dedekindCutsTA : ZFSet.{u}) dedekindCutsTA)
      dedekindCutsTA dedAddFunction :=
  TA_DEF_00018_functionTriple_iff.mpr (TA_DEF_00086_dedAddGraph_isFunc em)

/-- TA-DEF-00087: cero como sección racional, no como función elegida. -/
def dedZero : ZFSet.{u} := rationalSection ratZero

theorem TA_DEF_00087_dedZero_eq :
    (dedZero : ZFSet.{u}) = rationalSection ratZero := rfl

theorem dedZero_mem : (dedZero : ZFSet.{u}) ∈ dedekindCutsTA :=
  TA_PRO_00080_rationalSection_mem ratZero_mem_rationalsTA

theorem TA_COR_00018_embedding_zero :
    rationalSection (ratZero : ZFSet.{u}) = dedZero := rfl

theorem add_zero_right_rel {a : ZFSet.{u}} (ha : a ∈ rationalsTA) :
    RatAdd a ratZero a := by
  rcases ratAdd_exists ha ratZero_mem_rationalsTA with ⟨r, _, hr⟩
  rw [ratAdd_zero_right ha hr] at hr
  exact hr

theorem add_zero_left_rel {a : ZFSet.{u}} (ha : a ∈ rationalsTA) :
    RatAdd ratZero a a :=
  ratAdd_comm_rel ha ratZero_mem_rationalsTA (add_zero_right_rel ha)

/-- TA-PRO-00085: igualdad de constructores, sin em. -/
theorem TA_PRO_00085_rationalSection_add {p q r : ZFSet.{u}}
    (hp : p ∈ rationalsTA) (hq : q ∈ rationalsTA) (hpq : RatAdd p q r) :
    rationalSection r = dedAdd (rationalSection p) (rationalSection q) := by
  have hr := funcFoundational_value_mem ratAddGraph_isFunc hpq
  apply ZFSet.ext
  intro x
  constructor
  · intro hx
    rcases TA_DEF_00081_mem_rationalSection_iff.mp hx with ⟨hxQ, hxr⟩
    rcases ratSub_exists hxQ hq with ⟨d, hd, hdrel⟩
    have hdq := ratSub_add_cancel hxQ hq hdrel
    have hdp := ratLT_add_cancel_right_local hd hp hq hdq hpq hxr
    rcases TA_THM_00030_rational_density hd hp hdp with ⟨a, haQ, hda, hap⟩
    rcases ratSub_exists hxQ haQ with ⟨b, hbQ, hbrel⟩
    have hba := ratSub_add_cancel hxQ haQ hbrel
    rcases ratAdd_exists haQ hq with ⟨aq, haq, haqrel⟩
    have hxaq := ratLT_add_right_local hd haQ hq hda hdq haqrel
    have hbq := ratLT_add_cancel_right_local hbQ hq haQ hba
      (ratAdd_comm_rel haQ hq haqrel) hxaq
    exact mem_dedAdd_of_add haQ hbQ
      (TA_DEF_00081_mem_rationalSection_iff.mpr ⟨haQ, hap⟩)
      (TA_DEF_00081_mem_rationalSection_iff.mpr ⟨hbQ, hbq⟩)
      (ratAdd_comm_rel hbQ haQ hba)
  · intro hx
    rcases TA_DEF_00085_mem_dedAdd_iff.mp hx with ⟨hxQ, a, ha, b, hb, hab⟩
    rcases TA_DEF_00081_mem_rationalSection_iff.mp ha with ⟨haQ, hap⟩
    rcases TA_DEF_00081_mem_rationalSection_iff.mp hb with ⟨hbQ, hbq⟩
    rcases ratAdd_exists hp hbQ with ⟨pb, hpb, hpbrel⟩
    have hxpb := ratLT_add_right_local haQ hp hbQ hap hab hpbrel
    have hpbr := ratLT_add_left_local hbQ hq hp hbq hpbrel hpq
    exact TA_DEF_00081_mem_rationalSection_iff.mpr
      ⟨hxQ, ratLT_of_lt_of_le_local hxQ hpb hr hxpb hpbr.1⟩

/-- TA-THM-00042: constructiva, incluso para subconjuntos arbitrarios de Q. -/
theorem dedAdd_comm_of_subsets {α β : ZFSet.{u}}
    (hα : α ⊆ rationalsTA) (hβ : β ⊆ rationalsTA) :
    dedAdd α β = dedAdd β α := by
  apply ZFSet.ext
  intro x
  constructor
  · intro hx
    rcases TA_DEF_00085_mem_dedAdd_iff.mp hx with ⟨_, a, ha, b, hb, hs⟩
    exact mem_dedAdd_of_add (hβ hb) (hα ha) hb ha
      (ratAdd_comm_rel (hα ha) (hβ hb) hs)
  · intro hx
    rcases TA_DEF_00085_mem_dedAdd_iff.mp hx with ⟨_, b, hb, a, ha, hs⟩
    exact mem_dedAdd_of_add (hα ha) (hβ hb) ha hb
      (ratAdd_comm_rel (hβ hb) (hα ha) hs)

/-- TA-PRO-00086: neutro por testigos locales de redondez. -/
theorem TA_PRO_00086_dedZero_neutral {α : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) :
    dedAdd α dedZero = α ∧ dedAdd dedZero α = α := by
  have ca := TA_PRO_00079_mem_dedekindCuts_iff.mp hα
  have hz : (dedZero : ZFSet.{u}) ⊆ rationalsTA :=
    fun _ h => (TA_DEF_00081_mem_rationalSection_iff.mp h).1
  have he : dedAdd α dedZero = α := by
    apply ZFSet.ext
    intro x
    constructor
    · intro hx
      rcases TA_DEF_00085_mem_dedAdd_iff.mp hx with ⟨hxQ, a, ha, b, hb, hab⟩
      rcases TA_DEF_00081_mem_rationalSection_iff.mp hb with ⟨hbQ, hb0⟩
      have hxa := ratLT_add_left_local hbQ ratZero_mem_rationalsTA (ca.1 ha)
        hb0 hab (add_zero_right_rel (ca.1 ha))
      exact ca.2.2.2.1 a ha x hxQ hxa
    · intro hx
      rcases ca.2.2.2.2 x hx with ⟨a, ha, hxa⟩
      rcases ratSub_exists (ca.1 hx) (ca.1 ha) with ⟨b, hb, hbrel⟩
      have hba := ratSub_add_cancel (ca.1 hx) (ca.1 ha) hbrel
      have hb0 := ratLT_add_cancel_right_local hb ratZero_mem_rationalsTA (ca.1 ha)
        hba (add_zero_left_rel (ca.1 ha)) hxa
      exact mem_dedAdd_of_add (ca.1 ha) hb ha
        (TA_DEF_00081_mem_rationalSection_iff.mpr ⟨hb, hb0⟩)
        (ratAdd_comm_rel hb (ca.1 ha) hba)
  exact ⟨he, (dedAdd_comm_of_subsets hz ca.1).trans he⟩

/-- TA-THM-00041: asociatividad por reasociación de testigos racionales. -/
theorem dedAdd_assoc_of_subsets {α β γ : ZFSet.{u}}
    (hα : α ⊆ rationalsTA) (hβ : β ⊆ rationalsTA) (hγ : γ ⊆ rationalsTA) :
    dedAdd (dedAdd α β) γ = dedAdd α (dedAdd β γ) := by
  apply ZFSet.ext
  intro r
  constructor
  · intro hr
    rcases TA_DEF_00085_mem_dedAdd_iff.mp hr with ⟨_, ab, hab, c, hc, hsum⟩
    rcases TA_DEF_00085_mem_dedAdd_iff.mp hab with ⟨_, a, ha, b, hb, habrel⟩
    rcases ratAdd_exists (hβ hb) (hγ hc) with ⟨bc, hbc, hbcrel⟩
    rcases ratAdd_exists (hα ha) hbc with ⟨s, _, hs⟩
    have he := ratAdd_assoc (hα ha) (hβ hb) (hγ hc) habrel hsum hbcrel hs
    rw [he]
    exact mem_dedAdd_of_add (hα ha) hbc ha
      (mem_dedAdd_of_add (hβ hb) (hγ hc) hb hc hbcrel) hs
  · intro hr
    rcases TA_DEF_00085_mem_dedAdd_iff.mp hr with ⟨_, a, ha, bc, hbc, hsum⟩
    rcases TA_DEF_00085_mem_dedAdd_iff.mp hbc with ⟨_, b, hb, c, hc, hbcrel⟩
    rcases ratAdd_exists (hα ha) (hβ hb) with ⟨ab, hab, habrel⟩
    rcases ratAdd_exists hab (hγ hc) with ⟨s, _, hs⟩
    have he := ratAdd_assoc (hα ha) (hβ hb) (hγ hc) habrel hs hbcrel hsum
    rw [← he]
    exact mem_dedAdd_of_add hab (hγ hc)
      (mem_dedAdd_of_add (hα ha) (hβ hb) ha hb habrel) hc hs

/-- TA-THM-00041 en el dominio del manuscrito, sin em. -/
theorem TA_THM_00041_dedAdd_assoc {α β γ : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) (hβ : β ∈ dedekindCutsTA)
    (hγ : γ ∈ dedekindCutsTA) :
    dedAdd (dedAdd α β) γ = dedAdd α (dedAdd β γ) :=
  dedAdd_assoc_of_subsets
    (TA_PRO_00079_mem_dedekindCuts_iff.mp hα).1
    (TA_PRO_00079_mem_dedekindCuts_iff.mp hβ).1
    (TA_PRO_00079_mem_dedekindCuts_iff.mp hγ).1

/-- TA-THM-00042 en el dominio del manuscrito, sin em. -/
theorem TA_THM_00042_dedAdd_comm {α β : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) (hβ : β ∈ dedekindCutsTA) :
    dedAdd α β = dedAdd β α :=
  dedAdd_comm_of_subsets
    (TA_PRO_00079_mem_dedekindCuts_iff.mp hα).1
    (TA_PRO_00079_mem_dedekindCuts_iff.mp hβ).1

end TratadoAnalisis.Dedekind.Addition
