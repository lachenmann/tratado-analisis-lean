import TratadoAnalisis.Dedekind.Positivity

namespace TratadoAnalisis.Dedekind.PositiveMultiplication
universe u
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.Field
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.Trichotomy
open TratadoAnalisis.Rationals.OrderedFieldCompatibility
open TratadoAnalisis.Rationals.StrictOrder
open TratadoAnalisis.Rationals.SquareMonotonicity
open TratadoAnalisis.Rationals.NoSupremumSqrtTwo
open TratadoAnalisis.Rationals.Signs
open TratadoAnalisis.Rationals.Division
open TratadoAnalisis.Rationals.PositiveProducts
open TratadoAnalisis.Dedekind.Definition
open TratadoAnalisis.Dedekind.Order
open TratadoAnalisis.Dedekind.RationalSection
open TratadoAnalisis.Dedekind.Addition
open TratadoAnalisis.Dedekind.Positivity
open TratadoAnalisis.Foundations.FunctionTriple

theorem positive_product_lt_of_factor_bounds {a b x y ab xy : ZFSet.{u}}
    (ha : a ∈ rationalsTA) (hb : b ∈ rationalsTA)
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (h0b : RatLT ratZero b) (h0x : RatLT ratZero x)
    (hax : RatLT a x) (hby : RatLT b y)
    (hab : RatMul a b ab) (hxy : RatMul x y xy) : RatLT ab xy := by
  rcases ratMul_exists hx hb with ⟨xb, hxbQ, hxb⟩
  have hfirst := ratLT_mul_positive_right ha hx hb hax h0b hab hxb
  have hsecond := ratLT_mul_positive_left_local hb hy hx hby h0x hxb hxy
  exact ratLT_of_lt_of_le_local (ratMul_value_mem hab) hxbQ
    (ratMul_value_mem hxy) hfirst hsecond.1

/-- TA-PRO-00090: las extracciones interiores/exteriores reciben em. -/
theorem TA_PRO_00090_positiveMul_mem (em : ∀ p : Prop, p ∨ ¬p)
    {α β : ZFSet.{u}} (hα : α ∈ positiveCutsTA) (hβ : β ∈ positiveCutsTA) :
    dedPositiveMul α β ∈ positiveCutsTA := by
  have pa := TA_DEF_00091_mem_positiveCuts_iff.mp hα
  have pb := TA_DEF_00091_mem_positiveCuts_iff.mp hβ
  have hαD := pa.1.2.1
  have hβD := pb.1.2.1
  have ca := TA_PRO_00079_mem_dedekindCuts_iff.mp hαD
  have cb := TA_PRO_00079_mem_dedekindCuts_iff.mp hβD
  rcases (TA_LEM_00023_zero_mem_iff_positive_member hαD).mp
    (TA_LEM_00023_positive_implies_zero_mem em hαD pa) with ⟨a, ha, h0a⟩
  rcases (TA_LEM_00023_zero_mem_iff_positive_member hβD).mp
    (TA_LEM_00023_positive_implies_zero_mem em hβD pb) with ⟨b, hb, h0b⟩
  rcases ratMul_exists (ca.1 ha) (cb.1 hb) with ⟨ab, _, hab⟩
  have h0ab := TA_LEM_00020_clause5_positive_product (ca.1 ha) (cb.1 hb) hab h0a h0b
  have h0prod : (ratZero : ZFSet.{u}) ∈ dedPositiveMul α β :=
    mem_positiveMul_of_witness ratZero_mem_rationalsTA ha h0a hb h0b hab h0ab
  have hcut : IsDedekindCut (dedPositiveMul α β) := by
    refine ⟨dedPositiveMul_subset_rationals α β, ?_, ?_, ?_, ?_⟩
    · intro he
      exact ZFSet.notMem_empty ratZero (he ▸ h0prod)
    · rcases cut_exterior_inhabited em ca with ⟨x, hx, hxOut⟩
      rcases cut_exterior_inhabited em cb with ⟨y, hy, hyOut⟩
      have h0x := ratLT_of_lt_of_le_local ratZero_mem_rationalsTA (ca.1 ha) hx
        h0a (cut_member_lt_nonmember ca hx hxOut ha).1
      rcases ratMul_exists hx hy with ⟨xy, hxyQ, hxy⟩
      intro he
      have hm : xy ∈ dedPositiveMul α β := he.symm ▸ hxyQ
      rcases TA_DEF_00093_mem_positiveMul_iff.mp hm with ⟨_, c, hc, d, hd, cd, hcd, hlt⟩
      rcases TA_DEF_00092_mem_positivePart_iff.mp hc with ⟨hc, _⟩
      rcases TA_DEF_00092_mem_positivePart_iff.mp hd with ⟨hd, h0d⟩
      have hcdxy := positive_product_lt_of_factor_bounds (ca.1 hc) (cb.1 hd)
        hx hy h0d h0x (cut_member_lt_nonmember ca hx hxOut hc)
        (cut_member_lt_nonmember cb hy hyOut hd) hcd hxy
      exact (ratLT_of_lt_of_le_local hxyQ (ratMul_value_mem hcd) hxyQ hlt hcdxy.1).2 rfl
    · intro r hr s hs hsr
      rcases TA_DEF_00093_mem_positiveMul_iff.mp hr with ⟨hrQ, c, hc, d, hd, cd, hcd, hrlt⟩
      exact TA_DEF_00093_mem_positiveMul_iff.mpr
        ⟨hs, c, hc, d, hd, cd, hcd,
          ratLT_of_lt_of_le_local hs hrQ (ratMul_value_mem hcd) hsr hrlt.1⟩
    · intro r hr
      rcases TA_DEF_00093_mem_positiveMul_iff.mp hr with ⟨hrQ, c, hc, d, hd, cd, hcd, hrlt⟩
      rcases TA_THM_00030_rational_density hrQ (ratMul_value_mem hcd) hrlt
        with ⟨s, hs, hrs, hscd⟩
      exact ⟨s, TA_DEF_00093_mem_positiveMul_iff.mpr
        ⟨hs, c, hc, d, hd, cd, hcd, hscd⟩, hrs⟩
  exact TA_DEF_00091_mem_positiveCuts_iff.mpr
    (TA_LEM_00023_zero_mem_implies_positive
      (TA_PRO_00079_mem_dedekindCuts_iff.mpr hcut) h0prod)

/-- TA-PRO-00091: usa sólo la dirección constructiva de TA-LEM-00023. -/
theorem TA_PRO_00091_rationalSection_positive {p : ZFSet.{u}}
    (hp : p ∈ rationalsTA) (h0p : RatLT ratZero p) :
    rationalSection p ∈ positiveCutsTA :=
  TA_DEF_00091_mem_positiveCuts_iff.mpr
    (TA_LEM_00023_zero_mem_implies_positive (TA_PRO_00080_rationalSection_mem hp)
      (TA_DEF_00081_mem_rationalSection_iff.mpr ⟨ratZero_mem_rationalsTA, h0p⟩))

/-- TA-DEF-00094: grafo con dominio y codominio positivos. -/
def positiveMulGraph : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ α β γ : ZFSet.{u},
    z = ZFSet.pair (ZFSet.pair α β) γ ∧ γ = dedPositiveMul α β)
    (cartesianProductFoundational
      (cartesianProductFoundational positiveCutsTA positiveCutsTA) positiveCutsTA)

theorem mem_positiveMulGraph_iff {α β γ : ZFSet.{u}} :
    ZFSet.pair (ZFSet.pair α β) γ ∈ positiveMulGraph ↔
      α ∈ positiveCutsTA ∧ β ∈ positiveCutsTA ∧
      γ ∈ positiveCutsTA ∧ γ = dedPositiveMul α β := by
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

theorem TA_DEF_00094_positiveMulGraph_isFunc (em : ∀ p : Prop, p ∨ ¬p) :
    IsFuncFoundational
      (cartesianProductFoundational (positiveCutsTA : ZFSet.{u}) positiveCutsTA)
      positiveCutsTA positiveMulGraph := by
  constructor
  · intro z hz
    rcases (ZFSet.mem_sep.mp hz).2 with ⟨a, b, c, he, _⟩
    rw [he] at hz
    rcases mem_positiveMulGraph_iff.mp hz with ⟨ha, hb, hc, _⟩
    exact ⟨ZFSet.pair a b, mem_cartesianProductFoundational.mpr ⟨ha, hb⟩, c, hc, he⟩
  · intro z hz
    rcases (ZFSet.mem_sep.mp hz).2 with ⟨a, ha, b, hb, he⟩
    subst z
    have hc := TA_PRO_00090_positiveMul_mem em ha hb
    refine ⟨dedPositiveMul a b, ⟨hc, mem_positiveMulGraph_iff.mpr ⟨ha, hb, hc, rfl⟩⟩, ?_⟩
    intro c hc'
    exact (mem_positiveMulGraph_iff.mp hc'.2).2.2.2

def positiveMulFunction : ZFSet.{u} :=
  functionTriple (cartesianProductFoundational positiveCutsTA positiveCutsTA)
    positiveCutsTA positiveMulGraph

theorem TA_DEF_00094_positiveMulFunction_isTriple (em : ∀ p : Prop, p ∨ ¬p) :
    IsFunctionTriple
      (cartesianProductFoundational (positiveCutsTA : ZFSet.{u}) positiveCutsTA)
      positiveCutsTA positiveMulFunction :=
  TA_DEF_00018_functionTriple_iff.mpr (TA_DEF_00094_positiveMulGraph_isFunc em)

/-- TA-PRO-00092: identidad de constructores, sin em ni totalización. -/
theorem TA_PRO_00092_rationalSection_positiveMul {p q pq : ZFSet.{u}}
    (hp : p ∈ rationalsTA) (hq : q ∈ rationalsTA)
    (h0p : RatLT ratZero p) (h0q : RatLT ratZero q) (hpq : RatMul p q pq) :
    rationalSection pq = dedPositiveMul (rationalSection p) (rationalSection q) := by
  have hpqQ := ratMul_value_mem hpq
  apply ZFSet.ext
  intro x
  constructor
  · intro hx
    rcases TA_DEF_00081_mem_rationalSection_iff.mp hx with ⟨hxQ, hxlt⟩
    have hnonpos : RatLE x ratZero →
        x ∈ dedPositiveMul (rationalSection p) (rationalSection q) := by
      intro hx0
      rcases TA_THM_00030_rational_density ratZero_mem_rationalsTA hp h0p
        with ⟨a, haQ, h0a, hap⟩
      rcases TA_THM_00030_rational_density ratZero_mem_rationalsTA hq h0q
        with ⟨b, hbQ, h0b, hbq⟩
      rcases ratMul_exists haQ hbQ with ⟨ab, habQ, hab⟩
      have h0ab := TA_LEM_00020_clause5_positive_product haQ hbQ hab h0a h0b
      exact mem_positiveMul_of_witness hxQ
        (TA_DEF_00081_mem_rationalSection_iff.mpr ⟨haQ, hap⟩) h0a
        (TA_DEF_00081_mem_rationalSection_iff.mpr ⟨hbQ, hbq⟩) h0b hab
        (ratLT_of_le_of_lt_local hxQ ratZero_mem_rationalsTA habQ hx0 h0ab)
    rcases TA_PRO_00172_rational_trichotomy hxQ ratZero_mem_rationalsTA
      with hx0 | he | h0x
    · exact hnonpos hx0.1
    · apply hnonpos
      rw [← he]
      exact ratLE_refl hxQ
    · have hqNZ := mem_ratNonzeroTA_iff.mpr ⟨hq, fun he => h0q.2 he.symm⟩
      rcases ratDiv_exists hxQ hqNZ with ⟨d, hdQ, hd⟩
      have hdp := (ratDiv_lt_iff hxQ hp hq h0q hd hpq).mpr hxlt
      have h0d := ratDiv_positive hxQ hq h0x h0q hd
      rcases TA_THM_00030_rational_density hdQ hp hdp with ⟨a, haQ, hda, hap⟩
      have h0a := ratLT_of_lt_of_le_local ratZero_mem_rationalsTA hdQ haQ h0d hda.1
      rcases ratMul_exists haQ hq with ⟨aq, _, haq⟩
      have hxaq := (ratDiv_lt_iff hxQ haQ hq h0q hd haq).mp hda
      have haNZ := mem_ratNonzeroTA_iff.mpr ⟨haQ, fun he => h0a.2 he.symm⟩
      rcases ratDiv_exists hxQ haNZ with ⟨e, heQ, he⟩
      have heq := (ratDiv_lt_iff hxQ hq haQ h0a he
        (ratMul_comm_rel haQ hq haq)).mpr hxaq
      have h0e := ratDiv_positive hxQ haQ h0x h0a he
      rcases TA_THM_00030_rational_density heQ hq heq with ⟨b, hbQ, heb, hbq⟩
      have h0b := ratLT_of_lt_of_le_local ratZero_mem_rationalsTA heQ hbQ h0e heb.1
      rcases ratMul_exists haQ hbQ with ⟨ab, _, hab⟩
      have hxab := (ratDiv_lt_iff hxQ hbQ haQ h0a he
        (ratMul_comm_rel haQ hbQ hab)).mp heb
      exact mem_positiveMul_of_witness hxQ
        (TA_DEF_00081_mem_rationalSection_iff.mpr ⟨haQ, hap⟩) h0a
        (TA_DEF_00081_mem_rationalSection_iff.mpr ⟨hbQ, hbq⟩) h0b hab hxab
  · intro hx
    rcases TA_DEF_00093_mem_positiveMul_iff.mp hx with ⟨hxQ, a, ha, b, hb, ab, hab, hxab⟩
    rcases TA_DEF_00092_mem_positivePart_iff.mp ha with ⟨ha, _⟩
    rcases TA_DEF_00092_mem_positivePart_iff.mp hb with ⟨hb, h0b⟩
    rcases TA_DEF_00081_mem_rationalSection_iff.mp ha with ⟨haQ, hap⟩
    rcases TA_DEF_00081_mem_rationalSection_iff.mp hb with ⟨hbQ, hbq⟩
    have habpq := positive_product_lt_of_factor_bounds haQ hbQ hp hq
      h0b h0p hap hbq hab hpq
    exact TA_DEF_00081_mem_rationalSection_iff.mpr
      ⟨hxQ, ratLT_of_lt_of_le_local hxQ (ratMul_value_mem hab) hpqQ hxab habpq.1⟩

end TratadoAnalisis.Dedekind.PositiveMultiplication
