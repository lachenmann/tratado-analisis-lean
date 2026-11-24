import TratadoAnalisis.Dedekind.Nonzero

namespace TratadoAnalisis.Dedekind.PositiveInverse
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

/-- TA-DEF-00099: unión proposicional dentro de una única Separación. -/
def dedPositiveInv (α : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun q => RatLE q ratZero ∨
    ∃ s : ZFSet.{u}, s ∈ rationalsTA ∧ RatLT ratZero s ∧ s ∉ α ∧
      ∃ si : ZFSet.{u}, RatInv s si ∧ RatLT q si) rationalsTA

theorem TA_DEF_00099_mem_positiveInv_iff {α q : ZFSet.{u}} :
    q ∈ dedPositiveInv α ↔ q ∈ rationalsTA ∧
      (RatLE q ratZero ∨ ∃ s : ZFSet.{u}, s ∈ rationalsTA ∧
        RatLT ratZero s ∧ s ∉ α ∧
        ∃ si : ZFSet.{u}, RatInv s si ∧ RatLT q si) := ZFSet.mem_sep

theorem positiveInv_subset_rationals (α : ZFSet.{u}) :
    dedPositiveInv α ⊆ rationalsTA :=
  fun _ h => (TA_DEF_00099_mem_positiveInv_iff.mp h).1

theorem zero_mem_positiveInv (α : ZFSet.{u}) :
    (ratZero : ZFSet.{u}) ∈ dedPositiveInv α :=
  TA_DEF_00099_mem_positiveInv_iff.mpr
    ⟨ratZero_mem_rationalsTA, Or.inl (ratLE_refl ratZero_mem_rationalsTA)⟩

theorem positive_exterior_inverse (em : ∀ p : Prop, p ∨ ¬p)
    {α : ZFSet.{u}} (hp : IsPositiveCut α) :
    ∃ s si : ZFSet.{u}, s ∈ rationalsTA ∧ RatLT ratZero s ∧
      s ∉ α ∧ si ∈ rationalsTA ∧ RatInv s si ∧ RatLT ratZero si := by
  have ca := TA_PRO_00079_mem_dedekindCuts_iff.mp hp.1.2.1
  have h0 := TA_LEM_00023_positive_implies_zero_mem em hp.1.2.1 hp
  rcases cut_exterior_inhabited em ca with ⟨s, hs, ho⟩
  have h0s := cut_member_lt_nonmember ca hs ho h0
  rcases exists_inverse_of_mem_ratNonzeroTA
    (mem_ratNonzeroTA_iff.mpr ⟨hs, fun he => h0s.2 he.symm⟩) with ⟨si, hsi, hi, _, _⟩
  exact ⟨s, si, hs, h0s, ho, (mem_ratNonzeroTA_iff.mp hsi).1, hi,
    TA_LEM_00020_clause6_positive_inverse hs hi h0s⟩

theorem TA_PRO_00098_positiveInv_mem (em : ∀ p : Prop, p ∨ ¬p)
    {α : ZFSet.{u}} (hα : α ∈ positiveCutsTA) :
    dedPositiveInv α ∈ positiveCutsTA := by
  have hp := TA_DEF_00091_mem_positiveCuts_iff.mp hα
  have hαD := hp.1.2.1
  have ca := TA_PRO_00079_mem_dedekindCuts_iff.mp hαD
  have h0 := TA_LEM_00023_positive_implies_zero_mem em hαD hp
  rcases (TA_LEM_00023_zero_mem_iff_positive_member hαD).mp h0 with ⟨a, ha, h0a⟩
  have haQ := ca.1 ha
  rcases exists_inverse_of_mem_ratNonzeroTA
    (mem_ratNonzeroTA_iff.mpr ⟨haQ, fun he => h0a.2 he.symm⟩) with ⟨ai, hai, hi, _, _⟩
  have haiQ := (mem_ratNonzeroTA_iff.mp hai).1
  have h0ai := TA_LEM_00020_clause6_positive_inverse haQ hi h0a
  rcases positive_exterior_inverse em hp with ⟨s, si, hs, h0s, ho, hsiQ, hsi, h0si⟩
  have cut : IsDedekindCut (dedPositiveInv α) := by
    refine ⟨positiveInv_subset_rationals α, ?_, ?_, ?_, ?_⟩
    · intro he
      exact ZFSet.notMem_empty ratZero (he ▸ zero_mem_positiveInv α)
    · intro he
      have hmem : ai ∈ dedPositiveInv α := he.symm ▸ haiQ
      rcases (TA_DEF_00099_mem_positiveInv_iff.mp hmem).2 with hle | ⟨t, ht, h0t, hto, ti, hti, hlt⟩
      · exact h0ai.2 (ratLE_antisymm ratZero_mem_rationalsTA haiQ h0ai.1 hle)
      · have hta := (positive_inv_lt_iff ht haQ h0t h0a hti hi).mp hlt
        exact hto (ca.2.2.2.1 a ha t ht hta)
    · intro r hr q hq hqr
      rcases TA_DEF_00099_mem_positiveInv_iff.mp hr with ⟨hrQ, hr⟩
      apply TA_DEF_00099_mem_positiveInv_iff.mpr
      refine ⟨hq, ?_⟩
      rcases hr with hr0 | ⟨t, ht, h0t, hto, ti, hti, hrti⟩
      · exact Or.inl (ratLE_trans hq hrQ ratZero_mem_rationalsTA hqr.1 hr0)
      · exact Or.inr ⟨t, ht, h0t, hto, ti, hti,
          ratLT_of_lt_of_le_local hq hrQ
            (mem_ratNonzeroTA_iff.mp (funcFoundational_value_mem ratInvGraph_isFunc hti)).1
            hqr hrti.1⟩
    · intro q hq
      rcases TA_DEF_00099_mem_positiveInv_iff.mp hq with ⟨hqQ, hq⟩
      have above : ∀ t ti : ZFSet.{u}, t ∈ rationalsTA → RatLT ratZero t →
          t ∉ α → RatInv t ti → RatLT q ti →
          ∃ r : ZFSet.{u}, r ∈ dedPositiveInv α ∧ RatLT q r := by
        intro t ti ht h0t hto hti hqti
        have htiQ := (mem_ratNonzeroTA_iff.mp (funcFoundational_value_mem ratInvGraph_isFunc hti)).1
        rcases TA_THM_00030_rational_density hqQ htiQ hqti with ⟨r, hrQ, hqr, hrti⟩
        exact ⟨r, TA_DEF_00099_mem_positiveInv_iff.mpr
          ⟨hrQ, Or.inr ⟨t, ht, h0t, hto, ti, hti, hrti⟩⟩, hqr⟩
      rcases hq with hq0 | ⟨t, ht, h0t, hto, ti, hti, hqti⟩
      · rcases TA_PRO_00172_rational_trichotomy hqQ ratZero_mem_rationalsTA with hlt | he | hgt
        · exact ⟨ratZero, zero_mem_positiveInv α, hlt⟩
        · subst q
          exact above s si hs h0s ho hsi h0si
        · exact (hgt.2 (ratLE_antisymm ratZero_mem_rationalsTA hqQ hgt.1 hq0)).elim
      · exact above t ti ht h0t hto hti hqti
  exact TA_DEF_00091_mem_positiveCuts_iff.mpr
    (TA_LEM_00023_zero_mem_implies_positive
      (TA_PRO_00079_mem_dedekindCuts_iff.mpr cut) (zero_mem_positiveInv α))

theorem TA_PRO_00099_rationalSection_positiveInv {p pi : ZFSet.{u}}
    (hp : p ∈ rationalsTA) (h0p : RatLT ratZero p) (hi : RatInv p pi) :
    dedPositiveInv (rationalSection p) = rationalSection pi := by
  have hpiQ := (mem_ratNonzeroTA_iff.mp (funcFoundational_value_mem ratInvGraph_isFunc hi)).1
  have h0pi := TA_LEM_00020_clause6_positive_inverse hp hi h0p
  apply ZFSet.ext
  intro q
  constructor
  · intro hq
    rcases TA_DEF_00099_mem_positiveInv_iff.mp hq with ⟨hqQ, hq⟩
    apply TA_DEF_00081_mem_rationalSection_iff.mpr
    refine ⟨hqQ, ?_⟩
    rcases hq with hq0 | ⟨s, hs, h0s, ho, si, hsi, hqsi⟩
    · exact ratLT_of_le_of_lt_local hqQ ratZero_mem_rationalsTA hpiQ hq0 h0pi
    · have hps : RatLE p s := by
        rcases TA_PRO_00172_rational_trichotomy hp hs with h | he | h
        · exact h.1
        · rw [he]; exact ratLE_refl hs
        · exact (ho (TA_DEF_00081_mem_rationalSection_iff.mpr ⟨hs, h⟩)).elim
      have hsiQ := (mem_ratNonzeroTA_iff.mp (funcFoundational_value_mem ratInvGraph_isFunc hsi)).1
      exact ratLT_of_lt_of_le_local hqQ hsiQ hpiQ hqsi
        ((positive_inv_le_iff hp hs h0p h0s hi hsi).mpr hps)
  · intro hq
    rcases TA_DEF_00081_mem_rationalSection_iff.mp hq with ⟨hqQ, hqpi⟩
    exact TA_DEF_00099_mem_positiveInv_iff.mpr
      ⟨hqQ, Or.inr ⟨p, hp, h0p, fun h =>
        (TA_DEF_00081_mem_rationalSection_iff.mp h).2.2 rfl, pi, hi, hqpi⟩⟩

def positiveInvGraph : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ α β : ZFSet.{u},
    z = ZFSet.pair α β ∧ β = dedPositiveInv α)
    (cartesianProductFoundational positiveCutsTA positiveCutsTA)

theorem mem_positiveInvGraph_iff {α β : ZFSet.{u}} :
    ZFSet.pair α β ∈ positiveInvGraph ↔
      α ∈ positiveCutsTA ∧ β ∈ positiveCutsTA ∧ β = dedPositiveInv α := by
  constructor
  · intro h
    rcases ZFSet.mem_sep.mp h with ⟨hp, a, b, he, hb⟩
    rcases ZFSet.pair_injective he with ⟨rfl, rfl⟩
    exact ⟨(mem_cartesianProductFoundational.mp hp).1,
      (mem_cartesianProductFoundational.mp hp).2, hb⟩
  · rintro ⟨ha, hb, he⟩
    exact ZFSet.mem_sep.mpr
      ⟨mem_cartesianProductFoundational.mpr ⟨ha, hb⟩, α, β, rfl, he⟩

theorem TA_DEF_00100_positiveInvGraph_isFunc (em : ∀ p : Prop, p ∨ ¬p) :
    IsFuncFoundational (positiveCutsTA : ZFSet.{u}) positiveCutsTA positiveInvGraph := by
  constructor
  · intro z hz
    rcases (ZFSet.mem_sep.mp hz).2 with ⟨a, b, he, _⟩
    rw [he] at hz
    rcases mem_positiveInvGraph_iff.mp hz with ⟨ha, hb, _⟩
    exact ⟨a, ha, b, hb, he⟩
  · intro a ha
    have hc := TA_PRO_00098_positiveInv_mem em ha
    refine ⟨dedPositiveInv a, ⟨hc, mem_positiveInvGraph_iff.mpr ⟨ha, hc, rfl⟩⟩, ?_⟩
    intro b hb
    exact (mem_positiveInvGraph_iff.mp hb.2).2.2

def positiveInvFunction : ZFSet.{u} := functionTriple positiveCutsTA positiveCutsTA positiveInvGraph

theorem TA_DEF_00100_positiveInvFunction_isTriple (em : ∀ p : Prop, p ∨ ¬p) :
    IsFunctionTriple (positiveCutsTA : ZFSet.{u}) positiveCutsTA positiveInvFunction :=
  TA_DEF_00018_functionTriple_iff.mpr (TA_DEF_00100_positiveInvGraph_isFunc em)


end TratadoAnalisis.Dedekind.PositiveInverse
