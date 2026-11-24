import TratadoAnalisis.Dedekind.PositiveInverse
import TratadoAnalisis.Dedekind.Boundary

namespace TratadoAnalisis.Dedekind.PositiveInversePrep
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
open TratadoAnalisis.Dedekind.PositiveInverse
open TratadoAnalisis.Dedekind.Boundary

theorem multiply_by_inverse_then_original {a s si asi : ZFSet.{u}}
    (ha : a ∈ rationalsTA) (hs : s ∈ rationalsTA)
    (h0s : RatLT ratZero s) (hi : RatInv s si) (hm : RatMul a si asi) :
    RatMul asi s a := by
  have hsiQ := (mem_ratNonzeroTA_iff.mp (funcFoundational_value_mem ratInvGraph_isFunc hi)).1
  have law := TA_PRO_00063_inverse_law
    (mem_ratNonzeroTA_iff.mpr ⟨hs, fun he => h0s.2 he.symm⟩) hi
  rcases ratMul_exists (ratMul_value_mem hm) hs with ⟨r, _, hr⟩
  have he := ratMul_assoc ha hsiQ hs hm hr law.2
    (ratMul_comm_rel ratOne_mem_rationalsTA ha (ratMul_one_left_rel ha))
  rw [he] at hr
  exact hr

theorem quotient_lt_inverse_of_cross_bound {x a s d si xs : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (ha : a ∈ rationalsTA) (hs : s ∈ rationalsTA)
    (h0a : RatLT ratZero a) (h0s : RatLT ratZero s)
    (hd : RatDiv x a d) (hi : RatInv s si)
    (hxs : RatMul x s xs) (hcross : RatLT xs a) : RatLT d si := by
  have hsiQ := (mem_ratNonzeroTA_iff.mp (funcFoundational_value_mem ratInvGraph_isFunc hi)).1
  rcases ratMul_exists ha hsiQ with ⟨asi, hasiQ, hasi⟩
  have hc := (TA_LEM_00020_clause9_scale_iff hx hasiQ hs h0s hxs
    (multiply_by_inverse_then_original ha hs h0s hi hasi)).mpr hcross
  exact (ratDiv_lt_iff hx hsiQ ha h0a hd (ratMul_comm_rel ha hsiQ hasi)).mpr hc

/-- Aritmética local equivalente a (1-x)(c-h)-xh=(1-x)c-h>0.
Se transporta h<(1-x)c a h<(1-x)s y se cancela h en xs+h<a+h. -/
theorem boundary_cross_bound {x c h a s t tc : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hc : c ∈ rationalsTA) (hh : h ∈ rationalsTA)
    (ha : a ∈ rationalsTA) (hs : s ∈ rationalsTA)
    (h0x : RatLT ratZero x) (hx1 : RatLT x ratOne)
    (h0c : RatLT ratZero c) (hcs : RatLT c s)
    (ht : RatSub ratOne x t) (htc : RatMul t c tc)
    (hhtc : RatLT h tc) (hah : RatAdd a h s) :
    ∃ xs : ZFSet.{u}, RatMul x s xs ∧ RatLT xs a ∧
      RatLT ratZero a ∧ RatLT ratZero s := by
  have htQ : t ∈ rationalsTA := by
    rcases ht with ⟨nx, _, hm⟩
    exact funcFoundational_value_mem ratAddGraph_isFunc hm
  have h0t := ratSub_positive ratOne_mem_rationalsTA hx hx1 ht
  have h0s := ratLT_of_lt_of_le_local ratZero_mem_rationalsTA hc hs h0c hcs.1
  rcases ratMul_exists htQ hs with ⟨ts, htsQ, hts⟩
  have htcts := ratLT_mul_positive_left_local hc hs htQ hcs h0t htc hts
  have hhts := ratLT_of_lt_of_le_local hh (ratMul_value_mem htc) htsQ hhtc htcts.1
  rcases ratMul_exists hx hs with ⟨xs, hxsQ, hxs⟩
  rcases ratAdd_exists htsQ hxsQ with ⟨z, _, hz⟩
  have he : s = z := ratAdd_mul_right htQ hx hs
    (ratSub_add_cancel ratOne_mem_rationalsTA hx ht)
    (ratMul_one_left_rel hs) hts hxs hz
  rw [← he] at hz
  rcases ratAdd_exists hxsQ hh with ⟨w, hwQ, hw⟩
  have hws := ratLT_add_left_local hh htsQ hxsQ hhts hw (ratAdd_comm_rel htsQ hxsQ hz)
  have hxsa := ratLT_add_cancel_right_local hxsQ ha hh hw hah hws
  have h0xs := TA_LEM_00020_clause5_positive_product hx hs hxs h0x h0s
  exact ⟨xs, hxs, hxsa,
    ratLT_of_lt_of_le_local ratZero_mem_rationalsTA hxsQ ha h0xs hxsa.1, h0s⟩

/-- Testigos para la inclusión difícil de TA-THM-00045. -/
theorem positive_inverse_product_witness (em : ∀ p : Prop, p ∨ ¬p)
    {α x : ZFSet.{u}} (hp : IsPositiveCut α)
    (hx : x ∈ rationalsTA) (h0x : RatLT ratZero x) (hx1 : RatLT x ratOne) :
    ∃ a b ab : ZFSet.{u}, a ∈ α ∧ RatLT ratZero a ∧
      b ∈ dedPositiveInv α ∧ RatLT ratZero b ∧ RatMul a b ab ∧ RatLT x ab := by
  have ca := TA_PRO_00079_mem_dedekindCuts_iff.mp hp.1.2.1
  rcases (TA_LEM_00023_zero_mem_iff_positive_member hp.1.2.1).mp
    (TA_LEM_00023_positive_implies_zero_mem em hp.1.2.1 hp) with ⟨c, hc, h0c⟩
  have hcQ := ca.1 hc
  rcases ratSub_exists ratOne_mem_rationalsTA hx with ⟨t, htQ, ht⟩
  have h0t := ratSub_positive ratOne_mem_rationalsTA hx hx1 ht
  rcases ratMul_exists htQ hcQ with ⟨tc, htcQ, htc⟩
  have h0tc := TA_LEM_00020_clause5_positive_product htQ hcQ htc h0t h0c
  rcases TA_THM_00030_rational_density ratZero_mem_rationalsTA htcQ h0tc with ⟨h, hh, h0h, hhtc⟩
  rcases TA_LEM_00022_boundary_approximation em hp.1.2.1 hh h0h with ⟨a, ha, s, hah, ho⟩
  have haQ := ca.1 ha
  have hsQ := funcFoundational_value_mem ratAddGraph_isFunc hah
  have hcs := cut_member_lt_nonmember ca hsQ ho hc
  rcases boundary_cross_bound hx hcQ hh haQ hsQ h0x hx1 h0c hcs ht htc hhtc hah
    with ⟨xs, hxs, hxsa, h0a, h0s⟩
  rcases exists_inverse_of_mem_ratNonzeroTA
    (mem_ratNonzeroTA_iff.mpr ⟨hsQ, fun he => h0s.2 he.symm⟩) with ⟨si, hsi, hi, _, _⟩
  have hsiQ := (mem_ratNonzeroTA_iff.mp hsi).1
  rcases ratDiv_exists hx (mem_ratNonzeroTA_iff.mpr ⟨haQ, fun he => h0a.2 he.symm⟩)
    with ⟨d, hdQ, hd⟩
  have hdsi := quotient_lt_inverse_of_cross_bound hx haQ hsQ h0a h0s hd hi hxs hxsa
  have h0d := ratDiv_positive hx haQ h0x h0a hd
  rcases TA_THM_00030_rational_density hdQ hsiQ hdsi with ⟨b, hbQ, hdb, hbsi⟩
  have h0b := ratLT_of_lt_of_le_local ratZero_mem_rationalsTA hdQ hbQ h0d hdb.1
  rcases ratMul_exists haQ hbQ with ⟨ab, _, hab⟩
  have hxab := (ratDiv_lt_iff hx hbQ haQ h0a hd (ratMul_comm_rel haQ hbQ hab)).mp hdb
  exact ⟨a, b, ab, ha, h0a, TA_DEF_00099_mem_positiveInv_iff.mpr
    ⟨hbQ, Or.inr ⟨s, hsQ, h0s, ho, si, hi, hbsi⟩⟩, h0b, hab, hxab⟩


end TratadoAnalisis.Dedekind.PositiveInversePrep
