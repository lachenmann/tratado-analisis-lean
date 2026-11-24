import TratadoAnalisis.Dedekind.OrderedField
import TratadoAnalisis.Dedekind.EmbeddingTriple

namespace TratadoAnalisis.Dedekind.EmbeddingField
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

open TratadoAnalisis.Dedekind.FieldPredicates
open TratadoAnalisis.Dedekind.Field
open TratadoAnalisis.Dedekind.OrderedField
open TratadoAnalisis.Dedekind.Embedding
open TratadoAnalisis.Dedekind.EmbeddingTriple
open TratadoAnalisis.Dedekind.Nonzero
open TratadoAnalisis.Dedekind.Inverse
open TratadoAnalisis.Dedekind.Division
open TratadoAnalisis.Dedekind.MultiplicativeLaws

theorem rationalAdd_group :
    IsAbelianGroupFoundational (rationalsTA : ZFSet.{u}) ratZero RatAdd := by
  refine ⟨?_, ratZero_mem_rationalsTA, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    rcases ratAdd_exists hx hy with ⟨z, hz, hrel⟩
    exact ⟨z, ⟨hz, hrel⟩, fun w hw => RatAdd_unique hx hy hw.2 hrel⟩
  · intro x y z xy lhs yz rhs hx hy hz hxy hl hyz hr
    exact ratAdd_assoc hx hy hz hxy hl hyz hr
  · intro x y xy yx hx hy hxy hyx
    exact ratAdd_comm hx hy hxy hyx
  · intro x hx
    exact ⟨ratAdd_comm_rel ratZero_mem_rationalsTA hx (zero_add_rel hx), zero_add_rel hx⟩
  · intro x hx
    rcases ratNeg_exists hx with ⟨nx, hnQ, hn⟩
    have h := ratAdd_neg_right_rel hx hn
    exact ⟨nx, hnQ, h, ratAdd_comm_rel hx hnQ h⟩

theorem rationals_field :
    IsFieldFoundational (rationalsTA : ZFSet.{u}) ratZero ratOne RatAdd RatMul := by
  refine ⟨rationalAdd_group, ?_, ratOne_mem_rationalsTA, ?_, ?_, ?_, ?_, TA_PRO_00059_ratZero_ne_one, ?_⟩
  · intro x hx y hy
    rcases ratMul_exists hx hy with ⟨z, hz, hrel⟩
    exact ⟨z, ⟨hz, hrel⟩, fun w hw => RatMul_unique hx hy hw.2 hrel⟩
  · intro x y z xy lhs yz rhs hx hy hz hxy hl hyz hr
    exact ratMul_assoc hx hy hz hxy hl hyz hr
  · intro x y xy yx hx hy hxy hyx
    exact ratMul_comm hx hy hxy hyx
  · intro x hx
    exact ⟨ratMul_comm_rel ratOne_mem_rationalsTA hx (ratMul_one_left_rel hx), ratMul_one_left_rel hx⟩
  · exact ⟨fun _ _ _ _ _ _ _ _ hx hy hz hs hl hxy hxz hr => ratMul_add_left hx hy hz hs hl hxy hxz hr,
      fun _ _ _ _ _ _ _ _ hx hy hz hs hl hxz hyz hr => ratAdd_mul_right hx hy hz hs hl hxz hyz hr⟩
  · intro x hx hx0
    rcases exists_inverse_of_mem_ratNonzeroTA (mem_ratNonzeroTA_iff.mpr ⟨hx, hx0⟩) with ⟨ix, hi, _, hl, hr⟩
    exact ⟨ix, (mem_ratNonzeroTA_iff.mp hi).1, hl, hr⟩

theorem rationals_orderedField :
    IsOrderedFieldFoundational (rationalsTA : ZFSet.{u}) ratZero ratOne RatAdd RatMul RatLE := by
  refine ⟨rationals_field, TA_THM_00029_total_order, ?_, ?_⟩
  · intro x y z xz yz hx hy hz hle h1 h2
    exact ratLE_add_compat hx hy hz hle h1 h2
  · intro x y xy hx hy h0x h0y hm
    exact ratLE_mul_nonnegative_compat ratZero_mem_rationalsTA hx hy h0x h0y (ratMul_zero_left hy) hm

theorem rationalSection_ratLE_iff {p q : ZFSet.{u}}
    (hp : p ∈ rationalsTA) (hq : q ∈ rationalsTA) :
    RatLE p q ↔ DedLE (rationalSection p) (rationalSection q) := by
  constructor
  · intro h
    exact ⟨TA_PRO_00080_rationalSection_mem hp, TA_PRO_00080_rationalSection_mem hq,
      (TA_PRO_00083_ratLE_iff_sections_subset hp hq).mp h⟩
  · intro h
    exact (TA_PRO_00083_ratLE_iff_sections_subset hp hq).mpr h.2.2

/-- Las leyes de secciones racionales, separadas del paquete de cuerpos. -/
theorem TA_COR_00023_section_laws :
    (rationalSection (ratZero : ZFSet.{u}) = dedZero) ∧
    (rationalSection (ratOne : ZFSet.{u}) = dedOne) ∧
    (∀ p q r : ZFSet.{u}, p ∈ rationalsTA → q ∈ rationalsTA → RatAdd p q r →
      rationalSection r = dedAdd (rationalSection p) (rationalSection q)) ∧
    (∀ p q r : ZFSet.{u}, p ∈ rationalsTA → q ∈ rationalsTA → RatMul p q r →
      rationalSection r = dedMul (rationalSection p) (rationalSection q)) ∧
    (∀ p q : ZFSet.{u}, p ∈ rationalsTA → q ∈ rationalsTA →
      (RatLE p q ↔ DedLE (rationalSection p) (rationalSection q))) :=
  ⟨rfl, rfl, fun _ _ _ hp hq hr => TA_PRO_00085_rationalSection_add hp hq hr,
    fun _ _ _ hp hq hr => TA_PRO_00095_rationalSection_mul hp hq hr,
    fun _ _ hp hq => rationalSection_ratLE_iff hp hq⟩

theorem TA_COR_00023_orderedField_embedding (em : ∀ p : Prop, p ∨ ¬p) :
    IsOrderedFieldEmbeddingFoundational (rationalsTA : ZFSet.{u}) dedekindCutsTA
      ratZero ratOne dedZero dedOne RatAdd RatMul CutAdd CutMul RatLE DedLE
      rationalSection dedekindEmbeddingGraph dedekindEmbeddingFunction := by
  refine ⟨rationals_orderedField, TA_THM_00054_dedekind_orderedField em,
    rfl, TA_DEF_00084_embeddingFunction_isTriple, ?_, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · intro x hx
    exact TA_DEF_00084_mem_embeddingGraph_iff.mpr ⟨hx, TA_PRO_00080_rationalSection_mem hx, rfl⟩
  · intro x y hx hy he
    exact TA_COR_00016_rationalSection_injective hx hy he
  · intro x y z hx hy _ hrel
    exact TA_PRO_00085_rationalSection_add hx hy hrel
  · intro x y z hx hy _ hrel
    exact TA_PRO_00095_rationalSection_mul hx hy hrel
  · intro x y hx hy
    exact rationalSection_ratLE_iff hx hy

theorem dedMul_cancel_left (em : ∀ p : Prop, p ∨ ¬p)
    {a b c : ZFSet.{u}} (ha : a ∈ dedekindCutsTA) (hb : b ∈ dedekindCutsTA)
    (hc : c ∈ dedekindCutsTA) (ha0 : a ≠ dedZero) (he : dedMul a b = dedMul a c) : b = c := by
  have hn := TA_DEF_00101_mem_nonzeroCuts_iff.mpr ⟨ha, ha0⟩
  have hi : dedInvValue a ∈ dedekindCutsTA :=
    (TA_DEF_00101_mem_nonzeroCuts_iff.mp (TA_PRO_00100_signedInv_mem em hn)).1
  have law := TA_THM_00046_inverse_law em hn
  calc
    b = dedMul dedOne b := (TA_THM_00044_dedMul_one em hb).2.symm
    _ = dedMul (dedMul (dedInvValue a) a) b := congrArg (fun z => dedMul z b) law.2.symm
    _ = dedMul (dedInvValue a) (dedMul a b) := TA_THM_00051_dedMul_assoc em hi ha hb
    _ = dedMul (dedInvValue a) (dedMul a c) := congrArg (dedMul (dedInvValue a)) he
    _ = dedMul (dedMul (dedInvValue a) a) c := (TA_THM_00051_dedMul_assoc em hi ha hc).symm
    _ = dedMul dedOne c := congrArg (fun z => dedMul z c) law.2
    _ = c := (TA_THM_00044_dedMul_one em hc).2

theorem rationalSection_nonzero {p : ZFSet.{u}} (hp : p ∈ rationalsTA) (hp0 : p ≠ ratZero) :
    rationalSection p ∈ nonzeroCutsTA :=
  TA_DEF_00101_mem_nonzeroCuts_iff.mpr ⟨TA_PRO_00080_rationalSection_mem hp,
    fun he => hp0 (TA_COR_00016_rationalSection_injective hp ratZero_mem_rationalsTA he)⟩

theorem TA_COR_00024_rationalSection_inv (em : ∀ p : Prop, p ∨ ¬p)
    {p pi : ZFSet.{u}} (hp : p ∈ rationalsTA) (hp0 : p ≠ ratZero) (hi : RatInv p pi) :
    rationalSection pi = dedInvValue (rationalSection p) := by
  have hpi := (mem_ratNonzeroTA_iff.mp (funcFoundational_value_mem ratInvGraph_isFunc hi)).1
  have hn := rationalSection_nonzero hp hp0
  have hsp := TA_PRO_00080_rationalSection_mem hp
  have hsi := TA_PRO_00080_rationalSection_mem hpi
  have hdi : dedInvValue (rationalSection p) ∈ dedekindCutsTA :=
    (TA_DEF_00101_mem_nonzeroCuts_iff.mp (TA_PRO_00100_signedInv_mem em hn)).1
  apply dedMul_cancel_left em hsp hsi hdi (TA_DEF_00101_mem_nonzeroCuts_iff.mp hn).2
  exact (TA_PRO_00095_rationalSection_mul hp hpi
    (TA_PRO_00063_inverse_law (mem_ratNonzeroTA_iff.mpr ⟨hp, hp0⟩) hi).1).symm.trans
      (TA_THM_00046_inverse_law em hn).1.symm

theorem rationalSection_div (em : ∀ p : Prop, p ∨ ¬p)
    {p q d : ZFSet.{u}} (hp : p ∈ rationalsTA) (hq : q ∈ rationalsTA)
    (hq0 : q ≠ ratZero) (hd : RatDiv p q d) :
    rationalSection d = dedDiv (rationalSection p) (rationalSection q) := by
  rcases hd with ⟨iq, hi, hm⟩
  have hiQ := (mem_ratNonzeroTA_iff.mp (funcFoundational_value_mem ratInvGraph_isFunc hi)).1
  change rationalSection d = dedMul (rationalSection p) (dedInvValue (rationalSection q))
  rw [← TA_COR_00024_rationalSection_inv em hq hq0 hi]
  exact TA_PRO_00095_rationalSection_mul hp hiQ hm


end TratadoAnalisis.Dedekind.EmbeddingField
