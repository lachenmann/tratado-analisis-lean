import TratadoAnalisis.Dedekind.PositiveInversePrep

namespace TratadoAnalisis.Dedekind.PositiveInverseLaw
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
open TratadoAnalisis.Dedekind.PositiveInversePrep

theorem positive_inverse_product_lt_one {α a b ab : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) (ha : a ∈ α) (h0a : RatLT ratZero a)
    (hb : b ∈ dedPositiveInv α) (h0b : RatLT ratZero b)
    (hab : RatMul a b ab) : RatLT ab ratOne := by
  have ca := TA_PRO_00079_mem_dedekindCuts_iff.mp hα
  have haQ := ca.1 ha
  rcases TA_DEF_00099_mem_positiveInv_iff.mp hb with ⟨hbQ, hb⟩
  rcases hb with hb0 | ⟨s, hsQ, h0s, ho, si, hi, hbsi⟩
  · exact (h0b.2 (ratLE_antisymm ratZero_mem_rationalsTA hbQ h0b.1 hb0)).elim
  · have hsiQ := (mem_ratNonzeroTA_iff.mp (funcFoundational_value_mem ratInvGraph_isFunc hi)).1
    have h0si := TA_LEM_00020_clause6_positive_inverse hsQ hi h0s
    have has := cut_member_lt_nonmember ca hsQ ho ha
    rcases ratMul_exists haQ hsiQ with ⟨asi, hasiQ, hasi⟩
    have habasi := ratLT_mul_positive_left_local hbQ hsiQ haQ hbsi h0a hab hasi
    have hssi := (TA_PRO_00063_inverse_law
      (mem_ratNonzeroTA_iff.mpr ⟨hsQ, fun he => h0s.2 he.symm⟩) hi).1
    have hasi1 := ratLT_mul_positive_right haQ hsQ hsiQ has h0si hasi hssi
    exact ratLT_of_lt_of_le_local (ratMul_value_mem hab) hasiQ
      ratOne_mem_rationalsTA habasi hasi1.1

theorem inverse_product_witness (em : ∀ p : Prop, p ∨ ¬p)
    {α x : ZFSet.{u}} (hp : IsPositiveCut α)
    (hx : x ∈ rationalsTA) (hx1 : RatLT x ratOne) :
    ∃ a b ab : ZFSet.{u}, a ∈ α ∧ RatLT ratZero a ∧
      b ∈ dedPositiveInv α ∧ RatLT ratZero b ∧ RatMul a b ab ∧ RatLT x ab := by
  have nonpos : RatLE x ratZero →
      ∃ a b ab : ZFSet.{u}, a ∈ α ∧ RatLT ratZero a ∧
        b ∈ dedPositiveInv α ∧ RatLT ratZero b ∧ RatMul a b ab ∧ RatLT x ab := by
    intro hx0
    have hαD := hp.1.2.1
    rcases (TA_LEM_00023_zero_mem_iff_positive_member hαD).mp
      (TA_LEM_00023_positive_implies_zero_mem em hαD hp) with ⟨a, ha, h0a⟩
    have hiD := (TA_DEF_00091_mem_positiveCuts_iff.mp
      (TA_PRO_00098_positiveInv_mem em (TA_DEF_00091_mem_positiveCuts_iff.mpr hp))).1.2.1
    rcases (TA_LEM_00023_zero_mem_iff_positive_member hiD).mp
      (zero_mem_positiveInv α) with ⟨b, hb, h0b⟩
    have haQ := (TA_PRO_00079_mem_dedekindCuts_iff.mp hαD).1 ha
    have hbQ := positiveInv_subset_rationals α hb
    rcases ratMul_exists haQ hbQ with ⟨ab, habQ, hab⟩
    have h0ab := TA_LEM_00020_clause5_positive_product haQ hbQ hab h0a h0b
    exact ⟨a, b, ab, ha, h0a, hb, h0b, hab,
      ratLT_of_le_of_lt_local hx ratZero_mem_rationalsTA habQ hx0 h0ab⟩
  rcases TA_PRO_00172_rational_trichotomy hx ratZero_mem_rationalsTA with hn | he | hp0
  · exact nonpos hn.1
  · apply nonpos
    rw [he]
    exact ratLE_refl ratZero_mem_rationalsTA
  · exact positive_inverse_product_witness em hp hx hp0 hx1

/-- TA-THM-00045: ambas igualdades por testigos, sin conmutatividad de cortaduras. -/
theorem TA_THM_00045_positive_inverse_law (em : ∀ p : Prop, p ∨ ¬p)
    {α : ZFSet.{u}} (hp : IsPositiveCut α) :
    dedPositiveMul α (dedPositiveInv α) = dedOne ∧
      dedPositiveMul (dedPositiveInv α) α = dedOne := by
  have hαD := hp.1.2.1
  have ca := TA_PRO_00079_mem_dedekindCuts_iff.mp hαD
  constructor
  · apply ZFSet.ext
    intro x
    constructor
    · intro hx
      rcases TA_DEF_00093_mem_positiveMul_iff.mp hx with ⟨hxQ, a, ha, b, hb, ab, hab, hxab⟩
      rcases TA_DEF_00092_mem_positivePart_iff.mp ha with ⟨ha, h0a⟩
      rcases TA_DEF_00092_mem_positivePart_iff.mp hb with ⟨hb, h0b⟩
      exact TA_DEF_00081_mem_rationalSection_iff.mpr ⟨hxQ,
        ratLT_of_lt_of_le_local hxQ (ratMul_value_mem hab) ratOne_mem_rationalsTA
          hxab (positive_inverse_product_lt_one hαD ha h0a hb h0b hab).1⟩
    · intro hx
      rcases TA_DEF_00081_mem_rationalSection_iff.mp hx with ⟨hxQ, hx1⟩
      rcases inverse_product_witness em hp hxQ hx1 with ⟨a, b, ab, ha, h0a, hb, h0b, hab, hxab⟩
      exact mem_positiveMul_of_witness hxQ ha h0a hb h0b hab hxab
  · apply ZFSet.ext
    intro x
    constructor
    · intro hx
      rcases TA_DEF_00093_mem_positiveMul_iff.mp hx with ⟨hxQ, b, hb, a, ha, ab, hba, hxab⟩
      rcases TA_DEF_00092_mem_positivePart_iff.mp ha with ⟨ha, h0a⟩
      rcases TA_DEF_00092_mem_positivePart_iff.mp hb with ⟨hb, h0b⟩
      have hab := ratMul_comm_rel (positiveInv_subset_rationals α hb) (ca.1 ha) hba
      exact TA_DEF_00081_mem_rationalSection_iff.mpr ⟨hxQ,
        ratLT_of_lt_of_le_local hxQ (ratMul_value_mem hba) ratOne_mem_rationalsTA
          hxab (positive_inverse_product_lt_one hαD ha h0a hb h0b hab).1⟩
    · intro hx
      rcases TA_DEF_00081_mem_rationalSection_iff.mp hx with ⟨hxQ, hx1⟩
      rcases inverse_product_witness em hp hxQ hx1 with ⟨a, b, ab, ha, h0a, hb, h0b, hab, hxab⟩
      exact mem_positiveMul_of_witness hxQ hb h0b ha h0a
        (ratMul_comm_rel (ca.1 ha) (positiveInv_subset_rationals α hb) hab) hxab


end TratadoAnalisis.Dedekind.PositiveInverseLaw
