import TratadoAnalisis.Dedekind.Nonzero

namespace TratadoAnalisis.Dedekind.PositiveProductLaws
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

/-- Conmutatividad del constructor: testigos racionales intercambiados. -/
theorem positiveMul_comm_of_subsets {α β : ZFSet.{u}}
    (hα : α ⊆ rationalsTA) (hβ : β ⊆ rationalsTA) :
    dedPositiveMul α β = dedPositiveMul β α := by
  apply ZFSet.ext
  intro x
  constructor <;> intro hx
  · rcases TA_DEF_00093_mem_positiveMul_iff.mp hx with ⟨hxQ, a, ha, b, hb, ab, hab, hxab⟩
    rcases TA_DEF_00092_mem_positivePart_iff.mp ha with ⟨ha, h0a⟩
    rcases TA_DEF_00092_mem_positivePart_iff.mp hb with ⟨hb, h0b⟩
    exact mem_positiveMul_of_witness hxQ hb h0b ha h0a (ratMul_comm_rel (hα ha) (hβ hb) hab) hxab
  · rcases TA_DEF_00093_mem_positiveMul_iff.mp hx with ⟨hxQ, b, hb, a, ha, ab, hba, hxab⟩
    rcases TA_DEF_00092_mem_positivePart_iff.mp ha with ⟨ha, h0a⟩
    rcases TA_DEF_00092_mem_positivePart_iff.mp hb with ⟨hb, h0b⟩
    exact mem_positiveMul_of_witness hxQ ha h0a hb h0b (ratMul_comm_rel (hβ hb) (hα ha) hba) hxab

/-- Encogimiento de un factor positivo por densidad, con tricotomía racional. -/
theorem positive_factor_below {x a b ab : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (ha : a ∈ rationalsTA) (hb : b ∈ rationalsTA)
    (h0a : RatLT ratZero a) (h0b : RatLT ratZero b)
    (hab : RatMul a b ab) (hxab : RatLT x ab) :
    ∃ v av : ZFSet.{u}, v ∈ rationalsTA ∧ RatLT ratZero v ∧
      RatLT v b ∧ RatMul a v av ∧ RatLT x av := by
  have nonpos : RatLE x ratZero →
      ∃ v av : ZFSet.{u}, v ∈ rationalsTA ∧ RatLT ratZero v ∧
        RatLT v b ∧ RatMul a v av ∧ RatLT x av := by
    intro hx0
    rcases TA_THM_00030_rational_density ratZero_mem_rationalsTA hb h0b with ⟨v, hv, h0v, hvb⟩
    rcases ratMul_exists ha hv with ⟨av, havQ, hav⟩
    exact ⟨v, av, hv, h0v, hvb, hav,
      ratLT_of_le_of_lt_local hx ratZero_mem_rationalsTA havQ hx0
        (TA_LEM_00020_clause5_positive_product ha hv hav h0a h0v)⟩
  rcases TA_PRO_00172_rational_trichotomy hx ratZero_mem_rationalsTA with hn | he | hp
  · exact nonpos hn.1
  · apply nonpos
    rw [he]
    exact ratLE_refl ratZero_mem_rationalsTA
  · rcases ratDiv_exists hx (mem_ratNonzeroTA_iff.mpr ⟨ha, fun he => h0a.2 he.symm⟩) with ⟨d, hd, hdiv⟩
    have hdb := (ratDiv_lt_iff hx hb ha h0a hdiv (ratMul_comm_rel ha hb hab)).mpr hxab
    rcases TA_THM_00030_rational_density hd hb hdb with ⟨v, hv, hdv, hvb⟩
    have h0v := ratLT_of_lt_of_le_local ratZero_mem_rationalsTA hd hv
      (ratDiv_positive hx ha hp h0a hdiv) hdv.1
    rcases ratMul_exists ha hv with ⟨av, _, hav⟩
    exact ⟨v, av, hv, h0v, hvb, hav,
      (ratDiv_lt_iff hx hv ha h0a hdiv (ratMul_comm_rel ha hv hav)).mp hdv⟩

theorem positiveMul_assoc_subset {α β γ : ZFSet.{u}}
    (hα : α ⊆ rationalsTA) (hβ : β ⊆ rationalsTA) (hγ : γ ⊆ rationalsTA) :
    dedPositiveMul (dedPositiveMul α β) γ ⊆ dedPositiveMul α (dedPositiveMul β γ) := by
  intro x hx
  rcases TA_DEF_00093_mem_positiveMul_iff.mp hx with ⟨hxQ, u0, hu, c, hc, uc, huc, hxuc⟩
  rcases TA_DEF_00092_mem_positivePart_iff.mp hu with ⟨hu, h0u⟩
  rcases TA_DEF_00092_mem_positivePart_iff.mp hc with ⟨hc, h0c⟩
  rcases TA_DEF_00093_mem_positiveMul_iff.mp hu with ⟨huQ, a, ha, b, hb, ab, hab, huab⟩
  rcases TA_DEF_00092_mem_positivePart_iff.mp ha with ⟨ha, h0a⟩
  rcases TA_DEF_00092_mem_positivePart_iff.mp hb with ⟨hb, h0b⟩
  rcases ratMul_exists (ratMul_value_mem hab) (hγ hc) with ⟨abc, habcQ, habc⟩
  have hucabc := ratLT_mul_positive_right huQ (ratMul_value_mem hab) (hγ hc) huab h0c huc habc
  have hxabc := ratLT_of_lt_of_le_local hxQ (ratMul_value_mem huc) habcQ hxuc hucabc.1
  rcases ratMul_exists (hβ hb) (hγ hc) with ⟨bc, hbcQ, hbc⟩
  rcases ratMul_exists (hα ha) hbcQ with ⟨abc', _, habc'⟩
  have he := ratMul_assoc (hα ha) (hβ hb) (hγ hc) hab habc hbc habc'
  rw [he] at hxabc
  have h0bc := TA_LEM_00020_clause5_positive_product (hβ hb) (hγ hc) hbc h0b h0c
  rcases positive_factor_below hxQ (hα ha) hbcQ h0a h0bc habc' hxabc with ⟨v, av, hv, h0v, hvbc, hav, hxav⟩
  exact mem_positiveMul_of_witness hxQ ha h0a
    (mem_positiveMul_of_witness hv hb h0b hc h0c hbc hvbc) h0v hav hxav

theorem positiveMul_assoc_of_subsets {α β γ : ZFSet.{u}}
    (hα : α ⊆ rationalsTA) (hβ : β ⊆ rationalsTA) (hγ : γ ⊆ rationalsTA) :
    dedPositiveMul (dedPositiveMul α β) γ = dedPositiveMul α (dedPositiveMul β γ) := by
  apply TA_THM_00001_zfset_eq_iff_subset.mpr
  refine ⟨positiveMul_assoc_subset hα hβ hγ, ?_⟩
  intro x hx
  rw [positiveMul_comm_of_subsets hα (dedPositiveMul_subset_rationals β γ)] at hx
  have h1 := positiveMul_assoc_subset hβ hγ hα hx
  rw [positiveMul_comm_of_subsets hβ (dedPositiveMul_subset_rationals γ α)] at h1
  have h2 := positiveMul_assoc_subset hγ hα hβ h1
  rw [positiveMul_comm_of_subsets hγ (dedPositiveMul_subset_rationals α β)] at h2
  exact h2

theorem TA_THM_00047_positiveMul_comm {α β : ZFSet.{u}}
    (hα : IsPositiveCut α) (hβ : IsPositiveCut β) :
    dedPositiveMul α β = dedPositiveMul β α :=
  positiveMul_comm_of_subsets (TA_PRO_00079_mem_dedekindCuts_iff.mp hα.1.2.1).1
    (TA_PRO_00079_mem_dedekindCuts_iff.mp hβ.1.2.1).1

theorem TA_THM_00048_positiveMul_assoc {α β γ : ZFSet.{u}}
    (hα : IsPositiveCut α) (hβ : IsPositiveCut β) (hγ : IsPositiveCut γ) :
    dedPositiveMul (dedPositiveMul α β) γ = dedPositiveMul α (dedPositiveMul β γ) :=
  positiveMul_assoc_of_subsets (TA_PRO_00079_mem_dedekindCuts_iff.mp hα.1.2.1).1
    (TA_PRO_00079_mem_dedekindCuts_iff.mp hβ.1.2.1).1
    (TA_PRO_00079_mem_dedekindCuts_iff.mp hγ.1.2.1).1


end TratadoAnalisis.Dedekind.PositiveProductLaws
