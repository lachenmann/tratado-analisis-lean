import TratadoAnalisis.Rationals.PositiveDenominator

namespace TratadoAnalisis.Rationals.OrderWellDefined

open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Integers.Construction
open TratadoAnalisis.Integers.Operations
open TratadoAnalisis.Integers.Multiplication
open TratadoAnalisis.Integers.Algebra
open TratadoAnalisis.Integers.Domain
open TratadoAnalisis.Integers.Order
open TratadoAnalisis.Rationals.IntegerPrep
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.OrderPrep

/-!
# TA-LEAN-0003 — D1b

Independencia de la comparación cruzada respecto de representantes con
denominadores positivos.

No se define todavía la comparación racional ni su conjunto relacional.
-/

theorem mem_intNonzeroTA_of_positive
    {x : ZFSet}
    (hx : x ∈ integersTA)
    (hxPos : IntLT intZero x) :
    x ∈ intNonzeroTA := by
  apply mem_intNonzeroTA_iff.mpr
  refine ⟨hx, ?_⟩
  intro hxZero
  exact hxPos.2 hxZero.symm

theorem cross_comparison_forward
    {a b a' b' c d c' d' ad bc a'd' b'c' : ZFSet}
    (ha : a ∈ integersTA)
    (hb : b ∈ integersTA)
    (ha' : a' ∈ integersTA)
    (hb' : b' ∈ integersTA)
    (hc : c ∈ integersTA)
    (hd : d ∈ integersTA)
    (hc' : c' ∈ integersTA)
    (hd' : d' ∈ integersTA)
    (hbPos : IntLT intZero b)
    (hb'Pos : IntLT intZero b')
    (hdPos : IntLT intZero d)
    (hd'Pos : IntLT intZero d')
    (hab :
      ratClass (ZFSet.pair a b) =
        ratClass (ZFSet.pair a' b'))
    (hcd :
      ratClass (ZFSet.pair c d) =
        ratClass (ZFSet.pair c' d'))
    (had : IntMul a d ad)
    (hbc : IntMul b c bc)
    (ha'd' : IntMul a' d' a'd')
    (hb'c' : IntMul b' c' b'c')
    (hLE : IntLE ad bc) :
    IntLE a'd' b'c' := by
  have hbNZ := mem_intNonzeroTA_of_positive hb hbPos
  have hb'NZ := mem_intNonzeroTA_of_positive hb' hb'Pos
  have hdNZ := mem_intNonzeroTA_of_positive hd hdPos
  have hd'NZ := mem_intNonzeroTA_of_positive hd' hd'Pos

  rcases (TA_PRO_00053_ratClass_pairs_eq_iff
      ha hbNZ ha' hb'NZ).mp hab with
    ⟨ab', ba', hab', hba', hab'Eq⟩
  rcases (TA_PRO_00053_ratClass_pairs_eq_iff
      hc hdNZ hc' hd'NZ).mp hcd with
    ⟨cd', dc', hcd', hdc', hcd'Eq⟩

  have hab'I := funcFoundational_value_mem intMulGraph_isFunc hab'
  have hcd'I := funcFoundational_value_mem intMulGraph_isFunc hcd'

  have hadI := funcFoundational_value_mem intMulGraph_isFunc had
  have hbcI := funcFoundational_value_mem intMulGraph_isFunc hbc
  have ha'd'I := funcFoundational_value_mem intMulGraph_isFunc ha'd'
  have hb'c'I := funcFoundational_value_mem intMulGraph_isFunc hb'c'

  rcases intMul_exists_local hb' hd' with
    ⟨b'd', hb'd'I, hb'd'Mul⟩
  have hb'd'Pos : IntLT intZero b'd' :=
    TA_LEM_00012_positive_mul hb' hd' hb'Pos hd'Pos hb'd'Mul

  rcases intMul_exists_local hadI hb'd'I with
    ⟨scaledLeft, _hscaledLeftI, hScaledLeft⟩
  rcases intMul_exists_local hbcI hb'd'I with
    ⟨scaledRight, _hscaledRightI, hScaledRight⟩
  have hScaledLE : IntLE scaledLeft scaledRight :=
    (TA_LEM_00011_intLE_mul_positive_iff
      hadI hbcI hb'd'I hb'd'Pos
      hScaledLeft hScaledRight).mp hLE

  rcases intMul_exists_local hd hd' with
    ⟨dd', hdd'I, hdd'⟩
  rcases intMul_exists_local hab'I hdd'I with
    ⟨left₁, _hleft₁I, hLeft₁⟩
  have hScaledLeftEqLeft₁ : scaledLeft = left₁ :=
    intPairProducts_exchange_middle
      ha hd hb' hd'
      had hb'd'Mul hab' hdd'
      hScaledLeft hLeft₁

  have hLeft₁' : IntMul ba' dd' left₁ := by
    rw [← hab'Eq]
    exact hLeft₁

  rcases intMul_exists_local hb hd with
    ⟨bd, hbdI, hbd⟩
  have hbdPos : IntLT intZero bd :=
    TA_LEM_00012_positive_mul hb hd hbPos hdPos hbd
  rcases intMul_exists_local hbdI ha'd'I with
    ⟨left₂, _hleft₂I, hLeft₂⟩
  have hLeft₁EqLeft₂ : left₁ = left₂ :=
    intPairProducts_exchange_middle
      hb ha' hd hd'
      hba' hdd' hbd ha'd'
      hLeft₁' hLeft₂

  rcases intMul_exists_local hb hb' with
    ⟨bb', hbb'I, hbb'⟩
  rcases intMul_exists_local hbb'I hcd'I with
    ⟨right₁, _hright₁I, hRight₁⟩
  have hScaledRightEqRight₁ : scaledRight = right₁ :=
    intPairProducts_exchange_middle
      hb hc hb' hd'
      hbc hb'd'Mul hbb' hcd'
      hScaledRight hRight₁

  have hRight₁' : IntMul bb' dc' right₁ := by
    rw [← hcd'Eq]
    exact hRight₁

  rcases intMul_exists_local hbdI hb'c'I with
    ⟨right₂, _hright₂I, hRight₂⟩
  have hRight₁EqRight₂ : right₁ = right₂ :=
    intPairProducts_exchange_middle
      hb hb' hd hc'
      hbb' hdc' hbd hb'c'
      hRight₁' hRight₂

  have hCoreLE : IntLE left₂ right₂ := by
    rw [hScaledLeftEqLeft₁, hLeft₁EqLeft₂,
      hScaledRightEqRight₁, hRight₁EqRight₂] at hScaledLE
    exact hScaledLE

  rcases intMul_exists_local ha'd'I hbdI with
    ⟨left₃, _hleft₃I, hLeft₃⟩
  rcases intMul_exists_local hb'c'I hbdI with
    ⟨right₃, _hright₃I, hRight₃⟩
  have hLeft₂EqLeft₃ : left₂ = left₃ :=
    intMul_comm hbdI ha'd'I hLeft₂ hLeft₃
  have hRight₂EqRight₃ : right₂ = right₃ :=
    intMul_comm hbdI hb'c'I hRight₂ hRight₃

  have hCancelable : IntLE left₃ right₃ := by
    rw [← hLeft₂EqLeft₃, ← hRight₂EqRight₃]
    exact hCoreLE

  exact (TA_LEM_00011_intLE_mul_positive_iff
    ha'd'I hb'c'I hbdI hbdPos hLeft₃ hRight₃).mpr hCancelable

theorem TA_LEM_00014_cross_comparison_well_defined
    {a b a' b' c d c' d' ad bc a'd' b'c' : ZFSet}
    (ha : a ∈ integersTA)
    (hb : b ∈ integersTA)
    (ha' : a' ∈ integersTA)
    (hb' : b' ∈ integersTA)
    (hc : c ∈ integersTA)
    (hd : d ∈ integersTA)
    (hc' : c' ∈ integersTA)
    (hd' : d' ∈ integersTA)
    (hbPos : IntLT intZero b)
    (hb'Pos : IntLT intZero b')
    (hdPos : IntLT intZero d)
    (hd'Pos : IntLT intZero d')
    (hab :
      ratClass (ZFSet.pair a b) =
        ratClass (ZFSet.pair a' b'))
    (hcd :
      ratClass (ZFSet.pair c d) =
        ratClass (ZFSet.pair c' d'))
    (had : IntMul a d ad)
    (hbc : IntMul b c bc)
    (ha'd' : IntMul a' d' a'd')
    (hb'c' : IntMul b' c' b'c') :
    IntLE ad bc ↔ IntLE a'd' b'c' := by
  constructor
  · exact cross_comparison_forward
      ha hb ha' hb' hc hd hc' hd'
      hbPos hb'Pos hdPos hd'Pos
      hab hcd had hbc ha'd' hb'c'
  · exact cross_comparison_forward
      ha' hb' ha hb hc' hd' hc hd
      hb'Pos hbPos hd'Pos hdPos
      hab.symm hcd.symm ha'd' hb'c' had hbc

end TratadoAnalisis.Rationals.OrderWellDefined
