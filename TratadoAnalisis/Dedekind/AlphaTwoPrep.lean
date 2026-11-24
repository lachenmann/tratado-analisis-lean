import TratadoAnalisis.Rationals.Density

namespace TratadoAnalisis.Dedekind.AlphaTwoPrep

open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Naturals.ArithmeticBridge
open TratadoAnalisis.Integers.Construction
open TratadoAnalisis.Integers.Operations
open TratadoAnalisis.Integers.Multiplication
open TratadoAnalisis.Integers.Algebra
open TratadoAnalisis.Integers.Domain
open TratadoAnalisis.Integers.Order
open TratadoAnalisis.Rationals.IntegerPrep
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.Field
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.OrderedFieldCompatibility
open TratadoAnalisis.Rationals.StrictOrder
open TratadoAnalisis.Rationals.IrrationalitySqrtTwo
open TratadoAnalisis.Rationals.SquareMonotonicity
open TratadoAnalisis.Rationals.SqrtTwoSet


open TratadoAnalisis.Rationals.NoSupremumSqrtTwo

/-- Separador estricto por perturbación racional explícita.
delta=s²−2, den=2(s+1), h=delta/den, b=s−h.
La conclusión incluye 0<b<s y 2<b², no una propiedad de cota. -/
theorem positive_square_two_separator
    {s ss : ZFSet}
    (hs : s ∈ rationalsTA) (h0s : RatLT ratZero s)
    (hss : RatMul s s ss) (hTwoSs : RatLT ratTwoTA ss) :
    ∃ b : ZFSet, b ∈ rationalsTA ∧ RatLT ratZero b ∧ RatLT b s ∧
      ∃ bb : ZFSet, RatMul b b bb ∧ RatLT ratTwoTA bb := by
  have hssMem : ss ∈ rationalsTA :=
    funcFoundational_value_mem ratMulGraph_isFunc hss

  -- delta = s² - 2 > 0.
  rcases ratNeg_exists ratTwoTA_mem_rationalsTA with
    ⟨nTwo, hnTwoMem, hnTwo⟩
  rcases ratAdd_exists hssMem hnTwoMem with
    ⟨delta, hdeltaMem, hdelta⟩
  have h0delta : RatLT ratZero delta :=
    ratSub_positive_local hssMem ratTwoTA_mem_rationalsTA
      hTwoSs hnTwo hdelta
  have hDeltaTwo : RatAdd delta ratTwoTA ss :=
    ratSub_add_cancel_local hssMem ratTwoTA_mem_rationalsTA hnTwo hdelta

  -- den = 2(s+1) > 0.
  rcases ratAdd_exists hs ratOne_mem_rationalsTA with
    ⟨sOne, hsOneMem, hsOne⟩
  rcases ratAdd_exists hs ratZero_mem_rationalsTA with
    ⟨sZero, _hsZeroMem, hsZero⟩
  have hsZeroEq : sZero = s := ratAdd_zero_right hs hsZero
  have hsSOne : RatLT s sOne := by
    have h := ratLT_add_left_local
      ratZero_mem_rationalsTA ratOne_mem_rationalsTA hs
      ratZero_lt_one hsZero hsOne
    rw [hsZeroEq] at h
    exact h
  have h0sOne : RatLT ratZero sOne :=
    ratLT_of_lt_of_le_local
      ratZero_mem_rationalsTA hs hsOneMem h0s hsSOne.1
  rcases ratMul_exists ratTwoTA_mem_rationalsTA hsOneMem with
    ⟨den, hdenMem, hden⟩
  have h0den : RatLT ratZero den :=
    ratPositive_mul ratTwoTA_mem_rationalsTA hsOneMem hden
      ratZero_lt_two_local h0sOne

  -- h = delta / den > 0.
  have hdenNZ : den ∈ ratNonzeroTA :=
    mem_ratNonzeroTA_iff.mpr ⟨hdenMem, fun h => h0den.2 h.symm⟩
  rcases ratInvGraph_isFunc.2 den hdenNZ with ⟨iden, hidenData, _⟩
  have hidenNZ := hidenData.1
  have hiden : RatInv den iden := hidenData.2
  have hidenMem : iden ∈ rationalsTA :=
    (mem_ratNonzeroTA_iff.mp hidenNZ).1
  have h0iden : RatLT ratZero iden :=
    ratInv_positive hdenMem hiden h0den
  rcases ratMul_exists hdeltaMem hidenMem with ⟨h, hhMem, hh⟩
  have h0h : RatLT ratZero h :=
    ratPositive_mul hdeltaMem hidenMem hh h0delta h0iden

  -- delta < s² < s·den, luego h<s.
  rcases ratAdd_exists hssMem ratZero_mem_rationalsTA with
    ⟨ssZero, _hssZeroMem, hssZero⟩
  have hssZeroEq : ssZero = ss := ratAdd_zero_right hssMem hssZero
  have hnTwoLTZero : RatLT nTwo ratZero :=
    ratNeg_lt_zero_local ratTwoTA_mem_rationalsTA
      ratZero_lt_two_local hnTwo
  have hDeltaSs : RatLT delta ss := by
    have h := ratLT_add_left_local
      hnTwoMem ratZero_mem_rationalsTA hssMem
      hnTwoLTZero hdelta hssZero
    rw [hssZeroEq] at h
    exact h
  rcases ratMul_exists ratOne_mem_rationalsTA hsOneMem with
    ⟨oneSOne, _honeSOneMem, honeSOne⟩
  have honeSOneEq : oneSOne = sOne :=
    ratMul_one_left hsOneMem honeSOne
  have hSOneDen : RatLT sOne den := by
    have h := ratLT_mul_positive_right
      ratOne_mem_rationalsTA ratTwoTA_mem_rationalsTA hsOneMem
      ratOne_lt_two_local h0sOne honeSOne hden
    rw [honeSOneEq] at h
    exact h
  have hSDen : RatLT s den :=
    ratLT_of_lt_of_le_local hs hsOneMem hdenMem hsSOne hSOneDen.1
  rcases ratMul_exists hs hdenMem with ⟨sDen, hsDenMem, hsDen⟩
  have hSsSDen : RatLT ss sDen :=
    ratLT_mul_positive_left_local hs hdenMem hs hSDen h0s hss hsDen
  have hDeltaSDen : RatLT delta sDen :=
    ratLT_of_lt_of_le_local hdeltaMem hssMem hsDenMem
      hDeltaSs hSsSDen.1
  rcases ratMul_exists hsDenMem hidenMem with
    ⟨sDenInv, hsDenInvMem, hsDenInv⟩
  have hLaw := TA_PRO_00063_inverse_law hdenNZ hiden
  rcases ratMul_exists hs ratOne_mem_rationalsTA with
    ⟨sOneProd, _hsOneProdMem, hsOneProd⟩
  have hAssocCancel : sDenInv = sOneProd :=
    ratMul_assoc hs hdenMem hidenMem hsDen hsDenInv hLaw.1 hsOneProd
  have hsOneProdEq : sOneProd = s := ratMul_one_right hs hsOneProd
  have hsDenInvEq : sDenInv = s := hAssocCancel.trans hsOneProdEq
  have hHLTS : RatLT h s := by
    have hScaled := ratLT_mul_positive_right
      hdeltaMem hsDenMem hidenMem hDeltaSDen h0iden hh hsDenInv
    rw [hsDenInvEq] at hScaled
    exact hScaled

  -- r = s-h, con 0<r<s y r+h=s.
  rcases ratNeg_exists hhMem with ⟨nh, hnhMem, hnh⟩
  rcases ratAdd_exists hs hnhMem with ⟨r, hrMem, hr⟩
  have h0r : RatLT ratZero r :=
    ratSub_positive_local hs hhMem hHLTS hnh hr
  have hRPlusH : RatAdd r h s :=
    ratSub_add_cancel_local hs hhMem hnh hr
  have hnhLTZero : RatLT nh ratZero :=
    ratNeg_lt_zero_local hhMem h0h hnh
  have hrS : RatLT r s := by
    have h := ratLT_add_left_local
      hnhMem ratZero_mem_rationalsTA hs
      hnhLTZero hr hsZero
    rw [hsZeroEq] at h
    exact h

  -- tail = 2r+h = 2s-h < 2s < den.
  rcases ratMul_exists ratTwoTA_mem_rationalsTA hrMem with
    ⟨twoR, htwoRMem, htwoR⟩
  rcases ratMul_exists ratTwoTA_mem_rationalsTA hhMem with
    ⟨twoH, htwoHMem, htwoH⟩
  have hTwoHAdd : RatAdd h h twoH :=
    ratTwo_mul_as_add_local hhMem htwoH
  rcases ratMul_exists ratTwoTA_mem_rationalsTA hs with
    ⟨twoS, htwoSMem, htwoS⟩
  rcases ratAdd_exists htwoRMem htwoHMem with
    ⟨twoParts, htwoPartsMem, htwoParts⟩
  have hTwoDist : twoS = twoParts :=
    ratMul_add_left ratTwoTA_mem_rationalsTA hrMem hhMem
      hRPlusH htwoS htwoR htwoH htwoParts
  rcases ratAdd_exists htwoRMem hhMem with
    ⟨tail, htailMem, htail⟩
  rcases ratAdd_exists htailMem hhMem with
    ⟨tailH, _htailHMem, htailH⟩
  have hTailHParts : tailH = twoParts :=
    ratAdd_assoc htwoRMem hhMem hhMem
      htail htailH hTwoHAdd htwoParts
  have hTailHTwoS : RatAdd tail h twoS := by
    rw [hTailHParts, ← hTwoDist] at htailH
    exact htailH
  rcases ratAdd_exists htailMem ratZero_mem_rationalsTA with
    ⟨tailZero, _htailZeroMem, htailZero⟩
  have htailZeroEq : tailZero = tail :=
    ratAdd_zero_right htailMem htailZero
  have hTailTwoS : RatLT tail twoS := by
    have h := ratLT_add_left_local
      ratZero_mem_rationalsTA hhMem htailMem h0h
      htailZero hTailHTwoS
    rw [htailZeroEq] at h
    exact h
  have hTwoSDen : RatLT twoS den :=
    ratLT_mul_positive_left_local hs hsOneMem ratTwoTA_mem_rationalsTA
      hsSOne ratZero_lt_two_local htwoS hden
  have hTailDen : RatLT tail den :=
    ratLT_of_lt_of_le_local htailMem htwoSMem hdenMem
      hTailTwoS hTwoSDen.1

  -- h(2r+h)<delta.
  rcases ratMul_exists hhMem htailMem with
    ⟨hTail, hhTailMem, hhTail⟩
  have hhDen : RatMul h den delta :=
    ratQuotient_mul_denominator_local
      hdeltaMem hdenMem h0den hiden hh
  have hHTailDelta : RatLT hTail delta :=
    ratLT_mul_positive_left_local
      htailMem hdenMem hhMem hTailDen h0h hhTail hhDen

  -- s²=r²+h(2r+h), luego 2<r².
  rcases ratMul_exists hrMem hrMem with ⟨rr, hrrMem, hrr⟩
  rcases ratAdd_exists hrrMem hhTailMem with ⟨rhs, hrhsMem, hrhs⟩
  have hExpansion : ss = rhs :=
    square_add_expansion_local
      hrMem hhMem hrr htwoR htail hhTail hRPlusH hss hrhs
  rcases ratAdd_exists ratTwoTA_mem_rationalsTA hhTailMem with
    ⟨twoHTail, htwoHTailMem, htwoHTail⟩
  rcases ratAdd_exists ratTwoTA_mem_rationalsTA hdeltaMem with
    ⟨twoDelta, _htwoDeltaMem, htwoDelta⟩
  have hTwoDeltaEq : twoDelta = ss :=
    ratAdd_comm ratTwoTA_mem_rationalsTA hdeltaMem htwoDelta hDeltaTwo
  have hTwoHTailSs : RatLT twoHTail ss := by
    have h := ratLT_add_left_local
      hhTailMem hdeltaMem ratTwoTA_mem_rationalsTA
      hHTailDelta htwoHTail htwoDelta
    rw [hTwoDeltaEq] at h
    exact h
  have hTwoHTailRhs : RatLT twoHTail rhs := by
    rw [← hExpansion]
    exact hTwoHTailSs
  have hTwoRR : RatLT ratTwoTA rr :=
    ratLT_add_cancel_right_local
      ratTwoTA_mem_rationalsTA hrrMem hhTailMem
      htwoHTail hrhs hTwoHTailRhs


  exact ⟨r, hrMem, h0r, hrS, rr, hrr, hTwoRR⟩

end TratadoAnalisis.Dedekind.AlphaTwoPrep

