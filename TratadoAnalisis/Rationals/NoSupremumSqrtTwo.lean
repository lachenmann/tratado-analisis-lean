import TratadoAnalisis.Rationals.SqrtTwoSet
import TratadoAnalisis.Rationals.SquareMonotonicity

namespace TratadoAnalisis.Rationals.NoSupremumSqrtTwo

universe u

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

/-!
# E3 — `S₂` no posee supremo racional

La noción de supremo se expresa únicamente mediante la relación de orden del
tratado. No se introduce una operación `sup`, una estructura de Mathlib ni una
selección global de testigos aritméticos.
-/

/-- Cota superior racional de un subconjunto conjuntista. -/
def RatUpperBound (A u : ZFSet) : Prop :=
  u ∈ rationalsTA ∧ ∀ x : ZFSet, x ∈ A → RatLE x u

/-- Menor cota superior racional, expresada relacionalmente. -/
def RatSupremum (A s : ZFSet) : Prop :=
  RatUpperBound A s ∧
    ∀ u : ZFSet, RatUpperBound A u → RatLE s u

/-! ## Helpers técnicos de orden y suma -/

/-- Transitividad mixta `a < b ≤ c → a < c`. -/
theorem ratLT_of_lt_of_le_local
    {a b c : ZFSet}
    (ha : a ∈ rationalsTA) (hb : b ∈ rationalsTA)
    (hc : c ∈ rationalsTA)
    (hab : RatLT a b) (hbc : RatLE b c) :
    RatLT a c := by
  refine ⟨ratLE_trans ha hb hc hab.1 hbc, ?_⟩
  intro hac
  have hba : RatLE b a := by
    rw [hac]
    exact hbc
  exact hab.2 (ratLE_antisymm ha hb hab.1 hba)

/-- Cancelación de una suma común a la derecha. -/
theorem ratAdd_cancel_right_local
    {x y z xz yz : ZFSet}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (hz : z ∈ rationalsTA)
    (hxz : RatAdd x z xz) (hyz : RatAdd y z yz)
    (hEq : xz = yz) : x = y := by
  rcases ratNeg_exists hz with ⟨nz, hnzMem, hnz⟩
  rcases ratAdd_exists hz hnzMem with ⟨z0, hz0Mem, hz0⟩
  have hz0Eq : z0 = ratZero := ratAdd_neg_right hz hnz hz0
  have hxzMem : xz ∈ rationalsTA :=
    funcFoundational_value_mem ratAddGraph_isFunc hxz
  have hyzMem : yz ∈ rationalsTA :=
    funcFoundational_value_mem ratAddGraph_isFunc hyz
  rcases ratAdd_exists hxzMem hnzMem with ⟨xBack, _hxBackMem, hxBack⟩
  rcases ratAdd_exists hx hz0Mem with ⟨xFlat, _hxFlatMem, hxFlat⟩
  have hxAssoc : xBack = xFlat :=
    ratAdd_assoc hx hz hnzMem hxz hxBack hz0 hxFlat
  have hxFlatEq : xFlat = x := by
    rw [hz0Eq] at hxFlat
    exact ratAdd_zero_right hx hxFlat
  rcases ratAdd_exists hyzMem hnzMem with ⟨yBack, _hyBackMem, hyBack⟩
  rcases ratAdd_exists hy hz0Mem with ⟨yFlat, _hyFlatMem, hyFlat⟩
  have hyAssoc : yBack = yFlat :=
    ratAdd_assoc hy hz hnzMem hyz hyBack hz0 hyFlat
  have hyFlatEq : yFlat = y := by
    rw [hz0Eq] at hyFlat
    exact ratAdd_zero_right hy hyFlat
  have hBack : xBack = yBack := by
    apply RatAdd_unique hxzMem hnzMem hxBack
    rw [hEq]
    exact hyBack
  exact hxFlatEq.symm.trans (hxAssoc.symm.trans
    (hBack.trans (hyAssoc.trans hyFlatEq)))

/-- Cancelación monótona de una suma común a la derecha. -/
theorem ratLE_add_cancel_right_local
    {x y z xz yz : ZFSet}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (hz : z ∈ rationalsTA)
    (hxz : RatAdd x z xz) (hyz : RatAdd y z yz)
    (hxy : RatLE xz yz) : RatLE x y := by
  rcases ratNeg_exists hz with ⟨nz, hnzMem, hnz⟩
  have hxzMem : xz ∈ rationalsTA :=
    funcFoundational_value_mem ratAddGraph_isFunc hxz
  have hyzMem : yz ∈ rationalsTA :=
    funcFoundational_value_mem ratAddGraph_isFunc hyz
  rcases ratAdd_exists hxzMem hnzMem with ⟨xBack, hxBackMem, hxBack⟩
  rcases ratAdd_exists hyzMem hnzMem with ⟨yBack, hyBackMem, hyBack⟩
  have hBack : RatLE xBack yBack :=
    ratLE_add_compat hxzMem hyzMem hnzMem hxy hxBack hyBack
  rcases ratAdd_exists hz hnzMem with ⟨z0, hz0Mem, hz0⟩
  have hz0Eq : z0 = ratZero := ratAdd_neg_right hz hnz hz0
  rcases ratAdd_exists hx hz0Mem with ⟨xFlat, _hxFlatMem, hxFlat⟩
  rcases ratAdd_exists hy hz0Mem with ⟨yFlat, _hyFlatMem, hyFlat⟩
  have hxAssoc : xBack = xFlat :=
    ratAdd_assoc hx hz hnzMem hxz hxBack hz0 hxFlat
  have hyAssoc : yBack = yFlat :=
    ratAdd_assoc hy hz hnzMem hyz hyBack hz0 hyFlat
  have hxFlatEq : xFlat = x := by
    rw [hz0Eq] at hxFlat
    exact ratAdd_zero_right hx hxFlat
  have hyFlatEq : yFlat = y := by
    rw [hz0Eq] at hyFlat
    exact ratAdd_zero_right hy hyFlat
  rw [hxAssoc, hyAssoc, hxFlatEq, hyFlatEq] at hBack
  exact hBack

/-- Cancelación estricta de una suma común a la derecha. -/
theorem ratLT_add_cancel_right_local
    {x y z xz yz : ZFSet}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (hz : z ∈ rationalsTA)
    (hxz : RatAdd x z xz) (hyz : RatAdd y z yz)
    (hxy : RatLT xz yz) : RatLT x y := by
  refine ⟨ratLE_add_cancel_right_local hx hy hz hxz hyz hxy.1, ?_⟩
  intro hEq
  have hSumEq : xz = yz := by
    apply RatAdd_unique hx hz hxz
    rw [hEq]
    exact hyz
  exact hxy.2 hSumEq

/-- Traslación estricta por una suma común a la derecha. -/
theorem ratLT_add_right_local
    {x y z xz yz : ZFSet}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (hz : z ∈ rationalsTA)
    (hxy : RatLT x y)
    (hxz : RatAdd x z xz) (hyz : RatAdd y z yz) :
    RatLT xz yz := by
  refine ⟨ratLE_add_compat hx hy hz hxy.1 hxz hyz, ?_⟩
  intro hEq
  exact hxy.2 (ratAdd_cancel_right_local hx hy hz hxz hyz hEq)

/-- Traslación estricta por una suma común a la izquierda. -/
theorem ratLT_add_left_local
    {x y z zx zy : ZFSet}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (hz : z ∈ rationalsTA)
    (hxy : RatLT x y)
    (hzx : RatAdd z x zx) (hzy : RatAdd z y zy) :
    RatLT zx zy := by
  rcases ratAdd_exists hx hz with ⟨xz, _hxzMem, hxz⟩
  rcases ratAdd_exists hy hz with ⟨yz, _hyzMem, hyz⟩
  have hTranslated := ratLT_add_right_local hx hy hz hxy hxz hyz
  have hzxEq : zx = xz := ratAdd_comm hz hx hzx hxz
  have hzyEq : zy = yz := ratAdd_comm hz hy hzy hyz
  rw [hzxEq, hzyEq]
  exact hTranslated

/-- Traslación no estricta por una suma común a la izquierda. -/
theorem ratLE_add_left_local
    {x y z zx zy : ZFSet}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (hz : z ∈ rationalsTA)
    (hxy : RatLE x y)
    (hzx : RatAdd z x zx) (hzy : RatAdd z y zy) :
    RatLE zx zy := by
  rcases ratAdd_exists hx hz with ⟨xz, _hxzMem, hxz⟩
  rcases ratAdd_exists hy hz with ⟨yz, _hyzMem, hyz⟩
  have hTranslated := ratLE_add_compat hx hy hz hxy hxz hyz
  have hzxEq : zx = xz := ratAdd_comm hz hx hzx hxz
  have hzyEq : zy = yz := ratAdd_comm hz hy hzy hyz
  rw [hzxEq, hzyEq]
  exact hTranslated

/-- Escalamiento estricto por un factor positivo a la izquierda. -/
theorem ratLT_mul_positive_left_local
    {x y z zx zy : ZFSet}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (hz : z ∈ rationalsTA)
    (hxy : RatLT x y) (h0z : RatLT ratZero z)
    (hzx : RatMul z x zx) (hzy : RatMul z y zy) :
    RatLT zx zy := by
  rcases ratMul_exists hx hz with ⟨xz, _hxzMem, hxz⟩
  rcases ratMul_exists hy hz with ⟨yz, _hyzMem, hyz⟩
  have hxyScaled := ratLT_mul_positive_right hx hy hz hxy h0z hxz hyz
  have hzxEq : zx = xz := ratMul_comm hz hx hzx hxz
  have hzyEq : zy = yz := ratMul_comm hz hy hzy hyz
  rw [hzxEq, hzyEq]
  exact hxyScaled

/-- Relación canónica `1_Q + 1_Q = 2_Q`. -/
theorem ratOne_add_one_two_local :
    RatAdd (ratOne : ZFSet.{u}) ratOne ratTwoTA := by
  rcases intEmbedGraph_add_nat.{u, u, u, u} 1 1 with
    ⟨_h1, _h1', _h2, hAdd⟩
  have hIntAdd : IntAdd (intOne : ZFSet.{u}) intOne intTwoTA := by
    simpa [intOne, intTwoTA, intPositiveForm] using hAdd
  exact ratEmbedGraph_add ratEmbedGraph_one ratEmbedGraph_one
    intTwoTA_ratEmbed hIntAdd

/-- `2_Q * x` es también el valor relacional de `x + x`. -/
theorem ratTwo_mul_as_add_local
    {x twoX : ZFSet}
    (hx : x ∈ rationalsTA)
    (hTwoX : RatMul ratTwoTA x twoX) :
    RatAdd x x twoX := by
  rcases ratMul_exists ratOne_mem_rationalsTA hx with
    ⟨oneX₁, honeX₁Mem, honeX₁⟩
  rcases ratMul_exists ratOne_mem_rationalsTA hx with
    ⟨oneX₂, honeX₂Mem, honeX₂⟩
  rcases ratAdd_exists honeX₁Mem honeX₂Mem with
    ⟨sum, _hsumMem, hsum⟩
  have hDist : twoX = sum :=
    ratAdd_mul_right
      ratOne_mem_rationalsTA ratOne_mem_rationalsTA hx
      ratOne_add_one_two_local hTwoX honeX₁ honeX₂ hsum
  have honeX₁Eq : oneX₁ = x := ratMul_one_left hx honeX₁
  have honeX₂Eq : oneX₂ = x := ratMul_one_left hx honeX₂
  rw [honeX₁Eq, honeX₂Eq, ← hDist] at hsum
  exact hsum

/-- Expansión relacional `(a+b)² = a² + b(2a+b)`. -/
theorem square_add_expansion_local
    {a b aa twoA tail bTail sum sumSq rhs : ZFSet}
    (ha : a ∈ rationalsTA) (hb : b ∈ rationalsTA)
    (haa : RatMul a a aa)
    (hTwoA : RatMul ratTwoTA a twoA)
    (hTail : RatAdd twoA b tail)
    (hbTail : RatMul b tail bTail)
    (hSum : RatAdd a b sum)
    (hSumSq : RatMul sum sum sumSq)
    (hRhs : RatAdd aa bTail rhs) :
    sumSq = rhs := by
  have haaMem : aa ∈ rationalsTA :=
    funcFoundational_value_mem ratMulGraph_isFunc haa
  have hTwoAMem : twoA ∈ rationalsTA :=
    funcFoundational_value_mem ratMulGraph_isFunc hTwoA
  have hTailMem : tail ∈ rationalsTA :=
    funcFoundational_value_mem ratAddGraph_isFunc hTail
  have hSumMem : sum ∈ rationalsTA :=
    funcFoundational_value_mem ratAddGraph_isFunc hSum

  rcases ratMul_exists ha hb with ⟨ab, habMem, hab⟩
  rcases ratMul_exists hb ha with ⟨ba, hbaMem, hba⟩
  have habEq : ab = ba := ratMul_comm ha hb hab hba
  rcases ratMul_exists hb hb with ⟨bb, hbbMem, hbb⟩

  rcases ratMul_exists ha hSumMem with ⟨aSum, haSumMem, haSum⟩
  rcases ratAdd_exists haaMem habMem with ⟨aaAb, haaAbMem, haaAb⟩
  have haDist : aSum = aaAb :=
    ratMul_add_left ha ha hb hSum haSum haa hab haaAb

  rcases ratMul_exists hb hSumMem with ⟨bSum, hbSumMem, hbSum⟩
  rcases ratAdd_exists hbaMem hbbMem with ⟨baBb, hbaBbMem, hbaBb⟩
  have hbDist : bSum = baBb :=
    ratMul_add_left hb ha hb hSum hbSum hba hbb hbaBb

  rcases ratAdd_exists haSumMem hbSumMem with
    ⟨expanded, _hexpandedMem, hExpanded⟩
  have hOuterDist : sumSq = expanded :=
    ratAdd_mul_right ha hb hSumMem hSum hSumSq haSum hbSum hExpanded

  have hTwoAAdd : RatAdd a a twoA :=
    ratTwo_mul_as_add_local ha hTwoA
  rcases ratMul_exists hb hTwoAMem with
    ⟨bTwoA, hbTwoAMem, hbTwoA⟩
  rcases ratAdd_exists hbaMem hbaMem with
    ⟨baBa, hbaBaMem, hbaBa⟩
  have hbTwoDist : bTwoA = baBa :=
    ratMul_add_left hb ha ha hTwoAAdd hbTwoA hba hba hbaBa
  rcases ratAdd_exists hbTwoAMem hbbMem with
    ⟨bTwoABb, hbTwoABbMem, hbTwoABb⟩
  have hbTailDist : bTail = bTwoABb :=
    ratMul_add_left hb hTwoAMem hb hTail hbTail hbTwoA hbb hbTwoABb

  rcases ratAdd_exists habMem hbaBbMem with
    ⟨inner, hinnerMem, hInner⟩
  rcases ratAdd_exists hbaBaMem hbbMem with
    ⟨doubleTail, hdoubleTailMem, hDoubleTail⟩
  have hInnerAssoc : doubleTail = inner := by
    have hInner' : RatAdd ba baBb inner := by
      rw [← habEq]
      exact hInner
    exact ratAdd_assoc hbaMem hbaMem hbbMem
      hbaBa hDoubleTail hbaBb hInner'
  rcases ratAdd_exists haaMem hinnerMem with
    ⟨canonical, _hcanonicalMem, hCanonical⟩
  have hExpanded' : RatAdd aaAb baBb expanded := by
    rw [← haDist, ← hbDist]
    exact hExpanded
  have hExpandedAssoc : expanded = canonical :=
    ratAdd_assoc haaMem habMem hbaBbMem
      haaAb hExpanded' hInner hCanonical

  have hBTwoABbAt : RatAdd baBa bb bTwoABb := by
    rw [← hbTwoDist]
    exact hbTwoABb
  have hBTwoABbEq : bTwoABb = doubleTail :=
    RatAdd_unique hbaBaMem hbbMem hBTwoABbAt hDoubleTail
  have hInnerEq : inner = bTail :=
    hInnerAssoc.symm.trans
      (hBTwoABbEq.symm.trans hbTailDist.symm)

  have hCanonicalEq : canonical = rhs := by
    rw [hInnerEq] at hCanonical
    exact RatAdd_unique haaMem
      (funcFoundational_value_mem ratMulGraph_isFunc hbTail)
      hCanonical hRhs

  exact hOuterDist.trans (hExpandedAssoc.trans hCanonicalEq)

/-- Escalamiento no estricto por un factor no negativo a la izquierda. -/
theorem ratLE_mul_nonnegative_left_local
    {x y z zx zy : ZFSet}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (hz : z ∈ rationalsTA)
    (hxy : RatLE x y) (h0z : RatLE ratZero z)
    (hzx : RatMul z x zx) (hzy : RatMul z y zy) :
    RatLE zx zy := by
  rcases ratMul_exists hx hz with ⟨xz, _hxzMem, hxz⟩
  rcases ratMul_exists hy hz with ⟨yz, _hyzMem, hyz⟩
  have hScaled :=
    ratLE_mul_nonnegative_compat hx hy hz hxy h0z hxz hyz
  have hzxEq : zx = xz := ratMul_comm hz hx hzx hxz
  have hzyEq : zy = yz := ratMul_comm hz hy hzy hyz
  rw [hzxEq, hzyEq]
  exact hScaled

/-- Si `d = a + (-b)` y `b<a`, entonces `0<d`. -/
theorem ratSub_positive_local
    {a b nb d : ZFSet}
    (ha : a ∈ rationalsTA) (hb : b ∈ rationalsTA)
    (hba : RatLT b a)
    (hNeg : RatNeg b nb) (hSub : RatAdd a nb d) :
    RatLT ratZero d := by
  have hnbMem : nb ∈ rationalsTA :=
    funcFoundational_value_mem ratNegGraph_isFunc hNeg
  rcases ratAdd_exists hb hnbMem with ⟨zero, _hzeroMem, hzero⟩
  have hzeroEq : zero = ratZero := ratAdd_neg_right hb hNeg hzero
  have hTranslated :=
    ratLT_add_right_local hb ha hnbMem hba hzero hSub
  rw [hzeroEq] at hTranslated
  exact hTranslated

/-- Si `d = a-b`, entonces `d+b=a`. -/
theorem ratSub_add_cancel_local
    {a b nb d : ZFSet}
    (ha : a ∈ rationalsTA) (hb : b ∈ rationalsTA)
    (hNeg : RatNeg b nb) (hSub : RatAdd a nb d) :
    RatAdd d b a := by
  have hnbMem : nb ∈ rationalsTA :=
    funcFoundational_value_mem ratNegGraph_isFunc hNeg
  have hdMem : d ∈ rationalsTA :=
    funcFoundational_value_mem ratAddGraph_isFunc hSub
  rcases ratAdd_exists hnbMem hb with ⟨zero, hzeroMem, hzero⟩
  rcases ratAdd_exists hdMem hb with ⟨back, _hbackMem, hback⟩
  rcases ratAdd_exists ha hzeroMem with ⟨flat, _hflatMem, hflat⟩
  have hzeroEq : zero = ratZero := ratAdd_neg_left hb hNeg hzero
  have hAssoc : back = flat :=
    ratAdd_assoc ha hnbMem hb hSub hback hzero hflat
  have hflatEq : flat = a := by
    rw [hzeroEq] at hflat
    exact ratAdd_zero_right ha hflat
  rw [hAssoc, hflatEq] at hback
  exact hback

/-- El opuesto de un racional positivo es estrictamente negativo. -/
theorem ratNeg_lt_zero_local
    {x nx : ZFSet}
    (hx : x ∈ rationalsTA) (h0x : RatLT ratZero x)
    (hNeg : RatNeg x nx) :
    RatLT nx ratZero := by
  have hnxMem : nx ∈ rationalsTA :=
    funcFoundational_value_mem ratNegGraph_isFunc hNeg
  rcases ratAdd_exists ratZero_mem_rationalsTA hnxMem with
    ⟨left, _hleftMem, hleft⟩
  rcases ratAdd_exists hx hnxMem with ⟨right, _hrightMem, hright⟩
  have hTranslated := ratLT_add_right_local
    ratZero_mem_rationalsTA hx hnxMem h0x hleft hright
  have hleftEq : left = nx := ratAdd_zero_left hnxMem hleft
  have hrightEq : right = ratZero := ratAdd_neg_right hx hNeg hright
  rw [hleftEq, hrightEq] at hTranslated
  exact hTranslated

/-- Multiplicar un cociente relacional por su denominador recupera el numerador. -/
theorem ratQuotient_mul_denominator_local
    {a d id q : ZFSet}
    (ha : a ∈ rationalsTA) (hd : d ∈ rationalsTA)
    (h0d : RatLT ratZero d)
    (hInv : RatInv d id) (hQ : RatMul a id q) :
    RatMul q d a := by
  have hdNZ : d ∈ ratNonzeroTA :=
    mem_ratNonzeroTA_iff.mpr ⟨hd, fun h => h0d.2 h.symm⟩
  have hidMem : id ∈ rationalsTA :=
    (mem_ratNonzeroTA_iff.mp
      (funcFoundational_value_mem ratInvGraph_isFunc hInv)).1
  have hLaw := TA_PRO_00063_inverse_law hdNZ hInv
  have hqMem : q ∈ rationalsTA :=
    funcFoundational_value_mem ratMulGraph_isFunc hQ
  rcases ratMul_exists hqMem hd with ⟨qd, _hqdMem, hqd⟩
  rcases ratMul_exists ha ratOne_mem_rationalsTA with
    ⟨aOne, _haOneMem, haOne⟩
  have hAssoc : qd = aOne :=
    ratMul_assoc ha hidMem hd hQ hqd hLaw.2 haOne
  have haOneEq : aOne = a := ratMul_one_right ha haOne
  rw [hAssoc, haOneEq] at hqd
  exact hqd

/-! ## Primera perturbación: `s² < 2` -/

/-- Si `s>0` y `s²<2`, existe un elemento de `S₂` estrictamente mayor que `s`. -/
theorem square_lt_two_gives_larger_member_local
    {s ss : ZFSet}
    (hs : s ∈ rationalsTA) (h0s : RatLT ratZero s)
    (hss : RatMul s s ss) (hssTwo : RatLT ss ratTwoTA) :
    ∃ t : ZFSet, t ∈ sqrtTwoSet ∧ RatLT s t := by
  have hssMem : ss ∈ rationalsTA :=
    funcFoundational_value_mem ratMulGraph_isFunc hss
  have h0ss : RatLE ratZero ss :=
    ratLE_mul_nonnegative_compat
      ratZero_mem_rationalsTA hs hs h0s.1 h0s.1
      (ratMul_zero_left hs) hss

  -- delta = 2 - s² > 0.
  rcases ratNeg_exists hssMem with ⟨nss, hnssMem, hnss⟩
  rcases ratAdd_exists ratTwoTA_mem_rationalsTA hnssMem with
    ⟨delta, hdeltaMem, hdelta⟩
  have h0delta : RatLT ratZero delta :=
    ratSub_positive_local ratTwoTA_mem_rationalsTA hssMem
      hssTwo hnss hdelta
  have hDeltaSs : RatAdd delta ss ratTwoTA :=
    ratSub_add_cancel_local ratTwoTA_mem_rationalsTA hssMem hnss hdelta

  -- s+1 y 2(s+1).
  rcases ratAdd_exists hs ratOne_mem_rationalsTA with
    ⟨sOne, hsOneMem, hsOne⟩
  rcases ratAdd_exists ratZero_mem_rationalsTA ratOne_mem_rationalsTA with
    ⟨zeroOne, _hzeroOneMem, hzeroOne⟩
  have hzeroOneEq : zeroOne = ratOne :=
    ratAdd_zero_left ratOne_mem_rationalsTA hzeroOne
  have hOneSOne : RatLT ratOne sOne := by
    have h := ratLT_add_right_local
      ratZero_mem_rationalsTA hs ratOne_mem_rationalsTA
      h0s hzeroOne hsOne
    rw [hzeroOneEq] at h
    exact h
  have h0sOne : RatLT ratZero sOne :=
    ratLT_of_lt_of_le_local
      ratZero_mem_rationalsTA ratOne_mem_rationalsTA hsOneMem
      ratZero_lt_one hOneSOne.1
  rcases ratMul_exists ratTwoTA_mem_rationalsTA hsOneMem with
    ⟨den, hdenMem, hden⟩
  have h0den : RatLT ratZero den :=
    ratPositive_mul ratTwoTA_mem_rationalsTA hsOneMem hden
      ratZero_lt_two_local h0sOne

  -- h = delta / den, construido con el inverso relacional.
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

  -- delta ≤ 2 < den, luego h < 1.
  rcases ratAdd_exists ratTwoTA_mem_rationalsTA hssMem with
    ⟨twoSs, htwoSsMem, htwoSs⟩
  rcases ratAdd_exists ratZero_mem_rationalsTA ratTwoTA_mem_rationalsTA with
    ⟨zeroTwo, _hzeroTwoMem, hzeroTwo⟩
  rcases ratAdd_exists hssMem ratTwoTA_mem_rationalsTA with
    ⟨ssTwo, _hssTwoMem, hssTwoAdd⟩
  have hzeroTwoEq : zeroTwo = ratTwoTA :=
    ratAdd_zero_left ratTwoTA_mem_rationalsTA hzeroTwo
  have hssTwoEq : ssTwo = twoSs :=
    ratAdd_comm hssMem ratTwoTA_mem_rationalsTA hssTwoAdd htwoSs
  have hTwoLETwoSs : RatLE ratTwoTA twoSs := by
    have h := ratLE_add_compat
      ratZero_mem_rationalsTA hssMem ratTwoTA_mem_rationalsTA
      h0ss
      hzeroTwo hssTwoAdd
    rw [hzeroTwoEq, hssTwoEq] at h
    exact h
  have hDeltaLETwo : RatLE delta ratTwoTA :=
    ratLE_add_cancel_right_local
      hdeltaMem ratTwoTA_mem_rationalsTA hssMem
      hDeltaSs htwoSs hTwoLETwoSs

  rcases ratMul_exists ratTwoTA_mem_rationalsTA ratOne_mem_rationalsTA with
    ⟨twoOne, _htwoOneMem, htwoOne⟩
  have htwoOneEq : twoOne = ratTwoTA :=
    ratMul_one_right ratTwoTA_mem_rationalsTA htwoOne
  have hTwoDen : RatLT ratTwoTA den := by
    have h := ratLT_mul_positive_left_local
      ratOne_mem_rationalsTA hsOneMem ratTwoTA_mem_rationalsTA
      hOneSOne ratZero_lt_two_local htwoOne hden
    rw [htwoOneEq] at h
    exact h
  have hDeltaDen : RatLT delta den :=
    ratLT_of_le_of_lt_local
      hdeltaMem ratTwoTA_mem_rationalsTA hdenMem
      hDeltaLETwo hTwoDen
  have hLaw := TA_PRO_00063_inverse_law hdenNZ hiden
  have hHLTOne : RatLT h ratOne :=
    ratLT_mul_positive_right
      hdeltaMem hdenMem hidenMem hDeltaDen h0iden hh hLaw.1

  -- 2s+h < 2(s+1).
  rcases ratMul_exists ratTwoTA_mem_rationalsTA hs with
    ⟨twoS, htwoSMem, htwoS⟩
  rcases ratAdd_exists htwoSMem hhMem with ⟨tail, htailMem, htail⟩
  rcases ratAdd_exists htwoSMem ratOne_mem_rationalsTA with
    ⟨twoSOne, htwoSOneMem, htwoSOne⟩
  have hTailTwoSOne : RatLT tail twoSOne :=
    ratLT_add_left_local hhMem ratOne_mem_rationalsTA htwoSMem
      hHLTOne htail htwoSOne
  rcases ratAdd_exists htwoSMem ratTwoTA_mem_rationalsTA with
    ⟨twoSTwo, htwoSTwoMem, htwoSTwo⟩
  have hTwoSOneTwoSTwo : RatLT twoSOne twoSTwo :=
    ratLT_add_left_local
      ratOne_mem_rationalsTA ratTwoTA_mem_rationalsTA htwoSMem
      ratOne_lt_two_local htwoSOne htwoSTwo
  have hTailTwoSTwo : RatLT tail twoSTwo :=
    ratLT_of_lt_of_le_local htailMem htwoSOneMem htwoSTwoMem
      hTailTwoSOne hTwoSOneTwoSTwo.1
  have hDenEq : den = twoSTwo :=
    ratMul_add_left
      ratTwoTA_mem_rationalsTA hs ratOne_mem_rationalsTA
      hsOne hden htwoS
      (by simpa [htwoOneEq] using htwoOne) htwoSTwo
  have hTailDen : RatLT tail den := by
    rw [hDenEq]
    exact hTailTwoSTwo

  -- h(2s+h) < delta.
  rcases ratMul_exists hhMem htailMem with
    ⟨hTail, hhTailMem, hhTail⟩
  have hhDen : RatMul h den delta :=
    ratQuotient_mul_denominator_local
      hdeltaMem hdenMem h0den hiden hh
  have hHTailDelta : RatLT hTail delta :=
    ratLT_mul_positive_left_local
      htailMem hdenMem hhMem hTailDen h0h hhTail hhDen

  -- (s+h)² = s²+h(2s+h) < 2.
  rcases ratAdd_exists hs hhMem with ⟨t, htMem, ht⟩
  rcases ratMul_exists htMem htMem with ⟨tt, httMem, htt⟩
  rcases ratAdd_exists hssMem hhTailMem with ⟨rhs, hrhsMem, hrhs⟩
  have hExpansion : tt = rhs :=
    square_add_expansion_local hs hhMem hss htwoS htail hhTail ht htt hrhs
  rcases ratAdd_exists hssMem hdeltaMem with
    ⟨ssDelta, _hssDeltaMem, hssDelta⟩
  have hssDeltaEq : ssDelta = ratTwoTA :=
    ratAdd_comm hssMem hdeltaMem hssDelta hDeltaSs
  have hRhsLTTwo : RatLT rhs ratTwoTA := by
    have h := ratLT_add_left_local
      hhTailMem hdeltaMem hssMem hHTailDelta hrhs hssDelta
    rw [hssDeltaEq] at h
    exact h
  have hTTSmaller : RatLT tt ratTwoTA := by
    rw [hExpansion]
    exact hRhsLTTwo

  -- s<t y t∈S₂.
  rcases ratAdd_exists hs ratZero_mem_rationalsTA with
    ⟨sZero, _hsZeroMem, hsZero⟩
  have hsZeroEq : sZero = s := ratAdd_zero_right hs hsZero
  have hsT : RatLT s t := by
    have h := ratLT_add_left_local
      ratZero_mem_rationalsTA hhMem hs h0h hsZero ht
    rw [hsZeroEq] at h
    exact h
  have h0t : RatLE ratZero t :=
    ratLE_trans ratZero_mem_rationalsTA hs htMem h0s.1 hsT.1
  have htSet : t ∈ sqrtTwoSet :=
    TA_DEF_00066_mem_sqrtTwoSet_iff.mpr
      ⟨htMem, h0t, tt, htt, hTTSmaller⟩
  exact ⟨t, htSet, hsT⟩

/-! ## Segunda perturbación: `2 < s²` -/

/-- Si `s>0` y `2<s²`, existe una cota superior de `S₂` menor que `s`. -/
theorem two_lt_square_gives_smaller_upper_local
    {s ss : ZFSet}
    (hs : s ∈ rationalsTA) (h0s : RatLT ratZero s)
    (hss : RatMul s s ss) (hTwoSs : RatLT ratTwoTA ss) :
    ∃ r : ZFSet, RatUpperBound sqrtTwoSet r ∧ RatLT r s := by
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

  -- E2a: cualquier x∈S₂ no puede satisfacer r<x.
  have hUpper : RatUpperBound sqrtTwoSet r := by
    refine ⟨hrMem, ?_⟩
    intro x hxSet
    rcases TA_DEF_00066_mem_sqrtTwoSet_iff.mp hxSet with
      ⟨hxMem, h0x, xx, hxx, hxxTwo⟩
    rcases ratLE_total hxMem hrMem with hxr | hrx
    · exact hxr
    · have hrxNe : r ≠ x := by
        intro hEq
        have hxxAt : RatMul r r xx := by
          rw [hEq]
          exact hxx
        have hrrEq : rr = xx :=
          RatMul_unique hrMem hrMem hrr hxxAt
        have hTwoXX : RatLT ratTwoTA xx := by
          rw [← hrrEq]
          exact hTwoRR
        have hEqTwo : xx = ratTwoTA :=
          ratLE_antisymm
            (funcFoundational_value_mem ratMulGraph_isFunc hxx)
            ratTwoTA_mem_rationalsTA hxxTwo.1 hTwoXX.1
        exact hxxTwo.2 hEqTwo
      have hrxLT : RatLT r x := ⟨hrx, hrxNe⟩
      have hrrxx : RatLT rr xx :=
        TA_LEM_00018_square_strict_mono_nonnegative
          hrMem hxMem h0r.1 hrxLT hrr hxx
      have hTwoXX : RatLT ratTwoTA xx :=
        ratLT_of_lt_of_le_local
          ratTwoTA_mem_rationalsTA hrrMem
          (funcFoundational_value_mem ratMulGraph_isFunc hxx)
          hTwoRR hrrxx.1
      have hEqTwo : xx = ratTwoTA :=
        ratLE_antisymm
          (funcFoundational_value_mem ratMulGraph_isFunc hxx)
          ratTwoTA_mem_rationalsTA hxxTwo.1 hTwoXX.1
      exact False.elim (hxxTwo.2 hEqTwo)

  exact ⟨r, hUpper, hrS⟩

/-! ## TA-THM-00033 -/

/-- TA-THM-00033 — el conjunto racional `S₂` no posee supremo racional. -/
theorem TA_THM_00033_sqrtTwoSet_no_rational_supremum :
    ¬ ∃ s : ZFSet.{u}, RatSupremum (sqrtTwoSet : ZFSet.{u}) s := by
  rintro ⟨s, hSup⟩
  have hs : s ∈ rationalsTA := hSup.1.1
  have hOneSet : (ratOne : ZFSet.{u}) ∈ (sqrtTwoSet : ZFSet.{u}) :=
    TA_PRO_00067_sqrtTwoSet_nonempty_bounded.{u, u, u}.1
  have hOneS : RatLE ratOne s :=
    hSup.1.2 ratOne hOneSet
  have h0s : RatLT ratZero s :=
    ratLT_of_lt_of_le_local
      ratZero_mem_rationalsTA ratOne_mem_rationalsTA hs
      ratZero_lt_one hOneS

  rcases ratMul_exists hs hs with ⟨ss, hssMem, hss⟩
  have hssNeTwo : ss ≠ ratTwoTA := by
    intro hEq
    exact TA_THM_00032_no_rational_square_two
      ⟨s, ss, hs, hss, hEq⟩

  rcases ratLE_total hssMem ratTwoTA_mem_rationalsTA with
    hssLETwo | hTwoLESS
  · have hssLTTwo : RatLT ss ratTwoTA := ⟨hssLETwo, hssNeTwo⟩
    rcases square_lt_two_gives_larger_member_local
        hs h0s hss hssLTTwo with
      ⟨t, htSet, hsT⟩
    have htS : RatLE t s := hSup.1.2 t htSet
    have hEq : s = t :=
      ratLE_antisymm hs
        (TA_DEF_00066_mem_sqrtTwoSet_iff.mp htSet).1
        hsT.1 htS
    exact hsT.2 hEq
  · have hTwoLTSS : RatLT ratTwoTA ss := by
      refine ⟨hTwoLESS, ?_⟩
      intro hEq
      exact hssNeTwo hEq.symm
    rcases two_lt_square_gives_smaller_upper_local
        hs h0s hss hTwoLTSS with
      ⟨r, hrUpper, hrS⟩
    have hsR : RatLE s r := hSup.2 r hrUpper
    have hEq : r = s :=
      ratLE_antisymm hrUpper.1 hs hrS.1 hsR
    exact hrS.2 hEq

end TratadoAnalisis.Rationals.NoSupremumSqrtTwo
