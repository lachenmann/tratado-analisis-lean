import TratadoAnalisis.Rationals.TotalOrder

namespace TratadoAnalisis.Rationals.OrderedFieldCompatibility

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
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.OrderPrep
open TratadoAnalisis.Rationals.PositiveDenominator
open TratadoAnalisis.Rationals.OrderWellDefined
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder

/-!
# TA-LEAN-0003 — D2c

Compatibilidad del orden racional con suma y producto por un racional no
negativo, y preservación y reflexión del orden por el embedding entero.

No se crean instancias algebraicas ni de orden.
-/

theorem intOne_pos : IntLT intZero intOne := by
  simpa [intPositiveForm, intOne] using
    (intPositiveForm_pos (n := 1) Nat.one_ne_zero)

theorem ratLE_add_compat
    {x y z xz yz : ZFSet}
    (hx : x ∈ rationalsTA)
    (hy : y ∈ rationalsTA)
    (hz : z ∈ rationalsTA)
    (hxy : RatLE x y)
    (hxz : RatAdd x z xz)
    (hyz : RatAdd y z yz) :
    RatLE xz yz := by
  rcases TA_LEM_00013_positive_denominator hx with
    ⟨a, l, ha, hl, hbPos, hxClass⟩
  rcases TA_LEM_00013_positive_denominator hy with
    ⟨c, m, hc, hm, hdPos, hyClass⟩
  rcases TA_LEM_00013_positive_denominator hz with
    ⟨e, n, he, hn, hfPos, hzClass⟩
  let b := intPositiveForm l
  let d := intPositiveForm m
  let f := intPositiveForm n
  have hbI : b ∈ integersTA := intPositiveForm_mem_integersTA l
  have hdI : d ∈ integersTA := intPositiveForm_mem_integersTA m
  have hfI : f ∈ integersTA := intPositiveForm_mem_integersTA n
  have hbNZ := mem_intNonzeroTA_of_positive hbI hbPos
  have hdNZ := mem_intNonzeroTA_of_positive hdI hdPos
  have hfNZ := mem_intNonzeroTA_of_positive hfI hfPos

  rcases intMul_exists_local ha hdI with ⟨ad, hadI, had⟩
  rcases intMul_exists_local hbI hc with ⟨bc, hbcI, hbc⟩
  rw [hxClass, hyClass] at hxy
  have hADLEBC : IntLE ad bc :=
    (TA_PRO_00064_ratLE_classes_iff
      ha hbNZ hc hdNZ hbPos hdPos had hbc).mp hxy

  rcases intMul_exists_local ha hfI with ⟨af, hafI, haf⟩
  rcases intMul_exists_local hbI he with ⟨be, hbeI, hbe⟩
  rcases intAdd_exists_local hafI hbeI with ⟨sumX, hsumXI, hsumX⟩
  rcases intMul_exists_local hbI hfI with ⟨bf, hbfI, hbf⟩
  have hbfPos := TA_LEM_00012_positive_mul hbI hfI hbPos hfPos hbf
  have hbfNZ := mem_intNonzeroTA_of_positive hbfI hbfPos

  rcases intMul_exists_local hc hfI with ⟨cf, hcfI, hcf⟩
  rcases intMul_exists_local hdI he with ⟨de, hdeI, hde⟩
  rcases intAdd_exists_local hcfI hdeI with ⟨sumY, hsumYI, hsumY⟩
  rcases intMul_exists_local hdI hfI with ⟨df, hdfI, hdf⟩
  have hdfPos := TA_LEM_00012_positive_mul hdI hfI hdPos hfPos hdf
  have hdfNZ := mem_intNonzeroTA_of_positive hdfI hdfPos

  rw [hxClass, hzClass] at hxz
  rw [hyClass, hzClass] at hyz
  have hxzEq :
      xz = ratClass (ZFSet.pair sumX bf) :=
    (ratAddGraph_classes_value_iff
      ha hbNZ he hfNZ haf hbe hsumX hbf).mp hxz
  have hyzEq :
      yz = ratClass (ZFSet.pair sumY df) :=
    (ratAddGraph_classes_value_iff
      hc hdNZ he hfNZ hcf hde hsumY hdf).mp hyz

  rcases intMul_exists_local hfI hfI with ⟨f2, hf2I, hf2⟩
  have hf2Pos := TA_LEM_00012_positive_mul hfI hfI hfPos hfPos hf2
  rcases intMul_exists_local hadI hf2I with ⟨adf2, hadf2I, hadf2⟩
  rcases intMul_exists_local hbcI hf2I with ⟨bcf2, hbcf2I, hbcf2⟩
  have hScaled : IntLE adf2 bcf2 :=
    (TA_LEM_00011_intLE_mul_positive_iff
      hadI hbcI hf2I hf2Pos hadf2 hbcf2).mp hADLEBC

  rcases intMul_exists_local hbI hdI with ⟨bd, hbdI, hbd⟩
  rcases intMul_exists_local he hfI with ⟨ef, hefI, hef⟩
  rcases intMul_exists_local hbdI hefI with ⟨common, hcommonI, hcommon⟩
  rcases intAdd_exists_local hadf2I hcommonI with
    ⟨lower, hlowerI, hlower⟩
  rcases intAdd_exists_local hbcf2I hcommonI with
    ⟨upper, hupperI, hupper⟩
  have hAdded : IntLE lower upper :=
    intLE_add_compat hadf2I hbcf2I hcommonI
      hScaled hlower hupper

  rcases intMul_exists_local hsumXI hdfI with
    ⟨leftCross, hleftCrossI, hleftCross⟩
  rcases intMul_exists_local hafI hdfI with
    ⟨afdf, hafdfI, hafdf⟩
  rcases intMul_exists_local hbeI hdfI with
    ⟨bedf, hbedfI, hbedf⟩
  rcases intAdd_exists_local hafdfI hbedfI with
    ⟨leftParts, hleftPartsI, hleftParts⟩
  have hLeftDist : leftCross = leftParts :=
    intAdd_mul_right hafI hbeI hdfI
      hsumX hleftCross hafdf hbedf hleftParts
  have hAFDF : afdf = adf2 :=
    intPairProducts_exchange_middle
      ha hfI hdI hfI
      haf hdf had hf2
      hafdf hadf2
  have hBEDF : bedf = common :=
    intPairProducts_exchange_middle
      hbI he hdI hfI
      hbe hdf hbd hef
      hbedf hcommon
  have hLeftParts' : IntAdd adf2 common leftParts := by
    rw [← hAFDF, ← hBEDF]
    exact hleftParts
  have hLowerParts : lower = leftParts :=
    IntAdd_unique hadf2I hcommonI hlower hLeftParts'
  have hLeftLower : leftCross = lower :=
    hLeftDist.trans hLowerParts.symm

  rcases intMul_exists_local hbfI hsumYI with
    ⟨rightCross, hrightCrossI, hrightCross⟩
  rcases intMul_exists_local hbfI hcfI with
    ⟨bfcf, hbfcfI, hbfcf⟩
  rcases intMul_exists_local hbfI hdeI with
    ⟨bfde, hbfdeI, hbfde⟩
  rcases intAdd_exists_local hbfcfI hbfdeI with
    ⟨rightParts, hrightPartsI, hrightParts⟩
  have hRightDist : rightCross = rightParts :=
    intMul_add_left hbfI hcfI hdeI
      hsumY hrightCross hbfcf hbfde hrightParts
  have hBFCF : bfcf = bcf2 :=
    intPairProducts_exchange_middle
      hbI hfI hc hfI
      hbf hcf hbc hf2
      hbfcf hbcf2
  rcases intMul_exists_local hfI he with ⟨fe, hfeI, hfe⟩
  have hEFFE : ef = fe :=
    intMul_comm he hfI hef hfe
  have hCommonFE : IntMul bd fe common := by
    rw [← hEFFE]
    exact hcommon
  have hBFDE : bfde = common :=
    intPairProducts_exchange_middle
      hbI hfI hdI he
      hbf hde hbd hfe
      hbfde hCommonFE
  have hRightParts' : IntAdd bcf2 common rightParts := by
    rw [← hBFCF, ← hBFDE]
    exact hrightParts
  have hUpperParts : upper = rightParts :=
    IntAdd_unique hbcf2I hcommonI hupper hRightParts'
  have hRightUpper : rightCross = upper :=
    hRightDist.trans hUpperParts.symm

  have hCross : IntLE leftCross rightCross := by
    rw [hLeftLower, hRightUpper]
    exact hAdded
  rw [hxzEq, hyzEq]
  exact (TA_PRO_00064_ratLE_classes_iff
    hsumXI hbfNZ hsumYI hdfNZ
    hbfPos hdfPos hleftCross hrightCross).mpr hCross

theorem ratLE_mul_nonnegative_compat
    {x y z xz yz : ZFSet}
    (hx : x ∈ rationalsTA)
    (hy : y ∈ rationalsTA)
    (hz : z ∈ rationalsTA)
    (hxy : RatLE x y)
    (hz0 : RatLE ratZero z)
    (hxz : RatMul x z xz)
    (hyz : RatMul y z yz) :
    RatLE xz yz := by
  rcases TA_LEM_00013_positive_denominator hx with
    ⟨a, l, ha, hl, hbPos, hxClass⟩
  rcases TA_LEM_00013_positive_denominator hy with
    ⟨c, m, hc, hm, hdPos, hyClass⟩
  rcases TA_LEM_00013_positive_denominator hz with
    ⟨e, n, he, hn, hfPos, hzClass⟩
  let b := intPositiveForm l
  let d := intPositiveForm m
  let f := intPositiveForm n
  have hbI : b ∈ integersTA := intPositiveForm_mem_integersTA l
  have hdI : d ∈ integersTA := intPositiveForm_mem_integersTA m
  have hfI : f ∈ integersTA := intPositiveForm_mem_integersTA n
  have hbNZ := mem_intNonzeroTA_of_positive hbI hbPos
  have hdNZ := mem_intNonzeroTA_of_positive hdI hdPos
  have hfNZ := mem_intNonzeroTA_of_positive hfI hfPos

  rcases intMul_exists_local ha hdI with ⟨ad, hadI, had⟩
  rcases intMul_exists_local hbI hc with ⟨bc, hbcI, hbc⟩
  rw [hxClass, hyClass] at hxy
  have hADLEBC : IntLE ad bc :=
    (TA_PRO_00064_ratLE_classes_iff
      ha hbNZ hc hdNZ hbPos hdPos had hbc).mp hxy

  rcases intMul_exists_local intZero_mem_integersTA hfI with
    ⟨zeroF, hzeroFI, hzeroF⟩
  rcases intMul_exists_local intOne_mem_integersTA he with
    ⟨oneE, honeEI, honeE⟩
  rw [hzClass] at hz0
  have hZeroFE : IntLE zeroF oneE :=
    (TA_PRO_00064_ratLE_classes_iff
      intZero_mem_integersTA intOne_mem_intNonzeroTA
      he hfNZ intOne_pos hfPos hzeroF honeE).mp
      (by simpa [ratZero] using hz0)
  have hZeroFValue : zeroF = intZero :=
    intMul_zero_left hfI hzeroF
  have hOneEValue : oneE = e :=
    intMul_one_left he honeE
  have hZeroE : IntLE intZero e := by
    rw [hZeroFValue, hOneEValue] at hZeroFE
    exact hZeroFE

  rcases intMul_exists_local he hfI with ⟨ef, hefI, hef⟩
  have hZeroFEF : IntLE zeroF ef :=
    intLE_mul_nonnegative_compat
      intZero_mem_integersTA he hfI
      hZeroE hfPos.1 hzeroF hef
  have hZeroEF : IntLE intZero ef := by
    rw [hZeroFValue] at hZeroFEF
    exact hZeroFEF

  rcases intMul_exists_local hadI hefI with
    ⟨ad_ef, had_efI, had_ef⟩
  rcases intMul_exists_local hbcI hefI with
    ⟨bc_ef, hbc_efI, hbc_ef⟩
  have hScaled : IntLE ad_ef bc_ef :=
    intLE_mul_nonnegative_compat
      hadI hbcI hefI hADLEBC hZeroEF had_ef hbc_ef

  rcases intMul_exists_local ha he with ⟨ae, haeI, hae⟩
  rcases intMul_exists_local hbI hfI with ⟨bf, hbfI, hbf⟩
  rcases intMul_exists_local hc he with ⟨ce, hceI, hce⟩
  rcases intMul_exists_local hdI hfI with ⟨df, hdfI, hdf⟩
  have hbfPos := TA_LEM_00012_positive_mul hbI hfI hbPos hfPos hbf
  have hdfPos := TA_LEM_00012_positive_mul hdI hfI hdPos hfPos hdf
  have hbfNZ := mem_intNonzeroTA_of_positive hbfI hbfPos
  have hdfNZ := mem_intNonzeroTA_of_positive hdfI hdfPos

  rw [hxClass, hzClass] at hxz
  rw [hyClass, hzClass] at hyz
  have hxzEq :
      xz = ratClass (ZFSet.pair ae bf) :=
    (ratMulGraph_classes_value_iff
      ha hbNZ he hfNZ hae hbf).mp hxz
  have hyzEq :
      yz = ratClass (ZFSet.pair ce df) :=
    (ratMulGraph_classes_value_iff
      hc hdNZ he hfNZ hce hdf).mp hyz

  rcases intMul_exists_local haeI hdfI with
    ⟨leftCross, hleftCrossI, hleftCross⟩
  have hLeftEq : leftCross = ad_ef :=
    intPairProducts_exchange_middle
      ha he hdI hfI
      hae hdf had hef
      hleftCross had_ef

  rcases intMul_exists_local hbfI hceI with
    ⟨rightCross, hrightCrossI, hrightCross⟩
  rcases intMul_exists_local hfI he with ⟨fe, hfeI, hfe⟩
  have hEFFE : ef = fe :=
    intMul_comm he hfI hef hfe
  have hBCFE : IntMul bc fe bc_ef := by
    rw [← hEFFE]
    exact hbc_ef
  have hRightEq : rightCross = bc_ef :=
    intPairProducts_exchange_middle
      hbI hfI hc he
      hbf hce hbc hfe
      hrightCross hBCFE

  have hCross : IntLE leftCross rightCross := by
    rw [hLeftEq, hRightEq]
    exact hScaled
  rw [hxzEq, hyzEq]
  exact (TA_PRO_00064_ratLE_classes_iff
    haeI hbfNZ hceI hdfNZ
    hbfPos hdfPos hleftCross hrightCross).mpr hCross

theorem TA_PRO_00065_order_compatibility :
    (∀ {x y z xz yz : ZFSet},
      x ∈ rationalsTA → y ∈ rationalsTA → z ∈ rationalsTA →
      RatLE x y →
      RatAdd x z xz → RatAdd y z yz →
      RatLE xz yz) ∧
    (∀ {x y z xz yz : ZFSet},
      x ∈ rationalsTA → y ∈ rationalsTA → z ∈ rationalsTA →
      RatLE x y → RatLE ratZero z →
      RatMul x z xz → RatMul y z yz →
      RatLE xz yz) := by
  constructor
  · intro x y z xz yz hx hy hz hxy hxz hyz
    exact ratLE_add_compat hx hy hz hxy hxz hyz
  · intro x y z xz yz hx hy hz hxy hz0 hxz hyz
    exact ratLE_mul_nonnegative_compat hx hy hz hxy hz0 hxz hyz

theorem TA_PRO_00066_ratEmbed_order_iff
    {a c ja jc : ZFSet}
    (ha : a ∈ integersTA)
    (hc : c ∈ integersTA)
    (hja : ZFSet.pair a ja ∈ ratEmbedGraph)
    (hjc : ZFSet.pair c jc ∈ ratEmbedGraph) :
    IntLE a c ↔ RatLE ja jc := by
  have hjaEq : ja = ratClass (ZFSet.pair a intOne) :=
    (mem_ratEmbedGraph.mp hja).2.2.2
  have hjcEq : jc = ratClass (ZFSet.pair c intOne) :=
    (mem_ratEmbedGraph.mp hjc).2.2.2
  rcases intMul_exists_local ha intOne_mem_integersTA with
    ⟨aOne, _haOneI, haOne⟩
  rcases intMul_exists_local intOne_mem_integersTA hc with
    ⟨oneC, _honeCI, honeC⟩
  have haOneValue : aOne = a := intMul_one_right ha haOne
  have honeCValue : oneC = c := intMul_one_left hc honeC
  rw [hjaEq, hjcEq]
  constructor
  · intro h
    apply (TA_PRO_00064_ratLE_classes_iff
      ha intOne_mem_intNonzeroTA hc intOne_mem_intNonzeroTA
      intOne_pos intOne_pos haOne honeC).mpr
    rw [haOneValue, honeCValue]
    exact h
  · intro h
    have hCross :=
      (TA_PRO_00064_ratLE_classes_iff
        ha intOne_mem_intNonzeroTA hc intOne_mem_intNonzeroTA
        intOne_pos intOne_pos haOne honeC).mp h
    rw [haOneValue, honeCValue] at hCross
    exact hCross

end TratadoAnalisis.Rationals.OrderedFieldCompatibility
