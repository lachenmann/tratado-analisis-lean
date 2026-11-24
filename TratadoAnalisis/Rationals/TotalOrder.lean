import TratadoAnalisis.Rationals.OrderDefinition

namespace TratadoAnalisis.Rationals.TotalOrder

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
open TratadoAnalisis.Rationals.PositiveDenominator
open TratadoAnalisis.Rationals.OrderWellDefined
open TratadoAnalisis.Rationals.OrderDefinition

/-!
# TA-LEAN-0003 — D2b

Orden total relacional sobre los racionales y criterio de comparación estricta.

No se crean instancias de orden ni se prueban compatibilidades algebraicas.
-/

theorem ratLE_refl {q : ZFSet}
    (hq : q ∈ rationalsTA) :
    RatLE q q := by
  rcases TA_LEM_00013_positive_denominator hq with
    ⟨a, n, ha, hn, hbPos, hqClass⟩
  let b := intPositiveForm n
  have hbI : b ∈ integersTA :=
    intPositiveForm_mem_integersTA n
  have hbNZ : b ∈ intNonzeroTA :=
    mem_intNonzeroTA_of_positive hbI hbPos
  rcases intMul_exists_local ha hbI with
    ⟨ab, habI, hab⟩
  rcases intMul_exists_local hbI ha with
    ⟨ba, hbaI, hba⟩
  have habEq : ab = ba :=
    intMul_comm ha hbI hab hba
  have hLE : IntLE ab ba := by
    rw [habEq]
    exact intLE_refl hbaI
  rw [hqClass]
  exact (TA_PRO_00064_ratLE_classes_iff
    ha hbNZ ha hbNZ hbPos hbPos hab hba).mpr hLE

theorem ratLE_antisymm {q r : ZFSet}
    (hq : q ∈ rationalsTA)
    (hr : r ∈ rationalsTA)
    (hqr : RatLE q r)
    (hrq : RatLE r q) :
    q = r := by
  rcases TA_LEM_00013_positive_denominator hq with
    ⟨a, m, ha, hm, hbPos, hqClass⟩
  rcases TA_LEM_00013_positive_denominator hr with
    ⟨c, n, hc, hn, hdPos, hrClass⟩
  let b := intPositiveForm m
  let d := intPositiveForm n
  have hbI : b ∈ integersTA := intPositiveForm_mem_integersTA m
  have hdI : d ∈ integersTA := intPositiveForm_mem_integersTA n
  have hbNZ := mem_intNonzeroTA_of_positive hbI hbPos
  have hdNZ := mem_intNonzeroTA_of_positive hdI hdPos

  rcases intMul_exists_local ha hdI with ⟨ad, hadI, had⟩
  rcases intMul_exists_local hbI hc with ⟨bc, hbcI, hbc⟩
  rcases intMul_exists_local hc hbI with ⟨cb, _hcbI, hcb₀⟩
  rcases intMul_exists_local hdI ha with ⟨da, _hdaI, hda₀⟩
  have hbcCb : bc = cb := intMul_comm hbI hc hbc hcb₀
  have hadDa : ad = da := intMul_comm ha hdI had hda₀
  have hcb : IntMul c b bc := by
    rw [hbcCb]
    exact hcb₀
  have hda : IntMul d a ad := by
    rw [hadDa]
    exact hda₀

  rw [hqClass, hrClass] at hqr hrq
  have hForward : IntLE ad bc :=
    (TA_PRO_00064_ratLE_classes_iff
      ha hbNZ hc hdNZ hbPos hdPos had hbc).mp hqr
  have hBackward : IntLE bc ad :=
    (TA_PRO_00064_ratLE_classes_iff
      hc hdNZ ha hbNZ hdPos hbPos hcb hda).mp hrq
  have hProducts : ad = bc :=
    intLE_antisymm hadI hbcI hForward hBackward
  have hClasses :
      ratClass (ZFSet.pair a b) =
        ratClass (ZFSet.pair c d) :=
    (TA_PRO_00053_ratClass_pairs_eq_iff
      ha hbNZ hc hdNZ).mpr
      ⟨ad, bc, had, hbc, hProducts⟩
  exact hqClass.trans (hClasses.trans hrClass.symm)

theorem ratLE_trans {q r s : ZFSet}
    (hq : q ∈ rationalsTA)
    (hr : r ∈ rationalsTA)
    (hs : s ∈ rationalsTA)
    (hqr : RatLE q r)
    (hrs : RatLE r s) :
    RatLE q s := by
  rcases TA_LEM_00013_positive_denominator hq with
    ⟨a, l, ha, hl, hbPos, hqClass⟩
  rcases TA_LEM_00013_positive_denominator hr with
    ⟨c, m, hc, hm, hdPos, hrClass⟩
  rcases TA_LEM_00013_positive_denominator hs with
    ⟨e, n, he, hn, hfPos, hsClass⟩
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
  rcases intMul_exists_local hc hfI with ⟨cf, hcfI, hcf⟩
  rcases intMul_exists_local hdI he with ⟨de, hdeI, hde⟩
  rcases intMul_exists_local ha hfI with ⟨af, hafI, haf⟩
  rcases intMul_exists_local hbI he with ⟨be, hbeI, hbe⟩

  rw [hqClass, hrClass] at hqr
  rw [hrClass, hsClass] at hrs
  have hADLEBC : IntLE ad bc :=
    (TA_PRO_00064_ratLE_classes_iff
      ha hbNZ hc hdNZ hbPos hdPos had hbc).mp hqr
  have hCFLEDE : IntLE cf de :=
    (TA_PRO_00064_ratLE_classes_iff
      hc hdNZ he hfNZ hdPos hfPos hcf hde).mp hrs

  rcases intMul_exists_local hadI hfI with
    ⟨adf, hadfI, hadf⟩
  rcases intMul_exists_local hbcI hfI with
    ⟨bcf, hbcfI, hbcf⟩
  have hScaledF : IntLE adf bcf :=
    (TA_LEM_00011_intLE_mul_positive_iff
      hadI hbcI hfI hfPos hadf hbcf).mp hADLEBC

  rcases intMul_exists_local hcfI hbI with
    ⟨cfb, hcfbI, hcfb⟩
  rcases intMul_exists_local hdeI hbI with
    ⟨deb, hdebI, hdeb⟩
  have hScaledB : IntLE cfb deb :=
    (TA_LEM_00011_intLE_mul_positive_iff
      hcfI hdeI hbI hbPos hcfb hdeb).mp hCFLEDE

  rcases intMul_exists_local hbI hcfI with
    ⟨b_cf, _hb_cfI, hb_cf⟩
  have hBCFEq : bcf = b_cf :=
    intMul_assoc hbI hc hfI hbc hbcf hcf hb_cf
  have hCFBEq : cfb = b_cf :=
    intMul_comm hcfI hbI hcfb hb_cf
  have hMiddle : bcf = cfb :=
    hBCFEq.trans hCFBEq.symm
  have hScaledB' : IntLE bcf deb := by
    rw [hMiddle]
    exact hScaledB
  have hTriple : IntLE adf deb :=
    intLE_trans hadfI hbcfI hdebI hScaledF hScaledB'

  rcases intMul_exists_local hdI ha with
    ⟨da, _hdaI, hda⟩
  have hADDA : ad = da :=
    intMul_comm ha hdI had hda
  have hDAF' : IntMul da f adf := by
    rw [← hADDA]
    exact hadf
  rcases intMul_exists_local hdI hafI with
    ⟨d_af, hd_afI, hd_af⟩
  have hADFEq : adf = d_af :=
    intMul_assoc hdI ha hfI hda hDAF' haf hd_af

  rcases intMul_exists_local he hbI with
    ⟨eb, _hebI, heb⟩
  have hEBBE : eb = be :=
    intMul_comm he hbI heb hbe
  rcases intMul_exists_local hdI hbeI with
    ⟨d_be, hd_beI, hd_be⟩
  have hd_eb : IntMul d eb d_be := by
    rw [hEBBE]
    exact hd_be
  have hDEBEq : deb = d_be :=
    intMul_assoc hdI he hbI hde hdeb heb hd_eb

  have hCommonLeft : IntLE d_af d_be := by
    rw [← hADFEq, ← hDEBEq]
    exact hTriple

  rcases intMul_exists_local hafI hdI with
    ⟨af_d, _haf_dI, haf_d⟩
  rcases intMul_exists_local hbeI hdI with
    ⟨be_d, _hbe_dI, hbe_d⟩
  have hDAFComm : d_af = af_d :=
    intMul_comm hdI hafI hd_af haf_d
  have hDBEComm : d_be = be_d :=
    intMul_comm hdI hbeI hd_be hbe_d
  have hCancelable : IntLE af_d be_d := by
    rw [← hDAFComm, ← hDBEComm]
    exact hCommonLeft
  have hAFLEBE : IntLE af be :=
    (TA_LEM_00011_intLE_mul_positive_iff
      hafI hbeI hdI hdPos haf_d hbe_d).mpr hCancelable

  rw [hqClass, hsClass]
  exact (TA_PRO_00064_ratLE_classes_iff
    ha hbNZ he hfNZ hbPos hfPos haf hbe).mpr hAFLEBE

theorem ratLE_total {q r : ZFSet}
    (hq : q ∈ rationalsTA)
    (hr : r ∈ rationalsTA) :
    RatLE q r ∨ RatLE r q := by
  rcases TA_LEM_00013_positive_denominator hq with
    ⟨a, m, ha, hm, hbPos, hqClass⟩
  rcases TA_LEM_00013_positive_denominator hr with
    ⟨c, n, hc, hn, hdPos, hrClass⟩
  let b := intPositiveForm m
  let d := intPositiveForm n
  have hbI : b ∈ integersTA := intPositiveForm_mem_integersTA m
  have hdI : d ∈ integersTA := intPositiveForm_mem_integersTA n
  have hbNZ := mem_intNonzeroTA_of_positive hbI hbPos
  have hdNZ := mem_intNonzeroTA_of_positive hdI hdPos

  rcases intMul_exists_local ha hdI with ⟨ad, hadI, had⟩
  rcases intMul_exists_local hbI hc with ⟨bc, hbcI, hbc⟩
  rcases intMul_exists_local hc hbI with ⟨cb, _hcbI, hcb₀⟩
  rcases intMul_exists_local hdI ha with ⟨da, _hdaI, hda₀⟩
  have hbcCb : bc = cb := intMul_comm hbI hc hbc hcb₀
  have hadDa : ad = da := intMul_comm ha hdI had hda₀
  have hcb : IntMul c b bc := by
    rw [hbcCb]
    exact hcb₀
  have hda : IntMul d a ad := by
    rw [hadDa]
    exact hda₀

  rcases intLE_total hadI hbcI with h | h
  · left
    rw [hqClass, hrClass]
    exact (TA_PRO_00064_ratLE_classes_iff
      ha hbNZ hc hdNZ hbPos hdPos had hbc).mpr h
  · right
    rw [hrClass, hqClass]
    exact (TA_PRO_00064_ratLE_classes_iff
      hc hdNZ ha hbNZ hdPos hbPos hcb hda).mpr h

theorem TA_THM_00029_total_order :
    (∀ q : ZFSet, q ∈ rationalsTA → RatLE q q) ∧
    (∀ q r : ZFSet,
      q ∈ rationalsTA → r ∈ rationalsTA →
      RatLE q r → RatLE r q → q = r) ∧
    (∀ q r s : ZFSet,
      q ∈ rationalsTA → r ∈ rationalsTA → s ∈ rationalsTA →
      RatLE q r → RatLE r s → RatLE q s) ∧
    (∀ q r : ZFSet,
      q ∈ rationalsTA → r ∈ rationalsTA →
      RatLE q r ∨ RatLE r q) := by
  exact ⟨fun _ => ratLE_refl,
    fun _ _ => ratLE_antisymm,
    fun _ _ _ => ratLE_trans,
    fun _ _ => ratLE_total⟩

def RatLT (x y : ZFSet) : Prop :=
  RatLE x y ∧ x ≠ y

theorem TA_COR_00009_ratLT_classes_iff
    {a b c d ad bc : ZFSet}
    (ha : a ∈ integersTA)
    (hb : b ∈ intNonzeroTA)
    (hc : c ∈ integersTA)
    (hd : d ∈ intNonzeroTA)
    (hbPos : IntLT intZero b)
    (hdPos : IntLT intZero d)
    (had : IntMul a d ad)
    (hbc : IntMul b c bc) :
    RatLT
      (ratClass (ZFSet.pair a b))
      (ratClass (ZFSet.pair c d)) ↔
    IntLT ad bc := by
  have hbI : b ∈ integersTA := (mem_intNonzeroTA_iff.mp hb).1
  have hdI : d ∈ integersTA := (mem_intNonzeroTA_iff.mp hd).1

  have hClassEq :
      ratClass (ZFSet.pair a b) =
        ratClass (ZFSet.pair c d) ↔
      ad = bc := by
    rw [TA_PRO_00053_ratClass_pairs_eq_iff ha hb hc hd]
    constructor
    · rintro ⟨u, v, hu, hv, huv⟩
      have huEq : u = ad :=
        IntMul_unique ha hdI hu had
      have hvEq : v = bc :=
        IntMul_unique hbI hc hv hbc
      exact huEq.symm.trans (huv.trans hvEq)
    · intro h
      exact ⟨ad, bc, had, hbc, h⟩

  constructor
  · rintro ⟨hLE, hNe⟩
    exact ⟨
      (TA_PRO_00064_ratLE_classes_iff
        ha hb hc hd hbPos hdPos had hbc).mp hLE,
      (not_congr hClassEq).mp hNe⟩
  · rintro ⟨hLE, hNe⟩
    exact ⟨
      (TA_PRO_00064_ratLE_classes_iff
        ha hb hc hd hbPos hdPos had hbc).mpr hLE,
      (not_congr hClassEq).mpr hNe⟩

end TratadoAnalisis.Rationals.TotalOrder
