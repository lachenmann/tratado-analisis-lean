import TratadoAnalisis.Rationals.IntegerPrep

/-!
# TA-LEAN-0003 — C1b

Relación de equivalencia racional, clases y cociente conjuntista. No se
introducen todavía operaciones ni orden sobre los racionales.
-/

namespace TratadoAnalisis.Rationals.Construction

open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Integers.Construction
open TratadoAnalisis.Integers.Operations
open TratadoAnalisis.Integers.Multiplication
open TratadoAnalisis.Integers.Algebra
open TratadoAnalisis.Rationals.IntegerPrep

/-! ## Igualdad relacional de productos enteros -/

def IntProductEq (a b c d : ZFSet) : Prop :=
  ∃ u v : ZFSet,
    IntMul a b u ∧
    IntMul c d v ∧
    u = v

theorem intMul_exists
    {x y : ZFSet}
    (hx : x ∈ integersTA)
    (hy : y ∈ integersTA) :
    ∃ z : ZFSet, z ∈ integersTA ∧ IntMul x y z := by
  have hInput :
      ZFSet.pair x y ∈
        cartesianProductFoundational integersTA integersTA :=
    mem_cartesianProductFoundational.mpr ⟨hx, hy⟩
  rcases intMulGraph_isFunc.2 (ZFSet.pair x y) hInput with
    ⟨z, hz, _hzUnique⟩
  exact ⟨z, hz.1, hz.2⟩

theorem intProductEq_symm
    {a b c d : ZFSet}
    (h : IntProductEq a b c d) :
    IntProductEq c d a b := by
  rcases h with ⟨u, v, hab, hcd, huv⟩
  exact ⟨v, u, hcd, hab, huv.symm⟩

theorem intProductEq_transport
    {a b c d a' b' c' d' : ZFSet}
    (ha : a = a')
    (hb : b = b')
    (hc : c = c')
    (hd : d = d')
    (h : IntProductEq a b c d) :
    IntProductEq a' b' c' d' := by
  subst a'
  subst b'
  subst c'
  subst d'
  exact h

theorem intProductEq_commute
    {a b c d : ZFSet}
    (ha : a ∈ integersTA)
    (hb : b ∈ integersTA)
    (hc : c ∈ integersTA)
    (hd : d ∈ integersTA)
    (h : IntProductEq a b c d) :
    IntProductEq b a d c := by
  rcases h with ⟨u, v, hab, hcd, huv⟩
  rcases intMul_exists hb ha with ⟨uba, huba, hba⟩
  rcases intMul_exists hd hc with ⟨udc, hudc, hdc⟩
  have hu : u = uba := intMul_comm ha hb hab hba
  have hv : v = udc := intMul_comm hc hd hcd hdc
  exact ⟨uba, udc, hba, hdc, hu.symm.trans (huv.trans hv)⟩

theorem intProductEq_comm
    {a b : ZFSet}
    (ha : a ∈ integersTA)
    (hb : b ∈ integersTA) :
    IntProductEq a b b a := by
  rcases intMul_exists ha hb with ⟨uab, huab, hab⟩
  rcases intMul_exists hb ha with ⟨uba, huba, hba⟩
  exact ⟨uab, uba, hab, hba, intMul_comm ha hb hab hba⟩

/-! ## TA-DEF-00050 — relación racional -/

def ratRel (p q : ZFSet) : Prop :=
  ∃ a b c d : ZFSet,
    a ∈ integersTA ∧
    b ∈ intNonzeroTA ∧
    c ∈ integersTA ∧
    d ∈ intNonzeroTA ∧
    p = ZFSet.pair a b ∧
    q = ZFSet.pair c d ∧
    IntProductEq a d b c

theorem ratRel_pairs_iff
    {a b c d : ZFSet}
    (ha : a ∈ integersTA)
    (hb : b ∈ intNonzeroTA)
    (hc : c ∈ integersTA)
    (hd : d ∈ intNonzeroTA) :
    ratRel (ZFSet.pair a b) (ZFSet.pair c d) ↔
    IntProductEq a d b c := by
  constructor
  · rintro ⟨a', b', c', d', _ha', _hb', _hc', _hd', hp, hq, hProd⟩
    rcases ZFSet.pair_injective hp with ⟨haa, hbb⟩
    rcases ZFSet.pair_injective hq with ⟨hcc, hdd⟩
    subst a'
    subst b'
    subst c'
    subst d'
    exact hProd
  · intro hProd
    exact ⟨a, b, c, d, ha, hb, hc, hd, rfl, rfl, hProd⟩

/-! ## TA-PRO-00051 — equivalencia -/

theorem ratRel_refl
    {p : ZFSet}
    (hp : p ∈ ratDomain) :
    ratRel p p := by
  rcases mem_ratDomain_iff.mp hp with ⟨a, b, ha, hb, rfl⟩
  have hbInt : b ∈ integersTA := (mem_intNonzeroTA_iff.mp hb).1
  apply (ratRel_pairs_iff ha hb ha hb).mpr
  exact intProductEq_comm ha hbInt

theorem ratRel_symm
    {p q : ZFSet}
    (_hp : p ∈ ratDomain)
    (_hq : q ∈ ratDomain)
    (hpq : ratRel p q) :
    ratRel q p := by
  rcases hpq with
    ⟨a, b, c, d, ha, hb, hc, hd, rfl, rfl, hProd⟩
  have hbInt : b ∈ integersTA := (mem_intNonzeroTA_iff.mp hb).1
  have hdInt : d ∈ integersTA := (mem_intNonzeroTA_iff.mp hd).1
  refine ⟨c, d, a, b, hc, hd, ha, hb, rfl, rfl, ?_⟩
  exact intProductEq_symm
    (intProductEq_commute ha hdInt hbInt hc hProd)

/-- Núcleo algebraico de la transitividad racional. El factor cancelado es
exactamente el denominador intermedio `d`. -/
theorem intProductEq_fraction_trans
    {a b c d e f : ZFSet}
    (ha : a ∈ integersTA)
    (hb : b ∈ integersTA)
    (hc : c ∈ integersTA)
    (hd : d ∈ integersTA)
    (he : e ∈ integersTA)
    (hf : f ∈ integersTA)
    (hd0 : d ≠ intZero)
    (h₁ : IntProductEq a d b c)
    (h₂ : IntProductEq c f d e) :
    IntProductEq a f b e := by
  rcases h₁ with ⟨ad, bc, had, hbc, hadbc⟩
  rcases h₂ with ⟨cf, de, hcf, hde, hcfde⟩
  rcases intMul_exists ha hf with ⟨af, hafMem, haf⟩
  rcases intMul_exists hb he with ⟨be, hbeMem, hbe⟩
  rcases intMul_exists hd hafMem with ⟨daf, hdafMem, hdaf⟩

  rcases intMul_exists hd ha with ⟨da, hdaMem, hda⟩
  rcases intMul_exists hdaMem hf with ⟨left, hleftMem, hleft⟩
  have hLeftAssoc : left = daf :=
    intMul_assoc hd ha hf hda hleft haf hdaf
  have hADcomm : ad = da := intMul_comm ha hd had hda
  have hADf : IntMul ad f left := by
    rw [hADcomm]
    exact hleft
  have hBCf : IntMul bc f left := by
    rw [← hadbc]
    exact hADf

  rcases intMul_exists hb (funcFoundational_value_mem intMulGraph_isFunc hcf) with
    ⟨bcf, hbcfMem, hbcf⟩
  have hMiddleLeft : left = bcf :=
    intMul_assoc hb hc hf hbc hBCf hcf hbcf
  have hBDE : IntMul b de bcf := by
    rw [← hcfde]
    exact hbcf

  rcases intMul_exists hb hd with ⟨bd, hbdMem, hbd⟩
  rcases intMul_exists hbdMem he with ⟨right, hrightMem, hright⟩
  have hMiddleRight : right = bcf :=
    intMul_assoc hb hd he hbd hright hde hBDE
  rcases intMul_exists hd hb with ⟨db, hdbMem, hdb⟩
  have hBDcomm : bd = db := intMul_comm hb hd hbd hdb
  have hDBE : IntMul db e right := by
    rw [← hBDcomm]
    exact hright
  rcases intMul_exists hd hbeMem with ⟨dbe, hdbeMem, hdbe⟩
  have hRightAssoc : right = dbe :=
    intMul_assoc hd hb he hdb hDBE hbe hdbe

  have hProducts : daf = dbe :=
    hLeftAssoc.symm.trans
      (hMiddleLeft.trans (hMiddleRight.symm.trans hRightAssoc))
  have hdbeAtDaf : IntMul d be daf := by
    rw [hProducts]
    exact hdbe
  have hafbe : af = be :=
    TA_LEM_00009_intMul_cancel_left hd hafMem hbeMem hd0 hdaf hdbeAtDaf
  exact ⟨af, be, haf, hbe, hafbe⟩

theorem ratRel_trans
    {p q r : ZFSet}
    (_hp : p ∈ ratDomain)
    (_hq : q ∈ ratDomain)
    (_hr : r ∈ ratDomain)
    (hpq : ratRel p q)
    (hqr : ratRel q r) :
    ratRel p r := by
  rcases hpq with
    ⟨a, b, c, d, ha, hb, hc, hd, hp, hq₁, h₁⟩
  rcases hqr with
    ⟨c', d', e, f, hc', hd', he, hf, hq₂, hr, h₂⟩
  have hMiddlePair : ZFSet.pair c d = ZFSet.pair c' d' :=
    hq₁.symm.trans hq₂
  rcases ZFSet.pair_injective hMiddlePair with ⟨hcc, hdd⟩
  subst c'
  subst d'
  have hbInt : b ∈ integersTA := (mem_intNonzeroTA_iff.mp hb).1
  have hdData := mem_intNonzeroTA_iff.mp hd
  have hfInt : f ∈ integersTA := (mem_intNonzeroTA_iff.mp hf).1
  refine ⟨a, b, e, f, ha, hb, he, hf, hp, hr, ?_⟩
  exact intProductEq_fraction_trans
    ha hbInt hc hdData.1 he hfInt hdData.2 h₁ h₂

theorem TA_PRO_00051_ratRel_equivalence :
    (∀ p : ZFSet, p ∈ ratDomain → ratRel p p) ∧
    (∀ p q : ZFSet,
      p ∈ ratDomain → q ∈ ratDomain →
      ratRel p q → ratRel q p) ∧
    (∀ p q r : ZFSet,
      p ∈ ratDomain → q ∈ ratDomain → r ∈ ratDomain →
      ratRel p q → ratRel q r → ratRel p r) := by
  exact ⟨fun _ => ratRel_refl,
    fun _ _ => ratRel_symm,
    fun _ _ _ => ratRel_trans⟩

/-! ## TA-NOT-00013 y TA-DEF-00051 — clases y cociente -/

def ratClass (p : ZFSet) : ZFSet :=
  ZFSet.sep
    (fun q => ratRel p q)
    ratDomain

theorem mem_ratClass {p q : ZFSet} :
    q ∈ ratClass p ↔ q ∈ ratDomain ∧ ratRel p q := by
  exact ZFSet.mem_sep

theorem ratClass_subset_ratDomain (p : ZFSet) :
    ratClass p ⊆ ratDomain := by
  intro q hq
  exact (mem_ratClass.mp hq).1

theorem ratClass_mem_powerset_ratDomain
    {p : ZFSet}
    (_hp : p ∈ ratDomain) :
    ratClass p ∈ ZFSet.powerset ratDomain := by
  exact ZFSet.mem_powerset.mpr (ratClass_subset_ratDomain p)

def rationalsTA : ZFSet :=
  ZFSet.sep
    (fun C =>
      ∃ p : ZFSet,
        p ∈ ratDomain ∧
        C = ratClass p)
    (ZFSet.powerset ratDomain)

theorem mem_rationalsTA_iff {C : ZFSet} :
    C ∈ rationalsTA ↔
    ∃ p : ZFSet,
      p ∈ ratDomain ∧
      C = ratClass p := by
  constructor
  · intro hC
    exact (ZFSet.mem_sep.mp hC).2
  · rintro ⟨p, hp, rfl⟩
    exact ZFSet.mem_sep.mpr
      ⟨ratClass_mem_powerset_ratDomain hp, p, hp, rfl⟩

theorem ratClass_mem_rationalsTA
    {p : ZFSet}
    (hp : p ∈ ratDomain) :
    ratClass p ∈ rationalsTA := by
  exact mem_rationalsTA_iff.mpr ⟨p, hp, rfl⟩

theorem TA_PRO_00052_rational_quotient :
    ∀ C : ZFSet,
      C ∈ rationalsTA ↔
      ∃ p : ZFSet,
        p ∈ ratDomain ∧
        C = ratClass p := by
  intro C
  exact mem_rationalsTA_iff

/-! ## TA-PRO-00053 — criterio de igualdad de clases -/

theorem TA_PRO_00053_ratClass_eq_iff
    {p q : ZFSet}
    (hp : p ∈ ratDomain)
    (hq : q ∈ ratDomain) :
    ratClass p = ratClass q ↔ ratRel p q := by
  constructor
  · intro hClasses
    have hpInP : p ∈ ratClass p :=
      mem_ratClass.mpr ⟨hp, ratRel_refl hp⟩
    have hpInQ : p ∈ ratClass q := by
      rw [← hClasses]
      exact hpInP
    have hqp : ratRel q p := (mem_ratClass.mp hpInQ).2
    exact ratRel_symm hq hp hqp
  · intro hpq
    apply ZFSet.ext
    intro r
    constructor
    · intro hrP
      have hrDom : r ∈ ratDomain := (mem_ratClass.mp hrP).1
      have hpr : ratRel p r := (mem_ratClass.mp hrP).2
      have hqp : ratRel q p := ratRel_symm hp hq hpq
      exact mem_ratClass.mpr
        ⟨hrDom, ratRel_trans hq hp hrDom hqp hpr⟩
    · intro hrQ
      have hrDom : r ∈ ratDomain := (mem_ratClass.mp hrQ).1
      have hqr : ratRel q r := (mem_ratClass.mp hrQ).2
      exact mem_ratClass.mpr
        ⟨hrDom, ratRel_trans hp hq hrDom hpq hqr⟩

theorem TA_PRO_00053_ratClass_pairs_eq_iff
    {a b c d : ZFSet}
    (ha : a ∈ integersTA)
    (hb : b ∈ intNonzeroTA)
    (hc : c ∈ integersTA)
    (hd : d ∈ intNonzeroTA) :
    ratClass (ZFSet.pair a b) =
      ratClass (ZFSet.pair c d) ↔
    IntProductEq a d b c := by
  have hp : ZFSet.pair a b ∈ ratDomain :=
    mem_ratDomain_iff.mpr ⟨a, b, ha, hb, rfl⟩
  have hq : ZFSet.pair c d ∈ ratDomain :=
    mem_ratDomain_iff.mpr ⟨c, d, hc, hd, rfl⟩
  exact (TA_PRO_00053_ratClass_eq_iff hp hq).trans
    (ratRel_pairs_iff ha hb hc hd)

end TratadoAnalisis.Rationals.Construction
