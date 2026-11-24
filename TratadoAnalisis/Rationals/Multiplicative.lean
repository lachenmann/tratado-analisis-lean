import TratadoAnalisis.Rationals.Additive

/-!
# TA-LEAN-0003 — C2b

Producto y unidad racionales construidos mediante grafos relacionales.
-/

namespace TratadoAnalisis.Rationals.Multiplicative

open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Integers.Construction
open TratadoAnalisis.Integers.Operations
open TratadoAnalisis.Integers.Multiplication
open TratadoAnalisis.Integers.Algebra
open TratadoAnalisis.Rationals.IntegerPrep
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive

/-! ## TA-DEF-00057 — producto de representantes racionales -/

def ratRepMul (p q r : ZFSet) : Prop :=
  ∃ a b c d ac bd : ZFSet,
    a ∈ integersTA ∧
    b ∈ intNonzeroTA ∧
    c ∈ integersTA ∧
    d ∈ intNonzeroTA ∧
    p = ZFSet.pair a b ∧
    q = ZFSet.pair c d ∧
    r = ZFSet.pair ac bd ∧
    IntMul a c ac ∧
    IntMul b d bd

theorem ratRepMul_pairs
    {a b c d ac bd : ZFSet}
    (ha : a ∈ integersTA)
    (hb : b ∈ intNonzeroTA)
    (hc : c ∈ integersTA)
    (hd : d ∈ intNonzeroTA)
    (hac : IntMul a c ac)
    (hbd : IntMul b d bd) :
    ratRepMul
      (ZFSet.pair a b)
      (ZFSet.pair c d)
      (ZFSet.pair ac bd) := by
  exact ⟨a, b, c, d, ac, bd,
    ha, hb, hc, hd, rfl, rfl, rfl, hac, hbd⟩

theorem ratRepMul_exists_unique
    {p q : ZFSet}
    (hp : p ∈ ratDomain)
    (hq : q ∈ ratDomain) :
    ∃! r : ZFSet,
      r ∈ ratDomain ∧ ratRepMul p q r := by
  rcases mem_ratDomain_iff.mp hp with ⟨a, b, ha, hb, rfl⟩
  rcases mem_ratDomain_iff.mp hq with ⟨c, d, hc, hd, rfl⟩
  have hbMem := (mem_intNonzeroTA_iff.mp hb).1
  have hdMem := (mem_intNonzeroTA_iff.mp hd).1
  rcases intMul_exists ha hc with ⟨ac, hacMem, hac⟩
  rcases intMul_exists hbMem hdMem with ⟨bd, _hbdMem, hbd⟩
  have hbdNZ : bd ∈ intNonzeroTA := intNonzero_mul_closed hb hd hbd
  refine ⟨ZFSet.pair ac bd,
    ⟨mem_ratDomain_iff.mpr ⟨ac, bd, hacMem, hbdNZ, rfl⟩,
      ratRepMul_pairs ha hb hc hd hac hbd⟩, ?_⟩
  intro r hr
  rcases hr.2 with
    ⟨a', b', c', d', ac', bd',
      _ha', _hb', _hc', _hd', hpPair, hqPair, hrPair, hac', hbd'⟩
  rcases ZFSet.pair_injective hpPair with ⟨haa, hbb⟩
  rcases ZFSet.pair_injective hqPair with ⟨hcc, hdd⟩
  subst a'
  subst b'
  subst c'
  subst d'
  have hacEq : ac = ac' := IntMul_unique ha hc hac hac'
  have hbdEq : bd = bd' := IntMul_unique hbMem hdMem hbd hbd'
  subst ac'
  subst bd'
  exact hrPair

/-! ## TA-PRO-00057 — independencia de representantes -/

theorem TA_PRO_00057_ratRepMul_well_defined
    {p p' q q' r r' : ZFSet}
    (_hp : p ∈ ratDomain)
    (_hp' : p' ∈ ratDomain)
    (_hq : q ∈ ratDomain)
    (_hq' : q' ∈ ratDomain)
    (hpp' : ratRel p p')
    (hqq' : ratRel q q')
    (hMul : ratRepMul p q r)
    (hMul' : ratRepMul p' q' r') :
    ratRel r r' := by
  rcases hMul with
    ⟨a, b, c, d, ac, bd,
      ha, hb, hc, hd, hpPair, hqPair, hrPair, hac, hbd⟩
  rcases hMul' with
    ⟨a', b', c', d', ac', bd',
      ha', hb', hc', hd', hpPair', hqPair', hrPair', hac', hbd'⟩
  subst p
  subst q
  subst r
  subst p'
  subst q'
  subst r'
  have hbMem := (mem_intNonzeroTA_iff.mp hb).1
  have hdMem := (mem_intNonzeroTA_iff.mp hd).1
  have hbPrimeMem := (mem_intNonzeroTA_iff.mp hb').1
  have hdPrimeMem := (mem_intNonzeroTA_iff.mp hd').1
  have hP : IntProductEq a b' b a' :=
    (ratRel_pairs_iff ha hb ha' hb').mp hpp'
  have hQ : IntProductEq c d' d c' :=
    (ratRel_pairs_iff hc hd hc' hd').mp hqq'
  rcases hP with ⟨ab', ba', hab', hba', habba⟩
  rcases hQ with ⟨cd', dc', hcd', hdc', hcddc⟩
  have hacMem := funcFoundational_value_mem intMulGraph_isFunc hac
  have hbdMem := funcFoundational_value_mem intMulGraph_isFunc hbd
  have hac'Mem := funcFoundational_value_mem intMulGraph_isFunc hac'
  have hbd'Mem := funcFoundational_value_mem intMulGraph_isFunc hbd'
  have hbdNZ : bd ∈ intNonzeroTA := intNonzero_mul_closed hb hd hbd
  have hbd'NZ : bd' ∈ intNonzeroTA := intNonzero_mul_closed hb' hd' hbd'
  rcases intMul_exists hacMem hbd'Mem with ⟨lhs, _hlhsMem, hlhs⟩
  rcases intMul_exists hbdMem hac'Mem with ⟨rhs, _hrhsMem, hrhs⟩
  have hab'Mem := funcFoundational_value_mem intMulGraph_isFunc hab'
  have hcd'Mem := funcFoundational_value_mem intMulGraph_isFunc hcd'
  rcases intMul_exists hab'Mem hcd'Mem with ⟨middle, _hmiddleMem, hmiddle⟩
  have hLeft : lhs = middle :=
    intPairProducts_exchange_middle
      ha hc hbPrimeMem hdPrimeMem
      hac hbd' hab' hcd' hlhs hmiddle
  have hMiddle' : IntMul ba' dc' middle := by
    rw [← habba, ← hcddc]
    exact hmiddle
  have hRight : middle = rhs :=
    intPairProducts_exchange_middle
      hbMem ha' hdMem hc'
      hba' hdc' hbd hac' hMiddle' hrhs
  apply (ratRel_pairs_iff hacMem hbdNZ hac'Mem hbd'NZ).mpr
  exact ⟨lhs, rhs, hlhs, hrhs, hLeft.trans hRight⟩

/-! ## TA-DEF-00058 — producto sobre clases racionales -/

def RatMulValue (x y z : ZFSet) : Prop :=
  ∃ p q r : ZFSet,
    p ∈ ratDomain ∧
    q ∈ ratDomain ∧
    r ∈ ratDomain ∧
    x = ratClass p ∧
    y = ratClass q ∧
    z = ratClass r ∧
    ratRepMul p q r

def ratMulGraph : ZFSet :=
  ZFSet.sep
    (fun t =>
      ∃ x y z : ZFSet,
        x ∈ rationalsTA ∧
        y ∈ rationalsTA ∧
        z ∈ rationalsTA ∧
        t = ZFSet.pair (ZFSet.pair x y) z ∧
        RatMulValue x y z)
    (pairAmbient
      (cartesianProductFoundational rationalsTA rationalsTA)
      rationalsTA)

theorem mem_ratMulGraph {x y z : ZFSet} :
    ZFSet.pair (ZFSet.pair x y) z ∈ ratMulGraph ↔
    x ∈ rationalsTA ∧
    y ∈ rationalsTA ∧
    z ∈ rationalsTA ∧
    RatMulValue x y z := by
  constructor
  · intro h
    rcases (ZFSet.mem_sep.mp h).2 with
      ⟨x', y', z', hx', hy', hz', hPair, hValue⟩
    rcases ZFSet.pair_injective hPair with ⟨hxy, hzz⟩
    rcases ZFSet.pair_injective hxy with ⟨hxx, hyy⟩
    subst x'
    subst y'
    subst z'
    exact ⟨hx', hy', hz', hValue⟩
  · rintro ⟨hx, hy, hz, hValue⟩
    apply ZFSet.mem_sep.mpr
    exact ⟨pair_mem_pairAmbient
        (mem_cartesianProductFoundational.mpr ⟨hx, hy⟩) hz,
      x, y, z, hx, hy, hz, rfl, hValue⟩

theorem ratMulGraph_isFunc :
    IsFuncFoundational
      (cartesianProductFoundational rationalsTA rationalsTA)
      rationalsTA
      ratMulGraph := by
  constructor
  · intro t ht
    rcases (ZFSet.mem_sep.mp ht).2 with
      ⟨x, y, z, hx, hy, hz, rfl, _hValue⟩
    exact ⟨ZFSet.pair x y,
      mem_cartesianProductFoundational.mpr ⟨hx, hy⟩,
      z, hz, rfl⟩
  · intro xy hxy
    rcases mem_cartesianProductFoundational_iff.mp hxy with
      ⟨x, hx, y, hy, rfl⟩
    rcases mem_rationalsTA_iff.mp hx with ⟨p, hp, hxClass⟩
    rcases mem_rationalsTA_iff.mp hy with ⟨q, hq, hyClass⟩
    rcases ratRepMul_exists_unique hp hq with ⟨r, hr, _hrUnique⟩
    refine ⟨ratClass r, ?_, ?_⟩
    · exact ⟨ratClass_mem_rationalsTA hr.1,
        mem_ratMulGraph.mpr
          ⟨hx, hy, ratClass_mem_rationalsTA hr.1,
            p, q, r, hp, hq, hr.1,
            hxClass, hyClass, rfl, hr.2⟩⟩
    · intro z' hz'
      rcases (mem_ratMulGraph.mp hz'.2).2.2.2 with
        ⟨p', q', r', hp', hq', hr',
          hxClass', hyClass', hzClass', hMul'⟩
      have hpp' : ratRel p p' :=
        (TA_PRO_00053_ratClass_eq_iff hp hp').mp
          (hxClass.symm.trans hxClass')
      have hqq' : ratRel q q' :=
        (TA_PRO_00053_ratClass_eq_iff hq hq').mp
          (hyClass.symm.trans hyClass')
      have hrr' : ratRel r r' :=
        TA_PRO_00057_ratRepMul_well_defined
          hp hp' hq hq' hpp' hqq' hr.2 hMul'
      have hClasses : ratClass r = ratClass r' :=
        (TA_PRO_00053_ratClass_eq_iff hr.1 hr').mpr hrr'
      exact hzClass'.trans hClasses.symm

theorem ratMulGraph_classes
    {a b c d ac bd : ZFSet}
    (ha : a ∈ integersTA)
    (hb : b ∈ intNonzeroTA)
    (hc : c ∈ integersTA)
    (hd : d ∈ intNonzeroTA)
    (hac : IntMul a c ac)
    (hbd : IntMul b d bd) :
    ZFSet.pair
      (ZFSet.pair
        (ratClass (ZFSet.pair a b))
        (ratClass (ZFSet.pair c d)))
      (ratClass (ZFSet.pair ac bd)) ∈ ratMulGraph := by
  have hacMem := funcFoundational_value_mem intMulGraph_isFunc hac
  have hbdNZ : bd ∈ intNonzeroTA := intNonzero_mul_closed hb hd hbd
  have hp : ZFSet.pair a b ∈ ratDomain :=
    mem_ratDomain_iff.mpr ⟨a, b, ha, hb, rfl⟩
  have hq : ZFSet.pair c d ∈ ratDomain :=
    mem_ratDomain_iff.mpr ⟨c, d, hc, hd, rfl⟩
  have hr : ZFSet.pair ac bd ∈ ratDomain :=
    mem_ratDomain_iff.mpr ⟨ac, bd, hacMem, hbdNZ, rfl⟩
  apply mem_ratMulGraph.mpr
  exact ⟨ratClass_mem_rationalsTA hp,
    ratClass_mem_rationalsTA hq,
    ratClass_mem_rationalsTA hr,
    ZFSet.pair a b, ZFSet.pair c d, ZFSet.pair ac bd,
    hp, hq, hr, rfl, rfl, rfl,
    ratRepMul_pairs ha hb hc hd hac hbd⟩

theorem ratMulGraph_classes_value_iff
    {a b c d ac bd z : ZFSet}
    (ha : a ∈ integersTA)
    (hb : b ∈ intNonzeroTA)
    (hc : c ∈ integersTA)
    (hd : d ∈ intNonzeroTA)
    (hac : IntMul a c ac)
    (hbd : IntMul b d bd) :
    ZFSet.pair
      (ZFSet.pair
        (ratClass (ZFSet.pair a b))
        (ratClass (ZFSet.pair c d))) z ∈ ratMulGraph ↔
    z = ratClass (ZFSet.pair ac bd) := by
  have hp : ZFSet.pair a b ∈ ratDomain :=
    mem_ratDomain_iff.mpr ⟨a, b, ha, hb, rfl⟩
  have hq : ZFSet.pair c d ∈ ratDomain :=
    mem_ratDomain_iff.mpr ⟨c, d, hc, hd, rfl⟩
  have hacMem := funcFoundational_value_mem intMulGraph_isFunc hac
  have hbdNZ : bd ∈ intNonzeroTA := intNonzero_mul_closed hb hd hbd
  have hr : ZFSet.pair ac bd ∈ ratDomain :=
    mem_ratDomain_iff.mpr ⟨ac, bd, hacMem, hbdNZ, rfl⟩
  have hInput :
      ZFSet.pair
        (ratClass (ZFSet.pair a b))
        (ratClass (ZFSet.pair c d)) ∈
      cartesianProductFoundational rationalsTA rationalsTA :=
    mem_cartesianProductFoundational.mpr
      ⟨ratClass_mem_rationalsTA hp, ratClass_mem_rationalsTA hq⟩
  constructor
  · intro hz
    rcases ratMulGraph_isFunc.2 _ hInput with ⟨w, hw, hUnique⟩
    have hzMem := funcFoundational_value_mem ratMulGraph_isFunc hz
    have hKnown := ratMulGraph_classes ha hb hc hd hac hbd
    exact (hUnique z ⟨hzMem, hz⟩).trans
      (hUnique (ratClass (ZFSet.pair ac bd))
        ⟨ratClass_mem_rationalsTA hr, hKnown⟩).symm
  · rintro rfl
    exact ratMulGraph_classes ha hb hc hd hac hbd

/-! ## TA-NOT-00015 — unidad racional -/

def ratOne : ZFSet :=
  ratClass (ZFSet.pair intOne intOne)

theorem ratOne_mem_rationalsTA : ratOne ∈ rationalsTA := by
  apply ratClass_mem_rationalsTA
  exact mem_ratDomain_iff.mpr
    ⟨intOne, intOne, intOne_mem_integersTA,
      intOne_mem_intNonzeroTA, rfl⟩

end TratadoAnalisis.Rationals.Multiplicative
