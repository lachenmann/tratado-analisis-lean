import TratadoAnalisis.Rationals.Construction

/-!
# TA-LEAN-0003 — C2a

Suma, cero y opuesto racionales construidos mediante grafos relacionales.
-/

namespace TratadoAnalisis.Rationals.Additive

open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Integers.Construction
open TratadoAnalisis.Integers.Operations
open TratadoAnalisis.Integers.Multiplication
open TratadoAnalisis.Integers.Algebra
open TratadoAnalisis.Integers.Domain
open TratadoAnalisis.Rationals.IntegerPrep
open TratadoAnalisis.Rationals.Construction

theorem intAdd_exists
    {x y : ZFSet}
    (hx : x ∈ integersTA)
    (hy : y ∈ integersTA) :
    ∃ z : ZFSet, z ∈ integersTA ∧ IntAdd x y z := by
  have hInput :
      ZFSet.pair x y ∈
        cartesianProductFoundational integersTA integersTA :=
    mem_cartesianProductFoundational.mpr ⟨hx, hy⟩
  rcases intAddGraph_isFunc.2 (ZFSet.pair x y) hInput with
    ⟨z, hz, _hzUnique⟩
  exact ⟨z, hz.1, hz.2⟩

/-! ## TA-DEF-00052 — suma de representantes racionales -/

def ratRepAdd (p q r : ZFSet) : Prop :=
  ∃ a b c d ad bc u v : ZFSet,
    a ∈ integersTA ∧
    b ∈ intNonzeroTA ∧
    c ∈ integersTA ∧
    d ∈ intNonzeroTA ∧
    p = ZFSet.pair a b ∧
    q = ZFSet.pair c d ∧
    r = ZFSet.pair u v ∧
    IntMul a d ad ∧
    IntMul b c bc ∧
    IntAdd ad bc u ∧
    IntMul b d v

theorem ratRepAdd_pairs
    {a b c d ad bc u v : ZFSet}
    (ha : a ∈ integersTA)
    (hb : b ∈ intNonzeroTA)
    (hc : c ∈ integersTA)
    (hd : d ∈ intNonzeroTA)
    (had : IntMul a d ad)
    (hbc : IntMul b c bc)
    (hu : IntAdd ad bc u)
    (hv : IntMul b d v) :
    ratRepAdd
      (ZFSet.pair a b)
      (ZFSet.pair c d)
      (ZFSet.pair u v) := by
  exact ⟨a, b, c, d, ad, bc, u, v,
    ha, hb, hc, hd, rfl, rfl, rfl, had, hbc, hu, hv⟩

theorem ratRepAdd_exists_unique
    {p q : ZFSet}
    (hp : p ∈ ratDomain)
    (hq : q ∈ ratDomain) :
    ∃! r : ZFSet,
      r ∈ ratDomain ∧ ratRepAdd p q r := by
  rcases mem_ratDomain_iff.mp hp with ⟨a, b, ha, hb, rfl⟩
  rcases mem_ratDomain_iff.mp hq with ⟨c, d, hc, hd, rfl⟩
  have hbInt := (mem_intNonzeroTA_iff.mp hb).1
  have hdInt := (mem_intNonzeroTA_iff.mp hd).1
  rcases intMul_exists ha hdInt with ⟨ad, hadMem, had⟩
  rcases intMul_exists hbInt hc with ⟨bc, hbcMem, hbc⟩
  rcases intAdd_exists hadMem hbcMem with ⟨u, huMem, hu⟩
  rcases intMul_exists hbInt hdInt with ⟨v, hvMem, hv⟩
  have hvNZ : v ∈ intNonzeroTA := intNonzero_mul_closed hb hd hv
  refine ⟨ZFSet.pair u v,
    ⟨mem_ratDomain_iff.mpr ⟨u, v, huMem, hvNZ, rfl⟩,
      ratRepAdd_pairs ha hb hc hd had hbc hu hv⟩, ?_⟩
  intro r hr
  rcases hr.2 with
    ⟨a', b', c', d', ad', bc', u', v',
      _ha', _hb', _hc', _hd', hpPair, hqPair, hrPair,
      had', hbc', hu', hv'⟩
  rcases ZFSet.pair_injective hpPair with ⟨haa, hbb⟩
  rcases ZFSet.pair_injective hqPair with ⟨hcc, hdd⟩
  subst a'
  subst b'
  subst c'
  subst d'
  have hadEq : ad = ad' := IntMul_unique ha hdInt had had'
  have hbcEq : bc = bc' := IntMul_unique hbInt hc hbc hbc'
  subst ad'
  subst bc'
  have huEq : u = u' := IntAdd_unique hadMem hbcMem hu hu'
  have hvEq : v = v' := IntMul_unique hbInt hdInt hv hv'
  subst u'
  subst v'
  exact hrPair

/-! ## Álgebra relacional para TA-PRO-00054 -/

/-- Reordena explícitamente los cuatro factores
`(x*y)*(z*t) = (x*z)*(y*t)`. -/
theorem intPairProducts_exchange_middle
    {x y z t xy zt xz yt lhs rhs : ZFSet}
    (hx : x ∈ integersTA)
    (hy : y ∈ integersTA)
    (hz : z ∈ integersTA)
    (ht : t ∈ integersTA)
    (hxy : IntMul x y xy)
    (hzt : IntMul z t zt)
    (hxz : IntMul x z xz)
    (hyt : IntMul y t yt)
    (hlhs : IntMul xy zt lhs)
    (hrhs : IntMul xz yt rhs) :
    lhs = rhs := by
  have hxyMem := funcFoundational_value_mem intMulGraph_isFunc hxy
  have hztMem := funcFoundational_value_mem intMulGraph_isFunc hzt
  have hxzMem := funcFoundational_value_mem intMulGraph_isFunc hxz
  have hytMem := funcFoundational_value_mem intMulGraph_isFunc hyt
  rcases intMul_exists hy hztMem with ⟨yzt, hyztMem, hyzt⟩
  rcases intMul_exists hx hyztMem with ⟨xyzt, _hxyztMem, hxyzt⟩
  have hLeft : lhs = xyzt :=
    intMul_assoc hx hy hztMem hxy hlhs hyzt hxyzt
  rcases intMul_exists hy hz with ⟨yz, hyzMem, hyz⟩
  rcases intMul_exists hyzMem ht with ⟨yzt', _hyzt'Mem, hyzt'⟩
  have hAssocYZ : yzt' = yzt :=
    intMul_assoc hy hz ht hyz hyzt' hzt hyzt
  rcases intMul_exists hz hy with ⟨zy, hzyMem, hzy⟩
  have hYZcomm : yz = zy := intMul_comm hy hz hyz hzy
  have hzyt : IntMul zy t yzt' := by
    rw [← hYZcomm]
    exact hyzt'
  rcases intMul_exists hz hytMem with ⟨zyt, hzytMem, hzyt'⟩
  have hAssocZY : yzt' = zyt :=
    intMul_assoc hz hy ht hzy hzyt hyt hzyt'
  have hYztZyt : yzt = zyt := hAssocYZ.symm.trans hAssocZY
  have hXzyt : IntMul x zyt xyzt := by
    rw [← hYztZyt]
    exact hxyzt
  have hRight : rhs = xyzt :=
    intMul_assoc hx hz hytMem hxz hrhs hzyt' hXzyt
  exact hLeft.trans hRight.symm

theorem TA_PRO_00054_ratRepAdd_well_defined
    {p p' q q' r r' : ZFSet}
    (_hp : p ∈ ratDomain)
    (_hp' : p' ∈ ratDomain)
    (_hq : q ∈ ratDomain)
    (_hq' : q' ∈ ratDomain)
    (hpp' : ratRel p p')
    (hqq' : ratRel q q')
    (hAdd : ratRepAdd p q r)
    (hAdd' : ratRepAdd p' q' r') :
    ratRel r r' := by
  rcases hAdd with
    ⟨a, b, c, d, ad, bc, u, v,
      ha, hb, hc, hd, hpPair, hqPair, hrPair,
      had, hbc, hu, hv⟩
  rcases hAdd' with
    ⟨a', b', c', d', ad', bc', u', v',
      ha', hb', hc', hd', hpPair', hqPair', hrPair',
      had', hbc', hu', hv'⟩
  subst p
  subst q
  subst r
  subst p'
  subst q'
  subst r'
  have hbInt := (mem_intNonzeroTA_iff.mp hb).1
  have hdInt := (mem_intNonzeroTA_iff.mp hd).1
  have hbPrimeMem := (mem_intNonzeroTA_iff.mp hb').1
  have hdPrimeMem := (mem_intNonzeroTA_iff.mp hd').1
  have hP : IntProductEq a b' b a' :=
    (ratRel_pairs_iff ha hb ha' hb').mp hpp'
  have hQ : IntProductEq c d' d c' :=
    (ratRel_pairs_iff hc hd hc' hd').mp hqq'
  rcases hP with ⟨ab', ba', hab', hba', habba⟩
  rcases hQ with ⟨cd', dc', hcd', hdc', hcddc⟩

  have hadMem := funcFoundational_value_mem intMulGraph_isFunc had
  have hbcMem := funcFoundational_value_mem intMulGraph_isFunc hbc
  have had'Mem := funcFoundational_value_mem intMulGraph_isFunc had'
  have hbc'Mem := funcFoundational_value_mem intMulGraph_isFunc hbc'
  have huMem := funcFoundational_value_mem intAddGraph_isFunc hu
  have hu'Mem := funcFoundational_value_mem intAddGraph_isFunc hu'
  have hvMem := funcFoundational_value_mem intMulGraph_isFunc hv
  have hv'Mem := funcFoundational_value_mem intMulGraph_isFunc hv'
  have hvNZ : v ∈ intNonzeroTA := intNonzero_mul_closed hb hd hv
  have hv'NZ : v' ∈ intNonzeroTA := intNonzero_mul_closed hb' hd' hv'

  rcases intMul_exists huMem hv'Mem with ⟨lhs, hlhsMem, hlhs⟩
  rcases intMul_exists hvMem hu'Mem with ⟨rhs, hrhsMem, hrhs⟩
  rcases intMul_exists hadMem hv'Mem with ⟨l₁, hl₁Mem, hl₁⟩
  rcases intMul_exists hbcMem hv'Mem with ⟨l₂, hl₂Mem, hl₂⟩
  rcases intAdd_exists hl₁Mem hl₂Mem with ⟨lsum, hlsumMem, hlsum⟩
  have hDistLeft : lhs = lsum :=
    intAdd_mul_right hadMem hbcMem hv'Mem hu hlhs hl₁ hl₂ hlsum

  rcases intMul_exists hvMem had'Mem with ⟨r₁, hr₁Mem, hr₁⟩
  rcases intMul_exists hvMem hbc'Mem with ⟨r₂, hr₂Mem, hr₂⟩
  rcases intAdd_exists hr₁Mem hr₂Mem with ⟨rsum, hrsumMem, hrsum⟩
  have hDistRight : rhs = rsum :=
    intMul_add_left hvMem had'Mem hbc'Mem hu' hrhs hr₁ hr₂ hrsum

  rcases intMul_exists hdInt hdPrimeMem with ⟨dd', hdd'Mem, hdd'⟩
  have hab'Mem := funcFoundational_value_mem intMulGraph_isFunc hab'
  rcases intMul_exists hab'Mem hdd'Mem with ⟨midP, hmidPMem, hmidP⟩
  have hL₁Mid : l₁ = midP :=
    intPairProducts_exchange_middle
      ha hdInt hbPrimeMem hdPrimeMem had hv' hab' hdd' hl₁ hmidP
  have hba'Mid : IntMul ba' dd' midP := by
    rw [← habba]
    exact hmidP
  have hMidR₁ : midP = r₁ :=
    intPairProducts_exchange_middle
      hbInt ha' hdInt hdPrimeMem hba' hdd' hv had' hba'Mid hr₁
  have hL₁R₁ : l₁ = r₁ := hL₁Mid.trans hMidR₁

  rcases intMul_exists hbInt hbPrimeMem with ⟨bb', hbb'Mem, hbb'⟩
  have hcd'Mem := funcFoundational_value_mem intMulGraph_isFunc hcd'
  rcases intMul_exists hbb'Mem hcd'Mem with ⟨midQ, hmidQMem, hmidQ⟩
  have hL₂Mid : l₂ = midQ :=
    intPairProducts_exchange_middle
      hbInt hc hbPrimeMem hdPrimeMem hbc hv' hbb' hcd' hl₂ hmidQ
  have hdc'Mid : IntMul bb' dc' midQ := by
    rw [← hcddc]
    exact hmidQ
  have hMidR₂ : midQ = r₂ :=
    intPairProducts_exchange_middle
      hbInt hbPrimeMem hdInt hc' hbb' hdc' hv hbc' hdc'Mid hr₂
  have hL₂R₂ : l₂ = r₂ := hL₂Mid.trans hMidR₂

  have hrsumAtLeft : IntAdd l₁ l₂ rsum := by
    rw [hL₁R₁, hL₂R₂]
    exact hrsum
  have hSums : lsum = rsum :=
    IntAdd_unique hl₁Mem hl₂Mem hlsum hrsumAtLeft
  have hLhsRhs : lhs = rhs :=
    hDistLeft.trans (hSums.trans hDistRight.symm)
  apply (ratRel_pairs_iff huMem hvNZ hu'Mem hv'NZ).mpr
  exact ⟨lhs, rhs, hlhs, hrhs, hLhsRhs⟩

/-! ## TA-DEF-00053 — suma sobre clases racionales -/

def RatAddValue (x y z : ZFSet) : Prop :=
  ∃ p q r : ZFSet,
    p ∈ ratDomain ∧
    q ∈ ratDomain ∧
    r ∈ ratDomain ∧
    x = ratClass p ∧
    y = ratClass q ∧
    z = ratClass r ∧
    ratRepAdd p q r

def ratAddGraph : ZFSet :=
  ZFSet.sep
    (fun t =>
      ∃ x y z : ZFSet,
        x ∈ rationalsTA ∧
        y ∈ rationalsTA ∧
        z ∈ rationalsTA ∧
        t = ZFSet.pair (ZFSet.pair x y) z ∧
        RatAddValue x y z)
    (pairAmbient
      (cartesianProductFoundational rationalsTA rationalsTA)
      rationalsTA)

theorem mem_ratAddGraph {x y z : ZFSet} :
    ZFSet.pair (ZFSet.pair x y) z ∈ ratAddGraph ↔
    x ∈ rationalsTA ∧
    y ∈ rationalsTA ∧
    z ∈ rationalsTA ∧
    RatAddValue x y z := by
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

theorem ratAddGraph_isFunc :
    IsFuncFoundational
      (cartesianProductFoundational rationalsTA rationalsTA)
      rationalsTA
      ratAddGraph := by
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
    rcases ratRepAdd_exists_unique hp hq with ⟨r, hr, _hrUnique⟩
    refine ⟨ratClass r, ?_, ?_⟩
    · exact ⟨ratClass_mem_rationalsTA hr.1,
        mem_ratAddGraph.mpr
          ⟨hx, hy, ratClass_mem_rationalsTA hr.1,
            p, q, r, hp, hq, hr.1,
            hxClass, hyClass, rfl, hr.2⟩⟩
    · intro z' hz'
      rcases (mem_ratAddGraph.mp hz'.2).2.2.2 with
        ⟨p', q', r', hp', hq', hr',
          hxClass', hyClass', hzClass', hAdd'⟩
      have hpp' : ratRel p p' :=
        (TA_PRO_00053_ratClass_eq_iff hp hp').mp
          (hxClass.symm.trans hxClass')
      have hqq' : ratRel q q' :=
        (TA_PRO_00053_ratClass_eq_iff hq hq').mp
          (hyClass.symm.trans hyClass')
      have hrr' : ratRel r r' :=
        TA_PRO_00054_ratRepAdd_well_defined
          hp hp' hq hq' hpp' hqq' hr.2 hAdd'
      have hClasses : ratClass r = ratClass r' :=
        (TA_PRO_00053_ratClass_eq_iff hr.1 hr').mpr hrr'
      exact hzClass'.trans hClasses.symm

theorem ratAddGraph_classes
    {a b c d ad bc u v : ZFSet}
    (ha : a ∈ integersTA)
    (hb : b ∈ intNonzeroTA)
    (hc : c ∈ integersTA)
    (hd : d ∈ intNonzeroTA)
    (had : IntMul a d ad)
    (hbc : IntMul b c bc)
    (hu : IntAdd ad bc u)
    (hv : IntMul b d v) :
    ZFSet.pair
      (ZFSet.pair
        (ratClass (ZFSet.pair a b))
        (ratClass (ZFSet.pair c d)))
      (ratClass (ZFSet.pair u v)) ∈ ratAddGraph := by
  have hbInt := (mem_intNonzeroTA_iff.mp hb).1
  have hdInt := (mem_intNonzeroTA_iff.mp hd).1
  have huMem := funcFoundational_value_mem intAddGraph_isFunc hu
  have hvNZ : v ∈ intNonzeroTA := intNonzero_mul_closed hb hd hv
  have hp : ZFSet.pair a b ∈ ratDomain :=
    mem_ratDomain_iff.mpr ⟨a, b, ha, hb, rfl⟩
  have hq : ZFSet.pair c d ∈ ratDomain :=
    mem_ratDomain_iff.mpr ⟨c, d, hc, hd, rfl⟩
  have hr : ZFSet.pair u v ∈ ratDomain :=
    mem_ratDomain_iff.mpr ⟨u, v, huMem, hvNZ, rfl⟩
  apply mem_ratAddGraph.mpr
  exact ⟨ratClass_mem_rationalsTA hp,
    ratClass_mem_rationalsTA hq,
    ratClass_mem_rationalsTA hr,
    ZFSet.pair a b, ZFSet.pair c d, ZFSet.pair u v,
    hp, hq, hr, rfl, rfl, rfl,
    ratRepAdd_pairs ha hb hc hd had hbc hu hv⟩

theorem ratAddGraph_classes_value_iff
    {a b c d ad bc u v z : ZFSet}
    (ha : a ∈ integersTA)
    (hb : b ∈ intNonzeroTA)
    (hc : c ∈ integersTA)
    (hd : d ∈ intNonzeroTA)
    (had : IntMul a d ad)
    (hbc : IntMul b c bc)
    (hu : IntAdd ad bc u)
    (hv : IntMul b d v) :
    ZFSet.pair
      (ZFSet.pair
        (ratClass (ZFSet.pair a b))
        (ratClass (ZFSet.pair c d))) z ∈ ratAddGraph ↔
    z = ratClass (ZFSet.pair u v) := by
  have hp : ZFSet.pair a b ∈ ratDomain :=
    mem_ratDomain_iff.mpr ⟨a, b, ha, hb, rfl⟩
  have hq : ZFSet.pair c d ∈ ratDomain :=
    mem_ratDomain_iff.mpr ⟨c, d, hc, hd, rfl⟩
  have hvNZ : v ∈ intNonzeroTA := intNonzero_mul_closed hb hd hv
  have huMem := funcFoundational_value_mem intAddGraph_isFunc hu
  have hr : ZFSet.pair u v ∈ ratDomain :=
    mem_ratDomain_iff.mpr ⟨u, v, huMem, hvNZ, rfl⟩
  have hInput :
      ZFSet.pair
        (ratClass (ZFSet.pair a b))
        (ratClass (ZFSet.pair c d)) ∈
      cartesianProductFoundational rationalsTA rationalsTA :=
    mem_cartesianProductFoundational.mpr
      ⟨ratClass_mem_rationalsTA hp, ratClass_mem_rationalsTA hq⟩
  constructor
  · intro hz
    rcases ratAddGraph_isFunc.2 _ hInput with ⟨w, hw, hUnique⟩
    have hzMem := funcFoundational_value_mem ratAddGraph_isFunc hz
    have hKnown := ratAddGraph_classes ha hb hc hd had hbc hu hv
    exact (hUnique z ⟨hzMem, hz⟩).trans
      (hUnique (ratClass (ZFSet.pair u v))
        ⟨ratClass_mem_rationalsTA hr, hKnown⟩).symm
  · rintro rfl
    exact ratAddGraph_classes ha hb hc hd had hbc hu hv

/-! ## TA-NOT-00014 — cero racional -/

theorem intOne_mem_intNonzeroTA : intOne ∈ intNonzeroTA := by
  apply mem_intNonzeroTA_iff.mpr
  exact ⟨intOne_mem_integersTA, fun h => TA_PRO_00046_zero_ne_one h.symm⟩

def ratZero : ZFSet :=
  ratClass (ZFSet.pair intZero intOne)

theorem ratZero_mem_rationalsTA : ratZero ∈ rationalsTA := by
  apply ratClass_mem_rationalsTA
  exact mem_ratDomain_iff.mpr
    ⟨intZero, intOne, intZero_mem_integersTA,
      intOne_mem_intNonzeroTA, rfl⟩

/-! ## TA-DEF-00054 — opuesto de representantes -/

def ratRepNeg (p r : ZFSet) : Prop :=
  ∃ a b na : ZFSet,
    a ∈ integersTA ∧
    b ∈ intNonzeroTA ∧
    p = ZFSet.pair a b ∧
    r = ZFSet.pair na b ∧
    IntNeg a na

theorem ratRepNeg_exists_unique
    {p : ZFSet}
    (hp : p ∈ ratDomain) :
    ∃! r : ZFSet,
      r ∈ ratDomain ∧ ratRepNeg p r := by
  rcases mem_ratDomain_iff.mp hp with ⟨a, b, ha, hb, rfl⟩
  rcases intNegGraph_isFunc.2 a ha with ⟨na, hna, _hnaUnique⟩
  refine ⟨ZFSet.pair na b,
    ⟨mem_ratDomain_iff.mpr ⟨na, b, hna.1, hb, rfl⟩,
      a, b, na, ha, hb, rfl, rfl, hna.2⟩, ?_⟩
  intro r hr
  rcases hr.2 with
    ⟨a', b', na', _ha', _hb', hpPair, hrPair, hNeg'⟩
  rcases ZFSet.pair_injective hpPair with ⟨haa, hbb⟩
  subst a'
  subst b'
  have hnaEq : na = na' := IntNeg_unique ha hna.2 hNeg'
  subst na'
  exact hrPair

/-! ## Helpers enteros para producto y opuesto -/

theorem intAdd_cancel_left
    {x y z s : ZFSet}
    (hx : x ∈ integersTA)
    (hy : y ∈ integersTA)
    (hz : z ∈ integersTA)
    (hxy : IntAdd x y s)
    (hxz : IntAdd x z s) :
    y = z := by
  rcases intNegGraph_isFunc.2 x hx with ⟨nx, hnx, _hnxUnique⟩
  rcases intAdd_exists hnx.1 hx with ⟨t, htMem, ht⟩
  have htZero : t = intZero := intAdd_neg_left hx hnx.2 ht
  have hsMem := funcFoundational_value_mem intAddGraph_isFunc hxy
  rcases intAdd_exists hnx.1 hsMem with ⟨nxs, _hnxsMem, hnxs⟩
  rcases intAdd_exists htMem hy with ⟨ty, _htyMem, hty⟩
  have hAssocY : ty = nxs :=
    intAdd_assoc hnx.1 hx hy ht hty hxy hnxs
  rcases intAdd_exists htMem hz with ⟨tz, _htzMem, htz⟩
  have hAssocZ : tz = nxs :=
    intAdd_assoc hnx.1 hx hz ht htz hxz hnxs
  have htyY : ty = y :=
    intAdd_zero_left hy (by simpa [IntAdd, htZero] using hty)
  have htzZ : tz = z :=
    intAdd_zero_left hz (by simpa [IntAdd, htZero] using htz)
  exact htyY.symm.trans
    (hAssocY.trans (hAssocZ.symm.trans htzZ))

theorem intNeg_of_add_zero
    {x y : ZFSet}
    (hx : x ∈ integersTA)
    (hy : y ∈ integersTA)
    (hAdd : IntAdd x y intZero) :
    IntNeg x y := by
  rcases intNegGraph_isFunc.2 x hx with ⟨nx, hnx, _hnxUnique⟩
  rcases intAdd_exists hx hnx.1 with ⟨s, _hsMem, hs⟩
  have hsZero : s = intZero := intAdd_neg_right hx hnx.2 hs
  have hCanonical : IntAdd x nx intZero := by
    simpa [IntAdd, hsZero] using hs
  have hyEq : y = nx :=
    intAdd_cancel_left hx hy hnx.1 hAdd hCanonical
  rw [hyEq]
  exact hnx.2

theorem intMul_neg_right
    {x y ny xy xny : ZFSet}
    (hx : x ∈ integersTA)
    (hy : y ∈ integersTA)
    (hny : ny ∈ integersTA)
    (hNeg : IntNeg y ny)
    (hxy : IntMul x y xy)
    (hxny : IntMul x ny xny) :
    IntNeg xy xny := by
  have hxyMem := funcFoundational_value_mem intMulGraph_isFunc hxy
  have hxnyMem := funcFoundational_value_mem intMulGraph_isFunc hxny
  rcases intAdd_exists hxyMem hxnyMem with ⟨s, _hsMem, hs⟩
  have hsZero : s = intZero :=
    intMul_neg_sum_zero hx hy hny hNeg hxy hxny hs
  apply intNeg_of_add_zero hxyMem hxnyMem
  simpa [IntAdd, hsZero] using hs

theorem intMul_neg_left
    {x nx y xy nxy : ZFSet}
    (hx : x ∈ integersTA)
    (hnx : nx ∈ integersTA)
    (hy : y ∈ integersTA)
    (hNeg : IntNeg x nx)
    (hxy : IntMul x y xy)
    (hnxy : IntMul nx y nxy) :
    IntNeg xy nxy := by
  rcases intMul_exists hy hx with ⟨yx, _hyxMem, hyx⟩
  rcases intMul_exists hy hnx with ⟨ynx, _hynxMem, hynx⟩
  have hxyEq : xy = yx := intMul_comm hx hy hxy hyx
  have hnxyEq : nxy = ynx := intMul_comm hnx hy hnxy hynx
  have hNegRight : IntNeg yx ynx :=
    intMul_neg_right hy hx hnx hNeg hyx hynx
  rw [hxyEq, hnxyEq]
  exact hNegRight

theorem TA_PRO_00055_ratRepNeg_well_defined
    {p q np nq : ZFSet}
    (_hp : p ∈ ratDomain)
    (_hq : q ∈ ratDomain)
    (hpq : ratRel p q)
    (hNegP : ratRepNeg p np)
    (hNegQ : ratRepNeg q nq) :
    ratRel np nq := by
  rcases hNegP with
    ⟨a, b, na, ha, hb, hpPair, hnpPair, hNegA⟩
  rcases hNegQ with
    ⟨c, d, nc, hc, hd, hqPair, hnqPair, hNegC⟩
  subst p
  subst np
  subst q
  subst nq
  have hbInt := (mem_intNonzeroTA_iff.mp hb).1
  have hdInt := (mem_intNonzeroTA_iff.mp hd).1
  have hnaMem := funcFoundational_value_mem intNegGraph_isFunc hNegA
  have hncMem := funcFoundational_value_mem intNegGraph_isFunc hNegC
  have hProd : IntProductEq a d b c :=
    (ratRel_pairs_iff ha hb hc hd).mp hpq
  rcases hProd with ⟨ad, bc, had, hbc, hab⟩
  have hadMem := funcFoundational_value_mem intMulGraph_isFunc had
  rcases intMul_exists hnaMem hdInt with ⟨nad, _hnadMem, hnad⟩
  rcases intMul_exists hbInt hncMem with ⟨bnc, _hbncMem, hbnc⟩
  have hNegAD : IntNeg ad nad :=
    intMul_neg_left ha hnaMem hdInt hNegA had hnad
  have hNegBC : IntNeg bc bnc :=
    intMul_neg_right hbInt hc hncMem hNegC hbc hbnc
  have hNegBCAtAD : IntNeg ad bnc := by
    rw [hab]
    exact hNegBC
  have hProducts : nad = bnc :=
    IntNeg_unique hadMem hNegAD hNegBCAtAD
  apply (ratRel_pairs_iff hnaMem hb hncMem hd).mpr
  exact ⟨nad, bnc, hnad, hbnc, hProducts⟩

/-! ## TA-DEF-00055 — opuesto sobre clases racionales -/

def RatNegValue (x y : ZFSet) : Prop :=
  ∃ p r : ZFSet,
    p ∈ ratDomain ∧
    r ∈ ratDomain ∧
    x = ratClass p ∧
    y = ratClass r ∧
    ratRepNeg p r

def ratNegGraph : ZFSet :=
  ZFSet.sep
    (fun t =>
      ∃ x y : ZFSet,
        x ∈ rationalsTA ∧
        y ∈ rationalsTA ∧
        t = ZFSet.pair x y ∧
        RatNegValue x y)
    (pairAmbient rationalsTA rationalsTA)

theorem mem_ratNegGraph {x y : ZFSet} :
    ZFSet.pair x y ∈ ratNegGraph ↔
    x ∈ rationalsTA ∧ y ∈ rationalsTA ∧ RatNegValue x y := by
  constructor
  · intro h
    rcases (ZFSet.mem_sep.mp h).2 with
      ⟨x', y', hx', hy', hPair, hValue⟩
    rcases ZFSet.pair_injective hPair with ⟨hxx, hyy⟩
    subst x'
    subst y'
    exact ⟨hx', hy', hValue⟩
  · rintro ⟨hx, hy, hValue⟩
    apply ZFSet.mem_sep.mpr
    exact ⟨pair_mem_pairAmbient hx hy,
      x, y, hx, hy, rfl, hValue⟩

theorem ratNegGraph_isFunc :
    IsFuncFoundational rationalsTA rationalsTA ratNegGraph := by
  constructor
  · intro t ht
    rcases (ZFSet.mem_sep.mp ht).2 with
      ⟨x, y, hx, hy, rfl, _hValue⟩
    exact ⟨x, hx, y, hy, rfl⟩
  · intro x hx
    rcases mem_rationalsTA_iff.mp hx with ⟨p, hp, hxClass⟩
    rcases ratRepNeg_exists_unique hp with ⟨r, hr, _hrUnique⟩
    refine ⟨ratClass r, ?_, ?_⟩
    · exact ⟨ratClass_mem_rationalsTA hr.1,
        mem_ratNegGraph.mpr
          ⟨hx, ratClass_mem_rationalsTA hr.1,
            p, r, hp, hr.1, hxClass, rfl, hr.2⟩⟩
    · intro y' hy'
      rcases (mem_ratNegGraph.mp hy'.2).2.2 with
        ⟨p', r', hp', hr', hxClass', hyClass', hNeg'⟩
      have hpp' : ratRel p p' :=
        (TA_PRO_00053_ratClass_eq_iff hp hp').mp
          (hxClass.symm.trans hxClass')
      have hrr' : ratRel r r' :=
        TA_PRO_00055_ratRepNeg_well_defined
          hp hp' hpp' hr.2 hNeg'
      have hClasses : ratClass r = ratClass r' :=
        (TA_PRO_00053_ratClass_eq_iff hr.1 hr').mpr hrr'
      exact hyClass'.trans hClasses.symm

theorem ratNegGraph_classes
    {a b na : ZFSet}
    (ha : a ∈ integersTA)
    (hb : b ∈ intNonzeroTA)
    (hNeg : IntNeg a na) :
    ZFSet.pair
      (ratClass (ZFSet.pair a b))
      (ratClass (ZFSet.pair na b)) ∈ ratNegGraph := by
  have hnaMem := funcFoundational_value_mem intNegGraph_isFunc hNeg
  have hp : ZFSet.pair a b ∈ ratDomain :=
    mem_ratDomain_iff.mpr ⟨a, b, ha, hb, rfl⟩
  have hr : ZFSet.pair na b ∈ ratDomain :=
    mem_ratDomain_iff.mpr ⟨na, b, hnaMem, hb, rfl⟩
  apply mem_ratNegGraph.mpr
  exact ⟨ratClass_mem_rationalsTA hp,
    ratClass_mem_rationalsTA hr,
    ZFSet.pair a b, ZFSet.pair na b,
    hp, hr, rfl, rfl,
    a, b, na, ha, hb, rfl, rfl, hNeg⟩

theorem ratNegGraph_classes_value_iff
    {a b na y : ZFSet}
    (ha : a ∈ integersTA)
    (hb : b ∈ intNonzeroTA)
    (hNeg : IntNeg a na) :
    ZFSet.pair (ratClass (ZFSet.pair a b)) y ∈ ratNegGraph ↔
    y = ratClass (ZFSet.pair na b) := by
  have hnaMem := funcFoundational_value_mem intNegGraph_isFunc hNeg
  have hp : ZFSet.pair a b ∈ ratDomain :=
    mem_ratDomain_iff.mpr ⟨a, b, ha, hb, rfl⟩
  have hr : ZFSet.pair na b ∈ ratDomain :=
    mem_ratDomain_iff.mpr ⟨na, b, hnaMem, hb, rfl⟩
  constructor
  · intro hy
    rcases ratNegGraph_isFunc.2 _ (ratClass_mem_rationalsTA hp) with
      ⟨w, hw, hUnique⟩
    have hyMem := funcFoundational_value_mem ratNegGraph_isFunc hy
    have hKnown := ratNegGraph_classes ha hb hNeg
    exact (hUnique y ⟨hyMem, hy⟩).trans
      (hUnique (ratClass (ZFSet.pair na b))
        ⟨ratClass_mem_rationalsTA hr, hKnown⟩).symm
  · rintro rfl
    exact ratNegGraph_classes ha hb hNeg

end TratadoAnalisis.Rationals.Additive
