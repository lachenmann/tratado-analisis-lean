import TratadoAnalisis.Rationals.Multiplicative

namespace TratadoAnalisis.Rationals.Algebra

open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Integers.Construction
open TratadoAnalisis.Integers.Operations
open TratadoAnalisis.Integers.Multiplication
open TratadoAnalisis.Integers.Algebra
open TratadoAnalisis.Integers.Domain
open TratadoAnalisis.Rationals.IntegerPrep
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Multiplicative

/-! # Álgebra racional relacional -/

def RatAdd (x y z : ZFSet) : Prop :=
  ZFSet.pair (ZFSet.pair x y) z ∈ ratAddGraph

def RatMul (x y z : ZFSet) : Prop :=
  ZFSet.pair (ZFSet.pair x y) z ∈ ratMulGraph

def RatNeg (x y : ZFSet) : Prop :=
  ZFSet.pair x y ∈ ratNegGraph

/-! ## Existencia y unicidad local -/

theorem RatAdd_unique
    {x y z₁ z₂ : ZFSet}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (h₁ : RatAdd x y z₁) (h₂ : RatAdd x y z₂) : z₁ = z₂ := by
  have hxy := mem_cartesianProductFoundational.mpr ⟨hx, hy⟩
  rcases ratAddGraph_isFunc.2 (ZFSet.pair x y) hxy with ⟨z, hz, hUnique⟩
  have hz₁ := funcFoundational_value_mem ratAddGraph_isFunc h₁
  have hz₂ := funcFoundational_value_mem ratAddGraph_isFunc h₂
  exact (hUnique z₁ ⟨hz₁, h₁⟩).trans (hUnique z₂ ⟨hz₂, h₂⟩).symm

theorem RatMul_unique
    {x y z₁ z₂ : ZFSet}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (h₁ : RatMul x y z₁) (h₂ : RatMul x y z₂) : z₁ = z₂ := by
  have hxy := mem_cartesianProductFoundational.mpr ⟨hx, hy⟩
  rcases ratMulGraph_isFunc.2 (ZFSet.pair x y) hxy with ⟨z, hz, hUnique⟩
  have hz₁ := funcFoundational_value_mem ratMulGraph_isFunc h₁
  have hz₂ := funcFoundational_value_mem ratMulGraph_isFunc h₂
  exact (hUnique z₁ ⟨hz₁, h₁⟩).trans (hUnique z₂ ⟨hz₂, h₂⟩).symm

theorem RatNeg_unique
    {x y₁ y₂ : ZFSet}
    (hx : x ∈ rationalsTA)
    (h₁ : RatNeg x y₁) (h₂ : RatNeg x y₂) : y₁ = y₂ := by
  rcases ratNegGraph_isFunc.2 x hx with ⟨y, hy, hUnique⟩
  have hy₁ := funcFoundational_value_mem ratNegGraph_isFunc h₁
  have hy₂ := funcFoundational_value_mem ratNegGraph_isFunc h₂
  exact (hUnique y₁ ⟨hy₁, h₁⟩).trans (hUnique y₂ ⟨hy₂, h₂⟩).symm

theorem ratAdd_exists {x y : ZFSet}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA) :
    ∃ z : ZFSet, z ∈ rationalsTA ∧ RatAdd x y z := by
  rcases ratAddGraph_isFunc.2 _
      (mem_cartesianProductFoundational.mpr ⟨hx, hy⟩) with ⟨z, hz, _⟩
  exact ⟨z, hz⟩

theorem ratMul_exists {x y : ZFSet}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA) :
    ∃ z : ZFSet, z ∈ rationalsTA ∧ RatMul x y z := by
  rcases ratMulGraph_isFunc.2 _
      (mem_cartesianProductFoundational.mpr ⟨hx, hy⟩) with ⟨z, hz, _⟩
  exact ⟨z, hz⟩

theorem ratNeg_exists {x : ZFSet} (hx : x ∈ rationalsTA) :
    ∃ y : ZFSet, y ∈ rationalsTA ∧ RatNeg x y := by
  rcases ratNegGraph_isFunc.2 x hx with ⟨y, hy, _⟩
  exact ⟨y, hy⟩

theorem exists_ratClass_pair_of_mem {x : ZFSet} (hx : x ∈ rationalsTA) :
    ∃ a b : ZFSet, a ∈ integersTA ∧ b ∈ intNonzeroTA ∧
      x = ratClass (ZFSet.pair a b) := by
  rcases mem_rationalsTA_iff.mp hx with ⟨p, hp, rfl⟩
  rcases mem_ratDomain_iff.mp hp with ⟨a, b, ha, hb, rfl⟩
  exact ⟨a, b, ha, hb, rfl⟩

theorem intMul_zero_left
    {x z : ZFSet} (hx : x ∈ integersTA) (hMul : IntMul intZero x z) :
    z = intZero := by
  rcases intMul_exists hx intZero_mem_integersTA with ⟨w, _hw, hwMul⟩
  have hzw : z = w := intMul_comm intZero_mem_integersTA hx hMul hwMul
  exact hzw.trans (intMul_zero_right hx hwMul)

/-! ## Leyes aditivas racionales -/

theorem ratAdd_comm
    {x y xy yx : ZFSet}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (hxy : RatAdd x y xy) (hyx : RatAdd y x yx) : xy = yx := by
  rcases exists_ratClass_pair_of_mem hx with ⟨a, b, ha, hb, rfl⟩
  rcases exists_ratClass_pair_of_mem hy with ⟨c, d, hc, hd, rfl⟩
  rcases intMul_exists ha (mem_intNonzeroTA_iff.mp hd).1 with ⟨ad, hadMem, had⟩
  rcases intMul_exists (mem_intNonzeroTA_iff.mp hb).1 hc with ⟨bc, hbcMem, hbc⟩
  rcases intAdd_exists hadMem hbcMem with ⟨u, huMem, hu⟩
  rcases intMul_exists (mem_intNonzeroTA_iff.mp hb).1
      (mem_intNonzeroTA_iff.mp hd).1 with ⟨v, _hvMem, hv⟩
  rcases intMul_exists hc (mem_intNonzeroTA_iff.mp hb).1 with ⟨cb, hcbMem, hcb⟩
  rcases intMul_exists (mem_intNonzeroTA_iff.mp hd).1 ha with ⟨da, hdaMem, hda⟩
  rcases intAdd_exists hcbMem hdaMem with ⟨u', _hu'Mem, hu'⟩
  rcases intMul_exists (mem_intNonzeroTA_iff.mp hd).1
      (mem_intNonzeroTA_iff.mp hb).1 with ⟨v', _hv'Mem, hv'⟩
  have hadEq : ad = da := intMul_comm ha (mem_intNonzeroTA_iff.mp hd).1 had hda
  have hbcEq : bc = cb := intMul_comm (mem_intNonzeroTA_iff.mp hb).1 hc hbc hcb
  have huEq : u = u' := by
    have huRev : IntAdd bc ad u' := by
      rw [hbcEq, hadEq]
      exact hu'
    exact intAdd_comm hadMem hbcMem hu huRev
  have hvEq : v = v' := intMul_comm
    (mem_intNonzeroTA_iff.mp hb).1 (mem_intNonzeroTA_iff.mp hd).1 hv hv'
  have hxyVal := (ratAddGraph_classes_value_iff ha hb hc hd had hbc hu hv).mp hxy
  have hyxVal := (ratAddGraph_classes_value_iff hc hd ha hb hcb hda hu' hv').mp hyx
  rw [hxyVal, hyxVal, huEq, hvEq]

theorem ratAdd_zero_right
    {x z : ZFSet} (hx : x ∈ rationalsTA) (h : RatAdd x ratZero z) : z = x := by
  rcases exists_ratClass_pair_of_mem hx with ⟨a, b, ha, hb, rfl⟩
  rcases intMul_exists ha intOne_mem_integersTA with ⟨a1, ha1Mem, ha1⟩
  rcases intMul_exists (mem_intNonzeroTA_iff.mp hb).1 intZero_mem_integersTA with
    ⟨b0, hb0Mem, hb0⟩
  rcases intAdd_exists ha1Mem hb0Mem with ⟨u, _huMem, hu⟩
  rcases intMul_exists (mem_intNonzeroTA_iff.mp hb).1 intOne_mem_integersTA with
    ⟨v, _hvMem, hv⟩
  have hz := (ratAddGraph_classes_value_iff ha hb intZero_mem_integersTA
    intOne_mem_intNonzeroTA ha1 hb0 hu hv).mp h
  have ha1Eq := intMul_one_right ha ha1
  have hb0Eq := intMul_zero_right (mem_intNonzeroTA_iff.mp hb).1 hb0
  have huEq : u = a := by
    rw [ha1Eq, hb0Eq] at hu
    exact intAdd_zero_right ha hu
  have hvEq := intMul_one_right (mem_intNonzeroTA_iff.mp hb).1 hv
  rw [hz, huEq, hvEq]

theorem ratAdd_zero_left
    {x z : ZFSet} (hx : x ∈ rationalsTA) (h : RatAdd ratZero x z) : z = x := by
  rcases ratAdd_exists hx ratZero_mem_rationalsTA with ⟨w, _hw, hw⟩
  have hcomm : z = w := ratAdd_comm ratZero_mem_rationalsTA hx h hw
  exact hcomm.trans (ratAdd_zero_right hx hw)

theorem ratAdd_assoc
    {x y z xy lhs yz rhs : ZFSet}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA) (hz : z ∈ rationalsTA)
    (hxy : RatAdd x y xy) (hlhs : RatAdd xy z lhs)
    (hyz : RatAdd y z yz) (hrhs : RatAdd x yz rhs) : lhs = rhs := by
  rcases exists_ratClass_pair_of_mem hx with ⟨a, b, ha, hb, rfl⟩
  rcases exists_ratClass_pair_of_mem hy with ⟨c, d, hc, hd, rfl⟩
  rcases exists_ratClass_pair_of_mem hz with ⟨e, f, he, hf, rfl⟩
  have hbI := (mem_intNonzeroTA_iff.mp hb).1
  have hdI := (mem_intNonzeroTA_iff.mp hd).1
  have hfI := (mem_intNonzeroTA_iff.mp hf).1
  rcases intMul_exists ha hdI with ⟨ad, hadM, had⟩
  rcases intMul_exists hbI hc with ⟨bc, hbcM, hbc⟩
  rcases intAdd_exists hadM hbcM with ⟨s₁, hs₁M, hs₁⟩
  rcases intMul_exists hbI hdI with ⟨bd, hbdM, hbd⟩
  have hbdNZ := intNonzero_mul_closed hb hd hbd
  have hxyVal := (ratAddGraph_classes_value_iff ha hb hc hd had hbc hs₁ hbd).mp hxy
  rw [hxyVal] at hlhs
  rcases intMul_exists hs₁M hfI with ⟨s₁f, hs₁fM, hs₁f⟩
  rcases intMul_exists hbdM he with ⟨bde, hbdeM, hbde⟩
  rcases intAdd_exists hs₁fM hbdeM with ⟨nL, hnLM, hnL⟩
  rcases intMul_exists hbdM hfI with ⟨dL, _hdLM, hdL⟩
  have hlhsVal := (ratAddGraph_classes_value_iff hs₁M hbdNZ he hf
    hs₁f hbde hnL hdL).mp hlhs

  rcases intMul_exists hc hfI with ⟨cf, hcfM, hcf⟩
  rcases intMul_exists hdI he with ⟨de, hdeM, hde⟩
  rcases intAdd_exists hcfM hdeM with ⟨s₂, hs₂M, hs₂⟩
  rcases intMul_exists hdI hfI with ⟨df, hdfM, hdf⟩
  have hdfNZ := intNonzero_mul_closed hd hf hdf
  have hyzVal := (ratAddGraph_classes_value_iff hc hd he hf hcf hde hs₂ hdf).mp hyz
  rw [hyzVal] at hrhs
  rcases intMul_exists ha hdfM with ⟨adf', hadf'M, hadf'⟩
  rcases intMul_exists hbI hs₂M with ⟨bs₂, hbs₂M, hbs₂⟩
  rcases intAdd_exists hadf'M hbs₂M with ⟨nR, _hnRM, hnR⟩
  rcases intMul_exists hbI hdfM with ⟨dR, _hdRM, hdR⟩
  have hrhsVal := (ratAddGraph_classes_value_iff ha hb hs₂M hdfNZ
    hadf' hbs₂ hnR hdR).mp hrhs

  rcases intMul_exists hadM hfI with ⟨adf, hadfM, hadf⟩
  rcases intMul_exists hbcM hfI with ⟨bcf, hbcfM, hbcf⟩
  rcases intAdd_exists hadfM hbcfM with ⟨t₁, ht₁M, ht₁⟩
  have hs₁fEq : s₁f = t₁ :=
    intAdd_mul_right hadM hbcM hfI hs₁ hs₁f hadf hbcf ht₁
  have hnL' : IntAdd t₁ bde nL := by rw [← hs₁fEq]; exact hnL

  rcases intMul_exists hbI hcfM with ⟨bcf', hbcf'M, hbcf'⟩
  rcases intMul_exists hbI hdeM with ⟨bde', hbde'M, hbde'⟩
  rcases intAdd_exists hbcf'M hbde'M with ⟨t₂, ht₂M, ht₂⟩
  have hbs₂Eq : bs₂ = t₂ :=
    intMul_add_left hbI hcfM hdeM hs₂ hbs₂ hbcf' hbde' ht₂
  have hadfEq : adf = adf' :=
    intMul_assoc ha hdI hfI had hadf hdf hadf'
  have hbcfEq : bcf = bcf' :=
    intMul_assoc hbI hc hfI hbc hbcf hcf hbcf'
  have hbdeEq : bde = bde' :=
    intMul_assoc hbI hdI he hbd hbde hde hbde'
  have hnR' : IntAdd adf t₂ nR := by
    rw [hadfEq, ← hbs₂Eq]
    exact hnR
  have hnEq : nL = nR := by
    have ht₂' : IntAdd bcf bde t₂ := by
      rw [hbcfEq, hbdeEq]
      exact ht₂
    exact intAdd_assoc hadfM hbcfM hbdeM ht₁ hnL' ht₂' hnR'
  have hdEq : dL = dR := intMul_assoc hbI hdI hfI hbd hdL hdf hdR
  rw [hlhsVal, hrhsVal, hnEq, hdEq]

theorem ratAdd_neg_right
    {x nx z : ZFSet}
    (hx : x ∈ rationalsTA) (hNeg : RatNeg x nx)
    (hAdd : RatAdd x nx z) : z = ratZero := by
  rcases exists_ratClass_pair_of_mem hx with ⟨a, b, ha, hb, rfl⟩
  have hbI := (mem_intNonzeroTA_iff.mp hb).1
  rcases intNegGraph_isFunc.2 a ha with ⟨na, hna, _⟩
  have hnaM := hna.1
  have hIntNeg : IntNeg a na := hna.2
  have hNegVal := (ratNegGraph_classes_value_iff ha hb hIntNeg).mp hNeg
  rw [hNegVal] at hAdd
  rcases intMul_exists ha hbI with ⟨ab, habM, hab⟩
  rcases intMul_exists hbI hnaM with ⟨bna, hbnaM, hbna⟩
  rcases intAdd_exists habM hbnaM with ⟨s, hsM, hs⟩
  rcases intMul_exists hbI hbI with ⟨bb, hbbM, hbb⟩
  have hbbNZ := intNonzero_mul_closed hb hb hbb
  have hzVal := (ratAddGraph_classes_value_iff ha hb hnaM hb
    hab hbna hs hbb).mp hAdd
  rcases intMul_exists hnaM hbI with ⟨nab, hnabM, hnab⟩
  have hbnaEq : bna = nab := intMul_comm hbI hnaM hbna hnab
  have hNegProd : IntNeg ab bna := by
    rw [hbnaEq]
    exact intMul_neg_left ha hnaM hbI hIntNeg hab hnab
  have hsZero : s = intZero := intAdd_neg_right habM hNegProd hs
  have hClassZero :
      ratClass (ZFSet.pair intZero bb) = ratZero := by
    unfold ratZero
    apply (TA_PRO_00053_ratClass_pairs_eq_iff intZero_mem_integersTA hbbNZ
      intZero_mem_integersTA intOne_mem_intNonzeroTA).mpr
    rcases intMul_exists intZero_mem_integersTA intOne_mem_integersTA with
      ⟨l, _hlM, hl⟩
    rcases intMul_exists hbbM intZero_mem_integersTA with ⟨r, _hrM, hr⟩
    exact ⟨l, r, hl, hr,
      (intMul_zero_left intOne_mem_integersTA hl).trans
        (intMul_zero_right hbbM hr).symm⟩
  rw [hzVal, hsZero, hClassZero]

theorem ratAdd_neg_left
    {x nx z : ZFSet}
    (hx : x ∈ rationalsTA) (hNeg : RatNeg x nx)
    (hAdd : RatAdd nx x z) : z = ratZero := by
  have hnx := funcFoundational_value_mem ratNegGraph_isFunc hNeg
  rcases ratAdd_exists hx hnx with ⟨w, _hw, hw⟩
  have hcomm : z = w := ratAdd_comm hnx hx hAdd hw
  exact hcomm.trans (ratAdd_neg_right hx hNeg hw)

theorem TA_PRO_00056_additive_group_laws :
    (∀ {x y z xy lhs yz rhs : ZFSet},
      x ∈ rationalsTA → y ∈ rationalsTA → z ∈ rationalsTA →
      RatAdd x y xy → RatAdd xy z lhs → RatAdd y z yz →
      RatAdd x yz rhs → lhs = rhs) ∧
    (∀ {x y xy yx : ZFSet}, x ∈ rationalsTA → y ∈ rationalsTA →
      RatAdd x y xy → RatAdd y x yx → xy = yx) ∧
    (∀ {x z : ZFSet}, x ∈ rationalsTA → RatAdd ratZero x z → z = x) ∧
    (∀ {x z : ZFSet}, x ∈ rationalsTA → RatAdd x ratZero z → z = x) ∧
    (∀ {x nx z : ZFSet}, x ∈ rationalsTA → RatNeg x nx →
      RatAdd nx x z → z = ratZero) ∧
    (∀ {x nx z : ZFSet}, x ∈ rationalsTA → RatNeg x nx →
      RatAdd x nx z → z = ratZero) := by
  exact ⟨ratAdd_assoc, ratAdd_comm, ratAdd_zero_left, ratAdd_zero_right,
    ratAdd_neg_left, ratAdd_neg_right⟩

/-! ## Leyes multiplicativas racionales -/

theorem ratMul_assoc
    {x y z xy lhs yz rhs : ZFSet}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA) (hz : z ∈ rationalsTA)
    (hxy : RatMul x y xy) (hlhs : RatMul xy z lhs)
    (hyz : RatMul y z yz) (hrhs : RatMul x yz rhs) : lhs = rhs := by
  rcases exists_ratClass_pair_of_mem hx with ⟨a, b, ha, hb, rfl⟩
  rcases exists_ratClass_pair_of_mem hy with ⟨c, d, hc, hd, rfl⟩
  rcases exists_ratClass_pair_of_mem hz with ⟨e, f, he, hf, rfl⟩
  have hbI := (mem_intNonzeroTA_iff.mp hb).1
  have hdI := (mem_intNonzeroTA_iff.mp hd).1
  have hfI := (mem_intNonzeroTA_iff.mp hf).1
  rcases intMul_exists ha hc with ⟨ac, hacM, hac⟩
  rcases intMul_exists hbI hdI with ⟨bd, hbdM, hbd⟩
  have hbdNZ := intNonzero_mul_closed hb hd hbd
  have hxyVal := (ratMulGraph_classes_value_iff ha hb hc hd hac hbd).mp hxy
  rw [hxyVal] at hlhs
  rcases intMul_exists hacM he with ⟨ace, _haceM, hace⟩
  rcases intMul_exists hbdM hfI with ⟨bdf, _hbdfM, hbdf⟩
  have hlhsVal := (ratMulGraph_classes_value_iff hacM hbdNZ he hf hace hbdf).mp hlhs
  rcases intMul_exists hc he with ⟨ce, hceM, hce⟩
  rcases intMul_exists hdI hfI with ⟨df, hdfM, hdf⟩
  have hdfNZ := intNonzero_mul_closed hd hf hdf
  have hyzVal := (ratMulGraph_classes_value_iff hc hd he hf hce hdf).mp hyz
  rw [hyzVal] at hrhs
  rcases intMul_exists ha hceM with ⟨ace', _hace'M, hace'⟩
  rcases intMul_exists hbI hdfM with ⟨bdf', _hbdf'M, hbdf'⟩
  have hrhsVal := (ratMulGraph_classes_value_iff ha hb hceM hdfNZ hace' hbdf').mp hrhs
  have hn : ace = ace' := intMul_assoc ha hc he hac hace hce hace'
  have hdv : bdf = bdf' := intMul_assoc hbI hdI hfI hbd hbdf hdf hbdf'
  rw [hlhsVal, hrhsVal, hn, hdv]

theorem ratMul_comm
    {x y xy yx : ZFSet}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (hxy : RatMul x y xy) (hyx : RatMul y x yx) : xy = yx := by
  rcases exists_ratClass_pair_of_mem hx with ⟨a, b, ha, hb, rfl⟩
  rcases exists_ratClass_pair_of_mem hy with ⟨c, d, hc, hd, rfl⟩
  have hbI := (mem_intNonzeroTA_iff.mp hb).1
  have hdI := (mem_intNonzeroTA_iff.mp hd).1
  rcases intMul_exists ha hc with ⟨ac, _hacM, hac⟩
  rcases intMul_exists hbI hdI with ⟨bd, _hbdM, hbd⟩
  rcases intMul_exists hc ha with ⟨ca, _hcaM, hca⟩
  rcases intMul_exists hdI hbI with ⟨db, _hdbM, hdb⟩
  have hxyVal := (ratMulGraph_classes_value_iff ha hb hc hd hac hbd).mp hxy
  have hyxVal := (ratMulGraph_classes_value_iff hc hd ha hb hca hdb).mp hyx
  have hn := intMul_comm ha hc hac hca
  have hdv := intMul_comm hbI hdI hbd hdb
  rw [hxyVal, hyxVal, hn, hdv]

theorem ratMul_one_right
    {x z : ZFSet} (hx : x ∈ rationalsTA) (h : RatMul x ratOne z) : z = x := by
  rcases exists_ratClass_pair_of_mem hx with ⟨a, b, ha, hb, rfl⟩
  have hbI := (mem_intNonzeroTA_iff.mp hb).1
  rcases intMul_exists ha intOne_mem_integersTA with ⟨a1, _ha1M, ha1⟩
  rcases intMul_exists hbI intOne_mem_integersTA with ⟨b1, _hb1M, hb1⟩
  have hzVal := (ratMulGraph_classes_value_iff ha hb intOne_mem_integersTA
    intOne_mem_intNonzeroTA ha1 hb1).mp h
  rw [hzVal, intMul_one_right ha ha1, intMul_one_right hbI hb1]

theorem ratMul_one_left
    {x z : ZFSet} (hx : x ∈ rationalsTA) (h : RatMul ratOne x z) : z = x := by
  rcases ratMul_exists hx ratOne_mem_rationalsTA with ⟨w, _hw, hw⟩
  have hcomm : z = w := ratMul_comm ratOne_mem_rationalsTA hx h hw
  exact hcomm.trans (ratMul_one_right hx hw)

/-- Multiplicar simultáneamente numerador y denominador por un entero no nulo
no cambia la clase racional. -/
theorem ratClass_scale_left
    {n d s sn sd : ZFSet}
    (hn : n ∈ integersTA) (hd : d ∈ intNonzeroTA) (hs : s ∈ intNonzeroTA)
    (hsn : IntMul s n sn) (hsd : IntMul s d sd) :
    ratClass (ZFSet.pair n d) = ratClass (ZFSet.pair sn sd) := by
  have hdI := (mem_intNonzeroTA_iff.mp hd).1
  have hsI := (mem_intNonzeroTA_iff.mp hs).1
  have hsnM := funcFoundational_value_mem intMulGraph_isFunc hsn
  have hsdNZ := intNonzero_mul_closed hs hd hsd
  apply (TA_PRO_00053_ratClass_pairs_eq_iff hn hd hsnM hsdNZ).mpr
  rcases intMul_exists hn (funcFoundational_value_mem intMulGraph_isFunc hsd) with
    ⟨left, _hleftM, hleft⟩
  rcases intMul_exists hdI hsnM with ⟨right, _hrightM, hright⟩
  rcases intMul_exists hn hsI with ⟨ns, hnsM, hns⟩
  have hnsEq : ns = sn := intMul_comm hn hsI hns hsn
  rcases intMul_exists hnsM hdI with ⟨middle, _hmiddleM, hmiddle⟩
  have hMidLeft : middle = left :=
    intMul_assoc hn hsI hdI hns hmiddle hsd hleft
  have hMiddle' : IntMul sn d middle := by rw [← hnsEq]; exact hmiddle
  have hRightMid : right = middle := intMul_comm hdI hsnM hright hMiddle'
  exact ⟨left, right, hleft, hright, hMidLeft.symm.trans hRightMid.symm⟩

theorem ratMul_add_left
    {x y z yz lhs xy xz rhs : ZFSet}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA) (hz : z ∈ rationalsTA)
    (hyz : RatAdd y z yz) (hlhs : RatMul x yz lhs)
    (hxy : RatMul x y xy) (hxz : RatMul x z xz)
    (hrhs : RatAdd xy xz rhs) : lhs = rhs := by
  rcases exists_ratClass_pair_of_mem hx with ⟨a, b, ha, hb, rfl⟩
  rcases exists_ratClass_pair_of_mem hy with ⟨c, d, hc, hd, rfl⟩
  rcases exists_ratClass_pair_of_mem hz with ⟨e, f, he, hf, rfl⟩
  have hbI := (mem_intNonzeroTA_iff.mp hb).1
  have hdI := (mem_intNonzeroTA_iff.mp hd).1
  have hfI := (mem_intNonzeroTA_iff.mp hf).1

  rcases intMul_exists hc hfI with ⟨cf, hcfM, hcf⟩
  rcases intMul_exists hdI he with ⟨de, hdeM, hde⟩
  rcases intAdd_exists hcfM hdeM with ⟨s, hsM, hsAdd⟩
  rcases intMul_exists hdI hfI with ⟨df, hdfM, hdf⟩
  have hdfNZ := intNonzero_mul_closed hd hf hdf
  have hyzVal := (ratAddGraph_classes_value_iff hc hd he hf hcf hde hsAdd hdf).mp hyz
  rw [hyzVal] at hlhs
  rcases intMul_exists ha hsM with ⟨nL, hnLM, hnL⟩
  rcases intMul_exists hbI hdfM with ⟨dL, hdLM, hdL⟩
  have hdLNZ := intNonzero_mul_closed hb hdfNZ hdL
  have hlhsVal := (ratMulGraph_classes_value_iff ha hb hsM hdfNZ hnL hdL).mp hlhs

  rcases intMul_exists ha hc with ⟨ac, hacM, hac⟩
  rcases intMul_exists hbI hdI with ⟨bd, hbdM, hbd⟩
  have hbdNZ := intNonzero_mul_closed hb hd hbd
  have hxyVal := (ratMulGraph_classes_value_iff ha hb hc hd hac hbd).mp hxy
  rcases intMul_exists ha he with ⟨ae, haeM, hae⟩
  rcases intMul_exists hbI hfI with ⟨bf, hbfM, hbf⟩
  have hbfNZ := intNonzero_mul_closed hb hf hbf
  have hxzVal := (ratMulGraph_classes_value_iff ha hb he hf hae hbf).mp hxz
  rw [hxyVal, hxzVal] at hrhs
  rcases intMul_exists hacM hbfM with ⟨r₁, hr₁M, hr₁⟩
  rcases intMul_exists hbdM haeM with ⟨r₂, hr₂M, hr₂⟩
  rcases intAdd_exists hr₁M hr₂M with ⟨rSum, hrSumM, hrSum⟩
  rcases intMul_exists hbdM hbfM with ⟨dR, hdRM, hdR⟩
  have hrhsVal := (ratAddGraph_classes_value_iff hacM hbdNZ haeM hbfNZ
    hr₁ hr₂ hrSum hdR).mp hrhs

  rcases intMul_exists hbI hnLM with ⟨bnL, hbnLM, hbnL⟩
  rcases intMul_exists hbI hdLM with ⟨bdL, hbdLM, hbdL⟩
  have hScaled : ratClass (ZFSet.pair nL dL) = ratClass (ZFSet.pair bnL bdL) :=
    ratClass_scale_left hnLM hdLNZ hb hbnL hbdL

  rcases intMul_exists ha hcfM with ⟨acf, hacfM, hacf⟩
  rcases intMul_exists ha hdeM with ⟨ade, hadeM, hade⟩
  rcases intAdd_exists hacfM hadeM with ⟨aSum, haSumM, haSum⟩
  have hnLEq : nL = aSum :=
    intMul_add_left ha hcfM hdeM hsAdd hnL hacf hade haSum
  have hbnL' : IntMul b aSum bnL := by rw [← hnLEq]; exact hbnL
  rcases intMul_exists hbI hacfM with ⟨bacf, hbacfM, hbacf⟩
  rcases intMul_exists hbI hadeM with ⟨bade, hbadeM, hbade⟩
  rcases intAdd_exists hbacfM hbadeM with ⟨bSum, hbSumM, hbSum⟩
  have hbnLEq : bnL = bSum :=
    intMul_add_left hbI hacfM hadeM haSum hbnL' hbacf hbade hbSum

  rcases intMul_exists ha hbI with ⟨ab, habM, hab⟩
  rcases intMul_exists hbI ha with ⟨ba, hbaM, hba⟩
  have habEq : ab = ba := intMul_comm ha hbI hab hba
  rcases intMul_exists habM hcfM with ⟨abcf, habcfM, habcf⟩
  have hr₁Eq : r₁ = abcf :=
    intPairProducts_exchange_middle ha hc hbI hfI hac hbf hab hcf hr₁ habcf
  have hbaCf : IntMul ba cf abcf := by rw [← habEq]; exact habcf
  have habcfEq : abcf = bacf :=
    intMul_assoc hbI ha hcfM hba hbaCf hacf hbacf
  have hr₁Bacf : r₁ = bacf := hr₁Eq.trans habcfEq

  rcases intMul_exists habM hdeM with ⟨abde, habdeM, habde⟩
  have hbaDe : IntMul ba de abde := by rw [← habEq]; exact habde
  have hr₂Eq : r₂ = abde :=
    intPairProducts_exchange_middle hbI hdI ha he hbd hae hba hde hr₂ hbaDe
  have habdeEq : abde = bade :=
    intMul_assoc hbI ha hdeM hba hbaDe hade hbade
  have hr₂Bade : r₂ = bade := hr₂Eq.trans habdeEq
  have hrSum' : IntAdd bacf bade rSum := by
    rw [← hr₁Bacf, ← hr₂Bade]
    exact hrSum
  have hbSumEq : bSum = rSum := IntAdd_unique hbacfM hbadeM hbSum hrSum'
  have hNum : bnL = rSum := hbnLEq.trans hbSumEq

  rcases intMul_exists hbI hbI with ⟨bb, hbbM, hbb⟩
  rcases intMul_exists hbbM hdfM with ⟨bbdf, hbbdfM, hbbdf⟩
  have hbdLEq : bbdf = bdL :=
    intMul_assoc hbI hbI hdfM hbb hbbdf hdL hbdL
  have hdREq : dR = bbdf :=
    intPairProducts_exchange_middle hbI hdI hbI hfI hbd hbf hbb hdf hdR hbbdf
  have hDen : bdL = dR := hbdLEq.symm.trans hdREq.symm
  rw [hlhsVal, hrhsVal]
  exact hScaled.trans (by rw [hNum, hDen])

theorem ratAdd_mul_right
    {x y z xy lhs xz yz rhs : ZFSet}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA) (hz : z ∈ rationalsTA)
    (hxy : RatAdd x y xy) (hlhs : RatMul xy z lhs)
    (hxz : RatMul x z xz) (hyz : RatMul y z yz)
    (hrhs : RatAdd xz yz rhs) : lhs = rhs := by
  have hxyM := funcFoundational_value_mem ratAddGraph_isFunc hxy
  have hxzM := funcFoundational_value_mem ratMulGraph_isFunc hxz
  have hyzM := funcFoundational_value_mem ratMulGraph_isFunc hyz
  rcases ratMul_exists hz hxyM with ⟨lhs', _hlhs'M, hlhs'⟩
  rcases ratMul_exists hz hx with ⟨zx, hzxM, hzx⟩
  rcases ratMul_exists hz hy with ⟨zy, hzyM, hzy⟩
  rcases ratAdd_exists hzxM hzyM with ⟨rhs', _hrhs'M, hrhs'⟩
  have hLeftComm : lhs = lhs' := ratMul_comm hxyM hz hlhs hlhs'
  have hxComm : xz = zx := ratMul_comm hx hz hxz hzx
  have hyComm : yz = zy := ratMul_comm hy hz hyz hzy
  have hDistrib : lhs' = rhs' :=
    ratMul_add_left hz hx hy hxy hlhs' hzx hzy hrhs'
  have hrhsAt : RatAdd xz yz rhs' := by
    rw [hxComm, hyComm]
    exact hrhs'
  have hRight : rhs' = rhs := RatAdd_unique hxzM hyzM hrhsAt hrhs
  exact hLeftComm.trans (hDistrib.trans hRight)

theorem TA_PRO_00058_mul_distrib_laws :
    (∀ {x y z xy lhs yz rhs : ZFSet},
      x ∈ rationalsTA → y ∈ rationalsTA → z ∈ rationalsTA →
      RatMul x y xy → RatMul xy z lhs → RatMul y z yz →
      RatMul x yz rhs → lhs = rhs) ∧
    (∀ {x y xy yx : ZFSet}, x ∈ rationalsTA → y ∈ rationalsTA →
      RatMul x y xy → RatMul y x yx → xy = yx) ∧
    (∀ {x z : ZFSet}, x ∈ rationalsTA → RatMul ratOne x z → z = x) ∧
    (∀ {x z : ZFSet}, x ∈ rationalsTA → RatMul x ratOne z → z = x) ∧
    (∀ {x y z yz lhs xy xz rhs : ZFSet},
      x ∈ rationalsTA → y ∈ rationalsTA → z ∈ rationalsTA →
      RatAdd y z yz → RatMul x yz lhs → RatMul x y xy →
      RatMul x z xz → RatAdd xy xz rhs → lhs = rhs) ∧
    (∀ {x y z xy lhs xz yz rhs : ZFSet},
      x ∈ rationalsTA → y ∈ rationalsTA → z ∈ rationalsTA →
      RatAdd x y xy → RatMul xy z lhs → RatMul x z xz →
      RatMul y z yz → RatAdd xz yz rhs → lhs = rhs) := by
  exact ⟨ratMul_assoc, ratMul_comm, ratMul_one_left, ratMul_one_right,
    ratMul_add_left, ratAdd_mul_right⟩

theorem TA_PRO_00059_ratZero_ne_one : ratZero ≠ ratOne := by
  intro h
  have hCross := (TA_PRO_00053_ratClass_pairs_eq_iff
    intZero_mem_integersTA intOne_mem_intNonzeroTA
    intOne_mem_integersTA intOne_mem_intNonzeroTA).mp h
  rcases hCross with ⟨u, v, hu, hv, huv⟩
  have huZero : u = intZero := intMul_zero_left intOne_mem_integersTA hu
  have hvOne : v = intOne := intMul_one_left intOne_mem_integersTA hv
  exact TA_PRO_00046_zero_ne_one (huZero.symm.trans (huv.trans hvOne))

/-! ## TA-DEF-00059 — incrustación relacional de los enteros -/

def RatEmbedValue (a q : ZFSet) : Prop :=
  a ∈ integersTA ∧ q = ratClass (ZFSet.pair a intOne)

def ratEmbedGraph : ZFSet :=
  ZFSet.sep
    (fun t =>
      ∃ a q : ZFSet,
        a ∈ integersTA ∧ q ∈ rationalsTA ∧
        t = ZFSet.pair a q ∧ RatEmbedValue a q)
    (pairAmbient integersTA rationalsTA)

theorem mem_ratEmbedGraph {a q : ZFSet} :
    ZFSet.pair a q ∈ ratEmbedGraph ↔
    a ∈ integersTA ∧ q ∈ rationalsTA ∧ RatEmbedValue a q := by
  constructor
  · intro h
    rcases (ZFSet.mem_sep.mp h).2 with ⟨a', q', ha', hq', hp, hv⟩
    rcases ZFSet.pair_injective hp with ⟨haa, hqq⟩
    subst a'
    subst q'
    exact ⟨ha', hq', hv⟩
  · rintro ⟨ha, hq, hv⟩
    apply ZFSet.mem_sep.mpr
    exact ⟨pair_mem_pairAmbient ha hq, a, q, ha, hq, rfl, hv⟩

theorem ratEmbedGraph_isFunc :
    IsFuncFoundational integersTA rationalsTA ratEmbedGraph := by
  constructor
  · intro t ht
    rcases (ZFSet.mem_sep.mp ht).2 with ⟨a, q, ha, hq, rfl, _⟩
    exact ⟨a, ha, q, hq, rfl⟩
  · intro a ha
    have hq : ratClass (ZFSet.pair a intOne) ∈ rationalsTA := by
      apply ratClass_mem_rationalsTA
      exact mem_ratDomain_iff.mpr
        ⟨a, intOne, ha, intOne_mem_intNonzeroTA, rfl⟩
    refine ⟨ratClass (ZFSet.pair a intOne), ?_, ?_⟩
    · exact ⟨hq, mem_ratEmbedGraph.mpr
        ⟨ha, hq, ha, rfl⟩⟩
    · intro q' hq'
      have hv := (mem_ratEmbedGraph.mp hq'.2).2.2
      exact hv.2

theorem ratEmbedGraph_value {a : ZFSet} (ha : a ∈ integersTA) :
    ZFSet.pair a (ratClass (ZFSet.pair a intOne)) ∈ ratEmbedGraph := by
  apply mem_ratEmbedGraph.mpr
  have hq : ratClass (ZFSet.pair a intOne) ∈ rationalsTA := by
    apply ratClass_mem_rationalsTA
    exact mem_ratDomain_iff.mpr
      ⟨a, intOne, ha, intOne_mem_intNonzeroTA, rfl⟩
  exact ⟨ha, hq, ha, rfl⟩

theorem ratEmbedGraph_injective
    {a c q : ZFSet}
    (haq : ZFSet.pair a q ∈ ratEmbedGraph)
    (hcq : ZFSet.pair c q ∈ ratEmbedGraph) : a = c := by
  have hA := mem_ratEmbedGraph.mp haq
  have hC := mem_ratEmbedGraph.mp hcq
  have hClasses : ratClass (ZFSet.pair a intOne) =
      ratClass (ZFSet.pair c intOne) := hA.2.2.2.symm.trans hC.2.2.2
  have hCross := (TA_PRO_00053_ratClass_pairs_eq_iff hA.1
    intOne_mem_intNonzeroTA hC.1 intOne_mem_intNonzeroTA).mp hClasses
  rcases hCross with ⟨u, v, hu, hv, huv⟩
  have huA : u = a := intMul_one_right hA.1 hu
  have hvC : v = c := intMul_one_left hC.1 hv
  exact huA.symm.trans (huv.trans hvC)

theorem ratEmbedGraph_zero :
    ZFSet.pair intZero ratZero ∈ ratEmbedGraph := by
  simpa [ratZero] using ratEmbedGraph_value intZero_mem_integersTA

theorem ratEmbedGraph_one :
    ZFSet.pair intOne ratOne ∈ ratEmbedGraph := by
  simpa [ratOne] using ratEmbedGraph_value intOne_mem_integersTA

theorem ratEmbedGraph_add
    {a c s ja jc js : ZFSet}
    (hja : ZFSet.pair a ja ∈ ratEmbedGraph)
    (hjc : ZFSet.pair c jc ∈ ratEmbedGraph)
    (hjs : ZFSet.pair s js ∈ ratEmbedGraph)
    (hAdd : IntAdd a c s) : RatAdd ja jc js := by
  have hA := mem_ratEmbedGraph.mp hja
  have hC := mem_ratEmbedGraph.mp hjc
  have hS := mem_ratEmbedGraph.mp hjs
  rcases intMul_exists hA.1 intOne_mem_integersTA with ⟨a1, ha1M, ha1⟩
  rcases intMul_exists intOne_mem_integersTA hC.1 with ⟨c1, hc1M, hc1⟩
  rcases intAdd_exists ha1M hc1M with ⟨u, _huM, hu⟩
  rcases intMul_exists intOne_mem_integersTA intOne_mem_integersTA with
    ⟨one, _honeM, hone⟩
  have ha1Eq : a1 = a := intMul_one_right hA.1 ha1
  have hc1Eq : c1 = c := intMul_one_left hC.1 hc1
  have huAt : IntAdd a c u := by rw [← ha1Eq, ← hc1Eq]; exact hu
  have huEq : u = s := IntAdd_unique hA.1 hC.1 huAt hAdd
  have honeEq : one = intOne := intMul_one_left intOne_mem_integersTA hone
  have hFormula := ratAddGraph_classes hA.1 intOne_mem_intNonzeroTA
    hC.1 intOne_mem_intNonzeroTA ha1 hc1 hu hone
  rw [huEq, honeEq] at hFormula
  rw [hA.2.2.2, hC.2.2.2, hS.2.2.2]
  exact hFormula

theorem ratEmbedGraph_mul
    {a c p ja jc jp : ZFSet}
    (hja : ZFSet.pair a ja ∈ ratEmbedGraph)
    (hjc : ZFSet.pair c jc ∈ ratEmbedGraph)
    (hjp : ZFSet.pair p jp ∈ ratEmbedGraph)
    (hMul : IntMul a c p) : RatMul ja jc jp := by
  have hA := mem_ratEmbedGraph.mp hja
  have hC := mem_ratEmbedGraph.mp hjc
  have hP := mem_ratEmbedGraph.mp hjp
  rcases intMul_exists intOne_mem_integersTA intOne_mem_integersTA with
    ⟨one, _honeM, hone⟩
  have honeEq : one = intOne := intMul_one_left intOne_mem_integersTA hone
  have hFormula := ratMulGraph_classes hA.1 intOne_mem_intNonzeroTA
    hC.1 intOne_mem_intNonzeroTA hMul hone
  rw [honeEq] at hFormula
  rw [hA.2.2.2, hC.2.2.2, hP.2.2.2]
  exact hFormula

theorem ratEmbedGraph_neg
    {a na ja jna : ZFSet}
    (hja : ZFSet.pair a ja ∈ ratEmbedGraph)
    (hjna : ZFSet.pair na jna ∈ ratEmbedGraph)
    (hNeg : IntNeg a na) : RatNeg ja jna := by
  have hA := mem_ratEmbedGraph.mp hja
  have hNA := mem_ratEmbedGraph.mp hjna
  have hFormula := ratNegGraph_classes hA.1 intOne_mem_intNonzeroTA hNeg
  rw [hA.2.2.2, hNA.2.2.2]
  exact hFormula

theorem TA_PRO_00060_embedding_properties :
    IsFuncFoundational integersTA rationalsTA ratEmbedGraph ∧
    (∀ {a c q : ZFSet}, ZFSet.pair a q ∈ ratEmbedGraph →
      ZFSet.pair c q ∈ ratEmbedGraph → a = c) ∧
    ZFSet.pair intZero ratZero ∈ ratEmbedGraph ∧
    ZFSet.pair intOne ratOne ∈ ratEmbedGraph ∧
    (∀ {a c s ja jc js : ZFSet},
      ZFSet.pair a ja ∈ ratEmbedGraph →
      ZFSet.pair c jc ∈ ratEmbedGraph →
      ZFSet.pair s js ∈ ratEmbedGraph →
      IntAdd a c s → RatAdd ja jc js) ∧
    (∀ {a c p ja jc jp : ZFSet},
      ZFSet.pair a ja ∈ ratEmbedGraph →
      ZFSet.pair c jc ∈ ratEmbedGraph →
      ZFSet.pair p jp ∈ ratEmbedGraph →
      IntMul a c p → RatMul ja jc jp) ∧
    (∀ {a na ja jna : ZFSet},
      ZFSet.pair a ja ∈ ratEmbedGraph →
      ZFSet.pair na jna ∈ ratEmbedGraph →
      IntNeg a na → RatNeg ja jna) := by
  exact ⟨ratEmbedGraph_isFunc, ratEmbedGraph_injective,
    ratEmbedGraph_zero, ratEmbedGraph_one, ratEmbedGraph_add,
    ratEmbedGraph_mul, ratEmbedGraph_neg⟩

end TratadoAnalisis.Rationals.Algebra
