import TratadoAnalisis.Rationals.OrderWellDefined

namespace TratadoAnalisis.Rationals.OrderDefinition

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
open TratadoAnalisis.Rationals.OrderWellDefined

/-!
# TA-LEAN-0003 — D2a

Definición existencial y set-coded del orden racional, junto con su criterio
práctico sobre representantes de denominador positivo.

No se eligen representantes globalmente y no se crean instancias de orden.
-/

def RatLEWitness (x y : ZFSet) : Prop :=
  ∃ a b c d ad bc : ZFSet,
    a ∈ integersTA ∧
    b ∈ intNonzeroTA ∧
    c ∈ integersTA ∧
    d ∈ intNonzeroTA ∧
    IntLT intZero b ∧
    IntLT intZero d ∧
    x = ratClass (ZFSet.pair a b) ∧
    y = ratClass (ZFSet.pair c d) ∧
    IntMul a d ad ∧
    IntMul b c bc ∧
    IntLE ad bc

/-! TA-DEF-00062 — relación de orden racional como conjunto de pares. -/

def ratOrderRel : ZFSet :=
  ZFSet.sep
    (fun t =>
      ∃ x y : ZFSet,
        x ∈ rationalsTA ∧
        y ∈ rationalsTA ∧
        t = ZFSet.pair x y ∧
        RatLEWitness x y)
    (cartesianProductFoundational rationalsTA rationalsTA)

def RatLE (x y : ZFSet) : Prop :=
  ZFSet.pair x y ∈ ratOrderRel

theorem mem_ratOrderRel_iff {x y : ZFSet} :
    ZFSet.pair x y ∈ ratOrderRel ↔
      x ∈ rationalsTA ∧ y ∈ rationalsTA ∧ RatLEWitness x y := by
  constructor
  · intro h
    rcases (ZFSet.mem_sep.mp h).2 with
      ⟨x', y', hx', hy', hp, hw⟩
    rcases ZFSet.pair_injective hp with ⟨hxx, hyy⟩
    subst x'
    subst y'
    exact ⟨hx', hy', hw⟩
  · rintro ⟨hx, hy, hw⟩
    exact ZFSet.mem_sep.mpr
      ⟨mem_cartesianProductFoundational.mpr ⟨hx, hy⟩,
        x, y, hx, hy, rfl, hw⟩

theorem RatLE_iff_witness {x y : ZFSet} :
    RatLE x y ↔
      x ∈ rationalsTA ∧ y ∈ rationalsTA ∧ RatLEWitness x y := by
  exact mem_ratOrderRel_iff

/-! TA-PRO-00064 — criterio práctico sobre clases de denominador positivo. -/

theorem TA_PRO_00064_ratLE_classes_iff
    {a b c d ad bc : ZFSet}
    (ha : a ∈ integersTA)
    (hb : b ∈ intNonzeroTA)
    (hc : c ∈ integersTA)
    (hd : d ∈ intNonzeroTA)
    (hbPos : IntLT intZero b)
    (hdPos : IntLT intZero d)
    (had : IntMul a d ad)
    (hbc : IntMul b c bc) :
    RatLE
      (ratClass (ZFSet.pair a b))
      (ratClass (ZFSet.pair c d)) ↔
    IntLE ad bc := by
  have hbI : b ∈ integersTA := (mem_intNonzeroTA_iff.mp hb).1
  have hdI : d ∈ integersTA := (mem_intNonzeroTA_iff.mp hd).1
  have hLeftQ :
      ratClass (ZFSet.pair a b) ∈ rationalsTA :=
    ratClass_mem_rationalsTA
      (mem_ratDomain_iff.mpr ⟨a, b, ha, hb, rfl⟩)
  have hRightQ :
      ratClass (ZFSet.pair c d) ∈ rationalsTA :=
    ratClass_mem_rationalsTA
      (mem_ratDomain_iff.mpr ⟨c, d, hc, hd, rfl⟩)

  constructor
  · intro hRat
    rcases (RatLE_iff_witness.mp hRat).2.2 with
      ⟨a', b', c', d', a'd', b'c',
        ha', hb', hc', hd', hb'Pos, hd'Pos,
        hLeftClass, hRightClass, ha'd', hb'c', hCross⟩

    have hb'I : b' ∈ integersTA :=
      (mem_intNonzeroTA_iff.mp hb').1
    have hd'I : d' ∈ integersTA :=
      (mem_intNonzeroTA_iff.mp hd').1

    have hTransport :=
      TA_LEM_00014_cross_comparison_well_defined
        ha hbI ha' hb'I hc hdI hc' hd'I
        hbPos hb'Pos hdPos hd'Pos
        hLeftClass hRightClass
        had hbc ha'd' hb'c'

    exact hTransport.mpr hCross

  · intro hCross
    apply RatLE_iff_witness.mpr
    refine ⟨hLeftQ, hRightQ, ?_⟩
    exact ⟨a, b, c, d, ad, bc,
      ha, hb, hc, hd, hbPos, hdPos,
      rfl, rfl, had, hbc, hCross⟩

end TratadoAnalisis.Rationals.OrderDefinition

