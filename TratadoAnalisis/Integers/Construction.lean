import TratadoAnalisis.Naturals.ArithmeticBridge

namespace TratadoAnalisis.Integers.Construction

open TratadoAnalisis.Naturals.Foundational
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Naturals.ArithmeticBridge

/-! # Construcción conjuntista de los enteros

Una diferencia formal es un miembro de `omegaTA ×₀ omegaTA`. La relación
usa únicamente `natAddGraph`, sin presuponer resta. `Nat` interviene sólo a
través del puente explícito B0 y sus códigos se extraen localmente, sin una
selección global. `integersTA` es literalmente el conjunto de clases, cada
una subconjunto de `intDomain`; no se eligen representantes canónicos ni se
usa `Int` o un cociente de tipos como sustituto del objeto conjuntista.
-/

/-- Dominio de las diferencias formales: `omegaTA ×₀ omegaTA`. -/
def intDomain : ZFSet :=
  cartesianProductFoundational omegaTA omegaTA

/-- Caracterización de los elementos del dominio de diferencias formales. -/
theorem mem_intDomain_iff {p : ZFSet} :
    p ∈ intDomain ↔
      ∃ a b : ZFSet,
        a ∈ omegaTA ∧
        b ∈ omegaTA ∧
        p = ZFSet.pair a b := by
  constructor
  · intro hp
    rw [intDomain, cartesianProductFoundational] at hp
    rcases (ZFSet.mem_sep.mp hp).2 with
      ⟨a, ha, b, hb, hPair⟩
    exact ⟨a, b, ha, hb, hPair⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact mem_cartesianProductFoundational.mpr ⟨ha, hb⟩

/-- TA-DEF-00039 — dos diferencias formales `(a,b)` y `(c,d)` están
relacionadas cuando `a+d` y `b+c` tienen el mismo valor en `natAddGraph`. -/
def intRel (p q : ZFSet) : Prop :=
  ∃ a b c d : ZFSet,
    a ∈ omegaTA ∧
    b ∈ omegaTA ∧
    c ∈ omegaTA ∧
    d ∈ omegaTA ∧
    p = ZFSet.pair a b ∧
    q = ZFSet.pair c d ∧
    ∃ s : ZFSet,
      s ∈ omegaTA ∧
      ZFSet.pair (ZFSet.pair a d) s ∈ natAddGraph ∧
      ZFSet.pair (ZFSet.pair b c) s ∈ natAddGraph

/-- El puente B0 reduce la relación conjuntista al criterio aritmético
externo `A + D = B + C`. -/
theorem intRel_natEncode_iff (A B C D : Nat) :
    intRel
      (ZFSet.pair (natEncode A) (natEncode B))
      (ZFSet.pair (natEncode C) (natEncode D)) ↔
    A + D = B + C := by
  constructor
  · intro hRel
    rcases hRel with
      ⟨a, b, c, d, _ha, _hb, _hc, _hd,
        hp, hq, s, _hs, hAD, hBC⟩
    rcases ZFSet.pair_injective hp with ⟨rfl, rfl⟩
    rcases ZFSet.pair_injective hq with ⟨rfl, rfl⟩
    have hsAD : s = natEncode (A + D) :=
      natAddGraph_natEncode_value_iff.mp hAD
    have hsBC : s = natEncode (B + C) :=
      natAddGraph_natEncode_value_iff.mp hBC
    exact natEncode_injective (hsAD.symm.trans hsBC)
  · intro hEq
    refine ⟨natEncode A, natEncode B, natEncode C, natEncode D,
      natEncode_mem_omegaTA A, natEncode_mem_omegaTA B,
      natEncode_mem_omegaTA C, natEncode_mem_omegaTA D,
      rfl, rfl, natEncode (A + D), natEncode_mem_omegaTA (A + D),
      natAddGraph_natEncode A D, ?_⟩
    rw [hEq]
    exact natAddGraph_natEncode B C

/-- Reflexividad de `intRel` sobre el dominio de diferencias. -/
theorem intRel_refl {p : ZFSet}
    (hp : p ∈ intDomain) :
    intRel p p := by
  rcases mem_intDomain_iff.mp hp with ⟨a, b, ha, hb, rfl⟩
  rcases exists_natEncode_eq_of_mem ha with ⟨A, rfl⟩
  rcases exists_natEncode_eq_of_mem hb with ⟨B, rfl⟩
  apply (intRel_natEncode_iff A B A B).mpr
  omega

/-- Simetría de `intRel` sobre el dominio de diferencias. -/
theorem intRel_symm {p q : ZFSet}
    (hp : p ∈ intDomain)
    (hq : q ∈ intDomain)
    (hpq : intRel p q) :
    intRel q p := by
  rcases mem_intDomain_iff.mp hp with ⟨a, b, ha, hb, rfl⟩
  rcases mem_intDomain_iff.mp hq with ⟨c, d, hc, hd, rfl⟩
  rcases exists_natEncode_eq_of_mem ha with ⟨A, rfl⟩
  rcases exists_natEncode_eq_of_mem hb with ⟨B, rfl⟩
  rcases exists_natEncode_eq_of_mem hc with ⟨C, rfl⟩
  rcases exists_natEncode_eq_of_mem hd with ⟨D, rfl⟩
  have hEq : A + D = B + C :=
    (intRel_natEncode_iff A B C D).mp hpq
  apply (intRel_natEncode_iff C D A B).mpr
  omega

/-- Transitividad de `intRel` sobre el dominio de diferencias. -/
theorem intRel_trans {p q r : ZFSet}
    (hp : p ∈ intDomain)
    (hq : q ∈ intDomain)
    (hr : r ∈ intDomain)
    (hpq : intRel p q)
    (hqr : intRel q r) :
    intRel p r := by
  rcases mem_intDomain_iff.mp hp with ⟨a, b, ha, hb, rfl⟩
  rcases mem_intDomain_iff.mp hq with ⟨c, d, hc, hd, rfl⟩
  rcases mem_intDomain_iff.mp hr with ⟨e, f, he, hf, rfl⟩
  rcases exists_natEncode_eq_of_mem ha with ⟨A, rfl⟩
  rcases exists_natEncode_eq_of_mem hb with ⟨B, rfl⟩
  rcases exists_natEncode_eq_of_mem hc with ⟨C, rfl⟩
  rcases exists_natEncode_eq_of_mem hd with ⟨D, rfl⟩
  rcases exists_natEncode_eq_of_mem he with ⟨E, rfl⟩
  rcases exists_natEncode_eq_of_mem hf with ⟨F, rfl⟩
  have hEq₁ : A + D = B + C :=
    (intRel_natEncode_iff A B C D).mp hpq
  have hEq₂ : C + F = D + E :=
    (intRel_natEncode_iff C D E F).mp hqr
  apply (intRel_natEncode_iff A B E F).mpr
  omega

/-- TA-PRO-00036 — `intRel` es reflexiva, simétrica y transitiva sobre
`intDomain`. Las identidades de `Nat` se usan sólo después de extraer
localmente códigos mediante B0. -/
theorem TA_PRO_00036_intRel_equivalence :
    (∀ p : ZFSet,
      p ∈ intDomain → intRel p p) ∧
    (∀ p q : ZFSet,
      p ∈ intDomain →
      q ∈ intDomain →
      intRel p q →
      intRel q p) ∧
    (∀ p q r : ZFSet,
      p ∈ intDomain →
      q ∈ intDomain →
      r ∈ intDomain →
      intRel p q →
      intRel q r →
      intRel p r) := by
  exact ⟨fun _ hp => intRel_refl hp,
    fun _ _ hp hq hpq => intRel_symm hp hq hpq,
    fun _ _ _ hp hq hr hpq hqr => intRel_trans hp hq hr hpq hqr⟩

/-- TA-NOT-00009 — clase entera del representante `p`. -/
def intClass (p : ZFSet) : ZFSet :=
  ZFSet.sep (fun q => intRel p q) intDomain

/-- Caracterización de pertenencia a una clase entera. -/
theorem mem_intClass {p q : ZFSet} :
    q ∈ intClass p ↔
      q ∈ intDomain ∧ intRel p q := by
  exact ZFSet.mem_sep

/-- Toda clase entera es un subconjunto del dominio de diferencias. -/
theorem intClass_subset_intDomain (p : ZFSet) :
    intClass p ⊆ intDomain := by
  intro q hq
  exact (mem_intClass.mp hq).1

/-- Todo representante del dominio pertenece a su propia clase. -/
theorem intClass_self {p : ZFSet}
    (hp : p ∈ intDomain) :
    p ∈ intClass p := by
  exact mem_intClass.mpr
    ⟨hp, intRel_refl hp⟩

/-- TA-DEF-00040 — conjunto conjuntista de enteros: el conjunto de todas
las clases de equivalencia de representantes de `intDomain`. -/
def integersTA : ZFSet :=
  ZFSet.sep
    (fun C =>
      ∃ p : ZFSet,
        p ∈ intDomain ∧
        C = intClass p)
    (ZFSet.powerset intDomain)

/-- Caracterización de los miembros del cociente conjuntista entero. -/
theorem mem_integersTA_iff {C : ZFSet} :
    C ∈ integersTA ↔
      ∃ p : ZFSet,
        p ∈ intDomain ∧
        C = intClass p := by
  constructor
  · intro hC
    exact (ZFSet.mem_sep.mp hC).2
  · rintro ⟨p, hp, rfl⟩
    apply ZFSet.mem_sep.mpr
    exact ⟨ZFSet.mem_powerset.mpr (intClass_subset_intDomain p),
      p, hp, rfl⟩

/-- Cada representante del dominio determina una clase en `integersTA`. -/
theorem intClass_mem_integersTA {p : ZFSet}
    (hp : p ∈ intDomain) :
    intClass p ∈ integersTA := by
  exact mem_integersTA_iff.mpr ⟨p, hp, rfl⟩

/-- TA-PRO-00037 — el cociente entero contiene todas y sólo las clases
determinadas por representantes de `intDomain`. -/
theorem TA_PRO_00037_integer_quotient :
    (∀ p : ZFSet,
      p ∈ intDomain → intClass p ∈ integersTA) ∧
    (∀ C : ZFSet,
      C ∈ integersTA →
      ∃ p : ZFSet,
        p ∈ intDomain ∧ C = intClass p) := by
  constructor
  · intro p hp
    exact intClass_mem_integersTA hp
  · intro C hC
    exact mem_integersTA_iff.mp hC

/-- TA-PRO-00038 — dos representantes determinan la misma clase si y sólo
si están relacionados. -/
theorem TA_PRO_00038_intClass_eq_iff
    {p q : ZFSet}
    (hp : p ∈ intDomain)
    (hq : q ∈ intDomain) :
    intClass p = intClass q ↔ intRel p q := by
  constructor
  · intro hClasses
    have hpInP : p ∈ intClass p :=
      intClass_self hp
    have hpInQ : p ∈ intClass q := by
      rw [← hClasses]
      exact hpInP
    have hqp : intRel q p :=
      (mem_intClass.mp hpInQ).2
    exact intRel_symm hq hp hqp
  · intro hpq
    apply ZFSet.ext
    intro r
    constructor
    · intro hrP
      have hrDom : r ∈ intDomain :=
        (mem_intClass.mp hrP).1
      have hpr : intRel p r :=
        (mem_intClass.mp hrP).2
      have hqp : intRel q p :=
        intRel_symm hp hq hpq
      exact mem_intClass.mpr
        ⟨hrDom, intRel_trans hq hp hrDom hqp hpr⟩
    · intro hrQ
      have hrDom : r ∈ intDomain :=
        (mem_intClass.mp hrQ).1
      have hqr : intRel q r :=
        (mem_intClass.mp hrQ).2
      exact mem_intClass.mpr
        ⟨hrDom, intRel_trans hp hq hrDom hpq hqr⟩

/-- Criterio humano de igualdad de clases sobre códigos naturales. -/
theorem TA_PRO_00038_natEncode_class_eq_iff
    (A B C D : Nat) :
    intClass
      (ZFSet.pair (natEncode A) (natEncode B)) =
    intClass
      (ZFSet.pair (natEncode C) (natEncode D)) ↔
    A + D = B + C := by
  have hp :
      ZFSet.pair (natEncode A) (natEncode B) ∈ intDomain :=
    mem_cartesianProductFoundational.mpr
      ⟨natEncode_mem_omegaTA A, natEncode_mem_omegaTA B⟩
  have hq :
      ZFSet.pair (natEncode C) (natEncode D) ∈ intDomain :=
    mem_cartesianProductFoundational.mpr
      ⟨natEncode_mem_omegaTA C, natEncode_mem_omegaTA D⟩
  exact (TA_PRO_00038_intClass_eq_iff hp hq).trans
    (intRel_natEncode_iff A B C D)

end TratadoAnalisis.Integers.Construction
