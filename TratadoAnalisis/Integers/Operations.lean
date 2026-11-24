import TratadoAnalisis.Integers.Construction

namespace TratadoAnalisis.Integers.Operations

open TratadoAnalisis.Naturals.Foundational
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Naturals.ArithmeticBridge
open TratadoAnalisis.Integers.Construction

/-! # Operaciones relacionales sobre el cociente entero

La suma y el opuesto se construyen como grafos conjuntistas. Los
representantes y sus códigos naturales se eliminan localmente; no se define
ninguna función global que los seleccione.
-/

/-- Caracterización general del producto cartesiano fundacional. -/
theorem mem_cartesianProductFoundational_iff
    {A B p : ZFSet} :
    p ∈ cartesianProductFoundational A B ↔
      ∃ a : ZFSet, a ∈ A ∧
        ∃ b : ZFSet, b ∈ B ∧ p = ZFSet.pair a b := by
  constructor
  · intro hp
    rw [cartesianProductFoundational] at hp
    exact (ZFSet.mem_sep.mp hp).2
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact mem_cartesianProductFoundational.mpr ⟨ha, hb⟩

/-! ## Suma de representantes -/

/-- TA-DEF-00041 — relación de cálculo de la suma de dos diferencias
formales. Las dos sumas de naturales se expresan sólo mediante
`natAddGraph`. -/
def intRepAdd (p q r : ZFSet) : Prop :=
  ∃ a b c d u v : ZFSet,
    a ∈ omegaTA ∧
    b ∈ omegaTA ∧
    c ∈ omegaTA ∧
    d ∈ omegaTA ∧
    u ∈ omegaTA ∧
    v ∈ omegaTA ∧
    p = ZFSet.pair a b ∧
    q = ZFSet.pair c d ∧
    r = ZFSet.pair u v ∧
    ZFSet.pair (ZFSet.pair a c) u ∈ natAddGraph ∧
    ZFSet.pair (ZFSet.pair b d) v ∈ natAddGraph

/-- La funcionalidad de `natAddGraph` proporciona un único representante
suma para cada par de representantes del dominio. -/
theorem intRepAdd_exists_unique
    {p q : ZFSet}
    (hp : p ∈ intDomain)
    (hq : q ∈ intDomain) :
    ∃! r : ZFSet, r ∈ intDomain ∧ intRepAdd p q r := by
  rcases mem_intDomain_iff.mp hp with ⟨a, b, ha, hb, rfl⟩
  rcases mem_intDomain_iff.mp hq with ⟨c, d, hc, hd, rfl⟩
  have hac : ZFSet.pair a c ∈
      cartesianProductFoundational omegaTA omegaTA :=
    mem_cartesianProductFoundational.mpr ⟨ha, hc⟩
  have hbd : ZFSet.pair b d ∈
      cartesianProductFoundational omegaTA omegaTA :=
    mem_cartesianProductFoundational.mpr ⟨hb, hd⟩
  rcases natAddGraph_isFunc.2 (ZFSet.pair a c) hac with
    ⟨u, huData, huUnique⟩
  rcases natAddGraph_isFunc.2 (ZFSet.pair b d) hbd with
    ⟨v, hvData, hvUnique⟩
  refine ⟨ZFSet.pair u v, ?_, ?_⟩
  · exact ⟨mem_intDomain_iff.mpr ⟨u, v, huData.1, hvData.1, rfl⟩,
      a, b, c, d, u, v, ha, hb, hc, hd, huData.1, hvData.1,
      rfl, rfl, rfl, huData.2, hvData.2⟩
  · intro r hr
    rcases hr.2 with
      ⟨a', b', c', d', u', v', ha', hb', hc', hd', hu', hv',
        hp', hq', hr', hacu', hbdv'⟩
    rcases ZFSet.pair_injective hp' with ⟨rfl, rfl⟩
    rcases ZFSet.pair_injective hq' with ⟨rfl, rfl⟩
    have huu : u' = u := huUnique u' ⟨hu', hacu'⟩
    have hvv : v' = v := hvUnique v' ⟨hv', hbdv'⟩
    rw [huu, hvv] at hr'
    exact hr'

/-- Fórmula externa de la suma relacional de representantes codificados. -/
theorem intRepAdd_natEncode_iff
    (A B C D : Nat) (r : ZFSet) :
    intRepAdd
      (ZFSet.pair (natEncode A) (natEncode B))
      (ZFSet.pair (natEncode C) (natEncode D))
      r ↔
    r = ZFSet.pair (natEncode (A + C)) (natEncode (B + D)) := by
  constructor
  · rintro ⟨a, b, c, d, u, v, _ha, _hb, _hc, _hd, _hu, _hv,
      hp, hq, hr, hacu, hbdv⟩
    rcases ZFSet.pair_injective hp with ⟨rfl, rfl⟩
    rcases ZFSet.pair_injective hq with ⟨rfl, rfl⟩
    have huEq : u = natEncode (A + C) :=
      natAddGraph_natEncode_value_iff.mp hacu
    have hvEq : v = natEncode (B + D) :=
      natAddGraph_natEncode_value_iff.mp hbdv
    simpa [huEq, hvEq] using hr
  · intro hr
    refine ⟨natEncode A, natEncode B, natEncode C, natEncode D,
      natEncode (A + C), natEncode (B + D),
      natEncode_mem_omegaTA A, natEncode_mem_omegaTA B,
      natEncode_mem_omegaTA C, natEncode_mem_omegaTA D,
      natEncode_mem_omegaTA (A + C), natEncode_mem_omegaTA (B + D),
      rfl, rfl, hr, natAddGraph_natEncode A C,
      natAddGraph_natEncode B D⟩

/-- TA-PRO-00039 — la suma de representantes respeta `intRel` en ambas
entradas. -/
theorem TA_PRO_00039_intRepAdd_well_defined
    {p p' q q' r r' : ZFSet}
    (hp : p ∈ intDomain)
    (hp' : p' ∈ intDomain)
    (hq : q ∈ intDomain)
    (hq' : q' ∈ intDomain)
    (hpp' : intRel p p')
    (hqq' : intRel q q')
    (hAdd : intRepAdd p q r)
    (hAdd' : intRepAdd p' q' r') :
    intRel r r' := by
  rcases mem_intDomain_iff.mp hp with ⟨a, b, ha, hb, rfl⟩
  rcases mem_intDomain_iff.mp hp' with ⟨a', b', ha', hb', rfl⟩
  rcases mem_intDomain_iff.mp hq with ⟨c, d, hc, hd, rfl⟩
  rcases mem_intDomain_iff.mp hq' with ⟨c', d', hc', hd', rfl⟩
  rcases exists_natEncode_eq_of_mem ha with ⟨A, rfl⟩
  rcases exists_natEncode_eq_of_mem hb with ⟨B, rfl⟩
  rcases exists_natEncode_eq_of_mem ha' with ⟨A', rfl⟩
  rcases exists_natEncode_eq_of_mem hb' with ⟨B', rfl⟩
  rcases exists_natEncode_eq_of_mem hc with ⟨C, rfl⟩
  rcases exists_natEncode_eq_of_mem hd with ⟨D, rfl⟩
  rcases exists_natEncode_eq_of_mem hc' with ⟨C', rfl⟩
  rcases exists_natEncode_eq_of_mem hd' with ⟨D', rfl⟩
  have hpEq : A + B' = B + A' :=
    (intRel_natEncode_iff A B A' B').mp hpp'
  have hqEq : C + D' = D + C' :=
    (intRel_natEncode_iff C D C' D').mp hqq'
  have hrEq := (intRepAdd_natEncode_iff A B C D r).mp hAdd
  have hrEq' := (intRepAdd_natEncode_iff A' B' C' D' r').mp hAdd'
  rw [hrEq, hrEq']
  apply (intRel_natEncode_iff (A + C) (B + D) (A' + C') (B' + D')).mpr
  omega

/-! ## Grafo de suma sobre las clases -/

/-- Valor relacional de la suma de dos clases enteras. -/
def IntAddValue (x y z : ZFSet) : Prop :=
  ∃ p q r : ZFSet,
    p ∈ intDomain ∧
    q ∈ intDomain ∧
    r ∈ intDomain ∧
    x = intClass p ∧
    y = intClass q ∧
    z = intClass r ∧
    intRepAdd p q r

/-- TA-DEF-00042 — grafo conjuntista de la suma de enteros. -/
def intAddGraph : ZFSet :=
  ZFSet.sep
    (fun t =>
      ∃ x y z : ZFSet,
        x ∈ integersTA ∧
        y ∈ integersTA ∧
        z ∈ integersTA ∧
        t = ZFSet.pair (ZFSet.pair x y) z ∧
        IntAddValue x y z)
    (pairAmbient
      (cartesianProductFoundational integersTA integersTA)
      integersTA)

/-- Caracterización puntual del grafo de suma. -/
theorem mem_intAddGraph {x y z : ZFSet} :
    ZFSet.pair (ZFSet.pair x y) z ∈ intAddGraph ↔
      x ∈ integersTA ∧ y ∈ integersTA ∧ z ∈ integersTA ∧
        IntAddValue x y z := by
  constructor
  · intro h
    rcases (ZFSet.mem_sep.mp h).2 with
      ⟨x', y', z', hx', hy', hz', hEq, hValue⟩
    rcases ZFSet.pair_injective hEq with ⟨hxy, hz⟩
    rcases ZFSet.pair_injective hxy with ⟨hx, hy⟩
    subst x'
    subst y'
    subst z'
    exact ⟨hx', hy', hz', hValue⟩
  · rintro ⟨hx, hy, hz, hValue⟩
    apply ZFSet.mem_sep.mpr
    exact ⟨pair_mem_pairAmbient
        (mem_cartesianProductFoundational.mpr ⟨hx, hy⟩) hz,
      x, y, z, hx, hy, hz, rfl, hValue⟩

/-- El grafo de suma es una función total sobre pares de enteros. -/
theorem intAddGraph_isFunc :
    IsFuncFoundational
      (cartesianProductFoundational integersTA integersTA)
      integersTA
      intAddGraph := by
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
    rcases mem_integersTA_iff.mp hx with ⟨p, hp, hxClass⟩
    rcases mem_integersTA_iff.mp hy with ⟨q, hq, hyClass⟩
    rcases intRepAdd_exists_unique hp hq with ⟨r, hr, _hrUnique⟩
    refine ⟨intClass r, ?_, ?_⟩
    · exact ⟨intClass_mem_integersTA hr.1,
        mem_intAddGraph.mpr ⟨hx, hy, intClass_mem_integersTA hr.1,
          p, q, r, hp, hq, hr.1, hxClass, hyClass, rfl, hr.2⟩⟩
    · intro z' hz'
      rcases (mem_intAddGraph.mp hz'.2).2.2.2 with
        ⟨p', q', r', hp', hq', hr', hxClass', hyClass', hzClass', hAdd'⟩
      have hpp' : intRel p p' :=
        (TA_PRO_00038_intClass_eq_iff hp hp').mp
          (hxClass.symm.trans hxClass')
      have hqq' : intRel q q' :=
        (TA_PRO_00038_intClass_eq_iff hq hq').mp
          (hyClass.symm.trans hyClass')
      have hrr' : intRel r r' :=
        TA_PRO_00039_intRepAdd_well_defined
          hp hp' hq hq' hpp' hqq' hr.2 hAdd'
      have hClasses : intClass r = intClass r' :=
        (TA_PRO_00038_intClass_eq_iff hr.1 hr').mpr hrr'
      exact hzClass'.trans hClasses.symm

/-- Fórmula directa de la suma sobre clases de representantes codificados. -/
theorem intAddGraph_natEncode_classes (A B C D : Nat) :
    ZFSet.pair
      (ZFSet.pair
        (intClass (ZFSet.pair (natEncode A) (natEncode B)))
        (intClass (ZFSet.pair (natEncode C) (natEncode D))))
      (intClass
        (ZFSet.pair (natEncode (A + C)) (natEncode (B + D)))) ∈
      intAddGraph := by
  have hp : ZFSet.pair (natEncode A) (natEncode B) ∈ intDomain :=
    mem_intDomain_iff.mpr
      ⟨natEncode A, natEncode B, natEncode_mem_omegaTA A,
        natEncode_mem_omegaTA B, rfl⟩
  have hq : ZFSet.pair (natEncode C) (natEncode D) ∈ intDomain :=
    mem_intDomain_iff.mpr
      ⟨natEncode C, natEncode D, natEncode_mem_omegaTA C,
        natEncode_mem_omegaTA D, rfl⟩
  have hr : ZFSet.pair (natEncode (A + C)) (natEncode (B + D)) ∈ intDomain :=
    mem_intDomain_iff.mpr
      ⟨natEncode (A + C), natEncode (B + D),
        natEncode_mem_omegaTA (A + C), natEncode_mem_omegaTA (B + D), rfl⟩
  apply mem_intAddGraph.mpr
  exact ⟨intClass_mem_integersTA hp, intClass_mem_integersTA hq,
    intClass_mem_integersTA hr,
    ZFSet.pair (natEncode A) (natEncode B),
    ZFSet.pair (natEncode C) (natEncode D),
    ZFSet.pair (natEncode (A + C)) (natEncode (B + D)),
    hp, hq, hr, rfl, rfl, rfl,
    (intRepAdd_natEncode_iff A B C D _).mpr rfl⟩

/-- Un valor del grafo de suma sobre clases codificadas es exactamente la
clase del representante suma. -/
theorem intAddGraph_natEncode_classes_value_iff
    {A B C D : Nat} {z : ZFSet} :
    ZFSet.pair
      (ZFSet.pair
        (intClass (ZFSet.pair (natEncode A) (natEncode B)))
        (intClass (ZFSet.pair (natEncode C) (natEncode D)))) z ∈ intAddGraph ↔
    z = intClass
      (ZFSet.pair (natEncode (A + C)) (natEncode (B + D))) := by
  constructor
  · intro hz
    have hInput :
        ZFSet.pair
          (intClass (ZFSet.pair (natEncode A) (natEncode B)))
          (intClass (ZFSet.pair (natEncode C) (natEncode D))) ∈
        cartesianProductFoundational integersTA integersTA := by
      apply mem_cartesianProductFoundational.mpr
      exact ⟨intClass_mem_integersTA
          (mem_intDomain_iff.mpr ⟨natEncode A, natEncode B,
            natEncode_mem_omegaTA A, natEncode_mem_omegaTA B, rfl⟩),
        intClass_mem_integersTA
          (mem_intDomain_iff.mpr ⟨natEncode C, natEncode D,
            natEncode_mem_omegaTA C, natEncode_mem_omegaTA D, rfl⟩)⟩
    rcases intAddGraph_isFunc.2 _ hInput with ⟨w, hw, hUnique⟩
    have hzMem : z ∈ integersTA :=
      funcFoundational_value_mem intAddGraph_isFunc hz
    have hExpected := intAddGraph_natEncode_classes A B C D
    have hExpectedMem :
        intClass (ZFSet.pair (natEncode (A + C)) (natEncode (B + D))) ∈
          integersTA :=
      funcFoundational_value_mem intAddGraph_isFunc hExpected
    exact (hUnique z ⟨hzMem, hz⟩).trans
      (hUnique _ ⟨hExpectedMem, hExpected⟩).symm
  · rintro rfl
    exact intAddGraph_natEncode_classes A B C D

/-! ## Cero entero -/

/-- TA-NOT-00010 — clase de la diferencia formal `(0,0)`. -/
def intZero : ZFSet :=
  intClass (ZFSet.pair (natEncode 0) (natEncode 0))

/-- El cero entero es un miembro del cociente conjuntista. -/
theorem intZero_mem_integersTA : intZero ∈ integersTA := by
  apply intClass_mem_integersTA
  exact mem_intDomain_iff.mpr
    ⟨natEncode 0, natEncode 0, natEncode_mem_omegaTA 0,
      natEncode_mem_omegaTA 0, rfl⟩

/-! ## Opuesto -/

/-- Relación de valor del opuesto obtenida intercambiando las componentes
de un representante. -/
def IntNegValue (x y : ZFSet) : Prop :=
  ∃ a b : ZFSet,
    a ∈ omegaTA ∧
    b ∈ omegaTA ∧
    x = intClass (ZFSet.pair a b) ∧
    y = intClass (ZFSet.pair b a)

/-- Intercambiar simultáneamente las componentes conserva `intRel`. -/
theorem intRel_swap
    {a b c d : ZFSet}
    (ha : a ∈ omegaTA)
    (hb : b ∈ omegaTA)
    (hc : c ∈ omegaTA)
    (hd : d ∈ omegaTA)
    (hRel : intRel (ZFSet.pair a b) (ZFSet.pair c d)) :
    intRel (ZFSet.pair b a) (ZFSet.pair d c) := by
  rcases exists_natEncode_eq_of_mem ha with ⟨A, rfl⟩
  rcases exists_natEncode_eq_of_mem hb with ⟨B, rfl⟩
  rcases exists_natEncode_eq_of_mem hc with ⟨C, rfl⟩
  rcases exists_natEncode_eq_of_mem hd with ⟨D, rfl⟩
  have hEq : A + D = B + C :=
    (intRel_natEncode_iff A B C D).mp hRel
  apply (intRel_natEncode_iff B A D C).mpr
  omega

/-- TA-DEF-00043 / TA-PRO-00040 — el intercambio de componentes induce
un opuesto independiente del representante de la clase. -/
theorem TA_PRO_00040_intNeg_well_defined
    {a b c d : ZFSet}
    (ha : a ∈ omegaTA)
    (hb : b ∈ omegaTA)
    (hc : c ∈ omegaTA)
    (hd : d ∈ omegaTA)
    (hClasses :
      intClass (ZFSet.pair a b) = intClass (ZFSet.pair c d)) :
    intClass (ZFSet.pair b a) = intClass (ZFSet.pair d c) := by
  have hab : ZFSet.pair a b ∈ intDomain :=
    mem_intDomain_iff.mpr ⟨a, b, ha, hb, rfl⟩
  have hcd : ZFSet.pair c d ∈ intDomain :=
    mem_intDomain_iff.mpr ⟨c, d, hc, hd, rfl⟩
  have hba : ZFSet.pair b a ∈ intDomain :=
    mem_intDomain_iff.mpr ⟨b, a, hb, ha, rfl⟩
  have hdc : ZFSet.pair d c ∈ intDomain :=
    mem_intDomain_iff.mpr ⟨d, c, hd, hc, rfl⟩
  have hRel : intRel (ZFSet.pair a b) (ZFSet.pair c d) :=
    (TA_PRO_00038_intClass_eq_iff hab hcd).mp hClasses
  exact (TA_PRO_00038_intClass_eq_iff hba hdc).mpr
    (intRel_swap ha hb hc hd hRel)

/-- Grafo conjuntista del opuesto entero. -/
def intNegGraph : ZFSet :=
  ZFSet.sep
    (fun t =>
      ∃ x y : ZFSet,
        x ∈ integersTA ∧
        y ∈ integersTA ∧
        t = ZFSet.pair x y ∧
        IntNegValue x y)
    (pairAmbient integersTA integersTA)

/-- Caracterización puntual del grafo del opuesto. -/
theorem mem_intNegGraph {x y : ZFSet} :
    ZFSet.pair x y ∈ intNegGraph ↔
      x ∈ integersTA ∧ y ∈ integersTA ∧ IntNegValue x y := by
  constructor
  · intro h
    rcases (ZFSet.mem_sep.mp h).2 with
      ⟨x', y', hx', hy', hEq, hValue⟩
    rcases ZFSet.pair_injective hEq with ⟨hx, hy⟩
    subst x'
    subst y'
    exact ⟨hx', hy', hValue⟩
  · rintro ⟨hx, hy, hValue⟩
    apply ZFSet.mem_sep.mpr
    exact ⟨pair_mem_pairAmbient hx hy,
      x, y, hx, hy, rfl, hValue⟩

/-- El grafo del opuesto es una función total en `integersTA`. -/
theorem intNegGraph_isFunc :
    IsFuncFoundational integersTA integersTA intNegGraph := by
  constructor
  · intro t ht
    rcases (ZFSet.mem_sep.mp ht).2 with
      ⟨x, y, hx, hy, rfl, _hValue⟩
    exact ⟨x, hx, y, hy, rfl⟩
  · intro x hx
    rcases mem_integersTA_iff.mp hx with ⟨p, hp, hxClass⟩
    rcases mem_intDomain_iff.mp hp with ⟨a, b, ha, hb, hpPair⟩
    have hba : ZFSet.pair b a ∈ intDomain :=
      mem_intDomain_iff.mpr ⟨b, a, hb, ha, rfl⟩
    refine ⟨intClass (ZFSet.pair b a), ?_, ?_⟩
    · exact ⟨intClass_mem_integersTA hba,
        mem_intNegGraph.mpr ⟨hx, intClass_mem_integersTA hba,
          a, b, ha, hb, hxClass.trans (congrArg intClass hpPair), rfl⟩⟩
    · intro y hy
      rcases (mem_intNegGraph.mp hy.2).2.2 with
        ⟨c, d, hc, hd, hxClass', hyClass'⟩
      have hInputClasses :
          intClass (ZFSet.pair a b) = intClass (ZFSet.pair c d) := by
        exact (congrArg intClass hpPair).symm.trans
          (hxClass.symm.trans hxClass')
      have hOutputClasses :
          intClass (ZFSet.pair b a) = intClass (ZFSet.pair d c) :=
        TA_PRO_00040_intNeg_well_defined ha hb hc hd hInputClasses
      exact hyClass'.trans hOutputClasses.symm

/-- Fórmula directa del opuesto sobre una clase codificada. -/
theorem intNegGraph_natEncode_class (A B : Nat) :
    ZFSet.pair
      (intClass (ZFSet.pair (natEncode A) (natEncode B)))
      (intClass (ZFSet.pair (natEncode B) (natEncode A))) ∈
      intNegGraph := by
  have hab : ZFSet.pair (natEncode A) (natEncode B) ∈ intDomain :=
    mem_intDomain_iff.mpr
      ⟨natEncode A, natEncode B, natEncode_mem_omegaTA A,
        natEncode_mem_omegaTA B, rfl⟩
  have hba : ZFSet.pair (natEncode B) (natEncode A) ∈ intDomain :=
    mem_intDomain_iff.mpr
      ⟨natEncode B, natEncode A, natEncode_mem_omegaTA B,
        natEncode_mem_omegaTA A, rfl⟩
  exact mem_intNegGraph.mpr
    ⟨intClass_mem_integersTA hab, intClass_mem_integersTA hba,
      natEncode A, natEncode B, natEncode_mem_omegaTA A,
      natEncode_mem_omegaTA B, rfl, rfl⟩

/-- Un valor del grafo del opuesto sobre una clase codificada es exactamente
la clase obtenida intercambiando componentes. -/
theorem intNegGraph_natEncode_class_value_iff
    {A B : Nat} {y : ZFSet} :
    ZFSet.pair
      (intClass (ZFSet.pair (natEncode A) (natEncode B))) y ∈ intNegGraph ↔
    y = intClass (ZFSet.pair (natEncode B) (natEncode A)) := by
  constructor
  · intro hy
    have hx : intClass (ZFSet.pair (natEncode A) (natEncode B)) ∈
        integersTA :=
      intClass_mem_integersTA
        (mem_intDomain_iff.mpr ⟨natEncode A, natEncode B,
          natEncode_mem_omegaTA A, natEncode_mem_omegaTA B, rfl⟩)
    rcases intNegGraph_isFunc.2 _ hx with ⟨w, hw, hUnique⟩
    have hyMem : y ∈ integersTA :=
      funcFoundational_value_mem intNegGraph_isFunc hy
    have hExpected := intNegGraph_natEncode_class A B
    have hExpectedMem :
        intClass (ZFSet.pair (natEncode B) (natEncode A)) ∈ integersTA :=
      funcFoundational_value_mem intNegGraph_isFunc hExpected
    exact (hUnique y ⟨hyMem, hy⟩).trans
      (hUnique _ ⟨hExpectedMem, hExpected⟩).symm
  · rintro rfl
    exact intNegGraph_natEncode_class A B

end TratadoAnalisis.Integers.Operations
