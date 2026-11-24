import TratadoAnalisis.Integers.Operations

namespace TratadoAnalisis.Integers.Multiplication

open TratadoAnalisis.Naturals.Foundational
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Naturals.ArithmeticBridge
open TratadoAnalisis.Integers.Construction
open TratadoAnalisis.Integers.Operations

/-! # Multiplicación relacional sobre el cociente entero

El producto se construye mediante los grafos fundacionales de suma y
multiplicación natural. No se seleccionan globalmente representantes ni
códigos naturales.
-/

/-! ## Producto de representantes -/

/-- TA-DEF-00045 — relación de cálculo
`(a,b)(c,d) = (ac+bd, ad+bc)` para diferencias formales. -/
def intRepMul (p q r : ZFSet) : Prop :=
  ∃ a b c d ac bd ad bc u v : ZFSet,
    a ∈ omegaTA ∧
    b ∈ omegaTA ∧
    c ∈ omegaTA ∧
    d ∈ omegaTA ∧
    ac ∈ omegaTA ∧
    bd ∈ omegaTA ∧
    ad ∈ omegaTA ∧
    bc ∈ omegaTA ∧
    u ∈ omegaTA ∧
    v ∈ omegaTA ∧
    p = ZFSet.pair a b ∧
    q = ZFSet.pair c d ∧
    r = ZFSet.pair u v ∧
    ZFSet.pair (ZFSet.pair a c) ac ∈ natMulGraph ∧
    ZFSet.pair (ZFSet.pair b d) bd ∈ natMulGraph ∧
    ZFSet.pair (ZFSet.pair a d) ad ∈ natMulGraph ∧
    ZFSet.pair (ZFSet.pair b c) bc ∈ natMulGraph ∧
    ZFSet.pair (ZFSet.pair ac bd) u ∈ natAddGraph ∧
    ZFSet.pair (ZFSet.pair ad bc) v ∈ natAddGraph

/-- Cada par de representantes del dominio posee un único representante
producto. La unicidad procede sucesivamente de la funcionalidad de los
cuatro productos y las dos sumas naturales. -/
theorem intRepMul_exists_unique
    {p q : ZFSet}
    (hp : p ∈ intDomain)
    (hq : q ∈ intDomain) :
    ∃! r : ZFSet,
      r ∈ intDomain ∧ intRepMul p q r := by
  rcases mem_intDomain_iff.mp hp with ⟨a, b, ha, hb, rfl⟩
  rcases mem_intDomain_iff.mp hq with ⟨c, d, hc, hd, rfl⟩
  have hacDom := mem_cartesianProductFoundational.mpr ⟨ha, hc⟩
  have hbdDom := mem_cartesianProductFoundational.mpr ⟨hb, hd⟩
  have hadDom := mem_cartesianProductFoundational.mpr ⟨ha, hd⟩
  have hbcDom := mem_cartesianProductFoundational.mpr ⟨hb, hc⟩
  rcases natMulGraph_isFunc.2 (ZFSet.pair a c) hacDom with
    ⟨ac, hacData, hacUnique⟩
  rcases natMulGraph_isFunc.2 (ZFSet.pair b d) hbdDom with
    ⟨bd, hbdData, hbdUnique⟩
  rcases natMulGraph_isFunc.2 (ZFSet.pair a d) hadDom with
    ⟨ad, hadData, hadUnique⟩
  rcases natMulGraph_isFunc.2 (ZFSet.pair b c) hbcDom with
    ⟨bc, hbcData, hbcUnique⟩
  have huDom := mem_cartesianProductFoundational.mpr
    ⟨hacData.1, hbdData.1⟩
  have hvDom := mem_cartesianProductFoundational.mpr
    ⟨hadData.1, hbcData.1⟩
  rcases natAddGraph_isFunc.2 (ZFSet.pair ac bd) huDom with
    ⟨u, huData, huUnique⟩
  rcases natAddGraph_isFunc.2 (ZFSet.pair ad bc) hvDom with
    ⟨v, hvData, hvUnique⟩
  refine ⟨ZFSet.pair u v, ?_, ?_⟩
  · exact ⟨mem_intDomain_iff.mpr
        ⟨u, v, huData.1, hvData.1, rfl⟩,
      a, b, c, d, ac, bd, ad, bc, u, v,
      ha, hb, hc, hd, hacData.1, hbdData.1, hadData.1, hbcData.1,
      huData.1, hvData.1, rfl, rfl, rfl,
      hacData.2, hbdData.2, hadData.2, hbcData.2,
      huData.2, hvData.2⟩
  · intro r hr
    rcases hr.2 with
      ⟨a', b', c', d', ac', bd', ad', bc', u', v',
        ha', hb', hc', hd', hac', hbd', had', hbc', hu', hv',
        hp', hq', hr', hAC', hBD', hAD', hBC', hU', hV'⟩
    rcases ZFSet.pair_injective hp' with ⟨rfl, rfl⟩
    rcases ZFSet.pair_injective hq' with ⟨rfl, rfl⟩
    have hEqAC : ac' = ac := hacUnique ac' ⟨hac', hAC'⟩
    have hEqBD : bd' = bd := hbdUnique bd' ⟨hbd', hBD'⟩
    have hEqAD : ad' = ad := hadUnique ad' ⟨had', hAD'⟩
    have hEqBC : bc' = bc := hbcUnique bc' ⟨hbc', hBC'⟩
    subst ac'
    subst bd'
    subst ad'
    subst bc'
    have hEqU : u' = u := huUnique u' ⟨hu', hU'⟩
    have hEqV : v' = v := hvUnique v' ⟨hv', hV'⟩
    rw [hEqU, hEqV] at hr'
    exact hr'

/-! ## Puente con los naturales externos -/

/-- Fórmula exacta del producto de representantes codificados. -/
theorem intRepMul_natEncode_iff
    (A B C D : Nat)
    (r : ZFSet) :
    intRepMul
      (ZFSet.pair (natEncode A) (natEncode B))
      (ZFSet.pair (natEncode C) (natEncode D))
      r ↔
    r =
      ZFSet.pair
        (natEncode (A * C + B * D))
        (natEncode (A * D + B * C)) := by
  constructor
  · rintro ⟨a, b, c, d, ac, bd, ad, bc, u, v,
      _ha, _hb, _hc, _hd, _hac, _hbd, _had, _hbc, _hu, _hv,
      hp, hq, hr, hAC, hBD, hAD, hBC, hU, hV⟩
    rcases ZFSet.pair_injective hp with ⟨rfl, rfl⟩
    rcases ZFSet.pair_injective hq with ⟨rfl, rfl⟩
    have hEqAC : ac = natEncode (A * C) :=
      natMulGraph_natEncode_value_iff.mp hAC
    have hEqBD : bd = natEncode (B * D) :=
      natMulGraph_natEncode_value_iff.mp hBD
    have hEqAD : ad = natEncode (A * D) :=
      natMulGraph_natEncode_value_iff.mp hAD
    have hEqBC : bc = natEncode (B * C) :=
      natMulGraph_natEncode_value_iff.mp hBC
    subst ac
    subst bd
    subst ad
    subst bc
    have hEqU : u = natEncode (A * C + B * D) :=
      natAddGraph_natEncode_value_iff.mp hU
    have hEqV : v = natEncode (A * D + B * C) :=
      natAddGraph_natEncode_value_iff.mp hV
    simpa [hEqU, hEqV] using hr
  · intro hr
    refine ⟨natEncode A, natEncode B, natEncode C, natEncode D,
      natEncode (A * C), natEncode (B * D),
      natEncode (A * D), natEncode (B * C),
      natEncode (A * C + B * D), natEncode (A * D + B * C),
      natEncode_mem_omegaTA A, natEncode_mem_omegaTA B,
      natEncode_mem_omegaTA C, natEncode_mem_omegaTA D,
      natEncode_mem_omegaTA (A * C), natEncode_mem_omegaTA (B * D),
      natEncode_mem_omegaTA (A * D), natEncode_mem_omegaTA (B * C),
      natEncode_mem_omegaTA (A * C + B * D),
      natEncode_mem_omegaTA (A * D + B * C),
      rfl, rfl, hr,
      natMulGraph_natEncode A C, natMulGraph_natEncode B D,
      natMulGraph_natEncode A D, natMulGraph_natEncode B C,
      natAddGraph_natEncode (A * C) (B * D),
      natAddGraph_natEncode (A * D) (B * C)⟩

/-! ## Compatibilidad algebraica por factores -/

/-- Compatibilidad sobre códigos al cambiar únicamente el primer factor. -/
theorem intRepMul_congr_left_nat
    (A B A' B' C D : Nat)
    (hEq : A + B' = B + A') :
    intRel
      (ZFSet.pair
        (natEncode (A * C + B * D))
        (natEncode (A * D + B * C)))
      (ZFSet.pair
        (natEncode (A' * C + B' * D))
        (natEncode (A' * D + B' * C))) := by
  apply (intRel_natEncode_iff
    (A * C + B * D) (A * D + B * C)
    (A' * C + B' * D) (A' * D + B' * C)).mpr
  have hC₀ := congrArg (fun n : Nat => C * n) hEq
  have hD₀ := congrArg (fun n : Nat => D * n) hEq
  have hC : A * C + B' * C = B * C + A' * C := by
    simpa [Nat.mul_add, Nat.mul_comm] using hC₀
  have hD : A * D + B' * D = B * D + A' * D := by
    simpa [Nat.mul_add, Nat.mul_comm] using hD₀
  omega

/-- Compatibilidad sobre códigos al cambiar únicamente el segundo factor. -/
theorem intRepMul_congr_right_nat
    (A B C D C' D' : Nat)
    (hEq : C + D' = D + C') :
    intRel
      (ZFSet.pair
        (natEncode (A * C + B * D))
        (natEncode (A * D + B * C)))
      (ZFSet.pair
        (natEncode (A * C' + B * D'))
        (natEncode (A * D' + B * C'))) := by
  apply (intRel_natEncode_iff
    (A * C + B * D) (A * D + B * C)
    (A * C' + B * D') (A * D' + B * C')).mpr
  have hA₀ := congrArg (fun n : Nat => A * n) hEq
  have hB₀ := congrArg (fun n : Nat => B * n) hEq
  have hA : A * C + A * D' = A * D + A * C' := by
    simpa [Nat.mul_add] using hA₀
  have hB : B * C + B * D' = B * D + B * C' := by
    simpa [Nat.mul_add] using hB₀
  omega

/-- TA-PRO-00043 — el producto de representantes respeta `intRel` en
ambos factores, por dos cambios separados y transitividad. -/
theorem TA_PRO_00043_intRepMul_well_defined
    {p p' q q' r r' : ZFSet}
    (hp : p ∈ intDomain)
    (hp' : p' ∈ intDomain)
    (hq : q ∈ intDomain)
    (hq' : q' ∈ intDomain)
    (hpp' : intRel p p')
    (hqq' : intRel q q')
    (hMul : intRepMul p q r)
    (hMul' : intRepMul p' q' r') :
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
  have hrEq := (intRepMul_natEncode_iff A B C D r).mp hMul
  have hrEq' := (intRepMul_natEncode_iff A' B' C' D' r').mp hMul'
  let r₁ := ZFSet.pair
    (natEncode (A' * C + B' * D))
    (natEncode (A' * D + B' * C))
  have hrDom :
      ZFSet.pair
        (natEncode (A * C + B * D))
        (natEncode (A * D + B * C)) ∈ intDomain :=
    mem_intDomain_iff.mpr
      ⟨_, _, natEncode_mem_omegaTA _, natEncode_mem_omegaTA _, rfl⟩
  have hr₁Dom : r₁ ∈ intDomain := by
    exact mem_intDomain_iff.mpr
      ⟨_, _, natEncode_mem_omegaTA _, natEncode_mem_omegaTA _, rfl⟩
  have hr'Dom :
      ZFSet.pair
        (natEncode (A' * C' + B' * D'))
        (natEncode (A' * D' + B' * C')) ∈ intDomain :=
    mem_intDomain_iff.mpr
      ⟨_, _, natEncode_mem_omegaTA _, natEncode_mem_omegaTA _, rfl⟩
  have hLeft :
      intRel
        (ZFSet.pair
          (natEncode (A * C + B * D))
          (natEncode (A * D + B * C))) r₁ := by
    exact intRepMul_congr_left_nat A B A' B' C D hpEq
  have hRight :
      intRel r₁
        (ZFSet.pair
          (natEncode (A' * C' + B' * D'))
          (natEncode (A' * D' + B' * C'))) := by
    exact intRepMul_congr_right_nat A' B' C D C' D' hqEq
  rw [hrEq, hrEq']
  exact intRel_trans hrDom hr₁Dom hr'Dom hLeft hRight

/-! ## Grafo de multiplicación sobre clases -/

/-- Predicado relacional de valor para el producto de dos clases. -/
def IntMulValue (x y z : ZFSet) : Prop :=
  ∃ p q r : ZFSet,
    p ∈ intDomain ∧
    q ∈ intDomain ∧
    r ∈ intDomain ∧
    x = intClass p ∧
    y = intClass q ∧
    z = intClass r ∧
    intRepMul p q r

/-- TA-DEF-00046 — grafo conjuntista de la multiplicación entera. -/
def intMulGraph : ZFSet :=
  ZFSet.sep
    (fun t =>
      ∃ x y z : ZFSet,
        x ∈ integersTA ∧
        y ∈ integersTA ∧
        z ∈ integersTA ∧
        t = ZFSet.pair (ZFSet.pair x y) z ∧
        IntMulValue x y z)
    (pairAmbient
      (cartesianProductFoundational integersTA integersTA)
      integersTA)

/-- Caracterización puntual del grafo de multiplicación. -/
theorem mem_intMulGraph {x y z : ZFSet} :
    ZFSet.pair (ZFSet.pair x y) z ∈ intMulGraph ↔
      x ∈ integersTA ∧ y ∈ integersTA ∧ z ∈ integersTA ∧
        IntMulValue x y z := by
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

/-- El grafo de multiplicación es una función total sobre pares de enteros. -/
theorem intMulGraph_isFunc :
    IsFuncFoundational
      (cartesianProductFoundational integersTA integersTA)
      integersTA
      intMulGraph := by
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
    rcases intRepMul_exists_unique hp hq with ⟨r, hr, _hrUnique⟩
    refine ⟨intClass r, ?_, ?_⟩
    · exact ⟨intClass_mem_integersTA hr.1,
        mem_intMulGraph.mpr ⟨hx, hy, intClass_mem_integersTA hr.1,
          p, q, r, hp, hq, hr.1, hxClass, hyClass, rfl, hr.2⟩⟩
    · intro z' hz'
      rcases (mem_intMulGraph.mp hz'.2).2.2.2 with
        ⟨p', q', r', hp', hq', hr', hxClass', hyClass', hzClass', hMul'⟩
      have hpp' : intRel p p' :=
        (TA_PRO_00038_intClass_eq_iff hp hp').mp
          (hxClass.symm.trans hxClass')
      have hqq' : intRel q q' :=
        (TA_PRO_00038_intClass_eq_iff hq hq').mp
          (hyClass.symm.trans hyClass')
      have hrr' : intRel r r' :=
        TA_PRO_00043_intRepMul_well_defined
          hp hp' hq hq' hpp' hqq' hr.2 hMul'
      have hClasses : intClass r = intClass r' :=
        (TA_PRO_00038_intClass_eq_iff hr.1 hr').mpr hrr'
      exact hzClass'.trans hClasses.symm

/-! ## Fórmula de clases y unidad -/

/-- Fórmula directa del producto sobre clases de representantes codificados. -/
theorem intMulGraph_natEncode_classes (A B C D : Nat) :
    ZFSet.pair
      (ZFSet.pair
        (intClass (ZFSet.pair (natEncode A) (natEncode B)))
        (intClass (ZFSet.pair (natEncode C) (natEncode D))))
      (intClass
        (ZFSet.pair
          (natEncode (A * C + B * D))
          (natEncode (A * D + B * C)))) ∈ intMulGraph := by
  have hp : ZFSet.pair (natEncode A) (natEncode B) ∈ intDomain :=
    mem_intDomain_iff.mpr
      ⟨_, _, natEncode_mem_omegaTA A, natEncode_mem_omegaTA B, rfl⟩
  have hq : ZFSet.pair (natEncode C) (natEncode D) ∈ intDomain :=
    mem_intDomain_iff.mpr
      ⟨_, _, natEncode_mem_omegaTA C, natEncode_mem_omegaTA D, rfl⟩
  have hr :
      ZFSet.pair
        (natEncode (A * C + B * D))
        (natEncode (A * D + B * C)) ∈ intDomain :=
    mem_intDomain_iff.mpr
      ⟨_, _, natEncode_mem_omegaTA _, natEncode_mem_omegaTA _, rfl⟩
  apply mem_intMulGraph.mpr
  exact ⟨intClass_mem_integersTA hp, intClass_mem_integersTA hq,
    intClass_mem_integersTA hr,
    ZFSet.pair (natEncode A) (natEncode B),
    ZFSet.pair (natEncode C) (natEncode D),
    ZFSet.pair
      (natEncode (A * C + B * D))
      (natEncode (A * D + B * C)),
    hp, hq, hr, rfl, rfl, rfl,
    (intRepMul_natEncode_iff A B C D _).mpr rfl⟩

/-- Un valor del grafo de producto sobre clases codificadas es exactamente
la clase del representante producto. -/
theorem intMulGraph_natEncode_classes_value_iff
    {A B C D : Nat} {z : ZFSet} :
    ZFSet.pair
      (ZFSet.pair
        (intClass (ZFSet.pair (natEncode A) (natEncode B)))
        (intClass (ZFSet.pair (natEncode C) (natEncode D)))) z ∈ intMulGraph ↔
    z = intClass
      (ZFSet.pair
        (natEncode (A * C + B * D))
        (natEncode (A * D + B * C))) := by
  constructor
  · intro hz
    have hInput :
        ZFSet.pair
          (intClass (ZFSet.pair (natEncode A) (natEncode B)))
          (intClass (ZFSet.pair (natEncode C) (natEncode D))) ∈
        cartesianProductFoundational integersTA integersTA := by
      apply mem_cartesianProductFoundational.mpr
      exact ⟨intClass_mem_integersTA
          (mem_intDomain_iff.mpr ⟨_, _, natEncode_mem_omegaTA A,
            natEncode_mem_omegaTA B, rfl⟩),
        intClass_mem_integersTA
          (mem_intDomain_iff.mpr ⟨_, _, natEncode_mem_omegaTA C,
            natEncode_mem_omegaTA D, rfl⟩)⟩
    rcases intMulGraph_isFunc.2 _ hInput with ⟨w, hw, hUnique⟩
    have hzMem : z ∈ integersTA :=
      funcFoundational_value_mem intMulGraph_isFunc hz
    have hExpected := intMulGraph_natEncode_classes A B C D
    have hExpectedMem :
        intClass
          (ZFSet.pair
            (natEncode (A * C + B * D))
            (natEncode (A * D + B * C))) ∈ integersTA :=
      funcFoundational_value_mem intMulGraph_isFunc hExpected
    exact (hUnique z ⟨hzMem, hz⟩).trans
      (hUnique _ ⟨hExpectedMem, hExpected⟩).symm
  · rintro rfl
    exact intMulGraph_natEncode_classes A B C D

/-- TA-NOT-00011 — clase de la diferencia formal `(1,0)`. -/
def intOne : ZFSet :=
  intClass (ZFSet.pair (natEncode 1) (natEncode 0))

/-- La unidad entera distinguida pertenece al cociente conjuntista. -/
theorem intOne_mem_integersTA : intOne ∈ integersTA := by
  apply intClass_mem_integersTA
  exact mem_intDomain_iff.mpr
    ⟨natEncode 1, natEncode 0, natEncode_mem_omegaTA 1,
      natEncode_mem_omegaTA 0, rfl⟩

end TratadoAnalisis.Integers.Multiplication
