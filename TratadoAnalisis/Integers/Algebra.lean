import TratadoAnalisis.Integers.Multiplication

namespace TratadoAnalisis.Integers.Algebra

open TratadoAnalisis.Naturals.Foundational
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Naturals.ArithmeticBridge
open TratadoAnalisis.Integers.Construction
open TratadoAnalisis.Integers.Operations
open TratadoAnalisis.Integers.Multiplication

/-! # Álgebra relacional del cociente entero -/

/-- Abreviatura transparente del grafo de suma ya construido. -/
def IntAdd (x y z : ZFSet) : Prop :=
  ZFSet.pair (ZFSet.pair x y) z ∈ intAddGraph

/-- Abreviatura transparente del grafo de producto ya construido. -/
def IntMul (x y z : ZFSet) : Prop :=
  ZFSet.pair (ZFSet.pair x y) z ∈ intMulGraph

/-- Abreviatura transparente del grafo de opuesto ya construido. -/
def IntNeg (x y : ZFSet) : Prop :=
  ZFSet.pair x y ∈ intNegGraph

/-- Todo entero admite localmente una presentación por dos códigos
naturales. No se define una selección simultánea de representantes. -/
theorem exists_natEncode_intClass_of_mem
    {x : ZFSet}
    (hx : x ∈ integersTA) :
    ∃ A B : Nat,
      x = intClass (ZFSet.pair (natEncode A) (natEncode B)) := by
  rcases mem_integersTA_iff.mp hx with ⟨p, hp, hxClass⟩
  rcases mem_intDomain_iff.mp hp with ⟨a, b, ha, hb, hpPair⟩
  rcases exists_natEncode_eq_of_mem ha with ⟨A, hA⟩
  rcases exists_natEncode_eq_of_mem hb with ⟨B, hB⟩
  refine ⟨A, B, ?_⟩
  rw [hxClass, hpPair, ← hA, ← hB]

/-! ## Unicidad mínima de los valores de los grafos -/

theorem IntAdd_unique
    {x y z₁ z₂ : ZFSet}
    (hx : x ∈ integersTA)
    (hy : y ∈ integersTA)
    (h₁ : IntAdd x y z₁)
    (h₂ : IntAdd x y z₂) :
    z₁ = z₂ := by
  have hxy := mem_cartesianProductFoundational.mpr ⟨hx, hy⟩
  rcases intAddGraph_isFunc.2 (ZFSet.pair x y) hxy with
    ⟨z, hz, hUnique⟩
  have hz₁ : z₁ ∈ integersTA :=
    funcFoundational_value_mem intAddGraph_isFunc h₁
  have hz₂ : z₂ ∈ integersTA :=
    funcFoundational_value_mem intAddGraph_isFunc h₂
  exact (hUnique z₁ ⟨hz₁, h₁⟩).trans
    (hUnique z₂ ⟨hz₂, h₂⟩).symm

theorem IntMul_unique
    {x y z₁ z₂ : ZFSet}
    (hx : x ∈ integersTA)
    (hy : y ∈ integersTA)
    (h₁ : IntMul x y z₁)
    (h₂ : IntMul x y z₂) :
    z₁ = z₂ := by
  have hxy := mem_cartesianProductFoundational.mpr ⟨hx, hy⟩
  rcases intMulGraph_isFunc.2 (ZFSet.pair x y) hxy with
    ⟨z, hz, hUnique⟩
  have hz₁ : z₁ ∈ integersTA :=
    funcFoundational_value_mem intMulGraph_isFunc h₁
  have hz₂ : z₂ ∈ integersTA :=
    funcFoundational_value_mem intMulGraph_isFunc h₂
  exact (hUnique z₁ ⟨hz₁, h₁⟩).trans
    (hUnique z₂ ⟨hz₂, h₂⟩).symm

theorem IntNeg_unique
    {x y₁ y₂ : ZFSet}
    (hx : x ∈ integersTA)
    (h₁ : IntNeg x y₁)
    (h₂ : IntNeg x y₂) :
    y₁ = y₂ := by
  rcases intNegGraph_isFunc.2 x hx with ⟨y, hy, hUnique⟩
  have hy₁ : y₁ ∈ integersTA :=
    funcFoundational_value_mem intNegGraph_isFunc h₁
  have hy₂ : y₂ ∈ integersTA :=
    funcFoundational_value_mem intNegGraph_isFunc h₂
  exact (hUnique y₁ ⟨hy₁, h₁⟩).trans
    (hUnique y₂ ⟨hy₂, h₂⟩).symm

/-! ## TA-PRO-00041 — leyes aditivas -/

theorem intAdd_assoc
    {x y z xy lhs yz rhs : ZFSet}
    (hx : x ∈ integersTA)
    (hy : y ∈ integersTA)
    (hz : z ∈ integersTA)
    (hxy : IntAdd x y xy)
    (hlhs : IntAdd xy z lhs)
    (hyz : IntAdd y z yz)
    (hrhs : IntAdd x yz rhs) :
    lhs = rhs := by
  rcases exists_natEncode_intClass_of_mem hx with ⟨A, B, rfl⟩
  rcases exists_natEncode_intClass_of_mem hy with ⟨C, D, rfl⟩
  rcases exists_natEncode_intClass_of_mem hz with ⟨E, F, rfl⟩
  have hxyEq :=
    intAddGraph_natEncode_classes_value_iff.mp hxy
  rw [hxyEq] at hlhs
  have hlhsEq :=
    (intAddGraph_natEncode_classes_value_iff
      (A := A + C) (B := B + D) (C := E) (D := F)).mp hlhs
  have hyzEq :=
    intAddGraph_natEncode_classes_value_iff.mp hyz
  rw [hyzEq] at hrhs
  have hrhsEq :=
    (intAddGraph_natEncode_classes_value_iff
      (A := A) (B := B) (C := C + E) (D := D + F)).mp hrhs
  rw [hlhsEq, hrhsEq]
  apply (TA_PRO_00038_natEncode_class_eq_iff
    ((A + C) + E) ((B + D) + F)
    (A + (C + E)) (B + (D + F))).mpr
  omega

theorem intAdd_comm
    {x y xy yx : ZFSet}
    (hx : x ∈ integersTA)
    (hy : y ∈ integersTA)
    (hxy : IntAdd x y xy)
    (hyx : IntAdd y x yx) :
    xy = yx := by
  rcases exists_natEncode_intClass_of_mem hx with ⟨A, B, rfl⟩
  rcases exists_natEncode_intClass_of_mem hy with ⟨C, D, rfl⟩
  have hxyEq := intAddGraph_natEncode_classes_value_iff.mp hxy
  have hyxEq := intAddGraph_natEncode_classes_value_iff.mp hyx
  rw [hxyEq, hyxEq]
  apply (TA_PRO_00038_natEncode_class_eq_iff
    (A + C) (B + D) (C + A) (D + B)).mpr
  omega

theorem intAdd_zero_right
    {x z : ZFSet}
    (hx : x ∈ integersTA)
    (h : IntAdd x intZero z) :
    z = x := by
  rcases exists_natEncode_intClass_of_mem hx with ⟨A, B, rfl⟩
  have hz :=
    (intAddGraph_natEncode_classes_value_iff
      (A := A) (B := B) (C := 0) (D := 0)).mp (by
        simpa [IntAdd, intZero] using h)
  simpa using hz

theorem intAdd_zero_left
    {x z : ZFSet}
    (hx : x ∈ integersTA)
    (h : IntAdd intZero x z) :
    z = x := by
  rcases exists_natEncode_intClass_of_mem hx with ⟨A, B, rfl⟩
  have hz :=
    (intAddGraph_natEncode_classes_value_iff
      (A := 0) (B := 0) (C := A) (D := B)).mp (by
        simpa [IntAdd, intZero] using h)
  simpa using hz

theorem intAdd_neg_right
    {x nx z : ZFSet}
    (hx : x ∈ integersTA)
    (hNeg : IntNeg x nx)
    (hAdd : IntAdd x nx z) :
    z = intZero := by
  rcases exists_natEncode_intClass_of_mem hx with ⟨A, B, rfl⟩
  have hnx := intNegGraph_natEncode_class_value_iff.mp hNeg
  rw [hnx] at hAdd
  have hz :=
    (intAddGraph_natEncode_classes_value_iff
      (A := A) (B := B) (C := B) (D := A)).mp hAdd
  rw [hz]
  change intClass
      (ZFSet.pair (natEncode (A + B)) (natEncode (B + A))) =
    intClass (ZFSet.pair (natEncode 0) (natEncode 0))
  apply (TA_PRO_00038_natEncode_class_eq_iff
    (A + B) (B + A) 0 0).mpr
  omega

theorem intAdd_neg_left
    {x nx z : ZFSet}
    (hx : x ∈ integersTA)
    (hNeg : IntNeg x nx)
    (hAdd : IntAdd nx x z) :
    z = intZero := by
  rcases exists_natEncode_intClass_of_mem hx with ⟨A, B, rfl⟩
  have hnx := intNegGraph_natEncode_class_value_iff.mp hNeg
  rw [hnx] at hAdd
  have hz :=
    (intAddGraph_natEncode_classes_value_iff
      (A := B) (B := A) (C := A) (D := B)).mp hAdd
  rw [hz]
  change intClass
      (ZFSet.pair (natEncode (B + A)) (natEncode (A + B))) =
    intClass (ZFSet.pair (natEncode 0) (natEncode 0))
  apply (TA_PRO_00038_natEncode_class_eq_iff
    (B + A) (A + B) 0 0).mpr
  omega

/-- TA-PRO-00041 — paquete explícito de las leyes del grupo aditivo. -/
theorem TA_PRO_00041_additive_group_laws :
    (∀ x y z xy lhs yz rhs : ZFSet,
      x ∈ integersTA → y ∈ integersTA → z ∈ integersTA →
      IntAdd x y xy → IntAdd xy z lhs →
      IntAdd y z yz → IntAdd x yz rhs → lhs = rhs) ∧
    (∀ x y xy yx : ZFSet,
      x ∈ integersTA → y ∈ integersTA →
      IntAdd x y xy → IntAdd y x yx → xy = yx) ∧
    (∀ x z : ZFSet,
      x ∈ integersTA → IntAdd x intZero z → z = x) ∧
    (∀ x z : ZFSet,
      x ∈ integersTA → IntAdd intZero x z → z = x) ∧
    (∀ x nx z : ZFSet,
      x ∈ integersTA → IntNeg x nx →
      IntAdd x nx z → z = intZero) ∧
    (∀ x nx z : ZFSet,
      x ∈ integersTA → IntNeg x nx →
      IntAdd nx x z → z = intZero) := by
  exact ⟨fun _ _ _ _ _ _ _ => intAdd_assoc,
    fun _ _ _ _ => intAdd_comm,
    fun _ _ => intAdd_zero_right,
    fun _ _ => intAdd_zero_left,
    fun _ _ _ => intAdd_neg_right,
    fun _ _ _ => intAdd_neg_left⟩

/-! ## TA-PRO-00044 — leyes multiplicativas y distributivas -/

theorem intMul_assoc
    {x y z xy lhs yz rhs : ZFSet}
    (hx : x ∈ integersTA)
    (hy : y ∈ integersTA)
    (hz : z ∈ integersTA)
    (hxy : IntMul x y xy)
    (hlhs : IntMul xy z lhs)
    (hyz : IntMul y z yz)
    (hrhs : IntMul x yz rhs) :
    lhs = rhs := by
  rcases exists_natEncode_intClass_of_mem hx with ⟨A, B, rfl⟩
  rcases exists_natEncode_intClass_of_mem hy with ⟨C, D, rfl⟩
  rcases exists_natEncode_intClass_of_mem hz with ⟨E, F, rfl⟩
  have hxyEq := intMulGraph_natEncode_classes_value_iff.mp hxy
  rw [hxyEq] at hlhs
  have hlhsEq :=
    (intMulGraph_natEncode_classes_value_iff
      (A := A * C + B * D) (B := A * D + B * C)
      (C := E) (D := F)).mp hlhs
  have hyzEq := intMulGraph_natEncode_classes_value_iff.mp hyz
  rw [hyzEq] at hrhs
  have hrhsEq :=
    (intMulGraph_natEncode_classes_value_iff
      (A := A) (B := B)
      (C := C * E + D * F) (D := C * F + D * E)).mp hrhs
  rw [hlhsEq, hrhsEq]
  apply (TA_PRO_00038_natEncode_class_eq_iff
    ((A * C + B * D) * E + (A * D + B * C) * F)
    ((A * C + B * D) * F + (A * D + B * C) * E)
    (A * (C * E + D * F) + B * (C * F + D * E))
    (A * (C * F + D * E) + B * (C * E + D * F))).mpr
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc]
  omega

theorem intMul_comm
    {x y xy yx : ZFSet}
    (hx : x ∈ integersTA)
    (hy : y ∈ integersTA)
    (hxy : IntMul x y xy)
    (hyx : IntMul y x yx) :
    xy = yx := by
  rcases exists_natEncode_intClass_of_mem hx with ⟨A, B, rfl⟩
  rcases exists_natEncode_intClass_of_mem hy with ⟨C, D, rfl⟩
  have hxyEq := intMulGraph_natEncode_classes_value_iff.mp hxy
  have hyxEq := intMulGraph_natEncode_classes_value_iff.mp hyx
  rw [hxyEq, hyxEq]
  apply (TA_PRO_00038_natEncode_class_eq_iff
    (A * C + B * D) (A * D + B * C)
    (C * A + D * B) (C * B + D * A)).mpr
  simp only [Nat.mul_comm]
  omega

theorem intMul_one_left
    {x z : ZFSet}
    (hx : x ∈ integersTA)
    (h : IntMul intOne x z) :
    z = x := by
  rcases exists_natEncode_intClass_of_mem hx with ⟨A, B, rfl⟩
  have hz :=
    (intMulGraph_natEncode_classes_value_iff
      (A := 1) (B := 0) (C := A) (D := B)).mp (by
        simpa [IntMul, intOne] using h)
  simpa using hz

theorem intMul_one_right
    {x z : ZFSet}
    (hx : x ∈ integersTA)
    (h : IntMul x intOne z) :
    z = x := by
  rcases exists_natEncode_intClass_of_mem hx with ⟨A, B, rfl⟩
  have hz :=
    (intMulGraph_natEncode_classes_value_iff
      (A := A) (B := B) (C := 1) (D := 0)).mp (by
        simpa [IntMul, intOne] using h)
  simpa using hz

theorem intMul_add_left
    {x y z yz lhs xy xz rhs : ZFSet}
    (hx : x ∈ integersTA)
    (hy : y ∈ integersTA)
    (hz : z ∈ integersTA)
    (hyz : IntAdd y z yz)
    (hlhs : IntMul x yz lhs)
    (hxy : IntMul x y xy)
    (hxz : IntMul x z xz)
    (hrhs : IntAdd xy xz rhs) :
    lhs = rhs := by
  rcases exists_natEncode_intClass_of_mem hx with ⟨A, B, rfl⟩
  rcases exists_natEncode_intClass_of_mem hy with ⟨C, D, rfl⟩
  rcases exists_natEncode_intClass_of_mem hz with ⟨E, F, rfl⟩
  have hyzEq := intAddGraph_natEncode_classes_value_iff.mp hyz
  rw [hyzEq] at hlhs
  have hlhsEq :=
    (intMulGraph_natEncode_classes_value_iff
      (A := A) (B := B) (C := C + E) (D := D + F)).mp hlhs
  have hxyEq := intMulGraph_natEncode_classes_value_iff.mp hxy
  have hxzEq := intMulGraph_natEncode_classes_value_iff.mp hxz
  rw [hxyEq, hxzEq] at hrhs
  have hrhsEq :=
    (intAddGraph_natEncode_classes_value_iff
      (A := A * C + B * D) (B := A * D + B * C)
      (C := A * E + B * F) (D := A * F + B * E)).mp hrhs
  rw [hlhsEq, hrhsEq]
  apply (TA_PRO_00038_natEncode_class_eq_iff
    (A * (C + E) + B * (D + F))
    (A * (D + F) + B * (C + E))
    ((A * C + B * D) + (A * E + B * F))
    ((A * D + B * C) + (A * F + B * E))).mpr
  simp only [Nat.mul_add]
  omega

theorem intAdd_mul_right
    {x y z xy lhs xz yz rhs : ZFSet}
    (hx : x ∈ integersTA)
    (hy : y ∈ integersTA)
    (hz : z ∈ integersTA)
    (hxy : IntAdd x y xy)
    (hlhs : IntMul xy z lhs)
    (hxz : IntMul x z xz)
    (hyz : IntMul y z yz)
    (hrhs : IntAdd xz yz rhs) :
    lhs = rhs := by
  rcases exists_natEncode_intClass_of_mem hx with ⟨A, B, rfl⟩
  rcases exists_natEncode_intClass_of_mem hy with ⟨C, D, rfl⟩
  rcases exists_natEncode_intClass_of_mem hz with ⟨E, F, rfl⟩
  have hxyEq := intAddGraph_natEncode_classes_value_iff.mp hxy
  rw [hxyEq] at hlhs
  have hlhsEq :=
    (intMulGraph_natEncode_classes_value_iff
      (A := A + C) (B := B + D) (C := E) (D := F)).mp hlhs
  have hxzEq := intMulGraph_natEncode_classes_value_iff.mp hxz
  have hyzEq := intMulGraph_natEncode_classes_value_iff.mp hyz
  rw [hxzEq, hyzEq] at hrhs
  have hrhsEq :=
    (intAddGraph_natEncode_classes_value_iff
      (A := A * E + B * F) (B := A * F + B * E)
      (C := C * E + D * F) (D := C * F + D * E)).mp hrhs
  rw [hlhsEq, hrhsEq]
  apply (TA_PRO_00038_natEncode_class_eq_iff
    ((A + C) * E + (B + D) * F)
    ((A + C) * F + (B + D) * E)
    ((A * E + B * F) + (C * E + D * F))
    ((A * F + B * E) + (C * F + D * E))).mpr
  simp only [Nat.add_mul]
  omega

/-- TA-PRO-00044 — paquete explícito de asociatividad, conmutatividad,
unidad bilateral y ambas distributividades. -/
theorem TA_PRO_00044_mul_distrib_laws :
    (∀ x y z xy lhs yz rhs : ZFSet,
      x ∈ integersTA → y ∈ integersTA → z ∈ integersTA →
      IntMul x y xy → IntMul xy z lhs →
      IntMul y z yz → IntMul x yz rhs → lhs = rhs) ∧
    (∀ x y xy yx : ZFSet,
      x ∈ integersTA → y ∈ integersTA →
      IntMul x y xy → IntMul y x yx → xy = yx) ∧
    (∀ x z : ZFSet,
      x ∈ integersTA → IntMul intOne x z → z = x) ∧
    (∀ x z : ZFSet,
      x ∈ integersTA → IntMul x intOne z → z = x) ∧
    (∀ x y z yz lhs xy xz rhs : ZFSet,
      x ∈ integersTA → y ∈ integersTA → z ∈ integersTA →
      IntAdd y z yz → IntMul x yz lhs →
      IntMul x y xy → IntMul x z xz →
      IntAdd xy xz rhs → lhs = rhs) ∧
    (∀ x y z xy lhs xz yz rhs : ZFSet,
      x ∈ integersTA → y ∈ integersTA → z ∈ integersTA →
      IntAdd x y xy → IntMul xy z lhs →
      IntMul x z xz → IntMul y z yz →
      IntAdd xz yz rhs → lhs = rhs) := by
  exact ⟨fun _ _ _ _ _ _ _ => intMul_assoc,
    fun _ _ _ _ => intMul_comm,
    fun _ _ => intMul_one_left,
    fun _ _ => intMul_one_right,
    fun _ _ _ _ _ _ _ _ => intMul_add_left,
    fun _ _ _ _ _ _ _ _ => intAdd_mul_right⟩

/-! ## TA-THM-00024 — paquete de anillo -/

/-- Resumen explícito: las leyes aditivas y las leyes
multiplicativas/distributivas ya demostradas forman el paquete humano de
anillo conmutativo con identidad. -/
theorem TA_THM_00024_commutative_ring_package :
    ((∀ x y z xy lhs yz rhs : ZFSet,
        x ∈ integersTA → y ∈ integersTA → z ∈ integersTA →
        IntAdd x y xy → IntAdd xy z lhs →
        IntAdd y z yz → IntAdd x yz rhs → lhs = rhs) ∧
      (∀ x y xy yx : ZFSet,
        x ∈ integersTA → y ∈ integersTA →
        IntAdd x y xy → IntAdd y x yx → xy = yx) ∧
      (∀ x z : ZFSet,
        x ∈ integersTA → IntAdd x intZero z → z = x) ∧
      (∀ x z : ZFSet,
        x ∈ integersTA → IntAdd intZero x z → z = x) ∧
      (∀ x nx z : ZFSet,
        x ∈ integersTA → IntNeg x nx →
        IntAdd x nx z → z = intZero) ∧
      (∀ x nx z : ZFSet,
        x ∈ integersTA → IntNeg x nx →
        IntAdd nx x z → z = intZero)) ∧
    ((∀ x y z xy lhs yz rhs : ZFSet,
        x ∈ integersTA → y ∈ integersTA → z ∈ integersTA →
        IntMul x y xy → IntMul xy z lhs →
        IntMul y z yz → IntMul x yz rhs → lhs = rhs) ∧
      (∀ x y xy yx : ZFSet,
        x ∈ integersTA → y ∈ integersTA →
        IntMul x y xy → IntMul y x yx → xy = yx) ∧
      (∀ x z : ZFSet,
        x ∈ integersTA → IntMul intOne x z → z = x) ∧
      (∀ x z : ZFSet,
        x ∈ integersTA → IntMul x intOne z → z = x) ∧
      (∀ x y z yz lhs xy xz rhs : ZFSet,
        x ∈ integersTA → y ∈ integersTA → z ∈ integersTA →
        IntAdd y z yz → IntMul x yz lhs →
        IntMul x y xy → IntMul x z xz →
        IntAdd xy xz rhs → lhs = rhs) ∧
      (∀ x y z xy lhs xz yz rhs : ZFSet,
        x ∈ integersTA → y ∈ integersTA → z ∈ integersTA →
        IntAdd x y xy → IntMul xy z lhs →
        IntMul x z xz → IntMul y z yz →
        IntAdd xz yz rhs → lhs = rhs)) := by
  exact ⟨TA_PRO_00041_additive_group_laws,
    TA_PRO_00044_mul_distrib_laws⟩

/-! ## TA-DEF-00047 — incrustación conjuntista de los naturales -/

/-- Predicado de valor de la incrustación humana `n ↦ [(n,0)]`. -/
def IntEmbedValue (n z : ZFSet) : Prop :=
  n ∈ omegaTA ∧
  z = intClass (ZFSet.pair n (∅ : ZFSet))

/-- TA-DEF-00047 — grafo conjuntista de la incrustación
`omegaTA → integersTA`. -/
def intEmbedGraph : ZFSet :=
  ZFSet.sep
    (fun t =>
      ∃ n z : ZFSet,
        n ∈ omegaTA ∧
        z ∈ integersTA ∧
        t = ZFSet.pair n z ∧
        IntEmbedValue n z)
    (pairAmbient omegaTA integersTA)

theorem mem_intEmbedGraph {n z : ZFSet} :
    ZFSet.pair n z ∈ intEmbedGraph ↔
      n ∈ omegaTA ∧ z ∈ integersTA ∧ IntEmbedValue n z := by
  constructor
  · intro h
    rcases (ZFSet.mem_sep.mp h).2 with
      ⟨n', z', hn', hz', hEq, hValue⟩
    rcases ZFSet.pair_injective hEq with ⟨hn, hz⟩
    subst n'
    subst z'
    exact ⟨hn', hz', hValue⟩
  · rintro ⟨hn, hz, hValue⟩
    apply ZFSet.mem_sep.mpr
    exact ⟨pair_mem_pairAmbient hn hz,
      n, z, hn, hz, rfl, hValue⟩

theorem intEmbedGraph_isFunc :
    IsFuncFoundational omegaTA integersTA intEmbedGraph := by
  constructor
  · intro t ht
    rcases (ZFSet.mem_sep.mp ht).2 with
      ⟨n, z, hn, hz, rfl, _hValue⟩
    exact ⟨n, hn, z, hz, rfl⟩
  · intro n hn
    have hZero : (∅ : ZFSet) ∈ omegaTA := omegaTA_isInductive.1
    have hRep : ZFSet.pair n (∅ : ZFSet) ∈ intDomain :=
      mem_intDomain_iff.mpr ⟨n, ∅, hn, hZero, rfl⟩
    refine ⟨intClass (ZFSet.pair n (∅ : ZFSet)), ?_, ?_⟩
    · exact ⟨intClass_mem_integersTA hRep,
        mem_intEmbedGraph.mpr
          ⟨hn, intClass_mem_integersTA hRep, hn, rfl⟩⟩
    · intro z hz
      exact (mem_intEmbedGraph.mp hz.2).2.2.2

/-- Fórmula del embedding sobre un código natural. -/
theorem intEmbedGraph_natEncode (n : Nat) :
    ZFSet.pair
      (natEncode n)
      (intClass (ZFSet.pair (natEncode n) (natEncode 0))) ∈
      intEmbedGraph := by
  have hn := natEncode_mem_omegaTA n
  have hZero := natEncode_mem_omegaTA 0
  have hRep :
      ZFSet.pair (natEncode n) (natEncode 0) ∈ intDomain :=
    mem_intDomain_iff.mpr ⟨_, _, hn, hZero, rfl⟩
  apply mem_intEmbedGraph.mpr
  exact ⟨hn, intClass_mem_integersTA hRep, hn, rfl⟩

theorem intEmbedGraph_natEncode_value_iff
    {n : Nat} {z : ZFSet} :
    ZFSet.pair (natEncode n) z ∈ intEmbedGraph ↔
      z = intClass (ZFSet.pair (natEncode n) (natEncode 0)) := by
  constructor
  · intro hz
    rcases intEmbedGraph_isFunc.2 _ (natEncode_mem_omegaTA n) with
      ⟨w, hw, hUnique⟩
    have hzMem : z ∈ integersTA :=
      funcFoundational_value_mem intEmbedGraph_isFunc hz
    have hExpected := intEmbedGraph_natEncode n
    have hExpectedMem :
        intClass (ZFSet.pair (natEncode n) (natEncode 0)) ∈ integersTA :=
      funcFoundational_value_mem intEmbedGraph_isFunc hExpected
    exact (hUnique z ⟨hzMem, hz⟩).trans
      (hUnique _ ⟨hExpectedMem, hExpected⟩).symm
  · rintro rfl
    exact intEmbedGraph_natEncode n

/-! ## TA-PRO-00045 — propiedades del embedding -/

theorem intEmbedGraph_injective
    {m n zm zn : ZFSet}
    (hm : m ∈ omegaTA)
    (hn : n ∈ omegaTA)
    (hmz : ZFSet.pair m zm ∈ intEmbedGraph)
    (hnz : ZFSet.pair n zn ∈ intEmbedGraph)
    (hValues : zm = zn) :
    m = n := by
  rcases exists_natEncode_eq_of_mem hm with ⟨M, rfl⟩
  rcases exists_natEncode_eq_of_mem hn with ⟨N, rfl⟩
  have hzm := intEmbedGraph_natEncode_value_iff.mp hmz
  have hzn := intEmbedGraph_natEncode_value_iff.mp hnz
  rw [hzm, hzn] at hValues
  have hMN : M + 0 = 0 + N :=
    (TA_PRO_00038_natEncode_class_eq_iff M 0 N 0).mp hValues
  have : M = N := by omega
  exact congrArg natEncode this

theorem intEmbedGraph_zero :
    ZFSet.pair (natEncode 0) intZero ∈ intEmbedGraph := by
  simpa [intZero] using intEmbedGraph_natEncode 0

theorem intEmbedGraph_one :
    ZFSet.pair (natEncode 1) intOne ∈ intEmbedGraph := by
  simpa [intOne] using intEmbedGraph_natEncode 1

theorem intEmbedGraph_add_nat (M N : Nat) :
    ZFSet.pair (natEncode M)
        (intClass (ZFSet.pair (natEncode M) (natEncode 0))) ∈ intEmbedGraph ∧
    ZFSet.pair (natEncode N)
        (intClass (ZFSet.pair (natEncode N) (natEncode 0))) ∈ intEmbedGraph ∧
    ZFSet.pair (natEncode (M + N))
        (intClass (ZFSet.pair (natEncode (M + N)) (natEncode 0))) ∈
          intEmbedGraph ∧
    IntAdd
      (intClass (ZFSet.pair (natEncode M) (natEncode 0)))
      (intClass (ZFSet.pair (natEncode N) (natEncode 0)))
      (intClass (ZFSet.pair (natEncode (M + N)) (natEncode 0))) := by
  refine ⟨intEmbedGraph_natEncode M, intEmbedGraph_natEncode N,
    intEmbedGraph_natEncode (M + N), ?_⟩
  change ZFSet.pair
      (ZFSet.pair
        (intClass (ZFSet.pair (natEncode M) (natEncode 0)))
        (intClass (ZFSet.pair (natEncode N) (natEncode 0))))
      (intClass (ZFSet.pair (natEncode (M + N)) (natEncode 0))) ∈ intAddGraph
  simpa using intAddGraph_natEncode_classes M 0 N 0

theorem intEmbedGraph_mul_nat (M N : Nat) :
    ZFSet.pair (natEncode M)
        (intClass (ZFSet.pair (natEncode M) (natEncode 0))) ∈ intEmbedGraph ∧
    ZFSet.pair (natEncode N)
        (intClass (ZFSet.pair (natEncode N) (natEncode 0))) ∈ intEmbedGraph ∧
    ZFSet.pair (natEncode (M * N))
        (intClass (ZFSet.pair (natEncode (M * N)) (natEncode 0))) ∈
          intEmbedGraph ∧
    IntMul
      (intClass (ZFSet.pair (natEncode M) (natEncode 0)))
      (intClass (ZFSet.pair (natEncode N) (natEncode 0)))
      (intClass (ZFSet.pair (natEncode (M * N)) (natEncode 0))) := by
  refine ⟨intEmbedGraph_natEncode M, intEmbedGraph_natEncode N,
    intEmbedGraph_natEncode (M * N), ?_⟩
  change ZFSet.pair
      (ZFSet.pair
        (intClass (ZFSet.pair (natEncode M) (natEncode 0)))
        (intClass (ZFSet.pair (natEncode N) (natEncode 0))))
      (intClass (ZFSet.pair (natEncode (M * N)) (natEncode 0))) ∈ intMulGraph
  simpa using intMulGraph_natEncode_classes M 0 N 0

/-- TA-PRO-00045 — inyectividad y preservación explícita de cero, uno,
suma y producto por la incrustación conjuntista. -/
theorem TA_PRO_00045_embedding_properties :
    (∀ m n zm zn : ZFSet,
      m ∈ omegaTA → n ∈ omegaTA →
      ZFSet.pair m zm ∈ intEmbedGraph →
      ZFSet.pair n zn ∈ intEmbedGraph →
      zm = zn → m = n) ∧
    ZFSet.pair (natEncode 0) intZero ∈ intEmbedGraph ∧
    ZFSet.pair (natEncode 1) intOne ∈ intEmbedGraph ∧
    (∀ M N : Nat,
      ZFSet.pair (natEncode M)
          (intClass (ZFSet.pair (natEncode M) (natEncode 0))) ∈ intEmbedGraph ∧
      ZFSet.pair (natEncode N)
          (intClass (ZFSet.pair (natEncode N) (natEncode 0))) ∈ intEmbedGraph ∧
      ZFSet.pair (natEncode (M + N))
          (intClass (ZFSet.pair (natEncode (M + N)) (natEncode 0))) ∈
            intEmbedGraph ∧
      IntAdd
        (intClass (ZFSet.pair (natEncode M) (natEncode 0)))
        (intClass (ZFSet.pair (natEncode N) (natEncode 0)))
        (intClass (ZFSet.pair (natEncode (M + N)) (natEncode 0)))) ∧
    (∀ M N : Nat,
      ZFSet.pair (natEncode M)
          (intClass (ZFSet.pair (natEncode M) (natEncode 0))) ∈ intEmbedGraph ∧
      ZFSet.pair (natEncode N)
          (intClass (ZFSet.pair (natEncode N) (natEncode 0))) ∈ intEmbedGraph ∧
      ZFSet.pair (natEncode (M * N))
          (intClass (ZFSet.pair (natEncode (M * N)) (natEncode 0))) ∈
            intEmbedGraph ∧
      IntMul
        (intClass (ZFSet.pair (natEncode M) (natEncode 0)))
        (intClass (ZFSet.pair (natEncode N) (natEncode 0)))
        (intClass (ZFSet.pair (natEncode (M * N)) (natEncode 0)))) := by
  exact ⟨fun _ _ _ _ => intEmbedGraph_injective,
    intEmbedGraph_zero, intEmbedGraph_one,
    intEmbedGraph_add_nat, intEmbedGraph_mul_nat⟩

end TratadoAnalisis.Integers.Algebra
