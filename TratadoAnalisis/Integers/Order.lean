import TratadoAnalisis.Integers.Domain

namespace TratadoAnalisis.Integers.Order

open TratadoAnalisis.Naturals.Foundational
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Naturals.ArithmeticBridge
open TratadoAnalisis.Integers.Construction
open TratadoAnalisis.Integers.Operations
open TratadoAnalisis.Integers.Multiplication
open TratadoAnalisis.Integers.Algebra
open TratadoAnalisis.Integers.Domain

/-! # Orden entero definido directamente sobre el cociente -/

/-- Puente mínimo de orden sobre los naturales conjuntistas. -/
def NatLETA (m n : ZFSet) : Prop :=
  m ∈ omegaTA ∧
  n ∈ omegaTA ∧
  ∃ k : ZFSet,
    k ∈ omegaTA ∧
    ZFSet.pair (ZFSet.pair m k) n ∈ natAddGraph

theorem NatLETA_natEncode_iff (M N : Nat) :
    NatLETA (natEncode M) (natEncode N) ↔ M ≤ N := by
  constructor
  · rintro ⟨_hM, _hN, k, hk, hAdd⟩
    rcases exists_natEncode_eq_of_mem hk with ⟨K, rfl⟩
    have hEq : natEncode N = natEncode (M + K) :=
      natAddGraph_natEncode_value_iff.mp hAdd
    have : N = M + K := natEncode_injective hEq
    omega
  · intro hMN
    rcases Nat.exists_eq_add_of_le hMN with ⟨K, hEq⟩
    refine ⟨natEncode_mem_omegaTA M, natEncode_mem_omegaTA N,
      natEncode K, natEncode_mem_omegaTA K, ?_⟩
    rw [hEq]
    exact natAddGraph_natEncode M K

/-! ## TA-DEF-00048 — orden directo y su relación conjuntista -/

/-- Orden entero directo: `x ≤ y` cuando `y = x + ι(n)` para algún
natural conjuntista `n`. -/
def IntLE (x y : ZFSet) : Prop :=
  x ∈ integersTA ∧
  y ∈ integersTA ∧
  ∃ n e : ZFSet,
    n ∈ omegaTA ∧
    ZFSet.pair n e ∈ intEmbedGraph ∧
    IntAdd x e y

/-- TA-DEF-00048 — objeto conjuntista que representa la relación de orden. -/
def intOrderRel : ZFSet :=
  ZFSet.sep
    (fun t =>
      ∃ x y : ZFSet,
        x ∈ integersTA ∧
        y ∈ integersTA ∧
        t = ZFSet.pair x y ∧
        IntLE x y)
    (pairAmbient integersTA integersTA)

theorem mem_intOrderRel_iff {x y : ZFSet} :
    ZFSet.pair x y ∈ intOrderRel ↔ IntLE x y := by
  constructor
  · intro h
    rcases (ZFSet.mem_sep.mp h).2 with
      ⟨x', y', _hx', _hy', hEq, hLE⟩
    rcases ZFSet.pair_injective hEq with ⟨hx, hy⟩
    subst x'
    subst y'
    exact hLE
  · intro hLE
    apply ZFSet.mem_sep.mpr
    exact ⟨pair_mem_pairAmbient hLE.1 hLE.2.1,
      x, y, hLE.1, hLE.2.1, rfl, hLE⟩

/-! ## TA-PRO-00048 — criterio por representantes -/

theorem TA_PRO_00048_intLE_natEncode_classes_iff
    (A B C D : Nat) :
    IntLE
      (intClass (ZFSet.pair (natEncode A) (natEncode B)))
      (intClass (ZFSet.pair (natEncode C) (natEncode D))) ↔
    A + D ≤ C + B := by
  constructor
  · rintro ⟨_hx, _hy, n, e, hn, hEmbed, hAdd⟩
    rcases exists_natEncode_eq_of_mem hn with ⟨N, rfl⟩
    have he := intEmbedGraph_natEncode_value_iff.mp hEmbed
    rw [he] at hAdd
    have hValue :=
      (intAddGraph_natEncode_classes_value_iff
        (A := A) (B := B) (C := N) (D := 0)).mp hAdd
    have hEq :=
      (TA_PRO_00038_natEncode_class_eq_iff
        C D (A + N) (B + 0)).mp hValue
    omega
  · intro hLE
    rcases Nat.exists_eq_add_of_le hLE with ⟨N, hN⟩
    have hx :
        intClass (ZFSet.pair (natEncode A) (natEncode B)) ∈ integersTA :=
      intClass_mem_integersTA
        (mem_intDomain_iff.mpr ⟨_, _, natEncode_mem_omegaTA A,
          natEncode_mem_omegaTA B, rfl⟩)
    have hy :
        intClass (ZFSet.pair (natEncode C) (natEncode D)) ∈ integersTA :=
      intClass_mem_integersTA
        (mem_intDomain_iff.mpr ⟨_, _, natEncode_mem_omegaTA C,
          natEncode_mem_omegaTA D, rfl⟩)
    have hClass :
        intClass (ZFSet.pair (natEncode C) (natEncode D)) =
          intClass (ZFSet.pair (natEncode (A + N)) (natEncode B)) := by
      apply (TA_PRO_00038_natEncode_class_eq_iff
        C D (A + N) B).mpr
      omega
    refine ⟨hx, hy, natEncode N,
      intClass (ZFSet.pair (natEncode N) (natEncode 0)),
      natEncode_mem_omegaTA N, intEmbedGraph_natEncode N, ?_⟩
    rw [hClass]
    exact intAddGraph_natEncode_classes A B N 0

/-! ## TA-THM-00027 — orden total -/

theorem intLE_refl {x : ZFSet} (hx : x ∈ integersTA) : IntLE x x := by
  rcases exists_natEncode_intClass_of_mem hx with ⟨A, B, rfl⟩
  apply (TA_PRO_00048_intLE_natEncode_classes_iff A B A B).mpr
  omega

theorem intLE_trans
    {x y z : ZFSet}
    (hx : x ∈ integersTA)
    (hy : y ∈ integersTA)
    (hz : z ∈ integersTA)
    (hxy : IntLE x y)
    (hyz : IntLE y z) :
    IntLE x z := by
  rcases exists_natEncode_intClass_of_mem hx with ⟨A, B, rfl⟩
  rcases exists_natEncode_intClass_of_mem hy with ⟨C, D, rfl⟩
  rcases exists_natEncode_intClass_of_mem hz with ⟨E, F, rfl⟩
  have h₁ := (TA_PRO_00048_intLE_natEncode_classes_iff A B C D).mp hxy
  have h₂ := (TA_PRO_00048_intLE_natEncode_classes_iff C D E F).mp hyz
  apply (TA_PRO_00048_intLE_natEncode_classes_iff A B E F).mpr
  omega

theorem intLE_antisymm
    {x y : ZFSet}
    (hx : x ∈ integersTA)
    (hy : y ∈ integersTA)
    (hxy : IntLE x y)
    (hyx : IntLE y x) :
    x = y := by
  rcases exists_natEncode_intClass_of_mem hx with ⟨A, B, rfl⟩
  rcases exists_natEncode_intClass_of_mem hy with ⟨C, D, rfl⟩
  have h₁ := (TA_PRO_00048_intLE_natEncode_classes_iff A B C D).mp hxy
  have h₂ := (TA_PRO_00048_intLE_natEncode_classes_iff C D A B).mp hyx
  apply (TA_PRO_00038_natEncode_class_eq_iff A B C D).mpr
  omega

theorem intLE_total
    {x y : ZFSet}
    (hx : x ∈ integersTA)
    (hy : y ∈ integersTA) :
    IntLE x y ∨ IntLE y x := by
  rcases exists_natEncode_intClass_of_mem hx with ⟨A, B, rfl⟩
  rcases exists_natEncode_intClass_of_mem hy with ⟨C, D, rfl⟩
  rcases Nat.le_total (A + D) (C + B) with h | h
  · exact Or.inl
      ((TA_PRO_00048_intLE_natEncode_classes_iff A B C D).mpr h)
  · exact Or.inr
      ((TA_PRO_00048_intLE_natEncode_classes_iff C D A B).mpr h)

theorem TA_THM_00027_total_order :
    (∀ x : ZFSet, x ∈ integersTA → IntLE x x) ∧
    (∀ x y z : ZFSet,
      x ∈ integersTA → y ∈ integersTA → z ∈ integersTA →
      IntLE x y → IntLE y z → IntLE x z) ∧
    (∀ x y : ZFSet,
      x ∈ integersTA → y ∈ integersTA →
      IntLE x y → IntLE y x → x = y) ∧
    (∀ x y : ZFSet,
      x ∈ integersTA → y ∈ integersTA →
      IntLE x y ∨ IntLE y x) := by
  exact ⟨fun _ => intLE_refl,
    fun _ _ _ => intLE_trans,
    fun _ _ => intLE_antisymm,
    fun _ _ => intLE_total⟩

/-! ## TA-PRO-00049A — compatibilidad aditiva -/

theorem intLE_add_compat
    {x y z xz yz : ZFSet}
    (hx : x ∈ integersTA)
    (hy : y ∈ integersTA)
    (hz : z ∈ integersTA)
    (hxy : IntLE x y)
    (hxz : IntAdd x z xz)
    (hyz : IntAdd y z yz) :
    IntLE xz yz := by
  rcases exists_natEncode_intClass_of_mem hx with ⟨A, B, rfl⟩
  rcases exists_natEncode_intClass_of_mem hy with ⟨C, D, rfl⟩
  rcases exists_natEncode_intClass_of_mem hz with ⟨E, F, rfl⟩
  have hLE :=
    (TA_PRO_00048_intLE_natEncode_classes_iff A B C D).mp hxy
  have hxzEq := intAddGraph_natEncode_classes_value_iff.mp hxz
  have hyzEq := intAddGraph_natEncode_classes_value_iff.mp hyz
  rw [hxzEq, hyzEq]
  apply (TA_PRO_00048_intLE_natEncode_classes_iff
    (A + E) (B + F) (C + E) (D + F)).mpr
  omega

/-! ## TA-PRO-00049B — producto por un factor no negativo -/

theorem intEmbed_values_mul
    {n m en em : ZFSet}
    (hn : n ∈ omegaTA)
    (hm : m ∈ omegaTA)
    (hEmbedN : ZFSet.pair n en ∈ intEmbedGraph)
    (hEmbedM : ZFSet.pair m em ∈ intEmbedGraph) :
    ∃ k ek : ZFSet,
      k ∈ omegaTA ∧
      ZFSet.pair k ek ∈ intEmbedGraph ∧
      IntMul en em ek := by
  rcases exists_natEncode_eq_of_mem hn with ⟨N, rfl⟩
  rcases exists_natEncode_eq_of_mem hm with ⟨M, rfl⟩
  have hEnEq := intEmbedGraph_natEncode_value_iff.mp hEmbedN
  have hEmEq := intEmbedGraph_natEncode_value_iff.mp hEmbedM
  refine ⟨natEncode (N * M),
    intClass (ZFSet.pair (natEncode (N * M)) (natEncode 0)),
    natEncode_mem_omegaTA (N * M), intEmbedGraph_natEncode (N * M), ?_⟩
  rw [hEnEq, hEmEq]
  simpa [IntMul] using intMulGraph_natEncode_classes N 0 M 0

theorem intLE_mul_nonnegative_compat
    {x y z xz yz : ZFSet}
    (hx : x ∈ integersTA)
    (_hy : y ∈ integersTA)
    (hz : z ∈ integersTA)
    (hxy : IntLE x y)
    (hzNonnegative : IntLE intZero z)
    (hMulX : IntMul x z xz)
    (hMulY : IntMul y z yz) :
    IntLE xz yz := by
  rcases hxy with
    ⟨_hxLE, _hyLE, n, en, hn, hEmbedN, hAddXY⟩
  rcases hzNonnegative with
    ⟨_hZeroLE, _hzLE, m, em, hm, hEmbedM, hAddZeroM⟩
  have hEnMem : en ∈ integersTA :=
    funcFoundational_value_mem intEmbedGraph_isFunc hEmbedN
  have hEmMem : em ∈ integersTA :=
    funcFoundational_value_mem intEmbedGraph_isFunc hEmbedM
  have hzEq : z = em := intAdd_zero_left hEmMem hAddZeroM
  rcases intEmbed_values_mul hn hm hEmbedN hEmbedM with
    ⟨k, ek, hk, hEmbedK, hEnEm⟩
  have hEnZ : IntMul en z ek := by
    rw [hzEq]
    exact hEnEm
  have hxzMem : xz ∈ integersTA :=
    funcFoundational_value_mem intMulGraph_isFunc hMulX
  have hyzMem : yz ∈ integersTA :=
    funcFoundational_value_mem intMulGraph_isFunc hMulY
  have hekMem : ek ∈ integersTA :=
    funcFoundational_value_mem intEmbedGraph_isFunc hEmbedK
  have hInput :
      ZFSet.pair xz ek ∈
        cartesianProductFoundational integersTA integersTA :=
    mem_cartesianProductFoundational.mpr ⟨hxzMem, hekMem⟩
  rcases intAddGraph_isFunc.2 (ZFSet.pair xz ek) hInput with
    ⟨s, hs, _hsUnique⟩
  have hSum : IntAdd xz ek s := hs.2
  have hDistrib : yz = s :=
    intAdd_mul_right hx hEnMem hz
      hAddXY hMulY hMulX hEnZ hSum
  refine ⟨hxzMem, hyzMem, k, ek, hk, hEmbedK, ?_⟩
  rw [hDistrib]
  exact hSum

theorem TA_PRO_00049_order_compatibility :
    (∀ x y z xz yz : ZFSet,
      x ∈ integersTA → y ∈ integersTA → z ∈ integersTA →
      IntLE x y → IntAdd x z xz → IntAdd y z yz →
      IntLE xz yz) ∧
    (∀ x y z xz yz : ZFSet,
      x ∈ integersTA → y ∈ integersTA → z ∈ integersTA →
      IntLE x y → IntLE intZero z →
      IntMul x z xz → IntMul y z yz →
      IntLE xz yz) := by
  exact ⟨fun _ _ _ _ _ => intLE_add_compat,
    fun _ _ _ _ _ => intLE_mul_nonnegative_compat⟩

/-! ## TA-PRO-00050 — el embedding preserva y refleja orden -/

theorem intEmbed_order_nat_iff (M N : Nat) :
    M ≤ N ↔
    IntLE
      (intClass (ZFSet.pair (natEncode M) (natEncode 0)))
      (intClass (ZFSet.pair (natEncode N) (natEncode 0))) := by
  simpa using
    (TA_PRO_00048_intLE_natEncode_classes_iff M 0 N 0).symm

theorem TA_PRO_00050_embedding_order_iff
    {m n em en : ZFSet}
    (hm : m ∈ omegaTA)
    (hn : n ∈ omegaTA)
    (hem : ZFSet.pair m em ∈ intEmbedGraph)
    (hen : ZFSet.pair n en ∈ intEmbedGraph) :
    NatLETA m n ↔ IntLE em en := by
  rcases exists_natEncode_eq_of_mem hm with ⟨M, rfl⟩
  rcases exists_natEncode_eq_of_mem hn with ⟨N, rfl⟩
  have hemEq := intEmbedGraph_natEncode_value_iff.mp hem
  have henEq := intEmbedGraph_natEncode_value_iff.mp hen
  rw [hemEq, henEq]
  constructor
  · intro h
    exact (intEmbed_order_nat_iff M N).mp
      ((NatLETA_natEncode_iff M N).mp h)
  · intro h
    exact (NatLETA_natEncode_iff M N).mpr
      ((intEmbed_order_nat_iff M N).mpr h)

end TratadoAnalisis.Integers.Order
