import TratadoAnalisis.Rationals.OrderedFieldCompatibility
import TratadoAnalisis.Foundations.FunctionTriple

namespace TratadoAnalisis.Rationals.NatEmbedding
universe u
open TratadoAnalisis.Naturals.Foundational
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Naturals.ArithmeticBridge
open TratadoAnalisis.Integers.Construction
open TratadoAnalisis.Integers.Operations
open TratadoAnalisis.Integers.Multiplication
open TratadoAnalisis.Integers.Algebra
open TratadoAnalisis.Integers.Domain
open TratadoAnalisis.Integers.Order
open TratadoAnalisis.Rationals.IntegerPrep
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.OrderedFieldCompatibility
open TratadoAnalisis.Foundations.FunctionTriple

/-- Grafo de la composición N → Z → Q, por Separación. -/
def natEmbeddingGraph : ZFSet.{u} :=
  ZFSet.sep (fun p => ∃ n q : ZFSet.{u},
    p = ZFSet.pair n q ∧ ∃ z : ZFSet.{u},
      ZFSet.pair n z ∈ intEmbedGraph ∧ ZFSet.pair z q ∈ ratEmbedGraph)
    (cartesianProductFoundational omegaTA rationalsTA)

/-- TA-DEF-00063: pertenencia al grafo compuesto. -/
theorem TA_DEF_00063_mem_natEmbeddingGraph_iff {n q : ZFSet.{u}} :
    ZFSet.pair n q ∈ natEmbeddingGraph ↔
      n ∈ omegaTA ∧ q ∈ rationalsTA ∧
      ∃ z : ZFSet.{u}, ZFSet.pair n z ∈ intEmbedGraph ∧
        ZFSet.pair z q ∈ ratEmbedGraph := by
  constructor
  · intro h
    rcases ZFSet.mem_sep.mp h with ⟨hp, n', q', he, hz⟩
    rcases ZFSet.pair_injective he with ⟨rfl, rfl⟩
    exact ⟨(mem_cartesianProductFoundational.mp hp).1,
      (mem_cartesianProductFoundational.mp hp).2, hz⟩
  · rintro ⟨hn, hq, hz⟩
    exact ZFSet.mem_sep.mpr
      ⟨mem_cartesianProductFoundational.mpr ⟨hn, hq⟩, n, q, rfl, hz⟩

theorem TA_DEF_00063_natEmbeddingGraph_isFunc :
    IsFuncFoundational (omegaTA : ZFSet.{u}) rationalsTA natEmbeddingGraph := by
  constructor
  · intro p hp
    rcases (ZFSet.mem_sep.mp hp).2 with ⟨n, q, he, _⟩
    rw [he] at hp
    have h := TA_DEF_00063_mem_natEmbeddingGraph_iff.mp hp
    exact ⟨n, h.1, q, h.2.1, he⟩
  · intro n hn
    rcases intEmbedGraph_isFunc.2 n hn with ⟨z, ⟨hz, hi⟩, _⟩
    rcases ratEmbedGraph_isFunc.2 z hz with ⟨q, ⟨hq, hj⟩, _⟩
    refine ⟨q, ⟨hq, TA_DEF_00063_mem_natEmbeddingGraph_iff.mpr
      ⟨hn, hq, z, hi, hj⟩⟩, ?_⟩
    intro q' hq'
    rcases (TA_DEF_00063_mem_natEmbeddingGraph_iff.mp hq'.2).2.2 with ⟨z', hi', hj'⟩
    have hez := funcFoundational_pair_value_unique intEmbedGraph_isFunc hn hi' hi
    rw [hez] at hj'
    exact funcFoundational_pair_value_unique ratEmbedGraph_isFunc hz hj' hj

/-- El objeto función ν = ⟨omegaTA, rationalsTA, grafo compuesto⟩. -/
def natEmbeddingFunction : ZFSet.{u} :=
  functionTriple omegaTA rationalsTA natEmbeddingGraph

theorem TA_DEF_00063_natEmbeddingFunction_isTriple :
    IsFunctionTriple (omegaTA : ZFSet.{u}) rationalsTA natEmbeddingFunction :=
  TA_DEF_00018_functionTriple_iff.mpr TA_DEF_00063_natEmbeddingGraph_isFunc

/-- Fórmula local del valor; no es una selección global de representantes. -/
def natRational (n : ZFSet.{u}) : ZFSet.{u} :=
  ratClass (ZFSet.pair (intClass (ZFSet.pair n ∅)) intOne)

theorem intEmbedding_canonical {n : ZFSet.{u}} (hn : n ∈ omegaTA) :
    ZFSet.pair n (intClass (ZFSet.pair n ∅)) ∈ intEmbedGraph := by
  have hz := omegaTA_isInductive.1
  have hi := intClass_mem_integersTA (mem_intDomain_iff.mpr ⟨n, ∅, hn, hz, rfl⟩)
  exact mem_intEmbedGraph.mpr ⟨hn, hi, hn, rfl⟩

theorem natRational_graph {n : ZFSet.{u}} (hn : n ∈ omegaTA) :
    ZFSet.pair n (natRational n) ∈ natEmbeddingGraph := by
  have hi := intEmbedding_canonical hn
  have hz := funcFoundational_value_mem intEmbedGraph_isFunc hi
  have hj := ratEmbedGraph_value hz
  exact TA_DEF_00063_mem_natEmbeddingGraph_iff.mpr
    ⟨hn, funcFoundational_value_mem ratEmbedGraph_isFunc hj, _, hi, hj⟩

theorem natRational_mem {n : ZFSet.{u}} (hn : n ∈ omegaTA) :
    natRational n ∈ rationalsTA :=
  funcFoundational_value_mem TA_DEF_00063_natEmbeddingGraph_isFunc (natRational_graph hn)

theorem natRational_value_iff {n q : ZFSet.{u}} (hn : n ∈ omegaTA) :
    ZFSet.pair n q ∈ natEmbeddingGraph ↔ q = natRational n := by
  constructor
  · intro h
    exact funcFoundational_pair_value_unique TA_DEF_00063_natEmbeddingGraph_isFunc
      hn h (natRational_graph hn)
  · rintro rfl
    exact natRational_graph hn

theorem TA_COR_00008_natRational_injective {m n : ZFSet.{u}}
    (hm : m ∈ omegaTA) (hn : n ∈ omegaTA)
    (he : natRational m = natRational n) : m = n := by
  have hi := intEmbedding_canonical hm
  have hj := intEmbedding_canonical hn
  have hzi := funcFoundational_value_mem intEmbedGraph_isFunc hi
  have hzj := funcFoundational_value_mem intEmbedGraph_isFunc hj
  have hratm := ratEmbedGraph_value hzi
  have hratn := ratEmbedGraph_value hzj
  change ZFSet.pair _ (natRational m) ∈ ratEmbedGraph at hratm
  change ZFSet.pair _ (natRational n) ∈ ratEmbedGraph at hratn
  rw [← he] at hratn
  exact intEmbedGraph_injective hm hn hi hj (ratEmbedGraph_injective hratm hratn)

theorem TA_COR_00008_natRational_zero :
    natRational (∅ : ZFSet.{u}) = ratZero := rfl

theorem TA_COR_00008_natRational_one :
    natRational (succ (∅ : ZFSet.{u})) = ratOne := rfl

theorem natRational_add_nat (M N : Nat) :
    RatAdd (natRational (natEncode M : ZFSet.{u}))
      (natRational (natEncode N)) (natRational (natEncode (M + N))) := by
  exact ratEmbedGraph_add
    (ratEmbedGraph_value (intPositiveForm_mem_integersTA M))
    (ratEmbedGraph_value (intPositiveForm_mem_integersTA N))
    (ratEmbedGraph_value (intPositiveForm_mem_integersTA (M + N)))
    (intEmbedGraph_add_nat.{u, u, u, u} M N).2.2.2

theorem natRational_mul_nat (M N : Nat) :
    RatMul (natRational (natEncode M : ZFSet.{u}))
      (natRational (natEncode N)) (natRational (natEncode (M * N))) := by
  exact ratEmbedGraph_mul
    (ratEmbedGraph_value (intPositiveForm_mem_integersTA M))
    (ratEmbedGraph_value (intPositiveForm_mem_integersTA N))
    (ratEmbedGraph_value (intPositiveForm_mem_integersTA (M * N)))
    (intEmbedGraph_mul_nat.{u, u, u, u} M N).2.2.2

theorem TA_COR_00008_natRational_add {m n s : ZFSet.{u}}
    (hm : m ∈ omegaTA) (hn : n ∈ omegaTA)
    (hs : ZFSet.pair (ZFSet.pair m n) s ∈ natAddGraph) :
    RatAdd (natRational m) (natRational n) (natRational s) := by
  rcases exists_natEncode_eq_of_mem hm with ⟨M, rfl⟩
  rcases exists_natEncode_eq_of_mem hn with ⟨N, rfl⟩
  have he := natAddGraph_natEncode_value_iff.mp hs
  rw [he]
  exact natRational_add_nat M N

theorem TA_COR_00008_natRational_mul {m n p : ZFSet.{u}}
    (hm : m ∈ omegaTA) (hn : n ∈ omegaTA)
    (hp : ZFSet.pair (ZFSet.pair m n) p ∈ natMulGraph) :
    RatMul (natRational m) (natRational n) (natRational p) := by
  rcases exists_natEncode_eq_of_mem hm with ⟨M, rfl⟩
  rcases exists_natEncode_eq_of_mem hn with ⟨N, rfl⟩
  have he := natMulGraph_natEncode_value_iff.mp hp
  rw [he]
  exact natRational_mul_nat M N

theorem TA_COR_00008_natRational_succ {n : ZFSet.{u}} (hn : n ∈ omegaTA) :
    RatAdd (natRational n) ratOne (natRational (succ n)) := by
  rcases exists_natEncode_eq_of_mem hn with ⟨N, rfl⟩
  exact natRational_add_nat N 1

theorem TA_COR_00008_natRational_order_iff {m n : ZFSet.{u}}
    (hm : m ∈ omegaTA) (hn : n ∈ omegaTA) :
    NatLETA m n ↔ RatLE (natRational m) (natRational n) := by
  have hi := intEmbedding_canonical hm
  have hj := intEmbedding_canonical hn
  have hz := funcFoundational_value_mem intEmbedGraph_isFunc hi
  have hw := funcFoundational_value_mem intEmbedGraph_isFunc hj
  exact (TA_PRO_00050_embedding_order_iff hm hn hi hj).trans
    (TA_PRO_00066_ratEmbed_order_iff hz hw (ratEmbedGraph_value hz) (ratEmbedGraph_value hw))

theorem TA_COR_00008_natRational_strict_order_iff {m n : ZFSet.{u}}
    (hm : m ∈ omegaTA) (hn : n ∈ omegaTA) :
    (NatLETA m n ∧ m ≠ n) ↔ RatLT (natRational m) (natRational n) := by
  constructor
  · rintro ⟨hle, hne⟩
    exact ⟨(TA_COR_00008_natRational_order_iff hm hn).mp hle,
      fun he => hne (TA_COR_00008_natRational_injective hm hn he)⟩
  · rintro ⟨hle, hne⟩
    exact ⟨(TA_COR_00008_natRational_order_iff hm hn).mpr hle,
      fun he => hne (congrArg natRational he)⟩

end TratadoAnalisis.Rationals.NatEmbedding
