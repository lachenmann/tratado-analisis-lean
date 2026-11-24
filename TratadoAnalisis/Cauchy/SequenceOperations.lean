import TratadoAnalisis.Cauchy.RationalSequences
import TratadoAnalisis.Foundations.RelationalFunctions
import TratadoAnalisis.Rationals.Signs

/-!
# TA-LEAN-0011 A2 — Operaciones puntuales y constantes (§8.1.3–8.1.5)

Las sucesiones son triples conjuntistas. Sus grafos y los grafos de
las operaciones sobre ellas existen por separación. No se invoca
ninguna completitud, ni se selecciona una familia de valores.
-/

namespace TratadoAnalisis.Cauchy.SequenceOperations

universe u

open TratadoAnalisis.Naturals.Foundational
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Foundations.RelationalFunctions
open TratadoAnalisis.Foundations.FunctionSpace
open TratadoAnalisis.Cauchy.RationalSequences
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.Signs

def BinaryTerm (R : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (a b n z : ZFSet.{u}) : Prop :=
  ∃ x y : ZFSet.{u}, SequenceValue a n x ∧ SequenceValue b n y ∧ R x y z

def UnaryTerm (R : ZFSet.{u} → ZFSet.{u} → Prop)
    (a n z : ZFSet.{u}) : Prop :=
  ∃ x : ZFSet.{u}, SequenceValue a n x ∧ R x z

theorem binaryTerm_exists_unique
    {R : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop}
    (hR : ∀ x y : ZFSet.{u}, x ∈ rationalsTA → y ∈ rationalsTA →
      ∃! z : ZFSet.{u}, z ∈ rationalsTA ∧ R x y z)
    {a b n : ZFSet.{u}}
    (ha : a ∈ rationalSequences) (hb : b ∈ rationalSequences) (hn : n ∈ omegaTA) :
    ∃! z : ZFSet.{u}, z ∈ rationalsTA ∧ BinaryTerm R a b n z := by
  obtain ⟨x, ⟨hxQ, hx⟩, _⟩ := sequenceValue_exists_unique ha hn
  obtain ⟨y, ⟨hyQ, hy⟩, _⟩ := sequenceValue_exists_unique hb hn
  obtain ⟨z, hz, hu⟩ := hR x y hxQ hyQ
  refine ⟨z, ⟨hz.1, x, y, hx, hy, hz.2⟩, ?_⟩
  intro w hw
  obtain ⟨x', y', hx', hy', hR'⟩ := hw.2
  have ex := sequenceValue_unique ha hn hx' hx
  have ey := sequenceValue_unique hb hn hy' hy
  rw [ex, ey] at hR'
  exact hu w ⟨hw.1, hR'⟩

theorem unaryTerm_exists_unique
    {R : ZFSet.{u} → ZFSet.{u} → Prop}
    (hR : ∀ x : ZFSet.{u}, x ∈ rationalsTA →
      ∃! z : ZFSet.{u}, z ∈ rationalsTA ∧ R x z)
    {a n : ZFSet.{u}} (ha : a ∈ rationalSequences) (hn : n ∈ omegaTA) :
    ∃! z : ZFSet.{u}, z ∈ rationalsTA ∧ UnaryTerm R a n z := by
  obtain ⟨x, ⟨hxQ, hx⟩, _⟩ := sequenceValue_exists_unique ha hn
  obtain ⟨z, hz, hu⟩ := hR x hxQ
  refine ⟨z, ⟨hz.1, x, hx, hz.2⟩, ?_⟩
  intro w hw
  obtain ⟨x', hx', hR'⟩ := hw.2
  have ex := sequenceValue_unique ha hn hx' hx
  rw [ex] at hR'
  exact hu w ⟨hw.1, hR'⟩

def pointwiseBinary (R : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (a b : ZFSet.{u}) : ZFSet.{u} :=
  functionOfRelation omegaTA rationalsTA (BinaryTerm R a b)

def pointwiseUnary (R : ZFSet.{u} → ZFSet.{u} → Prop)
    (a : ZFSet.{u}) : ZFSet.{u} :=
  functionOfRelation omegaTA rationalsTA (UnaryTerm R a)

theorem pointwiseBinary_mem
    {R : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop}
    (hR : ∀ x y : ZFSet.{u}, x ∈ rationalsTA → y ∈ rationalsTA →
      ∃! z : ZFSet.{u}, z ∈ rationalsTA ∧ R x y z)
    {a b : ZFSet.{u}} (ha : a ∈ rationalSequences) (hb : b ∈ rationalSequences) :
    pointwiseBinary R a b ∈ rationalSequences :=
  functionOfRelation_mem (fun _ hn => binaryTerm_exists_unique hR ha hb hn)

theorem pointwiseUnary_mem
    {R : ZFSet.{u} → ZFSet.{u} → Prop}
    (hR : ∀ x : ZFSet.{u}, x ∈ rationalsTA →
      ∃! z : ZFSet.{u}, z ∈ rationalsTA ∧ R x z)
    {a : ZFSet.{u}} (ha : a ∈ rationalSequences) :
    pointwiseUnary R a ∈ rationalSequences :=
  functionOfRelation_mem (fun _ hn => unaryTerm_exists_unique hR ha hn)

/-- Evaluación puntual con los testigos de los dos términos ya suministrados. -/
theorem pointwiseBinary_value_iff
    {R : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop}
    {a b n x y z : ZFSet.{u}}
    (ha : a ∈ rationalSequences) (hb : b ∈ rationalSequences) (hn : n ∈ omegaTA)
    (hx : SequenceValue a n x) (hy : SequenceValue b n y) (hz : z ∈ rationalsTA) :
    SequenceValue (pointwiseBinary R a b) n z ↔ R x y z := by
  change FunctionValue omegaTA rationalsTA
    (functionOfRelation omegaTA rationalsTA (BinaryTerm R a b)) n z ↔ R x y z
  rw [functionOfRelation_value_iff]
  constructor
  · rintro ⟨_, _, x', y', hx', hy', hR⟩
    have ex := sequenceValue_unique ha hn hx' hx
    have ey := sequenceValue_unique hb hn hy' hy
    rw [ex, ey] at hR
    exact hR
  · intro hR
    exact ⟨hn, hz, x, y, hx, hy, hR⟩

theorem pointwiseUnary_value_iff
    {R : ZFSet.{u} → ZFSet.{u} → Prop}
    {a n x z : ZFSet.{u}} (ha : a ∈ rationalSequences) (hn : n ∈ omegaTA)
    (hx : SequenceValue a n x) (hz : z ∈ rationalsTA) :
    SequenceValue (pointwiseUnary R a) n z ↔ R x z := by
  change FunctionValue omegaTA rationalsTA
    (functionOfRelation omegaTA rationalsTA (UnaryTerm R a)) n z ↔ R x z
  rw [functionOfRelation_value_iff]
  constructor
  · rintro ⟨_, _, x', hx', hR⟩
    have ex := sequenceValue_unique ha hn hx' hx
    rw [ex] at hR
    exact hR
  · intro hR
    exact ⟨hn, hz, x, hx, hR⟩

theorem ratAdd_exists_unique (x y : ZFSet.{u})
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA) :
    ∃! z : ZFSet.{u}, z ∈ rationalsTA ∧ RatAdd x y z := by
  obtain ⟨z, hz, h⟩ := ratAdd_exists hx hy
  exact ⟨z, ⟨hz, h⟩, fun _ hw => RatAdd_unique hx hy hw.2 h⟩

theorem ratMul_exists_unique (x y : ZFSet.{u})
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA) :
    ∃! z : ZFSet.{u}, z ∈ rationalsTA ∧ RatMul x y z := by
  obtain ⟨z, hz, h⟩ := ratMul_exists hx hy
  exact ⟨z, ⟨hz, h⟩, fun _ hw => RatMul_unique hx hy hw.2 h⟩

theorem ratNeg_exists_unique (x : ZFSet.{u}) (hx : x ∈ rationalsTA) :
    ∃! z : ZFSet.{u}, z ∈ rationalsTA ∧ RatNeg x z := by
  obtain ⟨z, hz, h⟩ := ratNeg_exists hx
  exact ⟨z, ⟨hz, h⟩, fun _ hw => RatNeg_unique hx hw.2 h⟩

/-- TA-DEF-00106: suma puntual. -/
def seqAdd (a b : ZFSet.{u}) : ZFSet.{u} :=
  pointwiseBinary RatAdd a b

def seqNeg (a : ZFSet.{u}) : ZFSet.{u} :=
  pointwiseUnary RatNeg a

def seqMul (a b : ZFSet.{u}) : ZFSet.{u} :=
  pointwiseBinary RatMul a b

/-- La sustracción es la composición de suma y opuesto. -/
def seqSub (a b : ZFSet.{u}) : ZFSet.{u} :=
  seqAdd a (seqNeg b)

theorem seqAdd_mem {a b : ZFSet.{u}}
    (ha : a ∈ rationalSequences) (hb : b ∈ rationalSequences) :
    seqAdd a b ∈ rationalSequences :=
  pointwiseBinary_mem ratAdd_exists_unique ha hb

theorem seqNeg_mem {a : ZFSet.{u}} (ha : a ∈ rationalSequences) :
    seqNeg a ∈ rationalSequences :=
  pointwiseUnary_mem ratNeg_exists_unique ha

theorem seqMul_mem {a b : ZFSet.{u}}
    (ha : a ∈ rationalSequences) (hb : b ∈ rationalSequences) :
    seqMul a b ∈ rationalSequences :=
  pointwiseBinary_mem ratMul_exists_unique ha hb

theorem seqSub_mem {a b : ZFSet.{u}}
    (ha : a ∈ rationalSequences) (hb : b ∈ rationalSequences) :
    seqSub a b ∈ rationalSequences :=
  seqAdd_mem ha (seqNeg_mem hb)

theorem seqAdd_value_iff {a b n x y z : ZFSet.{u}}
    (ha : a ∈ rationalSequences) (hb : b ∈ rationalSequences) (hn : n ∈ omegaTA)
    (hx : SequenceValue a n x) (hy : SequenceValue b n y) (hz : z ∈ rationalsTA) :
    SequenceValue (seqAdd a b) n z ↔ RatAdd x y z :=
  pointwiseBinary_value_iff ha hb hn hx hy hz

theorem seqNeg_value_iff {a n x z : ZFSet.{u}}
    (ha : a ∈ rationalSequences) (hn : n ∈ omegaTA)
    (hx : SequenceValue a n x) (hz : z ∈ rationalsTA) :
    SequenceValue (seqNeg a) n z ↔ RatNeg x z :=
  pointwiseUnary_value_iff ha hn hx hz

theorem seqMul_value_iff {a b n x y z : ZFSet.{u}}
    (ha : a ∈ rationalSequences) (hb : b ∈ rationalSequences) (hn : n ∈ omegaTA)
    (hx : SequenceValue a n x) (hy : SequenceValue b n y) (hz : z ∈ rationalsTA) :
    SequenceValue (seqMul a b) n z ↔ RatMul x y z :=
  pointwiseBinary_value_iff ha hb hn hx hy hz

theorem seqSub_value_iff {a b n x y z : ZFSet.{u}}
    (ha : a ∈ rationalSequences) (hb : b ∈ rationalSequences) (hn : n ∈ omegaTA)
    (hx : SequenceValue a n x) (hy : SequenceValue b n y) (hz : z ∈ rationalsTA) :
    SequenceValue (seqSub a b) n z ↔ RatSub x y z := by
  change SequenceValue (seqAdd a (seqNeg b)) n z ↔ RatSub x y z
  constructor
  · intro h
    obtain ⟨ny, ⟨hnyQ, hny⟩, _⟩ := sequenceValue_exists_unique (seqNeg_mem hb) hn
    exact ⟨ny, (seqNeg_value_iff hb hn hy hnyQ).mp hny,
      (seqAdd_value_iff ha (seqNeg_mem hb) hn hx hny hz).mp h⟩
  · rintro ⟨ny, hneg, hadd⟩
    have hnyQ := funcFoundational_value_mem ratNegGraph_isFunc hneg
    have hny := (seqNeg_value_iff hb hn hy hnyQ).mpr hneg
    exact (seqAdd_value_iff ha (seqNeg_mem hb) hn hx hny hz).mpr hadd

/-- Los grafos globales de las operaciones sobre Q^N. -/
def seqAddGraph : ZFSet.{u} :=
  binaryMapGraph rationalSequences rationalSequences seqAdd

def seqNegGraph : ZFSet.{u} :=
  mapGraph rationalSequences rationalSequences seqNeg

def seqMulGraph : ZFSet.{u} :=
  binaryMapGraph rationalSequences rationalSequences seqMul

def seqSubGraph : ZFSet.{u} :=
  binaryMapGraph rationalSequences rationalSequences seqSub

theorem seqAddGraph_isFunc :
    IsFuncFoundational (cartesianProductFoundational rationalSequences rationalSequences)
      rationalSequences (seqAddGraph : ZFSet.{u}) :=
  binaryMapGraph_isFunc (fun _ _ ha hb => seqAdd_mem ha hb)

theorem seqNegGraph_isFunc :
    IsFuncFoundational rationalSequences rationalSequences (seqNegGraph : ZFSet.{u}) :=
  mapGraph_isFunc (fun _ ha => seqNeg_mem ha)

theorem seqMulGraph_isFunc :
    IsFuncFoundational (cartesianProductFoundational rationalSequences rationalSequences)
      rationalSequences (seqMulGraph : ZFSet.{u}) :=
  binaryMapGraph_isFunc (fun _ _ ha hb => seqMul_mem ha hb)

theorem seqSubGraph_isFunc :
    IsFuncFoundational (cartesianProductFoundational rationalSequences rationalSequences)
      rationalSequences (seqSubGraph : ZFSet.{u}) :=
  binaryMapGraph_isFunc (fun _ _ ha hb => seqSub_mem ha hb)

/-- Los grafos globales representan las asignaciones definidas, no otras. -/
theorem mem_seqAddGraph_iff {a b c : ZFSet.{u}} :
    ZFSet.pair (ZFSet.pair a b) c ∈ seqAddGraph ↔
      a ∈ rationalSequences ∧ b ∈ rationalSequences ∧ c ∈ rationalSequences ∧ c = seqAdd a b :=
  mem_binaryMapGraph_iff

theorem mem_seqNegGraph_iff {a c : ZFSet.{u}} :
    ZFSet.pair a c ∈ seqNegGraph ↔
      a ∈ rationalSequences ∧ c ∈ rationalSequences ∧ c = seqNeg a :=
  mem_mapGraph_iff

theorem mem_seqMulGraph_iff {a b c : ZFSet.{u}} :
    ZFSet.pair (ZFSet.pair a b) c ∈ seqMulGraph ↔
      a ∈ rationalSequences ∧ b ∈ rationalSequences ∧ c ∈ rationalSequences ∧ c = seqMul a b :=
  mem_binaryMapGraph_iff

theorem mem_seqSubGraph_iff {a b c : ZFSet.{u}} :
    ZFSet.pair (ZFSet.pair a b) c ∈ seqSubGraph ↔
      a ∈ rationalSequences ∧ b ∈ rationalSequences ∧ c ∈ rationalSequences ∧ c = seqSub a b :=
  mem_binaryMapGraph_iff

/-- TA-DEF-00107: la sucesión constante es un triple de función. -/
def constantSequence (c : ZFSet.{u}) : ZFSet.{u} :=
  functionOfRelation omegaTA rationalsTA (fun _ r => r = c)

theorem constantSequence_mem {c : ZFSet.{u}} (hc : c ∈ rationalsTA) :
    constantSequence c ∈ rationalSequences := by
  apply functionOfRelation_mem
  intro _ _
  exact ⟨c, ⟨hc, rfl⟩, fun _ h => h.2⟩

theorem constantSequence_value_iff {c n r : ZFSet.{u}}
    (hc : c ∈ rationalsTA) (hn : n ∈ omegaTA) :
    SequenceValue (constantSequence c) n r ↔ r = c := by
  change FunctionValue omegaTA rationalsTA
    (functionOfRelation omegaTA rationalsTA (fun _ r => r = c)) n r ↔ r = c
  rw [functionOfRelation_value_iff]
  constructor
  · exact fun h => h.2.2
  · intro e
    subst r
    exact ⟨hn, hc, rfl⟩

/-- El grafo de kappa: Q → Q^N. -/
def constantSequenceGraph : ZFSet.{u} :=
  mapGraph rationalsTA rationalSequences constantSequence

theorem constantSequenceGraph_isFunc :
    IsFuncFoundational rationalsTA rationalSequences (constantSequenceGraph : ZFSet.{u}) :=
  mapGraph_isFunc (fun _ hc => constantSequence_mem hc)

theorem mem_constantSequenceGraph_iff {c a : ZFSet.{u}} :
    ZFSet.pair c a ∈ constantSequenceGraph ↔
      c ∈ rationalsTA ∧ a ∈ rationalSequences ∧ a = constantSequence c :=
  mem_mapGraph_iff

/-- Compatibilidad general de constantes con una operación binaria puntual. -/
theorem constant_pointwiseBinary
    {R : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop}
    (hR : ∀ x y : ZFSet.{u}, x ∈ rationalsTA → y ∈ rationalsTA →
      ∃! z : ZFSet.{u}, z ∈ rationalsTA ∧ R x y z)
    {c d e : ZFSet.{u}} (hc : c ∈ rationalsTA) (hd : d ∈ rationalsTA)
    (he : e ∈ rationalsTA) (hop : R c d e) :
    pointwiseBinary R (constantSequence c) (constantSequence d) = constantSequence e := by
  have ha := constantSequence_mem hc
  have hb := constantSequence_mem hd
  have hleft := pointwiseBinary_mem hR ha hb
  apply (TA_PRO_00107_sequence_eq_iff_values hleft (constantSequence_mem he)).mpr
  intro n hn r s hr hs
  have hx := (constantSequence_value_iff hc hn).mpr rfl
  have hy := (constantSequence_value_iff hd hn).mpr rfl
  have hval := (pointwiseBinary_value_iff ha hb hn hx hy he).mpr hop
  exact (sequenceValue_unique hleft hn hr hval).trans
    ((constantSequence_value_iff he hn).mp hs).symm

theorem constant_pointwiseUnary
    {R : ZFSet.{u} → ZFSet.{u} → Prop}
    (hR : ∀ x : ZFSet.{u}, x ∈ rationalsTA →
      ∃! z : ZFSet.{u}, z ∈ rationalsTA ∧ R x z)
    {c e : ZFSet.{u}} (hc : c ∈ rationalsTA) (he : e ∈ rationalsTA) (hop : R c e) :
    pointwiseUnary R (constantSequence c) = constantSequence e := by
  have ha := constantSequence_mem hc
  have hleft := pointwiseUnary_mem hR ha
  apply (TA_PRO_00107_sequence_eq_iff_values hleft (constantSequence_mem he)).mpr
  intro n hn r s hr hs
  have hx := (constantSequence_value_iff hc hn).mpr rfl
  have hval := (pointwiseUnary_value_iff ha hn hx he).mpr hop
  exact (sequenceValue_unique hleft hn hr hval).trans
    ((constantSequence_value_iff he hn).mp hs).symm

/-- TA-PRO-00108: las cuatro identidades de constantes. -/
theorem constant_add {c d e : ZFSet.{u}}
    (hc : c ∈ rationalsTA) (hd : d ∈ rationalsTA)
    (he : e ∈ rationalsTA) (h : RatAdd c d e) :
    seqAdd (constantSequence c) (constantSequence d) = constantSequence e :=
  constant_pointwiseBinary ratAdd_exists_unique hc hd he h

theorem constant_neg {c e : ZFSet.{u}}
    (hc : c ∈ rationalsTA) (he : e ∈ rationalsTA) (h : RatNeg c e) :
    seqNeg (constantSequence c) = constantSequence e :=
  constant_pointwiseUnary ratNeg_exists_unique hc he h

theorem constant_mul {c d e : ZFSet.{u}}
    (hc : c ∈ rationalsTA) (hd : d ∈ rationalsTA)
    (he : e ∈ rationalsTA) (h : RatMul c d e) :
    seqMul (constantSequence c) (constantSequence d) = constantSequence e :=
  constant_pointwiseBinary ratMul_exists_unique hc hd he h

theorem constant_sub {c d e : ZFSet.{u}}
    (hc : c ∈ rationalsTA) (hd : d ∈ rationalsTA)
    (he : e ∈ rationalsTA) (h : RatSub c d e) :
    seqSub (constantSequence c) (constantSequence d) = constantSequence e := by
  obtain ⟨nd, hneg, hadd⟩ := h
  have hnd := funcFoundational_value_mem ratNegGraph_isFunc hneg
  change seqAdd (constantSequence c) (seqNeg (constantSequence d)) = constantSequence e
  rw [constant_neg hd hnd hneg]
  exact constant_add hc hnd he hadd

theorem TA_PRO_00108_constant_operations {c d : ZFSet.{u}}
    (hc : c ∈ rationalsTA) (hd : d ∈ rationalsTA) :
    (∀ e : ZFSet.{u}, e ∈ rationalsTA → RatAdd c d e →
      seqAdd (constantSequence c) (constantSequence d) = constantSequence e) ∧
    (∀ e : ZFSet.{u}, e ∈ rationalsTA → RatNeg c e →
      seqNeg (constantSequence c) = constantSequence e) ∧
    (∀ e : ZFSet.{u}, e ∈ rationalsTA → RatSub c d e →
      seqSub (constantSequence c) (constantSequence d) = constantSequence e) ∧
    (∀ e : ZFSet.{u}, e ∈ rationalsTA → RatMul c d e →
      seqMul (constantSequence c) (constantSequence d) = constantSequence e) :=
  ⟨fun _ he h => constant_add hc hd he h, fun _ he h => constant_neg hc he h,
    fun _ he h => constant_sub hc hd he h, fun _ he h => constant_mul hc hd he h⟩

end TratadoAnalisis.Cauchy.SequenceOperations
