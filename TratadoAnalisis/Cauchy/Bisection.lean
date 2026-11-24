import TratadoAnalisis.Cauchy.RationalConvergence
import TratadoAnalisis.Rationals.Density

/-!
TA-LEAN-0011 A8a — TA-DEF-00114 y TA-PRO-00115.
Bisección racional total sobre Q × Q y recursión conjuntista certificada.
La tricotomía proposicional basta para determinar una rama unívoca.
No se afirma aquí un algoritmo de extracción de códigos desde ZFSet.
-/
namespace TratadoAnalisis.Cauchy.Bisection
universe u
open TratadoAnalisis.Naturals.Foundational
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Foundations.FunctionSpace
open TratadoAnalisis.Foundations.FunctionTriple
open TratadoAnalisis.Foundations.RelationalFunctions
open TratadoAnalisis.Cauchy.RationalSequences
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.Field
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.Trichotomy
open TratadoAnalisis.Rationals.Division
open TratadoAnalisis.Rationals.IrrationalitySqrtTwo

abbrev BisectSpace : ZFSet.{u} := cartesianProductFoundational rationalsTA rationalsTA

def Midpoint (x y m : ZFSet.{u}) : Prop :=
  ∃ s : ZFSet.{u}, RatAdd x y s ∧ RatDiv s ratTwoTA m

theorem two_nonzero_mem : (ratTwoTA : ZFSet.{u}) ∈ ratNonzeroTA :=
  mem_ratNonzeroTA_iff.mpr ⟨ratTwoTA_mem_rationalsTA,ratTwoTA_ne_zero⟩

theorem midpoint_exists {x y : ZFSet.{u}} (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA) :
    ∃ m : ZFSet.{u}, m ∈ rationalsTA ∧ Midpoint x y m := by
  obtain ⟨s,hsQ,hs⟩ := ratAdd_exists hx hy
  obtain ⟨m,hmQ,hm⟩ := ratDiv_exists hsQ two_nonzero_mem
  exact ⟨m,hmQ,s,hs,hm⟩

theorem midpoint_unique {x y m n : ZFSet.{u}} (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (hm : Midpoint x y m) (hn : Midpoint x y n) : m = n := by
  obtain ⟨s,hs,hd⟩ := hm
  obtain ⟨t,ht,he⟩ := hn
  have est := RatAdd_unique hx hy hs ht
  subst t
  exact RatDiv_unique (funcFoundational_value_mem ratAddGraph_isFunc hs) two_nonzero_mem hd he

theorem midpoint_mem {x y m : ZFSet.{u}} (hm : Midpoint x y m) : m ∈ rationalsTA := by
  obtain ⟨_,_,hd⟩ := hm
  obtain ⟨_,_,hmul⟩ := hd
  exact funcFoundational_value_mem ratMulGraph_isFunc hmul

/-- TA-DEF-00114: las dos ramas literales del operador sobre pares. -/
def BisectStep (p v : ZFSet.{u}) : Prop :=
  ∃ x y m s : ZFSet.{u}, x ∈ rationalsTA ∧ y ∈ rationalsTA ∧
    p = ZFSet.pair x y ∧ Midpoint x y m ∧ RatMul m m s ∧
    ((RatLT s ratTwoTA ∧ v = ZFSet.pair m y) ∨
      (¬ RatLT s ratTwoTA ∧ v = ZFSet.pair x m))

theorem bisectStep_unique {p v w : ZFSet.{u}} (hv : BisectStep p v) (hw : BisectStep p w) : v = w := by
  obtain ⟨x,y,m,s,hx,hy,hp,hm,hs,hv⟩ := hv
  obtain ⟨x',y',m',s',_,_,hp',hm',hs',hw⟩ := hw
  obtain ⟨ex,ey⟩ := ZFSet.pair_injective (hp.symm.trans hp')
  subst x'
  subst y'
  have em := midpoint_unique hx hy hm hm'
  subst m'
  have es := RatMul_unique (midpoint_mem hm) (midpoint_mem hm) hs hs'
  subst s'
  rcases hv with ⟨hlt,hev⟩ | ⟨hnlt,hev⟩
  · rcases hw with ⟨_,hew⟩ | ⟨hn,hew⟩
    · exact hev.trans hew.symm
    · exact (hn hlt).elim
  · rcases hw with ⟨hlt,hew⟩ | ⟨_,hew⟩
    · exact (hnlt hlt).elim
    · exact hev.trans hew.symm

theorem bisectStep_exists_unique {p : ZFSet.{u}} (hp : p ∈ BisectSpace) :
    ∃! v : ZFSet.{u}, v ∈ BisectSpace ∧ BisectStep p v := by
  obtain ⟨x,hx,y,hy,rfl⟩ := (ZFSet.mem_sep.mp hp).2
  obtain ⟨m,hmQ,hm⟩ := midpoint_exists hx hy
  obtain ⟨s,hsQ,hs⟩ := ratMul_exists hmQ hmQ
  have hcases : RatLT s ratTwoTA ∨ ¬ RatLT s ratTwoTA := by
    rcases TA_PRO_00172_rational_trichotomy hsQ ratTwoTA_mem_rationalsTA with h | e | h
    · exact Or.inl h
    · exact Or.inr (fun h => h.2 e)
    · exact Or.inr (fun h' => h'.2 (ratLE_antisymm hsQ ratTwoTA_mem_rationalsTA h'.1 h.1))
  rcases hcases with h | h
  · have hv : BisectStep (ZFSet.pair x y) (ZFSet.pair m y) := ⟨x,y,m,s,hx,hy,rfl,hm,hs,Or.inl ⟨h,rfl⟩⟩
    exact ⟨_,⟨mem_cartesianProductFoundational.mpr ⟨hmQ,hy⟩,hv⟩,fun _ h => bisectStep_unique h.2 hv⟩
  · have hv : BisectStep (ZFSet.pair x y) (ZFSet.pair x m) := ⟨x,y,m,s,hx,hy,rfl,hm,hs,Or.inr ⟨h,rfl⟩⟩
    exact ⟨_,⟨mem_cartesianProductFoundational.mpr ⟨hx,hmQ⟩,hv⟩,fun _ h => bisectStep_unique h.2 hv⟩

def bisectStepGraph : ZFSet.{u} := relationGraph BisectSpace BisectSpace BisectStep

theorem bisectStepGraph_isFunc : IsFuncFoundational BisectSpace BisectSpace (bisectStepGraph : ZFSet.{u}) :=
  relationGraph_isFunc (fun _ hp => bisectStep_exists_unique hp)

def bisectFunction : ZFSet.{u} := functionTriple BisectSpace BisectSpace bisectStepGraph

theorem TA_DEF_00114_bisectFunction_isTriple : IsFunctionTriple BisectSpace BisectSpace (bisectFunction : ZFSet.{u}) :=
  TA_DEF_00018_functionTriple_iff.mpr bisectStepGraph_isFunc

theorem mem_bisectStepGraph_iff {p v : ZFSet.{u}} :
    ZFSet.pair p v ∈ bisectStepGraph ↔ p ∈ BisectSpace ∧ v ∈ BisectSpace ∧ BisectStep p v :=
  mem_relationGraph_iff

def bisectInitial : ZFSet.{u} := ZFSet.pair ratOne ratTwoTA

theorem bisectInitial_mem : (bisectInitial : ZFSet.{u}) ∈ BisectSpace :=
  mem_cartesianProductFoundational.mpr ⟨ratOne_mem_rationalsTA,ratTwoTA_mem_rationalsTA⟩

def bisectStatesGraph : ZFSet.{u} := globalRecursionGraph BisectSpace bisectInitial bisectStepGraph

theorem bisectStatesGraph_isFunc : IsFuncFoundational omegaTA BisectSpace (bisectStatesGraph : ZFSet.{u}) :=
  globalRecursionGraph_isFunc bisectInitial_mem bisectStepGraph_isFunc

def bisectStates : ZFSet.{u} := functionTriple omegaTA BisectSpace bisectStatesGraph

theorem bisectStates_isTriple : IsFunctionTriple omegaTA BisectSpace (bisectStates : ZFSet.{u}) :=
  TA_DEF_00018_functionTriple_iff.mpr bisectStatesGraph_isFunc

theorem bisectStates_unique {f : ZFSet.{u}} (hf : IsFunctionTriple omegaTA BisectSpace f)
    (h0 : FunctionValue omegaTA BisectSpace f ∅ bisectInitial)
    (hstep : ∀ n x y : ZFSet.{u}, n ∈ omegaTA → FunctionValue omegaTA BisectSpace f n x →
      ZFSet.pair x y ∈ bisectStepGraph → FunctionValue omegaTA BisectSpace f (succ n) y) :
    f = bisectStates := by
  obtain ⟨G,hG,hfunc⟩ := hf
  have hzero := (functionValue_iff_graph hG).mp h0
  have heq := globalRecursionGraph_unique bisectInitial_mem bisectStepGraph_isFunc hfunc hzero
    (fun n x y hn hx hy => (functionValue_iff_graph hG).mp (hstep n x y hn ((functionValue_iff_graph hG).mpr hx) hy))
  exact hG.trans (congrArg (functionTriple omegaTA BisectSpace) heq)

/-- Valor del estado recursivo en un índice, con coordenadas explícitas. -/
def BisectAt (n x y : ZFSet.{u}) : Prop := ZFSet.pair n (ZFSet.pair x y) ∈ bisectStatesGraph

theorem bisectAt_mem {n x y : ZFSet.{u}} (h : BisectAt n x y) : x ∈ rationalsTA ∧ y ∈ rationalsTA :=
  mem_cartesianProductFoundational.mp (funcFoundational_value_mem bisectStatesGraph_isFunc h)

theorem bisectAt_exists {n : ZFSet.{u}} (hn : n ∈ omegaTA) : ∃ x y : ZFSet.{u}, BisectAt n x y := by
  obtain ⟨p,⟨hp,hpval⟩,_⟩ := bisectStatesGraph_isFunc.2 n hn
  obtain ⟨x,_,y,_,rfl⟩ := (ZFSet.mem_sep.mp hp).2
  exact ⟨x,y,hpval⟩

theorem bisectAt_unique {n x y a b : ZFSet.{u}} (hn : n ∈ omegaTA)
    (h : BisectAt n x y) (h' : BisectAt n a b) : x = a ∧ y = b :=
  ZFSet.pair_injective (funcFoundational_pair_value_unique bisectStatesGraph_isFunc hn h h')

theorem bisectAt_zero : BisectAt (∅ : ZFSet.{u}) ratOne ratTwoTA :=
  globalRecursionGraph_zero bisectInitial_mem

theorem bisectAt_succ_step {n x y a b : ZFSet.{u}} (hn : n ∈ omegaTA)
    (h : BisectAt n x y) (h' : BisectAt (succ n) a b) :
    BisectStep (ZFSet.pair x y) (ZFSet.pair a b) := by
  have hp := mem_cartesianProductFoundational.mpr (bisectAt_mem h)
  obtain ⟨v,⟨hv,hstep⟩,_⟩ := bisectStep_exists_unique hp
  have hg := mem_bisectStepGraph_iff.mpr ⟨hp,hv,hstep⟩
  have hr := globalRecursionGraph_succ bisectInitial_mem bisectStepGraph_isFunc hn h hg
  have e := funcFoundational_pair_value_unique bisectStatesGraph_isFunc (TA_PRO_00022_succ_closed hn) hr h'
  rw [← e]
  exact hstep

/-- Coordenadas de la recursión, por Separación. -/
def lowerBisection : ZFSet.{u} := functionOfRelation omegaTA rationalsTA (fun n x => ∃ y : ZFSet.{u}, BisectAt n x y)

def upperBisection : ZFSet.{u} := functionOfRelation omegaTA rationalsTA (fun n y => ∃ x : ZFSet.{u}, BisectAt n x y)

theorem lowerBisection_mem : (lowerBisection : ZFSet.{u}) ∈ rationalSequences := by
  apply functionOfRelation_mem
  intro n hn
  obtain ⟨x,y,h⟩ := bisectAt_exists hn
  refine ⟨x,⟨(bisectAt_mem h).1,y,h⟩,?_⟩
  rintro a ⟨_,b,h'⟩
  exact (bisectAt_unique hn h' h).1

theorem upperBisection_mem : (upperBisection : ZFSet.{u}) ∈ rationalSequences := by
  apply functionOfRelation_mem
  intro n hn
  obtain ⟨x,y,h⟩ := bisectAt_exists hn
  refine ⟨y,⟨(bisectAt_mem h).2,x,h⟩,?_⟩
  rintro b ⟨_,a,h'⟩
  exact (bisectAt_unique hn h' h).2

theorem bisectAt_values {n x y : ZFSet.{u}} (hn : n ∈ omegaTA) (h : BisectAt n x y) :
    SequenceValue lowerBisection n x ∧ SequenceValue upperBisection n y := by
  have hmem := bisectAt_mem h
  exact ⟨functionOfRelation_value_iff.mpr ⟨hn,hmem.1,y,h⟩,
    functionOfRelation_value_iff.mpr ⟨hn,hmem.2,x,h⟩⟩

theorem bisectAt_of_values {n x y : ZFSet.{u}} (hn : n ∈ omegaTA)
    (hx : SequenceValue lowerBisection n x) (hy : SequenceValue upperBisection n y) : BisectAt n x y := by
  obtain ⟨a,b,h⟩ := bisectAt_exists hn
  have hv := bisectAt_values hn h
  have ex := sequenceValue_unique lowerBisection_mem hn hx hv.1
  have ey := sequenceValue_unique upperBisection_mem hn hy hv.2
  rw [ex,ey]
  exact h

/-- Ecuaciones de TA-PRO-00115, no sólo una definición del estado. -/
def IsBisectionPair (a b : ZFSet.{u}) : Prop :=
  a ∈ rationalSequences ∧ b ∈ rationalSequences ∧
    SequenceValue a ∅ ratOne ∧ SequenceValue b ∅ ratTwoTA ∧
      ∀ n : ZFSet.{u}, n ∈ omegaTA → ∀ x y v w : ZFSet.{u},
        SequenceValue a n x → SequenceValue b n y →
        SequenceValue a (succ n) v → SequenceValue b (succ n) w →
        BisectStep (ZFSet.pair x y) (ZFSet.pair v w)

theorem canonical_bisection_pair : IsBisectionPair (lowerBisection : ZFSet.{u}) upperBisection := by
  have h0 := bisectAt_values omegaTA_isInductive.1 bisectAt_zero
  refine ⟨lowerBisection_mem,upperBisection_mem,h0.1,h0.2,?_⟩
  intro n hn x y v w hx hy hv hw
  exact bisectAt_succ_step hn (bisectAt_of_values hn hx hy)
    (bisectAt_of_values (TA_PRO_00022_succ_closed hn) hv hw)

/-- Unicidad de ambos extremos mediante inducción, sin elegir ramas. -/
theorem bisection_pair_unique {a b : ZFSet.{u}} (h : IsBisectionPair a b) :
    a = lowerBisection ∧ b = upperBisection := by
  obtain ⟨ha,hb,h0a,h0b,hstep⟩ := h
  have hmatch : ∀ n : ZFSet.{u}, n ∈ omegaTA → ∀ x y : ZFSet.{u},
      BisectAt n x y → SequenceValue a n x ∧ SequenceValue b n y := by
    apply TA_THM_00008_induction
    · intro x y hv
      obtain ⟨ex,ey⟩ := bisectAt_unique omegaTA_isInductive.1 hv bisectAt_zero
      rw [ex,ey]
      exact ⟨h0a,h0b⟩
    · intro n hn ih x y hnext
      obtain ⟨v,w,hprev⟩ := bisectAt_exists hn
      have hp := ih v w hprev
      have hsn := TA_PRO_00022_succ_closed hn
      obtain ⟨r,⟨_,hr⟩,_⟩ := sequenceValue_exists_unique ha hsn
      obtain ⟨s,⟨_,hs⟩,_⟩ := sequenceValue_exists_unique hb hsn
      have h1 := hstep n hn v w r s hp.1 hp.2 hr hs
      have h2 := bisectAt_succ_step hn hprev hnext
      obtain ⟨er,es⟩ := ZFSet.pair_injective (bisectStep_unique h1 h2)
      rw [er] at hr
      rw [es] at hs
      exact ⟨hr,hs⟩
  constructor
  · apply (TA_PRO_00107_sequence_eq_iff_values ha lowerBisection_mem).mpr
    intro n hn x y hx hy
    obtain ⟨v,w,hv⟩ := bisectAt_exists hn
    have e := sequenceValue_unique lowerBisection_mem hn hy (bisectAt_values hn hv).1
    exact (sequenceValue_unique ha hn hx (hmatch n hn v w hv).1).trans e.symm
  · apply (TA_PRO_00107_sequence_eq_iff_values hb upperBisection_mem).mpr
    intro n hn x y hx hy
    obtain ⟨v,w,hv⟩ := bisectAt_exists hn
    have e := sequenceValue_unique upperBisection_mem hn hy (bisectAt_values hn hv).2
    exact (sequenceValue_unique hb hn hx (hmatch n hn v w hv).2).trans e.symm

theorem TA_PRO_00115_bisection_exists_unique :
    ∃ a b : ZFSet.{u}, IsBisectionPair a b ∧
      ∀ c d : ZFSet.{u}, IsBisectionPair c d → c = a ∧ d = b :=
  ⟨lowerBisection,upperBisection,canonical_bisection_pair,fun _ _ h => bisection_pair_unique h⟩

end TratadoAnalisis.Cauchy.Bisection
