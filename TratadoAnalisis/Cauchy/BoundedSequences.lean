import TratadoAnalisis.Cauchy.CauchySequences

/-!
TA-LEAN-0011 A7 — §8.6. Cotas de segmentos iniciales y de sucesiones
racionales de Cauchy. Sólo se utilizan índices y racionales conjuntistas.
-/
namespace TratadoAnalisis.Cauchy.BoundedSequences
universe u
open TratadoAnalisis.Naturals.Foundational
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Naturals.ArithmeticBridge
open TratadoAnalisis.Integers.Order
open TratadoAnalisis.Cauchy.RationalSequences
open TratadoAnalisis.Cauchy.RationalDistance
open TratadoAnalisis.Cauchy.RationalConvergence
open TratadoAnalisis.Cauchy.CauchySequences
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.OrderedFieldCompatibility
open TratadoAnalisis.Rationals.StrictOrder
open TratadoAnalisis.Rationals.Signs
open TratadoAnalisis.Rationals.DifferenceOrder
open TratadoAnalisis.Rationals.AbsoluteValue
open TratadoAnalisis.Rationals.NoSupremumSqrtTwo

/-- TA-DEF-00112. -/
def RationalBounded (q : ZFSet.{u}) : Prop :=
  q ∈ rationalSequences ∧ ∃ B : ZFSet.{u}, B ∈ rationalsTA ∧
    RatLE ratZero B ∧ ∀ n : ZFSet.{u}, n ∈ omegaTA →
      ∀ x a : ZFSet.{u}, SequenceValue q n x → RatAbs x a → RatLE a B

def InitialBound (q N B : ZFSet.{u}) : Prop :=
  B ∈ rationalsTA ∧ RatLE ratZero B ∧
    ∀ n : ZFSet.{u}, n ∈ omegaTA → NatLETA n N → n ≠ N →
      ∀ x a : ZFSet.{u}, SequenceValue q n x → RatAbs x a → RatLE a B

theorem ratAdd_nonnegative_bounds {x y z : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (h0x : RatLE ratZero x) (h0y : RatLE ratZero y) (h : RatAdd x y z) :
    RatLE ratZero z ∧ RatLE x z ∧ RatLE y z := by
  have hz := funcFoundational_value_mem ratAddGraph_isFunc h
  have hxz := ratLE_add_compat ratZero_mem_rationalsTA hy hx h0y
    (zero_add_rel hx) (ratAdd_comm_rel hx hy h)
  have hyz := ratLE_add_compat ratZero_mem_rationalsTA hx hy h0x (zero_add_rel hy) h
  exact ⟨ratLE_trans ratZero_mem_rationalsTA hx hz h0x hxz, hxz, hyz⟩

theorem ratSub_zero_right_rel {x : ZFSet.{u}} (hx : x ∈ rationalsTA) :
    RatSub x ratZero x :=
  (ratSub_iff_add hx ratZero_mem_rationalsTA hx).mpr (ratAdd_zero_right_rel hx)

theorem distance_zero_right_iff_abs {x a : ZFSet.{u}} (hx : x ∈ rationalsTA) :
    RatDistance x ratZero a ↔ RatAbs x a := by
  constructor
  · rintro ⟨d, hd, ha⟩
    have e := RatSub_unique hx ratZero_mem_rationalsTA hd (ratSub_zero_right_rel hx)
    rw [e] at ha
    exact ha
  · intro h
    exact ⟨x, ratSub_zero_right_rel hx, h⟩

/-- TA-LEM-00029. Inducción finita sobre un código local del índice. -/
theorem TA_LEM_00029_initial_bounded {q N : ZFSet.{u}}
    (hq : q ∈ rationalSequences) (hN : N ∈ omegaTA) :
    ∃ B : ZFSet.{u}, InitialBound q N B := by
  obtain ⟨K, rfl⟩ := exists_natEncode_eq_of_mem hN
  clear hN
  induction K with
  | zero =>
    refine ⟨ratZero, ratZero_mem_rationalsTA, ratLE_refl ratZero_mem_rationalsTA, ?_⟩
    intro n hn hle hne _ _ _ _
    obtain ⟨k, rfl⟩ := exists_natEncode_eq_of_mem hn
    have hk := (NatLETA_natEncode_iff k 0).mp hle
    have e : k = 0 := Nat.le_antisymm hk (Nat.zero_le k)
    exact (hne (congrArg (fun i : Nat => (natEncode i : ZFSet.{u})) e)).elim
  | succ k ih =>
    obtain ⟨B, hB, h0B, hprev⟩ := ih
    have hk := (natEncode_mem_omegaTA k : (natEncode k : ZFSet.{u}) ∈ omegaTA)
    obtain ⟨x, ⟨hxQ, hx⟩, _⟩ := sequenceValue_exists_unique hq hk
    obtain ⟨a, ha, _⟩ := ratAbs_exists_unique hxQ
    have haQ := (ratAbs_mem ha).2
    obtain ⟨C, hC, hsum⟩ := ratAdd_exists hB haQ
    have hc := ratAdd_nonnegative_bounds hB haQ h0B (ratAbs_nonnegative ha) hsum
    refine ⟨C, hC, hc.1, ?_⟩
    intro n hn hle hne y b hy hb
    obtain ⟨j, rfl⟩ := exists_natEncode_eq_of_mem hn
    have hjle := (NatLETA_natEncode_iff j (k+1)).mp hle
    have hjne : j ≠ k+1 := fun e => hne (congrArg (fun i : Nat => (natEncode i : ZFSet.{u})) e)
    have hjk : j ≤ k := by omega
    rcases Nat.lt_or_eq_of_le hjk with hlt | e
    · have hnb : (natEncode j : ZFSet.{u}) ≠ natEncode k := fun eq => (Nat.ne_of_lt hlt) (natEncode_injective eq)
      exact ratLE_trans (ratAbs_mem hb).2 hB hC
        (hprev _ (natEncode_mem_omegaTA j) ((NatLETA_natEncode_iff j k).mpr hjk) hnb y b hy hb) hc.2.1
    · subst j
      have ey := sequenceValue_unique hq hk hy hx
      subst y
      have eb := ratAbs_unique hb ha
      rw [eb]
      exact hc.2.2

/-- TA-THM-00060: cota global M+(1+|q_N|). -/
theorem TA_THM_00060_cauchy_bounded {q : ZFSet.{u}}
    (hq : RationalCauchy q) : RationalBounded q := by
  obtain ⟨N,hN,ht⟩ := hq.2 ratOne ratOne_mem_rationalsTA ratZero_lt_one
  obtain ⟨M,hM,h0M,hinit⟩ := TA_LEM_00029_initial_bounded hq.1 hN
  obtain ⟨y,⟨hyQ,hy⟩,_⟩ := sequenceValue_exists_unique hq.1 hN
  obtain ⟨b,hb,_⟩ := ratAbs_exists_unique hyQ
  have hbQ := (ratAbs_mem hb).2
  obtain ⟨T,hT,hsT⟩ := ratAdd_exists ratOne_mem_rationalsTA hbQ
  have h0T := (ratAdd_nonnegative_bounds ratOne_mem_rationalsTA hbQ ratZero_lt_one.1 (ratAbs_nonnegative hb) hsT).1
  obtain ⟨B,hB,hsB⟩ := ratAdd_exists hM hT
  have hbound := ratAdd_nonnegative_bounds hM hT h0M h0T hsB
  refine ⟨hq.1,B,hB,hbound.1,?_⟩
  intro n hn x a hx ha
  have hxQ := sequenceValue_mem hq.1 hx
  have haQ := (ratAbs_mem ha).2
  have tail : NatLETA N n → RatLE a B := by
    intro hNn
    obtain ⟨d,hd,hdlt⟩ := ht n N hn hN hNn (natLE_refl_local hN) x y hx hy
    have hdQ := distance_mem hd
    obtain ⟨s,hs,hsum⟩ := ratAdd_exists hdQ hbQ
    have htri := distance_triangle hxQ hyQ ratZero_mem_rationalsTA hd
      ((distance_zero_right_iff_abs hyQ).mpr hb) ((distance_zero_right_iff_abs hxQ).mpr ha) hsum
    have hsTlt := ratLT_add_right_local hdQ ratOne_mem_rationalsTA hbQ hdlt hsum hsT
    exact ratLE_trans haQ hT hB (ratLE_trans haQ hs hT htri hsTlt.1) hbound.2.2
  rcases natLE_total_local hN hn with h | h
  · exact tail h
  · obtain ⟨j,rfl⟩ := exists_natEncode_eq_of_mem hn
    obtain ⟨k,rfl⟩ := exists_natEncode_eq_of_mem hN
    have hjk := (NatLETA_natEncode_iff j k).mp h
    rcases Nat.lt_or_eq_of_le hjk with hjlt | he
    · have hne : (natEncode j : ZFSet.{u}) ≠ natEncode k := fun e => (Nat.ne_of_lt hjlt) (natEncode_injective e)
      exact ratLE_trans haQ hM hB (hinit _ (natEncode_mem_omegaTA j) h hne x a hx ha) hbound.2.1
    · subst j
      exact tail (natLE_refl_local (natEncode_mem_omegaTA k))

end TratadoAnalisis.Cauchy.BoundedSequences
