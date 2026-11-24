import TratadoAnalisis.Cauchy.Bisection
import TratadoAnalisis.Cauchy.BoundedSequences

/-! TA-LEAN-0011 A8b — TA-LEM-00030: invariantes y anidamiento. -/
namespace TratadoAnalisis.Cauchy.BisectionInvariants
universe u
open TratadoAnalisis.Naturals.Foundational
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Naturals.ArithmeticBridge
open TratadoAnalisis.Integers.Order
open TratadoAnalisis.Cauchy.Bisection
open TratadoAnalisis.Cauchy.RationalDistance
open TratadoAnalisis.Cauchy.RationalConvergence
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.Field
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.StrictOrder
open TratadoAnalisis.Rationals.NoSupremumSqrtTwo
open TratadoAnalisis.Rationals.Signs
open TratadoAnalisis.Rationals.Division
open TratadoAnalisis.Rationals.PositiveProducts
open TratadoAnalisis.Rationals.Density
open TratadoAnalisis.Rationals.Trichotomy
open TratadoAnalisis.Rationals.IrrationalitySqrtTwo
open TratadoAnalisis.Rationals.SqrtTwoSet
open TratadoAnalisis.Rationals.AbsoluteValue

/-- El cuadrado del punto medio y su orden se mantienen relacionales. -/
theorem midpoint_between {x y m : ZFSet.{u}} (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (hxy : RatLT x y) (hm : Midpoint x y m) : RatLT x m ∧ RatLT m y := by
  obtain ⟨s,hs,hd⟩ := hm
  obtain ⟨i,hi,hmul⟩ := hd
  exact rational_midpoint_between hx hy hxy hs hi hmul

theorem midpoint_double {x y m s : ZFSet.{u}} (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (hm : Midpoint x y m) (hs : RatAdd x y s) : RatAdd m m s := by
  have hmQ := midpoint_mem hm
  obtain ⟨t,ht,hd⟩ := hm
  have e := RatAdd_unique hx hy ht hs
  subst t
  have hmul := ratDiv_mul_denominator (funcFoundational_value_mem ratAddGraph_isFunc hs)
    ratTwoTA_mem_rationalsTA ratZero_lt_two_local hd
  exact ratTwo_mul_as_add_local hmQ (ratMul_comm_rel hmQ ratTwoTA_mem_rationalsTA hmul)

/-- De w+w=d se recupera la división literal por dos. -/
theorem double_is_half {w d : ZFSet.{u}} (hw : w ∈ rationalsTA) (hd : RatAdd w w d) :
    RatDiv d ratTwoTA w := by
  have hdQ := funcFoundational_value_mem ratAddGraph_isFunc hd
  obtain ⟨v,hvQ,hv⟩ := ratDiv_exists hdQ two_nonzero_mem
  have hvm := ratDiv_mul_denominator hdQ ratTwoTA_mem_rationalsTA ratZero_lt_two_local hv
  obtain ⟨z,_,hz⟩ := ratMul_exists hw ratTwoTA_mem_rationalsTA
  have hz' := ratTwo_mul_as_add_local hw (ratMul_comm_rel hw ratTwoTA_mem_rationalsTA hz)
  have e := RatAdd_unique hw hw hz' hd
  rw [e] at hz
  have hwv := ratLE_mul_positive_iff hw hvQ ratTwoTA_mem_rationalsTA ratZero_lt_two_local hz hvm
  have hvw := ratLE_mul_positive_iff hvQ hw ratTwoTA_mem_rationalsTA ratZero_lt_two_local hvm hz
  have eq := ratLE_antisymm hw hvQ (hwv.mpr (ratLE_refl hdQ)) (hvw.mpr (ratLE_refl hdQ))
  rw [eq]
  exact hv

theorem midpoint_halves {x y m d l r : ZFSet.{u}} (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (hm : Midpoint x y m) (hd : RatSub y x d) (hl : RatSub m x l) (hr : RatSub y m r) :
    RatDiv d ratTwoTA l ∧ RatDiv d ratTwoTA r := by
  have hmQ := midpoint_mem hm
  have hlQ := ratSub_value_mem hl
  have hrQ := ratSub_value_mem hr
  obtain ⟨s,_,hs⟩ := ratAdd_exists hx hy
  have hdouble := midpoint_double hx hy hm hs
  obtain ⟨c,hcQ,hc⟩ := ratAdd_exists hx hmQ
  obtain ⟨v,_,hv⟩ := ratAdd_exists hcQ hrQ
  obtain ⟨w,_,hw⟩ := ratAdd_exists hcQ hlQ
  have ev := ratAdd_assoc hx hmQ hrQ hc hv
    (ratAdd_comm_rel hrQ hmQ (ratSub_add_cancel hy hmQ hr)) hs
  have ew := ratAdd_assoc hmQ hx hlQ (ratAdd_comm_rel hx hmQ hc) hw
    (ratAdd_comm_rel hlQ hx (ratSub_add_cancel hmQ hx hl)) hdouble
  have er := ratAdd_cancel_right_local hrQ hlQ hcQ
    (ratAdd_comm_rel hcQ hrQ hv) (ratAdd_comm_rel hcQ hlQ hw) (ev.trans ew.symm)
  subst r
  have hadd := ratSub_chain_add hy hmQ hx hr hl hd
  exact ⟨double_is_half hlQ hadd,double_is_half hlQ hadd⟩

/-- 0<x<y y x²<2<y². -/
def BisectBracket (x y : ZFSet.{u}) : Prop :=
  RatLT ratZero x ∧ RatLT x y ∧ ∃ xx yy : ZFSet.{u},
    RatMul x x xx ∧ RatMul y y yy ∧ RatLT xx ratTwoTA ∧ RatLT ratTwoTA yy

theorem initial_bracket : BisectBracket (ratOne : ZFSet.{u}) ratTwoTA := by
  obtain ⟨s,_,hs⟩ := ratMul_exists ratTwoTA_mem_rationalsTA ratTwoTA_mem_rationalsTA
  have hsum := ratTwo_mul_as_add_local ratTwoTA_mem_rationalsTA hs
  have hlt := ratLT_add_right_local ratZero_mem_rationalsTA ratTwoTA_mem_rationalsTA ratTwoTA_mem_rationalsTA
    ratZero_lt_two_local (TratadoAnalisis.Rationals.DifferenceOrder.zero_add_rel ratTwoTA_mem_rationalsTA) hsum
  exact ⟨ratZero_lt_one,ratOne_lt_two_local,ratOne,s,ratOne_square_local,hs,ratOne_lt_two_local,hlt⟩

theorem bisect_step_invariants {x y a b : ZFSet.{u}}
    (h : BisectStep (ZFSet.pair x y) (ZFSet.pair a b)) (hb : BisectBracket x y) :
    BisectBracket a b ∧ RatLE x a ∧ RatLE b y ∧
      ∀ d e : ZFSet.{u}, RatSub y x d → RatSub b a e → RatDiv d ratTwoTA e := by
  obtain ⟨x',y',m,s,hx,hy,he,hm,hs,hcases⟩ := h
  obtain ⟨ex,ey⟩ := ZFSet.pair_injective he
  subst x'
  subst y'
  obtain ⟨h0x,hxy,xx,yy,hxx,hyy,hxx2,h2yy⟩ := hb
  have hmQ := midpoint_mem hm
  have hsQ := ratMul_value_mem hs
  have hmid := midpoint_between hx hy hxy hm
  have h0m := ratLT_of_lt_of_le_local ratZero_mem_rationalsTA hx hmQ h0x hmid.1.1
  rcases hcases with ⟨hlt,he⟩ | ⟨hnlt,he⟩
  · obtain ⟨ea,eb⟩ := ZFSet.pair_injective he
    subst a
    subst b
    refine ⟨⟨h0m,hmid.2,s,yy,hs,hyy,hlt,h2yy⟩,hmid.1.1,ratLE_refl hy,?_⟩
    intro d e hd he
    obtain ⟨l,_,hl⟩ := ratSub_exists hmQ hx
    exact (midpoint_halves hx hy hm hd hl he).2
  · obtain ⟨ea,eb⟩ := ZFSet.pair_injective he
    subst a
    subst b
    have hgt : RatLT ratTwoTA s := by
      rcases TA_PRO_00172_rational_trichotomy hsQ ratTwoTA_mem_rationalsTA with hlt | eq | hgt
      · exact (hnlt hlt).elim
      · exact ((TA_THM_00032_no_rational_square_two : ¬ ∃ q qq : ZFSet.{u}, q ∈ rationalsTA ∧ RatMul q q qq ∧ qq = ratTwoTA) ⟨m,s,hmQ,hs,eq⟩).elim
      · exact hgt
    refine ⟨⟨h0x,hmid.1,xx,s,hxx,hs,hxx2,hgt⟩,ratLE_refl hx,hmid.2.1,?_⟩
    intro d e hd he
    obtain ⟨r,_,hr⟩ := ratSub_exists hy hmQ
    exact (midpoint_halves hx hy hm hd he hr).1

/-- TA-LEM-00030, cláusulas 1 y 2. -/
theorem bisect_bracket {n x y : ZFSet.{u}} (hn : n ∈ omegaTA) (h : BisectAt n x y) : BisectBracket x y := by
  have hall : ∀ k : ZFSet.{u}, k ∈ omegaTA → ∀ a b : ZFSet.{u}, BisectAt k a b → BisectBracket a b := by
    apply TA_THM_00008_induction
    · intro a b h
      obtain ⟨ea,eb⟩ := bisectAt_unique omegaTA_isInductive.1 h bisectAt_zero
      rw [ea,eb]
      exact initial_bracket
    · intro k hk ih a b h
      obtain ⟨v,w,hprev⟩ := bisectAt_exists hk
      exact (bisect_step_invariants (bisectAt_succ_step hk hprev h) (ih v w hprev)).1
  exact hall n hn x y h

/-- TA-LEM-00030, cláusulas 3 y 4. -/
theorem bisect_adjacent {n x y a b : ZFSet.{u}} (hn : n ∈ omegaTA)
    (h : BisectAt n x y) (h' : BisectAt (succ n) a b) :
    RatLE x a ∧ RatLT a b ∧ RatLE b y ∧
      ∀ d e : ZFSet.{u}, RatSub y x d → RatSub b a e → RatDiv d ratTwoTA e := by
  have hi := bisect_step_invariants (bisectAt_succ_step hn h h') (bisect_bracket hn h)
  exact ⟨hi.2.1,hi.1.2.1,hi.2.2.1,hi.2.2.2⟩

/-- TA-LEM-00030, anidamiento para dos índices cualesquiera. -/
theorem TA_LEM_00030_nested {n k x y a b : ZFSet.{u}}
    (hn : n ∈ omegaTA) (hk : k ∈ omegaTA) (hnk : NatLETA n k)
    (h : BisectAt n x y) (h' : BisectAt k a b) : RatLE x a ∧ RatLT a b ∧ RatLE b y := by
  obtain ⟨N,rfl⟩ := exists_natEncode_eq_of_mem hn
  obtain ⟨K,rfl⟩ := exists_natEncode_eq_of_mem hk
  obtain ⟨D,hKD⟩ := Nat.exists_eq_add_of_le ((NatLETA_natEncode_iff N K).mp hnk)
  have hmem := bisectAt_mem h
  have hall : ∀ j : Nat, ∀ c d : ZFSet.{u}, BisectAt (natEncode (N+j)) c d → RatLE x c ∧ RatLT c d ∧ RatLE d y := by
    intro j
    induction j with
    | zero =>
      intro c d hv
      obtain ⟨ec,ed⟩ := bisectAt_unique hn hv h
      subst c
      subst d
      exact ⟨ratLE_refl hmem.1,(bisect_bracket hn h).2.1,ratLE_refl hmem.2⟩
    | succ j ih =>
      intro c d hv
      have hj := (natEncode_mem_omegaTA (N+j) : (natEncode (N+j) : ZFSet.{u}) ∈ omegaTA)
      obtain ⟨p,q,hp⟩ := bisectAt_exists hj
      have hprev := ih p q hp
      have hnext := bisect_adjacent hj hp hv
      have hpq := bisectAt_mem hp
      have hcd := bisectAt_mem hv
      exact ⟨ratLE_trans hmem.1 hpq.1 hcd.1 hprev.1 hnext.1,hnext.2.1,
        ratLE_trans hcd.2 hpq.2 hmem.2 hnext.2.2.1 hprev.2.2⟩
  rw [hKD] at h'
  exact hall D a b h'

end TratadoAnalisis.Cauchy.BisectionInvariants
