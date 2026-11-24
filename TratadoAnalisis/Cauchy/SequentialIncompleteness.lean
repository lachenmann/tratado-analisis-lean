import TratadoAnalisis.Cauchy.BisectionWidths
import TratadoAnalisis.Cauchy.ConvergentIsCauchy

/-!
A8d — TA-DEF-00113, TA-THM-00061, TA-COR-00029.
La sucesión inferior es de Cauchy y no tiene límite racional. Se usa la
convergencia de los extremos superiores hacia el mismo límite hipotético,
y perturbaciones racionales ya certificadas; no se reconstruye un supremo.
-/
namespace TratadoAnalisis.Cauchy.SequentialIncompleteness
universe u
open TratadoAnalisis.Naturals.Foundational
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Naturals.ArithmeticBridge
open TratadoAnalisis.Integers.Order
open TratadoAnalisis.Cauchy.RationalSequences
open TratadoAnalisis.Cauchy.RationalDistance
open TratadoAnalisis.Cauchy.RationalConvergence
open TratadoAnalisis.Cauchy.CauchySequences
open TratadoAnalisis.Cauchy.Bisection
open TratadoAnalisis.Cauchy.BisectionInvariants
open TratadoAnalisis.Cauchy.BisectionWidths
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.StrictOrder
open TratadoAnalisis.Rationals.NoSupremumSqrtTwo
open TratadoAnalisis.Rationals.Signs
open TratadoAnalisis.Rationals.DifferenceOrder
open TratadoAnalisis.Rationals.AbsoluteValue
open TratadoAnalisis.Rationals.Trichotomy
open TratadoAnalisis.Rationals.IrrationalitySqrtTwo
open TratadoAnalisis.Rationals.SqrtTwoSet
open TratadoAnalisis.Rationals.SquareMonotonicity

/-- TA-DEF-00113. No se postula un algoritmo para producir límites. -/
def RationalSequentialComplete : Prop :=
  ∀ q : ZFSet.{u}, q ∈ cauchySequences → ∃ l : ZFSet.{u}, l ∈ rationalsTA ∧ RationalConverges q l

theorem natLE_trans_local {a b c : ZFSet.{u}}
    (ha : a ∈ omegaTA) (hb : b ∈ omegaTA) (hc : c ∈ omegaTA)
    (hab : NatLETA a b) (hbc : NatLETA b c) : NatLETA a c := by
  obtain ⟨A,rfl⟩ := exists_natEncode_eq_of_mem ha
  obtain ⟨B,rfl⟩ := exists_natEncode_eq_of_mem hb
  obtain ⟨C,rfl⟩ := exists_natEncode_eq_of_mem hc
  exact (NatLETA_natEncode_iff A C).mpr (Nat.le_trans ((NatLETA_natEncode_iff A B).mp hab) ((NatLETA_natEncode_iff B C).mp hbc))

/-- x≤b y a≤y implican x-y≤b-a. -/
theorem difference_le_interval_width {x y a b t d : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA) (ha : a ∈ rationalsTA) (hb : b ∈ rationalsTA)
    (hxb : RatLE x b) (hay : RatLE a y) (ht : RatSub x y t) (hd : RatSub b a d) : RatLE t d := by
  obtain ⟨ny,hny,hs⟩ := ht
  obtain ⟨na,hna,hd'⟩ := hd
  have hnyQ := funcFoundational_value_mem ratNegGraph_isFunc hny
  have hnaQ := funcFoundational_value_mem ratNegGraph_isFunc hna
  have hnn := ratNeg_le_reverse ha hy hna hny hay
  exact ratAdd_pair_le hx hnyQ hb hnaQ hxb hnn hs hd'

theorem distance_le_interval_width {x y a b r d : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA) (ha : a ∈ rationalsTA) (hb : b ∈ rationalsTA)
    (hax : RatLE a x) (hxb : RatLE x b) (hay : RatLE a y) (hyb : RatLE y b)
    (hr : RatDistance x y r) (hd : RatSub b a d) : RatLE r d := by
  obtain ⟨t,ht,hab⟩ := hr
  obtain ⟨s,_,hs⟩ := ratSub_exists hy hx
  have hneg := ratSub_reverse_neg hx hy ht hs
  exact (ratAbs_upper_iff hneg hab (ratSub_value_mem hd)).mpr
    ⟨difference_le_interval_width hx hy ha hb hxb hay ht hd,
      difference_le_interval_width hy hx ha hb hyb hax hs hd⟩

theorem distance_of_positive_difference {x y d : ZFSet.{u}}
    (hd : RatSub x y d) (hp : RatLE ratZero d) : RatDistance x y d := by
  obtain ⟨a,ha,_⟩ := ratAbs_exists_unique (ratSub_value_mem hd)
  have he := ratAbs_of_nonnegative ha hp
  rw [he] at ha
  exact ⟨d,hd,ha⟩

/-- TA-THM-00061, primera parte. -/
theorem lower_bisection_isCauchy : RationalCauchy (lowerBisection : ZFSet.{u}) := by
  refine ⟨lowerBisection_mem,?_⟩
  intro e heQ hep
  obtain ⟨N,hN,hsmall⟩ := TA_LEM_00031_widths_small heQ hep
  obtain ⟨a,b,hbase⟩ := bisectAt_exists hN
  have hab := bisectAt_mem hbase
  obtain ⟨d,hdQ,hd⟩ := ratSub_exists hab.2 hab.1
  have hde := (hsmall N hN (natLE_refl_local hN) d ⟨a,b,hbase,hd⟩).2
  refine ⟨N,hN,?_⟩
  intro m n hm hn hNm hNn x y hx hy
  obtain ⟨p,p',hp⟩ := bisectAt_exists hm
  obtain ⟨q,q',hq⟩ := bisectAt_exists hn
  have ex := sequenceValue_unique lowerBisection_mem hm hx (bisectAt_values hm hp).1
  have ey := sequenceValue_unique lowerBisection_mem hn hy (bisectAt_values hn hq).1
  subst x
  subst y
  have hpQ := bisectAt_mem hp
  have hqQ := bisectAt_mem hq
  have h1 := TA_LEM_00030_nested hN hm hNm hbase hp
  have h2 := TA_LEM_00030_nested hN hn hNn hbase hq
  have hpb := ratLE_trans hpQ.1 hpQ.2 hab.2 h1.2.1.1 h1.2.2
  have hqb := ratLE_trans hqQ.1 hqQ.2 hab.2 h2.2.1.1 h2.2.2
  obtain ⟨r,hr,_⟩ := distance_exists_unique hpQ.1 hqQ.1
  have hrd := distance_le_interval_width hpQ.1 hqQ.1 hab.1 hab.2 h1.1 hpb h2.1 hqb hr hd
  exact ⟨r,hr,ratLE_lt_trans (distance_mem hr) hdQ heQ hrd hde⟩

/-- Si los extremos inferiores convergieran, los superiores tendrían el mismo límite. -/
theorem upper_converges_of_lower {l : ZFSet.{u}}
    (h : RationalConverges lowerBisection l) : RationalConverges upperBisection l := by
  refine ⟨upperBisection_mem,h.2.1,?_⟩
  intro e heQ hp
  obtain ⟨eta,hEta,hpEta,hdouble⟩ := positive_half heQ hp
  obtain ⟨M,hM,ht⟩ := h.2.2 eta hEta hpEta
  obtain ⟨N,hN,hw⟩ := TA_LEM_00031_widths_small hEta hpEta
  obtain ⟨K,hK,hMK,hNK⟩ := common_upper_index hM hN
  refine ⟨K,hK,?_⟩
  intro n hn hKn y hy
  obtain ⟨a,b,hstate⟩ := bisectAt_exists hn
  have hval := bisectAt_values hn hstate
  have ey := sequenceValue_unique upperBisection_mem hn hy hval.2
  subst y
  have hab := bisectAt_mem hstate
  obtain ⟨d,_,hd⟩ := ratSub_exists hab.2 hab.1
  have hsmall := hw n hn (natLE_trans_local hN hK hn hNK hKn) d ⟨a,b,hstate,hd⟩
  have hba : WithinDistance b a eta := ⟨d,distance_of_positive_difference hd hsmall.1.1,hsmall.2⟩
  have hal := ht n hn (natLE_trans_local hM hK hn hMK hKn) a hval.1
  exact withinDistance_triangle hab.2 hab.1 h.2.1 hEta hdouble hba hal

/-- Un límite racional respeta toda cota inferior común. -/
theorem rational_limit_ge_lower {q l a : ZFSet.{u}} (h : RationalConverges q l)
    (ha : a ∈ rationalsTA)
    (hb : ∀ n : ZFSet.{u}, n ∈ omegaTA → ∀ x : ZFSet.{u}, SequenceValue q n x → RatLE a x) : RatLE a l := by
  have hl := h.2.1
  rcases TA_PRO_00172_rational_trichotomy ha hl with hlt | eq | hgt
  · exact hlt.1
  · rw [eq]
    exact ratLE_refl hl
  · obtain ⟨e,heQ,he⟩ := ratSub_exists ha hl
    have hep := ratSub_positive ha hl hgt he
    obtain ⟨N,hN,ht⟩ := h.2.2 e heQ hep
    obtain ⟨x,⟨hxQ,hx⟩,_⟩ := sequenceValue_exists_unique h.1 hN
    obtain ⟨lo,hi,_,hhi,_,hxi⟩ := (withinDistance_iff_window hxQ hl heQ hep).mp (ht N hN (natLE_refl_local hN) x hx)
    have hAdd := ratAdd_comm_rel heQ hl (ratSub_add_cancel ha hl he)
    have eqhi := RatAdd_unique hl heQ hhi hAdd
    rw [eqhi] at hxi
    exact (hxi.2 (ratLE_antisymm hxQ ha hxi.1 (hb N hN x hx))).elim

/-- Un límite racional respeta toda cota superior común. -/
theorem rational_limit_le_upper {q l b : ZFSet.{u}} (h : RationalConverges q l)
    (hb : b ∈ rationalsTA)
    (ha : ∀ n : ZFSet.{u}, n ∈ omegaTA → ∀ x : ZFSet.{u}, SequenceValue q n x → RatLE x b) : RatLE l b := by
  have hl := h.2.1
  rcases TA_PRO_00172_rational_trichotomy hl hb with hlt | eq | hgt
  · exact hlt.1
  · rw [eq]
    exact ratLE_refl hb
  · obtain ⟨e,heQ,he⟩ := ratSub_exists hl hb
    have hep := ratSub_positive hl hb hgt he
    obtain ⟨N,hN,ht⟩ := h.2.2 e heQ hep
    obtain ⟨x,⟨hxQ,hx⟩,_⟩ := sequenceValue_exists_unique h.1 hN
    obtain ⟨lo,hi,hlo,_,hlx,_⟩ := (withinDistance_iff_window hxQ hl heQ hep).mp (ht N hN (natLE_refl_local hN) x hx)
    have hback := (ratSub_iff_add hl heQ hb).mpr (ratAdd_comm_rel heQ hb (ratSub_add_cancel hl hb he))
    have eqlo := RatSub_unique hl heQ hlo hback
    rw [eqlo] at hlx
    exact (hlx.2 (ratLE_antisymm hb hxQ hlx.1 (ha N hN x hx))).elim

/-- Todos los extremos inferiores pertenecen a S₂, y todos los superiores
    dominan cada elemento de S₂. Esto no afirma la existencia de supremo. -/
theorem lower_bisection_in_sqrtTwoSet {n x : ZFSet.{u}} (hn : n ∈ omegaTA)
    (hx : SequenceValue lowerBisection n x) : x ∈ sqrtTwoSet := by
  obtain ⟨a,b,h⟩ := bisectAt_exists hn
  have ex := sequenceValue_unique lowerBisection_mem hn hx (bisectAt_values hn h).1
  subst x
  obtain ⟨h0a,_,aa,_,haa,_,hlt,_⟩ := bisect_bracket hn h
  exact TA_DEF_00066_mem_sqrtTwoSet_iff.mpr ⟨(bisectAt_mem h).1,h0a.1,aa,haa,hlt⟩

theorem upper_bisection_ge_sqrtTwoSet {r n y : ZFSet.{u}} (hr : r ∈ sqrtTwoSet)
    (hn : n ∈ omegaTA) (hy : SequenceValue upperBisection n y) : RatLE r y := by
  obtain ⟨a,b,h⟩ := bisectAt_exists hn
  have ey := sequenceValue_unique upperBisection_mem hn hy (bisectAt_values hn h).2
  subst y
  obtain ⟨h0a,hab,_,bb,_,hbb,_,h2bb⟩ := bisect_bracket hn h
  have hmem := bisectAt_mem h
  have hbQ := hmem.2
  have h0b := ratLE_trans ratZero_mem_rationalsTA hmem.1 hbQ h0a.1 hab.1
  obtain ⟨hrQ,_,rr,hrr,hrr2⟩ := TA_DEF_00066_mem_sqrtTwoSet_iff.mp hr
  rcases TA_PRO_00172_rational_trichotomy hrQ hbQ with hlt | eq | hgt
  · exact hlt.1
  · rw [eq]
    exact ratLE_refl hbQ
  · have hsq := TA_LEM_00018_square_strict_mono_nonnegative hbQ hrQ h0b hgt hbb hrr
    have hbbQ := funcFoundational_value_mem ratMulGraph_isFunc hbb
    have hrrQ := funcFoundational_value_mem ratMulGraph_isFunc hrr
    have hbad := ratLE_trans hbbQ hrrQ ratTwoTA_mem_rationalsTA hsq.1 hrr2.1
    exact (h2bb.2 (ratLE_antisymm ratTwoTA_mem_rationalsTA hbbQ h2bb.1 hbad)).elim

/-- TA-THM-00061, segunda parte. Se reutilizan las perturbaciones racionales
    de E3, no el teorema de ausencia de supremo. -/
theorem lower_bisection_no_rational_limit {l : ZFSet.{u}} : ¬ RationalConverges lowerBisection l := by
  intro hl
  have hlQ := hl.2.1
  have hOne : RatLE ratOne l := by
    apply rational_limit_ge_lower hl ratOne_mem_rationalsTA
    intro n hn x hx
    obtain ⟨a,b,h⟩ := bisectAt_exists hn
    have ex := sequenceValue_unique lowerBisection_mem hn hx (bisectAt_values hn h).1
    subst x
    have h0le : NatLETA (∅ : ZFSet.{u}) n := by
      obtain ⟨k,rfl⟩ := exists_natEncode_eq_of_mem hn
      exact (NatLETA_natEncode_iff 0 k).mpr (Nat.zero_le k)
    exact (TA_LEM_00030_nested omegaTA_isInductive.1 hn h0le bisectAt_zero h).1
  have hpos := ratLT_of_lt_of_le_local ratZero_mem_rationalsTA ratOne_mem_rationalsTA hlQ ratZero_lt_one hOne
  obtain ⟨s,hsQ,hs⟩ := ratMul_exists hlQ hlQ
  rcases TA_PRO_00172_rational_trichotomy hsQ ratTwoTA_mem_rationalsTA with hlt | eq | hgt
  · obtain ⟨r,hr,hlr⟩ := square_lt_two_gives_larger_member_local hlQ hpos hs hlt
    have hrQ := (TA_DEF_00066_mem_sqrtTwoSet_iff.mp hr).1
    have hrl := rational_limit_ge_lower (upper_converges_of_lower hl) hrQ (fun n hn y hy => upper_bisection_ge_sqrtTwoSet hr hn hy)
    exact hlr.2 (ratLE_antisymm hlQ hrQ hlr.1 hrl)
  · exact (TA_THM_00032_no_rational_square_two : ¬ ∃ q qq : ZFSet.{u}, q ∈ rationalsTA ∧ RatMul q q qq ∧ qq = ratTwoTA) ⟨l,s,hlQ,hs,eq⟩
  · obtain ⟨r,hr,hrl⟩ := two_lt_square_gives_smaller_upper_local hlQ hpos hs hgt
    have hlr := rational_limit_le_upper hl hr.1 (fun n hn x hx => hr.2 x (lower_bisection_in_sqrtTwoSet hn hx))
    exact hrl.2 (ratLE_antisymm hr.1 hlQ hrl.1 hlr)

theorem TA_THM_00061_bisection_cauchy_no_limit :
    (lowerBisection : ZFSet.{u}) ∈ cauchySequences ∧
      ∀ l : ZFSet.{u}, l ∈ rationalsTA → ¬ RationalConverges lowerBisection l :=
  ⟨TA_DEF_00111_mem_cauchySequences_iff.mpr lower_bisection_isCauchy,fun _ _ => lower_bisection_no_rational_limit⟩

theorem TA_COR_00029_rational_not_sequentially_complete : ¬ (RationalSequentialComplete.{u}) := by
  intro h
  have hc := (TA_THM_00061_bisection_cauchy_no_limit : (lowerBisection : ZFSet.{u}) ∈ cauchySequences ∧ ∀ l : ZFSet.{u}, l ∈ rationalsTA → ¬ RationalConverges lowerBisection l)
  obtain ⟨l,hlQ,hl⟩ := h lowerBisection hc.1
  exact hc.2 l hlQ hl

end TratadoAnalisis.Cauchy.SequentialIncompleteness
