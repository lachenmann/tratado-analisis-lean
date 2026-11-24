import TratadoAnalisis.Cauchy.BisectionInvariants
import TratadoAnalisis.Rationals.Archimedean

/-! A8c — TA-LEM-00031. Anchura diádica exacta y cofinalidad racional.
La fórmula se expresa por el producto con el numeral 2^n; los códigos Nat
son locales y no sustituyen a los naturales conjuntistas. -/
namespace TratadoAnalisis.Cauchy.BisectionWidths
universe u
open TratadoAnalisis.Naturals.Foundational
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Naturals.ArithmeticBridge
open TratadoAnalisis.Integers.Order
open TratadoAnalisis.Cauchy.Bisection
open TratadoAnalisis.Cauchy.BisectionInvariants
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
open TratadoAnalisis.Rationals.IrrationalitySqrtTwo
open TratadoAnalisis.Rationals.SqrtTwoSet
open TratadoAnalisis.Rationals.AbsoluteValue
open TratadoAnalisis.Rationals.NatEmbedding
open TratadoAnalisis.Rationals.Archimedean

/-- δ_n=b_n-a_n, sin una función de selección. -/
def BisectWidth (n d : ZFSet.{u}) : Prop :=
  ∃ x y : ZFSet.{u}, BisectAt n x y ∧ RatSub y x d

theorem bisectWidth_mem {n d : ZFSet.{u}} (hd : BisectWidth n d) : d ∈ rationalsTA := by
  obtain ⟨_,_,_,h⟩ := hd
  exact ratSub_value_mem h

theorem bisectWidth_exists {n : ZFSet.{u}} (hn : n ∈ omegaTA) : ∃ d : ZFSet.{u}, BisectWidth n d := by
  obtain ⟨x,y,h⟩ := bisectAt_exists hn
  obtain ⟨d,_,hd⟩ := ratSub_exists (bisectAt_mem h).2 (bisectAt_mem h).1
  exact ⟨d,x,y,h,hd⟩

theorem bisectWidth_unique {n d e : ZFSet.{u}} (hn : n ∈ omegaTA)
    (hd : BisectWidth n d) (he : BisectWidth n e) : d = e := by
  obtain ⟨x,y,h,hd'⟩ := hd
  obtain ⟨a,b,h',he'⟩ := he
  obtain ⟨ex,ey⟩ := bisectAt_unique hn h h'
  subst a
  subst b
  exact RatSub_unique (bisectAt_mem h).2 (bisectAt_mem h).1 hd' he'

theorem bisectWidth_positive {n d : ZFSet.{u}} (hn : n ∈ omegaTA) (hd : BisectWidth n d) : RatLT ratZero d := by
  obtain ⟨x,y,h,hs⟩ := hd
  exact ratSub_positive (bisectAt_mem h).2 (bisectAt_mem h).1 (bisect_bracket hn h).2.1 hs

theorem bisectWidth_zero : BisectWidth (∅ : ZFSet.{u}) ratOne :=
  ⟨ratOne,ratTwoTA,bisectAt_zero,(ratSub_iff_add ratTwoTA_mem_rationalsTA ratOne_mem_rationalsTA ratOne_mem_rationalsTA).mpr ratOne_add_one_two_local⟩

theorem bisectWidth_succ {n d e : ZFSet.{u}} (hn : n ∈ omegaTA)
    (hd : BisectWidth n d) (he : BisectWidth (succ n) e) : RatDiv d ratTwoTA e := by
  obtain ⟨x,y,h,hd'⟩ := hd
  obtain ⟨a,b,h',he'⟩ := he
  exact (bisect_adjacent hn h h').2.2.2 d e hd' he'

/-- Fórmula exacta δ_n·ν(2^n)=1, por inducción. -/
theorem dyadic_width_product (n : Nat) {d : ZFSet.{u}} (hd : BisectWidth (natEncode n) d) :
    RatMul (natRational (natEncode (2^n) : ZFSet.{u})) d ratOne := by
  induction n generalizing d with
  | zero =>
    have eq := bisectWidth_unique omegaTA_isInductive.1 hd bisectWidth_zero
    subst d
    exact ratOne_square_local
  | succ n ih =>
    have hn := (natEncode_mem_omegaTA n : (natEncode n : ZFSet.{u}) ∈ omegaTA)
    obtain ⟨w,hw⟩ := bisectWidth_exists hn
    have hprev : RatMul (natRational (natEncode (2^n) : ZFSet.{u})) w ratOne := by
      apply ih
      exact hw
    have hdiv := bisectWidth_succ hn hw hd
    have hdQ := bisectWidth_mem hd
    have hwm := ratDiv_mul_denominator (bisectWidth_mem hw) ratTwoTA_mem_rationalsTA ratZero_lt_two_local hdiv
    have hprod : RatMul ratTwoTA d w := ratMul_comm_rel hdQ ratTwoTA_mem_rationalsTA hwm
    have hpowQ := natRational_mem (natEncode_mem_omegaTA (2^n) : (natEncode (2^n) : ZFSet.{u}) ∈ omegaTA)
    have hpowNextQ := natRational_mem (natEncode_mem_omegaTA (2^(n+1)) : (natEncode (2^(n+1)) : ZFSet.{u}) ∈ omegaTA)
    have hpow : RatMul (natRational (natEncode (2^n) : ZFSet.{u})) ratTwoTA (natRational (natEncode (2^(n+1)))) := by
      rw [Nat.pow_succ]
      exact natRational_mul_nat (2^n) 2
    obtain ⟨p,_,hp⟩ := ratMul_exists hpowNextQ hdQ
    have e := ratMul_assoc hpowQ ratTwoTA_mem_rationalsTA hdQ hpow hp hprod hprev
    rw [e] at hp
    exact hp

theorem nat_succ_le_pow_two (n : Nat) : n+1 ≤ 2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ]
    omega

/-- La fórmula anterior determina el cociente 1/2^n. -/
theorem dyadic_width_division (n : Nat) {d : ZFSet.{u}} (hd : BisectWidth (natEncode n) d) :
    RatDiv ratOne (natRational (natEncode (2^n) : ZFSet.{u})) d := by
  have hdQ := bisectWidth_mem hd
  have hnumQ := natRational_mem (natEncode_mem_omegaTA (2^n) : (natEncode (2^n) : ZFSet.{u}) ∈ omegaTA)
  have hnat : (0 : Nat) < 2^n := Nat.lt_of_lt_of_le (Nat.zero_lt_succ n) (nat_succ_le_pow_two n)
  have hnum : RatLT ratZero (natRational (natEncode (2^n) : ZFSet.{u})) := by
    have hle := (NatLETA_natEncode_iff 0 (2^n)).mpr (Nat.zero_le _)
    have hne : (natEncode 0 : ZFSet.{u}) ≠ natEncode (2^n) := fun h => (Nat.ne_of_lt hnat) (natEncode_injective h)
    exact (TA_COR_00008_natRational_strict_order_iff (natEncode_mem_omegaTA 0) (natEncode_mem_omegaTA (2^n))).mp ⟨hle,hne⟩
  have hNZ := mem_ratNonzeroTA_iff.mpr ⟨hnumQ,fun h => hnum.2 h.symm⟩
  obtain ⟨e,heQ,he⟩ := ratDiv_exists ratOne_mem_rationalsTA hNZ
  have hem := ratDiv_mul_denominator ratOne_mem_rationalsTA hnumQ hnum he
  have hdm := ratMul_comm_rel hnumQ hdQ (dyadic_width_product n hd)
  have hde := (ratLE_mul_positive_iff hdQ heQ hnumQ hnum hdm hem).mpr (ratLE_refl ratOne_mem_rationalsTA)
  have hed := (ratLE_mul_positive_iff heQ hdQ hnumQ hnum hem hdm).mpr (ratLE_refl ratOne_mem_rationalsTA)
  have eq := ratLE_antisymm hdQ heQ hde hed
  rw [eq]
  exact he

/-- TA-LEM-00031: una única instancia arquimediana para cada tolerancia.
La estimación diádica sustituye la inducción auxiliar del texto por una
cota directa de los denominadores; no usa completitud. -/
theorem TA_LEM_00031_widths_small {e : ZFSet.{u}}
    (heQ : e ∈ rationalsTA) (he : RatLT ratZero e) :
    ∃ N : ZFSet.{u}, N ∈ omegaTA ∧ ∀ n : ZFSet.{u}, n ∈ omegaTA → NatLETA N n →
      ∀ d : ZFSet.{u}, BisectWidth n d → RatLT ratZero d ∧ RatLT d e := by
  have hNZ := mem_ratNonzeroTA_iff.mpr ⟨heQ,fun h => he.2 h.symm⟩
  obtain ⟨i,hiNZ,hi,_,hie⟩ := exists_inverse_of_mem_ratNonzeroTA hNZ
  have hiQ := (mem_ratNonzeroTA_iff.mp hiNZ).1
  have h0i := ratInv_positive heQ hi he
  obtain ⟨N,hN,hNi⟩ := TA_THM_00031_rational_archimedean hiQ
  refine ⟨N,hN,?_⟩
  intro n hn hNn d hd
  have hdp := bisectWidth_positive hn hd
  have hdQ := bisectWidth_mem hd
  obtain ⟨k,rfl⟩ := exists_natEncode_eq_of_mem hn
  obtain ⟨j,rfl⟩ := exists_natEncode_eq_of_mem hN
  have hjk := (NatLETA_natEncode_iff j k).mp hNn
  have hjpow := Nat.le_trans hjk (Nat.le_trans (Nat.le_succ k) (nat_succ_le_pow_two k))
  have hnumQ := natRational_mem (natEncode_mem_omegaTA (2^k) : (natEncode (2^k) : ZFSet.{u}) ∈ omegaTA)
  have hjQ := natRational_mem (natEncode_mem_omegaTA j : (natEncode j : ZFSet.{u}) ∈ omegaTA)
  have hle := (TA_COR_00008_natRational_order_iff (natEncode_mem_omegaTA j) (natEncode_mem_omegaTA (2^k))).mp ((NatLETA_natEncode_iff j (2^k)).mpr hjpow)
  have hinum := ratLT_of_lt_of_le_local hiQ hjQ hnumQ hNi hle
  have h0num := ratLT_of_lt_of_le_local ratZero_mem_rationalsTA hiQ hnumQ h0i hinum.1
  obtain ⟨p,hpQ,hp⟩ := ratMul_exists hnumQ heQ
  have h1p := ratLT_mul_positive_right hiQ hnumQ heQ hinum he hie hp
  have hmul := dyadic_width_product k hd
  have hde := (TA_LEM_00020_clause9_scale_iff hdQ heQ hnumQ h0num
    (ratMul_comm_rel hnumQ hdQ hmul) (ratMul_comm_rel hnumQ heQ hp)).mpr h1p
  exact ⟨hdp,hde⟩

end TratadoAnalisis.Cauchy.BisectionWidths
