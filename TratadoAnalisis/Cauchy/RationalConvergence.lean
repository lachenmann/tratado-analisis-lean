import TratadoAnalisis.Cauchy.SequenceOperations
import TratadoAnalisis.Cauchy.RationalDistance
import TratadoAnalisis.Rationals.PositiveProducts

/-!
# TA-LEAN-0011 A4 — Convergencia racional (§8.3)

El límite, la precisión, las distancias y los valores de la sucesión
pertenecen al cuerpo racional conjuntista. Los índices pertenecen a omegaTA.
La convergencia no exige un módulo. La existencia del módulo mínimo
se demuestra separadamente con tercero excluido explícito, sin Choice.
-/

namespace TratadoAnalisis.Cauchy.RationalConvergence

universe u

open TratadoAnalisis.Naturals.Foundational
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Naturals.ArithmeticBridge
open TratadoAnalisis.Integers.Order
open TratadoAnalisis.Foundations.FunctionSpace
open TratadoAnalisis.Foundations.RelationalFunctions
open TratadoAnalisis.Cauchy.RationalSequences
open TratadoAnalisis.Cauchy.SequenceOperations
open TratadoAnalisis.Cauchy.RationalDistance
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.Field
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.StrictOrder
open TratadoAnalisis.Rationals.Signs
open TratadoAnalisis.Rationals.Division
open TratadoAnalisis.Rationals.PositiveProducts
open TratadoAnalisis.Rationals.AbsoluteValue
open TratadoAnalisis.Rationals.NoSupremumSqrtTwo
open TratadoAnalisis.Rationals.IrrationalitySqrtTwo
open TratadoAnalisis.Rationals.SqrtTwoSet
open TratadoAnalisis.Rationals.Trichotomy

/-- Infraestructura de orden natural independiente de módulos posteriores a Q. -/
theorem natLE_refl_local {n : ZFSet.{u}} (hn : n ∈ omegaTA) :
    NatLETA n n := by
  obtain ⟨N, rfl⟩ := exists_natEncode_eq_of_mem hn
  exact (NatLETA_natEncode_iff N N).mpr (Nat.le_refl N)

theorem natLE_antisymm_local {m n : ZFSet.{u}}
    (hm : m ∈ omegaTA) (hn : n ∈ omegaTA)
    (hmn : NatLETA m n) (hnm : NatLETA n m) : m = n := by
  obtain ⟨M, rfl⟩ := exists_natEncode_eq_of_mem hm
  obtain ⟨N, rfl⟩ := exists_natEncode_eq_of_mem hn
  exact congrArg (fun k : Nat => (natEncode k : ZFSet.{u}))
    (Nat.le_antisymm ((NatLETA_natEncode_iff M N).mp hmn)
      ((NatLETA_natEncode_iff N M).mp hnm))

theorem natLE_total_local {m n : ZFSet.{u}}
    (hm : m ∈ omegaTA) (hn : n ∈ omegaTA) :
    NatLETA m n ∨ NatLETA n m := by
  obtain ⟨M, rfl⟩ := exists_natEncode_eq_of_mem hm
  obtain ⟨N, rfl⟩ := exists_natEncode_eq_of_mem hn
  rcases Nat.le_total M N with h | h
  · exact Or.inl ((NatLETA_natEncode_iff M N).mpr h)
  · exact Or.inr ((NatLETA_natEncode_iff N M).mpr h)

theorem common_upper_index {m n : ZFSet.{u}}
    (hm : m ∈ omegaTA) (hn : n ∈ omegaTA) :
    ∃ k : ZFSet.{u}, k ∈ omegaTA ∧ NatLETA m k ∧ NatLETA n k := by
  rcases natLE_total_local hm hn with h | h
  · exact ⟨n, hn, h, natLE_refl_local hn⟩
  · exact ⟨m, hm, natLE_refl_local hm, h⟩

/-- Positividad estricta de una suma de dos incrementos estrictos. -/
theorem ratAdd_pair_lt {x y a b z s : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (ha : a ∈ rationalsTA) (hb : b ∈ rationalsTA)
    (hxa : RatLT x a) (hyb : RatLT y b)
    (hxy : RatAdd x y z) (hab : RatAdd a b s) : RatLT z s := by
  obtain ⟨t, ht, hay⟩ := ratAdd_exists ha hy
  have hzt := ratLT_add_right_local hx ha hy hxa hxy hay
  have hts := ratLT_add_left_local hy hb ha hyb hay hab
  exact ratLE_lt_trans (funcFoundational_value_mem ratAddGraph_isFunc hxy)
    ht (funcFoundational_value_mem ratAddGraph_isFunc hab) hzt.1 hts

/-- La mitad de un racional positivo es racional positiva y su doble es él mismo. -/
theorem positive_half {d : ZFSet.{u}}
    (hd : d ∈ rationalsTA) (hdpos : RatLT ratZero d) :
    ∃ e : ZFSet.{u}, e ∈ rationalsTA ∧ RatLT ratZero e ∧ RatAdd e e d := by
  have htwo : (ratTwoTA : ZFSet.{u}) ∈ ratNonzeroTA :=
    mem_ratNonzeroTA_iff.mpr ⟨ratTwoTA_mem_rationalsTA, ratTwoTA_ne_zero⟩
  obtain ⟨e, he, hdiv⟩ := ratDiv_exists hd htwo
  have hepos := ratDiv_positive hd ratTwoTA_mem_rationalsTA hdpos ratZero_lt_two_local hdiv
  have hemul := ratDiv_mul_denominator hd ratTwoTA_mem_rationalsTA ratZero_lt_two_local hdiv
  exact ⟨e, he, hepos, ratTwo_mul_as_add_local he
    (ratMul_comm_rel he ratTwoTA_mem_rationalsTA hemul)⟩

/-- Predicado d_Q(x,y)<e, sin elegir globalmente el valor de la distancia. -/
def WithinDistance (x y e : ZFSet.{u}) : Prop :=
  ∃ r : ZFSet.{u}, RatDistance x y r ∧ RatLT r e

theorem withinDistance_iff_value {x y e r : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA) (hr : RatDistance x y r) :
    WithinDistance x y e ↔ RatLT r e := by
  constructor
  · rintro ⟨s, hs, hlt⟩
    have h := distance_unique hx hy hs hr
    rw [h] at hlt
    exact hlt
  · intro h
    exact ⟨r, hr, h⟩

theorem withinDistance_self {x e : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (he : RatLT ratZero e) :
    WithinDistance x x e := by
  obtain ⟨r, hr, _⟩ := distance_exists_unique hx hx
  have h := (distance_zero_iff hx hx hr).mpr rfl
  refine ⟨r, hr, ?_⟩
  rw [h]
  exact he

theorem withinDistance_symm {x y e : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (h : WithinDistance x y e) : WithinDistance y x e := by
  obtain ⟨r, hr, hlt⟩ := h
  obtain ⟨s, hs, _⟩ := distance_exists_unique hy hx
  have he := distance_symm hx hy hr hs
  refine ⟨s, hs, ?_⟩
  rw [← he]
  exact hlt

/-- Si dos distancias son menores que e, la tercera es menor que 2e. -/
theorem withinDistance_triangle {x y z e d : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA) (hz : z ∈ rationalsTA)
    (he : e ∈ rationalsTA) (hd : RatAdd e e d)
    (hxy : WithinDistance x y e) (hyz : WithinDistance y z e) :
    WithinDistance x z d := by
  obtain ⟨a, ha, hae⟩ := hxy
  obtain ⟨b, hb, hbe⟩ := hyz
  obtain ⟨c, hc, _⟩ := distance_exists_unique hx hz
  obtain ⟨s, hs, hab⟩ := ratAdd_exists (distance_mem ha) (distance_mem hb)
  have hcs := distance_triangle hx hy hz ha hb hc hab
  have hsd := ratAdd_pair_lt (distance_mem ha) (distance_mem hb) he he hae hbe hab hd
  exact ⟨c, hc, ratLE_lt_trans (distance_mem hc) hs
    (funcFoundational_value_mem ratAddGraph_isFunc hd) hcs hsd⟩

/-- Las dos lecturas alternativas de TA-PRO-00111. -/
def WithinAbsolute (x y e : ZFSet.{u}) : Prop :=
  ∃ t a : ZFSet.{u}, RatSub x y t ∧ RatAbs t a ∧ RatLT a e

def WithinWindow (x y e : ZFSet.{u}) : Prop :=
  ∃ lo hi : ZFSet.{u}, RatSub y e lo ∧ RatAdd y e hi ∧
    RatLT lo x ∧ RatLT x hi

theorem withinDistance_iff_absolute {x y e : ZFSet.{u}} :
    WithinDistance x y e ↔ WithinAbsolute x y e := by
  constructor
  · rintro ⟨a, ⟨t, ht, ha⟩, hlt⟩
    exact ⟨t, a, ht, ha, hlt⟩
  · rintro ⟨t, a, ht, ha, hlt⟩
    exact ⟨a, ⟨t, ht, ha⟩, hlt⟩

theorem withinDistance_iff_window {x y e : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (he : e ∈ rationalsTA) (hepos : RatLT ratZero e) :
    WithinDistance x y e ↔ WithinWindow x y e := by
  obtain ⟨ne, _, hne⟩ := ratNeg_exists he
  obtain ⟨t, _, ht⟩ := ratSub_exists hx hy
  obtain ⟨r, hr, _⟩ := distance_exists_unique hx hy
  obtain ⟨lo, _, hlo⟩ := ratSub_exists hy he
  obtain ⟨hi, _, hhi⟩ := ratAdd_exists hy he
  have heq := TA_PRO_00110_distance_local hx hy he hepos hne ht hr hlo hhi
  have hiff := heq.1.trans heq.2
  constructor
  · intro h
    have hw := hiff.mp ((withinDistance_iff_value hx hy hr).mp h)
    exact ⟨lo, hi, hlo, hhi, hw.1, hw.2⟩
  · rintro ⟨lo', hi', hlo', hhi', h1, h2⟩
    have el := RatSub_unique hy he hlo' hlo
    have ei := RatAdd_unique hy he hhi' hhi
    rw [el] at h1
    rw [ei] at h2
    exact (withinDistance_iff_value hx hy hr).mpr (hiff.mpr ⟨h1, h2⟩)

/-- Una propiedad de todos los valores de una cola de la sucesión. -/
def TailProperty (q N : ZFSet.{u}) (P : ZFSet.{u} → Prop) : Prop :=
  ∀ n : ZFSet.{u}, n ∈ omegaTA → NatLETA N n →
    ∀ x : ZFSet.{u}, SequenceValue q n x → P x

theorem tailProperty_iff {q N : ZFSet.{u}} {P R : ZFSet.{u} → Prop}
    (hq : q ∈ rationalSequences)
    (h : ∀ x : ZFSet.{u}, x ∈ rationalsTA → (P x ↔ R x)) :
    TailProperty q N P ↔ TailProperty q N R := by
  constructor
  · intro hp n hn hN x hx
    exact (h x (sequenceValue_mem hq hx)).mp (hp n hn hN x hx)
  · intro hr n hn hN x hx
    exact (h x (sequenceValue_mem hq hx)).mpr (hr n hn hN x hx)

/-- Plantilla cuantificada para las tres lecturas de convergencia. -/
def ConvergesBy (R : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (q l : ZFSet.{u}) : Prop :=
  q ∈ rationalSequences ∧ l ∈ rationalsTA ∧
    ∀ e : ZFSet.{u}, e ∈ rationalsTA → RatLT ratZero e →
      ∃ N : ZFSet.{u}, N ∈ omegaTA ∧ TailProperty q N (fun x => R x l e)

/-- TA-DEF-00109: la convergencia sólo cuantifica sobre precisiones racionales. -/
def RationalConverges (q l : ZFSet.{u}) : Prop :=
  ConvergesBy WithinDistance q l

/-- TA-NOT-00019: notación local de convergencia racional. -/
scoped infix:50 " ⟶ℚ " => RationalConverges

theorem TA_NOT_00019_convergence_notation_iff {q l : ZFSet.{u}} :
    (q ⟶ℚ l) ↔ RationalConverges q l := Iff.rfl

def RationalConvergent (q : ZFSet.{u}) : Prop :=
  ∃ l : ZFSet.{u}, RationalConverges q l

def ConvergesAbsolute (q l : ZFSet.{u}) : Prop :=
  ConvergesBy WithinAbsolute q l

def ConvergesWindow (q l : ZFSet.{u}) : Prop :=
  ConvergesBy WithinWindow q l

theorem convergesBy_iff {q l : ZFSet.{u}}
    {R S : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop}
    (h : ∀ x y e : ZFSet.{u}, x ∈ rationalsTA → y ∈ rationalsTA →
      e ∈ rationalsTA → RatLT ratZero e → (R x y e ↔ S x y e)) :
    ConvergesBy R q l ↔ ConvergesBy S q l := by
  constructor
  · rintro ⟨hq, hl, hc⟩
    refine ⟨hq, hl, ?_⟩
    intro e he hp
    obtain ⟨N, hN, ht⟩ := hc e he hp
    exact ⟨N, hN, (tailProperty_iff hq (fun x hx => h x l e hx hl he hp)).mp ht⟩
  · rintro ⟨hq, hl, hc⟩
    refine ⟨hq, hl, ?_⟩
    intro e he hp
    obtain ⟨N, hN, ht⟩ := hc e he hp
    exact ⟨N, hN, (tailProperty_iff hq (fun x hx => h x l e hx hl he hp)).mpr ht⟩

/-- TA-PRO-00111: se conserva el mismo índice N en las tres formulaciones. -/
theorem TA_PRO_00111_convergence_equivalences {q l : ZFSet.{u}} :
    (RationalConverges q l ↔ ConvergesAbsolute q l) ∧
    (RationalConverges q l ↔ ConvergesWindow q l) :=
  ⟨convergesBy_iff (fun _ _ _ _ _ _ _ => withinDistance_iff_absolute),
    convergesBy_iff (fun _ _ _ hx hy he hp => withinDistance_iff_window hx hy he hp)⟩

/-- TA-PRO-00112: las constantes convergen, con índice N=0. -/
theorem TA_PRO_00112_constant_converges {c : ZFSet.{u}} (hc : c ∈ rationalsTA) :
    RationalConverges (constantSequence c) c := by
  refine ⟨constantSequence_mem hc, hc, ?_⟩
  intro e _he hp
  refine ⟨(∅ : ZFSet.{u}), omegaTA_isInductive.1, ?_⟩
  intro n hn _ x hx
  have ex := (constantSequence_value_iff hc hn).mp hx
  subst x
  exact withinDistance_self hc hp

/-- TA-THM-00058: unicidad del límite, sin hipótesis global de em. -/
theorem TA_THM_00058_rational_limit_unique {q l m : ZFSet.{u}}
    (hl : RationalConverges q l) (hm : RationalConverges q m) : l = m := by
  have hq := hl.1
  have hlQ := hl.2.1
  have hmQ := hm.2.1
  have hcontr : l ≠ m → False := by
    intro hne
    obtain ⟨d, hd, _⟩ := distance_exists_unique hlQ hmQ
    have hdp : RatLT ratZero d :=
      ⟨distance_nonnegative hd, fun h => hne ((distance_zero_iff hlQ hmQ hd).mp h.symm)⟩
    obtain ⟨e, heQ, hep, hdouble⟩ := positive_half (distance_mem hd) hdp
    obtain ⟨Nl, hNl, htL⟩ := hl.2.2 e heQ hep
    obtain ⟨Nm, hNm, htM⟩ := hm.2.2 e heQ hep
    obtain ⟨n, hn, hln, hmn⟩ := common_upper_index hNl hNm
    obtain ⟨x, ⟨hxQ, hx⟩, _⟩ := sequenceValue_exists_unique hq hn
    have hxl := htL n hn hln x hx
    have hxm := htM n hn hmn x hx
    have hld := withinDistance_triangle hlQ hxQ hmQ heQ hdouble
      (withinDistance_symm hxQ hlQ hxl) hxm
    have hbad := (withinDistance_iff_value hlQ hmQ hd).mp hld
    exact hbad.2 rfl
  rcases TA_PRO_00172_rational_trichotomy hlQ hmQ with hlt | he | hgt
  · exact (hcontr hlt.2).elim
  · exact he
  · exact (hcontr (fun e => hgt.2 e.symm)).elim

/-- Los racionales estrictamente positivos forman un conjunto por Separación. -/
def positiveRationals : ZFSet.{u} :=
  ZFSet.sep (fun e => RatLT ratZero e) rationalsTA

theorem mem_positiveRationals_iff {e : ZFSet.{u}} :
    e ∈ positiveRationals ↔ e ∈ rationalsTA ∧ RatLT ratZero e :=
  ZFSet.mem_sep

/-- Módulo conjuntista de convergencia, sin exigencia de computabilidad. -/
def IsConvergenceModulus (q l mu : ZFSet.{u}) : Prop :=
  q ∈ rationalSequences ∧ l ∈ rationalsTA ∧
    mu ∈ functionSpace positiveRationals omegaTA ∧
    ∀ e N : ZFSet.{u}, e ∈ positiveRationals →
      FunctionValue positiveRationals omegaTA mu e N →
      TailProperty q N (fun x => WithinDistance x l e)

theorem convergence_of_modulus {q l mu : ZFSet.{u}}
    (h : IsConvergenceModulus q l mu) : RationalConverges q l := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro e he hep
  have he' := mem_positiveRationals_iff.mpr ⟨he, hep⟩
  obtain ⟨N, ⟨hN, hv⟩, _⟩ := functionValue_exists_unique h.2.2.1 he'
  exact ⟨N, hN, h.2.2.2 e N he' hv⟩

/-- Mínimo natural de un predicado habitado, con em explícito.
    Se usan códigos locales y buena ordenación de los naturales,
    sin importar la capa abstracta posterior a Q. -/
theorem least_natural_index
    (em : ∀ p : Prop, p ∨ ¬p)
    (P : ZFSet.{u} → Prop)
    (hExists : ∃ n : ZFSet.{u}, n ∈ omegaTA ∧ P n) :
    ∃ m : ZFSet.{u}, m ∈ omegaTA ∧ P m ∧
      ∀ n : ZFSet.{u}, n ∈ omegaTA → P n → NatLETA m n := by
  have hleast : ∀ k : Nat, P (natEncode k) →
      ∃ j : Nat, P (natEncode j) ∧ ∀ i : Nat, P (natEncode i) → j ≤ i := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro hk
        rcases em (∃ j : Nat, j < k ∧ P (natEncode j)) with h | h
        · obtain ⟨j, hjk, hj⟩ := h
          exact ih j hjk hj
        · refine ⟨k, hk, ?_⟩
          intro i hi
          rcases Nat.lt_trichotomy i k with hlt | he | hgt
          · exact (h ⟨i, hlt, hi⟩).elim
          · rw [he]
            exact Nat.le_refl k
          · exact Nat.le_of_lt hgt
  obtain ⟨n, hn, hp⟩ := hExists
  obtain ⟨k, rfl⟩ := exists_natEncode_eq_of_mem hn
  obtain ⟨j, hj, hmin⟩ := hleast k hp
  refine ⟨natEncode j, natEncode_mem_omegaTA j, hj, ?_⟩
  intro n hn hpn
  obtain ⟨i, rfl⟩ := exists_natEncode_eq_of_mem hn
  exact (NatLETA_natEncode_iff j i).mpr (hmin i hpn)

/-- El menor índice que sirve para una precisión fija. -/
def MinimalTailIndex (q l e N : ZFSet.{u}) : Prop :=
  TailProperty q N (fun x => WithinDistance x l e) ∧
    ∀ M : ZFSet.{u}, M ∈ omegaTA →
      TailProperty q M (fun x => WithinDistance x l e) → NatLETA N M

theorem minimalTailIndex_exists_unique
    (em : ∀ p : Prop, p ∨ ¬p)
    {q l e : ZFSet.{u}} (h : RationalConverges q l)
    (he : e ∈ positiveRationals) :
    ∃! N : ZFSet.{u}, N ∈ omegaTA ∧ MinimalTailIndex q l e N := by
  have he' := mem_positiveRationals_iff.mp he
  obtain ⟨N, hN, ht, hmin⟩ := least_natural_index em
    (fun k => TailProperty q k (fun x => WithinDistance x l e))
    (h.2.2 e he'.1 he'.2)
  refine ⟨N, ⟨hN, ht, hmin⟩, ?_⟩
  intro M hM
  exact natLE_antisymm_local hM.1 hN
    (hM.2.2 N hN ht) (hmin M hM.1 hM.2.1)

/-- El módulo mínimo se forma por separación, no por selección global. -/
def minimalConvergenceModulus (q l : ZFSet.{u}) : ZFSet.{u} :=
  functionOfRelation positiveRationals omegaTA (MinimalTailIndex q l)

theorem minimalConvergenceModulus_mem
    (em : ∀ p : Prop, p ∨ ¬p)
    {q l : ZFSet.{u}} (h : RationalConverges q l) :
    minimalConvergenceModulus q l ∈ functionSpace positiveRationals omegaTA :=
  functionOfRelation_mem (fun _ he => minimalTailIndex_exists_unique em h he)

theorem minimalConvergenceModulus_isModulus
    (em : ∀ p : Prop, p ∨ ¬p)
    {q l : ZFSet.{u}} (h : RationalConverges q l) :
    IsConvergenceModulus q l (minimalConvergenceModulus q l) := by
  refine ⟨h.1, h.2.1, minimalConvergenceModulus_mem em h, ?_⟩
  intro e N _he hv
  have hval := (functionOfRelation_value_iff (R := MinimalTailIndex q l)).mp hv
  exact hval.2.2.1

theorem minimalConvergenceModulus_le
    {q l mu e N M : ZFSet.{u}}
    (hmu : IsConvergenceModulus q l mu) (he : e ∈ positiveRationals)
    (hN : FunctionValue positiveRationals omegaTA (minimalConvergenceModulus q l) e N)
    (hM : FunctionValue positiveRationals omegaTA mu e M) :
    NatLETA N M := by
  have hval := (functionOfRelation_value_iff (R := MinimalTailIndex q l)).mp hN
  exact hval.2.2.2 M (functionValue_mem hmu.2.2.1 hM) (hmu.2.2.2 e M he hM)

/-- La condición de minimalidad caracteriza un único triple de función.
    No se afirma que el módulo obtenido sea computable. -/
theorem minimalConvergenceModulus_exists_unique
    (em : ∀ p : Prop, p ∨ ¬p)
    {q l : ZFSet.{u}} (h : RationalConverges q l) :
    ∃! mu : ZFSet.{u}, mu ∈ functionSpace positiveRationals omegaTA ∧
      ∀ e N : ZFSet.{u}, e ∈ positiveRationals →
        FunctionValue positiveRationals omegaTA mu e N → MinimalTailIndex q l e N := by
  have hf := minimalConvergenceModulus_mem em h
  refine ⟨minimalConvergenceModulus q l, ⟨hf, ?_⟩, ?_⟩
  · intro e N _he hN
    exact ((functionOfRelation_value_iff (R := MinimalTailIndex q l)).mp hN).2.2
  · intro mu hmu
    apply (function_eq_iff_values hmu.1 hf).mpr
    intro e he M N hM hN
    have hm := hmu.2 e M he hM
    have hn := ((functionOfRelation_value_iff (R := MinimalTailIndex q l)).mp hN).2.2
    have hmNat := functionValue_mem hmu.1 hM
    have hnNat := functionValue_mem hf hN
    exact natLE_antisymm_local hmNat hnNat
      (hm.2 N hnNat hn.1) (hn.2 M hmNat hm.1)

end TratadoAnalisis.Cauchy.RationalConvergence
