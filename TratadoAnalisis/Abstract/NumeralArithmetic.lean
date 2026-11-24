import TratadoAnalisis.Naturals.OrderedArithmetic
import TratadoAnalisis.Abstract.PrimeLocalRefinement0009
import TratadoAnalisis.Abstract.AbsoluteValue

/-!
# Aritmética y orden del grafo canónico de numerales

TA-PRO-00069. Se conservan el portador omegaTA, los grafos de suma y
producto naturales y CanonicalNumeralGraphManual. Los códigos Nat son
testigos locales para las inducciones aritméticas, no el portador del
grafo. Todos los valores de las operaciones están en el cuerpo.
No se construye una función de numerales por elección.
-/

namespace TratadoAnalisis.AbstractCompleteness.NumeralArithmetic

universe u

open TratadoAnalisis.AbstractCompleteness.Manual0008
open TratadoAnalisis.AbstractCompleteness.Density0009
open TratadoAnalisis.AbstractCompleteness.AbsoluteValue
open TratadoAnalisis.Dedekind.FieldPredicates
open TratadoAnalisis.Naturals.Foundational
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Naturals.ArithmeticBridge
open TratadoAnalisis.Naturals.OrderedArithmetic
open TratadoAnalisis.Integers.Order

variable {F zero one : ZFSet.{u}}
variable {add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop}
variable {le : ZFSet.{u} → ZFSet.{u} → Prop}

/-- La notación de valor es sólo pertenencia al grafo ya construido. -/
abbrev NumeralValue (F zero one : ZFSet.{u})
    (add : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (n x : ZFSet.{u}) : Prop :=
  ZFSet.pair n x ∈ CanonicalNumeralGraphManual F zero one add

theorem numeral_graph_isFunc
    (h : IsOrderedFieldFoundational F zero one add mul le) :
    IsFuncFoundational omegaTA F (CanonicalNumeralGraphManual F zero one add) :=
  canonicalNumeralGraph_isFunc_manual F zero one add h.1.1.2.1 h.1.2.2.1 h.1.1.1

theorem numeral_mem
    (h : IsOrderedFieldFoundational F zero one add mul le)
    {n x : ZFSet.{u}} (hx : NumeralValue F zero one add n x) : x ∈ F :=
  funcFoundational_value_mem (numeral_graph_isFunc h) hx

theorem numeral_exists
    (h : IsOrderedFieldFoundational F zero one add mul le)
    {n : ZFSet.{u}} (hn : n ∈ omegaTA) :
    ∃ x : ZFSet.{u}, x ∈ F ∧ NumeralValue F zero one add n x := by
  obtain ⟨x, hx, _⟩ := (numeral_graph_isFunc h).2 n hn
  exact ⟨x, hx⟩

theorem numeral_unique
    (h : IsOrderedFieldFoundational F zero one add mul le)
    {n x y : ZFSet.{u}} (hn : n ∈ omegaTA)
    (hx : NumeralValue F zero one add n x)
    (hy : NumeralValue F zero one add n y) : x = y :=
  funcFoundational_pair_value_unique (numeral_graph_isFunc h) hn hx hy

theorem numeral_zero
    (h : IsOrderedFieldFoundational F zero one add mul le)
    {x : ZFSet.{u}} (hx : NumeralValue F zero one add ∅ x) : x = zero :=
  numeral_unique h omegaTA_isInductive.1 hx
    (canonicalNumeralGraph_zero_manual F zero one add h.1.1.2.1)

theorem numeral_succ_relation
    (h : IsOrderedFieldFoundational F zero one add mul le)
    {n x y : ZFSet.{u}} (hn : n ∈ omegaTA)
    (hx : NumeralValue F zero one add n x)
    (hy : NumeralValue F zero one add (succ n) y) : add x one y := by
  have hxF := numeral_mem h hx
  obtain ⟨w, ⟨hwF, hw⟩, _⟩ := h.1.1.1 x hxF one h.1.2.2.1
  have hnw := canonicalNumeralGraph_succ_manual F zero one add
    h.1.1.2.1 h.1.2.2.1 h.1.1.1 hn hx hxF hwF hw
  have e := numeral_unique h (TA_PRO_00022_succ_closed hn) hnw hy
  rw [← e]
  exact hw

/-- TA-PRO-00069(1). -/
theorem numeral_one
    (h : IsOrderedFieldFoundational F zero one add mul le) :
    NumeralValue F zero one add (succ (∅ : ZFSet.{u})) one := by
  have hz := h.1.1.2.1
  have ho := h.1.2.2.1
  exact canonicalNumeralGraph_succ_manual F zero one add hz ho h.1.1.1
    omegaTA_isInductive.1 (canonicalNumeralGraph_zero_manual F zero one add hz)
    hz ho (h.1.1.2.2.2.2.1 one ho).2

/-- Preservación de la suma sobre códigos suministrados. -/
theorem numeral_add_codes
    (h : IsOrderedFieldFoundational F zero one add mul le)
    (m n : Nat) {x y z : ZFSet.{u}}
    (hx : NumeralValue F zero one add (natEncode m) x)
    (hy : NumeralValue F zero one add (natEncode n) y)
    (hz : NumeralValue F zero one add (natEncode (m + n)) z) :
    add x y z := by
  induction n generalizing y z with
  | zero =>
      have ey := numeral_zero h hy
      change NumeralValue F zero one add (natEncode m) z at hz
      have ez := numeral_unique h (natEncode_mem_omegaTA m) hz hx
      rw [ey, ez]
      exact (h.1.1.2.2.2.2.1 x (numeral_mem h hx)).1
  | succ n ih =>
      obtain ⟨y0, hy0F, hy0⟩ := numeral_exists h (natEncode_mem_omegaTA n)
      obtain ⟨z0, hz0F, hz0⟩ := numeral_exists h (natEncode_mem_omegaTA (m + n))
      have hxy0 := ih hy0 hz0
      have hyS : NumeralValue F zero one add (succ (natEncode n)) y := hy
      have hzS : NumeralValue F zero one add (succ (natEncode (m + n))) z := by
        rw [Nat.add_succ, natEncode_succ] at hz
        exact hz
      have hyStep := numeral_succ_relation h (natEncode_mem_omegaTA n) hy0 hyS
      have hzStep := numeral_succ_relation h (natEncode_mem_omegaTA (m + n)) hz0 hzS
      have hxF := numeral_mem h hx
      have hyF := numeral_mem h hy
      obtain ⟨w, ⟨_, hw⟩, _⟩ := h.1.1.1 x hxF y hyF
      have e := h.1.1.2.2.1 x y0 one z0 z y w hxF hy0F h.1.2.2.1
        hxy0 hzStep hyStep hw
      rw [e]
      exact hw

/-- TA-PRO-00069(2), sobre el grafo de suma de los naturales conjuntistas. -/
theorem numeral_add
    (h : IsOrderedFieldFoundational F zero one add mul le)
    {m n k x y z : ZFSet.{u}}
    (hm : m ∈ omegaTA) (hn : n ∈ omegaTA) (hadd : NatAddRel m n k)
    (hx : NumeralValue F zero one add m x)
    (hy : NumeralValue F zero one add n y)
    (hz : NumeralValue F zero one add k z) : add x y z := by
  obtain ⟨M, rfl⟩ := exists_natEncode_eq_of_mem hm
  obtain ⟨N, rfl⟩ := exists_natEncode_eq_of_mem hn
  have e := natAddGraph_natEncode_value_iff.mp hadd
  subst k
  exact numeral_add_codes h M N hx hy hz

/-- Preservación del producto sobre códigos suministrados. -/
theorem numeral_mul_codes
    (h : IsOrderedFieldFoundational F zero one add mul le)
    (m n : Nat) {x y z : ZFSet.{u}}
    (hx : NumeralValue F zero one add (natEncode m) x)
    (hy : NumeralValue F zero one add (natEncode n) y)
    (hz : NumeralValue F zero one add (natEncode (m * n)) z) :
    mul x y z := by
  induction n generalizing y z with
  | zero =>
      have ey := numeral_zero h hy
      have ez := numeral_zero h hz
      have hxF := numeral_mem h hx
      obtain ⟨w, ⟨hwF, hw⟩, _⟩ := h.1.2.1 x hxF zero h.1.1.2.1
      have ew := rel_mul_zero_manual F zero one add mul h.1 x w hxF hwF hw
      rw [ey, ez]
      rw [ew] at hw
      exact hw
  | succ n ih =>
      obtain ⟨y0, hy0F, hy0⟩ := numeral_exists h (natEncode_mem_omegaTA n)
      obtain ⟨z0, hz0F, hz0⟩ := numeral_exists h (natEncode_mem_omegaTA (m * n))
      have hxy0 := ih hy0 hz0
      have hyS : NumeralValue F zero one add (succ (natEncode n)) y := hy
      have hyStep := numeral_succ_relation h (natEncode_mem_omegaTA n) hy0 hyS
      have hzSum : NumeralValue F zero one add (natEncode (m * n + m)) z := by
        rw [Nat.mul_succ] at hz
        exact hz
      have hsum := numeral_add_codes h (m * n) m hz0 hx hzSum
      have hxF := numeral_mem h hx
      have hyF := numeral_mem h hy
      obtain ⟨w, ⟨_, hw⟩, _⟩ := h.1.2.1 x hxF y hyF
      have e := h.1.2.2.2.2.2.2.1.1 x y0 one y w z0 x z
        hxF hy0F h.1.2.2.1 hyStep hw hxy0
        (h.1.2.2.2.2.2.1 x hxF).1 hsum
      rw [← e]
      exact hw

/-- TA-PRO-00069(3), sobre el grafo del producto natural. -/
theorem numeral_mul
    (h : IsOrderedFieldFoundational F zero one add mul le)
    {m n k x y z : ZFSet.{u}}
    (hm : m ∈ omegaTA) (hn : n ∈ omegaTA) (hmul : NatMulRel m n k)
    (hx : NumeralValue F zero one add m x)
    (hy : NumeralValue F zero one add n y)
    (hz : NumeralValue F zero one add k z) : mul x y z := by
  obtain ⟨M, rfl⟩ := exists_natEncode_eq_of_mem hm
  obtain ⟨N, rfl⟩ := exists_natEncode_eq_of_mem hn
  have e := natMulGraph_natEncode_value_iff.mp hmul
  subst k
  exact numeral_mul_codes h M N hx hy hz

theorem numeral_step_strict
    (h : IsOrderedFieldFoundational F zero one add mul le)
    {n x y : ZFSet.{u}} (hn : n ∈ omegaTA)
    (hx : NumeralValue F zero one add n x)
    (hy : NumeralValue F zero one add (succ n) y) :
    StrictFromLeManual le x y := by
  have hxF := numeral_mem h hx
  have hyF := numeral_mem h hy
  exact rel_add_left_strict_mono_manual F zero one add mul le h
    zero one x x y h.1.1.2.1 h.1.2.2.1 hxF hxF hyF
    (ordered_zero_lt_one_manual F zero one add mul le h)
    (h.1.1.2.2.2.2.1 x hxF).1 (numeral_succ_relation h hn hx hy)

/-- Transitividad de ≤ con < a su derecha, sin tercero excluido. -/
theorem le_strict_trans
    (h : IsOrderedFieldFoundational F zero one add mul le)
    {x y z : ZFSet.{u}} (hx : x ∈ F) (hy : y ∈ F) (hz : z ∈ F)
    (hxy : le x y) (hyz : StrictFromLeManual le y z) :
    StrictFromLeManual le x z := by
  refine ⟨h.2.1.2.2.1 x y z hx hy hz hxy hyz.1, ?_⟩
  intro e
  have hzy : le z y := by
    rw [← e]
    exact hxy
  exact hyz.2 (h.2.1.2.1 y z hy hz hyz.1 hzy)

theorem numeral_nonnegative_codes
    (h : IsOrderedFieldFoundational F zero one add mul le)
    (n : Nat) {x : ZFSet.{u}}
    (hx : NumeralValue F zero one add (natEncode n) x) : le zero x := by
  induction n generalizing x with
  | zero =>
      rw [numeral_zero h hx]
      exact h.2.1.1 zero h.1.1.2.1
  | succ n ih =>
      obtain ⟨y, hyF, hy⟩ := numeral_exists h (natEncode_mem_omegaTA n)
      exact (le_strict_trans h h.1.1.2.1 hyF (numeral_mem h hx) (ih hy)
        (numeral_step_strict h (natEncode_mem_omegaTA n) hy hx)).1

theorem numeral_nonnegative
    (h : IsOrderedFieldFoundational F zero one add mul le)
    {n x : ZFSet.{u}} (hn : n ∈ omegaTA)
    (hx : NumeralValue F zero one add n x) : le zero x := by
  obtain ⟨N, rfl⟩ := exists_natEncode_eq_of_mem hn
  exact numeral_nonnegative_codes h N hx

theorem numeral_positive_of_nonzero
    (h : IsOrderedFieldFoundational F zero one add mul le)
    {n x : ZFSet.{u}} (hn : n ∈ omegaTA) (hne : n ≠ ∅)
    (hx : NumeralValue F zero one add n x) :
    StrictFromLeManual le zero x := by
  obtain ⟨N, rfl⟩ := exists_natEncode_eq_of_mem hn
  cases N with
  | zero => exact (hne rfl).elim
  | succ N =>
      obtain ⟨y, hyF, hy⟩ := numeral_exists h (natEncode_mem_omegaTA N)
      exact le_strict_trans h h.1.1.2.1 hyF (numeral_mem h hx)
        (numeral_nonnegative_codes h N hy)
        (numeral_step_strict h (natEncode_mem_omegaTA N) hy hx)

/-- TA-PRO-00069(5), preservación del orden no estricto. -/
theorem numeral_le_of_nat_le
    (h : IsOrderedFieldFoundational F zero one add mul le)
    {m n x y : ZFSet.{u}} (hmn : NatLETA m n)
    (hx : NumeralValue F zero one add m x)
    (hy : NumeralValue F zero one add n y) : le x y := by
  obtain ⟨hm, _, k, hk, hkadd⟩ := hmn
  obtain ⟨d, hdF, hd⟩ := numeral_exists h hk
  have hxF := numeral_mem h hx
  have hadd := numeral_add h hm hk hkadd hx hd hy
  exact h.2.2.1 zero d x x y h.1.1.2.1 hdF hxF
    (numeral_nonnegative h hk hd) (h.1.1.2.2.2.2.1 x hxF).2
    (add_commutes h hxF hdF hadd)

/-- TA-PRO-00069(4), preservación del orden estricto. -/
theorem numeral_lt_of_nat_lt
    (h : IsOrderedFieldFoundational F zero one add mul le)
    {m n x y : ZFSet.{u}}
    (hmn : StrictFromLeManual NatLETA m n)
    (hx : NumeralValue F zero one add m x)
    (hy : NumeralValue F zero one add n y) :
    StrictFromLeManual le x y := by
  obtain ⟨hm, _, k, hk, hkadd⟩ := hmn.1
  have hkne : k ≠ ∅ := by
    intro e
    subst k
    have en := funcFoundational_pair_value_unique natAddGraph_isFunc
      (mem_cartesianProductFoundational.mpr ⟨hm, omegaTA_isInductive.1⟩)
      hkadd (natAddGraph_zero hm)
    exact hmn.2 en.symm
  obtain ⟨d, hdF, hd⟩ := numeral_exists h hk
  have hxF := numeral_mem h hx
  have hyF := numeral_mem h hy
  exact rel_add_left_strict_mono_manual F zero one add mul le h
    zero d x x y h.1.1.2.1 hdF hxF hxF hyF
    (numeral_positive_of_nonzero h hk hkne hd)
    (h.1.1.2.2.2.2.1 x hxF).1 (numeral_add h hm hk hkadd hx hd hy)

/-- TA-PRO-00069(5), inyectividad del grafo canónico de numerales. -/
theorem numeral_injective
    (h : IsOrderedFieldFoundational F zero one add mul le)
    {m n x y : ZFSet.{u}} (hm : m ∈ omegaTA) (hn : n ∈ omegaTA)
    (hx : NumeralValue F zero one add m x)
    (hy : NumeralValue F zero one add n y) (e : x = y) : m = n := by
  rcases (TA_PRO_00170_nat_trichotomy hm hn).1 with hlt | he | hgt
  · exact ((numeral_lt_of_nat_lt h hlt hx hy).2 e).elim
  · exact he
  · exact ((numeral_lt_of_nat_lt h hgt hy hx).2 e.symm).elim

/-- TA-PRO-00069(5), preservación y reflexión del orden. -/
theorem numeral_order_iff
    (h : IsOrderedFieldFoundational F zero one add mul le)
    {m n x y : ZFSet.{u}} (hm : m ∈ omegaTA) (hn : n ∈ omegaTA)
    (hx : NumeralValue F zero one add m x)
    (hy : NumeralValue F zero one add n y) :
    NatLETA m n ↔ le x y := by
  constructor
  · exact fun hmn => numeral_le_of_nat_le h hmn hx hy
  · intro hxy
    rcases (TA_PRO_00170_nat_trichotomy hm hn).1 with hlt | he | hgt
    · exact hlt.1
    · rw [he]
      exact TA_THM_00020_nat_total_order.1 n hn
    · have hyx := numeral_lt_of_nat_lt h hgt hy hx
      exact (hyx.2 (h.2.1.2.1 y x (numeral_mem h hy) (numeral_mem h hx)
        hyx.1 hxy)).elim

/-- TA-PRO-00069, los cinco apartados editoriales en un único enunciado
    sobre el grafo canónico, sin parámetros de elección o tercero excluido. -/
theorem TA_PRO_00069_numeral_arithmetic_order
    (h : IsOrderedFieldFoundational F zero one add mul le) :
    NumeralValue F zero one add (succ (∅ : ZFSet.{u})) one ∧
    (∀ m n k x y z : ZFSet.{u}, m ∈ omegaTA → n ∈ omegaTA →
      NatAddRel m n k → NumeralValue F zero one add m x →
      NumeralValue F zero one add n y → NumeralValue F zero one add k z →
      add x y z) ∧
    (∀ m n k x y z : ZFSet.{u}, m ∈ omegaTA → n ∈ omegaTA →
      NatMulRel m n k → NumeralValue F zero one add m x →
      NumeralValue F zero one add n y → NumeralValue F zero one add k z →
      mul x y z) ∧
    (∀ m n x y : ZFSet.{u}, StrictFromLeManual NatLETA m n →
      NumeralValue F zero one add m x → NumeralValue F zero one add n y →
      StrictFromLeManual le x y) ∧
    (∀ m n x y : ZFSet.{u}, m ∈ omegaTA → n ∈ omegaTA →
      NumeralValue F zero one add m x → NumeralValue F zero one add n y →
      ((x = y → m = n) ∧ (NatLETA m n ↔ le x y))) := by
  refine ⟨numeral_one h, ?_, ?_, ?_, ?_⟩
  · intro m n k x y z hm hn hk hx hy hz
    exact numeral_add h hm hn hk hx hy hz
  · intro m n k x y z hm hn hk hx hy hz
    exact numeral_mul h hm hn hk hx hy hz
  · intro m n x y hmn hx hy
    exact numeral_lt_of_nat_lt h hmn hx hy
  · intro m n x y hm hn hx hy
    exact ⟨numeral_injective h hm hn hx hy, numeral_order_iff h hm hn hx hy⟩

end TratadoAnalisis.AbstractCompleteness.NumeralArithmetic
