import TratadoAnalisis.Rationals.DifferenceOrder

/-!
# Especialización racional del valor absoluto de TA-DEF-00071

La relación de valor absoluto se obtiene por el máximo de x y -x.
La prueba usa exclusivamente el cuerpo racional conjuntista y los
lemas de orden ya disponibles antes de Dedekind. La equivalencia
con la interfaz abstracta de v0.1.2 se certifica en un puente
separado que no es importado por Cauchy.
-/

namespace TratadoAnalisis.Rationals.AbsoluteValue

universe u

open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.OrderedFieldCompatibility
open TratadoAnalisis.Rationals.NoSupremumSqrtTwo
open TratadoAnalisis.Rationals.Signs
open TratadoAnalisis.Rationals.DifferenceOrder

def RatAbs (x a : ZFSet.{u}) : Prop :=
  ∃ nx : ZFSet.{u}, RatNeg x nx ∧ a ∈ rationalsTA ∧
    (a = x ∨ a = nx) ∧ RatLE x a ∧ RatLE nx a

theorem ratAbs_mem {x a : ZFSet.{u}} (ha : RatAbs x a) :
    x ∈ rationalsTA ∧ a ∈ rationalsTA := by
  obtain ⟨nx, hn, haQ, _, _, _⟩ := ha
  exact ⟨(mem_ratNegGraph.mp hn).1, haQ⟩

theorem ratNeg_zero : RatNeg (ratZero : ZFSet.{u}) ratZero :=
  ratNeg_of_add_zero ratZero_mem_rationalsTA ratZero_mem_rationalsTA
    (zero_add_rel ratZero_mem_rationalsTA)

theorem ratAbs_upper_iff {x nx a r : ZFSet.{u}}
    (hn : RatNeg x nx) (ha : RatAbs x a) (hr : r ∈ rationalsTA) :
    RatLE a r ↔ RatLE x r ∧ RatLE nx r := by
  obtain ⟨n, hneg, haQ, hcase, hxle, hnle⟩ := ha
  have hx := (mem_ratNegGraph.mp hn).1
  have hnx := funcFoundational_value_mem ratNegGraph_isFunc hn
  have he := RatNeg_unique hx hneg hn
  subst n
  constructor
  · intro h
    exact ⟨ratLE_trans hx haQ hr hxle h,
      ratLE_trans hnx haQ hr hnle h⟩
  · rintro ⟨hx', hn'⟩
    rcases hcase with e | e
    · rw [e]
      exact hx'
    · rw [e]
      exact hn'

theorem ratAbs_unique {x a b : ZFSet.{u}}
    (ha : RatAbs x a) (hb : RatAbs x b) : a = b := by
  have haQ := (ratAbs_mem ha).2
  have hbQ := (ratAbs_mem hb).2
  have ha' := ha
  obtain ⟨nx, hn, _, _, _, _⟩ := ha'
  exact ratLE_antisymm haQ hbQ
    ((ratAbs_upper_iff hn ha hbQ).mpr
      ((ratAbs_upper_iff hn hb hbQ).mp (ratLE_refl hbQ)))
    ((ratAbs_upper_iff hn hb haQ).mpr
      ((ratAbs_upper_iff hn ha haQ).mp (ratLE_refl haQ)))

/-- Existencia y unicidad de max{x,-x}; no se elige una función de Lean. -/
theorem ratAbs_exists_unique {x : ZFSet.{u}} (hx : x ∈ rationalsTA) :
    ∃! a : ZFSet.{u}, RatAbs x a := by
  obtain ⟨nx, hnx, hn⟩ := ratNeg_exists hx
  rcases ratLE_total hx hnx with h | h
  · have ha : RatAbs x nx := ⟨nx, hn, hnx, Or.inr rfl, h, ratLE_refl hnx⟩
    exact ⟨nx, ha, fun _ hb => ratAbs_unique hb ha⟩
  · have ha : RatAbs x x := ⟨nx, hn, hx, Or.inl rfl, ratLE_refl hx, h⟩
    exact ⟨x, ha, fun _ hb => ratAbs_unique hb ha⟩

theorem ratAbs_nonnegative {x a : ZFSet.{u}} (ha : RatAbs x a) :
    RatLE ratZero a := by
  obtain ⟨nx, hn, haQ, _, hxle, hnle⟩ := ha
  have hx := (mem_ratNegGraph.mp hn).1
  have hnx := funcFoundational_value_mem ratNegGraph_isFunc hn
  rcases ratLE_total ratZero_mem_rationalsTA hx with h | h
  · exact ratLE_trans ratZero_mem_rationalsTA hx haQ h hxle
  · exact ratLE_trans ratZero_mem_rationalsTA hnx haQ
      (ratNeg_le_reverse hx ratZero_mem_rationalsTA hn ratNeg_zero h) hnle

theorem ratAbs_zero_iff {x a : ZFSet.{u}} (ha : RatAbs x a) :
    a = ratZero ↔ x = ratZero := by
  obtain ⟨nx, hn, _, hcase, hxle, hnle⟩ := ha
  have hx := (mem_ratNegGraph.mp hn).1
  have hnx := funcFoundational_value_mem ratNegGraph_isFunc hn
  constructor
  · intro e
    rw [e] at hxle hnle
    exact ratLE_antisymm hx ratZero_mem_rationalsTA hxle
      (ratNeg_le_reverse hnx ratZero_mem_rationalsTA
        (ratNeg_symm_rel hx hn) ratNeg_zero hnle)
  · intro e
    subst x
    have en := RatNeg_unique ratZero_mem_rationalsTA hn ratNeg_zero
    exact hcase.elim id (fun h => h.trans en)

theorem ratAbs_neg {x nx a b : ZFSet.{u}}
    (hn : RatNeg x nx) (ha : RatAbs x a) (hb : RatAbs nx b) : b = a := by
  obtain ⟨n, hn', haQ, hcase, hxle, hnle⟩ := ha
  have hx := (mem_ratNegGraph.mp hn).1
  have e := RatNeg_unique hx hn' hn
  subst n
  apply ratAbs_unique hb
  exact ⟨x, ratNeg_symm_rel hx hn, haQ, hcase.elim Or.inr Or.inl, hnle, hxle⟩

theorem ratAbs_of_nonnegative {x a : ZFSet.{u}} (ha : RatAbs x a)
    (h0x : RatLE ratZero x) : a = x := by
  have ha' := ha
  obtain ⟨nx, hn, _, _, _, _⟩ := ha'
  have hx := (mem_ratNegGraph.mp hn).1
  have hnx := funcFoundational_value_mem ratNegGraph_isFunc hn
  have hn0 := ratNeg_le_reverse ratZero_mem_rationalsTA hx ratNeg_zero hn h0x
  exact ratAbs_unique ha ⟨nx, hn, hx, Or.inl rfl, ratLE_refl hx,
    ratLE_trans hnx ratZero_mem_rationalsTA hx hn0 h0x⟩

theorem ratAbs_of_nonpositive {x nx a : ZFSet.{u}} (hn : RatNeg x nx)
    (ha : RatAbs x a) (hx0 : RatLE x ratZero) : a = nx := by
  have hx := (mem_ratNegGraph.mp hn).1
  have hnx := funcFoundational_value_mem ratNegGraph_isFunc hn
  have h0n := ratNeg_le_reverse hx ratZero_mem_rationalsTA hn ratNeg_zero hx0
  exact ratAbs_unique ha ⟨nx, hn, hnx, Or.inr rfl,
    ratLE_trans hx ratZero_mem_rationalsTA hnx hx0 h0n, ratLE_refl hnx⟩

theorem ratLE_lt_trans {x y z : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA) (hz : z ∈ rationalsTA)
    (hxy : RatLE x y) (hyz : RatLT y z) : RatLT x z := by
  refine ⟨ratLE_trans hx hy hz hxy hyz.1, ?_⟩
  intro e
  have hzy : RatLE z y := by
    rw [← e]
    exact hxy
  exact hyz.2 (ratLE_antisymm hy hz hyz.1 hzy)

theorem ratAbs_lt_iff {x nx a r : ZFSet.{u}}
    (hn : RatNeg x nx) (ha : RatAbs x a) (hr : r ∈ rationalsTA) :
    RatLT a r ↔ RatLT x r ∧ RatLT nx r := by
  obtain ⟨n, hneg, haQ, hcase, hxle, hnle⟩ := ha
  have hx := (mem_ratNegGraph.mp hn).1
  have hnx := funcFoundational_value_mem ratNegGraph_isFunc hn
  have he := RatNeg_unique hx hneg hn
  subst n
  constructor
  · intro h
    exact ⟨ratLE_lt_trans hx haQ hr hxle h, ratLE_lt_trans hnx haQ hr hnle h⟩
  · rintro ⟨h1, h2⟩
    rcases hcase with e | e
    · rw [e]
      exact h1
    · rw [e]
      exact h2

theorem ratAbs_lt_iff_symmetric {x a r nr : ZFSet.{u}}
    (ha : RatAbs x a) (hnr : RatNeg r nr) :
    RatLT a r ↔ RatLT nr x ∧ RatLT x r := by
  have ha' := ha
  obtain ⟨nx, hn, _, _, _, _⟩ := ha'
  have hx := (mem_ratNegGraph.mp hn).1
  have hnx := funcFoundational_value_mem ratNegGraph_isFunc hn
  have hr := (mem_ratNegGraph.mp hnr).1
  have hiff := TA_LEM_00020_clause2_neg_lt_iff hnx hr (ratNeg_symm_rel hx hn) hnr
  constructor
  · intro h
    have hh := (ratAbs_lt_iff hn ha hr).mp h
    exact ⟨hiff.mp hh.2, hh.1⟩
  · rintro ⟨h1, h2⟩
    exact (ratAbs_lt_iff hn ha hr).mpr ⟨h2, hiff.mpr h1⟩

theorem ratAdd_zero_right_rel {x : ZFSet.{u}} (hx : x ∈ rationalsTA) :
    RatAdd x ratZero x :=
  ratAdd_comm_rel ratZero_mem_rationalsTA hx (zero_add_rel hx)

/-- El opuesto de una suma es la suma de los opuestos. -/
theorem ratNeg_add {x nx y ny z w : ZFSet.{u}}
    (hnx : RatNeg x nx) (hny : RatNeg y ny)
    (hxy : RatAdd x y z) (hn : RatAdd nx ny w) : RatNeg z w := by
  have hx := (mem_ratNegGraph.mp hnx).1
  have hy := (mem_ratNegGraph.mp hny).1
  have hnxQ := funcFoundational_value_mem ratNegGraph_isFunc hnx
  have hnyQ := funcFoundational_value_mem ratNegGraph_isFunc hny
  have hz := funcFoundational_value_mem ratAddGraph_isFunc hxy
  have hw := funcFoundational_value_mem ratAddGraph_isFunc hn
  obtain ⟨t, htQ, ht⟩ := ratAdd_exists hnxQ hy
  obtain ⟨s, _, hs⟩ := ratAdd_exists htQ hnyQ
  have es : s = nx := ratAdd_assoc hnxQ hy hnyQ ht hs
    (ratAdd_neg_right_rel hy hny) (ratAdd_zero_right_rel hnxQ)
  obtain ⟨v, _, hv⟩ := ratAdd_exists hy hw
  have ev : s = v := ratAdd_assoc hy hnxQ hnyQ
    (ratAdd_comm_rel hnxQ hy ht) hs hn hv
  rw [← ev, es] at hv
  obtain ⟨p, _, hp⟩ := ratAdd_exists hz hw
  have ep := ratAdd_assoc hx hy hw hxy hp hv (ratAdd_neg_right_rel hx hnx)
  rw [ep] at hp
  exact ratNeg_of_add_zero hz hw hp

theorem ratAdd_pair_le {x y a b z s : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA)
    (ha : a ∈ rationalsTA) (hb : b ∈ rationalsTA)
    (hxa : RatLE x a) (hyb : RatLE y b)
    (hxy : RatAdd x y z) (hab : RatAdd a b s) : RatLE z s := by
  obtain ⟨t, ht, hay⟩ := ratAdd_exists ha hy
  exact ratLE_trans (funcFoundational_value_mem ratAddGraph_isFunc hxy) ht
    (funcFoundational_value_mem ratAddGraph_isFunc hab)
    (ratLE_add_compat hx ha hy hxa hxy hay)
    (ratLE_add_compat hy hb ha hyb (ratAdd_comm_rel ha hy hay)
      (ratAdd_comm_rel ha hb hab))

/-- TA-THM-00035, especialización independiente al cuerpo racional. -/
theorem ratAbs_triangle {x y z a b c s : ZFSet.{u}}
    (ha : RatAbs x a) (hb : RatAbs y b) (hc : RatAbs z c)
    (hxy : RatAdd x y z) (hab : RatAdd a b s) : RatLE c s := by
  obtain ⟨nx, hnx, haQ, _, hxle, hnxa⟩ := ha
  obtain ⟨ny, hny, hbQ, _, hyle, hnyb⟩ := hb
  have hx := (mem_ratNegGraph.mp hnx).1
  have hy := (mem_ratNegGraph.mp hny).1
  have hnxQ := funcFoundational_value_mem ratNegGraph_isFunc hnx
  have hnyQ := funcFoundational_value_mem ratNegGraph_isFunc hny
  obtain ⟨w, _, hn⟩ := ratAdd_exists hnxQ hnyQ
  apply (ratAbs_upper_iff (ratNeg_add hnx hny hxy hn) hc
    (funcFoundational_value_mem ratAddGraph_isFunc hab)).mpr
  exact ⟨ratAdd_pair_le hx hy haQ hbQ hxle hyle hxy hab,
    ratAdd_pair_le hnxQ hnyQ haQ hbQ hnxa hnyb hn hab⟩

end TratadoAnalisis.Rationals.AbsoluteValue
