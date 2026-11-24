import TratadoAnalisis.Abstract.PrimeInversePositivity0009
import TratadoAnalisis.Abstract.OppositeOrderPrep0008

/-!
# Valor absoluto en cuerpos ordenados relacionales

TA-DEF-00071, TA-PRO-00071 y TA-THM-00035.
El valor absoluto es el máximo de un elemento y su opuesto. Se prueban
existencia y unicidad sin seleccionar una función global.
-/

namespace TratadoAnalisis.AbstractCompleteness.AbsoluteValue

universe u

open TratadoAnalisis.AbstractCompleteness.Manual0008
open TratadoAnalisis.AbstractCompleteness.Density0009
open TratadoAnalisis.Dedekind.FieldPredicates

variable {F zero one : ZFSet.{u}}
variable {add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop}
variable {le : ZFSet.{u} → ZFSet.{u} → Prop}

/-- TA-DEF-00071: a es el máximo de x y su opuesto aditivo. -/
def IsAbsoluteValue (F zero : ZFSet.{u})
    (add : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop) (x a : ZFSet.{u}) : Prop :=
  ∃ nx : ZFSet.{u}, IsAdditiveOpposite F zero add x nx ∧
    a ∈ F ∧ (a = x ∨ a = nx) ∧ le x a ∧ le nx a

theorem opposite_unique
    (h : IsOrderedFieldFoundational F zero one add mul le)
    {x nx mx : ZFSet.{u}}
    (hn : IsAdditiveOpposite F zero add x nx)
    (hm : IsAdditiveOpposite F zero add x mx) : nx = mx :=
  rel_add_cancel_left_manual F zero add h.1.1 x nx mx zero
    hn.1 hn.2.1 hm.2.1 h.1.1.2.1 hn.2.2.1 hm.2.2.1

theorem zero_opposite
    (h : IsOrderedFieldFoundational F zero one add mul le) :
    IsAdditiveOpposite F zero add zero zero := by
  have hz := h.1.1.2.1
  have hu := h.1.1.2.2.2.2.1 zero hz
  exact ⟨hz, hz, hu.1, hu.2⟩

theorem absolute_mem
    {x a : ZFSet.{u}} (ha : IsAbsoluteValue F zero add le x a) :
    x ∈ F ∧ a ∈ F := by
  obtain ⟨_, hn, haF, _, _, _⟩ := ha
  exact ⟨hn.1, haF⟩

/-- Caracterización universal del máximo, con un opuesto cualquiera. -/
theorem absolute_upper_iff
    (h : IsOrderedFieldFoundational F zero one add mul le)
    {x nx a r : ZFSet.{u}}
    (hn : IsAdditiveOpposite F zero add x nx)
    (ha : IsAbsoluteValue F zero add le x a) (hr : r ∈ F) :
    le a r ↔ le x r ∧ le nx r := by
  obtain ⟨n, hneg, haF, hcase, hx, hnx⟩ := ha
  have he : n = nx := opposite_unique h hneg hn
  subst n
  constructor
  · intro har
    exact ⟨h.2.1.2.2.1 x a r hn.1 haF hr hx har,
      h.2.1.2.2.1 nx a r hn.2.1 haF hr hnx har⟩
  · rintro ⟨hxr, hnr⟩
    rcases hcase with he | he
    · rw [he]
      exact hxr
    · rw [he]
      exact hnr

theorem absolute_unique
    (h : IsOrderedFieldFoundational F zero one add mul le)
    {x a b : ZFSet.{u}}
    (ha : IsAbsoluteValue F zero add le x a)
    (hb : IsAbsoluteValue F zero add le x b) : a = b := by
  have hab := absolute_mem ha
  have hbb := absolute_mem hb
  have ha' := ha
  obtain ⟨n, hn, _, _, _, _⟩ := ha
  exact h.2.1.2.1 a b hab.2 hbb.2
    ((absolute_upper_iff h hn ha' hbb.2).mpr
      ((absolute_upper_iff h hn hb hbb.2).mp (h.2.1.1 b hbb.2)))
    ((absolute_upper_iff h hn hb hab.2).mpr
      ((absolute_upper_iff h hn ha' hab.2).mp (h.2.1.1 a hab.2)))

/-- TA-DEF-00071: existencia y unicidad del máximo de {x,-x}. -/
theorem TA_DEF_00071_absolute_exists_unique
    (h : IsOrderedFieldFoundational F zero one add mul le)
    {x : ZFSet.{u}} (hx : x ∈ F) :
    ∃! a : ZFSet.{u}, IsAbsoluteValue F zero add le x a := by
  obtain ⟨nx, hnx, hxn, hnx_x⟩ := h.1.1.2.2.2.2.2 x hx
  have hn : IsAdditiveOpposite F zero add x nx := ⟨hx, hnx, hxn, hnx_x⟩
  rcases h.2.1.2.2.2 x nx hx hnx with hle | hle
  · have ha : IsAbsoluteValue F zero add le x nx :=
      ⟨nx, hn, hnx, Or.inr rfl, hle, h.2.1.1 nx hnx⟩
    exact ⟨nx, ha, fun a hb => absolute_unique h hb ha⟩
  · have ha : IsAbsoluteValue F zero add le x x :=
      ⟨nx, hn, hx, Or.inl rfl, h.2.1.1 x hx, hle⟩
    exact ⟨x, ha, fun a hb => absolute_unique h hb ha⟩

theorem absolute_of_nonnegative
    (h : IsOrderedFieldFoundational F zero one add mul le)
    {x a : ZFSet.{u}} (ha : IsAbsoluteValue F zero add le x a)
    (hx : le zero x) : a = x := by
  have haCopy := ha
  obtain ⟨nx, hn, _, _, _, _⟩ := haCopy
  have hnz := opposite_reverses_le_manual F zero one add mul le
    zero x zero nx h hx (zero_opposite h) hn
  have hnx := h.2.1.2.2.1 nx zero x hn.2.1 h.1.1.2.1 hn.1 hnz hx
  exact absolute_unique h ha ⟨nx, hn, hn.1, Or.inl rfl, h.2.1.1 x hn.1, hnx⟩

theorem absolute_of_nonpositive
    (h : IsOrderedFieldFoundational F zero one add mul le)
    {x nx a : ZFSet.{u}} (hn : IsAdditiveOpposite F zero add x nx)
    (ha : IsAbsoluteValue F zero add le x a) (hx : le x zero) : a = nx := by
  have hzn := opposite_reverses_le_manual F zero one add mul le
    x zero nx zero h hx hn (zero_opposite h)
  have hxn := h.2.1.2.2.1 x zero nx hn.1 h.1.1.2.1 hn.2.1 hx hzn
  exact absolute_unique h ha ⟨nx, hn, hn.2.1, Or.inr rfl, hxn, h.2.1.1 nx hn.2.1⟩

/-- TA-PRO-00071(1). -/
theorem absolute_nonnegative
    (h : IsOrderedFieldFoundational F zero one add mul le)
    {x a : ZFSet.{u}} (ha : IsAbsoluteValue F zero add le x a) : le zero a := by
  obtain ⟨nx, hn, haF, _, hxle, hnle⟩ := ha
  rcases h.2.1.2.2.2 zero x h.1.1.2.1 hn.1 with hp | hp
  · exact h.2.1.2.2.1 zero x a h.1.1.2.1 hn.1 haF hp hxle
  · have hzn := opposite_reverses_le_manual F zero one add mul le
      x zero nx zero h hp hn (zero_opposite h)
    exact h.2.1.2.2.1 zero nx a h.1.1.2.1 hn.2.1 haF hzn hnle

/-- TA-PRO-00071(4). -/
theorem absolute_bounds
    (h : IsOrderedFieldFoundational F zero one add mul le)
    {x a na : ZFSet.{u}} (ha : IsAbsoluteValue F zero add le x a)
    (hna : IsAdditiveOpposite F zero add a na) : le na x ∧ le x a := by
  obtain ⟨nx, hn, _, _, hxle, hnle⟩ := ha
  exact ⟨opposite_reverses_le_manual F zero one add mul le nx a x na h hnle
    (opposite_symm_manual F zero add x nx hn) hna, hxle⟩

/-- TA-PRO-00071(2). -/
theorem absolute_zero_iff
    (h : IsOrderedFieldFoundational F zero one add mul le)
    {x a : ZFSet.{u}} (ha : IsAbsoluteValue F zero add le x a) :
    a = zero ↔ x = zero := by
  constructor
  · intro e
    subst a
    have hb := absolute_bounds h ha (zero_opposite h)
    exact h.2.1.2.1 x zero (absolute_mem ha).1 h.1.1.2.1 hb.2 hb.1
  · intro e
    subst x
    exact absolute_of_nonnegative h ha (h.2.1.1 zero h.1.1.2.1)

/-- TA-PRO-00071(3). -/
theorem absolute_opposite
    (h : IsOrderedFieldFoundational F zero one add mul le)
    {x nx a b : ZFSet.{u}}
    (hn : IsAdditiveOpposite F zero add x nx)
    (ha : IsAbsoluteValue F zero add le x a)
    (hb : IsAbsoluteValue F zero add le nx b) : b = a := by
  obtain ⟨n, hn', haF, hcase, hxa, hna⟩ := ha
  have e : n = nx := opposite_unique h hn' hn
  subst n
  apply absolute_unique h hb
  exact ⟨x, opposite_symm_manual F zero add x nx hn, haF,
    hcase.elim Or.inr Or.inl, hna, hxa⟩

/-- TA-PRO-00071(6). La equivalencia vale incluso sin suponer 0 ≤ r. -/
theorem absolute_le_iff
    (h : IsOrderedFieldFoundational F zero one add mul le)
    {x a r nr : ZFSet.{u}} (ha : IsAbsoluteValue F zero add le x a)
    (hnr : IsAdditiveOpposite F zero add r nr) :
    le a r ↔ le nr x ∧ le x r := by
  have haCopy := ha
  obtain ⟨nx, hn, _, _, _, _⟩ := haCopy
  constructor
  · intro har
    have hb := (absolute_upper_iff h hn ha hnr.1).mp har
    exact ⟨opposite_reverses_le_manual F zero one add mul le nx r x nr h hb.2
      (opposite_symm_manual F zero add x nx hn) hnr, hb.1⟩
  · rintro ⟨hnrx, hxr⟩
    have hnxr := opposite_reverses_le_manual F zero one add mul le nr x r nx h hnrx
      (opposite_symm_manual F zero add r nr hnr) hn
    exact (absolute_upper_iff h hn ha hnr.1).mpr ⟨hxr, hnxr⟩

/-- Conmutación de una suma relacional sin seleccionar una operación. -/
theorem add_commutes
    (h : IsOrderedFieldFoundational F zero one add mul le)
    {x y z : ZFSet.{u}} (hx : x ∈ F) (hy : y ∈ F) (hz : add x y z) :
    add y x z := by
  obtain ⟨w, ⟨_, hw⟩, _⟩ := h.1.1.1 y hy x hx
  have e := h.1.1.2.2.2.1 x y z w hx hy hz hw
  rw [e]
  exact hw

theorem mul_commutes
    (h : IsOrderedFieldFoundational F zero one add mul le)
    {x y z : ZFSet.{u}} (hx : x ∈ F) (hy : y ∈ F) (hz : mul x y z) :
    mul y x z := by
  obtain ⟨w, ⟨_, hw⟩, _⟩ := h.1.2.1 y hy x hx
  have e := h.1.2.2.2.2.1 x y z w hx hy hz hw
  rw [e]
  exact hw

theorem mul_value_unique
    (h : IsOrderedFieldFoundational F zero one add mul le)
    {x y p q : ZFSet.{u}} (hx : x ∈ F) (hy : y ∈ F)
    (hp : p ∈ F) (hq : q ∈ F) (hpq : mul x y p) (hqq : mul x y q) :
    p = q := by
  obtain ⟨w, _, hu⟩ := h.1.2.1 x hx y hy
  exact (hu p ⟨hp, hpq⟩).trans (hu q ⟨hq, hqq⟩).symm

/-- TA-PRO-00071(5): el valor absoluto preserva el producto. -/
theorem absolute_mul
    (h : IsOrderedFieldFoundational F zero one add mul le)
    {x y z a b c p : ZFSet.{u}}
    (ha : IsAbsoluteValue F zero add le x a)
    (hb : IsAbsoluteValue F zero add le y b)
    (hc : IsAbsoluteValue F zero add le z c)
    (hp : p ∈ F) (hxy : mul x y z) (hab : mul a b p) : c = p := by
  have hz := (absolute_mem hc).1
  have hp0 := h.2.2.2 a b p (absolute_mem ha).2 (absolute_mem hb).2
    (absolute_nonnegative h ha) (absolute_nonnegative h hb) hab
  obtain ⟨nx, hnx, haF, hax, _, _⟩ := ha
  obtain ⟨ny, hny, hbF, hby, _, _⟩ := hb
  have hcases : p = z ∨ IsAdditiveOpposite F zero add z p := by
    rcases hax with eax | eax
    · subst a
      rcases hby with eby | eby
      · subst b
        exact Or.inl (mul_value_unique h hnx.1 hny.1 hp hz hab hxy)
      · subst b
        exact Or.inr (rel_mul_opposite_right_manual F zero one add mul h.1
          x y ny z p hnx.1 hny.1 hny.2.1 hz hp hny hxy hab)
    · subst a
      rcases hby with eby | eby
      · subst b
        exact Or.inr (rel_mul_opposite_right_manual F zero one add mul h.1
          y x nx z p hny.1 hnx.1 hnx.2.1 hz hp hnx
          (mul_commutes h hnx.1 hny.1 hxy)
          (mul_commutes h hnx.2.1 hny.1 hab))
      · subst b
        obtain ⟨q, ⟨hq, hxny⟩, _⟩ := h.1.2.1 x hnx.1 ny hny.2.1
        have hzq := rel_mul_opposite_right_manual F zero one add mul h.1
          x y ny z q hnx.1 hny.1 hny.2.1 hz hq hny hxy hxny
        have hqp := rel_mul_opposite_right_manual F zero one add mul h.1
          ny x nx q p hny.2.1 hnx.1 hnx.2.1 hq hp hnx
          (mul_commutes h hnx.1 hny.2.1 hxny)
          (mul_commutes h hnx.2.1 hny.2.1 hab)
        exact Or.inl (opposite_unique h hqp (opposite_symm_manual F zero add z q hzq))
  rcases hcases with e | hn
  · subst p
    exact absolute_of_nonnegative h hc hp0
  · have hz0 := opposite_reverses_le_manual F zero one add mul le
      zero p zero z h hp0 (zero_opposite h) (opposite_symm_manual F zero add z p hn)
    exact absolute_of_nonpositive h hn hc hz0

/-- Los opuestos de una suma se suman. -/
theorem add_opposites
    (h : IsOrderedFieldFoundational F zero one add mul le)
    {x nx y ny z w : ZFSet.{u}}
    (hnx : IsAdditiveOpposite F zero add x nx)
    (hny : IsAdditiveOpposite F zero add y ny)
    (hz : z ∈ F) (hw : w ∈ F)
    (hxy : add x y z) (hn : add nx ny w) :
    IsAdditiveOpposite F zero add z w := by
  have hg := h.1.1
  have hassoc := hg.2.2.1
  have hunit := hg.2.2.2.2.1
  obtain ⟨t, ⟨ht, hty⟩, _⟩ := hg.1 nx hnx.2.1 y hny.1
  obtain ⟨s, ⟨_, htny⟩, _⟩ := hg.1 t ht ny hny.2.1
  have es : s = nx := hassoc nx y ny t s zero nx hnx.2.1 hny.1 hny.2.1
    hty htny hny.2.2.1 (hunit nx hnx.2.1).1
  obtain ⟨v, ⟨_, hyv⟩, _⟩ := hg.1 y hny.1 w hw
  have ev : s = v := hassoc y nx ny t s w v hny.1 hnx.2.1 hny.2.1
    (add_commutes h hnx.2.1 hny.1 hty) htny hn hyv
  have hyw : add y w nx := by
    rw [← es, ev]
    exact hyv
  obtain ⟨p, ⟨_, hzp⟩, _⟩ := hg.1 z hz w hw
  have ep : p = zero := hassoc x y w z p nx zero hnx.1 hny.1 hw
    hxy hzp hyw hnx.2.2.1
  have hzw : add z w zero := by
    rw [← ep]
    exact hzp
  exact ⟨hz, hw, hzw, add_commutes h hz hw hzw⟩

/-- Compatibilidad de la suma con dos desigualdades simultáneas. -/
theorem add_pair_le
    (h : IsOrderedFieldFoundational F zero one add mul le)
    {x y a b z s : ZFSet.{u}}
    (hx : x ∈ F) (hy : y ∈ F) (ha : a ∈ F) (hb : b ∈ F)
    (hz : z ∈ F) (hs : s ∈ F)
    (hxa : le x a) (hyb : le y b)
    (hxy : add x y z) (hab : add a b s) : le z s := by
  obtain ⟨t, ⟨ht, hay⟩, _⟩ := h.1.1.1 a ha y hy
  have hzt := h.2.2.1 x a y z t hx ha hy hxa hxy hay
  have hts := h.2.2.1 y b a t s hy hb ha hyb
    (add_commutes h ha hy hay) (add_commutes h ha hb hab)
  exact h.2.1.2.2.1 z t s hz ht hs hzt hts

/-- TA-THM-00035: desigualdad triangular en todo cuerpo ordenado. -/
theorem TA_THM_00035_triangle
    (h : IsOrderedFieldFoundational F zero one add mul le)
    {x y z a b c s : ZFSet.{u}}
    (ha : IsAbsoluteValue F zero add le x a)
    (hb : IsAbsoluteValue F zero add le y b)
    (hc : IsAbsoluteValue F zero add le z c)
    (hs : s ∈ F) (hxy : add x y z) (hab : add a b s) : le c s := by
  have hz := (absolute_mem hc).1
  obtain ⟨nx, hnx, haF, _, hxa, hnxa⟩ := ha
  obtain ⟨ny, hny, hbF, _, hyb, hnyb⟩ := hb
  obtain ⟨w, ⟨hw, hn⟩, _⟩ := h.1.1.1 nx hnx.2.1 ny hny.2.1
  have hOpp := add_opposites h hnx hny hz hw hxy hn
  apply (absolute_upper_iff h hOpp hc hs).mpr
  exact ⟨add_pair_le h hnx.1 hny.1 haF hbF hz hs hxa hyb hxy hab,
    add_pair_le h hnx.2.1 hny.2.1 haF hbF hw hs hnxa hnyb hn hab⟩

end TratadoAnalisis.AbstractCompleteness.AbsoluteValue
