import TratadoAnalisis.Abstract.CompletenessManual0008
import TratadoAnalisis.Naturals.Recursion

/-!
# Equivalencias de completitud: supremo, separación e intersección

TA-DEF-00075, TA-THM-00038, TA-DEF-00076 y TA-THM-00039.
Las familias de extremos son grafos conjuntistas totales y unívocos.
Las versiones positivas sólo requieren testigos de habitabilidad.
El tercero excluido se recibe expresamente al traducir la no vaciedad
negativa de los enunciados editoriales. No se eligen funciones globales.
-/

namespace TratadoAnalisis.AbstractCompleteness.Equivalences

universe u

open TratadoAnalisis.AbstractCompleteness.Manual0008
open TratadoAnalisis.Dedekind.FieldPredicates
open TratadoAnalisis.Naturals.Recursion

/-- De un testigo de habitabilidad se obtiene no vaciedad negativa. -/
theorem inhabited_implies_ne_empty
    {A : ZFSet.{u}} (h : ∃ a : ZFSet.{u}, a ∈ A) : A ≠ ∅ := by
  obtain ⟨a, ha⟩ := h
  intro he
  rw [he] at ha
  exact ZFSet.notMem_empty a ha

/-- El paso inverso exige aquí el tercero excluido explícito. -/
theorem ne_empty_implies_inhabited
    (em : ∀ p : Prop, p ∨ ¬p)
    {A : ZFSet.{u}} (hne : A ≠ ∅) : ∃ a : ZFSet.{u}, a ∈ A := by
  rcases em (∃ a : ZFSet.{u}, a ∈ A) with h | h
  · exact h
  · exfalso
    apply hne
    apply ZFSet.ext
    intro a
    exact ⟨fun ha => (h ⟨a, ha⟩).elim,
      fun ha => (ZFSet.notMem_empty a ha).elim⟩

def HasSupremumPropertyPositive (F : ZFSet.{u})
    (le : ZFSet.{u} → ZFSet.{u} → Prop) : Prop :=
  ∀ A : ZFSet.{u}, A ⊆ F → (∃ a : ZFSet.{u}, a ∈ A) →
    (∃ b : ZFSet.{u}, IsUpperBound F A le b) →
    ∃ s : ZFSet.{u}, IsSupremum F A le s

/-- TA-DEF-00075, forma positiva. -/
def HasSeparationPropertyPositive (F : ZFSet.{u})
    (le : ZFSet.{u} → ZFSet.{u} → Prop) : Prop :=
  ∀ A B : ZFSet.{u}, A ⊆ F → B ⊆ F →
    (∃ a : ZFSet.{u}, a ∈ A) → (∃ b : ZFSet.{u}, b ∈ B) →
    (∀ a b : ZFSet.{u}, a ∈ A → b ∈ B → le a b) →
    ∃ c : ZFSet.{u}, c ∈ F ∧
      (∀ a : ZFSet.{u}, a ∈ A → le a c) ∧
      (∀ b : ZFSet.{u}, b ∈ B → le c b)

/-- TA-DEF-00075, formulación editorial por no vaciedad. -/
def HasSeparationProperty (F : ZFSet.{u})
    (le : ZFSet.{u} → ZFSet.{u} → Prop) : Prop :=
  ∀ A B : ZFSet.{u}, A ⊆ F → B ⊆ F → A ≠ ∅ → B ≠ ∅ →
    (∀ a b : ZFSet.{u}, a ∈ A → b ∈ B → le a b) →
    ∃ c : ZFSet.{u}, c ∈ F ∧
      (∀ a : ZFSet.{u}, a ∈ A → le a c) ∧
      (∀ b : ZFSet.{u}, b ∈ B → le c b)

theorem supremum_iff_positive
    (em : ∀ p : Prop, p ∨ ¬p)
    (F : ZFSet.{u}) (le : ZFSet.{u} → ZFSet.{u} → Prop) :
    HasSupremumProperty F le ↔ HasSupremumPropertyPositive F le := by
  constructor
  · intro h A hA hne hb
    exact h A hA (inhabited_implies_ne_empty hne) hb
  · intro h A hA hne hb
    exact h A hA (ne_empty_implies_inhabited em hne) hb

theorem separation_iff_positive
    (em : ∀ p : Prop, p ∨ ¬p)
    (F : ZFSet.{u}) (le : ZFSet.{u} → ZFSet.{u} → Prop) :
    HasSeparationProperty F le ↔ HasSeparationPropertyPositive F le := by
  constructor
  · intro h A B hA hB ha hb hab
    exact h A B hA hB (inhabited_implies_ne_empty ha)
      (inhabited_implies_ne_empty hb) hab
  · intro h A B hA hB ha hb hab
    exact h A B hA hB (ne_empty_implies_inhabited em ha)
      (ne_empty_implies_inhabited em hb) hab

/-- Conjunto de todas las cotas superiores, por Separación en F. -/
def UpperBounds (F A : ZFSet.{u})
    (le : ZFSet.{u} → ZFSet.{u} → Prop) : ZFSet.{u} :=
  ZFSet.sep (fun b => ∀ a : ZFSet.{u}, a ∈ A → le a b) F

theorem mem_upperBounds_iff
    (F A : ZFSet.{u}) (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (b : ZFSet.{u}) :
    b ∈ UpperBounds F A le ↔ IsUpperBound F A le b :=
  ZFSet.mem_sep

/-- TA-THM-00038: núcleo positivo, sin tercero excluido. -/
theorem TA_THM_00038_supremum_iff_separation_positive
    (F : ZFSet.{u}) (le : ZFSet.{u} → ZFSet.{u} → Prop) :
    HasSupremumPropertyPositive F le ↔ HasSeparationPropertyPositive F le := by
  constructor
  · intro hs A B hA hB _ha hb hab
    obtain ⟨b, hbB⟩ := hb
    obtain ⟨c, hc⟩ := hs A hA _ha
      ⟨b, hB hbB, fun a ha => hab a b ha hbB⟩
    exact ⟨c, hc.1.1, hc.1.2,
      fun b hb => hc.2 b ⟨hB hb, fun a ha => hab a b ha hb⟩⟩
  · intro hs A hA ha hbounded
    obtain ⟨b, hb⟩ := hbounded
    let U := UpperBounds F A le
    have hU : U ⊆ F := fun _ h => (ZFSet.mem_sep.mp h).1
    have hUinh : ∃ u : ZFSet.{u}, u ∈ U :=
      ⟨b, (mem_upperBounds_iff F A le b).mpr hb⟩
    have hcross : ∀ a u : ZFSet.{u}, a ∈ A → u ∈ U → le a u :=
      fun a u ha hu => ((mem_upperBounds_iff F A le u).mp hu).2 a ha
    obtain ⟨c, hcF, hAc, hcU⟩ := hs A U hA hU ha hUinh hcross
    exact ⟨c, ⟨hcF, hAc⟩,
      fun u hu => hcU u ((mem_upperBounds_iff F A le u).mpr hu)⟩

/-- TA-THM-00038: equivalencia editorial. No requiere estructura algebraica. -/
theorem TA_THM_00038_supremum_iff_separation
    (em : ∀ p : Prop, p ∨ ¬p)
    (F : ZFSet.{u}) (le : ZFSet.{u} → ZFSet.{u} → Prop) :
    HasSupremumProperty F le ↔ HasSeparationProperty F le :=
  (supremum_iff_positive em F le).trans
    ((TA_THM_00038_supremum_iff_separation_positive F le).trans
      (separation_iff_positive em F le).symm)

/-- Imagen de una familia conjuntista por Separación en el codominio. -/
def FamilyImage (I F G : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun a => ∃ i : ZFSet.{u}, i ∈ I ∧ ZFSet.pair i a ∈ G) F

theorem mem_familyImage_iff {I F G a : ZFSet.{u}} :
    a ∈ FamilyImage I F G ↔
      a ∈ F ∧ ∃ i : ZFSet.{u}, i ∈ I ∧ ZFSet.pair i a ∈ G :=
  ZFSet.mem_sep

/-- Hipótesis cruzada de TA-DEF-00076: a_i ≤ b_j para todos i,j. -/
def CrossOrdered (I G H : ZFSet.{u})
    (le : ZFSet.{u} → ZFSet.{u} → Prop) : Prop :=
  ∀ i j a b : ZFSet.{u}, i ∈ I → j ∈ I →
    ZFSet.pair i a ∈ G → ZFSet.pair j b ∈ H → le a b

/-- Pertenencia simultánea a los intervalos cerrados de una familia. -/
def CommonIntervalPoint (I G H : ZFSet.{u})
    (le : ZFSet.{u} → ZFSet.{u} → Prop) (c : ZFSet.{u}) : Prop :=
  ∀ i a b : ZFSet.{u}, i ∈ I →
    ZFSet.pair i a ∈ G → ZFSet.pair i b ∈ H → le a c ∧ le c b

/-- Intersección de los intervalos como subconjunto de F. -/
def ClosedIntervalIntersection (I F G H : ZFSet.{u})
    (le : ZFSet.{u} → ZFSet.{u} → Prop) : ZFSet.{u} :=
  ZFSet.sep (CommonIntervalPoint I G H le) F

theorem mem_closedIntervalIntersection_iff
    {I F G H c : ZFSet.{u}} {le : ZFSet.{u} → ZFSet.{u} → Prop} :
    c ∈ ClosedIntervalIntersection I F G H le ↔
      c ∈ F ∧ CommonIntervalPoint I G H le c :=
  ZFSet.mem_sep

/-- TA-DEF-00076, versión positiva, con familias sobre cualquier conjunto I. -/
def HasClosedIntervalIntersectionPositive (F : ZFSet.{u})
    (le : ZFSet.{u} → ZFSet.{u} → Prop) : Prop :=
  ∀ I G H : ZFSet.{u}, (∃ i : ZFSet.{u}, i ∈ I) →
    IsFuncFoundational I F G → IsFuncFoundational I F H →
    CrossOrdered I G H le →
    ∃ c : ZFSet.{u}, c ∈ F ∧ CommonIntervalPoint I G H le c

/-- TA-DEF-00076, versión editorial, por no vaciedad de la intersección. -/
def HasClosedIntervalIntersectionProperty (F : ZFSet.{u})
    (le : ZFSet.{u} → ZFSet.{u} → Prop) : Prop :=
  ∀ I G H : ZFSet.{u}, I ≠ ∅ →
    IsFuncFoundational I F G → IsFuncFoundational I F H →
    CrossOrdered I G H le →
    ClosedIntervalIntersection I F G H le ≠ ∅

theorem interval_intersection_iff_positive
    (em : ∀ p : Prop, p ∨ ¬p)
    (F : ZFSet.{u}) (le : ZFSet.{u} → ZFSet.{u} → Prop) :
    HasClosedIntervalIntersectionProperty F le ↔
      HasClosedIntervalIntersectionPositive F le := by
  constructor
  · intro h I G H hi hg hh hc
    obtain ⟨c, hc'⟩ := ne_empty_implies_inhabited em
      (h I G H (inhabited_implies_ne_empty hi) hg hh hc)
    exact ⟨c, mem_closedIntervalIntersection_iff.mp hc'⟩
  · intro h I G H hi hg hh hc
    obtain ⟨c, hc'⟩ := h I G H (ne_empty_implies_inhabited em hi) hg hh hc
    exact inhabited_implies_ne_empty
      ⟨c, mem_closedIntervalIntersection_iff.mpr hc'⟩

/-- Grafo explícito de una proyección del producto; p se da de antemano.
    Las únicas aplicaciones son p(a,b)=a y p(a,b)=b, no se usa Choice. -/
def ProjectionGraph (A B F : ZFSet.{u})
    (p : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ a : ZFSet.{u}, a ∈ A ∧
    ∃ b : ZFSet.{u}, b ∈ B ∧ z = ZFSet.pair (ZFSet.pair a b) (p a b))
    (pairAmbient (cartesianProductFoundational A B) F)

theorem projection_pair_mem
    {A B F a b : ZFSet.{u}} {p : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}}
    (ha : a ∈ A) (hb : b ∈ B) (hp : p a b ∈ F) :
    ZFSet.pair (ZFSet.pair a b) (p a b) ∈ ProjectionGraph A B F p :=
  ZFSet.mem_sep.mpr
    ⟨pair_mem_pairAmbient (mem_cartesianProductFoundational.mpr ⟨ha, hb⟩) hp,
      a, ha, b, hb, rfl⟩

theorem projection_pair_value
    {A B F i x : ZFSet.{u}} {p : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}}
    (h : ZFSet.pair i x ∈ ProjectionGraph A B F p) :
    ∃ a : ZFSet.{u}, a ∈ A ∧ ∃ b : ZFSet.{u}, b ∈ B ∧
      i = ZFSet.pair a b ∧ x = p a b := by
  obtain ⟨a, ha, b, hb, he⟩ := (ZFSet.mem_sep.mp h).2
  have e := ZFSet.pair_injective he
  exact ⟨a, ha, b, hb, e.1, e.2⟩

theorem projectionGraph_isFunc
    {A B F : ZFSet.{u}} {p : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}}
    (hp : ∀ a b : ZFSet.{u}, a ∈ A → b ∈ B → p a b ∈ F) :
    IsFuncFoundational (cartesianProductFoundational A B) F
      (ProjectionGraph A B F p) := by
  constructor
  · intro z hz
    obtain ⟨a, ha, b, hb, he⟩ := (ZFSet.mem_sep.mp hz).2
    exact ⟨ZFSet.pair a b, mem_cartesianProductFoundational.mpr ⟨ha, hb⟩,
      p a b, hp a b ha hb, he⟩
  · intro i hi
    obtain ⟨a, ha, b, hb, rfl⟩ := (ZFSet.mem_sep.mp hi).2
    refine ⟨p a b, ⟨hp a b ha hb, projection_pair_mem ha hb (hp a b ha hb)⟩, ?_⟩
    intro x hx
    obtain ⟨a', _, b', _, he, hx'⟩ := projection_pair_value hx.2
    have e := ZFSet.pair_injective he
    rw [hx', ← e.1, ← e.2]

/-- Separación implica la intersección, por las imágenes de los extremos. -/
theorem intersection_positive_of_separation
    (F : ZFSet.{u}) (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hs : HasSeparationPropertyPositive F le) :
    HasClosedIntervalIntersectionPositive F le := by
  intro I G H hi hg hh hcross
  obtain ⟨i, hiI⟩ := hi
  obtain ⟨a, ⟨haF, haG⟩, _⟩ := hg.2 i hiI
  obtain ⟨b, ⟨hbF, hbH⟩, _⟩ := hh.2 i hiI
  let A := FamilyImage I F G
  let B := FamilyImage I F H
  have hA : A ⊆ F := fun _ h => (mem_familyImage_iff.mp h).1
  have hB : B ⊆ F := fun _ h => (mem_familyImage_iff.mp h).1
  have haA : a ∈ A := mem_familyImage_iff.mpr ⟨haF, i, hiI, haG⟩
  have hbB : b ∈ B := mem_familyImage_iff.mpr ⟨hbF, i, hiI, hbH⟩
  have hcAB : ∀ x y : ZFSet.{u}, x ∈ A → y ∈ B → le x y := by
    intro x y hx hy
    obtain ⟨_, k, hk, hxG⟩ := mem_familyImage_iff.mp hx
    obtain ⟨_, j, hj, hyH⟩ := mem_familyImage_iff.mp hy
    exact hcross k j x y hk hj hxG hyH
  obtain ⟨c, hcF, hac, hcb⟩ := hs A B hA hB ⟨a, haA⟩ ⟨b, hbB⟩ hcAB
  refine ⟨c, hcF, ?_⟩
  intro k x y hk hx hy
  exact ⟨hac x (mem_familyImage_iff.mpr
      ⟨funcFoundational_value_mem hg hx, k, hk, hx⟩),
    hcb y (mem_familyImage_iff.mpr
      ⟨funcFoundational_value_mem hh hy, k, hk, hy⟩)⟩

/-- Intersección implica separación mediante el índice I = A × B. -/
theorem separation_positive_of_intersection
    (F : ZFSet.{u}) (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hi : HasClosedIntervalIntersectionPositive F le) :
    HasSeparationPropertyPositive F le := by
  intro A B hA hB ha hb hab
  obtain ⟨a0, ha0⟩ := ha
  obtain ⟨b0, hb0⟩ := hb
  let I := cartesianProductFoundational A B
  let G := ProjectionGraph A B F (fun a _ => a)
  let H := ProjectionGraph A B F (fun _ b => b)
  have hiI : ∃ i : ZFSet.{u}, i ∈ I :=
    ⟨ZFSet.pair a0 b0, mem_cartesianProductFoundational.mpr ⟨ha0, hb0⟩⟩
  have hg : IsFuncFoundational I F G :=
    projectionGraph_isFunc (fun a _ ha _ => hA ha)
  have hh : IsFuncFoundational I F H :=
    projectionGraph_isFunc (fun _ b _ hb => hB hb)
  have hcross : CrossOrdered I G H le := by
    intro i j x y _hi _hj hx hy
    obtain ⟨a, ha, b, _, _, ex⟩ := projection_pair_value hx
    obtain ⟨a', _, b', hb, _, ey⟩ := projection_pair_value hy
    change x = a at ex
    change y = b' at ey
    rw [ex, ey]
    exact hab a b' ha hb
  obtain ⟨c, hcF, hc⟩ := hi I G H hiI hg hh hcross
  refine ⟨c, hcF, ?_, ?_⟩
  · intro a ha
    have hidx : ZFSet.pair a b0 ∈ I :=
      mem_cartesianProductFoundational.mpr ⟨ha, hb0⟩
    have hg' : ZFSet.pair (ZFSet.pair a b0) a ∈ G :=
      projection_pair_mem (p := fun a _ => a) ha hb0 (hA ha)
    have hh' : ZFSet.pair (ZFSet.pair a b0) b0 ∈ H :=
      projection_pair_mem (p := fun _ b => b) ha hb0 (hB hb0)
    exact (hc (ZFSet.pair a b0) a b0 hidx hg' hh').1
  · intro b hb
    have hidx : ZFSet.pair a0 b ∈ I :=
      mem_cartesianProductFoundational.mpr ⟨ha0, hb⟩
    have hg' : ZFSet.pair (ZFSet.pair a0 b) a0 ∈ G :=
      projection_pair_mem (p := fun a _ => a) ha0 hb (hA ha0)
    have hh' : ZFSet.pair (ZFSet.pair a0 b) b ∈ H :=
      projection_pair_mem (p := fun _ b => b) ha0 hb (hB hb)
    exact (hc (ZFSet.pair a0 b) a0 b hidx hg' hh').2

/-- TA-THM-00039: versión positiva; no requiere tercero excluido. -/
theorem TA_THM_00039_supremum_iff_intersection_positive
    (F : ZFSet.{u}) (le : ZFSet.{u} → ZFSet.{u} → Prop) :
    HasSupremumPropertyPositive F le ↔ HasClosedIntervalIntersectionPositive F le :=
  (TA_THM_00038_supremum_iff_separation_positive F le).trans
    ⟨intersection_positive_of_separation F le,
      separation_positive_of_intersection F le⟩

/-- Equivalencia editorial de las dos propiedades de completitud. -/
theorem TA_THM_00039_supremum_iff_intersection
    (em : ∀ p : Prop, p ∨ ¬p)
    (F : ZFSet.{u}) (le : ZFSet.{u} → ZFSet.{u} → Prop) :
    HasSupremumProperty F le ↔ HasClosedIntervalIntersectionProperty F le :=
  (supremum_iff_positive em F le).trans
    ((TA_THM_00039_supremum_iff_intersection_positive F le).trans
      (interval_intersection_iff_positive em F le).symm)

/-- TA-THM-00039 en el cuerpo ordenado del enunciado del manuscrito. -/
theorem TA_THM_00039_complete_iff_intersection
    (em : ∀ p : Prop, p ∨ ¬p)
    (F zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hordered : IsOrderedFieldFoundational F zero one add mul le) :
    IsCompleteOrderedFieldFoundational F zero one add mul le ↔
      HasClosedIntervalIntersectionProperty F le := by
  have he := TA_THM_00039_supremum_iff_intersection em F le
  exact ⟨fun h => he.mp h.2, fun h => ⟨hordered, he.mpr h⟩⟩

end TratadoAnalisis.AbstractCompleteness.Equivalences
