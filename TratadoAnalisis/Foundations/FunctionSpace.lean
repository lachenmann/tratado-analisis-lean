import TratadoAnalisis.Foundations.FunctionTriple

/-!
# Espacio conjuntista de funciones

TA-PRO-00014 (existencia de B^A). Los elementos son los triples
(A,B,G) de TA-DEF-00018, no meramente grafos ni funciones de Lean.
El conjunto ambiente se obtiene mediante potencias y pares; se
separan los triples funcionales. No se selecciona ningún grafo.
-/

namespace TratadoAnalisis.Foundations.FunctionSpace

universe u

open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Foundations.FunctionTriple

/-- Ambiente fijo de triples con grafo contenido en A × B. -/
def functionSpaceAmbient (A B : ZFSet.{u}) : ZFSet.{u} :=
  pairAmbient ({A} : ZFSet.{u})
    (pairAmbient ({B} : ZFSet.{u})
      (ZFSet.powerset (cartesianProductFoundational A B)))

/-- Todo grafo funcional está contenido en el producto conjuntista. -/
theorem functionGraph_subset_product
    {A B G : ZFSet.{u}} (hG : IsFuncFoundational A B G) :
    G ⊆ cartesianProductFoundational A B := by
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := hG.1 z hz
  exact mem_cartesianProductFoundational.mpr ⟨ha, hb⟩

/-- Los triples de dominio/codominio fijos y grafo funcional
    pertenecen al ambiente, sin Replacement ni Choice. -/
theorem functionTriple_mem_ambient
    {A B G : ZFSet.{u}} (hG : IsFuncFoundational A B G) :
    functionTriple A B G ∈ functionSpaceAmbient A B := by
  have hA : A ∈ ({A} : ZFSet.{u}) := ZFSet.mem_singleton.mpr rfl
  have hB : B ∈ ({B} : ZFSet.{u}) := ZFSet.mem_singleton.mpr rfl
  have hPow : G ∈ ZFSet.powerset (cartesianProductFoundational A B) :=
    ZFSet.mem_powerset.mpr (functionGraph_subset_product hG)
  have hBG : ZFSet.pair B G ∈ pairAmbient ({B} : ZFSet.{u})
      (ZFSet.powerset (cartesianProductFoundational A B)) :=
    pair_mem_pairAmbient hB hPow
  exact pair_mem_pairAmbient hA hBG

/-- El conjunto B^A por Separación dentro de un ambiente fijo. -/
def functionSpace (A B : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (IsFunctionTriple A B) (functionSpaceAmbient A B)

/-- TA-PRO-00014: pertenecer a B^A equivale a ser una función A → B. -/
theorem TA_PRO_00014_mem_functionSpace_iff
    {A B f : ZFSet.{u}} :
    f ∈ functionSpace A B ↔ IsFunctionTriple A B f := by
  constructor
  · intro hf
    exact (ZFSet.mem_sep.mp hf).2
  · intro hf
    obtain ⟨G, rfl, hG⟩ := hf
    exact ZFSet.mem_sep.mpr ⟨functionTriple_mem_ambient hG, G, rfl, hG⟩

/-- Existencia y unicidad del conjunto de todas las funciones A → B. -/
theorem TA_PRO_00014_functionSpace_exists_unique (A B : ZFSet.{u}) :
    ∃! S : ZFSet.{u}, ∀ f : ZFSet.{u}, f ∈ S ↔ IsFunctionTriple A B f := by
  refine ⟨functionSpace A B, fun _ => TA_PRO_00014_mem_functionSpace_iff, ?_⟩
  intro S hS
  apply ZFSet.ext
  intro f
  exact (hS f).trans TA_PRO_00014_mem_functionSpace_iff.symm

/-- Evaluación relacional del triple. La funcionalidad se exige
    mediante la pertenencia al espacio de funciones. -/
def FunctionValue (A B f a b : ZFSet.{u}) : Prop :=
  ∃ G : ZFSet.{u}, f = functionTriple A B G ∧ ZFSet.pair a b ∈ G

theorem functionValue_iff_graph
    {A B f G a b : ZFSet.{u}}
    (hf : f = functionTriple A B G) :
    FunctionValue A B f a b ↔ ZFSet.pair a b ∈ G := by
  constructor
  · rintro ⟨H, hH, hab⟩
    have he := functionTriple_graph_unique hH hf
    rw [← he]
    exact hab
  · intro hab
    exact ⟨G, hf, hab⟩

/-- Los valores evaluados pertenecen al codominio. -/
theorem functionValue_mem
    {A B f a b : ZFSet.{u}} (hf : f ∈ functionSpace A B)
    (hab : FunctionValue A B f a b) : b ∈ B := by
  obtain ⟨G, hG, hfunc⟩ := TA_PRO_00014_mem_functionSpace_iff.mp hf
  exact funcFoundational_value_mem hfunc ((functionValue_iff_graph hG).mp hab)

/-- Evaluación única sobre el dominio, sin escoger una aplicación de Lean. -/
theorem functionValue_exists_unique
    {A B f a : ZFSet.{u}} (hf : f ∈ functionSpace A B) (ha : a ∈ A) :
    ∃! b : ZFSet.{u}, b ∈ B ∧ FunctionValue A B f a b := by
  obtain ⟨G, hG, hfunc⟩ := TA_PRO_00014_mem_functionSpace_iff.mp hf
  obtain ⟨b, hb, hu⟩ := hfunc.2 a ha
  refine ⟨b, ⟨hb.1, (functionValue_iff_graph hG).mpr hb.2⟩, ?_⟩
  intro c hc
  exact hu c ⟨hc.1, (functionValue_iff_graph hG).mp hc.2⟩

theorem functionValue_unique
    {A B f a b c : ZFSet.{u}} (hf : f ∈ functionSpace A B)
    (ha : a ∈ A) (hb : FunctionValue A B f a b)
    (hc : FunctionValue A B f a c) : b = c := by
  obtain ⟨G, hG, hfunc⟩ := TA_PRO_00014_mem_functionSpace_iff.mp hf
  exact funcFoundational_pair_value_unique hfunc ha
    ((functionValue_iff_graph hG).mp hb) ((functionValue_iff_graph hG).mp hc)

/-- Igualdad extensional de funciones con dominio y codominio fijos. -/
theorem function_eq_iff_values
    {A B f g : ZFSet.{u}} (hf : f ∈ functionSpace A B)
    (hg : g ∈ functionSpace A B) :
    f = g ↔ ∀ a : ZFSet.{u}, a ∈ A →
      ∀ b c : ZFSet.{u}, FunctionValue A B f a b →
        FunctionValue A B g a c → b = c := by
  constructor
  · intro he a ha b c hb hc
    rw [← he] at hc
    exact functionValue_unique hf ha hb hc
  · intro h
    obtain ⟨G, hG, hfuncG⟩ := TA_PRO_00014_mem_functionSpace_iff.mp hf
    obtain ⟨H, hH, hfuncH⟩ := TA_PRO_00014_mem_functionSpace_iff.mp hg
    have e : G = H := by
      apply ZFSet.ext
      intro z
      constructor
      · intro hz
        obtain ⟨a, ha, b, _, rfl⟩ := hfuncG.1 z hz
        obtain ⟨c, hc, _⟩ := hfuncH.2 a ha
        have ebc := h a ha b c ⟨G, hG, hz⟩ ⟨H, hH, hc.2⟩
        rw [ebc]
        exact hc.2
      · intro hz
        obtain ⟨a, ha, c, _, rfl⟩ := hfuncH.1 z hz
        obtain ⟨b, hb, _⟩ := hfuncG.2 a ha
        have ebc := h a ha b c ⟨G, hG, hb.2⟩ ⟨H, hH, hz⟩
        rw [← ebc]
        exact hb.2
    rw [hG, hH, e]

end TratadoAnalisis.Foundations.FunctionSpace
