import TratadoAnalisis.Foundations.FunctionSpace

/-!
# Grafos por relaciones unívocas

Infraestructura para TA-DEF-00106 y TA-DEF-00107. Los grafos se forman
por separación dentro de ambientes de pares. No se construye una función
de Lean que seleccione testigos de una relación.
-/

namespace TratadoAnalisis.Foundations.RelationalFunctions

universe u

open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Foundations.FunctionTriple
open TratadoAnalisis.Foundations.FunctionSpace

def relationGraph (A B : ZFSet.{u})
    (R : ZFSet.{u} → ZFSet.{u} → Prop) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ a : ZFSet.{u}, a ∈ A ∧
    ∃ b : ZFSet.{u}, b ∈ B ∧ z = ZFSet.pair a b ∧ R a b)
    (pairAmbient A B)

theorem mem_relationGraph_iff {A B a b : ZFSet.{u}}
    {R : ZFSet.{u} → ZFSet.{u} → Prop} :
    ZFSet.pair a b ∈ relationGraph A B R ↔ a ∈ A ∧ b ∈ B ∧ R a b := by
  constructor
  · intro h
    obtain ⟨x, hx, y, hy, e, hxy⟩ := (ZFSet.mem_sep.mp h).2
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective e
    exact ⟨hx, hy, hxy⟩
  · rintro ⟨ha, hb, hab⟩
    exact ZFSet.mem_sep.mpr ⟨pair_mem_pairAmbient ha hb, a, ha, b, hb, rfl, hab⟩

theorem relationGraph_isFunc {A B : ZFSet.{u}}
    {R : ZFSet.{u} → ZFSet.{u} → Prop}
    (hR : ∀ a : ZFSet.{u}, a ∈ A → ∃! b : ZFSet.{u}, b ∈ B ∧ R a b) :
    IsFuncFoundational A B (relationGraph A B R) := by
  constructor
  · intro z hz
    obtain ⟨a, ha, b, hb, he, _⟩ := (ZFSet.mem_sep.mp hz).2
    exact ⟨a, ha, b, hb, he⟩
  · intro a ha
    obtain ⟨b, hb, hu⟩ := hR a ha
    refine ⟨b, ⟨hb.1, mem_relationGraph_iff.mpr ⟨ha, hb.1, hb.2⟩⟩, ?_⟩
    intro c hc
    exact hu c ⟨hc.1, (mem_relationGraph_iff.mp hc.2).2.2⟩

def functionOfRelation (A B : ZFSet.{u})
    (R : ZFSet.{u} → ZFSet.{u} → Prop) : ZFSet.{u} :=
  functionTriple A B (relationGraph A B R)

theorem functionOfRelation_mem {A B : ZFSet.{u}}
    {R : ZFSet.{u} → ZFSet.{u} → Prop}
    (hR : ∀ a : ZFSet.{u}, a ∈ A → ∃! b : ZFSet.{u}, b ∈ B ∧ R a b) :
    functionOfRelation A B R ∈ functionSpace A B :=
  TA_PRO_00014_mem_functionSpace_iff.mpr ⟨relationGraph A B R, rfl, relationGraph_isFunc hR⟩

theorem functionOfRelation_value_iff {A B a b : ZFSet.{u}}
    {R : ZFSet.{u} → ZFSet.{u} → Prop} :
    FunctionValue A B (functionOfRelation A B R) a b ↔
      a ∈ A ∧ b ∈ B ∧ R a b :=
  (functionValue_iff_graph (G := relationGraph A B R) rfl).trans mem_relationGraph_iff

/-- Grafo de una asignación explícitamente definida; no hay elección. -/
def mapGraph (A B : ZFSet.{u}) (f : ZFSet.{u} → ZFSet.{u}) : ZFSet.{u} :=
  relationGraph A B (fun a b => b = f a)

theorem mapGraph_isFunc {A B : ZFSet.{u}} {f : ZFSet.{u} → ZFSet.{u}}
    (hf : ∀ a : ZFSet.{u}, a ∈ A → f a ∈ B) :
    IsFuncFoundational A B (mapGraph A B f) := by
  apply relationGraph_isFunc
  intro a ha
  exact ⟨f a, ⟨hf a ha, rfl⟩, fun _ h => h.2⟩

theorem mem_mapGraph_iff {A B a b : ZFSet.{u}} {f : ZFSet.{u} → ZFSet.{u}} :
    ZFSet.pair a b ∈ mapGraph A B f ↔ a ∈ A ∧ b ∈ B ∧ b = f a :=
  mem_relationGraph_iff

/-- Grafo de una asignación binaria, con dominio el producto A × A. -/
def binaryMapGraph (A B : ZFSet.{u})
    (f : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}) : ZFSet.{u} :=
  relationGraph (cartesianProductFoundational A A) B
    (fun p z => ∃ a : ZFSet.{u}, a ∈ A ∧ ∃ b : ZFSet.{u}, b ∈ A ∧
      p = ZFSet.pair a b ∧ z = f a b)

theorem mem_binaryMapGraph_iff {A B a b z : ZFSet.{u}}
    {f : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}} :
    ZFSet.pair (ZFSet.pair a b) z ∈ binaryMapGraph A B f ↔
      a ∈ A ∧ b ∈ A ∧ z ∈ B ∧ z = f a b := by
  constructor
  · intro h
    obtain ⟨_, hz, x, hx, y, hy, he, hval⟩ := mem_relationGraph_iff.mp h
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective he
    exact ⟨hx, hy, hz, hval⟩
  · rintro ⟨ha, hb, hz, he⟩
    exact mem_relationGraph_iff.mpr ⟨mem_cartesianProductFoundational.mpr ⟨ha, hb⟩,
      hz, a, ha, b, hb, rfl, he⟩

theorem binaryMapGraph_isFunc {A B : ZFSet.{u}}
    {f : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}}
    (hf : ∀ a b : ZFSet.{u}, a ∈ A → b ∈ A → f a b ∈ B) :
    IsFuncFoundational (cartesianProductFoundational A A) B (binaryMapGraph A B f) := by
  apply relationGraph_isFunc
  intro p hp
  obtain ⟨a, ha, b, hb, rfl⟩ := (ZFSet.mem_sep.mp hp).2
  refine ⟨f a b, ⟨hf a b ha hb, a, ha, b, hb, rfl, rfl⟩, ?_⟩
  intro z hz
  obtain ⟨x, _, y, _, he, hval⟩ := hz.2
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective he
  exact hval

end TratadoAnalisis.Foundations.RelationalFunctions
