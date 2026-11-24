import TratadoAnalisis.Naturals.Recursion

namespace TratadoAnalisis.Foundations.FunctionTriple
universe u
open TratadoAnalisis.Naturals.Recursion

/-- Tupla recursiva de TA-0001 §8.3: ⟨A, ⟨B, G⟩⟩. -/
def functionTriple (A B G : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.pair A (ZFSet.pair B G)

theorem functionTriple_eq_iff {A B G A' B' G' : ZFSet.{u}} :
    functionTriple A B G = functionTriple A' B' G' ↔
      A = A' ∧ B = B' ∧ G = G' := by
  constructor
  · intro h
    rcases ZFSet.pair_injective h with ⟨ha, hbg⟩
    rcases ZFSet.pair_injective hbg with ⟨hb, hg⟩
    exact ⟨ha, hb, hg⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/-- Un objeto función con dominio y codominio fijados y grafo funcional. -/
def IsFunctionTriple (A B f : ZFSet.{u}) : Prop :=
  ∃ G : ZFSet.{u}, f = functionTriple A B G ∧ IsFuncFoundational A B G

/-- TA-DEF-00018: criterio de decodificación y puente al grafo. -/
theorem TA_DEF_00018_functionTriple_iff {A B G : ZFSet.{u}} :
    IsFunctionTriple A B (functionTriple A B G) ↔
      IsFuncFoundational A B G := by
  constructor
  · rintro ⟨G', he, hg⟩
    have h := (functionTriple_eq_iff.mp he).2.2
    rw [h]
    exact hg
  · intro hg
    exact ⟨G, rfl, hg⟩

theorem functionTriple_graph_unique {A B f G H : ZFSet.{u}}
    (hg : f = functionTriple A B G) (hh : f = functionTriple A B H) :
    G = H :=
  (functionTriple_eq_iff.mp (hg.symm.trans hh)).2.2

end TratadoAnalisis.Foundations.FunctionTriple
