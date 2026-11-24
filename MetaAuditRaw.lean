import Mathlib.SetTheory.ZFC.Basic

namespace MetaAuditRaw

open ZFSet

/-- Grafo funcional expresado directamente mediante pares de Kuratowski,
sin usar ZFSet.prod. -/
def IsFuncRaw (A B f : ZFSet) : Prop :=
  (∀ z : ZFSet, z ∈ f →
    ∃ a : ZFSet, a ∈ A ∧
      ∃ b : ZFSet, b ∈ B ∧ z = ZFSet.pair a b) ∧
  ∀ a : ZFSet, a ∈ A →
    ∃! b : ZFSet, b ∈ B ∧ ZFSet.pair a b ∈ f

/-- Restricción expresada por separación directa:
los elementos de f que son pares (c,b) con c ∈ C y b ∈ B. -/
def restrictRaw (f C B : ZFSet) : ZFSet :=
  ZFSet.sep
    (fun z =>
      ∃ c : ZFSet, c ∈ C ∧
        ∃ b : ZFSet, b ∈ B ∧ z = ZFSet.pair c b)
    f

theorem restrictionRaw {A B C f : ZFSet}
    (hC : C ⊆ A)
    (hf : IsFuncRaw A B f) :
    IsFuncRaw C B (restrictRaw f C B) := by
  constructor
  · intro z hz
    rcases (ZFSet.mem_sep.mp hz).2 with ⟨c, hc, b, hb, hpair⟩
    exact ⟨c, hc, b, hb, hpair⟩

  · intro c hc
    rcases hf.2 c (hC hc) with ⟨b, hb, huniq⟩
    refine ⟨b, ?_, ?_⟩
    · refine ⟨hb.1, ?_⟩
      apply ZFSet.mem_sep.mpr
      refine ⟨hb.2, ?_⟩
      exact ⟨c, hc, b, hb.1, rfl⟩
    · intro y hy
      apply huniq y
      exact ⟨hy.1, (ZFSet.mem_sep.mp hy.2).1⟩

#print axioms IsFuncRaw
#print axioms restrictRaw
#print axioms restrictionRaw

end MetaAuditRaw