import TratadoAnalisis.Abstract.NumeralStepGraph0008

/-!
# TA-LEAN-0008 — Etapa 5B (candidato, no compilado)

Grafo de numerales sobre `omegaTA` construido mediante el teorema
fundacional de recursión del tratado, sin elegir una función metateórica
`nu : ZFSet → ZFSet` y sin reemplazar los naturales por `Nat`.
-/

namespace TratadoAnalisis.AbstractCompleteness.Manual0008

open TratadoAnalisis.Dedekind.FieldPredicates
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Naturals.Foundational

/-- Grafo recursivo de ν_F, como ZFSet de pares de Kuratowski. -/
def CanonicalNumeralGraphManual (F zero one : ZFSet)
    (add : ZFSet → ZFSet → ZFSet → Prop) : ZFSet :=
  globalRecursionGraph F zero (NumeralStepGraphManual F one add)

/-- Funcionalidad total del grafo ω_TA → F. -/
theorem canonicalNumeralGraph_isFunc_manual
    (F zero one : ZFSet)
    (add : ZFSet → ZFSet → ZFSet → Prop)
    (hzero : zero ∈ F) (hone : one ∈ F)
    (hadd : IsBinaryOperationFoundational F add) :
    IsFuncFoundational omegaTA F (CanonicalNumeralGraphManual F zero one add) := by
  unfold CanonicalNumeralGraphManual
  exact globalRecursionGraph_isFunc hzero
    (numeralStepGraph_isFunc_manual F one add hadd hone)

/-- ν_F(0) = 0_F, expresado por pertenencia a un grafo. -/
theorem canonicalNumeralGraph_zero_manual
    (F zero one : ZFSet)
    (add : ZFSet → ZFSet → ZFSet → Prop)
    (hzero : zero ∈ F) :
    ZFSet.pair (∅ : ZFSet) zero ∈ CanonicalNumeralGraphManual F zero one add := by
  unfold CanonicalNumeralGraphManual
  exact globalRecursionGraph_zero hzero

/-- ν_F(S(n)) = ν_F(n)+1_F, sin función global escogida. -/
theorem canonicalNumeralGraph_succ_manual
    (F zero one : ZFSet)
    (add : ZFSet → ZFSet → ZFSet → Prop)
    (hzero : zero ∈ F) (hone : one ∈ F)
    (hadd : IsBinaryOperationFoundational F add)
    {n x y : ZFSet}
    (hn : n ∈ omegaTA)
    (hnx : ZFSet.pair n x ∈ CanonicalNumeralGraphManual F zero one add)
    (hx : x ∈ F) (hy : y ∈ F)
    (hxy : add x one y) :
    ZFSet.pair (succ n) y ∈ CanonicalNumeralGraphManual F zero one add := by
  have hg : IsFuncFoundational F F (NumeralStepGraphManual F one add) :=
    numeralStepGraph_isFunc_manual F one add hadd hone
  have hstep : ZFSet.pair x y ∈ NumeralStepGraphManual F one add :=
    (numeralStepGraph_mem_iff_manual F one add x y).mpr ⟨hx, hy, hxy⟩
  unfold CanonicalNumeralGraphManual at hnx ⊢
  exact globalRecursionGraph_succ hzero hg hn hnx hstep

/-- Imagen conjuntista de ν_F por separación; no presupone Choice. -/
def NumeralGraphImageManual (F G : ZFSet) : ZFSet :=
  ZFSet.sep
    (fun y => ∃ n : ZFSet, n ∈ omegaTA ∧ ZFSet.pair n y ∈ G) F

theorem mem_numeralGraphImage_iff_manual (F G y : ZFSet) :
    y ∈ NumeralGraphImageManual F G ↔
      y ∈ F ∧ ∃ n : ZFSet, n ∈ omegaTA ∧ ZFSet.pair n y ∈ G := by
  exact ZFSet.mem_sep

/-- Los numerales construidos pertenecen a F. -/
theorem numeralGraphImage_subset_manual (F G : ZFSet) :
    NumeralGraphImageManual F G ⊆ F := by
  intro y hy
  exact ((mem_numeralGraphImage_iff_manual F G y).mp hy).1

/-- El cero del cuerpo pertenece a la imagen del grafo. -/
theorem numeralGraphImage_zero_manual
    (F zero one : ZFSet)
    (add : ZFSet → ZFSet → ZFSet → Prop)
    (hzero : zero ∈ F) :
    zero ∈ NumeralGraphImageManual F
      (CanonicalNumeralGraphManual F zero one add) := by
  apply (mem_numeralGraphImage_iff_manual F
    (CanonicalNumeralGraphManual F zero one add) zero).mpr
  exact ⟨hzero, (∅ : ZFSet), omegaTA_isInductive.1,
    canonicalNumeralGraph_zero_manual F zero one add hzero⟩

/-- La imagen del grafo es cerrada por suma relacional de 1. -/
theorem numeralGraphImage_successor_closed_manual
    (F zero one : ZFSet)
    (add : ZFSet → ZFSet → ZFSet → Prop)
    (hzero : zero ∈ F) (hone : one ∈ F)
    (hadd : IsBinaryOperationFoundational F add) :
    ∀ x : ZFSet,
      x ∈ NumeralGraphImageManual F
        (CanonicalNumeralGraphManual F zero one add) →
      ∃ y : ZFSet,
        y ∈ NumeralGraphImageManual F
          (CanonicalNumeralGraphManual F zero one add) ∧
        add x one y := by
  intro x hx
  let G : ZFSet := CanonicalNumeralGraphManual F zero one add
  have hmem : x ∈ F ∧ ∃ n : ZFSet, n ∈ omegaTA ∧ ZFSet.pair n x ∈ G :=
    (mem_numeralGraphImage_iff_manual F G x).mp hx
  rcases hmem with ⟨hxF, n, hn, hnx⟩
  obtain ⟨y, ⟨hyF, hxy⟩, _⟩ := hadd x hxF one hone
  have hsucc : ZFSet.pair (succ n) y ∈ G :=
    canonicalNumeralGraph_succ_manual
      F zero one add hzero hone hadd hn hnx hxF hyF hxy
  have hyImage : y ∈ NumeralGraphImageManual F G :=
    (mem_numeralGraphImage_iff_manual F G y).mpr
      ⟨hyF, succ n, TA_PRO_00022_succ_closed hn, hsucc⟩
  exact ⟨y, hyImage, hxy⟩

#check CanonicalNumeralGraphManual
#check canonicalNumeralGraph_isFunc_manual
#print axioms canonicalNumeralGraph_isFunc_manual
#check numeralGraphImage_successor_closed_manual
#print axioms numeralGraphImage_successor_closed_manual

end TratadoAnalisis.AbstractCompleteness.Manual0008
