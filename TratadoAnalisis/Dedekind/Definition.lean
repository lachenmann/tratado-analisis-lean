import TratadoAnalisis.Rationals.SqrtTwoSet

namespace TratadoAnalisis.Dedekind.Definition

universe u

open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.SqrtTwoSet

/-!
# TA-LEAN-0004 B — definiciones de cortaduras

Los objetos siguen siendo conjuntos de racionales del tratado. Las dos
condiciones negativas de la definición no se sustituyen por testigos.
La aritmética racional permanece expresada mediante relaciones de grafo.
-/

/-- TA-THM-00001 especializado a objetos ZFSet, sin pasar por Chapter0. -/
theorem TA_THM_00001_zfset_eq_iff_subset {A B : ZFSet} :
    A = B ↔ A ⊆ B ∧ B ⊆ A := by
  constructor
  · intro h
    subst B
    exact ⟨fun _ hx => hx, fun _ hx => hx⟩
  · rintro ⟨hAB, hBA⟩
    apply ZFSet.ext
    intro z
    exact ⟨fun hz => hAB hz, fun hz => hBA hz⟩

/-- TA-DEF-00079 — lado inferior propio, no vacío y sin máximo. -/
def IsDedekindCut (α : ZFSet) : Prop :=
  α ⊆ rationalsTA ∧
  α ≠ ∅ ∧
  α ≠ rationalsTA ∧
  (∀ r : ZFSet, r ∈ α →
    ∀ s : ZFSet, s ∈ rationalsTA → RatLT s r → s ∈ α) ∧
  ∀ r : ZFSet, r ∈ α →
    ∃ s : ZFSet, s ∈ α ∧ RatLT r s

/-- Especificación de las cuatro condiciones y su ambiente racional. -/
theorem TA_DEF_00079_isDedekindCut_iff {α : ZFSet} :
    IsDedekindCut α ↔
      α ⊆ rationalsTA ∧
      α ≠ ∅ ∧
      α ≠ rationalsTA ∧
      (∀ r : ZFSet, r ∈ α →
        ∀ s : ZFSet, s ∈ rationalsTA → RatLT s r → s ∈ α) ∧
      ∀ r : ZFSet, r ∈ α →
        ∃ s : ZFSet, s ∈ α ∧ RatLT r s := by
  rfl

/-- TA-DEF-00080 — el conjunto D es el conjunto subyacente del modelo. -/
def dedekindCutsTA : ZFSet :=
  ZFSet.sep IsDedekindCut (ZFSet.powerset rationalsTA)

/-- La identificación R_D = D conserva la fórmula de Separación. -/
theorem TA_DEF_00080_dedekindCuts_eq_sep :
    (dedekindCutsTA : ZFSet.{u}) =
      ZFSet.sep IsDedekindCut (ZFSet.powerset rationalsTA) := by
  rfl

/-- TA-PRO-00079 — pertenecer al conjunto equivale a ser una cortadura. -/
theorem TA_PRO_00079_mem_dedekindCuts_iff {α : ZFSet} :
    α ∈ dedekindCutsTA ↔ IsDedekindCut α := by
  constructor
  · intro h
    exact (ZFSet.mem_sep.mp h).2
  · intro h
    exact ZFSet.mem_sep.mpr ⟨ZFSet.mem_powerset.mpr h.1, h⟩

/-- TA-DEF-00081 — sección inferior racional definida por Separación. -/
def rationalSection (q : ZFSet) : ZFSet :=
  ZFSet.sep (fun r => RatLT r q) rationalsTA

/-- Criterio de pertenencia de la sección; no presupone que sea cortadura. -/
theorem TA_DEF_00081_mem_rationalSection_iff {q r : ZFSet} :
    r ∈ rationalSection q ↔ r ∈ rationalsTA ∧ RatLT r q := by
  exact ZFSet.mem_sep

/-- TA-DEF-00082 — negativos junto con el conjunto racional S₂. -/
def alphaTwoCut : ZFSet :=
  ZFSet.sep (fun q => RatLT q ratZero ∨ q ∈ sqrtTwoSet) rationalsTA

/-- Criterio de pertenencia de la cortadura cuadrática candidata. -/
theorem TA_DEF_00082_mem_alphaTwoCut_iff {q : ZFSet} :
    q ∈ alphaTwoCut ↔
      q ∈ rationalsTA ∧ (RatLT q ratZero ∨ q ∈ sqrtTwoSet) := by
  exact ZFSet.mem_sep

/-- TA-DEF-00083 — inclusión con ambos argumentos en el modelo de Dedekind. -/
def DedLE (α β : ZFSet) : Prop :=
  α ∈ dedekindCutsTA ∧ β ∈ dedekindCutsTA ∧ α ⊆ β

/-- Sobre cortaduras, el orden de Dedekind es exactamente inclusión. -/
theorem TA_DEF_00083_dedLE_iff_subset
    {α β : ZFSet}
    (hα : α ∈ dedekindCutsTA)
    (hβ : β ∈ dedekindCutsTA) :
    DedLE α β ↔ α ⊆ β := by
  constructor
  · intro h
    exact h.2.2
  · intro h
    exact ⟨hα, hβ, h⟩

end TratadoAnalisis.Dedekind.Definition
