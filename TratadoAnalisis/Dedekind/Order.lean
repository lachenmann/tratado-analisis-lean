import TratadoAnalisis.Dedekind.Definition
import TratadoAnalisis.Rationals.Trichotomy

namespace TratadoAnalisis.Dedekind.Order

open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.Trichotomy
open TratadoAnalisis.Dedekind.Definition

/-- Reflexividad en el dominio, sin tercero excluido. -/
theorem dedLE_refl {α : ZFSet} (hα : α ∈ dedekindCutsTA) : DedLE α α :=
  ⟨hα, hα, fun _ h => h⟩

/-- Antisimetría por doble inclusión, sin tercero excluido. -/
theorem dedLE_antisymm {α β : ZFSet}
    (hαβ : DedLE α β) (hβα : DedLE β α) : α = β :=
  TA_THM_00001_zfset_eq_iff_subset.mpr ⟨hαβ.2.2, hβα.2.2⟩

/-- Transitividad por composición de inclusiones, sin tercero excluido. -/
theorem dedLE_trans {α β γ : ZFSet}
    (hαβ : DedLE α β) (hβγ : DedLE β γ) : DedLE α γ :=
  ⟨hαβ.1, hβγ.2.1, fun _ h => hβγ.2.2 (hαβ.2.2 h)⟩

/-- Extracción explícita con em; no usa lemas de negación de cuantificadores. -/
theorem subset_failure_witness (em : ∀ p : Prop, p ∨ ¬p)
    {A B : ZFSet} (h : ¬ A ⊆ B) :
    ∃ a : ZFSet, a ∈ A ∧ a ∉ B := by
  rcases em (∃ a : ZFSet, a ∈ A ∧ a ∉ B) with hw | hn
  · exact hw
  · apply False.elim
    apply h
    intro a ha
    rcases em (a ∈ B) with hb | hb
    · exact hb
    · exact (hn ⟨a, ha, hb⟩).elim

/-- Un racional exterior es estrictamente mayor que cada miembro.
Solo usa la tricotomía racional proposicional de §3.3. -/
theorem cut_member_lt_nonmember {α r s : ZFSet}
    (hα : IsDedekindCut α) (hr : r ∈ rationalsTA) (hrOut : r ∉ α)
    (hs : s ∈ α) : RatLT s r := by
  have hsQ := hα.1 hs
  rcases TA_PRO_00172_rational_trichotomy hsQ hr with h | he | h
  · exact h
  · rw [he] at hs
    exact (hrOut hs).elim
  · exact (hrOut (hα.2.2.2.1 s hs r hr h)).elim

/-- Un testigo de diferencia fuerza la inclusión inversa, sin em. -/
theorem cut_reverse_subset_of_witness {α β a : ZFSet}
    (hα : IsDedekindCut α) (hβ : IsDedekindCut β)
    (ha : a ∈ α) (haOut : a ∉ β) : β ⊆ α := by
  intro b hb
  have hba := cut_member_lt_nonmember hβ (hα.1 ha) haOut hb
  exact hα.2.2.2.1 a ha b (hβ.1 hb) hba

/-- TA-THM-00040: totalidad con toda la dependencia clásica en la hipótesis. -/
theorem TA_THM_00040_dedLE_total (em : ∀ p : Prop, p ∨ ¬p)
    {α β : ZFSet} (hα : α ∈ dedekindCutsTA) (hβ : β ∈ dedekindCutsTA) :
    DedLE α β ∨ DedLE β α := by
  rcases em (α ⊆ β) with h | h
  · exact Or.inl ⟨hα, hβ, h⟩
  · rcases subset_failure_witness em h with ⟨a, ha, haOut⟩
    have hαCut := TA_PRO_00079_mem_dedekindCuts_iff.mp hα
    have hβCut := TA_PRO_00079_mem_dedekindCuts_iff.mp hβ
    exact Or.inr ⟨hβ, hα, cut_reverse_subset_of_witness hαCut hβCut ha haOut⟩

/-- TA-THM-00040: paquete conjunto de orden total sobre el conjunto concreto. -/
theorem TA_THM_00040_total_order_package (em : ∀ p : Prop, p ∨ ¬p) :
    (∀ α : ZFSet, α ∈ dedekindCutsTA → DedLE α α) ∧
    (∀ α β : ZFSet, α ∈ dedekindCutsTA → β ∈ dedekindCutsTA →
      DedLE α β → DedLE β α → α = β) ∧
    (∀ α β γ : ZFSet, α ∈ dedekindCutsTA → β ∈ dedekindCutsTA →
      γ ∈ dedekindCutsTA → DedLE α β → DedLE β γ → DedLE α γ) ∧
    (∀ α β : ZFSet, α ∈ dedekindCutsTA → β ∈ dedekindCutsTA →
      DedLE α β ∨ DedLE β α) := by
  exact ⟨fun _ h => dedLE_refl h,
    fun _ _ _ _ h h' => dedLE_antisymm h h',
    fun _ _ _ _ _ _ h h' => dedLE_trans h h',
    fun _ _ h h' => TA_THM_00040_dedLE_total em h h'⟩

/-- Orden estricto asociado; no cambia la definición de DedLE. -/
def DedLT (α β : ZFSet) : Prop := DedLE α β ∧ α ≠ β

/-- TA-COR-00015: inclusión propia, sin em ni uso de la totalidad clásica. -/
theorem TA_COR_00015_dedLT_iff_proper_subset {α β : ZFSet}
    (hα : α ∈ dedekindCutsTA) (hβ : β ∈ dedekindCutsTA) :
    DedLT α β ↔ α ⊂ β := by
  constructor
  · rintro ⟨hle, hne⟩
    change α ⊆ β ∧ ¬ β ⊆ α
    exact ⟨hle.2.2, fun hback =>
      hne (TA_THM_00001_zfset_eq_iff_subset.mpr ⟨hle.2.2, hback⟩)⟩
  · intro h
    change α ⊆ β ∧ ¬ β ⊆ α at h
    refine ⟨⟨hα, hβ, h.1⟩, ?_⟩
    intro he
    apply h.2
    rw [he]

/-- Habitabilidad interior: el paso desde α≠∅ recibe em explícitamente. -/
theorem cut_inhabited (em : ∀ p : Prop, p ∨ ¬p)
    {α : ZFSet} (hα : IsDedekindCut α) : ∃ r : ZFSet, r ∈ α := by
  rcases em (∃ r : ZFSet, r ∈ α) with hw | hn
  · exact hw
  · apply False.elim
    apply hα.2.1
    apply TA_THM_00001_zfset_eq_iff_subset.mpr
    constructor
    · intro r hr
      exact (hn ⟨r, hr⟩).elim
    · intro r hr
      exact (ZFSet.notMem_empty r hr).elim

/-- Habitabilidad exterior desde α≠Q, con em explícito. -/
theorem cut_exterior_inhabited (em : ∀ p : Prop, p ∨ ¬p)
    {α : ZFSet} (hα : IsDedekindCut α) :
    ∃ r : ZFSet, r ∈ rationalsTA ∧ r ∉ α := by
  apply subset_failure_witness em
  intro hback
  exact hα.2.2.1 (TA_THM_00001_zfset_eq_iff_subset.mpr ⟨hα.1, hback⟩)

end TratadoAnalisis.Dedekind.Order

