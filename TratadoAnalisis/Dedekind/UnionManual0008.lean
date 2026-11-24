import TratadoAnalisis.Dedekind.Definition

/-!
TA-LEAN-0008 — prototipos manuales de TA-PRO-00105 y TA-THM-00055.
Estado: CANDIDATO NO COMPILADO. No sustituye la certificación del proyecto.

Ubicación de prueba sugerida:
  TratadoAnalisis/Dedekind/UnionManual0008.lean

Usa únicamente la construcción propia de cortaduras, el axioma de Unión
modelado por ZFSet.sUnion y eliminación explícita de tercero excluido.
-/


namespace TratadoAnalisis.Dedekind.Manual0008

open TratadoAnalisis.Dedekind.Definition
open TratadoAnalisis.Rationals.Construction

/-- Extrae un testigo de una no vaciedad NEGATIVA, bajo tercero excluido
    recibido como hipótesis. No es una función de elección. -/
private theorem exists_mem_of_ne_empty
    (em : ∀ p : Prop, p ∨ ¬p)
    (X : ZFSet) (hne : X ≠ ∅) :
    ∃ x : ZFSet, x ∈ X := by
  rcases em (∃ x : ZFSet, x ∈ X) with hx | hnot
  · exact hx
  · have hzero : X = ∅ := by
      apply (ZFSet.eq_empty X).mpr
      intro x hx
      exact hnot ⟨x, hx⟩
    exact False.elim (hne hzero)

/-- TA-PRO-00105: una familia no vacía de cortaduras, si tiene una cota
    superior en el orden propio DedLE, posee unión que es cortadura.

    Los testigos del enunciado son locales. La prueba conserva la teoría
    objeto: ZFSet, IsDedekindCut, dedekindCutsTA, DedLE y sUnion.
-/
theorem TA_PRO_00105_union_is_cut_manual
    (em : ∀ p : Prop, p ∨ ¬p)
    (A : ZFSet)
    (hfamily : A ⊆ dedekindCutsTA)
    (hnonempty : A ≠ ∅)
    (hbounded : ∃ b : ZFSet, b ∈ dedekindCutsTA ∧
      ∀ a : ZFSet, a ∈ A → DedLE a b) :
    ZFSet.sUnion A ∈ dedekindCutsTA := by
  rcases hbounded with ⟨b, hb, hupper⟩
  have hbcut : IsDedekindCut b :=
    (TA_PRO_00079_mem_dedekindCuts_iff).mp hb
  rcases exists_mem_of_ne_empty em A hnonempty with ⟨a0, ha0⟩
  have ha0cut : IsDedekindCut a0 :=
    (TA_PRO_00079_mem_dedekindCuts_iff).mp (hfamily ha0)
  apply (TA_PRO_00079_mem_dedekindCuts_iff).mpr
  unfold IsDedekindCut
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- La unión está incluida en los racionales propios.
    intro q hq
    obtain ⟨a, ha, hqa⟩ := ZFSet.mem_sUnion.mp hq
    have hacut : IsDedekindCut a :=
      (TA_PRO_00079_mem_dedekindCuts_iff).mp (hfamily ha)
    exact hacut.1 hqa
  · -- La unión no está vacía.
    intro hzero
    rcases exists_mem_of_ne_empty em a0 ha0cut.2.1 with ⟨q, hqa0⟩
    have hqu : q ∈ ZFSet.sUnion A :=
      ZFSet.mem_sUnion.mpr ⟨a0, ha0, hqa0⟩
    rw [hzero] at hqu
    exact ZFSet.notMem_empty q hqu
  · -- La unión es propia: está contenida en una cortadura b ≠ ℚ.
    intro hwhole
    have hbeq : b = rationalsTA := by
      apply (TA_THM_00001_zfset_eq_iff_subset).mpr
      constructor
      · exact hbcut.1
      · intro q hqrat
        have hqu : q ∈ ZFSet.sUnion A := by
          rw [hwhole]
          exact hqrat
        obtain ⟨a, ha, hqa⟩ := ZFSet.mem_sUnion.mp hqu
        have hle : DedLE a b := hupper a ha
        exact hle.2.2 hqa
    exact hbcut.2.2.1 hbeq
  · -- La clausura inferior se hereda de la cortadura testigo.
    intro r hr s hsRat hsr
    obtain ⟨a, ha, hra⟩ := ZFSet.mem_sUnion.mp hr
    have hacut : IsDedekindCut a :=
      (TA_PRO_00079_mem_dedekindCuts_iff).mp (hfamily ha)
    exact ZFSet.mem_sUnion.mpr
      ⟨a, ha, hacut.2.2.2.1 r hra s hsRat hsr⟩
  · -- La ausencia de máximo se hereda de la cortadura testigo.
    intro r hr
    obtain ⟨a, ha, hra⟩ := ZFSet.mem_sUnion.mp hr
    have hacut : IsDedekindCut a :=
      (TA_PRO_00079_mem_dedekindCuts_iff).mp (hfamily ha)
    obtain ⟨s, hsa, hrs⟩ := hacut.2.2.2.2 r hra
    exact ⟨s, ZFSet.mem_sUnion.mpr ⟨a, ha, hsa⟩, hrs⟩

/-- La unión es efectivamente el supremo: este predicado reúne las
    tres obligaciones que expresa TA-THM-00055. -/
def IsLeastUpperBoundDedekind (A s : ZFSet) : Prop :=
  s ∈ dedekindCutsTA ∧
  (∀ a : ZFSet, a ∈ A → DedLE a s) ∧
  (∀ b : ZFSet, b ∈ dedekindCutsTA →
    (∀ a : ZFSet, a ∈ A → DedLE a b) → DedLE s b)

/-- TA-THM-00055: el supremo de A es su unión, mediante la definición
    conjuntista del orden. Se apoya en el prototipo TA-PRO-00105. -/
theorem TA_THM_00055_union_is_lub_manual
    (em : ∀ p : Prop, p ∨ ¬p)
    (A : ZFSet)
    (hfamily : A ⊆ dedekindCutsTA)
    (hnonempty : A ≠ ∅)
    (hbounded : ∃ b : ZFSet, b ∈ dedekindCutsTA ∧
      ∀ a : ZFSet, a ∈ A → DedLE a b) :
    IsLeastUpperBoundDedekind A (ZFSet.sUnion A) := by
  have hU : ZFSet.sUnion A ∈ dedekindCutsTA :=
    TA_PRO_00105_union_is_cut_manual em A hfamily hnonempty hbounded
  refine ⟨hU, ?_, ?_⟩
  · intro a ha
    refine ⟨hfamily ha, hU, ?_⟩
    intro q hqa
    exact ZFSet.mem_sUnion.mpr ⟨a, ha, hqa⟩
  · intro b hb hupper
    refine ⟨hU, hb, ?_⟩
    intro q hqu
    obtain ⟨a, ha, hqa⟩ := ZFSet.mem_sUnion.mp hqu
    exact (hupper a ha).2.2 hqa

#check TA_PRO_00105_union_is_cut_manual
#print axioms TA_PRO_00105_union_is_cut_manual
#check TA_THM_00055_union_is_lub_manual
#print axioms TA_THM_00055_union_is_lub_manual

end TratadoAnalisis.Dedekind.Manual0008
