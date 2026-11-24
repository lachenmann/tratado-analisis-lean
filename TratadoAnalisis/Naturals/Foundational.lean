import Mathlib.SetTheory.ZFC.Basic

/-!
# TA-LEAN-0002 — Reconstrucción fundacional de ℕ = ω

Primera etapa: reconstrucción del núcleo inductivo de TA-0004 dentro de `ZFSet`.
La existencia inicial de un conjunto inductivo se instancia todavía mediante
`ZFSet.omega`; a partir de un inductivo arbitrario `I`, la definición de
`omegaKernel`, su inductividad, minimalidad, independencia y el principio de
inducción reproducen la arquitectura del tratado.
-/

namespace TratadoAnalisis.Naturals.Foundational

open ZFSet

/-- TA-DEF-00030 — sucesor de von Neumann. -/
def succ (x : ZFSet) : ZFSet := insert x x

/-- TA-DEF-00031 — un conjunto contiene cero y es cerrado por sucesor. -/
def IsInductive (I : ZFSet) : Prop :=
  (∅ : ZFSet) ∈ I ∧ ∀ x : ZFSet, x ∈ I → succ x ∈ I

/-- TA-PRO-00019, todavía como puente: `ZFSet.omega` proporciona un testigo
explícito de la existencia de un conjunto inductivo. -/
theorem TA_PRO_00019_exists_inductive : ∃ I : ZFSet, IsInductive I := by
  refine ⟨ZFSet.omega, ?_⟩
  constructor
  · exact ZFSet.omega_zero
  · intro x hx
    exact ZFSet.omega_succ hx

/-- El `omega` estándar de mathlib es inductivo. Se usa sólo como testigo
canónico para instanciar la construcción una vez probada su independencia. -/
theorem standardOmega_isInductive : IsInductive ZFSet.omega := by
  constructor
  · exact ZFSet.omega_zero
  · intro x hx
    exact ZFSet.omega_succ hx

/-- TA-DEF-00032 — núcleo inductivo dentro de un conjunto ambiente `I`.

Corresponde exactamente a
`{x ∈ I | ∀ J, J ⊆ I → IsInductive J → x ∈ J}`.
-/
def omegaKernel (I : ZFSet) : ZFSet :=
  ZFSet.sep
    (fun x => ∀ J : ZFSet, J ⊆ I → IsInductive J → x ∈ J)
    I

@[simp]
theorem mem_omegaKernel {I x : ZFSet} :
    x ∈ omegaKernel I ↔
      x ∈ I ∧ ∀ J : ZFSet, J ⊆ I → IsInductive J → x ∈ J := by
  simp [omegaKernel]

/-- La intersección de dos conjuntos inductivos es inductiva. -/
theorem inductive_inter {I J : ZFSet}
    (hI : IsInductive I) (hJ : IsInductive J) :
    IsInductive (I ∩ J) := by
  constructor
  · exact ZFSet.mem_inter.mpr ⟨hI.1, hJ.1⟩
  · intro x hx
    rcases ZFSet.mem_inter.mp hx with ⟨hxI, hxJ⟩
    exact ZFSet.mem_inter.mpr ⟨hI.2 x hxI, hJ.2 x hxJ⟩

/-- TA-PRO-00020 — el núcleo inductivo de un inductivo es inductivo. -/
theorem TA_PRO_00020_omegaKernel_isInductive {I : ZFSet}
    (hI : IsInductive I) : IsInductive (omegaKernel I) := by
  constructor
  · apply mem_omegaKernel.mpr
    refine ⟨hI.1, ?_⟩
    intro J hJI hJ
    exact hJ.1
  · intro x hx
    rcases mem_omegaKernel.mp hx with ⟨hxI, hxAll⟩
    apply mem_omegaKernel.mpr
    refine ⟨hI.2 x hxI, ?_⟩
    intro J hJI hJ
    exact hJ.2 x (hxAll J hJI hJ)

/-- TA-THM-00006 — minimalidad del núcleo inductivo respecto de todo
conjunto inductivo, no sólo de los contenidos en `I`. -/
theorem TA_THM_00006_omegaKernel_minimal {I J : ZFSet}
    (hI : IsInductive I) (hJ : IsInductive J) :
    omegaKernel I ⊆ J := by
  intro x hx
  have hIJ : IsInductive (I ∩ J) := inductive_inter hI hJ
  have hSub : I ∩ J ⊆ I := by
    intro z hz
    exact (ZFSet.mem_inter.mp hz).1
  have hxInter : x ∈ I ∩ J :=
    (mem_omegaKernel.mp hx).2 (I ∩ J) hSub hIJ
  exact (ZFSet.mem_inter.mp hxInter).2

/-- TA-THM-00007 — independencia del conjunto inductivo ambiente. -/
theorem TA_THM_00007_omegaKernel_independent {I J : ZFSet}
    (hI : IsInductive I) (hJ : IsInductive J) :
    omegaKernel I = omegaKernel J := by
  apply ZFSet.ext
  intro x
  constructor
  · intro hx
    exact TA_THM_00006_omegaKernel_minimal hI
      (TA_PRO_00020_omegaKernel_isInductive hJ) hx
  · intro hx
    exact TA_THM_00006_omegaKernel_minimal hJ
      (TA_PRO_00020_omegaKernel_isInductive hI) hx

/-- TA-NOT-00007 — instancia canónica del conjunto construido.

La elección de `ZFSet.omega` como ambiente no introduce una elección
matemática: la independencia anterior demuestra que cualquier ambiente
inductivo produce el mismo núcleo.
-/
def omegaTA : ZFSet := omegaKernel ZFSet.omega

/-- El `omega` construido por el tratado es inductivo. -/
theorem omegaTA_isInductive : IsInductive omegaTA := by
  exact TA_PRO_00020_omegaKernel_isInductive standardOmega_isInductive

/-- El `omega` construido está contenido en todo conjunto inductivo. -/
theorem omegaTA_minimal (J : ZFSet) (hJ : IsInductive J) :
    omegaTA ⊆ J := by
  exact TA_THM_00006_omegaKernel_minimal standardOmega_isInductive hJ

/-- Cualquier ambiente inductivo produce literalmente `omegaTA`. -/
theorem omegaTA_eq_kernel {I : ZFSet} (hI : IsInductive I) :
    omegaTA = omegaKernel I := by
  exact TA_THM_00007_omegaKernel_independent standardOmega_isInductive hI

/-- TA-THM-00008 — principio de inducción en forma de predicados.

Si `P` vale en cero y se preserva por sucesor dentro de `omegaTA`, entonces
vale para todo miembro de `omegaTA`.
-/
theorem TA_THM_00008_induction
    (P : ZFSet → Prop)
    (h0 : P (∅ : ZFSet))
    (hs : ∀ n : ZFSet, n ∈ omegaTA → P n → P (succ n)) :
    ∀ n : ZFSet, n ∈ omegaTA → P n := by
  let A : ZFSet := ZFSet.sep P omegaTA
  have hA : IsInductive A := by
    constructor
    · exact ZFSet.mem_sep.mpr ⟨omegaTA_isInductive.1, h0⟩
    · intro n hnA
      have hnOmega : n ∈ omegaTA := (ZFSet.mem_sep.mp hnA).1
      have hnP : P n := (ZFSet.mem_sep.mp hnA).2
      exact ZFSet.mem_sep.mpr
        ⟨omegaTA_isInductive.2 n hnOmega, hs n hnOmega hnP⟩
  have hMin : omegaTA ⊆ A := omegaTA_minimal A hA
  intro n hn
  exact (ZFSet.mem_sep.mp (hMin hn)).2

/-- TA-PRO-00022 — clausura de `omegaTA` por sucesor. -/
theorem TA_PRO_00022_succ_closed {n : ZFSet} (hn : n ∈ omegaTA) :
    succ n ∈ omegaTA := by
  exact omegaTA_isInductive.2 n hn

/-- TA-PRO-00023 — ningún sucesor es el conjunto vacío. -/
theorem TA_PRO_00023_succ_ne_zero (n : ZFSet) :
    succ n ≠ (∅ : ZFSet) := by
  intro h
  have hn : n ∈ succ n := ZFSet.mem_insert n n
  rw [h] at hn
  exact ZFSet.notMem_empty n hn

/-! ## TA-LEAN-0002 — Etapa B: estructura de von Neumann y Peano -/

/-- TA-DEF-00033 — transitividad conjuntista. -/
def IsTransitive (T : ZFSet) : Prop :=
  ∀ x : ZFSet, x ∈ T → x ⊆ T

/-- Todo conjunto está contenido en su sucesor de von Neumann. -/
theorem subset_succ (n : ZFSet) : n ⊆ succ n := by
  intro z hz
  exact ZFSet.mem_insert_of_mem n hz

/-- TA-PRO-00021 — todo natural construido es transitivo e irreflexivo. -/
theorem TA_PRO_00021_transitive_irreflexive {n : ZFSet}
    (hn : n ∈ omegaTA) :
    IsTransitive n ∧ n ∉ n := by
  let P : ZFSet → Prop := fun k => IsTransitive k ∧ k ∉ k

  have h0 : P (∅ : ZFSet) := by
    constructor
    · intro x hx
      exact (ZFSet.notMem_empty x hx).elim
    · exact ZFSet.notMem_empty (∅ : ZFSet)

  have hs : ∀ k : ZFSet, k ∈ omegaTA → P k → P (succ k) := by
    intro k _hk ih
    rcases ih with ⟨hTrans, hIrrefl⟩
    constructor
    · intro x hx
      rcases ZFSet.mem_insert_iff.mp hx with hEq | hxk
      · subst x
        exact subset_succ k
      · intro z hzx
        exact subset_succ k (hTrans x hxk hzx)
    · intro hSelf
      rcases ZFSet.mem_insert_iff.mp hSelf with hEq | hMem
      · have hkMem : k ∈ succ k := ZFSet.mem_insert k k
        rw [hEq] at hkMem
        exact hIrrefl hkMem
      · have hSub : succ k ⊆ k := hTrans (succ k) hMem
        have hkMem : k ∈ succ k := ZFSet.mem_insert k k
        exact hIrrefl (hSub hkMem)

  exact TA_THM_00008_induction P h0 hs n hn

/-- TA-THM-00009 — inyectividad del sucesor en los naturales construidos. -/
theorem TA_THM_00009_succ_injective {m n : ZFSet}
    (_hm : m ∈ omegaTA) (hn : n ∈ omegaTA)
    (hEq : succ m = succ n) :
    m = n := by
  have hmInSuccN : m ∈ succ n := by
    rw [← hEq]
    exact ZFSet.mem_insert m m

  have hnInSuccM : n ∈ succ m := by
    rw [hEq]
    exact ZFSet.mem_insert n n

  rcases ZFSet.mem_insert_iff.mp hmInSuccN with hmn | hmn
  · exact hmn
  rcases ZFSet.mem_insert_iff.mp hnInSuccM with hnm | hnm
  · exact hnm.symm

  have hTransN : IsTransitive n :=
    (TA_PRO_00021_transitive_irreflexive hn).1
  have hmSubsetN : m ⊆ n := hTransN m hmn
  have hnn : n ∈ n := hmSubsetN hnm
  exact ((TA_PRO_00021_transitive_irreflexive hn).2 hnn).elim

/-- TA-THM-00010 — paquete de Peano obtenido como teorema de la construcción. -/
theorem TA_THM_00010_peano :
    (∅ : ZFSet) ∈ omegaTA ∧
    (∀ n : ZFSet, n ∈ omegaTA → succ n ∈ omegaTA) ∧
    (∀ n : ZFSet, n ∈ omegaTA → succ n ≠ (∅ : ZFSet)) ∧
    (∀ m n : ZFSet,
      m ∈ omegaTA → n ∈ omegaTA → succ m = succ n → m = n) ∧
    (∀ P : ZFSet → Prop,
      P (∅ : ZFSet) →
      (∀ n : ZFSet, n ∈ omegaTA → P n → P (succ n)) →
      ∀ n : ZFSet, n ∈ omegaTA → P n) := by
  constructor
  · exact omegaTA_isInductive.1
  constructor
  · intro n hn
    exact TA_PRO_00022_succ_closed hn
  constructor
  · intro n _hn
    exact TA_PRO_00023_succ_ne_zero n
  constructor
  · intro m n hm hn hEq
    exact TA_THM_00009_succ_injective hm hn hEq
  · intro P h0 hs n hn
    exact TA_THM_00008_induction P h0 hs n hn

end TratadoAnalisis.Naturals.Foundational
