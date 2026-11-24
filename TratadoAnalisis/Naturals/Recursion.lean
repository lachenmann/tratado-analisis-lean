import TratadoAnalisis.Naturals.Foundational
import Mathlib.SetTheory.ZFC.Basic

/-!
# TA-LEAN-0002 — Etapa C1: predecesor y restricción

Primera subetapa de la reconstrucción fundacional del teorema de recursión.
Se formalizan la descomposición de cada natural en cero o sucesor único y la
restricción de un grafo funcional a un subdominio.
-/

namespace TratadoAnalisis.Naturals.Recursion

open ZFSet
open TratadoAnalisis.Naturals.Foundational

/-- TA-THM-00011 — todo natural es cero o tiene un predecesor natural único. -/
theorem TA_THM_00011_predecessor {n : ZFSet} (hn : n ∈ omegaTA) :
    n = (∅ : ZFSet) ∨
      ∃! m : ZFSet, m ∈ omegaTA ∧ n = succ m := by
  let P : ZFSet → Prop := fun k =>
    k = (∅ : ZFSet) ∨ ∃! m : ZFSet, m ∈ omegaTA ∧ k = succ m

  have h0 : P (∅ : ZFSet) := by
    exact Or.inl rfl

  have hs : ∀ k : ZFSet, k ∈ omegaTA → P k → P (succ k) := by
    intro k hk _ih
    right
    refine ⟨k, ⟨hk, rfl⟩, ?_⟩
    intro m hm
    have hmNat : m ∈ omegaTA := hm.1
    have hEq : succ k = succ m := hm.2
    exact TA_THM_00009_succ_injective
      (m := m) (n := k) hmNat hk hEq.symm

  exact TA_THM_00008_induction P h0 hs n hn

/-! ### Puente exacto con la representación de funciones de mathlib -/

/-- TA-DEF-00034 — grafo de la restricción de `f : A → B` al subdominio `C`.

El grafo es `f ∩ (C × B)`, exactamente como en TA-0004. Esta variante usa
`ZFSet.prod` y se conserva como puente de compatibilidad con la API de mathlib.
-/
def restrictGraph (f C B : ZFSet) : ZFSet :=
  f ∩ ZFSet.prod C B

@[simp]
theorem mem_restrictGraph {f C B z : ZFSet} :
    z ∈ restrictGraph f C B ↔ z ∈ f ∧ z ∈ ZFSet.prod C B := by
  simp [restrictGraph]

/-- TA-PRO-00024 — variante puente con `ZFSet.IsFunc`.

La auditoría de esta formulación puede heredar `Classical.choice` de la
implementación de `ZFSet.prod`/`pairSep` en mathlib. Ese hecho pertenece a la
metateoría de la biblioteca, no al `choice-use` del tratado.
-/
theorem TA_PRO_00024_restriction {A B C f : ZFSet}
    (hC : C ⊆ A)
    (hf : ZFSet.IsFunc A B f) :
    ZFSet.IsFunc C B (restrictGraph f C B) := by
  constructor
  · intro z hz
    exact (ZFSet.mem_inter.mp hz).2
  · intro c hc
    rcases hf.2 c (hC hc) with ⟨b, hb, huniq⟩
    have hbB : b ∈ B := by
      exact (ZFSet.pair_mem_prod.mp (hf.1 hb)).2
    refine ⟨b, ?_, ?_⟩
    · exact ZFSet.mem_inter.mpr
        ⟨hb, ZFSet.pair_mem_prod.mpr ⟨hc, hbB⟩⟩
    · intro y hy
      exact huniq y (ZFSet.mem_inter.mp hy).1

/-! ### Variante fundacional directa, sin `ZFSet.prod` -/

/-- Condición de grafo funcional expresada directamente mediante pares de
Kuratowski, evitando `ZFSet.prod` y su infraestructura `pairSep`. -/
def IsFuncFoundational (A B f : ZFSet) : Prop :=
  (∀ z : ZFSet, z ∈ f →
    ∃ a : ZFSet, a ∈ A ∧
      ∃ b : ZFSet, b ∈ B ∧ z = ZFSet.pair a b) ∧
  ∀ a : ZFSet, a ∈ A →
    ∃! b : ZFSet, b ∈ B ∧ ZFSet.pair a b ∈ f

/-- TA-DEF-00034 — variante fundacional de la restricción por separación
explícita de los pares `(c,b)` con `c ∈ C` y `b ∈ B`. -/
def restrictGraphFoundational (f C B : ZFSet) : ZFSet :=
  ZFSet.sep
    (fun z =>
      ∃ c : ZFSet, c ∈ C ∧
        ∃ b : ZFSet, b ∈ B ∧ z = ZFSet.pair c b)
    f

/-- TA-PRO-00024 — certificación fundacional directa de la restricción.

Esta prueba usa sólo separación y pares de Kuratowski; evita la codificación
de producto de mathlib que introduce `Classical.choice` metateórico.
-/
theorem TA_PRO_00024_restriction_foundational {A B C f : ZFSet}
    (hC : C ⊆ A)
    (hf : IsFuncFoundational A B f) :
    IsFuncFoundational C B (restrictGraphFoundational f C B) := by
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


/-! ### Etapa C2a — aproximaciones finitas -/

/-- TA-DEF-00035 — una `n`-aproximación para los datos `(X, x0, g)`.

La función aproximante tiene dominio `S(n)`. La ecuación recursiva se expresa
relacionalmente: si `h(k)=y` y `g(y)=z`, entonces `h(S(k))=z` siempre que
`S(k)` todavía pertenezca al dominio `S(n)`.

Las hipótesis externas `x0 ∈ X`, `g : X → X` y `n ∈ omegaTA` permanecerán
explícitas en los teoremas de existencia y extensión, como en TA-0004.
-/
def IsFiniteApproximation
    (X x0 g n h : ZFSet) : Prop :=
  IsFuncFoundational (succ n) X h ∧
  ZFSet.pair (∅ : ZFSet) x0 ∈ h ∧
  ∀ k : ZFSet, k ∈ omegaTA → succ k ∈ succ n →
    ∀ y z : ZFSet,
      ZFSet.pair k y ∈ h →
      ZFSet.pair y z ∈ g →
      ZFSet.pair (succ k) z ∈ h

/-- Toda aproximación finita es un grafo funcional `S(n) → X`. -/
theorem finiteApproximation_isFunc {X x0 g n h : ZFSet}
    (ha : IsFiniteApproximation X x0 g n h) :
    IsFuncFoundational (succ n) X h :=
  ha.1

/-- Toda aproximación finita toma el valor inicial en cero. -/
theorem finiteApproximation_zero {X x0 g n h : ZFSet}
    (ha : IsFiniteApproximation X x0 g n h) :
    ZFSet.pair (∅ : ZFSet) x0 ∈ h :=
  ha.2.1

/-- Ecuación recursiva de una aproximación finita. -/
theorem finiteApproximation_step {X x0 g n h k y z : ZFSet}
    (ha : IsFiniteApproximation X x0 g n h)
    (hk : k ∈ omegaTA)
    (hsk : succ k ∈ succ n)
    (hky : ZFSet.pair k y ∈ h)
    (hyz : ZFSet.pair y z ∈ g) :
    ZFSet.pair (succ k) z ∈ h :=
  ha.2.2 k hk hsk y z hky hyz


/-! ### Etapa C2b1 — candidato de extensión de una aproximación -/

/-- Grafo candidato para extender una aproximación un paso:
se añade exactamente el par correspondiente al nuevo índice `S(n)`. -/
def extendGraphFoundational (h n z : ZFSet) : ZFSet :=
  insert (ZFSet.pair (succ n) z) h

/-- El grafo original queda contenido en su extensión de un paso. -/
theorem subset_extendGraphFoundational {h n z : ZFSet} :
    h ⊆ extendGraphFoundational h n z := by
  intro w hw
  exact ZFSet.mem_insert_of_mem (ZFSet.pair (succ n) z) hw

/-- El nuevo par pertenece al grafo extendido. -/
theorem newPair_mem_extendGraphFoundational {h n z : ZFSet} :
    ZFSet.pair (succ n) z ∈ extendGraphFoundational h n z := by
  exact ZFSet.mem_insert (ZFSet.pair (succ n) z) h

/-- Caracterización de pertenencia al grafo extendido. -/
@[simp]
theorem mem_extendGraphFoundational {h n z w : ZFSet} :
    w ∈ extendGraphFoundational h n z ↔
      w = ZFSet.pair (succ n) z ∨ w ∈ h := by
  exact ZFSet.mem_insert_iff

/-- El nuevo índice `S(n)` no pertenecía al dominio anterior `S(n)`. -/
theorem succ_not_mem_own_segment {n : ZFSet} (hn : n ∈ omegaTA) :
    succ n ∉ succ n := by
  have hsn : succ n ∈ omegaTA := TA_PRO_00022_succ_closed hn
  exact (TA_PRO_00021_transitive_irreflexive hsn).2



/-! ### Etapa C2b2 — funcionalidad del grafo extendido -/

/-- Si el primer componente pertenece al dominio antiguo `S(n)`, pertenecer
al grafo extendido equivale a pertenecer al grafo original. El nuevo par no
puede interferir porque su primer componente es precisamente `S(n)`, que no
pertenece a `S(n)`. -/
theorem oldPair_mem_extendGraphFoundational_iff
    {h n z a b : ZFSet}
    (hn : n ∈ omegaTA)
    (ha : a ∈ succ n) :
    ZFSet.pair a b ∈ extendGraphFoundational h n z ↔
      ZFSet.pair a b ∈ h := by
  constructor
  · intro hp
    rcases mem_extendGraphFoundational.mp hp with hEq | hOld
    · have hCoord := ZFSet.pair_injective hEq
      have hBad : succ n ∈ succ n := by
        exact hCoord.1 ▸ ha
      exact (succ_not_mem_own_segment hn hBad).elim
    · exact hOld
  · intro hOld
    exact subset_extendGraphFoundational hOld

/-- Añadir un único valor nuevo en el índice `S(n)` preserva la funcionalidad
y amplía el dominio exactamente de `S(n)` a `S(S(n))`. -/
theorem extendGraphFoundational_isFunc
    {X h n z : ZFSet}
    (hn : n ∈ omegaTA)
    (hh : IsFuncFoundational (succ n) X h)
    (hz : z ∈ X) :
    IsFuncFoundational (succ (succ n)) X
      (extendGraphFoundational h n z) := by
  constructor
  · intro w hw
    rcases mem_extendGraphFoundational.mp hw with hEq | hOld
    · subst w
      refine ⟨succ n, ?_, z, hz, rfl⟩
      exact ZFSet.mem_insert (succ n) (succ n)
    · rcases hh.1 w hOld with ⟨a, ha, b, hb, hPair⟩
      refine ⟨a, ?_, b, hb, hPair⟩
      exact ZFSet.mem_insert_of_mem (succ n) ha
  · intro a ha
    rcases ZFSet.mem_insert_iff.mp ha with hNew | hOld
    · subst a
      refine ⟨z, ⟨hz, newPair_mem_extendGraphFoundational⟩, ?_⟩
      intro y hy
      rcases mem_extendGraphFoundational.mp hy.2 with hPair | hInOld
      · exact (ZFSet.pair_injective hPair).2
      · rcases hh.1 (ZFSet.pair (succ n) y) hInOld with ⟨a, haOld, b, _hb, hPairOld⟩
        have hCoord := ZFSet.pair_injective hPairOld
        have hBad : succ n ∈ succ n := by
          exact hCoord.1.symm ▸ haOld
        exact (succ_not_mem_own_segment hn hBad).elim
    · rcases hh.2 a hOld with ⟨b, hb, huniq⟩
      refine ⟨b, ⟨hb.1, subset_extendGraphFoundational hb.2⟩, ?_⟩
      intro y hy
      apply huniq y
      exact ⟨hy.1,
        (oldPair_mem_extendGraphFoundational_iff hn hOld).mp hy.2⟩


/-! ### Etapa C2b3 — preservación de la aproximación finita -/

/-- En una relación funcional fundacional, todo valor que aparece en un par
del grafo pertenece al codominio declarado. -/
theorem funcFoundational_value_mem
    {A B f a b : ZFSet}
    (hf : IsFuncFoundational A B f)
    (hab : ZFSet.pair a b ∈ f) :
    b ∈ B := by
  rcases hf.1 (ZFSet.pair a b) hab with
    ⟨a', _ha, b', hb', hEq⟩
  have hCoord := ZFSet.pair_injective hEq
  exact hCoord.2.symm ▸ hb'

/-- Si `h` es una `n`-aproximación, `h(n)=y` y `g(y)=z`, entonces añadir
exactamente el par `(S(n), z)` produce una `(S(n))`-aproximación.

Esta es la parte de existencia constructiva de TA-LEM-00004 una vez fijados
los dos valores determinados por la funcionalidad de `h` y `g`.
-/
theorem extendFiniteApproximation_given
    {X x0 g n h y z : ZFSet}
    (hn : n ∈ omegaTA)
    (ha : IsFiniteApproximation X x0 g n h)
    (hg : IsFuncFoundational X X g)
    (hny : ZFSet.pair n y ∈ h)
    (hyz : ZFSet.pair y z ∈ g) :
    IsFiniteApproximation X x0 g (succ n)
      (extendGraphFoundational h n z) := by
  have hyX : y ∈ X :=
    funcFoundational_value_mem ha.1 hny
  have hzX : z ∈ X :=
    funcFoundational_value_mem hg hyz

  constructor
  · exact extendGraphFoundational_isFunc hn ha.1 hzX
  constructor
  · exact subset_extendGraphFoundational ha.2.1
  · intro k hk hsk y' z' hky hyz'
    rcases ZFSet.mem_insert_iff.mp hsk with hEqSucc | hOldSucc
    · have hkn : k = n :=
        TA_THM_00009_succ_injective
          (m := k) (n := n) hk hn hEqSucc
      subst k

      have hnOld : n ∈ succ n :=
        ZFSet.mem_insert n n
      have hny' : ZFSet.pair n y' ∈ h :=
        (oldPair_mem_extendGraphFoundational_iff hn hnOld).mp hky
      have hy'X : y' ∈ X :=
        funcFoundational_value_mem ha.1 hny'

      rcases ha.1.2 n hnOld with ⟨u, _hu, huniqH⟩
      have hy_u : y = u := huniqH y ⟨hyX, hny⟩
      have hy'_u : y' = u := huniqH y' ⟨hy'X, hny'⟩
      have hyEq : y' = y := hy'_u.trans hy_u.symm
      rw [hyEq] at hyz'

      have hz'X : z' ∈ X :=
        funcFoundational_value_mem hg hyz'
      rcases hg.2 y hyX with ⟨v, _hv, huniqG⟩
      have hz_v : z = v := huniqG z ⟨hzX, hyz⟩
      have hz'_v : z' = v := huniqG z' ⟨hz'X, hyz'⟩
      have hzEq : z' = z := hz'_v.trans hz_v.symm
      rw [hzEq]
      exact newPair_mem_extendGraphFoundational

    · have hsn : succ n ∈ omegaTA :=
        TA_PRO_00022_succ_closed hn
      have hTrans : IsTransitive (succ n) :=
        (TA_PRO_00021_transitive_irreflexive hsn).1
      have hkInSuccK : k ∈ succ k :=
        ZFSet.mem_insert k k
      have hkOld : k ∈ succ n :=
        hTrans (succ k) hOldSucc hkInSuccK
      have hkyOld : ZFSet.pair k y' ∈ h :=
        (oldPair_mem_extendGraphFoundational_iff hn hkOld).mp hky
      have hstep : ZFSet.pair (succ k) z' ∈ h :=
        finiteApproximation_step ha hk hOldSucc hkyOld hyz'
      exact subset_extendGraphFoundational hstep


/-! ### Etapa C2b4 — existencia de la extensión -/

/-- TA-LEM-00004 (existencia) — toda `n`-aproximación admite una extensión
un paso. Los valores `y = h(n)` y `z = g(y)` se obtienen por eliminación de
existenciales a partir de la funcionalidad de `h` y `g`; no se realiza ninguna
elección global.
-/
theorem TA_LEM_00004_extension_exists
    {X x0 g n h : ZFSet}
    (hn : n ∈ omegaTA)
    (ha : IsFiniteApproximation X x0 g n h)
    (hg : IsFuncFoundational X X g) :
    ∃ hPlus : ZFSet,
      h ⊆ hPlus ∧
      IsFiniteApproximation X x0 g (succ n) hPlus := by
  have hnDom : n ∈ succ n :=
    ZFSet.mem_insert n n
  rcases ha.1.2 n hnDom with ⟨y, hy, _huniqH⟩
  rcases hg.2 y hy.1 with ⟨z, hz, _huniqG⟩
  refine ⟨extendGraphFoundational h n z, ?_, ?_⟩
  · exact subset_extendGraphFoundational
  · exact extendFiniteApproximation_given hn ha hg hy.2 hz.2


/-! ### Etapa C2b5 — unicidad de la extensión -/

/-- En cualquier extensión funcional del grafo `h`, los valores sobre el
subdominio antiguo `S(n)` coinciden exactamente con los de `h`. -/
theorem oldPair_mem_anyExtension_iff
    {X h n q a b : ZFSet}
    (hh : IsFuncFoundational (succ n) X h)
    (hq : IsFuncFoundational (succ (succ n)) X q)
    (hExt : h ⊆ q)
    (ha : a ∈ succ n) :
    ZFSet.pair a b ∈ q ↔ ZFSet.pair a b ∈ h := by
  constructor
  · intro habq
    have hbX : b ∈ X :=
      funcFoundational_value_mem hq habq
    rcases hh.2 a ha with ⟨c, hc, _huniqH⟩
    have hcq : ZFSet.pair a c ∈ q := hExt hc.2
    have haBig : a ∈ succ (succ n) :=
      ZFSet.mem_insert_of_mem (succ n) ha
    rcases hq.2 a haBig with ⟨u, _hu, huniqQ⟩
    have hb_u : b = u := huniqQ b ⟨hbX, habq⟩
    have hc_u : c = u := huniqQ c ⟨hc.1, hcq⟩
    have hbc : b = c := hb_u.trans hc_u.symm
    rw [hbc]
    exact hc.2
  · intro habh
    exact hExt habh

/-- En una extensión que sigue siendo aproximación, el valor del nuevo índice
`S(n)` queda forzado por la ecuación recursiva y por la funcionalidad de `g`. -/
theorem newPair_forced_by_recursion
    {X x0 g n h q b : ZFSet}
    (hn : n ∈ omegaTA)
    (ha : IsFiniteApproximation X x0 g n h)
    (hg : IsFuncFoundational X X g)
    (hExt : h ⊆ q)
    (hq : IsFiniteApproximation X x0 g (succ n) q)
    (hnew : ZFSet.pair (succ n) b ∈ q) :
    ∃ y : ZFSet,
      ZFSet.pair n y ∈ h ∧ ZFSet.pair y b ∈ g := by
  have hnDom : n ∈ succ n :=
    ZFSet.mem_insert n n
  rcases ha.1.2 n hnDom with ⟨y, hy, _huniqH⟩
  rcases hg.2 y hy.1 with ⟨z, hz, _huniqG⟩

  have hnyQ : ZFSet.pair n y ∈ q := hExt hy.2
  have hsnDom : succ n ∈ succ (succ n) :=
    ZFSet.mem_insert (succ n) (succ n)
  have hstep : ZFSet.pair (succ n) z ∈ q :=
    finiteApproximation_step hq hn hsnDom hnyQ hz.2

  have hbX : b ∈ X :=
    funcFoundational_value_mem hq.1 hnew
  rcases hq.1.2 (succ n) hsnDom with ⟨u, _hu, huniqQ⟩
  have hb_u : b = u := huniqQ b ⟨hbX, hnew⟩
  have hz_u : z = u := huniqQ z ⟨hz.1, hstep⟩
  have hbz : b = z := hb_u.trans hz_u.symm

  refine ⟨y, hy.2, ?_⟩
  rw [hbz]
  exact hz.2

/-- Dos extensiones de la misma `n`-aproximación que siguen siendo
`(S(n))`-aproximaciones coinciden como conjuntos-grafo. -/
theorem finiteApproximation_extensions_equal
    {X x0 g n h q r : ZFSet}
    (hn : n ∈ omegaTA)
    (ha : IsFiniteApproximation X x0 g n h)
    (hg : IsFuncFoundational X X g)
    (hqExt : h ⊆ q)
    (hq : IsFiniteApproximation X x0 g (succ n) q)
    (hrExt : h ⊆ r)
    (hr : IsFiniteApproximation X x0 g (succ n) r) :
    q = r := by
  apply subset_antisymm
  · intro w hw
    rcases hq.1.1 w hw with ⟨a, haDom, b, _hbX, hEq⟩
    rw [hEq] at hw ⊢
    rcases ZFSet.mem_insert_iff.mp haDom with hNew | hOld
    · subst a
      rcases newPair_forced_by_recursion hn ha hg hqExt hq hw with
        ⟨y, hny, hyb⟩
      have hnyR : ZFSet.pair n y ∈ r := hrExt hny
      have hsnDom : succ n ∈ succ (succ n) :=
        ZFSet.mem_insert (succ n) (succ n)
      exact finiteApproximation_step hr hn hsnDom hnyR hyb
    · have habH : ZFSet.pair a b ∈ h :=
        (oldPair_mem_anyExtension_iff ha.1 hq.1 hqExt hOld).mp hw
      exact hrExt habH

  · intro w hw
    rcases hr.1.1 w hw with ⟨a, haDom, b, _hbX, hEq⟩
    rw [hEq] at hw ⊢
    rcases ZFSet.mem_insert_iff.mp haDom with hNew | hOld
    · subst a
      rcases newPair_forced_by_recursion hn ha hg hrExt hr hw with
        ⟨y, hny, hyb⟩
      have hnyQ : ZFSet.pair n y ∈ q := hqExt hny
      have hsnDom : succ n ∈ succ (succ n) :=
        ZFSet.mem_insert (succ n) (succ n)
      exact finiteApproximation_step hq hn hsnDom hnyQ hyb
    · have habH : ZFSet.pair a b ∈ h :=
        (oldPair_mem_anyExtension_iff ha.1 hr.1 hrExt hOld).mp hw
      exact hqExt habH

/-- TA-LEM-00004 — extensión única de una aproximación finita. -/
theorem TA_LEM_00004_extension_unique
    {X x0 g n h : ZFSet}
    (hn : n ∈ omegaTA)
    (ha : IsFiniteApproximation X x0 g n h)
    (hg : IsFuncFoundational X X g) :
    ∃! hPlus : ZFSet,
      h ⊆ hPlus ∧
      IsFiniteApproximation X x0 g (succ n) hPlus := by
  rcases TA_LEM_00004_extension_exists hn ha hg with
    ⟨hPlus, hExt, hApprox⟩
  refine ⟨hPlus, ⟨hExt, hApprox⟩, ?_⟩
  intro q hq
  exact finiteApproximation_extensions_equal
    hn ha hg hq.1 hq.2 hExt hApprox

/-! ### Etapa C3a1 — caso base de TA-THM-00012 -/

/-- Grafo de la única `0`-aproximación: sólo contiene el valor inicial. -/
def zeroApproximationGraph (x0 : ZFSet) : ZFSet :=
  insert (ZFSet.pair (∅ : ZFSet) x0) (∅ : ZFSet)

/-- Caracterización exacta del grafo base. -/
theorem mem_zeroApproximationGraph {x0 w : ZFSet} :
    w ∈ zeroApproximationGraph x0 ↔
      w = ZFSet.pair (∅ : ZFSet) x0 := by
  constructor
  · intro hw
    rcases ZFSet.mem_insert_iff.mp hw with hEq | hEmpty
    · exact hEq
    · exact (ZFSet.notMem_empty w hEmpty).elim
  · intro hEq
    rw [hEq]
    exact ZFSet.mem_insert
      (ZFSet.pair (∅ : ZFSet) x0) (∅ : ZFSet)

/-- El grafo base es funcional de `S(0)` en `X`. -/
theorem zeroApproximationGraph_isFunc
    {X x0 : ZFSet}
    (hx0 : x0 ∈ X) :
    IsFuncFoundational (succ (∅ : ZFSet)) X
      (zeroApproximationGraph x0) := by
  constructor
  · intro w hw
    have hEq := mem_zeroApproximationGraph.mp hw
    subst w
    refine ⟨(∅ : ZFSet), ?_, x0, hx0, rfl⟩
    exact ZFSet.mem_insert (∅ : ZFSet) (∅ : ZFSet)

  · intro a ha
    rcases ZFSet.mem_insert_iff.mp ha with ha0 | haEmpty
    · subst a
      refine ⟨x0, ?_, ?_⟩
      · exact ⟨hx0,
          mem_zeroApproximationGraph.mpr rfl⟩
      · intro y hy
        have hPair :
            ZFSet.pair (∅ : ZFSet) y =
              ZFSet.pair (∅ : ZFSet) x0 :=
          mem_zeroApproximationGraph.mp hy.2
        exact (ZFSet.pair_injective hPair).2

    · exact (ZFSet.notMem_empty a haEmpty).elim

/-- El grafo base satisface la definición completa de `0`-aproximación. -/
theorem zeroApproximationGraph_isApproximation
    {X x0 g : ZFSet}
    (hx0 : x0 ∈ X) :
    IsFiniteApproximation X x0 g (∅ : ZFSet)
      (zeroApproximationGraph x0) := by
  constructor
  · exact zeroApproximationGraph_isFunc hx0
  constructor
  · exact mem_zeroApproximationGraph.mpr rfl
  · intro k hk hsk y z hky hyz
    rcases ZFSet.mem_insert_iff.mp hsk with hEq | hEmpty
    · exact (TA_PRO_00023_succ_ne_zero k hEq).elim
    · exact (ZFSet.notMem_empty (succ k) hEmpty).elim

/-- Toda `0`-aproximación coincide con el grafo base. -/
theorem zeroApproximationGraph_unique
    {X x0 g q : ZFSet}
    (hq : IsFiniteApproximation X x0 g (∅ : ZFSet) q) :
    q = zeroApproximationGraph x0 := by
  apply ZFSet.ext
  intro w
  constructor
  · intro hw
    rcases hq.1.1 w hw with
      ⟨a, ha, b, hbX, hEq⟩

    rcases ZFSet.mem_insert_iff.mp ha with ha0 | haEmpty
    · subst a

      have hwb : ZFSet.pair (∅ : ZFSet) b ∈ q := by
        rw [← hEq]
        exact hw

      have hx0X : x0 ∈ X :=
        funcFoundational_value_mem hq.1 hq.2.1

      have hzeroDom : (∅ : ZFSet) ∈ succ (∅ : ZFSet) :=
        ZFSet.mem_insert (∅ : ZFSet) (∅ : ZFSet)

      rcases hq.1.2 (∅ : ZFSet) hzeroDom with
        ⟨u, _hu, huniq⟩

      have hb_u : b = u :=
        huniq b ⟨hbX, hwb⟩

      have hx0_u : x0 = u :=
        huniq x0 ⟨hx0X, hq.2.1⟩

      have hb0 : b = x0 :=
        hb_u.trans hx0_u.symm

      apply mem_zeroApproximationGraph.mpr
      rw [hEq, hb0]

    · exact (ZFSet.notMem_empty a haEmpty).elim

  · intro hw
    have hEq := mem_zeroApproximationGraph.mp hw
    rw [hEq]
    exact hq.2.1

/-- TA-THM-00012 — caso base: existe una única `0`-aproximación. -/
theorem TA_THM_00012_zero
    {X x0 g : ZFSet}
    (hx0 : x0 ∈ X) :
    ∃! h : ZFSet,
      IsFiniteApproximation X x0 g (∅ : ZFSet) h := by
  refine ⟨zeroApproximationGraph x0, ?_, ?_⟩
  · exact zeroApproximationGraph_isApproximation hx0
  · intro q hq
    exact zeroApproximationGraph_unique hq

/-! ### Etapa C3a2 — restricción de una aproximación sucesora -/

/-- Para todo natural `n`, cero pertenece al segmento inicial `S(n)`. -/
theorem zero_mem_succ_of_nat
    {n : ZFSet}
    (hn : n ∈ omegaTA) :
    (∅ : ZFSet) ∈ succ n := by
  let P : ZFSet → Prop :=
    fun k => (∅ : ZFSet) ∈ succ k

  have h0 : P (∅ : ZFSet) := by
    exact ZFSet.mem_insert (∅ : ZFSet) (∅ : ZFSet)

  have hs :
      ∀ k : ZFSet,
        k ∈ omegaTA →
        P k →
        P (succ k) := by
    intro k _hk ih
    exact ZFSet.mem_insert_of_mem (succ k) ih

  exact TA_THM_00008_induction P h0 hs n hn

/-- La restricción fundacional de un grafo está contenida en el grafo original. -/
theorem restrictGraphFoundational_subset
    {f C B : ZFSet} :
    restrictGraphFoundational f C B ⊆ f := by
  intro w hw
  exact (ZFSet.mem_sep.mp hw).1

/-- Restringir una `(S(n))`-aproximación al dominio antiguo `S(n)`
produce una `n`-aproximación. -/
theorem finiteApproximation_restrict_succ
    {X x0 g n q : ZFSet}
    (hn : n ∈ omegaTA)
    (hq : IsFiniteApproximation X x0 g (succ n) q) :
    IsFiniteApproximation X x0 g n
      (restrictGraphFoundational q (succ n) X) := by
  constructor
  · exact TA_PRO_00024_restriction_foundational
      (subset_succ (succ n))
      hq.1

  constructor
  · have hx0X : x0 ∈ X :=
      funcFoundational_value_mem hq.1 hq.2.1

    apply ZFSet.mem_sep.mpr
    refine ⟨hq.2.1, ?_⟩
    exact ⟨
      (∅ : ZFSet),
      zero_mem_succ_of_nat hn,
      x0,
      hx0X,
      rfl
    ⟩

  · intro k hk hsk y z hky hyz

    have hkyQ : ZFSet.pair k y ∈ q :=
      (ZFSet.mem_sep.mp hky).1

    have hskBig : succ k ∈ succ (succ n) :=
      ZFSet.mem_insert_of_mem (succ n) hsk

    have hstepQ : ZFSet.pair (succ k) z ∈ q :=
      finiteApproximation_step
        hq hk hskBig hkyQ hyz

    have hzX : z ∈ X :=
      funcFoundational_value_mem hq.1 hstepQ

    apply ZFSet.mem_sep.mpr
    refine ⟨hstepQ, ?_⟩
    exact ⟨succ k, hsk, z, hzX, rfl⟩

/-! ### Etapa C3a3 — paso inductivo y cierre de TA-THM-00012 -/

/-- Paso inductivo de TA-THM-00012.

Si existe una única `n`-aproximación, entonces existe una única
`S(n)`-aproximación. La existencia procede de TA-LEM-00004.
Para la unicidad, cualquier otra aproximación sucesora se restringe al
dominio anterior; la hipótesis inductiva identifica esa restricción con la
única `n`-aproximación y TA-LEM-00004 identifica entonces las extensiones.
-/
theorem TA_THM_00012_succ
    {X x0 g n : ZFSet}
    (hn : n ∈ omegaTA)
    (hg : IsFuncFoundational X X g)
    (ih :
      ∃! h : ZFSet,
        IsFiniteApproximation X x0 g n h) :
    ∃! q : ZFSet,
      IsFiniteApproximation X x0 g (succ n) q := by

  rcases ih with ⟨h, hh, huniqH⟩

  rcases TA_LEM_00004_extension_unique hn hh hg with
    ⟨hPlus, hPlusData, huniqPlus⟩

  refine ⟨hPlus, hPlusData.2, ?_⟩

  intro q hq

  have hqRestr :
      IsFiniteApproximation X x0 g n
        (restrictGraphFoundational q (succ n) X) :=
    finiteApproximation_restrict_succ hn hq

  have hRestrEq :
      restrictGraphFoundational q (succ n) X = h :=
    huniqH _ hqRestr

  have hExtQ : h ⊆ q := by
    intro w hw

    have hwRestr :
        w ∈ restrictGraphFoundational q (succ n) X := by
      rw [hRestrEq]
      exact hw

    exact restrictGraphFoundational_subset hwRestr

  exact huniqPlus q ⟨hExtQ, hq⟩

/-- TA-THM-00012 — para todo natural `n` existe una única `n`-aproximación. -/
theorem TA_THM_00012_finite_approximations
    {X x0 g : ZFSet}
    (hx0 : x0 ∈ X)
    (hg : IsFuncFoundational X X g) :
    ∀ n : ZFSet,
      n ∈ omegaTA →
      ∃! h : ZFSet,
        IsFiniteApproximation X x0 g n h := by

  let P : ZFSet → Prop :=
    fun n =>
      ∃! h : ZFSet,
        IsFiniteApproximation X x0 g n h

  have h0 : P (∅ : ZFSet) := by
    exact TA_THM_00012_zero
      (X := X) (x0 := x0) (g := g) hx0

  have hs :
      ∀ n : ZFSet,
        n ∈ omegaTA →
        P n →
        P (succ n) := by
    intro n hn ih
    exact TA_THM_00012_succ
      (X := X) (x0 := x0) (g := g)
      hn hg ih

  exact TA_THM_00008_induction P h0 hs

/-! ### Etapa C3b — TA-LEM-00005: coherencia de aproximaciones -/

/-- En un grafo funcional, dos pares con el mismo primer componente tienen
necesariamente el mismo segundo componente. -/
theorem funcFoundational_pair_value_unique
    {A B f a b c : ZFSet}
    (hf : IsFuncFoundational A B f)
    (ha : a ∈ A)
    (hab : ZFSet.pair a b ∈ f)
    (hac : ZFSet.pair a c ∈ f) :
    b = c := by
  have hbB : b ∈ B :=
    funcFoundational_value_mem hf hab
  have hcB : c ∈ B :=
    funcFoundational_value_mem hf hac

  rcases hf.2 a ha with ⟨u, _hu, huniq⟩

  have hbu : b = u :=
    huniq b ⟨hbB, hab⟩
  have hcu : c = u :=
    huniq c ⟨hcB, hac⟩

  exact hbu.trans hcu.symm

/-- TA-LEM-00005 — coherencia de aproximaciones.

Si `h` es una `n`-aproximación y `q` una `m`-aproximación, ambas coinciden
en todo índice `k` perteneciente simultáneamente a `S(n)` y `S(m)`.

La demostración se realiza por inducción sobre `k`. -/
theorem TA_LEM_00005_coherence
    {X x0 g : ZFSet}
    (hg : IsFuncFoundational X X g) :
    ∀ k : ZFSet,
      k ∈ omegaTA →
      ∀ n m h q y z : ZFSet,
        n ∈ omegaTA →
        m ∈ omegaTA →
        IsFiniteApproximation X x0 g n h →
        IsFiniteApproximation X x0 g m q →
        k ∈ succ n →
        k ∈ succ m →
        ZFSet.pair k y ∈ h →
        ZFSet.pair k z ∈ q →
        y = z := by

  let P : ZFSet → Prop :=
    fun k =>
      ∀ n m h q y z : ZFSet,
        n ∈ omegaTA →
        m ∈ omegaTA →
        IsFiniteApproximation X x0 g n h →
        IsFiniteApproximation X x0 g m q →
        k ∈ succ n →
        k ∈ succ m →
        ZFSet.pair k y ∈ h →
        ZFSet.pair k z ∈ q →
        y = z

  have h0 : P (∅ : ZFSet) := by
    intro n m h q y z hn hm hh hq hkN hkM hhy hqz

    have hy0 : y = x0 :=
      funcFoundational_pair_value_unique
        hh.1 hkN hhy hh.2.1

    have hz0 : z = x0 :=
      funcFoundational_pair_value_unique
        hq.1 hkM hqz hq.2.1

    exact hy0.trans hz0.symm

  have hs :
      ∀ k : ZFSet,
        k ∈ omegaTA →
        P k →
        P (succ k) := by
    intro k hk ih n m h q y z hn hm hh hq hskN hskM hhy hqz

    have hsnNat : succ n ∈ omegaTA :=
      TA_PRO_00022_succ_closed hn
    have hsmNat : succ m ∈ omegaTA :=
      TA_PRO_00022_succ_closed hm

    have hTransN : IsTransitive (succ n) :=
      (TA_PRO_00021_transitive_irreflexive hsnNat).1
    have hTransM : IsTransitive (succ m) :=
      (TA_PRO_00021_transitive_irreflexive hsmNat).1

    have hkInSuccK : k ∈ succ k :=
      ZFSet.mem_insert k k

    have hkN : k ∈ succ n :=
      hTransN (succ k) hskN hkInSuccK
    have hkM : k ∈ succ m :=
      hTransM (succ k) hskM hkInSuccK

    rcases hh.1.2 k hkN with
      ⟨a, ha, _huniqA⟩

    rcases hq.1.2 k hkM with
      ⟨b, hb, _huniqB⟩

    have hab : a = b :=
      ih n m h q a b
        hn hm hh hq
        hkN hkM
        ha.2 hb.2

    have hkaQ : ZFSet.pair k a ∈ q := by
      rw [hab]
      exact hb.2

    rcases hg.2 a ha.1 with
      ⟨u, hu, _huniqG⟩

    have hstepH :
        ZFSet.pair (succ k) u ∈ h :=
      finiteApproximation_step
        hh hk hskN ha.2 hu.2

    have hstepQ :
        ZFSet.pair (succ k) u ∈ q :=
      finiteApproximation_step
        hq hk hskM hkaQ hu.2

    have hyu : y = u :=
      funcFoundational_pair_value_unique
        hh.1 hskN hhy hstepH

    have hzu : z = u :=
      funcFoundational_pair_value_unique
        hq.1 hskM hqz hstepQ

    exact hyu.trans hzu.symm

  exact TA_THM_00008_induction P h0 hs

/-! ### Etapa C4a — grafo recursivo global -/

/-- Ambiente fundacional que contiene todos los pares de Kuratowski con
primera componente en `A` y segunda componente en `B`. -/
def pairAmbient (A B : ZFSet) : ZFSet :=
  ZFSet.powerset (ZFSet.powerset (A ∪ B))

/-- Todo par de Kuratowski formado con elementos de `A` y `B` pertenece al
ambiente fundacional de pares. -/
theorem pair_mem_pairAmbient {A B a b : ZFSet}
    (ha : a ∈ A)
    (hb : b ∈ B) :
    ZFSet.pair a b ∈ pairAmbient A B := by
  apply ZFSet.mem_powerset.mpr
  intro u hu
  rw [ZFSet.pair] at hu
  rcases ZFSet.mem_pair.mp hu with rfl | rfl
  · apply ZFSet.mem_powerset.mpr
    intro v hv
    have hvEq : v = a := ZFSet.mem_singleton.mp hv
    subst v
    exact ZFSet.mem_union.mpr (Or.inl ha)
  · apply ZFSet.mem_powerset.mpr
    intro v hv
    rcases ZFSet.mem_pair.mp hv with rfl | rfl
    · exact ZFSet.mem_union.mpr (Or.inl ha)
    · exact ZFSet.mem_union.mpr (Or.inr hb)

/-- Grafo recursivo global obtenido por separación dentro del ambiente de
pares. Un par pertenece cuando aparece en alguna aproximación finita cuyo
dominio contiene su índice. -/
def globalRecursionGraph (X x0 g : ZFSet) : ZFSet :=
  ZFSet.sep
    (fun z =>
      ∃ k : ZFSet, k ∈ omegaTA ∧
        ∃ x : ZFSet, x ∈ X ∧ z = ZFSet.pair k x ∧
          ∃ n : ZFSet, n ∈ omegaTA ∧
            ∃ h : ZFSet,
              IsFiniteApproximation X x0 g n h ∧
              k ∈ succ n ∧
              ZFSet.pair k x ∈ h)
    (pairAmbient omegaTA X)

/-- Caracterización de pertenencia de un par al grafo recursivo global. -/
theorem mem_globalRecursionGraph {X x0 g k x : ZFSet} :
    ZFSet.pair k x ∈ globalRecursionGraph X x0 g ↔
      k ∈ omegaTA ∧
      x ∈ X ∧
      ∃ n : ZFSet, n ∈ omegaTA ∧
        ∃ h : ZFSet,
          IsFiniteApproximation X x0 g n h ∧
          k ∈ succ n ∧
          ZFSet.pair k x ∈ h := by
  constructor
  · intro hkx
    rcases (ZFSet.mem_sep.mp hkx).2 with
      ⟨k', hk', x', hx', hPair, n, hn, h, hh, hk'n, hk'x'⟩
    have hCoord : k = k' ∧ x = x' :=
      ZFSet.pair_injective hPair
    rcases hCoord with ⟨rfl, rfl⟩
    exact ⟨hk', hx', n, hn, h, hh, hk'n, hk'x'⟩
  · rintro ⟨hk, hx, n, hn, h, hh, hkn, hkxh⟩
    apply ZFSet.mem_sep.mpr
    refine ⟨pair_mem_pairAmbient hk hx, ?_⟩
    exact ⟨k, hk, x, hx, rfl, n, hn, h, hh, hkn, hkxh⟩

/-- C4a — el grafo recursivo global es una función fundacional de `omegaTA`
en `X`. La existencia usa una aproximación finita en el índice dado y la
unicidad se deduce de la coherencia entre aproximaciones. -/
theorem globalRecursionGraph_isFunc
    {X x0 g : ZFSet}
    (hx0 : x0 ∈ X)
    (hg : IsFuncFoundational X X g) :
    IsFuncFoundational omegaTA X
      (globalRecursionGraph X x0 g) := by
  constructor
  · intro z hz
    rcases (ZFSet.mem_sep.mp hz).2 with
      ⟨k, hk, x, hx, hPair, _n, _hn, _h, _hh, _hkn, _hkxh⟩
    exact ⟨k, hk, x, hx, hPair⟩
  · intro k hk
    rcases TA_THM_00012_finite_approximations hx0 hg k hk with
      ⟨h, hh, _huniqH⟩
    have hkk : k ∈ succ k :=
      ZFSet.mem_insert k k
    rcases hh.1.2 k hkk with ⟨x, hx, _huniqX⟩
    refine ⟨x, ?_, ?_⟩
    · refine ⟨hx.1, ?_⟩
      exact mem_globalRecursionGraph.mpr
        ⟨hk, hx.1, k, hk, h, hh, hkk, hx.2⟩
    · intro y hy
      rcases mem_globalRecursionGraph.mp hy.2 with
        ⟨_yNat, _hyX, n, hn, q, hq, hkn, hky⟩
      exact (TA_LEM_00005_coherence hg k hk
        k n h q x y hk hn hh hq hkk hkn hx.2 hky).symm

/-! ### Etapa C4b — ecuaciones recursivas del grafo global -/

/-- El grafo recursivo global toma el valor inicial `x0` en cero. -/
theorem globalRecursionGraph_zero
    {X x0 g : ZFSet}
    (hx0 : x0 ∈ X) :
    ZFSet.pair (∅ : ZFSet) x0 ∈
      globalRecursionGraph X x0 g := by
  exact mem_globalRecursionGraph.mpr
    ⟨omegaTA_isInductive.1,
      hx0,
      (∅ : ZFSet),
      omegaTA_isInductive.1,
      zeroApproximationGraph x0,
      zeroApproximationGraph_isApproximation hx0,
      ZFSet.mem_insert (∅ : ZFSet) (∅ : ZFSet),
      mem_zeroApproximationGraph.mpr rfl⟩

/-- La ecuación sucesora del grafo recursivo global. -/
theorem globalRecursionGraph_succ
    {X x0 g n x y : ZFSet}
    (hx0 : x0 ∈ X)
    (hg : IsFuncFoundational X X g)
    (hn : n ∈ omegaTA)
    (hnx :
      ZFSet.pair n x ∈ globalRecursionGraph X x0 g)
    (hxy : ZFSet.pair x y ∈ g) :
    ZFSet.pair (succ n) y ∈
      globalRecursionGraph X x0 g := by
  rcases mem_globalRecursionGraph.mp hnx with
    ⟨_hnNat, _hxX, m, hm, h, hh, hnm, hnxh⟩

  have hsn : succ n ∈ omegaTA :=
    TA_PRO_00022_succ_closed hn

  rcases TA_THM_00012_finite_approximations hx0 hg (succ n) hsn with
    ⟨q, hq, _huniqQ⟩

  have hnn : n ∈ succ n :=
    ZFSet.mem_insert n n
  have hnBig : n ∈ succ (succ n) :=
    ZFSet.mem_insert_of_mem (succ n) hnn

  rcases hq.1.2 n hnBig with ⟨xq, hxq, _huniqXq⟩

  have hxxq : x = xq :=
    TA_LEM_00005_coherence hg n hn
      m (succ n) h q x xq hm hsn hh hq hnm hnBig hnxh hxq.2

  have hnxq : ZFSet.pair n x ∈ q := by
    rw [hxxq]
    exact hxq.2

  have hsnDom : succ n ∈ succ (succ n) :=
    ZFSet.mem_insert (succ n) (succ n)

  have hsnyq : ZFSet.pair (succ n) y ∈ q :=
    finiteApproximation_step hq hn hsnDom hnxq hxy

  have hyX : y ∈ X :=
    funcFoundational_value_mem hg hxy

  exact mem_globalRecursionGraph.mpr
    ⟨hsn, hyX, succ n, hsn, q, hq, hsnDom, hsnyq⟩

/-- Las ecuaciones inicial y sucesora del grafo recursivo global. -/
theorem globalRecursionGraph_equations
    {X x0 g : ZFSet}
    (hx0 : x0 ∈ X)
    (hg : IsFuncFoundational X X g) :
    ZFSet.pair (∅ : ZFSet) x0 ∈
        globalRecursionGraph X x0 g ∧
    ∀ n x y : ZFSet,
      n ∈ omegaTA →
      ZFSet.pair n x ∈ globalRecursionGraph X x0 g →
      ZFSet.pair x y ∈ g →
      ZFSet.pair (succ n) y ∈
        globalRecursionGraph X x0 g := by
  refine ⟨globalRecursionGraph_zero hx0, ?_⟩
  intro n x y hn hnx hxy
  exact globalRecursionGraph_succ hx0 hg hn hnx hxy

/-! ### Etapa C4c — unicidad y cierre de la recursión global -/

/-- Todo grafo funcional sobre `omegaTA` que satisface las ecuaciones
recursivas coincide con el grafo recursivo global. -/
theorem globalRecursionGraph_unique
    {X x0 g f : ZFSet}
    (hx0 : x0 ∈ X)
    (hg : IsFuncFoundational X X g)
    (hf : IsFuncFoundational omegaTA X f)
    (hf0 : ZFSet.pair (∅ : ZFSet) x0 ∈ f)
    (hfSucc :
      ∀ n x y : ZFSet,
        n ∈ omegaTA →
        ZFSet.pair n x ∈ f →
        ZFSet.pair x y ∈ g →
        ZFSet.pair (succ n) y ∈ f) :
    f = globalRecursionGraph X x0 g := by
  let G : ZFSet := globalRecursionGraph X x0 g

  have hG : IsFuncFoundational omegaTA X G := by
    exact globalRecursionGraph_isFunc hx0 hg

  let P : ZFSet → Prop := fun n =>
    ∀ x y : ZFSet,
      ZFSet.pair n x ∈ f →
      ZFSet.pair n y ∈ G →
      x = y

  have h0 : P (∅ : ZFSet) := by
    intro x y hfx hGy
    have hZeroNat : (∅ : ZFSet) ∈ omegaTA :=
      omegaTA_isInductive.1
    have hxx0 : x = x0 :=
      funcFoundational_pair_value_unique hf hZeroNat hfx hf0
    have hG0 : ZFSet.pair (∅ : ZFSet) x0 ∈ G := by
      exact globalRecursionGraph_zero hx0
    have hyx0 : y = x0 :=
      funcFoundational_pair_value_unique hG hZeroNat hGy hG0
    exact hxx0.trans hyx0.symm

  have hs :
      ∀ n : ZFSet,
        n ∈ omegaTA →
        P n →
        P (succ n) := by
    intro n hn ih x y hfx hGy

    have hsn : succ n ∈ omegaTA :=
      TA_PRO_00022_succ_closed hn

    rcases hf.2 n hn with ⟨a, ha, _huniqA⟩
    rcases hG.2 n hn with ⟨b, hb, _huniqB⟩

    have hab : a = b :=
      ih a b ha.2 hb.2

    rcases hg.2 a ha.1 with ⟨c, hc, _huniqC⟩

    have hSuccF : ZFSet.pair (succ n) c ∈ f :=
      hfSucc n a c hn ha.2 hc.2

    have hnaG : ZFSet.pair n a ∈ G := by
      rw [hab]
      exact hb.2

    have hSuccG : ZFSet.pair (succ n) c ∈ G := by
      exact globalRecursionGraph_succ hx0 hg hn hnaG hc.2

    have hxc : x = c :=
      funcFoundational_pair_value_unique hf hsn hfx hSuccF
    have hyc : y = c :=
      funcFoundational_pair_value_unique hG hsn hGy hSuccG

    exact hxc.trans hyc.symm

  have hAgreement :
      ∀ n : ZFSet,
        n ∈ omegaTA →
        P n :=
    TA_THM_00008_induction P h0 hs

  apply ZFSet.ext
  intro z
  constructor
  · intro hzf
    rcases hf.1 z hzf with ⟨n, hn, x, _hxX, hzPair⟩
    rcases hG.2 n hn with ⟨y, hy, _huniqY⟩
    have hnxF : ZFSet.pair n x ∈ f := by
      rw [← hzPair]
      exact hzf
    have hxy : x = y :=
      hAgreement n hn x y hnxF hy.2
    rw [hzPair, hxy]
    exact hy.2
  · intro hzG
    rcases hG.1 z hzG with ⟨n, hn, y, _hyX, hzPair⟩
    rcases hf.2 n hn with ⟨x, hx, _huniqX⟩
    have hnyG : ZFSet.pair n y ∈ G := by
      rw [← hzPair]
      exact hzG
    have hxy : x = y :=
      hAgreement n hn x y hx.2 hnyG
    rw [hzPair, ← hxy]
    exact hx.2

/-- TA-THM-00013 — existencia y unicidad de la función recursiva global. -/
theorem TA_THM_00013_global_recursion
    {X x0 g : ZFSet}
    (hx0 : x0 ∈ X)
    (hg : IsFuncFoundational X X g) :
    ∃! f : ZFSet,
      IsFuncFoundational omegaTA X f ∧
      ZFSet.pair (∅ : ZFSet) x0 ∈ f ∧
      ∀ n x y : ZFSet,
        n ∈ omegaTA →
        ZFSet.pair n x ∈ f →
        ZFSet.pair x y ∈ g →
        ZFSet.pair (succ n) y ∈ f := by
  refine ⟨globalRecursionGraph X x0 g, ?_, ?_⟩
  · have hEq := globalRecursionGraph_equations hx0 hg
    exact ⟨globalRecursionGraph_isFunc hx0 hg, hEq.1, hEq.2⟩
  · intro f hfData
    exact globalRecursionGraph_unique
      hx0 hg hfData.1 hfData.2.1 hfData.2.2

/-! ### Etapa C5a1 — infraestructura fundacional para parámetros -/

/-- Producto cartesiano fundacional construido por separación dentro del
ambiente de pares de Kuratowski. -/
def cartesianProductFoundational (A B : ZFSet) : ZFSet :=
  ZFSet.sep
    (fun z =>
      ∃ a : ZFSet, a ∈ A ∧
        ∃ b : ZFSet, b ∈ B ∧
          z = ZFSet.pair a b)
    (pairAmbient A B)

/-- Caracterización de los pares del producto cartesiano fundacional. -/
theorem mem_cartesianProductFoundational
    {A B a b : ZFSet} :
    ZFSet.pair a b ∈ cartesianProductFoundational A B ↔
      a ∈ A ∧ b ∈ B := by
  constructor
  · intro hab
    rcases (ZFSet.mem_sep.mp hab).2 with
      ⟨a', ha', b', hb', hPair⟩
    have hCoord : a = a' ∧ b = b' :=
      ZFSet.pair_injective hPair
    rcases hCoord with ⟨rfl, rfl⟩
    exact ⟨ha', hb'⟩
  · rintro ⟨ha, hb⟩
    apply ZFSet.mem_sep.mpr
    exact ⟨pair_mem_pairAmbient ha hb, a, ha, b, hb, rfl⟩

/-- Especialización al parámetro `p` de un grafo de pasos sobre pares
parametrizados. -/
def parameterStepGraph (_P X r p : ZFSet) : ZFSet :=
  ZFSet.sep
    (fun z =>
      ∃ x : ZFSet, x ∈ X ∧
        ∃ y : ZFSet, y ∈ X ∧
          z = ZFSet.pair x y ∧
          ZFSet.pair (ZFSet.pair p x) y ∈ r)
    (pairAmbient X X)

/-- Caracterización de pertenencia al grafo de pasos especializado. -/
theorem parameterStepGraph_mem
    {P X r p x y : ZFSet} :
    ZFSet.pair x y ∈ parameterStepGraph P X r p ↔
      x ∈ X ∧
      y ∈ X ∧
      ZFSet.pair (ZFSet.pair p x) y ∈ r := by
  constructor
  · intro hxy
    rcases (ZFSet.mem_sep.mp hxy).2 with
      ⟨x', hx', y', hy', hPair, hStep⟩
    have hCoord : x = x' ∧ y = y' :=
      ZFSet.pair_injective hPair
    rcases hCoord with ⟨rfl, rfl⟩
    exact ⟨hx', hy', hStep⟩
  · rintro ⟨hx, hy, hStep⟩
    apply ZFSet.mem_sep.mpr
    exact ⟨pair_mem_pairAmbient hx hy,
      x, hx, y, hy, rfl, hStep⟩

/-- Para `p ∈ P`, especializar un paso funcional `P ×₀ X → X` produce
un paso funcional `X → X`. -/
theorem parameterStepGraph_isFunc
    {P X r p : ZFSet}
    (hp : p ∈ P)
    (hr :
      IsFuncFoundational
        (cartesianProductFoundational P X)
        X
        r) :
    IsFuncFoundational X X
      (parameterStepGraph P X r p) := by
  constructor
  · intro z hz
    rcases (ZFSet.mem_sep.mp hz).2 with
      ⟨x, hx, y, hy, hPair, _hStep⟩
    exact ⟨x, hx, y, hy, hPair⟩
  · intro x hx
    have hpxDom :
        ZFSet.pair p x ∈ cartesianProductFoundational P X :=
      mem_cartesianProductFoundational.mpr ⟨hp, hx⟩

    rcases hr.2 (ZFSet.pair p x) hpxDom with
      ⟨y, hy, _huniqY⟩

    refine ⟨y, ?_, ?_⟩
    · exact ⟨hy.1,
        parameterStepGraph_mem.mpr ⟨hx, hy.1, hy.2⟩⟩
    · intro z hz
      have hzStep : ZFSet.pair (ZFSet.pair p x) z ∈ r :=
        (parameterStepGraph_mem.mp hz.2).2.2
      exact funcFoundational_pair_value_unique
        hr hpxDom hzStep hy.2

/-! ### Etapa C5a2a — grafo recursivo parametrizado -/

/-- Grafo parametrizado construido directamente por separación. El valor en
`(p,n)` pertenece al grafo recursivo asociado al valor inicial de `p` y al
paso especializado en `p`. -/
def parameterizedRecursionGraph
    (P X b r : ZFSet) : ZFSet :=
  ZFSet.sep
    (fun z =>
      ∃ p : ZFSet, p ∈ P ∧
        ∃ n : ZFSet, n ∈ omegaTA ∧
          ∃ x0 : ZFSet, x0 ∈ X ∧
            ZFSet.pair p x0 ∈ b ∧
            ∃ x : ZFSet, x ∈ X ∧
              z = ZFSet.pair (ZFSet.pair p n) x ∧
              ZFSet.pair n x ∈
                globalRecursionGraph
                  X x0
                  (parameterStepGraph P X r p))
    (pairAmbient
      (cartesianProductFoundational P omegaTA)
      X)

/-- Caracterización de pertenencia al grafo recursivo parametrizado. -/
theorem parameterizedRecursionGraph_mem
    {P X b r p n x : ZFSet} :
    ZFSet.pair (ZFSet.pair p n) x ∈
      parameterizedRecursionGraph P X b r ↔
      p ∈ P ∧
      n ∈ omegaTA ∧
      x ∈ X ∧
      ∃ x0 : ZFSet,
        x0 ∈ X ∧
        ZFSet.pair p x0 ∈ b ∧
        ZFSet.pair n x ∈
          globalRecursionGraph
            X x0
            (parameterStepGraph P X r p) := by
  constructor
  · intro hpnx
    rcases (ZFSet.mem_sep.mp hpnx).2 with
      ⟨p', hp', n', hn', x0, hx0, hp'x0,
        x', hx', hOuter, hRec⟩
    rcases ZFSet.pair_injective hOuter with ⟨hInner, hX⟩
    rcases ZFSet.pair_injective hInner with ⟨rfl, rfl⟩
    rcases hX with rfl
    exact ⟨hp', hn', hx', x0, hx0, hp'x0, hRec⟩
  · rintro ⟨hp, hn, hx, x0, hx0, hpx0, hRec⟩
    have hpnDom :
        ZFSet.pair p n ∈ cartesianProductFoundational P omegaTA :=
      mem_cartesianProductFoundational.mpr ⟨hp, hn⟩
    apply ZFSet.mem_sep.mpr
    refine ⟨pair_mem_pairAmbient hpnDom hx, ?_⟩
    exact ⟨p, hp, n, hn, x0, hx0, hpx0,
      x, hx, rfl, hRec⟩

/-- El grafo recursivo parametrizado es una función total
`P ×₀ omegaTA → X`. -/
theorem parameterizedRecursionGraph_isFunc
    {P X b r : ZFSet}
    (hb : IsFuncFoundational P X b)
    (hr :
      IsFuncFoundational
        (cartesianProductFoundational P X)
        X
        r) :
    IsFuncFoundational
      (cartesianProductFoundational P omegaTA)
      X
      (parameterizedRecursionGraph P X b r) := by
  constructor
  · intro z hz
    rcases (ZFSet.mem_sep.mp hz).2 with
      ⟨p, hp, n, hn, _x0, _hx0, _hpx0,
        x, hx, hPair, _hRec⟩
    have hpnDom :
        ZFSet.pair p n ∈ cartesianProductFoundational P omegaTA :=
      mem_cartesianProductFoundational.mpr ⟨hp, hn⟩
    exact ⟨ZFSet.pair p n, hpnDom, x, hx, hPair⟩
  · intro u hu
    rcases (ZFSet.mem_sep.mp hu).2 with
      ⟨p, hp, n, hn, huPair⟩
    rcases huPair with rfl

    rcases hb.2 p hp with ⟨x0, hx0, _huniqX0⟩

    have hStep :
        IsFuncFoundational X X
          (parameterStepGraph P X r p) :=
      parameterStepGraph_isFunc hp hr

    have hGlobal :
        IsFuncFoundational omegaTA X
          (globalRecursionGraph
            X x0 (parameterStepGraph P X r p)) :=
      globalRecursionGraph_isFunc hx0.1 hStep

    rcases hGlobal.2 n hn with ⟨x, hx, _huniqX⟩

    refine ⟨x, ?_, ?_⟩
    · refine ⟨hx.1, ?_⟩
      exact parameterizedRecursionGraph_mem.mpr
        ⟨hp, hn, hx.1, x0, hx0.1, hx0.2, hx.2⟩
    · intro y hy
      rcases parameterizedRecursionGraph_mem.mp hy.2 with
        ⟨_hp, _hn, _hyX, y0, hy0, hpy0, hny⟩

      have hx0y0 : x0 = y0 :=
        funcFoundational_pair_value_unique
          hb hp hx0.2 hpy0

      have hnySame :
          ZFSet.pair n y ∈
            globalRecursionGraph
              X x0 (parameterStepGraph P X r p) := by
        rw [hx0y0]
        exact hny

      exact funcFoundational_pair_value_unique
        hGlobal hn hnySame hx.2

/-! ### Etapa C5a2b — ecuaciones y unicidad de la recursión parametrizada -/

/-- La recursión parametrizada toma en `(p, 0)` el valor inicial asignado
por `b` al parámetro `p`. -/
theorem parameterizedRecursionGraph_zero
    {P X b r p x0 : ZFSet}
    (hb : IsFuncFoundational P X b)
    (hr :
      IsFuncFoundational
        (cartesianProductFoundational P X)
        X
        r)
    (hp : p ∈ P)
    (hpx0 : ZFSet.pair p x0 ∈ b) :
    ZFSet.pair (ZFSet.pair p (∅ : ZFSet)) x0 ∈
      parameterizedRecursionGraph P X b r := by
  have hx0 : x0 ∈ X :=
    funcFoundational_value_mem hb hpx0

  have hStep :
      IsFuncFoundational X X
        (parameterStepGraph P X r p) :=
    parameterStepGraph_isFunc hp hr

  have hZero :
      ZFSet.pair (∅ : ZFSet) x0 ∈
        globalRecursionGraph
          X x0 (parameterStepGraph P X r p) :=
    globalRecursionGraph_zero hx0

  exact parameterizedRecursionGraph_mem.mpr
    ⟨hp, omegaTA_isInductive.1, hx0,
      x0, hx0, hpx0, hZero⟩

/-- La ecuación sucesora del grafo recursivo parametrizado. -/
theorem parameterizedRecursionGraph_succ
    {P X b r p n x y : ZFSet}
    (_hb : IsFuncFoundational P X b)
    (hr :
      IsFuncFoundational
        (cartesianProductFoundational P X)
        X
        r)
    (hp : p ∈ P)
    (hn : n ∈ omegaTA)
    (hpnx :
      ZFSet.pair (ZFSet.pair p n) x ∈
        parameterizedRecursionGraph P X b r)
    (hpxy : ZFSet.pair (ZFSet.pair p x) y ∈ r) :
    ZFSet.pair (ZFSet.pair p (succ n)) y ∈
      parameterizedRecursionGraph P X b r := by
  rcases parameterizedRecursionGraph_mem.mp hpnx with
    ⟨_hp, _hn, hx, x0, hx0, hpx0, hnx⟩

  have hy : y ∈ X :=
    funcFoundational_value_mem hr hpxy

  have hStep :
      IsFuncFoundational X X
        (parameterStepGraph P X r p) :=
    parameterStepGraph_isFunc hp hr

  have hxyStep :
      ZFSet.pair x y ∈ parameterStepGraph P X r p :=
    parameterStepGraph_mem.mpr ⟨hx, hy, hpxy⟩

  have hSucc :
      ZFSet.pair (succ n) y ∈
        globalRecursionGraph
          X x0 (parameterStepGraph P X r p) :=
    globalRecursionGraph_succ hx0 hStep hn hnx hxyStep

  exact parameterizedRecursionGraph_mem.mpr
    ⟨hp, TA_PRO_00022_succ_closed hn, hy,
      x0, hx0, hpx0, hSucc⟩

/-- Las ecuaciones inicial y sucesora del grafo recursivo parametrizado. -/
theorem parameterizedRecursionGraph_equations
    {P X b r : ZFSet}
    (hb : IsFuncFoundational P X b)
    (hr :
      IsFuncFoundational
        (cartesianProductFoundational P X)
        X
        r) :
    (∀ p x0 : ZFSet,
      p ∈ P →
      ZFSet.pair p x0 ∈ b →
      ZFSet.pair (ZFSet.pair p (∅ : ZFSet)) x0 ∈
        parameterizedRecursionGraph P X b r) ∧
    (∀ p n x y : ZFSet,
      p ∈ P →
      n ∈ omegaTA →
      ZFSet.pair (ZFSet.pair p n) x ∈
        parameterizedRecursionGraph P X b r →
      ZFSet.pair (ZFSet.pair p x) y ∈ r →
      ZFSet.pair (ZFSet.pair p (succ n)) y ∈
        parameterizedRecursionGraph P X b r) := by
  refine ⟨?_, ?_⟩
  · intro p x0 hp hpx0
    exact parameterizedRecursionGraph_zero hb hr hp hpx0
  · intro p n x y hp hn hpnx hpxy
    exact parameterizedRecursionGraph_succ
      hb hr hp hn hpnx hpxy

/-- Todo grafo funcional sobre `P ×₀ omegaTA` que satisface las ecuaciones
parametrizadas coincide con el grafo recursivo parametrizado canónico. -/
theorem parameterizedRecursionGraph_unique
    {P X b r F : ZFSet}
    (hb : IsFuncFoundational P X b)
    (hr :
      IsFuncFoundational
        (cartesianProductFoundational P X)
        X
        r)
    (hF :
      IsFuncFoundational
        (cartesianProductFoundational P omegaTA)
        X
        F)
    (hF0 :
      ∀ p x0 : ZFSet,
        p ∈ P →
        ZFSet.pair p x0 ∈ b →
        ZFSet.pair (ZFSet.pair p (∅ : ZFSet)) x0 ∈ F)
    (hFSucc :
      ∀ p n x y : ZFSet,
        p ∈ P →
        n ∈ omegaTA →
        ZFSet.pair (ZFSet.pair p n) x ∈ F →
        ZFSet.pair (ZFSet.pair p x) y ∈ r →
        ZFSet.pair (ZFSet.pair p (succ n)) y ∈ F) :
    F = parameterizedRecursionGraph P X b r := by
  let G : ZFSet := parameterizedRecursionGraph P X b r

  have hG :
      IsFuncFoundational
        (cartesianProductFoundational P omegaTA)
        X
        G := by
    exact parameterizedRecursionGraph_isFunc hb hr

  let PRED : ZFSet → Prop := fun n =>
    ∀ p x y : ZFSet,
      p ∈ P →
      ZFSet.pair (ZFSet.pair p n) x ∈ F →
      ZFSet.pair (ZFSet.pair p n) y ∈ G →
      x = y

  have h0 : PRED (∅ : ZFSet) := by
    intro p x y hp hFx hGy
    rcases hb.2 p hp with ⟨x0, hx0, _huniqX0⟩

    have hFZero :
        ZFSet.pair (ZFSet.pair p (∅ : ZFSet)) x0 ∈ F :=
      hF0 p x0 hp hx0.2
    have hGZero :
        ZFSet.pair (ZFSet.pair p (∅ : ZFSet)) x0 ∈ G := by
      exact parameterizedRecursionGraph_zero hb hr hp hx0.2
    have hpZeroDom :
        ZFSet.pair p (∅ : ZFSet) ∈
          cartesianProductFoundational P omegaTA :=
      mem_cartesianProductFoundational.mpr
        ⟨hp, omegaTA_isInductive.1⟩

    have hxx0 : x = x0 :=
      funcFoundational_pair_value_unique
        hF hpZeroDom hFx hFZero
    have hyx0 : y = x0 :=
      funcFoundational_pair_value_unique
        hG hpZeroDom hGy hGZero
    exact hxx0.trans hyx0.symm

  have hs :
      ∀ n : ZFSet,
        n ∈ omegaTA →
        PRED n →
        PRED (succ n) := by
    intro n hn ih p x y hp hFx hGy

    have hsn : succ n ∈ omegaTA :=
      TA_PRO_00022_succ_closed hn
    have hpnDom :
        ZFSet.pair p n ∈
          cartesianProductFoundational P omegaTA :=
      mem_cartesianProductFoundational.mpr ⟨hp, hn⟩
    have hpsnDom :
        ZFSet.pair p (succ n) ∈
          cartesianProductFoundational P omegaTA :=
      mem_cartesianProductFoundational.mpr ⟨hp, hsn⟩

    rcases hF.2 (ZFSet.pair p n) hpnDom with
      ⟨a, ha, _huniqA⟩
    rcases hG.2 (ZFSet.pair p n) hpnDom with
      ⟨bval, hbval, _huniqB⟩

    have hab : a = bval :=
      ih p a bval hp ha.2 hbval.2

    have hpaDom :
        ZFSet.pair p a ∈ cartesianProductFoundational P X :=
      mem_cartesianProductFoundational.mpr ⟨hp, ha.1⟩
    rcases hr.2 (ZFSet.pair p a) hpaDom with
      ⟨c, hc, _huniqC⟩

    have hSuccF :
        ZFSet.pair (ZFSet.pair p (succ n)) c ∈ F :=
      hFSucc p n a c hp hn ha.2 hc.2

    have hnaG :
        ZFSet.pair (ZFSet.pair p n) a ∈ G := by
      rw [hab]
      exact hbval.2
    have hSuccG :
        ZFSet.pair (ZFSet.pair p (succ n)) c ∈ G := by
      exact parameterizedRecursionGraph_succ
        hb hr hp hn hnaG hc.2

    have hxc : x = c :=
      funcFoundational_pair_value_unique
        hF hpsnDom hFx hSuccF
    have hyc : y = c :=
      funcFoundational_pair_value_unique
        hG hpsnDom hGy hSuccG
    exact hxc.trans hyc.symm

  have hAgreement :
      ∀ n : ZFSet,
        n ∈ omegaTA →
        PRED n :=
    TA_THM_00008_induction PRED h0 hs

  apply ZFSet.ext
  intro z
  constructor
  · intro hzF
    rcases hF.1 z hzF with
      ⟨u, hu, x, _hx, hzPair⟩
    rcases (ZFSet.mem_sep.mp hu).2 with
      ⟨p, hp, n, hn, huPair⟩
    rcases huPair with rfl
    rcases hG.2 (ZFSet.pair p n) hu with
      ⟨y, hy, _huniqY⟩
    have hpnxF : ZFSet.pair (ZFSet.pair p n) x ∈ F := by
      rw [← hzPair]
      exact hzF
    have hxy : x = y :=
      hAgreement n hn p x y hp hpnxF hy.2
    rw [hzPair, hxy]
    exact hy.2
  · intro hzG
    rcases hG.1 z hzG with
      ⟨u, hu, y, _hy, hzPair⟩
    rcases (ZFSet.mem_sep.mp hu).2 with
      ⟨p, hp, n, hn, huPair⟩
    rcases huPair with rfl
    rcases hF.2 (ZFSet.pair p n) hu with
      ⟨x, hx, _huniqX⟩
    have hpnyG : ZFSet.pair (ZFSet.pair p n) y ∈ G := by
      rw [← hzPair]
      exact hzG
    have hxy : x = y :=
      hAgreement n hn p x y hp hx.2 hpnyG
    rw [hzPair, ← hxy]
    exact hx.2

/-- TA-COR-00002 — existencia y unicidad de la recursión parametrizada. -/
theorem TA_COR_00002_parameterized_recursion
    {P X b r : ZFSet}
    (hb : IsFuncFoundational P X b)
    (hr :
      IsFuncFoundational
        (cartesianProductFoundational P X)
        X
        r) :
    ∃! F : ZFSet,
      IsFuncFoundational
        (cartesianProductFoundational P omegaTA)
        X
        F ∧
      (∀ p x0 : ZFSet,
        p ∈ P →
        ZFSet.pair p x0 ∈ b →
        ZFSet.pair (ZFSet.pair p (∅ : ZFSet)) x0 ∈ F) ∧
      (∀ p n x y : ZFSet,
        p ∈ P →
        n ∈ omegaTA →
        ZFSet.pair (ZFSet.pair p n) x ∈ F →
        ZFSet.pair (ZFSet.pair p x) y ∈ r →
        ZFSet.pair (ZFSet.pair p (succ n)) y ∈ F) := by
  refine ⟨parameterizedRecursionGraph P X b r, ?_, ?_⟩
  · have hEq := parameterizedRecursionGraph_equations hb hr
    exact ⟨parameterizedRecursionGraph_isFunc hb hr, hEq.1, hEq.2⟩
  · intro F hData
    exact parameterizedRecursionGraph_unique
      hb hr hData.1 hData.2.1 hData.2.2

/-! ### Etapa C5b1 — TA-DEF-00036: adición por recursión parametrizada -/

/-- Grafo base de la adición. Asigna a cada parámetro natural `m` el
valor inicial `m`, sin presuponer ninguna operación de suma. -/
def natAddBaseGraph : ZFSet :=
  ZFSet.sep
    (fun z =>
      ∃ m : ZFSet,
        m ∈ omegaTA ∧
        z = ZFSet.pair m m)
    (pairAmbient omegaTA omegaTA)

/-- Caracterización del grafo base de la adición. -/
theorem natAddBaseGraph_mem {m x : ZFSet} :
    ZFSet.pair m x ∈ natAddBaseGraph ↔
      m ∈ omegaTA ∧ x = m := by
  constructor
  · intro hmx
    rcases (ZFSet.mem_sep.mp hmx).2 with
      ⟨m', hm', hPair⟩
    rcases ZFSet.pair_injective hPair with ⟨rfl, rfl⟩
    exact ⟨hm', rfl⟩
  · rintro ⟨hm, rfl⟩
    apply ZFSet.mem_sep.mpr
    exact ⟨pair_mem_pairAmbient hm hm, x, hm, rfl⟩

/-- El grafo base es la función identidad fundacional sobre `omegaTA`. -/
theorem natAddBaseGraph_isFunc :
    IsFuncFoundational omegaTA omegaTA natAddBaseGraph := by
  constructor
  · intro z hz
    rcases (ZFSet.mem_sep.mp hz).2 with ⟨m, hm, hPair⟩
    exact ⟨m, hm, m, hm, hPair⟩
  · intro m hm
    refine ⟨m, ⟨hm, natAddBaseGraph_mem.mpr ⟨hm, rfl⟩⟩, ?_⟩
    intro x hx
    exact (natAddBaseGraph_mem.mp hx.2).2

/-- Grafo de paso de la adición. El primer natural `m` permanece como
parámetro; el valor siguiente es `succ x`. -/
def natAddStepGraph : ZFSet :=
  ZFSet.sep
    (fun z =>
      ∃ m : ZFSet,
        m ∈ omegaTA ∧
        ∃ x : ZFSet,
          x ∈ omegaTA ∧
          z = ZFSet.pair (ZFSet.pair m x) (succ x))
    (pairAmbient
      (cartesianProductFoundational omegaTA omegaTA)
      omegaTA)

/-- Caracterización del paso parametrizado de la adición. -/
theorem natAddStepGraph_mem {m x y : ZFSet} :
    ZFSet.pair (ZFSet.pair m x) y ∈ natAddStepGraph ↔
      m ∈ omegaTA ∧
      x ∈ omegaTA ∧
      y = succ x := by
  constructor
  · intro hmxy
    rcases (ZFSet.mem_sep.mp hmxy).2 with
      ⟨m', hm', x', hx', hPair⟩
    rcases ZFSet.pair_injective hPair with ⟨hArg, hValue⟩
    rcases ZFSet.pair_injective hArg with ⟨rfl, rfl⟩
    rcases hValue with rfl
    exact ⟨hm', hx', rfl⟩
  · rintro ⟨hm, hx, rfl⟩
    have hmxDom :
        ZFSet.pair m x ∈
          cartesianProductFoundational omegaTA omegaTA :=
      mem_cartesianProductFoundational.mpr ⟨hm, hx⟩
    have hsx : succ x ∈ omegaTA :=
      TA_PRO_00022_succ_closed hx
    apply ZFSet.mem_sep.mpr
    exact ⟨pair_mem_pairAmbient hmxDom hsx,
      m, hm, x, hx, rfl⟩

/-- El paso `((m,x), succ x)` es una función fundacional total sobre
`omegaTA ×₀ omegaTA`. -/
theorem natAddStepGraph_isFunc :
    IsFuncFoundational
      (cartesianProductFoundational omegaTA omegaTA)
      omegaTA
      natAddStepGraph := by
  constructor
  · intro z hz
    rcases (ZFSet.mem_sep.mp hz).2 with
      ⟨m, hm, x, hx, hPair⟩
    have hmxDom :
        ZFSet.pair m x ∈
          cartesianProductFoundational omegaTA omegaTA :=
      mem_cartesianProductFoundational.mpr ⟨hm, hx⟩
    have hsx : succ x ∈ omegaTA :=
      TA_PRO_00022_succ_closed hx
    exact ⟨ZFSet.pair m x, hmxDom, succ x, hsx, hPair⟩
  · intro u hu
    rcases (ZFSet.mem_sep.mp hu).2 with
      ⟨m, hm, x, hx, huPair⟩
    rcases huPair with rfl
    have hsx : succ x ∈ omegaTA :=
      TA_PRO_00022_succ_closed hx
    refine ⟨succ x, ?_, ?_⟩
    · exact ⟨hsx, natAddStepGraph_mem.mpr ⟨hm, hx, rfl⟩⟩
    · intro y hy
      exact (natAddStepGraph_mem.mp hy.2).2.2

/-- Grafo canónico de la adición. El primer argumento `m` es el parámetro
y la recursión se realiza sobre el segundo argumento `n`. -/
def natAddGraph : ZFSet :=
  parameterizedRecursionGraph
    omegaTA
    omegaTA
    natAddBaseGraph
    natAddStepGraph

/-- El grafo canónico de la adición es una función total
`omegaTA ×₀ omegaTA → omegaTA`. -/
theorem natAddGraph_isFunc :
    IsFuncFoundational
      (cartesianProductFoundational omegaTA omegaTA)
      omegaTA
      natAddGraph := by
  exact parameterizedRecursionGraph_isFunc
    natAddBaseGraph_isFunc natAddStepGraph_isFunc

/-- Ecuación inicial de la adición: `m + 0 = m`, expresada sin usar una
operación de suma preexistente. -/
theorem natAddGraph_zero {m : ZFSet}
    (hm : m ∈ omegaTA) :
    ZFSet.pair (ZFSet.pair m (∅ : ZFSet)) m ∈ natAddGraph := by
  have hmm : ZFSet.pair m m ∈ natAddBaseGraph :=
    natAddBaseGraph_mem.mpr ⟨hm, rfl⟩
  exact parameterizedRecursionGraph_zero
    natAddBaseGraph_isFunc natAddStepGraph_isFunc hm hmm

/-- Ecuación sucesora de la adición. La recursión es sobre `n`, el segundo
argumento: el valor en `succ n` es el sucesor del valor en `n`.
La conmutatividad no forma parte de esta definición. -/
theorem natAddGraph_succ {m n x : ZFSet}
    (hm : m ∈ omegaTA)
    (hn : n ∈ omegaTA)
    (hmnx : ZFSet.pair (ZFSet.pair m n) x ∈ natAddGraph) :
    ZFSet.pair (ZFSet.pair m (succ n)) (succ x) ∈ natAddGraph := by
  have hx : x ∈ omegaTA :=
    funcFoundational_value_mem natAddGraph_isFunc hmnx
  have hStep :
      ZFSet.pair (ZFSet.pair m x) (succ x) ∈ natAddStepGraph :=
    natAddStepGraph_mem.mpr ⟨hm, hx, rfl⟩
  exact parameterizedRecursionGraph_succ
    natAddBaseGraph_isFunc natAddStepGraph_isFunc
    hm hn hmnx hStep

/-- Las dos ecuaciones definitorias del grafo de adición. -/
theorem natAddGraph_equations :
    (∀ m : ZFSet,
      m ∈ omegaTA →
      ZFSet.pair (ZFSet.pair m (∅ : ZFSet)) m ∈ natAddGraph) ∧
    (∀ m n x : ZFSet,
      m ∈ omegaTA →
      n ∈ omegaTA →
      ZFSet.pair (ZFSet.pair m n) x ∈ natAddGraph →
      ZFSet.pair (ZFSet.pair m (succ n)) (succ x) ∈ natAddGraph) := by
  refine ⟨?_, ?_⟩
  · intro m hm
    exact natAddGraph_zero hm
  · intro m n x hm hn hmnx
    exact natAddGraph_succ hm hn hmnx

/-- TA-DEF-00036 — existencia y unicidad de la adición de naturales.
El primer argumento es un parámetro y la recursión se efectúa sobre el
segundo; esta construcción no presupone suma ni conmutatividad previas. -/
theorem TA_DEF_00036_addition :
    ∃! add : ZFSet,
      IsFuncFoundational
        (cartesianProductFoundational omegaTA omegaTA)
        omegaTA
        add ∧
      (∀ m : ZFSet,
        m ∈ omegaTA →
        ZFSet.pair (ZFSet.pair m (∅ : ZFSet)) m ∈ add) ∧
      (∀ m n x : ZFSet,
        m ∈ omegaTA →
        n ∈ omegaTA →
        ZFSet.pair (ZFSet.pair m n) x ∈ add →
        ZFSet.pair (ZFSet.pair m (succ n)) (succ x) ∈ add) := by
  rcases TA_COR_00002_parameterized_recursion
      natAddBaseGraph_isFunc natAddStepGraph_isFunc with
    ⟨add, hAdd, hUnique⟩

  refine ⟨add, ?_, ?_⟩
  · refine ⟨hAdd.1, ?_, ?_⟩
    · intro m hm
      exact hAdd.2.1 m m hm
        (natAddBaseGraph_mem.mpr ⟨hm, rfl⟩)
    · intro m n x hm hn hmnx
      have hx : x ∈ omegaTA :=
        funcFoundational_value_mem hAdd.1 hmnx
      exact hAdd.2.2 m n x (succ x) hm hn hmnx
        (natAddStepGraph_mem.mpr ⟨hm, hx, rfl⟩)
  · intro f hf
    apply hUnique f
    refine ⟨hf.1, ?_, ?_⟩
    · intro m x0 hm hmx0
      have hx0m : x0 = m :=
        (natAddBaseGraph_mem.mp hmx0).2
      rw [hx0m]
      exact hf.2.1 m hm
    · intro m n x y hm hn hmnx hmxy
      have hy : y = succ x :=
        (natAddStepGraph_mem.mp hmxy).2.2
      rw [hy]
      exact hf.2.2 m n x hm hn hmnx

/-! ### Etapa C5b2 — TA-DEF-00037: multiplicación por recursión parametrizada -/

/-- Grafo base de la multiplicación. Asigna a cada parámetro natural `m`
el valor inicial cero. -/
def natMulBaseGraph : ZFSet :=
  ZFSet.sep
    (fun z =>
      ∃ m : ZFSet,
        m ∈ omegaTA ∧
        z = ZFSet.pair m (∅ : ZFSet))
    (pairAmbient omegaTA omegaTA)

/-- Caracterización del grafo base constante cero. -/
theorem natMulBaseGraph_mem {m x : ZFSet} :
    ZFSet.pair m x ∈ natMulBaseGraph ↔
      m ∈ omegaTA ∧ x = (∅ : ZFSet) := by
  constructor
  · intro hmx
    rcases (ZFSet.mem_sep.mp hmx).2 with
      ⟨m', hm', hPair⟩
    rcases ZFSet.pair_injective hPair with ⟨rfl, rfl⟩
    exact ⟨hm', rfl⟩
  · rintro ⟨hm, rfl⟩
    have hZero : (∅ : ZFSet) ∈ omegaTA :=
      omegaTA_isInductive.1
    apply ZFSet.mem_sep.mpr
    exact ⟨pair_mem_pairAmbient hm hZero, m, hm, rfl⟩

/-- El grafo base de la multiplicación es una función fundacional total. -/
theorem natMulBaseGraph_isFunc :
    IsFuncFoundational omegaTA omegaTA natMulBaseGraph := by
  have hZero : (∅ : ZFSet) ∈ omegaTA :=
    omegaTA_isInductive.1
  constructor
  · intro z hz
    rcases (ZFSet.mem_sep.mp hz).2 with ⟨m, hm, hPair⟩
    exact ⟨m, hm, (∅ : ZFSet), hZero, hPair⟩
  · intro m hm
    refine ⟨(∅ : ZFSet), ?_, ?_⟩
    · exact ⟨hZero, natMulBaseGraph_mem.mpr ⟨hm, rfl⟩⟩
    · intro x hx
      exact (natMulBaseGraph_mem.mp hx.2).2

/-- Grafo de paso de la multiplicación. El primer argumento `m` permanece
como parámetro y el nuevo valor es `x + m`, representado exclusivamente
por la pertenencia `<<x,m>,y> ∈ natAddGraph`; no se usa conmutatividad. -/
def natMulStepGraph : ZFSet :=
  ZFSet.sep
    (fun z =>
      ∃ m : ZFSet,
        m ∈ omegaTA ∧
        ∃ x : ZFSet,
          x ∈ omegaTA ∧
          ∃ y : ZFSet,
            y ∈ omegaTA ∧
            z = ZFSet.pair (ZFSet.pair m x) y ∧
            ZFSet.pair (ZFSet.pair x m) y ∈ natAddGraph)
    (pairAmbient
      (cartesianProductFoundational omegaTA omegaTA)
      omegaTA)

/-- Caracterización del paso de multiplicación mediante el grafo de la
adición previamente construido. -/
theorem natMulStepGraph_mem {m x y : ZFSet} :
    ZFSet.pair (ZFSet.pair m x) y ∈ natMulStepGraph ↔
      m ∈ omegaTA ∧
      x ∈ omegaTA ∧
      y ∈ omegaTA ∧
      ZFSet.pair (ZFSet.pair x m) y ∈ natAddGraph := by
  constructor
  · intro hmxy
    rcases (ZFSet.mem_sep.mp hmxy).2 with
      ⟨m', hm', x', hx', y', hy', hPair, hAdd⟩
    rcases ZFSet.pair_injective hPair with ⟨hArg, hValue⟩
    rcases ZFSet.pair_injective hArg with ⟨rfl, rfl⟩
    rcases hValue with rfl
    exact ⟨hm', hx', hy', hAdd⟩
  · rintro ⟨hm, hx, hy, hAdd⟩
    have hmxDom :
        ZFSet.pair m x ∈
          cartesianProductFoundational omegaTA omegaTA :=
      mem_cartesianProductFoundational.mpr ⟨hm, hx⟩
    apply ZFSet.mem_sep.mpr
    exact ⟨pair_mem_pairAmbient hmxDom hy,
      m, hm, x, hx, y, hy, rfl, hAdd⟩

/-- El paso `(m,x) ↦ x + m` es una función fundacional total; su
funcionalidad procede de `natAddGraph_isFunc`. -/
theorem natMulStepGraph_isFunc :
    IsFuncFoundational
      (cartesianProductFoundational omegaTA omegaTA)
      omegaTA
      natMulStepGraph := by
  constructor
  · intro z hz
    rcases (ZFSet.mem_sep.mp hz).2 with
      ⟨m, hm, x, hx, y, hy, hPair, _hAdd⟩
    have hmxDom :
        ZFSet.pair m x ∈
          cartesianProductFoundational omegaTA omegaTA :=
      mem_cartesianProductFoundational.mpr ⟨hm, hx⟩
    exact ⟨ZFSet.pair m x, hmxDom, y, hy, hPair⟩
  · intro u hu
    rcases (ZFSet.mem_sep.mp hu).2 with
      ⟨m, hm, x, hx, huPair⟩
    rcases huPair with rfl

    have hxmDom :
        ZFSet.pair x m ∈
          cartesianProductFoundational omegaTA omegaTA :=
      mem_cartesianProductFoundational.mpr ⟨hx, hm⟩
    rcases natAddGraph_isFunc.2 (ZFSet.pair x m) hxmDom with
      ⟨y, hy, _huniqY⟩

    refine ⟨y, ?_, ?_⟩
    · exact ⟨hy.1,
        natMulStepGraph_mem.mpr ⟨hm, hx, hy.1, hy.2⟩⟩
    · intro z hz
      have hzAdd :
          ZFSet.pair (ZFSet.pair x m) z ∈ natAddGraph :=
        (natMulStepGraph_mem.mp hz.2).2.2.2
      exact funcFoundational_pair_value_unique
        natAddGraph_isFunc hxmDom hzAdd hy.2

/-- Grafo canónico de la multiplicación. `m` es parámetro y la recursión
se realiza sobre `n`, el segundo argumento. -/
def natMulGraph : ZFSet :=
  parameterizedRecursionGraph
    omegaTA
    omegaTA
    natMulBaseGraph
    natMulStepGraph

/-- El grafo canónico de la multiplicación es una función total
`omegaTA ×₀ omegaTA → omegaTA`. -/
theorem natMulGraph_isFunc :
    IsFuncFoundational
      (cartesianProductFoundational omegaTA omegaTA)
      omegaTA
      natMulGraph := by
  exact parameterizedRecursionGraph_isFunc
    natMulBaseGraph_isFunc natMulStepGraph_isFunc

/-- Ecuación inicial de la multiplicación: el valor en `(m,0)` es cero. -/
theorem natMulGraph_zero {m : ZFSet}
    (hm : m ∈ omegaTA) :
    ZFSet.pair (ZFSet.pair m (∅ : ZFSet)) (∅ : ZFSet) ∈
      natMulGraph := by
  have hmZero :
      ZFSet.pair m (∅ : ZFSet) ∈ natMulBaseGraph :=
    natMulBaseGraph_mem.mpr ⟨hm, rfl⟩
  exact parameterizedRecursionGraph_zero
    natMulBaseGraph_isFunc natMulStepGraph_isFunc hm hmZero

/-- Ecuación sucesora de la multiplicación. Si `x` representa `m · n` y
`y` representa exactamente `x + m` en `natAddGraph`, entonces `y` es el
valor en `(m, succ n)`. No se invierte el orden mediante conmutatividad. -/
theorem natMulGraph_succ {m n x y : ZFSet}
    (hm : m ∈ omegaTA)
    (hn : n ∈ omegaTA)
    (hmnx : ZFSet.pair (ZFSet.pair m n) x ∈ natMulGraph)
    (hxmy : ZFSet.pair (ZFSet.pair x m) y ∈ natAddGraph) :
    ZFSet.pair (ZFSet.pair m (succ n)) y ∈ natMulGraph := by
  have hx : x ∈ omegaTA :=
    funcFoundational_value_mem natMulGraph_isFunc hmnx
  have hy : y ∈ omegaTA :=
    funcFoundational_value_mem natAddGraph_isFunc hxmy
  have hStep :
      ZFSet.pair (ZFSet.pair m x) y ∈ natMulStepGraph :=
    natMulStepGraph_mem.mpr ⟨hm, hx, hy, hxmy⟩
  exact parameterizedRecursionGraph_succ
    natMulBaseGraph_isFunc natMulStepGraph_isFunc
    hm hn hmnx hStep

/-- Las dos ecuaciones definitorias del grafo de multiplicación. -/
theorem natMulGraph_equations :
    (∀ m : ZFSet,
      m ∈ omegaTA →
      ZFSet.pair (ZFSet.pair m (∅ : ZFSet)) (∅ : ZFSet) ∈
        natMulGraph) ∧
    (∀ m n x y : ZFSet,
      m ∈ omegaTA →
      n ∈ omegaTA →
      ZFSet.pair (ZFSet.pair m n) x ∈ natMulGraph →
      ZFSet.pair (ZFSet.pair x m) y ∈ natAddGraph →
      ZFSet.pair (ZFSet.pair m (succ n)) y ∈ natMulGraph) := by
  refine ⟨?_, ?_⟩
  · intro m hm
    exact natMulGraph_zero hm
  · intro m n x y hm hn hmnx hxmy
    exact natMulGraph_succ hm hn hmnx hxmy

/-- TA-DEF-00037 — existencia y unicidad de la multiplicación de naturales.
El paso usa únicamente la suma ya construida: `x + m`, en ese orden. No se
presupone multiplicación ni se usa conmutatividad. -/
theorem TA_DEF_00037_multiplication :
    ∃! mul : ZFSet,
      IsFuncFoundational
        (cartesianProductFoundational omegaTA omegaTA)
        omegaTA
        mul ∧
      (∀ m : ZFSet,
        m ∈ omegaTA →
        ZFSet.pair (ZFSet.pair m (∅ : ZFSet)) (∅ : ZFSet) ∈ mul) ∧
      (∀ m n x y : ZFSet,
        m ∈ omegaTA →
        n ∈ omegaTA →
        ZFSet.pair (ZFSet.pair m n) x ∈ mul →
        ZFSet.pair (ZFSet.pair x m) y ∈ natAddGraph →
        ZFSet.pair (ZFSet.pair m (succ n)) y ∈ mul) := by
  rcases TA_COR_00002_parameterized_recursion
      natMulBaseGraph_isFunc natMulStepGraph_isFunc with
    ⟨mul, hMul, hUnique⟩

  refine ⟨mul, ?_, ?_⟩
  · refine ⟨hMul.1, ?_, ?_⟩
    · intro m hm
      exact hMul.2.1 m (∅ : ZFSet) hm
        (natMulBaseGraph_mem.mpr ⟨hm, rfl⟩)
    · intro m n x y hm hn hmnx hxmy
      have hx : x ∈ omegaTA :=
        funcFoundational_value_mem hMul.1 hmnx
      have hy : y ∈ omegaTA :=
        funcFoundational_value_mem natAddGraph_isFunc hxmy
      exact hMul.2.2 m n x y hm hn hmnx
        (natMulStepGraph_mem.mpr ⟨hm, hx, hy, hxmy⟩)
  · intro f hf
    apply hUnique f
    refine ⟨hf.1, ?_, ?_⟩
    · intro m x0 hm hmx0
      have hx0Zero : x0 = (∅ : ZFSet) :=
        (natMulBaseGraph_mem.mp hmx0).2
      rw [hx0Zero]
      exact hf.2.1 m hm
    · intro m n x y hm hn hmnx hmxy
      have hxmy :
          ZFSet.pair (ZFSet.pair x m) y ∈ natAddGraph :=
        (natMulStepGraph_mem.mp hmxy).2.2.2
      exact hf.2.2 m n x y hm hn hmnx hxmy

end TratadoAnalisis.Naturals.Recursion
