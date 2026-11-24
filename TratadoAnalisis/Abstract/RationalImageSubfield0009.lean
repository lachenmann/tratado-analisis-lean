import TratadoAnalisis.Abstract.RationalImageGraphBridge0009

/-!
# TA-PRO-00078 — P2: la imagen racional por grafo es un subcuerpo

Candidato experimental, pendiente de compilación en Lean 4.32.1.

El conjunto principal es RationalImageByGraphManual Q E G, definido por
Separación directamente a partir del grafo conjuntista G : ZFSet.

La función auxiliar ι solo aparece en hipótesis y pruebas de transporte,
nunca en la definición de la imagen principal. No se demuestra aquí
TA-THM-00036, TA-COR-00012 ni la densidad TA-PRO-00078.
-/

namespace TratadoAnalisis.AbstractCompleteness.Density0009

universe u

open TratadoAnalisis.Dedekind.FieldPredicates
open TratadoAnalisis.Naturals.Recursion

/-- TA-DEF-00069, expresada sobre operaciones relacionales y un portador
    conjuntista: subcampo del cuerpo ambiente con clausura bajo suma,
    producto, opuesto e inversos no nulos.

    Las operaciones de E se *restringen* a K; la unicidad de sus valores
    se hereda del predicado IsFieldFoundational E, sin seleccionarlos. -/
def IsSubfieldRelationalManual
    (E K zeroE oneE : ZFSet.{u})
    (addE mulE : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop) : Prop :=
  IsFieldFoundational E zeroE oneE addE mulE ∧
  K ⊆ E ∧
  zeroE ∈ K ∧
  oneE ∈ K ∧
  (∀ x y : ZFSet.{u}, x ∈ K → y ∈ K →
    ∃ z : ZFSet.{u}, z ∈ K ∧ addE x y z) ∧
  (∀ x y : ZFSet.{u}, x ∈ K → y ∈ K →
    ∃ z : ZFSet.{u}, z ∈ K ∧ mulE x y z) ∧
  (∀ x : ZFSet.{u}, x ∈ K →
    ∃ nx : ZFSet.{u}, nx ∈ K ∧
      addE x nx zeroE ∧ addE nx x zeroE) ∧
  (∀ x : ZFSet.{u}, x ∈ K → x ≠ zeroE →
    ∃ ix : ZFSet.{u}, ix ∈ K ∧
      mulE x ix oneE ∧ mulE ix x oneE)

/-- Lectura definicional completa de TA-DEF-00069; no es una nueva
    demostración de leyes de cuerpo. -/
theorem isSubfieldRelational_iff_manual
    (E K zeroE oneE : ZFSet.{u})
    (addE mulE : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop) :
    IsSubfieldRelationalManual E K zeroE oneE addE mulE ↔
    (IsFieldFoundational E zeroE oneE addE mulE ∧
      K ⊆ E ∧ zeroE ∈ K ∧ oneE ∈ K ∧
      (∀ x y : ZFSet.{u}, x ∈ K → y ∈ K →
        ∃ z : ZFSet.{u}, z ∈ K ∧ addE x y z) ∧
      (∀ x y : ZFSet.{u}, x ∈ K → y ∈ K →
        ∃ z : ZFSet.{u}, z ∈ K ∧ mulE x y z) ∧
      (∀ x : ZFSet.{u}, x ∈ K →
        ∃ nx : ZFSet.{u}, nx ∈ K ∧
          addE x nx zeroE ∧ addE nx x zeroE) ∧
      (∀ x : ZFSet.{u}, x ∈ K → x ≠ zeroE →
        ∃ ix : ZFSet.{u}, ix ∈ K ∧
          mulE x ix oneE ∧ mulE ix x oneE)) := by
  rfl

/-- Lema algebraico de transporte: si ι lleva Q a E, preserva las
    operaciones relacionales y las unidades, su imagen definida por
    Separación es un subcuerpo. El campo del dominio y el ambiente son
    predicados ZFSet propios, no instancias Field de mathlib. -/
theorem rationalImageFunction_isSubfield_manual
    (Q E zeroQ oneQ zeroE oneE : ZFSet.{u})
    (addQ mulQ addE mulE : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (ι : ZFSet.{u} → ZFSet.{u})
    (hQ : IsFieldFoundational Q zeroQ oneQ addQ mulQ)
    (hE : IsFieldFoundational E zeroE oneE addE mulE)
    (hmap : ∀ q : ZFSet.{u}, q ∈ Q → ι q ∈ E)
    (hzero : ι zeroQ = zeroE)
    (hone : ι oneQ = oneE)
    (hadd : ∀ x y z : ZFSet.{u}, x ∈ Q → y ∈ Q → z ∈ Q →
      addQ x y z → addE (ι x) (ι y) (ι z))
    (hmul : ∀ x y z : ZFSet.{u}, x ∈ Q → y ∈ Q → z ∈ Q →
      mulQ x y z → mulE (ι x) (ι y) (ι z)) :
    IsSubfieldRelationalManual E (RationalImageManual Q E ι)
      zeroE oneE addE mulE := by
  rcases hQ with
    ⟨haddGroupQ, hmulTotalQ, honeQ, _, _, _, _, _, hinvQ⟩
  rcases haddGroupQ with
    ⟨haddTotalQ, hzeroQ, _, _, _, hnegQ⟩
  refine ⟨hE, rationalImage_subset_manual Q E ι, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h0 : ι zeroQ ∈ RationalImageManual Q E ι :=
      rationalImage_mem_of_maps_manual Q E ι hmap zeroQ hzeroQ
    simpa only [hzero] using h0
  · have h1 : ι oneQ ∈ RationalImageManual Q E ι :=
      rationalImage_mem_of_maps_manual Q E ι hmap oneQ honeQ
    simpa only [hone] using h1
  · intro x y hx hy
    rcases (ZFSet.mem_sep.mp hx) with ⟨_, q, hq, hqx⟩
    rcases (ZFSet.mem_sep.mp hy) with ⟨_, r, hr, hry⟩
    rcases haddTotalQ q hq r hr with ⟨z, ⟨hz, hqr⟩, _⟩
    refine ⟨ι z, rationalImage_mem_of_maps_manual Q E ι hmap z hz, ?_⟩
    have he : addE (ι q) (ι r) (ι z) := hadd q r z hq hr hz hqr
    rw [hqx, hry] at he
    exact he
  · intro x y hx hy
    rcases (ZFSet.mem_sep.mp hx) with ⟨_, q, hq, hqx⟩
    rcases (ZFSet.mem_sep.mp hy) with ⟨_, r, hr, hry⟩
    rcases hmulTotalQ q hq r hr with ⟨z, ⟨hz, hqr⟩, _⟩
    refine ⟨ι z, rationalImage_mem_of_maps_manual Q E ι hmap z hz, ?_⟩
    have he : mulE (ι q) (ι r) (ι z) := hmul q r z hq hr hz hqr
    rw [hqx, hry] at he
    exact he
  · intro x hx
    rcases (ZFSet.mem_sep.mp hx) with ⟨_, q, hq, hqx⟩
    rcases hnegQ q hq with ⟨nq, hnq, hqneg, hnegq⟩
    refine ⟨ι nq, rationalImage_mem_of_maps_manual Q E ι hmap nq hnq, ?_, ?_⟩
    · have he : addE (ι q) (ι nq) (ι zeroQ) :=
        hadd q nq zeroQ hq hnq hzeroQ hqneg
      rw [hqx, hzero] at he
      exact he
    · have he : addE (ι nq) (ι q) (ι zeroQ) :=
        hadd nq q zeroQ hnq hq hzeroQ hnegq
      rw [hqx, hzero] at he
      exact he
  · intro x hx hxne
    rcases (ZFSet.mem_sep.mp hx) with ⟨_, q, hq, hqx⟩
    have hqne : q ≠ zeroQ := by
      intro heq
      apply hxne
      calc
        x = ι q := hqx.symm
        _ = ι zeroQ := congrArg ι heq
        _ = zeroE := hzero
    rcases hinvQ q hq hqne with ⟨iq, hiq, hqinv, hinvq⟩
    refine ⟨ι iq, rationalImage_mem_of_maps_manual Q E ι hmap iq hiq, ?_, ?_⟩
    · have he : mulE (ι q) (ι iq) (ι oneQ) :=
        hmul q iq oneQ hq hiq honeQ hqinv
      rw [hqx, hone] at he
      exact he
    · have he : mulE (ι iq) (ι q) (ι oneQ) :=
        hmul iq q oneQ hiq hq honeQ hinvq
      rw [hqx, hone] at he
      exact he

/-- P2: la imagen primaria *por grafo ZFSet* de una incrustación de
    cuerpos ordenados es un subcuerpo del codominio, según TA-DEF-00069.
    Esta declaración no presupone ni demuestra densidad de la imagen. -/
theorem rationalImageByGraph_isSubfield_manual
    (Q E zeroQ oneQ zeroE oneE : ZFSet.{u})
    (addQ mulQ addE mulE : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (leQ leE : ZFSet.{u} → ZFSet.{u} → Prop)
    (ι : ZFSet.{u} → ZFSet.{u}) (G f : ZFSet.{u})
    (hemb : IsOrderedFieldEmbeddingFoundational
      Q E zeroQ oneQ zeroE oneE addQ mulQ addE mulE leQ leE ι G f) :
    IsSubfieldRelationalManual E (RationalImageByGraphManual Q E G)
      zeroE oneE addE mulE := by
  have hG : IsFuncFoundational Q E G :=
    embedding_graph_isFunc_manual Q E zeroQ oneQ zeroE oneE
      addQ mulQ addE mulE leQ leE ι G f hemb
  have heq : RationalImageByGraphManual Q E G = RationalImageManual Q E ι :=
    rationalImageByGraph_eq_of_embedding_manual Q E zeroQ oneQ zeroE oneE
      addQ mulQ addE mulE leQ leE ι G f hemb
  rcases hemb with
    ⟨hQord, hEord, _, _, hgraph, _, hzero, hone, hadd, hmul, _⟩
  have hmap : ∀ q : ZFSet.{u}, q ∈ Q → ι q ∈ E := by
    intro q hq
    exact funcFoundational_value_mem hG (hgraph q hq)
  rw [heq]
  exact rationalImageFunction_isSubfield_manual Q E zeroQ oneQ zeroE oneE
    addQ mulQ addE mulE ι hQord.1 hEord.1 hmap hzero hone hadd hmul

end TratadoAnalisis.AbstractCompleteness.Density0009
