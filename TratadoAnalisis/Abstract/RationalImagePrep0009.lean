import TratadoAnalisis.Abstract.ArchimedeanEditorialBridge0008
import TratadoAnalisis.Dedekind.FieldPredicates

/-!
TA-PRO-00078 — Etapa preliminar, NO certificado.
Conserva la interfaz relacional ZFSet y separa las obligaciones de la imagen
racional de la dependencia todavía no formalizada TA-THM-00036 / TA-COR-00012.
No demuestra aún la densidad: prueba la compatibilidad estricta de una
incrustación de cuerpos ordenados y prepara la imagen por Separación.
-/

namespace TratadoAnalisis.AbstractCompleteness.Density0009

open TratadoAnalisis.Dedekind.FieldPredicates
open TratadoAnalisis.AbstractCompleteness.Manual0008

universe u

/-- Imagen de una aplicación racional dentro del cuerpo ambiente, mediante Separación. -/
def RationalImageManual (Q E : ZFSet.{u})
    (iota : ZFSet.{u} → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun y => ∃ q : ZFSet.{u}, q ∈ Q ∧ iota q = y) E

theorem rationalImage_subset_manual (Q E : ZFSet.{u})
    (iota : ZFSet.{u} → ZFSet.{u}) :
    RationalImageManual Q E iota ⊆ E := by
  intro y hy
  exact (ZFSet.mem_sep.mp hy).1

/-- Una aplicación que envía Q a E tiene imagen conjuntista bien definida. -/
theorem rationalImage_mem_of_maps_manual (Q E : ZFSet.{u})
    (iota : ZFSet.{u} → ZFSet.{u})
    (hmap : ∀ q : ZFSet.{u}, q ∈ Q → iota q ∈ E)
    (q : ZFSet.{u}) (hq : q ∈ Q) :
    iota q ∈ RationalImageManual Q E iota := by
  exact ZFSet.mem_sep.mpr ⟨hmap q hq, q, hq, rfl⟩

/-- La inmersión preserva y refleja el orden estricto. -/
theorem orderedEmbedding_strict_iff_manual
    (Q E zeroQ oneQ zeroE oneE : ZFSet.{u})
    (addQ mulQ addE mulE : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (leQ leE : ZFSet.{u} → ZFSet.{u} → Prop)
    (iota : ZFSet.{u} → ZFSet.{u}) (G f : ZFSet.{u})
    (hemb : IsOrderedFieldEmbeddingFoundational
      Q E zeroQ oneQ zeroE oneE addQ mulQ addE mulE leQ leE iota G f)
    (q r : ZFSet.{u}) (hq : q ∈ Q) (hr : r ∈ Q) :
    StrictFromLeManual leQ q r ↔ StrictFromLeManual leE (iota q) (iota r) := by
  rcases hemb with ⟨_, _, _, _, _, hinj, _, _, _, _, hle⟩
  constructor
  · rintro ⟨hqr, hneq⟩
    refine ⟨(hle q r hq hr).mp hqr, ?_⟩
    intro heq
    exact hneq (hinj q r hq hr heq)
  · rintro ⟨hqr, hneq⟩
    refine ⟨(hle q r hq hr).mpr hqr, ?_⟩
    intro heq
    exact hneq (congrArg iota heq)

#check RationalImageManual
#check rationalImage_subset_manual
#print axioms rationalImage_subset_manual
#check rationalImage_mem_of_maps_manual
#print axioms rationalImage_mem_of_maps_manual
#check orderedEmbedding_strict_iff_manual
#print axioms orderedEmbedding_strict_iff_manual

end TratadoAnalisis.AbstractCompleteness.Density0009
