import TratadoAnalisis.Abstract.RationalImagePrep0009

/-!
# TA-PRO-00078 — puente grafo–función–imagen, candidato experimental

La imagen primaria se define mediante un grafo ZFSet y Separación sobre E.
El parámetro funcional `ι` solo se utiliza para cotejar la representación
anterior bajo las hipótesis explícitas de TA-DEF-00077.
No se demuestra todavía la densidad TA-PRO-00078.
-/

namespace TratadoAnalisis.AbstractCompleteness.Density0009

universe u

open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Dedekind.FieldPredicates
open TratadoAnalisis.Foundations.FunctionTriple

/-- Imagen conjuntista de un grafo G : Q → E. No elige una función ni valores. -/
def RationalImageByGraphManual (Q E G : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep
    (fun y => ∃ q : ZFSet.{u}, q ∈ Q ∧ ZFSet.pair q y ∈ G) E

/-- Especificación extensional exacta de la imagen por el grafo. -/
theorem mem_rationalImageByGraph_iff_manual
    (Q E G y : ZFSet.{u}) :
    y ∈ RationalImageByGraphManual Q E G ↔
      y ∈ E ∧ ∃ q : ZFSet.{u}, q ∈ Q ∧ ZFSet.pair q y ∈ G := by
  exact ZFSet.mem_sep

/-- La imagen por grafo está contenida en el codominio fijado. -/
theorem rationalImageByGraph_subset_manual
    (Q E G : ZFSet.{u}) :
    RationalImageByGraphManual Q E G ⊆ E := by
  intro y hy
  exact ((mem_rationalImageByGraph_iff_manual Q E G y).mp hy).1

/-- Un par del grafo funcional determina un elemento de la imagen. -/
theorem rationalImageByGraph_mem_of_pair_manual
    (Q E G : ZFSet.{u})
    (hG : IsFuncFoundational Q E G)
    (q y : ZFSet.{u}) (hq : q ∈ Q)
    (hqy : ZFSet.pair q y ∈ G) :
    y ∈ RationalImageByGraphManual Q E G := by
  have hy : y ∈ E := funcFoundational_value_mem hG hqy
  exact (mem_rationalImageByGraph_iff_manual Q E G y).mpr
    ⟨hy, q, hq, hqy⟩

/-- Para un grafo funcional, pertenecer a la imagen equivale a ser un valor. -/
theorem rationalImageByGraph_mem_iff_pair_manual
    (Q E G : ZFSet.{u})
    (hG : IsFuncFoundational Q E G) (y : ZFSet.{u}) :
    y ∈ RationalImageByGraphManual Q E G ↔
      ∃ q : ZFSet.{u}, q ∈ Q ∧ ZFSet.pair q y ∈ G := by
  constructor
  · intro hy
    exact ((mem_rationalImageByGraph_iff_manual Q E G y).mp hy).2
  · rintro ⟨q, hq, hqy⟩
    exact rationalImageByGraph_mem_of_pair_manual Q E G hG q y hq hqy

/-- Comparación fundacional: ambos constructores de imagen coinciden siempre
    que G sea una función conjuntista y cada valor de ι figure en ese grafo. -/
theorem rationalImageByGraph_eq_function_manual
    (Q E G : ZFSet.{u}) (ι : ZFSet.{u} → ZFSet.{u})
    (hG : IsFuncFoundational Q E G)
    (hGraph : ∀ q : ZFSet.{u}, q ∈ Q → ZFSet.pair q (ι q) ∈ G) :
    RationalImageByGraphManual Q E G = RationalImageManual Q E ι := by
  apply ZFSet.ext
  intro y
  constructor
  · intro hy
    rcases (mem_rationalImageByGraph_iff_manual Q E G y).mp hy with
      ⟨hyE, q, hq, hqy⟩
    have hiE : ι q ∈ E := funcFoundational_value_mem hG (hGraph q hq)
    rcases hG.2 q hq with ⟨b, _hb, hunique⟩
    have hyb : y = b := hunique y ⟨hyE, hqy⟩
    have hib : ι q = b := hunique (ι q) ⟨hiE, hGraph q hq⟩
    exact ZFSet.mem_sep.mpr ⟨hyE, q, hq, hib.trans hyb.symm⟩
  · intro hy
    rcases (ZFSet.mem_sep.mp hy) with ⟨hyE, q, hq, heq⟩
    apply (mem_rationalImageByGraph_iff_manual Q E G y).mpr
    refine ⟨hyE, q, hq, ?_⟩
    exact heq ▸ hGraph q hq

/-- La parte de función conjuntista incluida en TA-DEF-00077 se recupera
    sin Choice y sin crear un selector sobre Q. -/
theorem embedding_graph_isFunc_manual
    (Q E zeroQ oneQ zeroE oneE : ZFSet.{u})
    (addQ mulQ addE mulE : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (leQ leE : ZFSet.{u} → ZFSet.{u} → Prop)
    (ι : ZFSet.{u} → ZFSet.{u}) (G f : ZFSet.{u})
    (hemb : IsOrderedFieldEmbeddingFoundational
      Q E zeroQ oneQ zeroE oneE addQ mulQ addE mulE leQ leE ι G f) :
    IsFuncFoundational Q E G := by
  rcases hemb with ⟨_, _, hfg, htriple, _, _, _, _, _, _, _⟩
  rw [hfg] at htriple
  exact TA_DEF_00018_functionTriple_iff.mp htriple

/-- TA-DEF-00077 garantiza que la imagen ZFSet por G es exactamente la
    imagen auxiliar por ι. No se añade ninguna hipótesis sobre G. -/
theorem rationalImageByGraph_eq_of_embedding_manual
    (Q E zeroQ oneQ zeroE oneE : ZFSet.{u})
    (addQ mulQ addE mulE : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (leQ leE : ZFSet.{u} → ZFSet.{u} → Prop)
    (ι : ZFSet.{u} → ZFSet.{u}) (G f : ZFSet.{u})
    (hemb : IsOrderedFieldEmbeddingFoundational
      Q E zeroQ oneQ zeroE oneE addQ mulQ addE mulE leQ leE ι G f) :
    RationalImageByGraphManual Q E G = RationalImageManual Q E ι := by
  have hG : IsFuncFoundational Q E G :=
    embedding_graph_isFunc_manual Q E zeroQ oneQ zeroE oneE
      addQ mulQ addE mulE leQ leE ι G f hemb
  rcases hemb with ⟨_, _, _, _, hGraph, _, _, _, _, _, _⟩
  exact rationalImageByGraph_eq_function_manual Q E G ι hG hGraph

/-- Toda imagen de un racional por la incrustación pertenece al conjunto
    definido por G, usando el contrato completo de TA-DEF-00077. -/
theorem rationalImageByGraph_mem_of_embedding_manual
    (Q E zeroQ oneQ zeroE oneE : ZFSet.{u})
    (addQ mulQ addE mulE : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (leQ leE : ZFSet.{u} → ZFSet.{u} → Prop)
    (ι : ZFSet.{u} → ZFSet.{u}) (G f : ZFSet.{u})
    (hemb : IsOrderedFieldEmbeddingFoundational
      Q E zeroQ oneQ zeroE oneE addQ mulQ addE mulE leQ leE ι G f)
    (q : ZFSet.{u}) (hq : q ∈ Q) :
    ι q ∈ RationalImageByGraphManual Q E G := by
  have hG : IsFuncFoundational Q E G :=
    embedding_graph_isFunc_manual Q E zeroQ oneQ zeroE oneE
      addQ mulQ addE mulE leQ leE ι G f hemb
  rcases hemb with ⟨_, _, _, _, hGraph, _, _, _, _, _, _⟩
  exact rationalImageByGraph_mem_of_pair_manual Q E G
    hG q (ι q) hq (hGraph q hq)


/-- Cotejo punto a punto: en el dominio Q, el grafo G contiene
    exactamente los pares (q, ι(q)). Esta es la igualdad relacional
    necesaria para que ι no flote libre respecto del grafo. -/
theorem embedding_graph_pair_iff_manual
    (Q E zeroQ oneQ zeroE oneE : ZFSet.{u})
    (addQ mulQ addE mulE : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (leQ leE : ZFSet.{u} → ZFSet.{u} → Prop)
    (ι : ZFSet.{u} → ZFSet.{u}) (G f : ZFSet.{u})
    (hemb : IsOrderedFieldEmbeddingFoundational
      Q E zeroQ oneQ zeroE oneE addQ mulQ addE mulE leQ leE ι G f)
    (q y : ZFSet.{u}) (hq : q ∈ Q) :
    ZFSet.pair q y ∈ G ↔ ι q = y := by
  have hG : IsFuncFoundational Q E G :=
    embedding_graph_isFunc_manual Q E zeroQ oneQ zeroE oneE
      addQ mulQ addE mulE leQ leE ι G f hemb
  rcases hemb with ⟨_, _, _, _, hGraph, _, _, _, _, _, _⟩
  constructor
  · intro hqy
    have hyE : y ∈ E := funcFoundational_value_mem hG hqy
    have hiE : ι q ∈ E := funcFoundational_value_mem hG (hGraph q hq)
    rcases hG.2 q hq with ⟨b, _hb, hunique⟩
    exact (hunique (ι q) ⟨hiE, hGraph q hq⟩).trans
      (hunique y ⟨hyE, hqy⟩).symm
  · intro heq
    exact heq ▸ hGraph q hq

end TratadoAnalisis.AbstractCompleteness.Density0009
