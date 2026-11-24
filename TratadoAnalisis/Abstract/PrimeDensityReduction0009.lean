import TratadoAnalisis.Abstract.RationalImageSubfield0009

/-!
# TA-PRO-00078 — P3a: reducción de densidad al subcuerpo primo

Candidato experimental NO compilado aquí.

Especifica la densidad con el orden relacional y el predicado estricto
ya certificado en TA-LEAN-0008. Formaliza la conexión:

  completitud -> arquimedianidad (TA-THM-00037 ya certificado),
  arquimedianidad -> densidad del subcuerpo primo (OBLIGACIÓN PENDIENTE),
  minimalidad del subcuerpo primo (OBLIGACIÓN PENDIENTE),
  densidad del subcuerpo primo -> densidad de la imagen racional por grafo,
  densidad de esa imagen -> existencia del racional intermedio.

No introduce axiomas nuevos: los dos resultados aún no certificados
figuran como HIPÓTESIS explícitas, sin huecos de demostración.
No demuestra aún TA-THM-00036, TA-PRO-00070 ni TA-PRO-00078 sin hipótesis.
-/

namespace TratadoAnalisis.AbstractCompleteness.Density0009

universe u

open TratadoAnalisis.AbstractCompleteness.Manual0008
open TratadoAnalisis.Dedekind.FieldPredicates

/-- Densidad de un subconjunto K en un cuerpo E, con relación estricta
    derivada de su orden no estricto, siguiendo TA-DEF-00073 y §4.5. -/
def IsOrderDenseSubsetManual
    (E K : ZFSet.{u}) (leE : ZFSet.{u} → ZFSet.{u} → Prop) : Prop :=
  K ⊆ E ∧
  ∀ x y : ZFSet.{u}, x ∈ E → y ∈ E →
    StrictFromLeManual leE x y →
    ∃ z : ZFSet.{u}, z ∈ K ∧
      StrictFromLeManual leE x z ∧ StrictFromLeManual leE z y

/-- Interfaz explícita de TA-DEF-00070 y TA-PRO-00070:
    P es un subcuerpo contenido en todos los subcuerpos de E.
    Aquí no se pretende construir P por intersección conjuntista. -/
def IsPrimeSubfieldRelationalManual
    (E P zeroE oneE : ZFSet.{u})
    (addE mulE : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop) : Prop :=
  IsSubfieldRelationalManual E P zeroE oneE addE mulE ∧
    ∀ K : ZFSet.{u},
      IsSubfieldRelationalManual E K zeroE oneE addE mulE → P ⊆ K

/-- Una inclusión conserva la densidad hacia el subconjunto mayor. -/
theorem orderDense_mono_manual
    (E P K : ZFSet.{u})
    (leE : ZFSet.{u} → ZFSet.{u} → Prop)
    (hPK : P ⊆ K)
    (hKsubset : K ⊆ E)
    (hDenseP : IsOrderDenseSubsetManual E P leE) :
    IsOrderDenseSubsetManual E K leE := by
  refine ⟨hKsubset, ?_⟩
  intro x y hx hy hxy
  obtain ⟨z, hzP, hxz, hzy⟩ := hDenseP.2 x y hx hy hxy
  exact ⟨z, hPK hzP, hxz, hzy⟩

/-- Una especialización de la minimalidad definicional del subcuerpo primo. -/
theorem primeSubfield_subset_subfield_manual
    (E P K zeroE oneE : ZFSet.{u})
    (addE mulE : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (hPrime : IsPrimeSubfieldRelationalManual E P zeroE oneE addE mulE)
    (hK : IsSubfieldRelationalManual E K zeroE oneE addE mulE) :
    P ⊆ K :=
  hPrime.2 K hK

/-- El teorema P2 más minimalidad implica que la imagen racional
    contiene al subcuerpo primo. La CONCLUSIÓN usa solo el grafo G. -/
theorem primeSubfield_subset_rationalImageByGraph_manual
    (Q E P zeroQ oneQ zeroE oneE : ZFSet.{u})
    (addQ mulQ addE mulE : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (leQ leE : ZFSet.{u} → ZFSet.{u} → Prop)
    (ι : ZFSet.{u} → ZFSet.{u}) (G f : ZFSet.{u})
    (hemb : IsOrderedFieldEmbeddingFoundational
      Q E zeroQ oneQ zeroE oneE addQ mulQ addE mulE leQ leE ι G f)
    (hPrime : IsPrimeSubfieldRelationalManual E P zeroE oneE addE mulE) :
    P ⊆ RationalImageByGraphManual Q E G := by
  have hK : IsSubfieldRelationalManual E
      (RationalImageByGraphManual Q E G) zeroE oneE addE mulE :=
    rationalImageByGraph_isSubfield_manual
      Q E zeroQ oneQ zeroE oneE addQ mulQ addE mulE leQ leE ι G f hemb
  exact primeSubfield_subset_subfield_manual E P
    (RationalImageByGraphManual Q E G) zeroE oneE addE mulE hPrime hK

/-- La densidad del subcuerpo primo se transfiere al conjunto definido
    mediante el grafo conjuntista de la incrustación Q -> E. -/
theorem rationalImageByGraph_dense_of_prime_manual
    (Q E P zeroQ oneQ zeroE oneE : ZFSet.{u})
    (addQ mulQ addE mulE : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (leQ leE : ZFSet.{u} → ZFSet.{u} → Prop)
    (ι : ZFSet.{u} → ZFSet.{u}) (G f : ZFSet.{u})
    (hemb : IsOrderedFieldEmbeddingFoundational
      Q E zeroQ oneQ zeroE oneE addQ mulQ addE mulE leQ leE ι G f)
    (hPrime : IsPrimeSubfieldRelationalManual E P zeroE oneE addE mulE)
    (hDenseP : IsOrderDenseSubsetManual E P leE) :
    IsOrderDenseSubsetManual E (RationalImageByGraphManual Q E G) leE := by
  have hPK : P ⊆ RationalImageByGraphManual Q E G :=
    primeSubfield_subset_rationalImageByGraph_manual
      Q E P zeroQ oneQ zeroE oneE addQ mulQ addE mulE leQ leE
      ι G f hemb hPrime
  have hKsubset : RationalImageByGraphManual Q E G ⊆ E :=
    rationalImageByGraph_subset_manual Q E G
  exact orderDense_mono_manual E P
    (RationalImageByGraphManual Q E G) leE hPK hKsubset hDenseP

/-- Extrae el racional concreto de la imagen por G, sin tratar
    la función auxiliar ι como definición primaria de la imagen. -/
theorem rational_between_of_dense_graphImage_manual
    (Q E zeroQ oneQ zeroE oneE : ZFSet.{u})
    (addQ mulQ addE mulE : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (leQ leE : ZFSet.{u} → ZFSet.{u} → Prop)
    (ι : ZFSet.{u} → ZFSet.{u}) (G f : ZFSet.{u})
    (hemb : IsOrderedFieldEmbeddingFoundational
      Q E zeroQ oneQ zeroE oneE addQ mulQ addE mulE leQ leE ι G f)
    (hDenseImage : IsOrderDenseSubsetManual E
      (RationalImageByGraphManual Q E G) leE)
    (x y : ZFSet.{u}) (hxE : x ∈ E) (hyE : y ∈ E)
    (hxy : StrictFromLeManual leE x y) :
    ∃ q : ZFSet.{u}, q ∈ Q ∧
      StrictFromLeManual leE x (ι q) ∧
      StrictFromLeManual leE (ι q) y := by
  obtain ⟨z, hzK, hxz, hzy⟩ := hDenseImage.2 x y hxE hyE hxy
  obtain ⟨_, q, hq, hqz⟩ :=
    (mem_rationalImageByGraph_iff_manual Q E G z).mp hzK
  have hiq : ι q = z :=
    (embedding_graph_pair_iff_manual
      Q E zeroQ oneQ zeroE oneE addQ mulQ addE mulE leQ leE
      ι G f hemb q z hq).mp hqz
  refine ⟨q, hq, ?_, ?_⟩
  · simpa only [hiq] using hxz
  · simpa only [hiq] using hzy

/-- REDUCCIÓN CONDICIONAL de TA-PRO-00078.
    Se utiliza TA-THM-00037 para deducir arquimedianidad, pero la
    minimalidad del subcuerpo primo y TA-THM-00036 figuran explícitamente
    como hipótesis todavía NO certificadas en esta etapa.

    Este teorema NO certifica por sí solo la densidad de completaciones. -/
theorem TA_PRO_00078_reduction_manual
    (em : ∀ p : Prop, p ∨ ¬p)
    (Q E P zeroQ oneQ zeroE oneE : ZFSet.{u})
    (addQ mulQ addE mulE : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (leQ leE : ZFSet.{u} → ZFSet.{u} → Prop)
    (ι : ZFSet.{u} → ZFSet.{u}) (G f : ZFSet.{u})
    (hComplete : IsCompleteOrderedFieldFoundational E zeroE oneE addE mulE leE)
    (hemb : IsOrderedFieldEmbeddingFoundational
      Q E zeroQ oneQ zeroE oneE addQ mulQ addE mulE leQ leE ι G f)
    (hPrime : IsPrimeSubfieldRelationalManual E P zeroE oneE addE mulE)
    (hArchPrimeDense :
      IsArchimedeanGraphEditorialManual E zeroE oneE addE leE →
      IsOrderDenseSubsetManual E P leE)
    (x y : ZFSet.{u}) (hxE : x ∈ E) (hyE : y ∈ E)
    (hxy : StrictFromLeManual leE x y) :
    ∃ q : ZFSet.{u}, q ∈ Q ∧
      StrictFromLeManual leE x (ι q) ∧
      StrictFromLeManual leE (ι q) y := by
  have hArch : IsArchimedeanGraphEditorialManual E zeroE oneE addE leE :=
    TA_THM_00037_archimedean_editorial_manual
      em E zeroE oneE addE mulE leE hComplete
  have hDensePrime : IsOrderDenseSubsetManual E P leE :=
    hArchPrimeDense hArch
  have hDenseImage : IsOrderDenseSubsetManual E
      (RationalImageByGraphManual Q E G) leE :=
    rationalImageByGraph_dense_of_prime_manual
      Q E P zeroQ oneQ zeroE oneE addQ mulQ addE mulE leQ leE
      ι G f hemb hPrime hDensePrime
  exact rational_between_of_dense_graphImage_manual
    Q E zeroQ oneQ zeroE oneE addQ mulQ addE mulE leQ leE
    ι G f hemb hDenseImage x y hxE hyE hxy

end TratadoAnalisis.AbstractCompleteness.Density0009
