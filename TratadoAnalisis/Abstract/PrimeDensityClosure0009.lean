import TratadoAnalisis.Abstract.PrimeShiftedGrid0009

/-!
# TA-LEAN-0009 / P3c-10 — densidad del subcuerpo primo y de la imagen racional

La prueba combina la malla trasladada de P3c-09 con la cota del
sucesor de P3c-08. El resultado es incondicional respecto de la
densidad: solo se presupone un cuerpo ordenado arquimediano (o bien
uno completo en la aplicacion TA-PRO-00078).

Todas las operaciones son relaciones sobre ZFSet. El indice natural
se interpreta mediante el grafo canonico de numerales. El tercero
excluido se recibe como parametro `em`; no se aplica eleccion global.

CANDIDATO EXPERIMENTAL, sujeto a compilacion y auditoria de Lean.
-/

namespace TratadoAnalisis.AbstractCompleteness.Density0009

universe u

open TratadoAnalisis.AbstractCompleteness.Manual0008
open TratadoAnalisis.Dedekind.FieldPredicates
open TratadoAnalisis.Naturals.Foundational
open TratadoAnalisis.Naturals.Recursion

/-- Trasladar a p el paso de un producto por numerales consecutivos.
    El testigo relacional r0+d coincide con p+q1 por asociatividad y
    unicidad. No se emplean funciones globales de suma o producto. -/
theorem prime_shifted_successor_step_manual
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hordered : IsOrderedFieldFoundational E zero one add mul le)
    (k a b p d q0 q1 r0 r1 : ZFSet.{u})
    (hk : k ∈ omegaTA)
    (hKA : ZFSet.pair k a ∈ CanonicalNumeralGraphManual E zero one add)
    (hSB : ZFSet.pair (succ k) b ∈ CanonicalNumeralGraphManual E zero one add)
    (hpPrime : p ∈ PrimeSubfieldCoreManual E zero one add mul)
    (hdPrime : d ∈ PrimeSubfieldCoreManual E zero one add mul)
    (hq0Prime : q0 ∈ PrimeSubfieldCoreManual E zero one add mul)
    (_hq1Prime : q1 ∈ PrimeSubfieldCoreManual E zero one add mul)
    (hr0Prime : r0 ∈ PrimeSubfieldCoreManual E zero one add mul)
    (_hr1Prime : r1 ∈ PrimeSubfieldCoreManual E zero one add mul)
    (hADQ0 : mul a d q0) (hBDQ1 : mul b d q1)
    (hPq0r0 : add p q0 r0) (hPq1r1 : add p q1 r1) :
    add r0 d r1 := by
  have hPrime : IsSubfieldRelationalManual E
      (PrimeSubfieldCoreManual E zero one add mul) zero one add mul :=
    primeSubfieldCore_isSubfield_manual E zero one add mul hordered.1
  rcases hPrime with ⟨_, hSub, _, _, hAddPrime, _, _, _⟩
  have hpE : p ∈ E := hSub hpPrime
  have hdE : d ∈ E := hSub hdPrime
  have hq0E : q0 ∈ E := hSub hq0Prime
  have hr0E : r0 ∈ E := hSub hr0Prime
  obtain ⟨s, _hsPrime, hQ0DS⟩ :=
    hAddPrime q0 d hq0Prime hdPrime
  have hQ1S : q1 = s :=
    prime_grid_successor_product_eq_manual
      E zero one add mul le hordered
      k a b d q0 q1 s hk hKA hSB hdE hADQ0 hBDQ1 hQ0DS
  have hQ0DQ1 : add q0 d q1 := by
    simpa only [← hQ1S] using hQ0DS
  rcases hordered.1.1 with ⟨hAddTotal, _, hAddAssoc, _, _, _⟩
  obtain ⟨t, ⟨_htE, hR0DT⟩, _⟩ := hAddTotal r0 hr0E d hdE
  have hTR1 : t = r1 :=
    hAddAssoc p q0 d r0 t q1 r1
      hpE hq0E hdE hPq0r0 hR0DT hQ0DQ1 hPq1r1
  simpa only [hTR1] using hR0DT

/-- El primer punto de una malla trasladada que supera x es menor
    que x+epsilon cuando el paso d es menor que epsilon. La existencia
    del primer cruce se recibe de P3c-09; aqui no se presupone densidad. -/
theorem prime_shifted_first_crossing_in_interval_manual
    (em : ∀ p : Prop, p ∨ ¬p)
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hordered : IsOrderedFieldFoundational E zero one add mul le)
    (p d epsilon k x y : ZFSet.{u})
    (hk : k ∈ omegaTA)
    (hpPrime : p ∈ PrimeSubfieldCoreManual E zero one add mul)
    (hdPrime : d ∈ PrimeSubfieldCoreManual E zero one add mul)
    (hxE : x ∈ E) (hyE : y ∈ E) (hepsilonE : epsilon ∈ E)
    (hdSmall : StrictFromLeManual le d epsilon)
    (hXepsY : add x epsilon y)
    (hCross : ShiftedGridCrossingManual E zero one add mul le
      p d x (succ k))
    (hNotCross : ¬ ShiftedGridCrossingManual E zero one add mul le
      p d x k) :
    ∃ r : ZFSet.{u},
      r ∈ PrimeSubfieldCoreManual E zero one add mul ∧
      StrictFromLeManual le x r ∧ StrictFromLeManual le r y := by
  obtain ⟨b, q1, r1, hSB, hq1Prime, hr1Prime,
    hBDQ1, hPq1r1, hxR1⟩ := hCross
  have hPrime : IsSubfieldRelationalManual E
      (PrimeSubfieldCoreManual E zero one add mul) zero one add mul :=
    primeSubfieldCore_isSubfield_manual E zero one add mul hordered.1
  rcases hPrime with ⟨_, hSub, _, _, hAddPrime, hMulPrime, _, _⟩
  have hdE : d ∈ E := hSub hdPrime
  have hr1E : r1 ∈ E := hSub hr1Prime
  have hFunc : IsFuncFoundational omegaTA E
      (CanonicalNumeralGraphManual E zero one add) :=
    canonicalNumeralGraph_isFunc_manual
      E zero one add
      hordered.1.1.2.1 hordered.1.2.2.1 hordered.1.1.1
  obtain ⟨a, ⟨_haE, hKA⟩, _⟩ := hFunc.2 k hk
  have haPrime : a ∈ PrimeSubfieldCoreManual E zero one add mul :=
    TA_COR_00011_numerals_in_prime_manual
      E zero one add mul hordered.1 k a hk hKA
  obtain ⟨q0, hq0Prime, hADQ0⟩ :=
    hMulPrime a d haPrime hdPrime
  obtain ⟨r0, hr0Prime, hPq0r0⟩ :=
    hAddPrime p q0 hpPrime hq0Prime
  have hr0E : r0 ∈ E := hSub hr0Prime
  have hNotAbove : ¬StrictFromLeManual le x r0 := by
    intro hxR0
    exact hNotCross ⟨a, q0, r0, hKA, hq0Prime, hr0Prime,
      hADQ0, hPq0r0, hxR0⟩
  have hR0DR1 : add r0 d r1 :=
    prime_shifted_successor_step_manual
      E zero one add mul le hordered
      k a b p d q0 q1 r0 r1 hk hKA hSB hpPrime hdPrime
      hq0Prime hq1Prime hr0Prime hr1Prime
      hADQ0 hBDQ1 hPq0r0 hPq1r1
  have hr1Y : StrictFromLeManual le r1 y :=
    prime_grid_step_upper_bound_manual
      em E zero one add mul le hordered
      x epsilon r0 d r1 y hxE hepsilonE hr0E hdE hr1E hyE
      hNotAbove hdSmall hR0DR1 hXepsY
  exact ⟨r1, hr1Prime, hxR1, hr1Y⟩

/-- TA-THM-00036: el subcuerpo primo de todo cuerpo ordenado
    arquimediano es denso, sin suponer la densidad en las hipotesis. -/
theorem TA_THM_00036_prime_dense_archimedean_manual
    (em : ∀ p : Prop, p ∨ ¬p)
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hordered : IsOrderedFieldFoundational E zero one add mul le)
    (hArch : IsArchimedeanGraphEditorialManual E zero one add le) :
    IsOrderDenseSubsetManual E
      (PrimeSubfieldCoreManual E zero one add mul) le := by
  have hPrime : IsSubfieldRelationalManual E
      (PrimeSubfieldCoreManual E zero one add mul) zero one add mul :=
    primeSubfieldCore_isSubfield_manual E zero one add mul hordered.1
  refine ⟨hPrime.2.1, ?_⟩
  intro x y hxE hyE hxy
  obtain ⟨p, d, epsilon, k, hpPrime, hdPrime, _hpX, _hdPos,
      hepsilonE, hdSmall, hXepsY, hk, hCross, hNotCross⟩ :=
    prime_shifted_small_mesh_successor_manual
      em E zero one add mul le hordered hArch x y hxE hyE hxy
  exact prime_shifted_first_crossing_in_interval_manual
    em E zero one add mul le hordered
    p d epsilon k x y hk hpPrime hdPrime
    hxE hyE hepsilonE hdSmall hXepsY hCross hNotCross

/-- Variante de TA-THM-00036 para cuerpos ordenados completos;
    la arquimedianidad procede de TA-THM-00037. -/
theorem TA_THM_00036_prime_dense_complete_manual
    (em : ∀ p : Prop, p ∨ ¬p)
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hComplete : IsCompleteOrderedFieldFoundational E zero one add mul le) :
    IsOrderDenseSubsetManual E
      (PrimeSubfieldCoreManual E zero one add mul) le := by
  have hArch : IsArchimedeanGraphEditorialManual E zero one add le :=
    TA_THM_00037_archimedean_editorial_manual
      em E zero one add mul le hComplete
  exact TA_THM_00036_prime_dense_archimedean_manual
    em E zero one add mul le hComplete.1 hArch

/-- TA-PRO-00078: en una completacion ordenada, para x<y existe
    q del dominio cuya imagen por la incrustacion esta entre ambos.
    El subcuerpo primo es el construido por interseccion de ZFSet. -/
theorem TA_PRO_00078_rational_between_graph_manual
    (em : ∀ p : Prop, p ∨ ¬p)
    (Q E zeroQ oneQ zeroE oneE : ZFSet.{u})
    (addQ mulQ addE mulE : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (leQ leE : ZFSet.{u} → ZFSet.{u} → Prop)
    (ι : ZFSet.{u} → ZFSet.{u}) (G f : ZFSet.{u})
    (hComplete : IsCompleteOrderedFieldFoundational E zeroE oneE addE mulE leE)
    (hemb : IsOrderedFieldEmbeddingFoundational
      Q E zeroQ oneQ zeroE oneE addQ mulQ addE mulE leQ leE ι G f)
    (x y : ZFSet.{u}) (hxE : x ∈ E) (hyE : y ∈ E)
    (hxy : StrictFromLeManual leE x y) :
    ∃ q : ZFSet.{u}, q ∈ Q ∧
      StrictFromLeManual leE x (ι q) ∧
      StrictFromLeManual leE (ι q) y := by
  have hDensePrime : IsArchimedeanGraphEditorialManual
        E zeroE oneE addE leE →
      IsOrderDenseSubsetManual E
        (PrimeSubfieldCoreManual E zeroE oneE addE mulE) leE := by
    intro hArch
    exact TA_THM_00036_prime_dense_archimedean_manual
      em E zeroE oneE addE mulE leE hComplete.1 hArch
  exact TA_PRO_00078_reduction_with_constructed_prime_manual
    em Q E zeroQ oneQ zeroE oneE addQ mulQ addE mulE leQ leE
    ι G f hComplete hemb hDensePrime x y hxE hyE hxy

/-- Formulacion primaria por G: entre dos elementos de E existe
    un par (q,z) del grafo conjuntista de la incrustacion con x<z<y. -/
theorem TA_PRO_00078_rational_graph_witness_manual
    (em : ∀ p : Prop, p ∨ ¬p)
    (Q E zeroQ oneQ zeroE oneE : ZFSet.{u})
    (addQ mulQ addE mulE : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (leQ leE : ZFSet.{u} → ZFSet.{u} → Prop)
    (ι : ZFSet.{u} → ZFSet.{u}) (G f : ZFSet.{u})
    (hComplete : IsCompleteOrderedFieldFoundational E zeroE oneE addE mulE leE)
    (hemb : IsOrderedFieldEmbeddingFoundational
      Q E zeroQ oneQ zeroE oneE addQ mulQ addE mulE leQ leE ι G f)
    (x y : ZFSet.{u}) (hxE : x ∈ E) (hyE : y ∈ E)
    (hxy : StrictFromLeManual leE x y) :
    ∃ q z : ZFSet.{u}, q ∈ Q ∧ z ∈ E ∧
      ZFSet.pair q z ∈ G ∧
      StrictFromLeManual leE x z ∧ StrictFromLeManual leE z y := by
  obtain ⟨q, hq, hxq, hqy⟩ :=
    TA_PRO_00078_rational_between_graph_manual
      em Q E zeroQ oneQ zeroE oneE addQ mulQ addE mulE leQ leE
      ι G f hComplete hemb x y hxE hyE hxy
  have hGraph : ∀ q : ZFSet.{u}, q ∈ Q → ZFSet.pair q (ι q) ∈ G := by
    rcases hemb with ⟨_, _, _, _, hmap, _, _, _, _, _, _⟩
    exact hmap
  have hFunc : IsFuncFoundational Q E G :=
    embedding_graph_isFunc_manual
      Q E zeroQ oneQ zeroE oneE addQ mulQ addE mulE leQ leE
      ι G f hemb
  have hPair : ZFSet.pair q (ι q) ∈ G := hGraph q hq
  have hImageE : ι q ∈ E := funcFoundational_value_mem hFunc hPair
  exact ⟨q, ι q, hq, hImageE, hPair, hxq, hqy⟩

end TratadoAnalisis.AbstractCompleteness.Density0009
