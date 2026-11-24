import TratadoAnalisis.Abstract.PrimeSubfieldConstruction0009

/-!
# TA-LEAN-0009 — P3c-01: numerales en el subcuerpo primo y cofinalidad

ETAPA EXPERIMENTAL. La fuente se entrega como candidato para Lean 4.32.1.

TA-COR-00011: todo valor de la aplicación canónica de numerales, definida
mediante un grafo funcional ZFSet sobre omegaTA, pertenece al subcuerpo primo
construido por Potencia/Separación en P3b.

Como consecuencia, TA-DEF-00073 aporta cofinalidad superior del subcuerpo
primo. TA-THM-00037 permite obtenerla desde completitud.

No se afirma TA-THM-00036: la cofinalidad superior NO es densidad.
No se asume una función de numerales del metalenguaje ni se usa Choice.
-/

namespace TratadoAnalisis.AbstractCompleteness.Density0009

universe u

open TratadoAnalisis.AbstractCompleteness.Manual0008
open TratadoAnalisis.Dedekind.FieldPredicates
open TratadoAnalisis.Naturals.Foundational
open TratadoAnalisis.Naturals.Recursion

/-- Cada subcuerpo K contiene algún valor del grafo canónico de numerales
    en cada índice natural. La prueba usa la inducción de omegaTA y la
    clausura relacional de K bajo suma; no escoge una función de valores. -/
theorem numeralGraph_value_in_any_subfield_manual
    (E K zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (hK : IsSubfieldRelationalManual E K zero one add mul)
    (n : ZFSet.{u}) (hn : n ∈ omegaTA) :
    ∃ y : ZFSet.{u}, y ∈ K ∧
      ZFSet.pair n y ∈ CanonicalNumeralGraphManual E zero one add := by
  rcases hK with ⟨hField, hSubset, hKzero, hKone, hKadd,
    _hKmul, _hKneg, _hKinv⟩
  have hEzero : zero ∈ E := hField.1.2.1
  have hEone : one ∈ E := hField.2.2.1
  have hAddTotal : IsBinaryOperationFoundational E add := hField.1.1
  let P : ZFSet.{u} → Prop := fun k =>
    ∃ y : ZFSet.{u}, y ∈ K ∧
      ZFSet.pair k y ∈ CanonicalNumeralGraphManual E zero one add
  have hbase : P (∅ : ZFSet.{u}) := by
    exact ⟨zero, hKzero,
      canonicalNumeralGraph_zero_manual E zero one add hEzero⟩
  have hstep : ∀ k : ZFSet.{u}, k ∈ omegaTA → P k →
      P (succ k) := by
    intro k hk hPk
    obtain ⟨x, hxK, hkx⟩ := hPk
    obtain ⟨y, hyK, hxy⟩ := hKadd x one hxK hKone
    have hxE : x ∈ E := hSubset hxK
    have hyE : y ∈ E := hSubset hyK
    exact ⟨y, hyK,
      canonicalNumeralGraph_succ_manual
        E zero one add hEzero hEone hAddTotal
        hk hkx hxE hyE hxy⟩
  exact TA_THM_00008_induction P hbase hstep n hn

/-- TA-COR-00011: el valor de un numeral canónico pertenece a P_E.
    Una vez fijado n, la funcionalidad del grafo identifica el valor
    de cada subcuerpo con el valor y; no se elige un representante. -/
theorem TA_COR_00011_numerals_in_prime_manual
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (hField : IsFieldFoundational E zero one add mul)
    (n y : ZFSet.{u}) (hn : n ∈ omegaTA)
    (hny : ZFSet.pair n y ∈
      CanonicalNumeralGraphManual E zero one add) :
    y ∈ PrimeSubfieldCoreManual E zero one add mul := by
  have hEzero : zero ∈ E := hField.1.2.1
  have hEone : one ∈ E := hField.2.2.1
  have hAddTotal : IsBinaryOperationFoundational E add := hField.1.1
  have hFunc : IsFuncFoundational omegaTA E
      (CanonicalNumeralGraphManual E zero one add) :=
    canonicalNumeralGraph_isFunc_manual
      E zero one add hEzero hEone hAddTotal
  apply (mem_primeSubfieldCore_iff_manual E y zero one add mul).mpr
  refine ⟨funcFoundational_value_mem hFunc hny, ?_⟩
  intro K hK
  obtain ⟨z, hzK, hnz⟩ :=
    numeralGraph_value_in_any_subfield_manual E K zero one
      add mul hK n hn
  have hyz : y = z :=
    funcFoundational_pair_value_unique hFunc hn hny hnz
  simpa only [hyz] using hzK

/-- Forma conjuntista de TA-COR-00011: toda la imagen de numerales
    obtenida por Separación está contenida en el subcuerpo primo. -/
theorem numeralGraphImage_subset_prime_manual
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (hField : IsFieldFoundational E zero one add mul) :
    NumeralGraphImageManual E
      (CanonicalNumeralGraphManual E zero one add) ⊆
      PrimeSubfieldCoreManual E zero one add mul := by
  intro y hy
  rcases (mem_numeralGraphImage_iff_manual E
    (CanonicalNumeralGraphManual E zero one add) y).mp hy with
    ⟨_hyE, n, hn, hny⟩
  exact TA_COR_00011_numerals_in_prime_manual
    E zero one add mul hField n y hn hny

/-- Consecuencia propia de TA-DEF-00073: P_E es cofinal superiormente.
    No se introducen recíprocos, enteros, mínimas cotas ni hipótesis de
    densidad; se transporta un testigo del grafo canónico a P_E. -/
theorem primeSubfield_cofinal_of_archimedean_manual
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hField : IsFieldFoundational E zero one add mul)
    (hArch : IsArchimedeanGraphEditorialManual E zero one add le)
    (x : ZFSet.{u}) (hxE : x ∈ E) :
    ∃ y : ZFSet.{u},
      y ∈ PrimeSubfieldCoreManual E zero one add mul ∧
      StrictFromLeManual le x y := by
  obtain ⟨n, hn, y, hny, hxy⟩ := hArch x hxE
  exact ⟨y,
    TA_COR_00011_numerals_in_prime_manual E zero one
      add mul hField n y hn hny,
    hxy⟩

/-- Aplicación directa de TA-THM-00037: el subcuerpo primo de un cuerpo
    ordenado completo es cofinal. `em` permanece hipótesis explícita.
    IMPORTANTE: esta conclusión es más débil que TA-THM-00036. -/
theorem primeSubfield_cofinal_of_complete_manual
    (em : ∀ p : Prop, p ∨ ¬p)
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hComplete : IsCompleteOrderedFieldFoundational E zero one add mul le)
    (x : ZFSet.{u}) (hxE : x ∈ E) :
    ∃ y : ZFSet.{u},
      y ∈ PrimeSubfieldCoreManual E zero one add mul ∧
      StrictFromLeManual le x y := by
  have hArch : IsArchimedeanGraphEditorialManual E zero one add le :=
    TA_THM_00037_archimedean_editorial_manual
      em E zero one add mul le hComplete
  exact primeSubfield_cofinal_of_archimedean_manual
    E zero one add mul le hComplete.1.1 hArch x hxE

end TratadoAnalisis.AbstractCompleteness.Density0009
