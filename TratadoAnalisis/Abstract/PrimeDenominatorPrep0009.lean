import TratadoAnalisis.Abstract.PrimeNumeralCofinality0009

/-!
# TA-LEAN-0009 / P3c-02 — denominadores naturales e intervalo bilateral

Esta etapa prepara la prueba de TA-THM-00036 sin presuponer su resultado.

1. Desde una cota r ≥ 0, la arquimedianidad aporta un numeral y > r,
   que pertenece al subcuerpo primo y es estrictamente positivo.
2. La clausura del subcuerpo primo da el inverso bilateral de y *dentro*
   del subcuerpo primo, sin seleccionar una función global de inversos.
3. La cofinalidad superior implica la inferior usando opuestos aditivos
   locales, antitonia del opuesto y unicidad algebraica del inverso aditivo.

NO se demuestra todavía que el inverso de y sea positivo ni menor que
un epsilon dado. Esa comparación requiere las reglas de orden de inversos
(TA-LEM-00020(6)/(7)) en un cuerpo ordenado abstracto.
No se afirma TA-THM-00036 ni TA-PRO-00078 incondicionalmente.
-/

namespace TratadoAnalisis.AbstractCompleteness.Density0009

universe u

open TratadoAnalisis.AbstractCompleteness.Manual0008
open TratadoAnalisis.Dedekind.FieldPredicates
open TratadoAnalisis.Naturals.Foundational
open TratadoAnalisis.Naturals.Recursion

/-- Dada una cota r no negativa, existe un numeral del grafo canonico
    mayor que r; esta en el subcuerpo primo y es estrictamente positivo. -/
theorem prime_numeral_above_nonnegative_manual
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hordered : IsOrderedFieldFoundational E zero one add mul le)
    (hArch : IsArchimedeanGraphEditorialManual E zero one add le)
    (r : ZFSet.{u}) (hrE : r ∈ E) (hzeroLeR : le zero r) :
    ∃ n y : ZFSet.{u},
      n ∈ omegaTA ∧
      ZFSet.pair n y ∈ CanonicalNumeralGraphManual E zero one add ∧
      y ∈ PrimeSubfieldCoreManual E zero one add mul ∧
      StrictFromLeManual le zero y ∧
      StrictFromLeManual le r y := by
  have hField : IsFieldFoundational E zero one add mul := hordered.1
  have hOrder : IsTotalOrderFoundational E le := hordered.2.1
  have hZeroE : zero ∈ E := hField.1.2.1
  have hOneE : one ∈ E := hField.2.2.1
  have hAddTotal : IsBinaryOperationFoundational E add := hField.1.1
  have hNumeralFunc : IsFuncFoundational omegaTA E
      (CanonicalNumeralGraphManual E zero one add) :=
    canonicalNumeralGraph_isFunc_manual E zero one add
      hZeroE hOneE hAddTotal
  obtain ⟨n, hn, y, hny, hry⟩ := hArch r hrE
  have hyE : y ∈ E := funcFoundational_value_mem hNumeralFunc hny
  have hyP : y ∈ PrimeSubfieldCoreManual E zero one add mul :=
    TA_COR_00011_numerals_in_prime_manual
      E zero one add mul hField n y hn hny
  have hZeroLeY : le zero y :=
    hOrder.2.2.1 zero r y hZeroE hrE hyE hzeroLeR hry.1
  have hZeroNeY : zero ≠ y := by
    intro hZeroEqY
    have hrLeZero : le r zero := by
      simpa only [hZeroEqY] using hry.1
    have hrEqZero : r = zero :=
      hOrder.2.1 r zero hrE hZeroE hrLeZero hzeroLeR
    exact hry.2 (hrEqZero.trans hZeroEqY)
  exact ⟨n, y, hn, hny, hyP,
    ⟨hZeroLeY, hZeroNeY⟩, hry⟩

/-- Un numeral suficientemente grande para superar r ≥ 0 posee
    un inverso bilateral que tambien pertenece al subcuerpo primo.
    Todavia NO se afirma la positividad ni el tamano de ese inverso. -/
theorem prime_positive_numeral_inverse_manual
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hordered : IsOrderedFieldFoundational E zero one add mul le)
    (hArch : IsArchimedeanGraphEditorialManual E zero one add le)
    (r : ZFSet.{u}) (hrE : r ∈ E) (hzeroLeR : le zero r) :
    ∃ n y iy : ZFSet.{u},
      n ∈ omegaTA ∧
      ZFSet.pair n y ∈ CanonicalNumeralGraphManual E zero one add ∧
      y ∈ PrimeSubfieldCoreManual E zero one add mul ∧
      iy ∈ PrimeSubfieldCoreManual E zero one add mul ∧
      StrictFromLeManual le zero y ∧
      StrictFromLeManual le r y ∧
      mul y iy one ∧ mul iy y one := by
  obtain ⟨n, y, hn, hny, hyP, hZeroY, hry⟩ :=
    prime_numeral_above_nonnegative_manual E zero one
      add mul le hordered hArch r hrE hzeroLeR
  have hField : IsFieldFoundational E zero one add mul := hordered.1
  have hP : IsSubfieldRelationalManual E
      (PrimeSubfieldCoreManual E zero one add mul) zero one add mul :=
    primeSubfieldCore_isSubfield_manual E zero one add mul hField
  rcases hP with ⟨_, _, _, _, _, _, _, hPInv⟩
  have hyNeZero : y ≠ zero := Ne.symm hZeroY.2
  obtain ⟨iy, hiyP, hyiy, hiyy⟩ := hPInv y hyP hyNeZero
  exact ⟨n, y, iy, hn, hny, hyP, hiyP, hZeroY, hry, hyiy, hiyy⟩

/-- Variante con completitud: la arquimedianidad se obtiene del
    TA-THM-00037 ya certificado; el tercero excluido es dato explicito. -/
theorem prime_positive_numeral_inverse_of_complete_manual
    (em : ∀ p : Prop, p ∨ ¬p)
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hComplete : IsCompleteOrderedFieldFoundational E zero one add mul le)
    (r : ZFSet.{u}) (hrE : r ∈ E) (hzeroLeR : le zero r) :
    ∃ n y iy : ZFSet.{u},
      n ∈ omegaTA ∧
      ZFSet.pair n y ∈ CanonicalNumeralGraphManual E zero one add ∧
      y ∈ PrimeSubfieldCoreManual E zero one add mul ∧
      iy ∈ PrimeSubfieldCoreManual E zero one add mul ∧
      StrictFromLeManual le zero y ∧
      StrictFromLeManual le r y ∧
      mul y iy one ∧ mul iy y one := by
  have hArch : IsArchimedeanGraphEditorialManual E zero one add le :=
    TA_THM_00037_archimedean_editorial_manual
      em E zero one add mul le hComplete
  exact prime_positive_numeral_inverse_manual
    E zero one add mul le hComplete.1 hArch r hrE hzeroLeR

/-- Cofinalidad inferior del primo: aplicar la cofinalidad superior al
    opuesto -x, tomar el opuesto del numeral obtenido y reflejar el orden.
    La desigualdad es estricta por unicidad de los inversos aditivos. -/
theorem primeSubfield_coinitial_of_archimedean_manual
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hordered : IsOrderedFieldFoundational E zero one add mul le)
    (hArch : IsArchimedeanGraphEditorialManual E zero one add le)
    (x : ZFSet.{u}) (hxE : x ∈ E) :
    ∃ q : ZFSet.{u},
      q ∈ PrimeSubfieldCoreManual E zero one add mul ∧
      StrictFromLeManual le q x := by
  have hField : IsFieldFoundational E zero one add mul := hordered.1
  have hGroup : IsAbelianGroupFoundational E zero add := hField.1
  rcases hGroup with ⟨_, _, hAssoc, _, hUnit, hNeg⟩
  obtain ⟨nx, hnxE, hxnxZero, hnxXZero⟩ := hNeg x hxE
  obtain ⟨p, hpP, hnxLessP⟩ :=
    primeSubfield_cofinal_of_archimedean_manual
      E zero one add mul le hField hArch nx hnxE
  have hP : IsSubfieldRelationalManual E
      (PrimeSubfieldCoreManual E zero one add mul) zero one add mul :=
    primeSubfieldCore_isSubfield_manual E zero one add mul hField
  rcases hP with ⟨_, hSub, _, _, _, _, hNegP, _⟩
  obtain ⟨np, hnpP, hpnpZero, hnpPZero⟩ := hNegP p hpP
  have hpE : p ∈ E := hSub hpP
  have hnpE : np ∈ E := hSub hnpP
  have hOppNx : IsAdditiveOpposite E zero add nx x :=
    ⟨hnxE, hxE, hnxXZero, hxnxZero⟩
  have hOppP : IsAdditiveOpposite E zero add p np :=
    ⟨hpE, hnpE, hpnpZero, hnpPZero⟩
  have hnpLeX : le np x :=
    opposite_reverses_le_manual E zero one add mul le
      nx p x np hordered hnxLessP.1 hOppNx hOppP
  have hnpNeX : np ≠ x := by
    intro hnpEqX
    have hxPZero : add x p zero := by
      simpa only [hnpEqX] using hnpPZero
    have hnxEqP : nx = p :=
      relational_inverse_unique_manual
        E zero x nx p add hAssoc hUnit
        hxE hnxE hpE hnxXZero hxPZero
    exact hnxLessP.2 hnxEqP
  exact ⟨np, hnpP, ⟨hnpLeX, hnpNeX⟩⟩

/-- Cofinalidad inferior desde completitud, con em explicito. -/
theorem primeSubfield_coinitial_of_complete_manual
    (em : ∀ p : Prop, p ∨ ¬p)
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hComplete : IsCompleteOrderedFieldFoundational E zero one add mul le)
    (x : ZFSet.{u}) (hxE : x ∈ E) :
    ∃ q : ZFSet.{u},
      q ∈ PrimeSubfieldCoreManual E zero one add mul ∧
      StrictFromLeManual le q x := by
  have hArch : IsArchimedeanGraphEditorialManual E zero one add le :=
    TA_THM_00037_archimedean_editorial_manual
      em E zero one add mul le hComplete
  exact primeSubfield_coinitial_of_archimedean_manual
    E zero one add mul le hComplete.1 hArch x hxE

/-- El primo es cofinal por ambos lados, sin afirmar densidad. -/
theorem primeSubfield_two_sided_cofinal_manual
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hordered : IsOrderedFieldFoundational E zero one add mul le)
    (hArch : IsArchimedeanGraphEditorialManual E zero one add le)
    (x : ZFSet.{u}) (hxE : x ∈ E) :
    ∃ lower upper : ZFSet.{u},
      lower ∈ PrimeSubfieldCoreManual E zero one add mul ∧
      upper ∈ PrimeSubfieldCoreManual E zero one add mul ∧
      StrictFromLeManual le lower x ∧
      StrictFromLeManual le x upper := by
  obtain ⟨lower, hLower, hLowerX⟩ :=
    primeSubfield_coinitial_of_archimedean_manual
      E zero one add mul le hordered hArch x hxE
  obtain ⟨upper, hUpper, hXUpper⟩ :=
    primeSubfield_cofinal_of_archimedean_manual
      E zero one add mul le hordered.1 hArch x hxE
  exact ⟨lower, upper, hLower, hUpper, hLowerX, hXUpper⟩

end TratadoAnalisis.AbstractCompleteness.Density0009
