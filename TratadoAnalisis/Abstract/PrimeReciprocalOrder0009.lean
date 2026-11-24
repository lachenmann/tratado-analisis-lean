import TratadoAnalisis.Abstract.PrimeInversePositivity0009

/-!
# TA-LEAN-0009 / P3c-04 — antitonia de inversos y reciprocos pequenos

Candidato experimental. La prueba no importa estructuras de cuerpo de Mathlib:
trabaja con las relaciones ternarias `add` y `mul`, operaciones locales
existenciales, desigualdades `StrictFromLeManual` y un unico universo.

1. Multiplicar por un factor no negativo preserva `le`; el resultado
   se deduce de la distributividad y de opuestos aditivos locales.
2. Para x,y positivos con x<y, los inversos bilaterales cumplen iy<ix.
3. Si E es arquimediano y epsilon>0, hay un numeral positivo y cuyo
   inverso iy pertenece al subcuerpo primo y cumple 0<iy<epsilon.
4. Variante de (3) para cuerpo ordenado completo, con `em` explicito.

NO se afirma aun la densidad del subcuerpo primo: resta el argumento
conjuntista de minimo natural para ubicar un elemento dentro de un intervalo.
-/

namespace TratadoAnalisis.AbstractCompleteness.Density0009

universe u

open TratadoAnalisis.AbstractCompleteness.Manual0008
open TratadoAnalisis.Dedekind.FieldPredicates
open TratadoAnalisis.Naturals.Foundational

/-- Monotonia multiplicativa por un factor derecho no negativo,
    derivada de la distributividad, el orden aditivo y opuestos locales.
    No se postula ninguna compatibilidad multiplicativa adicional. -/
theorem rel_mul_right_mono_nonnegative_manual
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hordered : IsOrderedFieldFoundational E zero one add mul le)
    (x y z xz yz : ZFSet.{u})
    (hxE : x ∈ E) (hyE : y ∈ E) (hzE : z ∈ E)
    (hxzE : xz ∈ E) (hyzE : yz ∈ E)
    (hxy : le x y) (hzNonneg : le zero z)
    (hXZ : mul x z xz) (hYZ : mul y z yz) :
    le xz yz := by
  have horderedCopy := hordered
  have hFieldCopy : IsFieldFoundational E zero one add mul := hordered.1
  rcases hordered with ⟨hField, _, hTranslate, hMulNonneg⟩
  rcases hField with
    ⟨hAddGroup, hMulTotal, _, _, hMulComm, _, hDistrib, _, _⟩
  rcases hAddGroup with
    ⟨hAddTotal, hzeroE, _, _, _, hNeg⟩
  obtain ⟨nx, hnxE, hxnxZero, hnxXZero⟩ := hNeg x hxE
  obtain ⟨d, ⟨hdE, hYNx⟩, _⟩ := hAddTotal y hyE nx hnxE
  have hzeroLeD : le zero d :=
    hTranslate x y nx zero d hxE hyE hnxE
      hxy hxnxZero hYNx
  obtain ⟨dz, ⟨hdzE, hDZ⟩, _⟩ := hMulTotal d hdE z hzE
  obtain ⟨nxz, ⟨hnxzE, hNxZ⟩, _⟩ := hMulTotal nx hnxE z hzE
  obtain ⟨s, ⟨_hsE, hYZ_NxZ⟩, _⟩ :=
    hAddTotal yz hyzE nxz hnxzE
  have hdzEqS : dz = s :=
    hDistrib.2 y nx z d dz yz nxz s hyE hnxE hzE
      hYNx hDZ hYZ hNxZ hYZ_NxZ
  have hYZ_NxZ_DZ : add yz nxz dz := by
    simpa only [← hdzEqS] using hYZ_NxZ
  have hzeroLeDZ : le zero dz :=
    hMulNonneg d z dz hdE hzE hzeroLeD hzNonneg hDZ
  obtain ⟨cx, ⟨_hcxE, hZX_CX⟩, _⟩ := hMulTotal z hzE x hxE
  have hxzEqCX : xz = cx :=
    hMulComm x z xz cx hxE hzE hXZ hZX_CX
  have hZX : mul z x xz := by
    simpa only [← hxzEqCX] using hZX_CX
  obtain ⟨cnx, ⟨_hcnxE, hZNx_CNx⟩, _⟩ :=
    hMulTotal z hzE nx hnxE
  have hnxzEqCNx : nxz = cnx :=
    hMulComm nx z nxz cnx hnxE hzE hNxZ hZNx_CNx
  have hZNx : mul z nx nxz := by
    simpa only [← hnxzEqCNx] using hZNx_CNx
  have hOppX : IsAdditiveOpposite E zero add x nx :=
    ⟨hxE, hnxE, hxnxZero, hnxXZero⟩
  have hOppXZ : IsAdditiveOpposite E zero add xz nxz :=
    rel_mul_opposite_right_manual E zero one add mul
      hFieldCopy z x nx xz nxz
      hzE hxE hnxE hxzE hnxzE hOppX hZX hZNx
  exact rel_add_reflect_le_manual E zero one add mul le
    xz yz nxz zero dz horderedCopy
    hxzE hyzE hnxzE hzeroE hdzE
    hOppXZ.2.2.1 hYZ_NxZ_DZ hzeroLeDZ

/-- La inversion revierte el orden estricto de positivos.
    Los inversos se expresan como testigos de relaciones bilaterales;
    no se supone una funcion global `inv`. -/
theorem rel_inverse_strict_antitone_manual
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hordered : IsOrderedFieldFoundational E zero one add mul le)
    (x y ix iy : ZFSet.{u})
    (hxE : x ∈ E) (hyE : y ∈ E)
    (hixE : ix ∈ E) (hiyE : iy ∈ E)
    (hxPos : StrictFromLeManual le zero x)
    (hyPos : StrictFromLeManual le zero y)
    (hxy : StrictFromLeManual le x y)
    (hxi : mul x ix one) (_hixx : mul ix x one)
    (hyiy : mul y iy one) (hiyy : mul iy y one) :
    StrictFromLeManual le iy ix := by
  have hixPos : StrictFromLeManual le zero ix :=
    rel_inverse_positive_manual E zero one add mul le hordered
      x ix hxE hixE hxPos hxi
  have hiyPos : StrictFromLeManual le zero iy :=
    rel_inverse_positive_manual E zero one add mul le hordered
      y iy hyE hiyE hyPos hyiy
  have hField : IsFieldFoundational E zero one add mul := hordered.1
  rcases hField with
    ⟨_, hMulTotal, honeE, hMulAssoc, hMulComm, hMulUnit, _, _, _⟩
  obtain ⟨t, ⟨htE, hXIY⟩, _⟩ := hMulTotal x hxE iy hiyE
  have htLeOne : le t one :=
    rel_mul_right_mono_nonnegative_manual
      E zero one add mul le hordered
      x y iy t one hxE hyE hiyE htE honeE
      hxy.1 hiyPos.1 hXIY hyiy
  obtain ⟨s, ⟨hsE, hTIX⟩, _⟩ := hMulTotal t htE ix hixE
  have hsLeIx : le s ix :=
    rel_mul_right_mono_nonnegative_manual
      E zero one add mul le hordered
      t one ix s ix htE honeE hixE hsE hixE
      htLeOne hixPos.1 hTIX (hMulUnit ix hixE).2
  obtain ⟨v, ⟨_hvE, hIYX_V⟩, _⟩ := hMulTotal iy hiyE x hxE
  have htEqV : t = v := hMulComm x iy t v hxE hiyE hXIY hIYX_V
  have hIYX : mul iy x t := by
    simpa only [← htEqV] using hIYX_V
  have hsEqIy : s = iy :=
    hMulAssoc iy x ix t s one iy hiyE hxE hixE
      hIYX hTIX hxi (hMulUnit iy hiyE).1
  have hIyLeIx : le iy ix := by
    simpa only [hsEqIy] using hsLeIx
  have hIyNeIx : iy ≠ ix := by
    intro hEq
    have hIxY : mul ix y one := by
      simpa only [hEq] using hiyy
    have hXeqY : x = y :=
      relational_inverse_unique_manual
        E one ix x y mul hMulAssoc hMulUnit
        hixE hxE hyE hxi hIxY
    exact hxy.2 hXeqY
  exact ⟨hIyLeIx, hIyNeIx⟩

/-- Para cada epsilon positivo, el inverso de algun numeral canonico
    positivo del subcuerpo primo pertenece al intervalo (0,epsilon).
    Esta cota NO usa ni presupone la densidad del subcuerpo primo. -/
theorem prime_numeral_inverse_below_positive_manual
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hordered : IsOrderedFieldFoundational E zero one add mul le)
    (hArch : IsArchimedeanGraphEditorialManual E zero one add le)
    (epsilon : ZFSet.{u})
    (hepsilonE : epsilon ∈ E)
    (hepsilonPos : StrictFromLeManual le zero epsilon) :
    ∃ n y iy : ZFSet.{u},
      n ∈ omegaTA ∧
      ZFSet.pair n y ∈ CanonicalNumeralGraphManual E zero one add ∧
      y ∈ PrimeSubfieldCoreManual E zero one add mul ∧
      iy ∈ PrimeSubfieldCoreManual E zero one add mul ∧
      StrictFromLeManual le zero y ∧
      StrictFromLeManual le zero iy ∧
      StrictFromLeManual le iy epsilon ∧
      mul y iy one ∧ mul iy y one := by
  have hField : IsFieldFoundational E zero one add mul := hordered.1
  have hParts := hField
  rcases hParts with ⟨_, _, _, _, _, _, _, _, hInv⟩
  obtain ⟨r, hrE, hEpsR, hREps⟩ :=
    hInv epsilon hepsilonE (Ne.symm hepsilonPos.2)
  have hrPos : StrictFromLeManual le zero r :=
    rel_inverse_positive_manual E zero one add mul le hordered
      epsilon r hepsilonE hrE hepsilonPos hEpsR
  obtain ⟨n, y, iy, hn, hGraph, hyPrime, hiyPrime,
      hyPos, hrLessY, hiyPos, hyiy, hiyy⟩ :=
    prime_positive_numeral_inverse_strict_manual
      E zero one add mul le hordered hArch r hrE hrPos.1
  have hPrime : IsSubfieldRelationalManual E
      (PrimeSubfieldCoreManual E zero one add mul) zero one add mul :=
    primeSubfieldCore_isSubfield_manual
      E zero one add mul hField
  have hyE : y ∈ E := hPrime.2.1 hyPrime
  have hiyE : iy ∈ E := hPrime.2.1 hiyPrime
  have hiyLtEpsilon : StrictFromLeManual le iy epsilon :=
    rel_inverse_strict_antitone_manual E zero one add mul le
      hordered r y epsilon iy hrE hyE hepsilonE hiyE
      hrPos hyPos hrLessY hREps hEpsR hyiy hiyy
  exact ⟨n, y, iy, hn, hGraph, hyPrime, hiyPrime,
    hyPos, hiyPos, hiyLtEpsilon, hyiy, hiyy⟩

/-- Variante con completitud; la arquimedianidad proviene de
    TA-THM-00037 con el tercero excluido como parametro expreso. -/
theorem prime_numeral_inverse_below_positive_of_complete_manual
    (em : ∀ p : Prop, p ∨ ¬p)
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hComplete : IsCompleteOrderedFieldFoundational E zero one add mul le)
    (epsilon : ZFSet.{u})
    (hepsilonE : epsilon ∈ E)
    (hepsilonPos : StrictFromLeManual le zero epsilon) :
    ∃ n y iy : ZFSet.{u},
      n ∈ omegaTA ∧
      ZFSet.pair n y ∈ CanonicalNumeralGraphManual E zero one add ∧
      y ∈ PrimeSubfieldCoreManual E zero one add mul ∧
      iy ∈ PrimeSubfieldCoreManual E zero one add mul ∧
      StrictFromLeManual le zero y ∧
      StrictFromLeManual le zero iy ∧
      StrictFromLeManual le iy epsilon ∧
      mul y iy one ∧ mul iy y one := by
  have hArch : IsArchimedeanGraphEditorialManual E zero one add le :=
    TA_THM_00037_archimedean_editorial_manual
      em E zero one add mul le hComplete
  exact prime_numeral_inverse_below_positive_manual
    E zero one add mul le hComplete.1 hArch
    epsilon hepsilonE hepsilonPos

end TratadoAnalisis.AbstractCompleteness.Density0009
