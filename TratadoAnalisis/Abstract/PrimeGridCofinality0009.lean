import TratadoAnalisis.Abstract.PrimeLocalRefinement0009

/-!
# TA-LEAN-0009 / P3c-06 — monotonia estricta multiplicativa y malla cofinal

Candidato experimental. Todo se expresa mediante ZFSet y operaciones
relacionales totales y univocas. No se usa una funcion escogida de inversos.

1. Cancelacion por un factor derecho distinto de cero.
2. Multiplicacion estrictamente creciente por un factor positivo.
3. Para d>0 en el subcuerpo primo, los productos de d por numerales
   canonicos son cofinales superiormente en E.
4. Variante bajo completitud, con `em` explicito.
5. Preparacion de malla: dado epsilon>0, se encuentra un paso positivo
   d en el primo con d<epsilon y un multiplo numeral de d mayor que x.

NO se prueba aqui que existe un multiplo dentro de (x,y). Falta tomar
el primer indice natural que supera x y comparar con su predecesor.
NO se afirma TA-THM-00036 ni TA-PRO-00078 incondicionalmente.
-/

namespace TratadoAnalisis.AbstractCompleteness.Density0009

universe u

open TratadoAnalisis.AbstractCompleteness.Manual0008
open TratadoAnalisis.Dedekind.FieldPredicates
open TratadoAnalisis.Naturals.Foundational

/-- Cancelar un factor derecho no nulo usando un inverso bilateral local
    y la unicidad del producto. No se necesita orden ni eleccion. -/
theorem rel_mul_right_cancel_nonzero_manual
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (hField : IsFieldFoundational E zero one add mul)
    (x y z xz yz : ZFSet.{u})
    (hxE : x ∈ E) (hyE : y ∈ E) (hzE : z ∈ E)
    (hxzE : xz ∈ E) (hyzE : yz ∈ E)
    (hzNonzero : z ≠ zero)
    (hXZ : mul x z xz) (hYZ : mul y z yz)
    (hSame : xz = yz) : x = y := by
  rcases hField with
    ⟨_, hMulTotal, _, hAssoc, _, hUnit, _, _, hInv⟩
  obtain ⟨iz, hizE, hZIz, _hIzZ⟩ := hInv z hzE hzNonzero
  obtain ⟨tx, ⟨htxE, hXzIz⟩, hUnique⟩ :=
    hMulTotal xz hxzE iz hizE
  obtain ⟨ty, ⟨htyE, hYzIz⟩, _⟩ :=
    hMulTotal yz hyzE iz hizE
  have hTxEqX : tx = x :=
    hAssoc x z iz xz tx one x hxE hzE hizE
      hXZ hXzIz hZIz (hUnit x hxE).1
  have hTyEqY : ty = y :=
    hAssoc y z iz yz ty one y hyE hzE hizE
      hYZ hYzIz hZIz (hUnit y hyE).1
  have hYzIzAtXz : mul xz iz ty := by
    simpa only [← hSame] using hYzIz
  have hTxEqTy : tx = ty :=
    (hUnique ty ⟨htyE, hYzIzAtXz⟩).symm
  exact hTxEqX.symm.trans (hTxEqTy.trans hTyEqY)

/-- TA-LEM-00020, monotonia estricta de la multiplicacion por un
    positivo. Su parte debil ya fue obtenida en P3c-04; la estricta
    resulta de cancelar el factor positivo, que no es cero. -/
theorem rel_mul_right_strict_mono_positive_manual
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hordered : IsOrderedFieldFoundational E zero one add mul le)
    (x y z xz yz : ZFSet.{u})
    (hxE : x ∈ E) (hyE : y ∈ E) (hzE : z ∈ E)
    (hxzE : xz ∈ E) (hyzE : yz ∈ E)
    (hxy : StrictFromLeManual le x y)
    (hzPos : StrictFromLeManual le zero z)
    (hXZ : mul x z xz) (hYZ : mul y z yz) :
    StrictFromLeManual le xz yz := by
  have hLe : le xz yz :=
    rel_mul_right_mono_nonnegative_manual
      E zero one add mul le hordered
      x y z xz yz hxE hyE hzE hxzE hyzE
      hxy.1 hzPos.1 hXZ hYZ
  have hNe : xz ≠ yz := by
    intro hEq
    have hXYeq : x = y :=
      rel_mul_right_cancel_nonzero_manual
        E zero one add mul hordered.1
        x y z xz yz hxE hyE hzE hxzE hyzE
        (Ne.symm hzPos.2) hXZ hYZ hEq
    exact hxy.2 hXYeq
  exact ⟨hLe, hNe⟩

/-- Cofinalidad por multiplos de cualquier paso primo positivo d.
    La constante entera y esta representada por un par del grafo
    canonico de numerales, sin escoger una aplicacion global omega->E. -/
theorem prime_canonical_multiples_cofinal_manual
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hordered : IsOrderedFieldFoundational E zero one add mul le)
    (hArch : IsArchimedeanGraphEditorialManual E zero one add le)
    (d : ZFSet.{u})
    (hdPrime : d ∈ PrimeSubfieldCoreManual E zero one add mul)
    (hdPos : StrictFromLeManual le zero d)
    (x : ZFSet.{u}) (hxE : x ∈ E) :
    ∃ n y q : ZFSet.{u},
      n ∈ omegaTA ∧
      ZFSet.pair n y ∈ CanonicalNumeralGraphManual E zero one add ∧
      q ∈ PrimeSubfieldCoreManual E zero one add mul ∧
      mul y d q ∧ StrictFromLeManual le x q := by
  have hField : IsFieldFoundational E zero one add mul := hordered.1
  rcases hField with
    ⟨_, hMulTotal, _, hAssoc, _, hMulUnit, _, _, hInv⟩
  have hPrime : IsSubfieldRelationalManual E
      (PrimeSubfieldCoreManual E zero one add mul) zero one add mul :=
    primeSubfieldCore_isSubfield_manual E zero one add mul hordered.1
  rcases hPrime with ⟨_, hSub, _, _, _, hPrimeMul, _, _⟩
  have hdE : d ∈ E := hSub hdPrime
  obtain ⟨id, hidE, _hDId, hIdD⟩ :=
    hInv d hdE (Ne.symm hdPos.2)
  obtain ⟨t, ⟨htE, hXIdT⟩, _⟩ :=
    hMulTotal x hxE id hidE
  obtain ⟨n, hn, y, hNY, hTY⟩ := hArch t htE
  have hyPrime : y ∈ PrimeSubfieldCoreManual E zero one add mul :=
    TA_COR_00011_numerals_in_prime_manual
      E zero one add mul hordered.1 n y hn hNY
  have hyE : y ∈ E := hSub hyPrime
  obtain ⟨q, hqPrime, hYDq⟩ :=
    hPrimeMul y d hyPrime hdPrime
  have hqE : q ∈ E := hSub hqPrime
  obtain ⟨td, ⟨htdE, hTD⟩, _⟩ :=
    hMulTotal t htE d hdE
  have hTdEqX : td = x :=
    hAssoc x id d t td one x hxE hidE hdE
      hXIdT hTD hIdD (hMulUnit x hxE).1
  have hTdLtQ : StrictFromLeManual le td q :=
    rel_mul_right_strict_mono_positive_manual
      E zero one add mul le hordered
      t y d td q htE hyE hdE htdE hqE hTY hdPos hTD hYDq
  have hXLtQ : StrictFromLeManual le x q := by
    simpa only [hTdEqX] using hTdLtQ
  exact ⟨n, y, q, hn, hNY, hqPrime, hYDq, hXLtQ⟩

/-- Especializacion a un cuerpo completo, conservando em como
    parametro explicito de la derivacion de arquimedianidad. -/
theorem prime_canonical_multiples_cofinal_of_complete_manual
    (em : ∀ p : Prop, p ∨ ¬p)
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hComplete : IsCompleteOrderedFieldFoundational E zero one add mul le)
    (d : ZFSet.{u})
    (hdPrime : d ∈ PrimeSubfieldCoreManual E zero one add mul)
    (hdPos : StrictFromLeManual le zero d)
    (x : ZFSet.{u}) (hxE : x ∈ E) :
    ∃ n y q : ZFSet.{u},
      n ∈ omegaTA ∧
      ZFSet.pair n y ∈ CanonicalNumeralGraphManual E zero one add ∧
      q ∈ PrimeSubfieldCoreManual E zero one add mul ∧
      mul y d q ∧ StrictFromLeManual le x q := by
  have hArch : IsArchimedeanGraphEditorialManual E zero one add le :=
    TA_THM_00037_archimedean_editorial_manual
      em E zero one add mul le hComplete
  exact prime_canonical_multiples_cofinal_manual
    E zero one add mul le hComplete.1 hArch d hdPrime hdPos x hxE

/-- Malla cofinal de paso menor que un epsilon dado: primero obtener
    un reciproco natural pequeno, luego superar x con un multiplo
    numeral de ese paso. NO se selecciona aun el indice minimo. -/
theorem prime_small_mesh_cofinal_manual
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hordered : IsOrderedFieldFoundational E zero one add mul le)
    (hArch : IsArchimedeanGraphEditorialManual E zero one add le)
    (epsilon x : ZFSet.{u})
    (hepsilonE : epsilon ∈ E)
    (hepsilonPos : StrictFromLeManual le zero epsilon)
    (hxE : x ∈ E) :
    ∃ d n y q : ZFSet.{u},
      d ∈ PrimeSubfieldCoreManual E zero one add mul ∧
      StrictFromLeManual le zero d ∧
      StrictFromLeManual le d epsilon ∧
      n ∈ omegaTA ∧
      ZFSet.pair n y ∈ CanonicalNumeralGraphManual E zero one add ∧
      q ∈ PrimeSubfieldCoreManual E zero one add mul ∧
      mul y d q ∧ StrictFromLeManual le x q := by
  obtain ⟨_, _, d, _, _, _, hdPrime, _, hdPos, hdLtEps, _, _⟩ :=
    prime_numeral_inverse_below_positive_manual
      E zero one add mul le hordered hArch
      epsilon hepsilonE hepsilonPos
  obtain ⟨n, y, q, hn, hNY, hqPrime, hYDq, hxq⟩ :=
    prime_canonical_multiples_cofinal_manual
      E zero one add mul le hordered hArch
      d hdPrime hdPos x hxE
  exact ⟨d, n, y, q, hdPrime, hdPos, hdLtEps,
    hn, hNY, hqPrime, hYDq, hxq⟩

end TratadoAnalisis.AbstractCompleteness.Density0009
