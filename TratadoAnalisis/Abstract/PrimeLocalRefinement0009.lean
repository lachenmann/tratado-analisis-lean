import TratadoAnalisis.Abstract.PrimeReciprocalOrder0009

/-!
# TA-LEAN-0009 / P3c-05 — intervalos y refinamiento local del primo

Candidato experimental. Conserva un unico universo y la semantica
conjuntista de P_E. No postula ninguna forma de densidad.

1. Una traslacion relacional preserva el orden estricto.
2. Una traslacion por la izquierda tambien lo preserva.
3. Si x<y existe d>0 con x+d=y, usando opuestos locales.
4. Si p pertenece al subcuerpo primo y p<y, otro q del primo verifica
   p<q<y. Se utiliza el reciproco pequeno certificado por P3c-04.
5. Variante para cuerpo completo, con em explicito.

La afirmacion 4 NO implica por si sola la densidad del primo en E:
requiere que el extremo izquierdo ya pertenezca al subcuerpo primo.
Para extremos arbitrarios falta un argumento de minimo natural o
una construccion equivalente de multiplos racionales.
-/

namespace TratadoAnalisis.AbstractCompleteness.Density0009

universe u

open TratadoAnalisis.AbstractCompleteness.Manual0008
open TratadoAnalisis.Dedekind.FieldPredicates

/-- La traslacion por la derecha preserva desigualdades estrictas,
    sin suponer funciones totales escogidas para la suma. -/
theorem rel_add_right_strict_mono_manual
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hordered : IsOrderedFieldFoundational E zero one add mul le)
    (x y z xz yz : ZFSet.{u})
    (hxE : x ∈ E) (hyE : y ∈ E) (hzE : z ∈ E)
    (hxzE : xz ∈ E) (hyzE : yz ∈ E)
    (hxy : StrictFromLeManual le x y)
    (hXZ : add x z xz) (hYZ : add y z yz) :
    StrictFromLeManual le xz yz := by
  have hOrder : IsTotalOrderFoundational E le := hordered.2.1
  have hLe : le xz yz :=
    hordered.2.2.1 x y z xz yz hxE hyE hzE hxy.1 hXZ hYZ
  have hNe : xz ≠ yz := by
    intro hEq
    have hReverse : le yz xz := by
      rw [hEq]
      exact hOrder.1 yz hyzE
    have hyx : le y x :=
      rel_add_reflect_le_manual E zero one add mul le
        y x z yz xz hordered hyE hxE hzE hyzE hxzE
        hYZ hXZ hReverse
    have hxyEq : x = y :=
      hOrder.2.1 x y hxE hyE hxy.1 hyx
    exact hxy.2 hxyEq
  exact ⟨hLe, hNe⟩

/-- Lo mismo para una traslacion por la izquierda; la conversion al
    caso derecho emplea conmutatividad relacional. -/
theorem rel_add_left_strict_mono_manual
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hordered : IsOrderedFieldFoundational E zero one add mul le)
    (x y z zx zy : ZFSet.{u})
    (hxE : x ∈ E) (hyE : y ∈ E) (hzE : z ∈ E)
    (hzxE : zx ∈ E) (hzyE : zy ∈ E)
    (hxy : StrictFromLeManual le x y)
    (hZX : add z x zx) (hZY : add z y zy) :
    StrictFromLeManual le zx zy := by
  rcases hordered.1.1 with ⟨hBin, _, _, hComm, _, _⟩
  obtain ⟨xz, ⟨_hxzE, hXZ⟩, _⟩ := hBin x hxE z hzE
  obtain ⟨yz, ⟨_hyzE, hYZ⟩, _⟩ := hBin y hyE z hzE
  have hEqZX : zx = xz := hComm z x zx xz hzE hxE hZX hXZ
  have hEqZY : zy = yz := hComm z y zy yz hzE hyE hZY hYZ
  have hXZ' : add x z zx := by simpa only [← hEqZX] using hXZ
  have hYZ' : add y z zy := by simpa only [← hEqZY] using hYZ
  exact rel_add_right_strict_mono_manual
    E zero one add mul le hordered x y z zx zy
    hxE hyE hzE hzxE hzyE hxy hXZ' hYZ'

/-- Todo intervalo abierto tiene una diferencia positiva local:
    si x<y, existe d>0 con x+d=y. Se prueba con el opuesto local de x. -/
theorem rel_interval_positive_gap_manual
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hordered : IsOrderedFieldFoundational E zero one add mul le)
    (x y : ZFSet.{u})
    (hxE : x ∈ E) (hyE : y ∈ E)
    (hxy : StrictFromLeManual le x y) :
    ∃ d : ZFSet.{u}, d ∈ E ∧
      StrictFromLeManual le zero d ∧ add x d y := by
  have hOrder : IsTotalOrderFoundational E le := hordered.2.1
  rcases hordered.1.1 with
    ⟨hBin, hzeroE, hAssoc, hComm, hUnit, hNeg⟩
  obtain ⟨nx, hnxE, hxnxZero, _hnxXZero⟩ := hNeg x hxE
  obtain ⟨d, ⟨hdE, hYNxD⟩, _⟩ := hBin y hyE nx hnxE
  have hZeroLeD : le zero d :=
    hordered.2.2.1 x y nx zero d hxE hyE hnxE
      hxy.1 hxnxZero hYNxD
  have hZeroNeD : zero ≠ d := by
    intro hEq
    have hDLeZero : le d zero := by
      rw [← hEq]
      exact hOrder.1 zero hzeroE
    have hyLeX : le y x :=
      rel_add_reflect_le_manual E zero one add mul le
        y x nx d zero hordered hyE hxE hnxE hdE hzeroE
        hYNxD hxnxZero hDLeZero
    have hEqXY : x = y :=
      hOrder.2.1 x y hxE hyE hxy.1 hyLeX
    exact hxy.2 hEqXY
  obtain ⟨v, ⟨_hvE, hNxYV⟩, _⟩ := hBin nx hnxE y hyE
  have hDEqV : d = v := hComm y nx d v hyE hnxE hYNxD hNxYV
  have hNxYD : add nx y d := by simpa only [← hDEqV] using hNxYV
  obtain ⟨t, ⟨_htE, hXDT⟩, _⟩ := hBin x hxE d hdE
  have hYEqT : y = t :=
    hAssoc x nx y zero y d t hxE hnxE hyE
      hxnxZero (hUnit y hyE).2 hNxYD hXDT
  have hXDY : add x d y := by simpa only [← hYEqT] using hXDT
  exact ⟨d, hdE, ⟨hZeroLeD, hZeroNeD⟩, hXDY⟩

/-- Refinamiento local por la derecha de un punto YA perteneciente al
    primo: entre p ∈ P y un y>p hay otro q∈P. No presupone densidad. -/
theorem prime_refine_right_of_archimedean_manual
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hordered : IsOrderedFieldFoundational E zero one add mul le)
    (hArch : IsArchimedeanGraphEditorialManual E zero one add le)
    (p y : ZFSet.{u})
    (hpPrime : p ∈ PrimeSubfieldCoreManual E zero one add mul)
    (hyE : y ∈ E)
    (hpy : StrictFromLeManual le p y) :
    ∃ q : ZFSet.{u},
      q ∈ PrimeSubfieldCoreManual E zero one add mul ∧
      StrictFromLeManual le p q ∧
      StrictFromLeManual le q y := by
  have hPrime : IsSubfieldRelationalManual E
      (PrimeSubfieldCoreManual E zero one add mul) zero one add mul :=
    primeSubfieldCore_isSubfield_manual E zero one add mul hordered.1
  rcases hPrime with ⟨_, hSub, _, _, hAddPrime, _, _, _⟩
  have hpE : p ∈ E := hSub hpPrime
  obtain ⟨d, hdE, hDPos, hPdY⟩ :=
    rel_interval_positive_gap_manual E zero one add mul le hordered
      p y hpE hyE hpy
  obtain ⟨_, _, eps, _, _, _, hEpsPrime, _, hEpsPos, hEpsLtD, _, _⟩ :=
    prime_numeral_inverse_below_positive_manual
      E zero one add mul le hordered hArch d hdE hDPos
  have hEpsE : eps ∈ E := hSub hEpsPrime
  obtain ⟨q, hqPrime, hPEpsQ⟩ := hAddPrime p eps hpPrime hEpsPrime
  have hqE : q ∈ E := hSub hqPrime
  rcases hordered.1.1 with ⟨_, hZeroE, _, _, hAddUnit, _⟩
  have hpLtQ : StrictFromLeManual le p q :=
    rel_add_left_strict_mono_manual E zero one add mul le hordered
      zero eps p p q hZeroE hEpsE hpE hpE hqE
      hEpsPos (hAddUnit p hpE).1 hPEpsQ
  have hqLtY : StrictFromLeManual le q y :=
    rel_add_left_strict_mono_manual E zero one add mul le hordered
      eps d p q y hEpsE hdE hpE hqE hyE
      hEpsLtD hPEpsQ hPdY
  exact ⟨q, hqPrime, hpLtQ, hqLtY⟩

/-- Variante bajo completitud; em se explicita como en TA-THM-00037. -/
theorem prime_refine_right_of_complete_manual
    (em : ∀ p : Prop, p ∨ ¬p)
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hComplete : IsCompleteOrderedFieldFoundational E zero one add mul le)
    (p y : ZFSet.{u})
    (hpPrime : p ∈ PrimeSubfieldCoreManual E zero one add mul)
    (hyE : y ∈ E)
    (hpy : StrictFromLeManual le p y) :
    ∃ q : ZFSet.{u},
      q ∈ PrimeSubfieldCoreManual E zero one add mul ∧
      StrictFromLeManual le p q ∧
      StrictFromLeManual le q y := by
  have hArch : IsArchimedeanGraphEditorialManual E zero one add le :=
    TA_THM_00037_archimedean_editorial_manual
      em E zero one add mul le hComplete
  exact prime_refine_right_of_archimedean_manual
    E zero one add mul le hComplete.1 hArch p y hpPrime hyE hpy

end TratadoAnalisis.AbstractCompleteness.Density0009
