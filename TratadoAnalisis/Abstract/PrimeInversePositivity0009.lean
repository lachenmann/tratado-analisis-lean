import TratadoAnalisis.Abstract.PrimeDenominatorPrep0009

/-!
# TA-LEAN-0009 / P3c-03 — signo de productos e inversos en cuerpos relacionales

Candidato experimental; NO validado con Lean durante la creación.

Se prueban sobre ZFSet y operaciones relacionales: positividad de 1,
no anulación de un producto de factores no nulos, positividad de
productos de positivos, no anulación del inverso, compatibilidad del
producto con el opuesto aditivo DERECHO, y positividad de inversos.

La última proposición aplica esos hechos a un numeral del subcuerpo primo.
NO se prueba todavía que el inverso sea menor que un epsilon dado.
No se introducen operadores escogidos de negación o de inversión.
No se emplea tercero excluido ni Classical.choice.
-/

namespace TratadoAnalisis.AbstractCompleteness.Density0009

universe u

open TratadoAnalisis.AbstractCompleteness.Manual0008
open TratadoAnalisis.Dedekind.FieldPredicates
open TratadoAnalisis.Naturals.Foundational

/-- La unidad es no negativa, deducida de la totalidad y de 1 ≰ 0. -/
theorem ordered_zero_le_one_manual
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hordered : IsOrderedFieldFoundational E zero one add mul le) :
    le zero one := by
  have hzeroE : zero ∈ E := hordered.1.1.2.1
  have honeE : one ∈ E := hordered.1.2.2.1
  have hnot : ¬ le one zero :=
    one_not_le_zero_manual E zero one add mul le hordered
  rcases hordered.2.1 with ⟨_, _, _, htotal⟩
  rcases htotal zero one hzeroE honeE with hzo | hoz
  · exact hzo
  · exact False.elim (hnot hoz)

/-- La unidad es estrictamente positiva; TA-LEM-00020(3) abstracto. -/
theorem ordered_zero_lt_one_manual
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hordered : IsOrderedFieldFoundational E zero one add mul le) :
    StrictFromLeManual le zero one := by
  have hz : le zero one :=
    ordered_zero_le_one_manual E zero one add mul le hordered
  rcases hordered.1 with ⟨_, _, _, _, _, _, _, hzeroNeOne, _⟩
  exact ⟨hz, hzeroNeOne⟩

/-- Un producto de elementos no nulos no puede ser el cero. Se cancela
    con un inverso multiplicativo local y la asociatividad relacional. -/
theorem rel_mul_nonzero_of_nonzero_manual
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (hField : IsFieldFoundational E zero one add mul)
    (x y z : ZFSet.{u})
    (hxE : x ∈ E) (hyE : y ∈ E) (hzE : z ∈ E)
    (hxNonzero : x ≠ zero) (hyNonzero : y ≠ zero)
    (hxy : mul x y z) : z ≠ zero := by
  have hFieldCopy := hField
  rcases hField with
    ⟨hGroup, hMulTotal, _, hMulAssoc, _, hMulUnit,
      _, _, hInv⟩
  obtain ⟨ix, hixE, _hxi, hixx⟩ := hInv x hxE hxNonzero
  obtain ⟨t, ⟨htE, hixt⟩, _⟩ := hMulTotal ix hixE z hzE
  have hyEqT : y = t :=
    hMulAssoc ix x y one y z t hixE hxE hyE
      hixx (hMulUnit y hyE).2 hxy hixt
  intro hzZero
  have hixZero : mul ix zero t := by
    simpa only [hzZero] using hixt
  have htZero : t = zero :=
    rel_mul_zero_manual E zero one add mul hFieldCopy
      ix t hixE htE hixZero
  exact hyNonzero (hyEqT.trans htZero)

/-- Dos elementos estrictamente positivos tienen producto estrictamente
    positivo: compatibilidad de orden y producto no nulo. -/
theorem rel_mul_positive_positive_manual
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hordered : IsOrderedFieldFoundational E zero one add mul le)
    (x y z : ZFSet.{u})
    (hxE : x ∈ E) (hyE : y ∈ E) (hzE : z ∈ E)
    (hxPos : StrictFromLeManual le zero x)
    (hyPos : StrictFromLeManual le zero y)
    (hxy : mul x y z) :
    StrictFromLeManual le zero z := by
  have hnonzero : z ≠ zero :=
    rel_mul_nonzero_of_nonzero_manual E zero one add mul
      hordered.1 x y z hxE hyE hzE
      (Ne.symm hxPos.2) (Ne.symm hyPos.2) hxy
  have hnonneg : le zero z :=
    hordered.2.2.2 x y z hxE hyE hxPos.1 hyPos.1 hxy
  exact ⟨hnonneg, Ne.symm hnonzero⟩

/-- El inverso multiplicativo bilateral de x no es cero. -/
theorem rel_inverse_nonzero_manual
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (hField : IsFieldFoundational E zero one add mul)
    (x ix : ZFSet.{u})
    (hxE : x ∈ E) (_hixE : ix ∈ E)
    (hxi : mul x ix one) : ix ≠ zero := by
  have hFieldCopy := hField
  rcases hField with ⟨_, _, honeE, _, _, _, _, hzeroNeOne, _⟩
  intro hixZero
  have hxZero : mul x zero one := by
    simpa only [hixZero] using hxi
  have honeZero : one = zero :=
    rel_mul_zero_manual E zero one add mul hFieldCopy
      x one hxE honeE hxZero
  exact hzeroNeOne honeZero.symm

/-- Si ny es el opuesto aditivo de y, entonces x*ny es el opuesto
    aditivo de x*y. La distributividad es usada sobre la suma local,
    sin definir una función global de opuestos. -/
theorem rel_mul_opposite_right_manual
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (hField : IsFieldFoundational E zero one add mul)
    (x y ny p np : ZFSet.{u})
    (hxE : x ∈ E) (hyE : y ∈ E) (hnyE : ny ∈ E)
    (hpE : p ∈ E) (hnpE : np ∈ E)
    (hOpp : IsAdditiveOpposite E zero add y ny)
    (hxy : mul x y p) (hxny : mul x ny np) :
    IsAdditiveOpposite E zero add p np := by
  have hFieldCopy := hField
  rcases hField with
    ⟨hGroup, hMulTotal, _, _, _, _, hDistrib, _, _⟩
  rcases hGroup with
    ⟨hAddTotal, hzeroE, _, hAddComm, _, _⟩
  obtain ⟨r, ⟨hrE, hxzeroR⟩, _⟩ :=
    hMulTotal x hxE zero hzeroE
  have hrZero : r = zero :=
    rel_mul_zero_manual E zero one add mul hFieldCopy
      x r hxE hrE hxzeroR
  obtain ⟨s, ⟨_hsE, hpnpS⟩, _⟩ :=
    hAddTotal p hpE np hnpE
  have hrEqS : r = s :=
    hDistrib.1 x y ny zero r p np s hxE hyE hnyE
      hOpp.2.2.1 hxzeroR hxy hxny hpnpS
  have hsZero : s = zero := hrEqS.symm.trans hrZero
  have hpnpZero : add p np zero := by
    simpa only [hsZero] using hpnpS
  obtain ⟨t, ⟨_htE, hnpPT⟩, _⟩ :=
    hAddTotal np hnpE p hpE
  have hzeroEqT : zero = t :=
    hAddComm p np zero t hpE hnpE hpnpZero hnpPT
  have hnpPZero : add np p zero := by
    simpa only [← hzeroEqT] using hnpPT
  exact ⟨hpE, hnpE, hpnpZero, hnpPZero⟩

/-- TA-LEM-00020(6), interfaz abstracta: el inverso de un elemento
    estrictamente positivo es estrictamente positivo. La demostración
    usa positividad del producto de no negativos y distributividad,
    pero no presupone el criterio de cuadrados positivos. -/
theorem rel_inverse_positive_manual
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hordered : IsOrderedFieldFoundational E zero one add mul le)
    (x ix : ZFSet.{u})
    (hxE : x ∈ E) (hixE : ix ∈ E)
    (hxPos : StrictFromLeManual le zero x)
    (hxi : mul x ix one) :
    StrictFromLeManual le zero ix := by
  have horderedCopy := hordered
  have hFieldCopy : IsFieldFoundational E zero one add mul := hordered.1
  rcases hordered with ⟨hField, hOrder, _, hMulPos⟩
  rcases hField with
    ⟨hGroup, hMulTotal, honeE, _, _, _, _, _, _⟩
  rcases hGroup with
    ⟨_, hzeroE, _, _, hAddUnit, hNeg⟩
  rcases hOrder with ⟨_, _, _, hTotal⟩
  have hzeroOpp : IsAdditiveOpposite E zero add zero zero :=
    ⟨hzeroE, hzeroE, (hAddUnit zero hzeroE).1,
      (hAddUnit zero hzeroE).2⟩
  have hzeroLeIx : le zero ix := by
    rcases hTotal zero ix hzeroE hixE with h0ix | hix0
    · exact h0ix
    · obtain ⟨nix, hnixE, hixnix0, hnixix0⟩ := hNeg ix hixE
      have hixOpp : IsAdditiveOpposite E zero add ix nix :=
        ⟨hixE, hnixE, hixnix0, hnixix0⟩
      have h0nix : le zero nix :=
        opposite_reverses_le_manual E zero one add mul le
          ix zero nix zero horderedCopy hix0 hixOpp hzeroOpp
      obtain ⟨p, ⟨hpE, hxNixP⟩, _⟩ := hMulTotal x hxE nix hnixE
      have h0p : le zero p :=
        hMulPos x nix p hxE hnixE hxPos.1 h0nix hxNixP
      have honeOpp : IsAdditiveOpposite E zero add one p :=
        rel_mul_opposite_right_manual E zero one add mul
          hFieldCopy x ix nix one p
          hxE hixE hnixE honeE hpE hixOpp hxi hxNixP
      have hpOpp : IsAdditiveOpposite E zero add p one :=
        opposite_symm_manual E zero add one p honeOpp
      have honeLeZero : le one zero :=
        opposite_reverses_le_manual E zero one add mul le
          zero p zero one horderedCopy h0p hzeroOpp hpOpp
      exact False.elim
        ((one_not_le_zero_manual E zero one add mul le horderedCopy)
          honeLeZero)
  have hixNZ : ix ≠ zero :=
    rel_inverse_nonzero_manual E zero one add mul hFieldCopy
      x ix hxE hixE hxi
  exact ⟨hzeroLeIx, Ne.symm hixNZ⟩

/-- Aplicación al denominador canónico de P3c-02: el inverso situado
    en el subcuerpo primo también es estrictamente positivo. -/
theorem prime_positive_numeral_inverse_strict_manual
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
      StrictFromLeManual le zero iy ∧
      mul y iy one ∧ mul iy y one := by
  obtain ⟨n, y, iy, hn, hny, hyP, hiyP, hPosY,
      hrY, hyiy, hiyy⟩ :=
    prime_positive_numeral_inverse_manual
      E zero one add mul le hordered hArch r hrE hzeroLeR
  have hP : IsSubfieldRelationalManual E
      (PrimeSubfieldCoreManual E zero one add mul)
      zero one add mul :=
    primeSubfieldCore_isSubfield_manual E zero one add mul hordered.1
  have hSub : PrimeSubfieldCoreManual E zero one add mul ⊆ E := hP.2.1
  have hyE : y ∈ E := hSub hyP
  have hiyE : iy ∈ E := hSub hiyP
  have hPosIy : StrictFromLeManual le zero iy :=
    rel_inverse_positive_manual E zero one add mul le hordered
      y iy hyE hiyE hPosY hyiy
  exact ⟨n, y, iy, hn, hny, hyP, hiyP,
    hPosY, hrY, hPosIy, hyiy, hiyy⟩

end TratadoAnalisis.AbstractCompleteness.Density0009
