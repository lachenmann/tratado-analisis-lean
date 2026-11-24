import TratadoAnalisis.Abstract.PrimeDensityReduction0009

/-!
# TA-LEAN-0009 — P3b: construcción conjuntista del subcuerpo primo

Candidato experimental; pendiente de ejecución en Lean 4.32.1.

TA-DEF-00070: familia de todos los subcuerpos por Potencia y Separación;
subcuerpo primo como intersección acotada por E, también por Separación.
TA-PRO-00070: clausura bajo las operaciones relacionales y minimalidad.
No se usa el axioma de elección ni una función global de inversos.
NO demuestra TA-THM-00036 ni TA-PRO-00078 incondicionalmente.
-/

namespace TratadoAnalisis.AbstractCompleteness.Density0009

universe u

open TratadoAnalisis.Dedekind.FieldPredicates
open TratadoAnalisis.AbstractCompleteness.Manual0008

/-- Intersección indexada de todos los subcuerpos: la familia existe
    por Potencia y Separación, en la base ZF del tratado. -/
def PrimeSubfieldFamilyManual
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop) : ZFSet.{u} :=
  ZFSet.sep
    (fun K => IsSubfieldRelationalManual E K zero one add mul)
    (ZFSet.powerset E)

/-- Intersección de la familia, acotada por el cuerpo E.
    La cota E hace explícito el conjunto ambiente. -/
def PrimeSubfieldCoreManual
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop) : ZFSet.{u} :=
  ZFSet.sep
    (fun x => ∀ K : ZFSet.{u},
      K ∈ PrimeSubfieldFamilyManual E zero one add mul → x ∈ K) E

/-- Caracterización de los miembros de la familia de subcuerpos. -/
theorem mem_primeSubfieldFamily_iff_manual
    (E K zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop) :
    K ∈ PrimeSubfieldFamilyManual E zero one add mul ↔
      IsSubfieldRelationalManual E K zero one add mul := by
  constructor
  · intro hK
    exact (ZFSet.mem_sep.mp hK).2
  · intro hK
    exact ZFSet.mem_sep.mpr
      ⟨ZFSet.mem_powerset.mpr hK.2.1, hK⟩

/-- La pertenencia a la intersección equivale a pertenecer a E y a
    cada uno de los subcuerpos de E. -/
theorem mem_primeSubfieldCore_iff_manual
    (E x zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop) :
    x ∈ PrimeSubfieldCoreManual E zero one add mul ↔
      x ∈ E ∧
        ∀ K : ZFSet.{u},
          IsSubfieldRelationalManual E K zero one add mul → x ∈ K := by
  constructor
  · intro hx
    rcases ZFSet.mem_sep.mp hx with ⟨hxE, hxAll⟩
    refine ⟨hxE, ?_⟩
    intro K hK
    exact hxAll K ((mem_primeSubfieldFamily_iff_manual
      E K zero one add mul).mpr hK)
  · rintro ⟨hxE, hxAll⟩
    apply ZFSet.mem_sep.mpr
    refine ⟨hxE, ?_⟩
    intro K hK
    exact hxAll K ((mem_primeSubfieldFamily_iff_manual
      E K zero one add mul).mp hK)

/-- El cuerpo ambiente E, considerado como subconjunto de sí mismo,
    satisface la interfaz relacional de subcuerpo. -/
theorem ambient_isSubfield_manual
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (hField : IsFieldFoundational E zero one add mul) :
    IsSubfieldRelationalManual E E zero one add mul := by
  have hParts : IsFieldFoundational E zero one add mul := hField
  rcases hParts with
    ⟨hAddGroup, hMulTotal, hOne, _hMulAssoc, _hMulComm,
      _hMulUnit, _hDistrib, _hZeroNeOne, hInv⟩
  rcases hAddGroup with
    ⟨hAddTotal, hZero, _hAddAssoc, _hAddComm, _hAddUnit, hNeg⟩
  refine ⟨hField, ?_, hZero, hOne, ?_, ?_, hNeg, hInv⟩
  · intro x hx
    exact hx
  · intro x y hx hy
    obtain ⟨z, ⟨hz, hOp⟩, _⟩ := hAddTotal x hx y hy
    exact ⟨z, hz, hOp⟩
  · intro x y hx hy
    obtain ⟨z, ⟨hz, hOp⟩, _⟩ := hMulTotal x hx y hy
    exact ⟨z, hz, hOp⟩

/-- La familia de subcuerpos está habitada: E es uno de sus miembros.
    Así la intersección no se toma sobre una familia vacía. -/
theorem ambient_mem_primeSubfieldFamily_manual
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (hField : IsFieldFoundational E zero one add mul) :
    E ∈ PrimeSubfieldFamilyManual E zero one add mul := by
  exact (mem_primeSubfieldFamily_iff_manual
    E E zero one add mul).mpr
    (ambient_isSubfield_manual E zero one add mul hField)

/-- Unicidad de inversos bilaterales en una operación relacional asociativa
    con neutro: el mismo argumento sirve para opuestos e inversos del campo.
    No se elige una función global para ninguna operación. -/
theorem relational_inverse_unique_manual
    (A e x a b : ZFSet.{u})
    (op : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (hAssoc : RelAssociative A op)
    (hUnit : RelUnit A e op)
    (hx : x ∈ A) (ha : a ∈ A) (hb : b ∈ A)
    (hax : op a x e) (hxb : op x b e) : a = b := by
  have hLeft : op e b b := (hUnit b hb).2
  have hRight : op a e a := (hUnit a ha).1
  have h : b = a :=
    hAssoc a x b e b e a ha hx hb hax hLeft hxb hRight
  exact h.symm

/-- TA-PRO-00070 (estructura): la intersección de todos los subcuerpos
    satisface las cláusulas de TA-DEF-00069. Los resultados de suma/producto
    se identifican por unicidad; los opuestos e inversos por asociatividad. -/
theorem primeSubfieldCore_isSubfield_manual
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (hField : IsFieldFoundational E zero one add mul) :
    IsSubfieldRelationalManual E
      (PrimeSubfieldCoreManual E zero one add mul) zero one add mul := by
  have hParts := hField
  rcases hParts with
    ⟨hAddGroup, hMulTotal, hOne, hMulAssoc, _hMulComm,
      hMulUnit, _hDistrib, _hZeroNeOne, hInv⟩
  rcases hAddGroup with
    ⟨hAddTotal, hZero, hAddAssoc, _hAddComm, hAddUnit, hNeg⟩
  let P := PrimeSubfieldCoreManual E zero one add mul
  have hMem (v : ZFSet.{u}) :
      v ∈ P ↔ v ∈ E ∧
        ∀ K : ZFSet.{u},
          IsSubfieldRelationalManual E K zero one add mul → v ∈ K :=
    mem_primeSubfieldCore_iff_manual E v zero one add mul
  refine ⟨hField, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact ((hMem x).mp hx).1
  · apply (hMem zero).mpr
    refine ⟨hZero, ?_⟩
    intro K hK
    rcases hK with ⟨_, _, hzK, _, _, _, _, _⟩
    exact hzK
  · apply (hMem one).mpr
    refine ⟨hOne, ?_⟩
    intro K hK
    rcases hK with ⟨_, _, _, hoK, _, _, _, _⟩
    exact hoK
  · intro x y hx hy
    have hxE : x ∈ E := ((hMem x).mp hx).1
    have hyE : y ∈ E := ((hMem y).mp hy).1
    obtain ⟨z, ⟨hzE, hzOp⟩, hUnique⟩ := hAddTotal x hxE y hyE
    refine ⟨z, (hMem z).mpr ⟨hzE, ?_⟩, hzOp⟩
    intro K hK
    have hxK : x ∈ K := ((hMem x).mp hx).2 K hK
    have hyK : y ∈ K := ((hMem y).mp hy).2 K hK
    rcases hK with ⟨_, hSub, _, _, hClosure, _, _, _⟩
    obtain ⟨w, hwK, hwOp⟩ := hClosure x y hxK hyK
    have hwE : w ∈ E := hSub hwK
    have hWZ : w = z := hUnique w ⟨hwE, hwOp⟩
    simpa only [hWZ] using hwK
  · intro x y hx hy
    have hxE : x ∈ E := ((hMem x).mp hx).1
    have hyE : y ∈ E := ((hMem y).mp hy).1
    obtain ⟨z, ⟨hzE, hzOp⟩, hUnique⟩ := hMulTotal x hxE y hyE
    refine ⟨z, (hMem z).mpr ⟨hzE, ?_⟩, hzOp⟩
    intro K hK
    have hxK : x ∈ K := ((hMem x).mp hx).2 K hK
    have hyK : y ∈ K := ((hMem y).mp hy).2 K hK
    rcases hK with ⟨_, hSub, _, _, _, hClosure, _, _⟩
    obtain ⟨w, hwK, hwOp⟩ := hClosure x y hxK hyK
    have hwE : w ∈ E := hSub hwK
    have hWZ : w = z := hUnique w ⟨hwE, hwOp⟩
    simpa only [hWZ] using hwK
  · intro x hx
    have hxE : x ∈ E := ((hMem x).mp hx).1
    obtain ⟨nx, hnxE, hxn, hnx⟩ := hNeg x hxE
    refine ⟨nx, (hMem nx).mpr ⟨hnxE, ?_⟩, hxn, hnx⟩
    intro K hK
    have hxK : x ∈ K := ((hMem x).mp hx).2 K hK
    rcases hK with ⟨_, hSub, _, _, _, _, hNegK, _⟩
    obtain ⟨nK, hnK, hxnK, _hnKx⟩ := hNegK x hxK
    have hnKE : nK ∈ E := hSub hnK
    have hEq : nx = nK := relational_inverse_unique_manual
      E zero x nx nK add hAddAssoc hAddUnit
      hxE hnxE hnKE hnx hxnK
    simpa only [hEq] using hnK
  · intro x hx hxne
    have hxE : x ∈ E := ((hMem x).mp hx).1
    obtain ⟨ix, hixE, hxi, hix⟩ := hInv x hxE hxne
    refine ⟨ix, (hMem ix).mpr ⟨hixE, ?_⟩, hxi, hix⟩
    intro K hK
    have hxK : x ∈ K := ((hMem x).mp hx).2 K hK
    rcases hK with ⟨_, hSub, _, _, _, _, _, hInvK⟩
    obtain ⟨iK, hiK, hxiK, _hiKx⟩ := hInvK x hxK hxne
    have hiKE : iK ∈ E := hSub hiK
    have hEq : ix = iK := relational_inverse_unique_manual
      E one x ix iK mul hMulAssoc hMulUnit
      hxE hixE hiKE hix hxiK
    simpa only [hEq] using hiK

/-- Minimalidad de la intersección: el subcuerpo primo se incluye en
    cualquier subcuerpo K del mismo cuerpo E. -/
theorem primeSubfieldCore_subset_subfield_manual
    (E K zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (hK : IsSubfieldRelationalManual E K zero one add mul) :
    PrimeSubfieldCoreManual E zero one add mul ⊆ K := by
  intro x hx
  exact ((mem_primeSubfieldCore_iff_manual
    E x zero one add mul).mp hx).2 K hK

/-- TA-PRO-00070 íntegra, en la interfaz de P3a:
    P_F es un subcuerpo contenido en todos los subcuerpos de E. -/
theorem TA_PRO_00070_primeSubfield_manual
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (hField : IsFieldFoundational E zero one add mul) :
    IsPrimeSubfieldRelationalManual E
      (PrimeSubfieldCoreManual E zero one add mul) zero one add mul := by
  refine ⟨primeSubfieldCore_isSubfield_manual
    E zero one add mul hField, ?_⟩
  intro K hK
  exact primeSubfieldCore_subset_subfield_manual E K zero one add mul hK

/-- Reemplaza la hipótesis abstracta hPrime de P3a por la construcción
    conjuntista acreditada de P_F. SOLO resta la densidad arquimediana
    del primo (TA-THM-00036), como hipótesis expresa; no se afirma todavía
    TA-PRO-00078 sin condiciones adicionales. -/
theorem TA_PRO_00078_reduction_with_constructed_prime_manual
    (em : ∀ p : Prop, p ∨ ¬p)
    (Q E zeroQ oneQ zeroE oneE : ZFSet.{u})
    (addQ mulQ addE mulE : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (leQ leE : ZFSet.{u} → ZFSet.{u} → Prop)
    (ι : ZFSet.{u} → ZFSet.{u}) (G f : ZFSet.{u})
    (hComplete : IsCompleteOrderedFieldFoundational E zeroE oneE addE mulE leE)
    (hemb : IsOrderedFieldEmbeddingFoundational
      Q E zeroQ oneQ zeroE oneE addQ mulQ addE mulE leQ leE ι G f)
    (hArchPrimeDense :
      IsArchimedeanGraphEditorialManual E zeroE oneE addE leE →
      IsOrderDenseSubsetManual E
        (PrimeSubfieldCoreManual E zeroE oneE addE mulE) leE)
    (x y : ZFSet.{u}) (hxE : x ∈ E) (hyE : y ∈ E)
    (hxy : StrictFromLeManual leE x y) :
    ∃ q : ZFSet.{u}, q ∈ Q ∧
      StrictFromLeManual leE x (ι q) ∧
      StrictFromLeManual leE (ι q) y := by
  have hField : IsFieldFoundational E zeroE oneE addE mulE := hComplete.1.1
  exact TA_PRO_00078_reduction_manual
    em Q E (PrimeSubfieldCoreManual E zeroE oneE addE mulE)
    zeroQ oneQ zeroE oneE addQ mulQ addE mulE leQ leE
    ι G f hComplete hemb
    (TA_PRO_00070_primeSubfield_manual E zeroE oneE addE mulE hField)
    hArchPrimeDense x y hxE hyE hxy

end TratadoAnalisis.AbstractCompleteness.Density0009
