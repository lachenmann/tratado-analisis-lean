import TratadoAnalisis.Abstract.PrimeGridSuccessor0009

/-!
# TA-LEAN-0009 / P3c-09 — malla trasladada y primer cruce sucesor

Se fija un origen p en el subcuerpo primo tal que p < x. La malla
trasladada p + nu(n)*d alcanza cualquier cota; su primer indice que
supera x nunca es cero. Todo se formula con testigos de las relaciones
add/mul y con el grafo conjuntista de numerales, sin elegir funciones.

Esta etapa NO demuestra todavia que el primer punto de la malla este
por debajo de y. La cota estricta por el extremo derecho requiere
transferir la identidad del sucesor de P3c-08 a la malla trasladada.
-/

namespace TratadoAnalisis.AbstractCompleteness.Density0009

universe u

open TratadoAnalisis.AbstractCompleteness.Manual0008
open TratadoAnalisis.Dedekind.FieldPredicates
open TratadoAnalisis.Naturals.Foundational
open TratadoAnalisis.Naturals.Recursion

/-- Predicado de cruce de una malla trasladada, definido sin funciones
    globales: el indice n se interpreta por el grafo de numerales. -/
def ShiftedGridCrossingManual
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (p d x n : ZFSet.{u}) : Prop :=
  ∃ a q r : ZFSet.{u},
    ZFSet.pair n a ∈ CanonicalNumeralGraphManual E zero one add ∧
    q ∈ PrimeSubfieldCoreManual E zero one add mul ∧
    r ∈ PrimeSubfieldCoreManual E zero one add mul ∧
    mul a d q ∧ add p q r ∧ StrictFromLeManual le x r

/-- Cofinalidad de la malla con origen p en el primo: para p<x y d>0,
    existe un punto primo p+nu(n)*d estrictamente mayor que x. -/
theorem prime_shifted_grid_cofinal_manual
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hordered : IsOrderedFieldFoundational E zero one add mul le)
    (hArch : IsArchimedeanGraphEditorialManual E zero one add le)
    (p d x : ZFSet.{u})
    (hpPrime : p ∈ PrimeSubfieldCoreManual E zero one add mul)
    (hdPrime : d ∈ PrimeSubfieldCoreManual E zero one add mul)
    (hdPos : StrictFromLeManual le zero d)
    (hxE : x ∈ E) (hpx : StrictFromLeManual le p x) :
    ∃ n : ZFSet.{u}, n ∈ omegaTA ∧
      ShiftedGridCrossingManual E zero one add mul le p d x n := by
  have hPrime : IsSubfieldRelationalManual E
      (PrimeSubfieldCoreManual E zero one add mul) zero one add mul :=
    primeSubfieldCore_isSubfield_manual E zero one add mul hordered.1
  rcases hPrime with ⟨_, hSub, _, _, hAddPrime, _, _, _⟩
  have hpE : p ∈ E := hSub hpPrime
  obtain ⟨t, htE, _htPos, hPtX⟩ :=
    rel_interval_positive_gap_manual
      E zero one add mul le hordered p x hpE hxE hpx
  obtain ⟨n, a, q, hn, hNA, hqPrime, hADQ, htQ⟩ :=
    prime_canonical_multiples_cofinal_manual
      E zero one add mul le hordered hArch
      d hdPrime hdPos t htE
  obtain ⟨r, hrPrime, hPQR⟩ := hAddPrime p q hpPrime hqPrime
  have hqE : q ∈ E := hSub hqPrime
  have hrE : r ∈ E := hSub hrPrime
  have hxR : StrictFromLeManual le x r :=
    rel_add_left_strict_mono_manual
      E zero one add mul le hordered
      t q p x r htE hqE hpE hxE hrE htQ hPtX hPQR
  exact ⟨n, hn, a, q, r, hNA, hqPrime, hrPrime, hADQ, hPQR, hxR⟩

/-- Un indice cero en la malla trasladada produce exactamente p,
    que no puede superar x cuando p<x. -/
theorem prime_shifted_grid_zero_not_cross_manual
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hordered : IsOrderedFieldFoundational E zero one add mul le)
    (p d x : ZFSet.{u})
    (hpPrime : p ∈ PrimeSubfieldCoreManual E zero one add mul)
    (hdPrime : d ∈ PrimeSubfieldCoreManual E zero one add mul)
    (hxE : x ∈ E) (hpx : StrictFromLeManual le p x) :
    ¬ ShiftedGridCrossingManual E zero one add mul le p d x
      (∅ : ZFSet.{u}) := by
  intro hCross
  rcases hCross with ⟨a, q, r, hNA, hqPrime, hrPrime, hADQ, hPQR, hxR⟩
  have hField : IsFieldFoundational E zero one add mul := hordered.1
  have hOrder : IsTotalOrderFoundational E le := hordered.2.1
  rcases hField with
    ⟨hGroup, hMulTotal, hOneE, _, hMulComm, _, _, _, _⟩
  rcases hGroup with ⟨hAddTotal, hZeroE, _, _, hAddUnit, _⟩
  have hFieldCopy : IsFieldFoundational E zero one add mul := hordered.1
  have hPrime : IsSubfieldRelationalManual E
      (PrimeSubfieldCoreManual E zero one add mul) zero one add mul :=
    primeSubfieldCore_isSubfield_manual E zero one add mul hFieldCopy
  rcases hPrime with ⟨_, hSub, _, _, _, _, _, _⟩
  have hpE : p ∈ E := hSub hpPrime
  have hdE : d ∈ E := hSub hdPrime
  have hqE : q ∈ E := hSub hqPrime
  have hrE : r ∈ E := hSub hrPrime
  have hFunc : IsFuncFoundational omegaTA E
      (CanonicalNumeralGraphManual E zero one add) :=
    canonicalNumeralGraph_isFunc_manual
      E zero one add hZeroE hOneE hAddTotal
  have hNatZero : (∅ : ZFSet.{u}) ∈ omegaTA := omegaTA_isInductive.1
  have hZeroGraph : ZFSet.pair (∅ : ZFSet.{u}) zero ∈
      CanonicalNumeralGraphManual E zero one add :=
    canonicalNumeralGraph_zero_manual E zero one add hZeroE
  have hAZero : a = zero :=
    funcFoundational_pair_value_unique hFunc hNatZero hNA hZeroGraph
  have hZeroDQ : mul zero d q := by
    simpa only [hAZero] using hADQ
  obtain ⟨t, ⟨htE, hDZeroT⟩, _⟩ :=
    hMulTotal d hdE zero hZeroE
  have hQT : q = t :=
    hMulComm zero d q t hZeroE hdE hZeroDQ hDZeroT
  have hTZero : t = zero :=
    rel_mul_zero_manual E zero one add mul hFieldCopy
      d t hdE htE hDZeroT
  have hQZero : q = zero := hQT.trans hTZero
  have hPZeroR : add p zero r := by
    simpa only [hQZero] using hPQR
  obtain ⟨z, ⟨_hzE, _hPZeroZ⟩, hUnique⟩ :=
    hAddTotal p hpE zero hZeroE
  have hRZ : r = z := (hUnique r ⟨hrE, hPZeroR⟩)
  have hPZ : p = z :=
    (hUnique p ⟨hpE, (hAddUnit p hpE).1⟩)
  have hRP : r = p := hRZ.trans hPZ.symm
  have hxP : StrictFromLeManual le x p := by
    simpa only [hRP] using hxR
  have hPxEq : p = x :=
    hOrder.2.1 p x hpE hxE hpx.1 hxP.1
  exact hpx.2 hPxEq

/-- El primer indice de cruce de la malla trasladada es sucesor.
    A diferencia de la malla anclada en cero, esto vale aunque x<0. -/
theorem prime_shifted_grid_first_successor_manual
    (em : ∀ p : Prop, p ∨ ¬p)
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hordered : IsOrderedFieldFoundational E zero one add mul le)
    (hArch : IsArchimedeanGraphEditorialManual E zero one add le)
    (p d x : ZFSet.{u})
    (hpPrime : p ∈ PrimeSubfieldCoreManual E zero one add mul)
    (hdPrime : d ∈ PrimeSubfieldCoreManual E zero one add mul)
    (hdPos : StrictFromLeManual le zero d)
    (hxE : x ∈ E) (hpx : StrictFromLeManual le p x) :
    ∃ k : ZFSet.{u}, k ∈ omegaTA ∧
      ShiftedGridCrossingManual E zero one add mul le p d x (succ k) ∧
      ¬ ShiftedGridCrossingManual E zero one add mul le p d x k := by
  let P : ZFSet.{u} → Prop :=
    ShiftedGridCrossingManual E zero one add mul le p d x
  have hExists : ∃ n : ZFSet.{u}, n ∈ omegaTA ∧ P n :=
    prime_shifted_grid_cofinal_manual
      E zero one add mul le hordered hArch
      p d x hpPrime hdPrime hdPos hxE hpx
  have hNotZero : ¬P (∅ : ZFSet.{u}) :=
    prime_shifted_grid_zero_not_cross_manual
      E zero one add mul le hordered p d x
      hpPrime hdPrime hxE hpx
  exact omega_least_successor_manual em P hExists hNotZero

/-- Preparacion de la densidad para un intervalo arbitrario (x,y):
    existe un origen primo p<x, un paso primo 0<d<epsilon con
    x+epsilon=y, y un primer cruce en indice sucesor. -/
theorem prime_shifted_small_mesh_successor_manual
    (em : ∀ p : Prop, p ∨ ¬p)
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hordered : IsOrderedFieldFoundational E zero one add mul le)
    (hArch : IsArchimedeanGraphEditorialManual E zero one add le)
    (x y : ZFSet.{u})
    (hxE : x ∈ E) (hyE : y ∈ E)
    (hxy : StrictFromLeManual le x y) :
    ∃ p d epsilon k : ZFSet.{u},
      p ∈ PrimeSubfieldCoreManual E zero one add mul ∧
      d ∈ PrimeSubfieldCoreManual E zero one add mul ∧
      StrictFromLeManual le p x ∧
      StrictFromLeManual le zero d ∧
      epsilon ∈ E ∧ StrictFromLeManual le d epsilon ∧
      add x epsilon y ∧
      k ∈ omegaTA ∧
      ShiftedGridCrossingManual E zero one add mul le p d x (succ k) ∧
      ¬ ShiftedGridCrossingManual E zero one add mul le p d x k := by
  obtain ⟨epsilon, hepsilonE, hepsilonPos, hXepsY⟩ :=
    rel_interval_positive_gap_manual
      E zero one add mul le hordered x y hxE hyE hxy
  obtain ⟨p, hpPrime, hpX⟩ :=
    primeSubfield_coinitial_of_archimedean_manual
      E zero one add mul le hordered hArch x hxE
  obtain ⟨_, _, d, _, _, _, hdPrime, _, hdPos, hdSmall, _, _⟩ :=
    prime_numeral_inverse_below_positive_manual
      E zero one add mul le hordered hArch
      epsilon hepsilonE hepsilonPos
  obtain ⟨k, hk, hCross, hNotCross⟩ :=
    prime_shifted_grid_first_successor_manual
      em E zero one add mul le hordered hArch
      p d x hpPrime hdPrime hdPos hxE hpX
  exact ⟨p, d, epsilon, k, hpPrime, hdPrime, hpX, hdPos,
    hepsilonE, hdSmall, hXepsY, hk, hCross, hNotCross⟩

end TratadoAnalisis.AbstractCompleteness.Density0009
