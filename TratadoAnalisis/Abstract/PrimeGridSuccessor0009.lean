import TratadoAnalisis.Abstract.PrimeGridLeastIndex0009

/-!
# TA-LEAN-0009 / P3c-08 — sucesor de la malla y cota del cruce

Se demuestra la identidad relacional entre productos consecutivos
`nu(succ n) * d = (nu n * d) + d` sin elegir funciones globales.
La prueba usa la ecuacion del grafo canonico y la distributividad.

Si un indice precedente no cruza x, y el sucesor si, y el paso d
es menor que epsilon, ese punto cruzado es menor que x+epsilon.

Todavia NO se demuestra que el primer indice de P3c-07 sea sucesor
para un intervalo arbitrario: ello requiere desplazar el origen de
la malla o tratar cuidadosamente el caso x<0. Por tanto NO se afirma
TA-THM-00036 ni TA-PRO-00078 incondicionalmente.
-/

namespace TratadoAnalisis.AbstractCompleteness.Density0009

universe u

open TratadoAnalisis.AbstractCompleteness.Manual0008
open TratadoAnalisis.Dedekind.FieldPredicates
open TratadoAnalisis.Naturals.Foundational
open TratadoAnalisis.Naturals.Recursion

/-- El orden estricto derivado de <= es transitivo con una cota debil
    a la derecha, a partir de la antisimetría de un orden total. -/
theorem rel_strict_le_trans_grid_manual
    (E : ZFSet.{u}) (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hOrder : IsTotalOrderFoundational E le)
    (a b c : ZFSet.{u})
    (haE : a ∈ E) (hbE : b ∈ E) (hcE : c ∈ E)
    (hab : StrictFromLeManual le a b) (hbc : le b c) :
    StrictFromLeManual le a c := by
  have hac : le a c :=
    hOrder.2.2.1 a b c haE hbE hcE hab.1 hbc
  refine ⟨hac, ?_⟩
  intro heq
  have hba : le b a := by
    simpa only [← heq] using hbc
  exact hab.2 (hOrder.2.1 a b haE hbE hab.1 hba)

/-- Si x no es estrictamente menor que q, entonces q <= x.
    El tercero excluido se recibe expresamente; no se usa Choice. -/
theorem rel_not_strict_reverse_le_grid_manual
    (em : ∀ p : Prop, p ∨ ¬p)
    (E : ZFSet.{u}) (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hOrder : IsTotalOrderFoundational E le)
    (x q : ZFSet.{u})
    (hxE : x ∈ E) (hqE : q ∈ E)
    (hNot : ¬StrictFromLeManual le x q) : le q x := by
  rcases em (x = q) with heq | hne
  · simpa only [heq] using (hOrder.1 q hqE)
  · rcases hOrder.2.2.2 x q hxE hqE with hxq | hqx
    · exact (hNot ⟨hxq, hne⟩).elim
    · exact hqx

/-- Relacion numeral-sucesor y distributividad:
    si a = nu(n), b = nu(succ n), q = a*d y r = b*d,
    entonces todo testigo s de q+d satisface r=s. -/
theorem prime_grid_successor_product_eq_manual
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hordered : IsOrderedFieldFoundational E zero one add mul le)
    (n a b d q r s : ZFSet.{u})
    (hn : n ∈ omegaTA)
    (hNA : ZFSet.pair n a ∈ CanonicalNumeralGraphManual E zero one add)
    (hNSB : ZFSet.pair (succ n) b ∈ CanonicalNumeralGraphManual E zero one add)
    (hdE : d ∈ E)
    (hADQ : mul a d q) (hBDR : mul b d r) (hQDS : add q d s) :
    r = s := by
  rcases hordered.1 with
    ⟨hAddGroup, _, hOneE, _, _, hMulUnit, hDistrib, _, _⟩
  have hAddTotal : IsBinaryOperationFoundational E add := hAddGroup.1
  have hZeroE : zero ∈ E := hAddGroup.2.1
  have hFunc : IsFuncFoundational omegaTA E
      (CanonicalNumeralGraphManual E zero one add) :=
    canonicalNumeralGraph_isFunc_manual
      E zero one add hZeroE hOneE hAddTotal
  have haE : a ∈ E := funcFoundational_value_mem hFunc hNA
  obtain ⟨c, ⟨hcE, hAOneC⟩, _⟩ :=
    hAddTotal a haE one hOneE
  have hNSC : ZFSet.pair (succ n) c ∈
      CanonicalNumeralGraphManual E zero one add :=
    canonicalNumeralGraph_succ_manual
      E zero one add hZeroE hOneE hAddTotal
      hn hNA haE hcE hAOneC
  have hCB : c = b :=
    funcFoundational_pair_value_unique hFunc
      (TA_PRO_00022_succ_closed hn) hNSC hNSB
  have hAOneB : add a one b := by
    simpa only [hCB] using hAOneC
  exact hDistrib.2 a one d b r q d s
    haE hOneE hdE hAOneB hBDR hADQ
    (hMulUnit d hdE).2 hQDS

/-- Los productos de dos indices sucesivos de una malla prima estan
    relacionados por suma relacional del paso d; todos los testigos
    quedan en el subcuerpo primo. -/
theorem prime_grid_successor_closure_manual
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hordered : IsOrderedFieldFoundational E zero one add mul le)
    (n a d q : ZFSet.{u})
    (hn : n ∈ omegaTA)
    (hNA : ZFSet.pair n a ∈ CanonicalNumeralGraphManual E zero one add)
    (hdPrime : d ∈ PrimeSubfieldCoreManual E zero one add mul)
    (hqPrime : q ∈ PrimeSubfieldCoreManual E zero one add mul)
    (hADQ : mul a d q) :
    ∃ b r : ZFSet.{u},
      ZFSet.pair (succ n) b ∈ CanonicalNumeralGraphManual E zero one add ∧
      r ∈ PrimeSubfieldCoreManual E zero one add mul ∧
      mul b d r ∧ add q d r := by
  have hPrime : IsSubfieldRelationalManual E
      (PrimeSubfieldCoreManual E zero one add mul) zero one add mul :=
    primeSubfieldCore_isSubfield_manual E zero one add mul hordered.1
  rcases hPrime with ⟨_, hSub, _, hOnePrime, hAddPrime, hMulPrime, _, _⟩
  have haPrime : a ∈ PrimeSubfieldCoreManual E zero one add mul :=
    TA_COR_00011_numerals_in_prime_manual
      E zero one add mul hordered.1 n a hn hNA
  obtain ⟨b, hbPrime, hAOneB⟩ :=
    hAddPrime a one haPrime hOnePrime
  have haE : a ∈ E := hSub haPrime
  have hbE : b ∈ E := hSub hbPrime
  have hdE : d ∈ E := hSub hdPrime
  have hZeroE : zero ∈ E := hordered.1.1.2.1
  have hOneE : one ∈ E := hordered.1.2.2.1
  have hAddTotal : IsBinaryOperationFoundational E add :=
    hordered.1.1.1
  have hNSB : ZFSet.pair (succ n) b ∈
      CanonicalNumeralGraphManual E zero one add :=
    canonicalNumeralGraph_succ_manual
      E zero one add hZeroE hOneE hAddTotal
      hn hNA haE hbE hAOneB
  obtain ⟨r, hrPrime, hBDR⟩ :=
    hMulPrime b d hbPrime hdPrime
  obtain ⟨s, _hsPrime, hQDS⟩ :=
    hAddPrime q d hqPrime hdPrime
  have hRS : r = s :=
    prime_grid_successor_product_eq_manual
      E zero one add mul le hordered
      n a b d q r s hn hNA hNSB hdE hADQ hBDR hQDS
  have hQDR : add q d r := by
    simpa only [← hRS] using hQDS
  exact ⟨b, r, hNSB, hrPrime, hBDR, hQDR⟩

/-- Una malla cuyo paso d es menor que epsilon no puede dar un salto
    desde q <= x hasta r = q+d sobre la cota x+epsilon. -/
theorem prime_grid_step_upper_bound_manual
    (em : ∀ p : Prop, p ∨ ¬p)
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hordered : IsOrderedFieldFoundational E zero one add mul le)
    (x epsilon q d r top : ZFSet.{u})
    (hxE : x ∈ E) (hepsilonE : epsilon ∈ E)
    (hqE : q ∈ E) (hdE : d ∈ E)
    (hrE : r ∈ E) (htopE : top ∈ E)
    (hNotAbove : ¬StrictFromLeManual le x q)
    (hdSmall : StrictFromLeManual le d epsilon)
    (hQDR : add q d r)
    (hXepsTop : add x epsilon top) :
    StrictFromLeManual le r top := by
  have hqLeX : le q x :=
    rel_not_strict_reverse_le_grid_manual
      em E le hordered.2.1 x q hxE hqE hNotAbove
  obtain ⟨t, ⟨htE, hQepsT⟩, _⟩ :=
    hordered.1.1.1 q hqE epsilon hepsilonE
  have hRltT : StrictFromLeManual le r t :=
    rel_add_left_strict_mono_manual
      E zero one add mul le hordered
      d epsilon q r t hdE hepsilonE hqE hrE htE
      hdSmall hQDR hQepsT
  have hTLeTop : le t top :=
    hordered.2.2.1 q x epsilon t top
      hqE hxE hepsilonE hqLeX hQepsT hXepsTop
  exact rel_strict_le_trans_grid_manual
    E le hordered.2.1 r t top hrE htE htopE hRltT hTLeTop

/-- Si el predecesor no cruza x y el sucesor si, la distribucion
    del producto de numerales y un paso d<epsilon coloca el cruce en
    el intervalo (x,x+epsilon). Es una reduccion explicita que NO
    presupone densidad ni existencia de tal predecesor para todo x. -/
theorem prime_grid_successor_in_interval_manual
    (em : ∀ p : Prop, p ∨ ¬p)
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hordered : IsOrderedFieldFoundational E zero one add mul le)
    (n a b d q r x epsilon top : ZFSet.{u})
    (hn : n ∈ omegaTA)
    (hNA : ZFSet.pair n a ∈ CanonicalNumeralGraphManual E zero one add)
    (hNSB : ZFSet.pair (succ n) b ∈ CanonicalNumeralGraphManual E zero one add)
    (hdPrime : d ∈ PrimeSubfieldCoreManual E zero one add mul)
    (hqPrime : q ∈ PrimeSubfieldCoreManual E zero one add mul)
    (hrPrime : r ∈ PrimeSubfieldCoreManual E zero one add mul)
    (hxE : x ∈ E) (hepsilonE : epsilon ∈ E) (htopE : top ∈ E)
    (hADQ : mul a d q) (hBDR : mul b d r)
    (hMinAtN : ¬(∃ a' q' : ZFSet.{u},
        ZFSet.pair n a' ∈ CanonicalNumeralGraphManual E zero one add ∧
        q' ∈ PrimeSubfieldCoreManual E zero one add mul ∧
        mul a' d q' ∧ StrictFromLeManual le x q'))
    (hxR : StrictFromLeManual le x r)
    (hdSmall : StrictFromLeManual le d epsilon)
    (hXepsTop : add x epsilon top) :
    r ∈ PrimeSubfieldCoreManual E zero one add mul ∧
    StrictFromLeManual le x r ∧ StrictFromLeManual le r top := by
  have hPrime : IsSubfieldRelationalManual E
      (PrimeSubfieldCoreManual E zero one add mul) zero one add mul :=
    primeSubfieldCore_isSubfield_manual E zero one add mul hordered.1
  rcases hPrime with ⟨_, hSub, _, _, hAddPrime, _, _, _⟩
  have hqE : q ∈ E := hSub hqPrime
  have hrE : r ∈ E := hSub hrPrime
  have hdE : d ∈ E := hSub hdPrime
  obtain ⟨s, _hsPrime, hQDS⟩ :=
    hAddPrime q d hqPrime hdPrime
  have hRS : r = s :=
    prime_grid_successor_product_eq_manual
      E zero one add mul le hordered
      n a b d q r s hn hNA hNSB hdE hADQ hBDR hQDS
  have hQDR : add q d r := by
    simpa only [← hRS] using hQDS
  have hNotAbove : ¬StrictFromLeManual le x q := by
    intro hXQ
    exact hMinAtN ⟨a, q, hNA, hqPrime, hADQ, hXQ⟩
  have hBound : StrictFromLeManual le r top :=
    prime_grid_step_upper_bound_manual
      em E zero one add mul le hordered
      x epsilon q d r top hxE hepsilonE hqE hdE hrE htopE
      hNotAbove hdSmall hQDR hXepsTop
  exact ⟨hrPrime, hxR, hBound⟩

end TratadoAnalisis.AbstractCompleteness.Density0009
