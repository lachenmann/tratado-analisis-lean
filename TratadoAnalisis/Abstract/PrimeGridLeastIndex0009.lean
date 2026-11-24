import TratadoAnalisis.Abstract.PrimeGridCofinality0009

/-!
# TA-LEAN-0009 / P3c-07 — primer indice de una malla primo-numerica

Se demuestra por induccion en `omegaTA` el principio de minimo para
predicados sobre naturales de von Neumann. El tercero excluido se pasa
expresamente como `em`; no se usa un axioma de eleccion.

Aplicacion: la malla cofinal de P3c-06 tiene un PRIMER indice natural
cuyo multiplo supera la cota indicada. La minimalidad afirma que ningun
indice perteneciente a ese natural tiene la misma propiedad.

Este modulo no prueba todavia el lema de transicion entre numerales
consecutivos ni la densidad de P_E en un intervalo arbitrario.
-/

namespace TratadoAnalisis.AbstractCompleteness.Density0009

universe u

open TratadoAnalisis.AbstractCompleteness.Manual0008
open TratadoAnalisis.Dedekind.FieldPredicates
open TratadoAnalisis.Naturals.Foundational
open TratadoAnalisis.Naturals.Recursion

/-- Todo elemento de un natural de von Neumann construido es natural.
    La prueba es una induccion por el sucesor conjuntista. -/
theorem omega_member_of_member_nat_manual :
    ∀ n : ZFSet.{u}, n ∈ omegaTA →
      ∀ k : ZFSet.{u}, k ∈ n → k ∈ omegaTA := by
  let Q : ZFSet.{u} → Prop := fun n =>
    ∀ k : ZFSet.{u}, k ∈ n → k ∈ omegaTA
  have h0 : Q (∅ : ZFSet.{u}) := by
    intro k hk
    exact (ZFSet.notMem_empty k hk).elim
  have hs : ∀ n : ZFSet.{u}, n ∈ omegaTA → Q n → Q (succ n) := by
    intro n hn ih k hk
    rcases ZFSet.mem_insert_iff.mp hk with hEq | hIn
    · simpa only [hEq] using hn
    · exact ih k hIn
  exact TA_THM_00008_induction Q h0 hs

/-- Si un predicado vale en algun miembro de `succ n`, vale en un
    miembro minimo de ese segmento inicial. No se presupone que P
    sea decidible: se utiliza el parametro explicito `em`. -/
theorem omega_bounded_least_manual
    (em : ∀ p : Prop, p ∨ ¬p)
    (P : ZFSet.{u} → Prop) :
    ∀ n : ZFSet.{u}, n ∈ omegaTA →
      (∃ k : ZFSet.{u}, k ∈ succ n ∧ P k) →
      ∃ m : ZFSet.{u}, m ∈ succ n ∧ P m ∧
        (∀ k : ZFSet.{u}, k ∈ m → ¬P k) := by
  let Q : ZFSet.{u} → Prop := fun n =>
    (∃ k : ZFSet.{u}, k ∈ succ n ∧ P k) →
      ∃ m : ZFSet.{u}, m ∈ succ n ∧ P m ∧
        (∀ k : ZFSet.{u}, k ∈ m → ¬P k)
  have h0 : Q (∅ : ZFSet.{u}) := by
    intro hSome
    rcases hSome with ⟨k, hk, hkP⟩
    have hkZero : k = (∅ : ZFSet.{u}) := by
      rcases ZFSet.mem_insert_iff.mp hk with hEq | hIn
      · exact hEq
      · exact (ZFSet.notMem_empty k hIn).elim
    refine ⟨(∅ : ZFSet.{u}), ?_, ?_, ?_⟩
    · exact ZFSet.mem_insert (∅ : ZFSet.{u}) (∅ : ZFSet.{u})
    · simpa only [hkZero] using hkP
    · intro j hj
      exact (ZFSet.notMem_empty j hj).elim
  have hs : ∀ n : ZFSet.{u}, n ∈ omegaTA → Q n → Q (succ n) := by
    intro n _hn ih hSome
    rcases em (∃ k : ZFSet.{u}, k ∈ succ n ∧ P k) with hEarlier | hNone
    · obtain ⟨m, hmIn, hmP, hmMin⟩ := ih hEarlier
      refine ⟨m, ?_, hmP, hmMin⟩
      exact ZFSet.mem_insert_of_mem (succ n) hmIn
    · obtain ⟨k, hk, hkP⟩ := hSome
      have hkSucc : k = succ n := by
        rcases ZFSet.mem_insert_iff.mp hk with hEq | hIn
        · exact hEq
        · exact (hNone ⟨k, hIn, hkP⟩).elim
      refine ⟨succ n, ZFSet.mem_insert (succ n) (succ n), ?_, ?_⟩
      · simpa only [hkSucc] using hkP
      · intro j hj hjP
        exact hNone ⟨j, hj, hjP⟩
  exact TA_THM_00008_induction Q h0 hs

/-- Principio de minimo sobre `omegaTA`, derivado de Peano y de la
    estructura de segmentos de von Neumann; sin postular buen orden. -/
theorem omega_least_manual
    (em : ∀ p : Prop, p ∨ ¬p)
    (P : ZFSet.{u} → Prop)
    (hExists : ∃ n : ZFSet.{u}, n ∈ omegaTA ∧ P n) :
    ∃ m : ZFSet.{u}, m ∈ omegaTA ∧ P m ∧
      (∀ k : ZFSet.{u}, k ∈ m → ¬P k) := by
  obtain ⟨n, hn, hnP⟩ := hExists
  obtain ⟨m, hmIn, hmP, hmMin⟩ :=
    omega_bounded_least_manual em P n hn
      ⟨n, ZFSet.mem_insert n n, hnP⟩
  have hmNat : m ∈ omegaTA := by
    rcases ZFSet.mem_insert_iff.mp hmIn with hEq | hIn
    · simpa only [hEq] using hn
    · exact omega_member_of_member_nat_manual n hn m hIn
  exact ⟨m, hmNat, hmP, hmMin⟩

/-- Si cero no satisface P, el primer indice que satisface P es un
    sucesor y su predecesor ya no satisface P. -/
theorem omega_least_successor_manual
    (em : ∀ p : Prop, p ∨ ¬p)
    (P : ZFSet.{u} → Prop)
    (hExists : ∃ n : ZFSet.{u}, n ∈ omegaTA ∧ P n)
    (hNotZero : ¬P (∅ : ZFSet.{u})) :
    ∃ k : ZFSet.{u}, k ∈ omegaTA ∧ P (succ k) ∧ ¬P k := by
  obtain ⟨m, hmNat, hmP, hmMin⟩ :=
    omega_least_manual em P hExists
  rcases TA_THM_00011_predecessor hmNat with hZero | hSucc
  · exact (hNotZero (hZero ▸ hmP)).elim
  · obtain ⟨k, ⟨hkNat, hmk⟩, _⟩ := hSucc
    have hkNot : ¬P k := by
      apply hmMin k
      rw [hmk]
      exact ZFSet.mem_insert k k
    refine ⟨k, hkNat, ?_, hkNot⟩
    simpa only [hmk] using hmP

/-- Primer indice de la malla primo-numerica cofinal: existe un
    producto en P_E mayor que x, y ningun indice anterior permite
    obtener otro producto de esta forma mayor que x. -/
theorem prime_grid_first_crossing_manual
    (em : ∀ p : Prop, p ∨ ¬p)
    (E zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop)
    (hordered : IsOrderedFieldFoundational E zero one add mul le)
    (hArch : IsArchimedeanGraphEditorialManual E zero one add le)
    (d : ZFSet.{u})
    (hdPrime : d ∈ PrimeSubfieldCoreManual E zero one add mul)
    (hdPos : StrictFromLeManual le zero d)
    (x : ZFSet.{u}) (hxE : x ∈ E) :
    ∃ n : ZFSet.{u}, n ∈ omegaTA ∧
      (∃ y q : ZFSet.{u},
        ZFSet.pair n y ∈ CanonicalNumeralGraphManual E zero one add ∧
        q ∈ PrimeSubfieldCoreManual E zero one add mul ∧
        mul y d q ∧ StrictFromLeManual le x q) ∧
      (∀ k : ZFSet.{u}, k ∈ n →
        ¬(∃ y q : ZFSet.{u},
          ZFSet.pair k y ∈ CanonicalNumeralGraphManual E zero one add ∧
          q ∈ PrimeSubfieldCoreManual E zero one add mul ∧
          mul y d q ∧ StrictFromLeManual le x q)) := by
  let P : ZFSet.{u} → Prop := fun n =>
    ∃ y q : ZFSet.{u},
      ZFSet.pair n y ∈ CanonicalNumeralGraphManual E zero one add ∧
      q ∈ PrimeSubfieldCoreManual E zero one add mul ∧
      mul y d q ∧ StrictFromLeManual le x q
  obtain ⟨n, y, q, hn, hNY, hqPrime, hYDq, hxq⟩ :=
    prime_canonical_multiples_cofinal_manual
      E zero one add mul le hordered hArch d hdPrime hdPos x hxE
  have hSome : ∃ n : ZFSet.{u}, n ∈ omegaTA ∧ P n :=
    ⟨n, hn, ⟨y, q, hNY, hqPrime, hYDq, hxq⟩⟩
  exact omega_least_manual em P hSome

/-- Malla de paso positivo menor que epsilon, y primer indice cuyo
    producto supera x. No se afirma todavia que ese producto sea < y. -/
theorem prime_small_mesh_first_crossing_manual
    (em : ∀ p : Prop, p ∨ ¬p)
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
      mul y d q ∧ StrictFromLeManual le x q ∧
      (∀ k : ZFSet.{u}, k ∈ n →
        ¬(∃ y' q' : ZFSet.{u},
          ZFSet.pair k y' ∈ CanonicalNumeralGraphManual E zero one add ∧
          q' ∈ PrimeSubfieldCoreManual E zero one add mul ∧
          mul y' d q' ∧ StrictFromLeManual le x q')) := by
  obtain ⟨d, _, _, _, hdPrime, hdPos, hdSmall, _, _, _, _, _⟩ :=
    prime_small_mesh_cofinal_manual
      E zero one add mul le hordered hArch
      epsilon x hepsilonE hepsilonPos hxE
  obtain ⟨n, hn, hP, hMin⟩ :=
    prime_grid_first_crossing_manual
      em E zero one add mul le hordered hArch
      d hdPrime hdPos x hxE
  obtain ⟨y, q, hNY, hqPrime, hYDq, hxq⟩ := hP
  exact ⟨d, n, y, q, hdPrime, hdPos, hdSmall,
    hn, hNY, hqPrime, hYDq, hxq, hMin⟩

end TratadoAnalisis.AbstractCompleteness.Density0009
