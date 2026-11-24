import TratadoAnalisis.Foundations.FunctionSpace
import TratadoAnalisis.Rationals.Construction

/-!
# TA-LEAN-0011 A1 — Sucesiones racionales (§8.1.1–8.1.2)

TA-DEF-00105: el conjunto Q^N contiene funciones conjuntistas completas.
TA-PRO-00107: igualdad término a término.
La evaluación es una relación total y unívoca sobre el dominio.
No se presupone que una sucesión extensional sea computable.
No se utilizan cortaduras, números reales ni completitud de Dedekind.
-/

namespace TratadoAnalisis.Cauchy.RationalSequences

universe u

open TratadoAnalisis.Foundations.FunctionSpace
open TratadoAnalisis.Foundations.FunctionTriple
open TratadoAnalisis.Naturals.Foundational
open TratadoAnalisis.Rationals.Construction

/-- TA-DEF-00105: el conjunto de funciones de N en Q. -/
def rationalSequences : ZFSet.{u} :=
  functionSpace omegaTA rationalsTA

theorem TA_DEF_00105_mem_rationalSequences_iff {s : ZFSet.{u}} :
    s ∈ rationalSequences ↔ IsFunctionTriple omegaTA rationalsTA s :=
  TA_PRO_00014_mem_functionSpace_iff

/-- El conjunto de sucesiones existe con su criterio extensional exacto. -/
theorem TA_DEF_00105_rationalSequences_exists_unique :
    ∃! S : ZFSet.{u}, ∀ s : ZFSet.{u},
      s ∈ S ↔ IsFunctionTriple omegaTA rationalsTA s :=
  TA_PRO_00014_functionSpace_exists_unique omegaTA rationalsTA

/-- q_n = r, como relación de evaluación del triple de la sucesión. -/
abbrev SequenceValue (q n r : ZFSet.{u}) : Prop :=
  FunctionValue omegaTA rationalsTA q n r

theorem sequenceValue_mem {q n r : ZFSet.{u}}
    (hq : q ∈ rationalSequences) (hr : SequenceValue q n r) :
    r ∈ rationalsTA :=
  functionValue_mem hq hr

theorem sequenceValue_exists_unique {q n : ZFSet.{u}}
    (hq : q ∈ rationalSequences) (hn : n ∈ omegaTA) :
    ∃! r : ZFSet.{u}, r ∈ rationalsTA ∧ SequenceValue q n r :=
  functionValue_exists_unique hq hn

theorem sequenceValue_unique {q n r s : ZFSet.{u}}
    (hq : q ∈ rationalSequences) (hn : n ∈ omegaTA)
    (hr : SequenceValue q n r) (hs : SequenceValue q n s) : r = s :=
  functionValue_unique hq hn hr hs

/-- TA-PRO-00107: igualdad de sucesiones exactamente cuando coinciden
    todos los valores correspondientes a un mismo índice. -/
theorem TA_PRO_00107_sequence_eq_iff_values
    {a b : ZFSet.{u}} (ha : a ∈ rationalSequences) (hb : b ∈ rationalSequences) :
    a = b ↔ ∀ n : ZFSet.{u}, n ∈ omegaTA →
      ∀ r s : ZFSet.{u}, SequenceValue a n r →
        SequenceValue b n s → r = s :=
  function_eq_iff_values ha hb

end TratadoAnalisis.Cauchy.RationalSequences
