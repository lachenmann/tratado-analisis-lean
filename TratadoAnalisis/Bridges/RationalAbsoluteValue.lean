import TratadoAnalisis.Rationals.AbsoluteValue
import TratadoAnalisis.Abstract.AbsoluteValue

/-!
# Puente de cotejo: valor absoluto racional y abstracto

Este módulo se audita separadamente. No se importa en ninguna
fuente matemática de Cauchy. El predicado racional independiente
es exactamente la especialización de TA-DEF-00071 de v0.1.2.
-/

namespace TratadoAnalisis.Bridges.RationalAbsoluteValue

universe u

open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.Signs
open TratadoAnalisis.Rationals.AbsoluteValue
open TratadoAnalisis.AbstractCompleteness.Manual0008
open TratadoAnalisis.AbstractCompleteness.AbsoluteValue

theorem ratAbs_iff_abstract {x a : ZFSet.{u}} :
    RatAbs x a ↔ IsAbsoluteValue rationalsTA ratZero RatAdd RatLE x a := by
  constructor
  · rintro ⟨nx, hn, ha, hcase, hxa, hna⟩
    have hx := (mem_ratNegGraph.mp hn).1
    have hnx := funcFoundational_value_mem ratNegGraph_isFunc hn
    have hs := ratAdd_neg_right_rel hx hn
    exact ⟨nx, ⟨hx, hnx, hs, ratAdd_comm_rel hx hnx hs⟩,
      ha, hcase, hxa, hna⟩
  · rintro ⟨nx, hn, ha, hcase, hxa, hna⟩
    exact ⟨nx, ratNeg_of_add_zero hn.1 hn.2.1 hn.2.2.1, ha, hcase, hxa, hna⟩

end TratadoAnalisis.Bridges.RationalAbsoluteValue
