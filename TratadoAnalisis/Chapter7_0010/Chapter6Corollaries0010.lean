import TratadoAnalisis.Dedekind.EmbeddingField

/-! TA-LEAN-0010 / P05: cierre de dos corolarios del capitulo 6.
    Independiente de P00--P04. -/
namespace TratadoAnalisis.Chapter7_0010
universe u

open TratadoAnalisis.Dedekind.Definition
open TratadoAnalisis.Dedekind.Addition
open TratadoAnalisis.Dedekind.Negation
open TratadoAnalisis.Dedekind.AdditiveGroup
open TratadoAnalisis.Dedekind.Division
open TratadoAnalisis.Dedekind.EmbeddingField
open TratadoAnalisis.Dedekind.Embedding
open TratadoAnalisis.Dedekind.RationalSection
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Division
open TratadoAnalisis.Rationals.OrderDefinition

/-- TA-COR-00137: unicidad del opuesto aditivo. -/
theorem TA_COR_00137_ded_neg_unique_0010
    (em : ∀ p : Prop, p ∨ ¬p)
    (alpha beta : ZFSet.{u})
    (halpha : alpha ∈ dedekindCutsTA)
    (hbeta : beta ∈ dedekindCutsTA)
    (hadd : dedAdd alpha beta = dedZero) :
    beta = dedNeg alpha := by
  apply TA_PRO_00089_dedAdd_cancel_left em
    hbeta (TA_PRO_00087_dedNeg_mem em halpha) halpha
  exact hadd.trans ((TA_COR_00020_dedAdd_neg_bilateral em halpha).1.symm)

/-- TA-COR-00138: inmersion de la division racional, con no-nulidad
    del denominador en el modelo de Dedekind. -/
theorem TA_COR_00138_rational_division_0010
    (em : ∀ p : Prop, p ∨ ¬p)
    (p q d : ZFSet.{u})
    (hp : p ∈ rationalsTA)
    (hq : q ∈ rationalsTA)
    (hq0 : q ≠ ratZero)
    (hd : RatDiv p q d) :
    rationalSection q ≠ dedZero ∧
      rationalSection d =
        dedDiv (rationalSection p) (rationalSection q) := by
  constructor
  · intro he
    have hzero : rationalSection (ratZero : ZFSet.{u}) = dedZero :=
      (TA_COR_00023_section_laws).1
    have hEq : rationalSection q = rationalSection ratZero :=
      he.trans hzero.symm
    exact hq0 (TA_COR_00016_rationalSection_injective hq
      ratZero_mem_rationalsTA hEq)
  · exact rationalSection_div em hp hq hq0 hd

end TratadoAnalisis.Chapter7_0010
