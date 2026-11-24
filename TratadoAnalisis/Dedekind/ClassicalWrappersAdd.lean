import TratadoAnalisis.Dedekind.AdditiveGroup
import TratadoAnalisis.Dedekind.Boundary
import TratadoAnalisis.Dedekind.Addition

namespace TratadoAnalisis.Dedekind.ClassicalWrappersAdd
universe u
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Foundations.FunctionTriple
open TratadoAnalisis.Dedekind.Definition
open TratadoAnalisis.Dedekind.Addition

/-- Envoltorio metateórico; no expresa elección conjuntista del tratado. -/
theorem TA_PRO_00084_dedAdd_mem {α β : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) (hβ : β ∈ dedekindCutsTA) :
    dedAdd α β ∈ dedekindCutsTA :=
  Addition.TA_PRO_00084_dedAdd_mem Classical.em hα hβ

theorem TA_DEF_00086_dedAddGraph_isFunc :
    IsFuncFoundational
      (cartesianProductFoundational (dedekindCutsTA : ZFSet.{u}) dedekindCutsTA)
      dedekindCutsTA dedAddGraph :=
  Addition.TA_DEF_00086_dedAddGraph_isFunc Classical.em

theorem TA_DEF_00086_dedAddFunction_isTriple :
    IsFunctionTriple
      (cartesianProductFoundational (dedekindCutsTA : ZFSet.{u}) dedekindCutsTA)
      dedekindCutsTA dedAddFunction :=
  Addition.TA_DEF_00086_dedAddFunction_isTriple Classical.em

end TratadoAnalisis.Dedekind.ClassicalWrappersAdd

namespace TratadoAnalisis.Dedekind.ClassicalWrappersAdd
universe u
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Dedekind.Definition

theorem TA_LEM_00022_boundary_approximation {α h : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) (hh : h ∈ rationalsTA)
    (hpos : RatLT ratZero h) :
    ∃ a : ZFSet.{u}, a ∈ α ∧
      ∃ ah : ZFSet.{u}, RatAdd a h ah ∧ ah ∉ α :=
  Boundary.TA_LEM_00022_boundary_approximation Classical.em hα hh hpos

end TratadoAnalisis.Dedekind.ClassicalWrappersAdd

namespace TratadoAnalisis.Dedekind.ClassicalWrappersAdd
universe u
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Foundations.FunctionTriple
open TratadoAnalisis.Dedekind.Definition
open TratadoAnalisis.Dedekind.Addition
open TratadoAnalisis.Dedekind.Negation
open TratadoAnalisis.Dedekind.AdditiveGroup

theorem TA_PRO_00087_dedNeg_mem {α : ZFSet.{u}} (hα : α ∈ dedekindCutsTA) :
    dedNeg α ∈ dedekindCutsTA :=
  Negation.TA_PRO_00087_dedNeg_mem Classical.em hα

theorem TA_DEF_00089_dedNegGraph_isFunc :
    IsFuncFoundational (dedekindCutsTA : ZFSet.{u}) dedekindCutsTA dedNegGraph :=
  Negation.TA_DEF_00089_dedNegGraph_isFunc Classical.em

theorem TA_DEF_00089_dedNegFunction_isTriple :
    IsFunctionTriple (dedekindCutsTA : ZFSet.{u}) dedekindCutsTA dedNegFunction :=
  Negation.TA_DEF_00089_dedNegFunction_isTriple Classical.em

theorem TA_PRO_00088_dedAdd_neg {α : ZFSet.{u}} (hα : α ∈ dedekindCutsTA) :
    dedAdd α (dedNeg α) = dedZero :=
  Negation.TA_PRO_00088_dedAdd_neg Classical.em hα

theorem TA_COR_00020_dedAdd_neg_bilateral {α : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) :
    dedAdd α (dedNeg α) = dedZero ∧ dedAdd (dedNeg α) α = dedZero :=
  AdditiveGroup.TA_COR_00020_dedAdd_neg_bilateral Classical.em hα

theorem TA_THM_00043_additive_group_package  :
    (∀ α β : ZFSet.{u}, α ∈ dedekindCutsTA → β ∈ dedekindCutsTA →
      dedAdd α β ∈ dedekindCutsTA) ∧
    (dedZero : ZFSet.{u}) ∈ dedekindCutsTA ∧
    (∀ α : ZFSet.{u}, α ∈ dedekindCutsTA →
      dedNeg α ∈ dedekindCutsTA ∧
      dedAdd α (dedNeg α) = dedZero ∧ dedAdd (dedNeg α) α = dedZero) ∧
    (∀ α β γ : ZFSet.{u}, α ∈ dedekindCutsTA → β ∈ dedekindCutsTA →
      γ ∈ dedekindCutsTA →
      dedAdd (dedAdd α β) γ = dedAdd α (dedAdd β γ)) ∧
    (∀ α : ZFSet.{u}, α ∈ dedekindCutsTA →
      dedAdd α dedZero = α ∧ dedAdd dedZero α = α) ∧
    (∀ α β : ZFSet.{u}, α ∈ dedekindCutsTA → β ∈ dedekindCutsTA →
      dedAdd α β = dedAdd β α) :=
  AdditiveGroup.TA_THM_00043_additive_group_package Classical.em

theorem TA_PRO_00089_dedAdd_cancel_right {α β γ : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) (hβ : β ∈ dedekindCutsTA)
    (hγ : γ ∈ dedekindCutsTA) (he : dedAdd α γ = dedAdd β γ) : α = β :=
  AdditiveGroup.TA_PRO_00089_dedAdd_cancel_right Classical.em hα hβ hγ he

theorem TA_PRO_00089_dedAdd_cancel_left {α β γ : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) (hβ : β ∈ dedekindCutsTA)
    (hγ : γ ∈ dedekindCutsTA) (he : dedAdd γ α = dedAdd γ β) : α = β :=
  AdditiveGroup.TA_PRO_00089_dedAdd_cancel_left Classical.em hα hβ hγ he

theorem dedSub_mem {α β : ZFSet.{u}} (hα : α ∈ dedekindCutsTA)
    (hβ : β ∈ dedekindCutsTA) : dedSub α β ∈ dedekindCutsTA :=
  AdditiveGroup.dedSub_mem Classical.em hα hβ

theorem dedSubGraph_isFunc :
    IsFuncFoundational
      (cartesianProductFoundational (dedekindCutsTA : ZFSet.{u}) dedekindCutsTA)
      dedekindCutsTA dedSubGraph :=
  AdditiveGroup.dedSubGraph_isFunc Classical.em

theorem dedSubFunction_isTriple :
    IsFunctionTriple
      (cartesianProductFoundational (dedekindCutsTA : ZFSet.{u}) dedekindCutsTA)
      dedekindCutsTA dedSubFunction :=
  AdditiveGroup.dedSubFunction_isTriple Classical.em

end TratadoAnalisis.Dedekind.ClassicalWrappersAdd
