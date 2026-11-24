import TratadoAnalisis.Dedekind.FieldPredicates

namespace TratadoAnalisis.Dedekind.Field
universe u
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.Field
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.OrderedFieldCompatibility
open TratadoAnalisis.Rationals.StrictOrder
open TratadoAnalisis.Rationals.NoSupremumSqrtTwo
open TratadoAnalisis.Rationals.Signs
open TratadoAnalisis.Rationals.Division
open TratadoAnalisis.Rationals.PositiveProducts
open TratadoAnalisis.Rationals.Trichotomy
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.SquareMonotonicity
open TratadoAnalisis.Rationals.InverseOrder
open TratadoAnalisis.Rationals.DifferenceOrder
open TratadoAnalisis.Rationals.PositiveBounds
open TratadoAnalisis.Dedekind.Definition
open TratadoAnalisis.Dedekind.Order
open TratadoAnalisis.Dedekind.RationalSection
open TratadoAnalisis.Dedekind.Addition
open TratadoAnalisis.Dedekind.Negation
open TratadoAnalisis.Dedekind.AdditiveGroup
open TratadoAnalisis.Dedekind.Positivity
open TratadoAnalisis.Dedekind.PositiveMultiplication
open TratadoAnalisis.Dedekind.Signs
open TratadoAnalisis.Dedekind.Multiplication
open TratadoAnalisis.Dedekind.Unit
open TratadoAnalisis.Foundations.FunctionTriple

open TratadoAnalisis.Dedekind.FieldPredicates
open TratadoAnalisis.Dedekind.Distributivity
open TratadoAnalisis.Dedekind.MultiplicativeLaws
open TratadoAnalisis.Dedekind.Nonzero
open TratadoAnalisis.Dedekind.Inverse

def CutAdd (x y z : ZFSet.{u}) : Prop := z = dedAdd x y

def CutMul (x y z : ZFSet.{u}) : Prop := z = dedMul x y

theorem cutAdd_isBinary (em : ∀ p : Prop, p ∨ ¬p) :
    IsBinaryOperationFoundational (dedekindCutsTA : ZFSet.{u}) CutAdd := by
  intro x hx y hy
  refine ⟨dedAdd x y, ⟨TA_PRO_00084_dedAdd_mem em hx hy, rfl⟩, ?_⟩
  intro z hz
  exact hz.2

theorem cutMul_isBinary (em : ∀ p : Prop, p ∨ ¬p) :
    IsBinaryOperationFoundational (dedekindCutsTA : ZFSet.{u}) CutMul := by
  intro x hx y hy
  refine ⟨dedMul x y, ⟨TA_PRO_00094_dedSignedMul_mem em hx hy, rfl⟩, ?_⟩
  intro z hz
  exact hz.2

theorem cutAdd_group (em : ∀ p : Prop, p ∨ ¬p) :
    IsAbelianGroupFoundational (dedekindCutsTA : ZFSet.{u}) dedZero CutAdd := by
  refine ⟨cutAdd_isBinary em, dedZero_mem, ?_, ?_, ?_, ?_⟩
  · rintro x y z xy lhs yz rhs hx hy hz rfl rfl rfl rfl
    exact TA_THM_00041_dedAdd_assoc hx hy hz
  · rintro x y xy yx hx hy rfl rfl
    exact TA_THM_00042_dedAdd_comm hx hy
  · intro x hx
    exact ⟨(TA_PRO_00086_dedZero_neutral hx).1.symm, (TA_PRO_00086_dedZero_neutral hx).2.symm⟩
  · intro x hx
    exact ⟨dedNeg x, TA_PRO_00087_dedNeg_mem em hx,
      (TA_COR_00020_dedAdd_neg_bilateral em hx).1.symm,
      (TA_COR_00020_dedAdd_neg_bilateral em hx).2.symm⟩

theorem TA_THM_00053_dedekind_field (em : ∀ p : Prop, p ∨ ¬p) :
    IsFieldFoundational (dedekindCutsTA : ZFSet.{u}) dedZero dedOne CutAdd CutMul := by
  refine ⟨cutAdd_group em, cutMul_isBinary em, dedOne_mem, ?_, ?_, ?_, ?_, TA_PRO_00096_zero_ne_one, ?_⟩
  · rintro x y z xy lhs yz rhs hx hy hz rfl rfl rfl rfl
    exact TA_THM_00051_dedMul_assoc em hx hy hz
  · rintro x y xy yx hx hy rfl rfl
    exact TA_THM_00050_dedMul_comm hx hy
  · intro x hx
    exact ⟨(TA_THM_00044_dedMul_one em hx).1.symm, (TA_THM_00044_dedMul_one em hx).2.symm⟩
  · constructor
    · rintro x y z yz lhs xy xz rhs hx hy hz rfl rfl rfl rfl rfl
      exact (TA_THM_00052_dedMul_distrib em hx hy hz).1
    · rintro x y z xy lhs xz yz rhs hx hy hz rfl rfl rfl rfl rfl
      exact (TA_THM_00052_dedMul_distrib em hz hx hy).2
  · intro x hx hx0
    have hn := TA_DEF_00101_mem_nonzeroCuts_iff.mpr ⟨hx, hx0⟩
    exact ⟨dedInvValue x, (TA_DEF_00101_mem_nonzeroCuts_iff.mp (TA_PRO_00100_signedInv_mem em hn)).1,
      (TA_THM_00046_inverse_law em hn).1.symm, (TA_THM_00046_inverse_law em hn).2.symm⟩


end TratadoAnalisis.Dedekind.Field
