import TratadoAnalisis.Chapter7_0010.AlphaTwoOrderBounds0010
import TratadoAnalisis.Chapter7_0010.AlphaTwoSquareLower0010
import TratadoAnalisis.Chapter7_0010.AlphaTwoSquareSandwich0010
import TratadoAnalisis.Chapter7_0010.AlphaTwoSquareUpper0010
import TratadoAnalisis.Chapter7_0010.Chapter6Corollaries0010
import TratadoAnalisis.Chapter7_0010.Completeness0010
import TratadoAnalisis.Chapter7_0010.Completion0010
import TratadoAnalisis.Chapter7_0010.Consequences0010
import TratadoAnalisis.Chapter7_0010.CutPosition0010
import TratadoAnalisis.Chapter7_0010.SqrtTwoReadiness0010
import TratadoAnalisis.Chapter7_0010.SupremumBridge0010
import TratadoAnalisis.Chapter7_0010.I03EditorialBridges0010
import TratadoAnalisis.Abstract.RationalImagePrep0009
import TratadoAnalisis.Chapter7_0010.N05PositiveSquareUniqueness
import TratadoAnalisis.Abstract.RationalImageGraphBridge0009
import TratadoAnalisis.Abstract.RationalImageSubfield0009
import TratadoAnalisis.Abstract.PrimeDensityReduction0009
import TratadoAnalisis.Abstract.PrimeSubfieldConstruction0009
import TratadoAnalisis.Abstract.PrimeNumeralCofinality0009
import TratadoAnalisis.Abstract.PrimeDenominatorPrep0009
import TratadoAnalisis.Abstract.PrimeInversePositivity0009
import TratadoAnalisis.Abstract.PrimeReciprocalOrder0009
import TratadoAnalisis.Abstract.PrimeLocalRefinement0009
import TratadoAnalisis.Abstract.PrimeGridCofinality0009
import TratadoAnalisis.Abstract.PrimeGridLeastIndex0009
import TratadoAnalisis.Abstract.PrimeGridSuccessor0009
import TratadoAnalisis.Abstract.PrimeShiftedGrid0009
import TratadoAnalisis.Abstract.PrimeDensityClosure0009

import TratadoAnalisis.Abstract.ArchimedeanEditorialBridge0008
import TratadoAnalisis.Abstract.InfimumManual0008
import TratadoAnalisis.Dedekind.UnionManual0008

import TratadoAnalisis.Dedekind.ClassicalWrappersField
import TratadoAnalisis.Dedekind.EmbeddingField
import TratadoAnalisis.Dedekind.OrderedField
import TratadoAnalisis.Dedekind.Field
import TratadoAnalisis.Dedekind.FieldPredicates
import TratadoAnalisis.Dedekind.Distributivity
import TratadoAnalisis.Dedekind.MultiplicativeLaws
import TratadoAnalisis.Dedekind.ProductSignLaws
import TratadoAnalisis.Dedekind.AdditiveIdentities
import TratadoAnalisis.Dedekind.PositiveDistributivity
import TratadoAnalisis.Dedekind.PositiveProductLaws
import TratadoAnalisis.Dedekind.ClassicalWrappersInv
import TratadoAnalisis.Dedekind.Division
import TratadoAnalisis.Dedekind.Inverse
import TratadoAnalisis.Dedekind.PositiveInverseLaw
import TratadoAnalisis.Dedekind.PositiveInversePrep
import TratadoAnalisis.Dedekind.MultiplicativeOrder
import TratadoAnalisis.Dedekind.TranslationOrder
import TratadoAnalisis.Dedekind.PositiveInverse
import TratadoAnalisis.Dedekind.Nonzero
import TratadoAnalisis.Rationals.PositiveBounds
import TratadoAnalisis.Rationals.DifferenceOrder
import TratadoAnalisis.Rationals.InverseOrder
import TratadoAnalisis.Dedekind.ClassicalWrappersMul
import TratadoAnalisis.Dedekind.Unit
import TratadoAnalisis.Dedekind.Multiplication
import TratadoAnalisis.Dedekind.Signs
import TratadoAnalisis.Dedekind.PositiveMultiplication
import TratadoAnalisis.Dedekind.Positivity
import TratadoAnalisis.Rationals.PositiveProducts
import TratadoAnalisis.Dedekind.AdditiveGroup
import TratadoAnalisis.Dedekind.Boundary
import TratadoAnalisis.Rationals.Archimedean
import TratadoAnalisis.Rationals.NatEmbedding
import TratadoAnalisis.Dedekind.ClassicalWrappersAdd
import TratadoAnalisis.Dedekind.Addition
import TratadoAnalisis.Rationals.Division
import TratadoAnalisis.Dedekind.EmbeddingTriple
import TratadoAnalisis.Dedekind.Definition
import TratadoAnalisis.Rationals.Density
import TratadoAnalisis.Dedekind.RationalSection
import TratadoAnalisis.Dedekind.ClassicalWrappers
import TratadoAnalisis.Dedekind.AlphaTwo
import TratadoAnalisis.Dedekind.Embedding
import TratadoAnalisis.Rationals.Field
import TratadoAnalisis.Rationals.IrrationalitySqrtTwo
import TratadoAnalisis.Rationals.SquareMonotonicity
import TratadoAnalisis.Rationals.SqrtTwoSet
import TratadoAnalisis.Rationals.NoSupremumSqrtTwo
import TratadoAnalisis.Rationals.IrrationalityPrep
import TratadoAnalisis.Rationals.StrictOrder
import TratadoAnalisis.Rationals.NoZeroDivisors
import TratadoAnalisis.Rationals.OrderedFieldCompatibility
import TratadoAnalisis.Rationals.TotalOrder
import TratadoAnalisis.Rationals.OrderDefinition
import TratadoAnalisis.Rationals.OrderWellDefined
import TratadoAnalisis.Rationals.PositiveDenominator
import TratadoAnalisis.Rationals.OrderPrep
import TratadoAnalisis.Naturals.Structural
import TratadoAnalisis.Naturals.MathlibCheck
import TratadoAnalisis.Naturals.ZFCBridge
import TratadoAnalisis.Naturals.Foundational
import TratadoAnalisis.Naturals.Recursion
import TratadoAnalisis.Naturals.ArithmeticBridge
import TratadoAnalisis.Integers.Construction
import TratadoAnalisis.Integers.Operations
import TratadoAnalisis.Integers.Multiplication
import TratadoAnalisis.Integers.Algebra
import TratadoAnalisis.Integers.Domain
import TratadoAnalisis.Integers.Order
import TratadoAnalisis.Rationals.IntegerPrep
import TratadoAnalisis.Rationals.Construction
import TratadoAnalisis.Rationals.Additive
import TratadoAnalisis.Rationals.Multiplicative
import TratadoAnalisis.Rationals.Algebra

/-!
# Auditoría de axiomas — TA-LEAN-0001 / TA-LEAN-0002

Ejecutar con:

    lake env lean TratadoAnalisis/Audit.lean

Las líneas `#print axioms` inspeccionan dependencias metateóricas de Lean.
No deben confundirse con `choice-use` del tratado.
-/

#print axioms TratadoAnalisis.Naturals.Structural.TA_THM_00014_add_assoc
#print axioms TratadoAnalisis.Naturals.Structural.TA_THM_00015_add_comm
#print axioms TratadoAnalisis.Naturals.MathlibCheck.TA_THM_00014_mathlib_check
#print axioms TratadoAnalisis.Naturals.ZFCBridge.TA_LEAN_OMEGA_isInductive

#print axioms TratadoAnalisis.Naturals.Foundational.TA_PRO_00019_exists_inductive
#print axioms TratadoAnalisis.Naturals.Foundational.TA_PRO_00020_omegaKernel_isInductive
#print axioms TratadoAnalisis.Naturals.Foundational.TA_THM_00006_omegaKernel_minimal
#print axioms TratadoAnalisis.Naturals.Foundational.TA_THM_00007_omegaKernel_independent
#print axioms TratadoAnalisis.Naturals.Foundational.TA_THM_00008_induction
#print axioms TratadoAnalisis.Naturals.Foundational.TA_PRO_00023_succ_ne_zero

#print axioms TratadoAnalisis.Naturals.Foundational.TA_PRO_00021_transitive_irreflexive
#print axioms TratadoAnalisis.Naturals.Foundational.TA_THM_00009_succ_injective
#print axioms TratadoAnalisis.Naturals.Foundational.TA_THM_00010_peano

#print axioms TratadoAnalisis.Naturals.Recursion.TA_THM_00011_predecessor
#print axioms TratadoAnalisis.Naturals.Recursion.TA_PRO_00024_restriction
#print axioms TratadoAnalisis.Naturals.Recursion.TA_PRO_00024_restriction_foundational
#print axioms TratadoAnalisis.Naturals.Recursion.IsFiniteApproximation
#print axioms TratadoAnalisis.Naturals.Recursion.succ_not_mem_own_segment
#print axioms TratadoAnalisis.Naturals.Recursion.extendGraphFoundational_isFunc
#print axioms TratadoAnalisis.Naturals.Recursion.extendFiniteApproximation_given
#print axioms TratadoAnalisis.Naturals.Recursion.TA_LEM_00004_extension_exists
#print axioms TratadoAnalisis.Naturals.Recursion.TA_LEM_00004_extension_unique
#print axioms TratadoAnalisis.Naturals.Recursion.TA_THM_00012_zero
#print axioms TratadoAnalisis.Naturals.Recursion.finiteApproximation_restrict_succ
#print axioms TratadoAnalisis.Naturals.Recursion.TA_THM_00012_finite_approximations
#print axioms TratadoAnalisis.Naturals.Recursion.TA_LEM_00005_coherence
#print axioms TratadoAnalisis.Naturals.Recursion.pair_mem_pairAmbient
#print axioms TratadoAnalisis.Naturals.Recursion.globalRecursionGraph_isFunc
#print axioms TratadoAnalisis.Naturals.Recursion.globalRecursionGraph_zero
#print axioms TratadoAnalisis.Naturals.Recursion.globalRecursionGraph_succ
#print axioms TratadoAnalisis.Naturals.Recursion.globalRecursionGraph_equations
#print axioms TratadoAnalisis.Naturals.Recursion.globalRecursionGraph_unique
#print axioms TratadoAnalisis.Naturals.Recursion.TA_THM_00013_global_recursion
#print axioms TratadoAnalisis.Naturals.Recursion.mem_cartesianProductFoundational
#print axioms TratadoAnalisis.Naturals.Recursion.parameterStepGraph_mem
#print axioms TratadoAnalisis.Naturals.Recursion.parameterStepGraph_isFunc
#print axioms TratadoAnalisis.Naturals.Recursion.parameterizedRecursionGraph_mem
#print axioms TratadoAnalisis.Naturals.Recursion.parameterizedRecursionGraph_isFunc
#print axioms TratadoAnalisis.Naturals.Recursion.parameterizedRecursionGraph_zero
#print axioms TratadoAnalisis.Naturals.Recursion.parameterizedRecursionGraph_succ
#print axioms TratadoAnalisis.Naturals.Recursion.parameterizedRecursionGraph_equations
#print axioms TratadoAnalisis.Naturals.Recursion.parameterizedRecursionGraph_unique
#print axioms TratadoAnalisis.Naturals.Recursion.TA_COR_00002_parameterized_recursion
#print axioms TratadoAnalisis.Naturals.Recursion.natAddBaseGraph_isFunc
#print axioms TratadoAnalisis.Naturals.Recursion.natAddStepGraph_isFunc
#print axioms TratadoAnalisis.Naturals.Recursion.natAddGraph_isFunc
#print axioms TratadoAnalisis.Naturals.Recursion.natAddGraph_zero
#print axioms TratadoAnalisis.Naturals.Recursion.natAddGraph_succ
#print axioms TratadoAnalisis.Naturals.Recursion.TA_DEF_00036_addition
#print axioms TratadoAnalisis.Naturals.Recursion.natMulBaseGraph_isFunc
#print axioms TratadoAnalisis.Naturals.Recursion.natMulStepGraph_isFunc
#print axioms TratadoAnalisis.Naturals.Recursion.natMulGraph_isFunc
#print axioms TratadoAnalisis.Naturals.Recursion.natMulGraph_zero
#print axioms TratadoAnalisis.Naturals.Recursion.natMulGraph_succ
#print axioms TratadoAnalisis.Naturals.Recursion.natMulGraph_equations
#print axioms TratadoAnalisis.Naturals.Recursion.TA_DEF_00037_multiplication

#print axioms TratadoAnalisis.Naturals.ArithmeticBridge.natEncode_mem_omegaTA
#print axioms TratadoAnalisis.Naturals.ArithmeticBridge.natEncode_injective
#print axioms TratadoAnalisis.Naturals.ArithmeticBridge.exists_natEncode_eq_of_mem
#print axioms TratadoAnalisis.Naturals.ArithmeticBridge.natAddGraph_natEncode
#print axioms TratadoAnalisis.Naturals.ArithmeticBridge.natAddGraph_natEncode_value_iff
#print axioms TratadoAnalisis.Naturals.ArithmeticBridge.natMulGraph_natEncode
#print axioms TratadoAnalisis.Naturals.ArithmeticBridge.natMulGraph_natEncode_value_iff

#print axioms TratadoAnalisis.Integers.Construction.intRel_natEncode_iff
#print axioms TratadoAnalisis.Integers.Construction.TA_PRO_00036_intRel_equivalence
#print axioms TratadoAnalisis.Integers.Construction.intClass_subset_intDomain
#print axioms TratadoAnalisis.Integers.Construction.intClass_mem_integersTA
#print axioms TratadoAnalisis.Integers.Construction.TA_PRO_00037_integer_quotient
#print axioms TratadoAnalisis.Integers.Construction.TA_PRO_00038_intClass_eq_iff
#print axioms TratadoAnalisis.Integers.Construction.TA_PRO_00038_natEncode_class_eq_iff

#print axioms TratadoAnalisis.Integers.Operations.TA_PRO_00039_intRepAdd_well_defined
#print axioms TratadoAnalisis.Integers.Operations.intAddGraph_isFunc
#print axioms TratadoAnalisis.Integers.Operations.intAddGraph_natEncode_classes
#print axioms TratadoAnalisis.Integers.Operations.TA_PRO_00040_intNeg_well_defined
#print axioms TratadoAnalisis.Integers.Operations.intNegGraph_isFunc
#print axioms TratadoAnalisis.Integers.Operations.intNegGraph_natEncode_class
#print axioms TratadoAnalisis.Integers.Operations.intZero_mem_integersTA

#print axioms TratadoAnalisis.Integers.Multiplication.intRepMul_natEncode_iff
#print axioms TratadoAnalisis.Integers.Multiplication.intRepMul_congr_left_nat
#print axioms TratadoAnalisis.Integers.Multiplication.intRepMul_congr_right_nat
#print axioms TratadoAnalisis.Integers.Multiplication.TA_PRO_00043_intRepMul_well_defined
#print axioms TratadoAnalisis.Integers.Multiplication.intMulGraph_isFunc
#print axioms TratadoAnalisis.Integers.Multiplication.intMulGraph_natEncode_classes
#print axioms TratadoAnalisis.Integers.Multiplication.intMulGraph_natEncode_classes_value_iff
#print axioms TratadoAnalisis.Integers.Multiplication.intOne_mem_integersTA

#print axioms TratadoAnalisis.Integers.Algebra.exists_natEncode_intClass_of_mem
#print axioms TratadoAnalisis.Integers.Algebra.IntAdd_unique
#print axioms TratadoAnalisis.Integers.Algebra.IntMul_unique
#print axioms TratadoAnalisis.Integers.Algebra.IntNeg_unique
#print axioms TratadoAnalisis.Integers.Algebra.TA_PRO_00041_additive_group_laws
#print axioms TratadoAnalisis.Integers.Algebra.TA_PRO_00044_mul_distrib_laws
#print axioms TratadoAnalisis.Integers.Algebra.TA_THM_00024_commutative_ring_package
#print axioms TratadoAnalisis.Integers.Algebra.intEmbedGraph_isFunc
#print axioms TratadoAnalisis.Integers.Algebra.intEmbedGraph_natEncode
#print axioms TratadoAnalisis.Integers.Algebra.intEmbedGraph_injective
#print axioms TratadoAnalisis.Integers.Algebra.intEmbedGraph_add_nat
#print axioms TratadoAnalisis.Integers.Algebra.intEmbedGraph_mul_nat
#print axioms TratadoAnalisis.Integers.Algebra.TA_PRO_00045_embedding_properties

#print axioms TratadoAnalisis.Integers.Domain.int_sign_normal_exists
#print axioms TratadoAnalisis.Integers.Domain.intPositiveForm_eq_negativeForm_iff
#print axioms TratadoAnalisis.Integers.Domain.TA_THM_00025_sign_normal_form
#print axioms TratadoAnalisis.Integers.Domain.TA_PRO_00046_zero_ne_one
#print axioms TratadoAnalisis.Integers.Domain.intMul_positive_positive
#print axioms TratadoAnalisis.Integers.Domain.intMul_positive_negative
#print axioms TratadoAnalisis.Integers.Domain.intMul_negative_positive
#print axioms TratadoAnalisis.Integers.Domain.intMul_negative_negative
#print axioms TratadoAnalisis.Integers.Domain.nat_mul_ne_zero_for_sign
#print axioms TratadoAnalisis.Integers.Domain.TA_PRO_00047_no_zero_divisors
#print axioms TratadoAnalisis.Integers.Domain.intMul_ne_zero_of_ne_zero
#print axioms TratadoAnalisis.Integers.Domain.TA_THM_00026_integral_domain_package

#print axioms TratadoAnalisis.Integers.Order.NatLETA_natEncode_iff
#print axioms TratadoAnalisis.Integers.Order.mem_intOrderRel_iff
#print axioms TratadoAnalisis.Integers.Order.TA_PRO_00048_intLE_natEncode_classes_iff
#print axioms TratadoAnalisis.Integers.Order.TA_THM_00027_total_order
#print axioms TratadoAnalisis.Integers.Order.intLE_add_compat
#print axioms TratadoAnalisis.Integers.Order.intEmbed_values_mul
#print axioms TratadoAnalisis.Integers.Order.intLE_mul_nonnegative_compat
#print axioms TratadoAnalisis.Integers.Order.TA_PRO_00049_order_compatibility
#print axioms TratadoAnalisis.Integers.Order.intEmbed_order_nat_iff
#print axioms TratadoAnalisis.Integers.Order.TA_PRO_00050_embedding_order_iff

#print axioms TratadoAnalisis.Rationals.IntegerPrep.intSubValue_exists_unique
#print axioms TratadoAnalisis.Rationals.IntegerPrep.intSubValue_eq_zero_iff
#print axioms TratadoAnalisis.Rationals.IntegerPrep.intMul_neg_sum_zero
#print axioms TratadoAnalisis.Rationals.IntegerPrep.TA_LEM_00009_intMul_cancel_left
#print axioms TratadoAnalisis.Rationals.IntegerPrep.mem_intNonzeroTA_iff
#print axioms TratadoAnalisis.Rationals.IntegerPrep.intNonzero_mul_closed
#print axioms TratadoAnalisis.Rationals.IntegerPrep.mem_ratDomain_iff

#print axioms TratadoAnalisis.Rationals.Construction.ratRel_pairs_iff
#print axioms TratadoAnalisis.Rationals.Construction.ratRel_refl
#print axioms TratadoAnalisis.Rationals.Construction.ratRel_symm
#print axioms TratadoAnalisis.Rationals.Construction.intProductEq_fraction_trans
#print axioms TratadoAnalisis.Rationals.Construction.ratRel_trans
#print axioms TratadoAnalisis.Rationals.Construction.TA_PRO_00051_ratRel_equivalence
#print axioms TratadoAnalisis.Rationals.Construction.ratClass_mem_rationalsTA
#print axioms TratadoAnalisis.Rationals.Construction.TA_PRO_00052_rational_quotient
#print axioms TratadoAnalisis.Rationals.Construction.TA_PRO_00053_ratClass_eq_iff
#print axioms TratadoAnalisis.Rationals.Construction.TA_PRO_00053_ratClass_pairs_eq_iff

#print axioms TratadoAnalisis.Rationals.Additive.ratRepAdd_exists_unique
#print axioms TratadoAnalisis.Rationals.Additive.intPairProducts_exchange_middle
#print axioms TratadoAnalisis.Rationals.Additive.TA_PRO_00054_ratRepAdd_well_defined
#print axioms TratadoAnalisis.Rationals.Additive.ratAddGraph_isFunc
#print axioms TratadoAnalisis.Rationals.Additive.ratAddGraph_classes
#print axioms TratadoAnalisis.Rationals.Additive.ratAddGraph_classes_value_iff
#print axioms TratadoAnalisis.Rationals.Additive.ratZero_mem_rationalsTA
#print axioms TratadoAnalisis.Rationals.Additive.ratRepNeg_exists_unique
#print axioms TratadoAnalisis.Rationals.Additive.intMul_neg_left
#print axioms TratadoAnalisis.Rationals.Additive.intMul_neg_right
#print axioms TratadoAnalisis.Rationals.Additive.TA_PRO_00055_ratRepNeg_well_defined
#print axioms TratadoAnalisis.Rationals.Additive.ratNegGraph_isFunc
#print axioms TratadoAnalisis.Rationals.Additive.ratNegGraph_classes
#print axioms TratadoAnalisis.Rationals.Additive.ratNegGraph_classes_value_iff

#print axioms TratadoAnalisis.Rationals.Multiplicative.ratRepMul_exists_unique
#print axioms TratadoAnalisis.Rationals.Multiplicative.TA_PRO_00057_ratRepMul_well_defined
#print axioms TratadoAnalisis.Rationals.Multiplicative.ratMulGraph_isFunc
#print axioms TratadoAnalisis.Rationals.Multiplicative.ratMulGraph_classes
#print axioms TratadoAnalisis.Rationals.Multiplicative.ratMulGraph_classes_value_iff
#print axioms TratadoAnalisis.Rationals.Multiplicative.ratOne_mem_rationalsTA

#print axioms TratadoAnalisis.Rationals.Algebra.exists_ratClass_pair_of_mem
#print axioms TratadoAnalisis.Rationals.Algebra.RatAdd_unique
#print axioms TratadoAnalisis.Rationals.Algebra.RatMul_unique
#print axioms TratadoAnalisis.Rationals.Algebra.RatNeg_unique
#print axioms TratadoAnalisis.Rationals.Algebra.intMul_zero_left
#print axioms TratadoAnalisis.Rationals.IntegerPrep.intMul_zero_right

#print axioms TratadoAnalisis.Rationals.Algebra.ratAdd_assoc
#print axioms TratadoAnalisis.Rationals.Algebra.ratAdd_comm
#print axioms TratadoAnalisis.Rationals.Algebra.ratAdd_zero_right
#print axioms TratadoAnalisis.Rationals.Algebra.ratAdd_neg_right
#print axioms TratadoAnalisis.Rationals.Algebra.TA_PRO_00056_additive_group_laws

#print axioms TratadoAnalisis.Rationals.Algebra.ratMul_assoc
#print axioms TratadoAnalisis.Rationals.Algebra.ratMul_comm
#print axioms TratadoAnalisis.Rationals.Algebra.ratMul_one_left
#print axioms TratadoAnalisis.Rationals.Algebra.ratMul_add_left
#print axioms TratadoAnalisis.Rationals.Algebra.ratAdd_mul_right
#print axioms TratadoAnalisis.Rationals.Algebra.TA_PRO_00058_mul_distrib_laws

#print axioms TratadoAnalisis.Rationals.Algebra.TA_PRO_00059_ratZero_ne_one

#print axioms TratadoAnalisis.Rationals.Algebra.ratEmbedGraph_isFunc
#print axioms TratadoAnalisis.Rationals.Algebra.ratEmbedGraph_injective
#print axioms TratadoAnalisis.Rationals.Algebra.ratEmbedGraph_add
#print axioms TratadoAnalisis.Rationals.Algebra.ratEmbedGraph_mul
#print axioms TratadoAnalisis.Rationals.Algebra.ratEmbedGraph_neg
#print axioms TratadoAnalisis.Rationals.Algebra.TA_PRO_00060_embedding_properties

/-! C3b: criterio de nulidad, recíproco y cuerpo relacional. -/
#print axioms TratadoAnalisis.Rationals.Field.TA_PRO_00061_ratClass_eq_zero_iff
#print axioms TratadoAnalisis.Rationals.Field.TA_PRO_00061_ratClass_ne_zero_iff
#print axioms TratadoAnalisis.Rationals.Field.mem_ratNonzeroTA_iff
#print axioms TratadoAnalisis.Rationals.Field.exists_nonzero_ratClass_pair_of_mem
#print axioms TratadoAnalisis.Rationals.Field.ratRepInv_exists_unique
#print axioms TratadoAnalisis.Rationals.Field.TA_PRO_00062_ratRepInv_well_defined
#print axioms TratadoAnalisis.Rationals.Field.ratClass_swapped_mem_ratNonzeroTA
#print axioms TratadoAnalisis.Rationals.Field.mem_ratInvGraph
#print axioms TratadoAnalisis.Rationals.Field.ratInvGraph_isFunc
#print axioms TratadoAnalisis.Rationals.Field.RatInv_unique
#print axioms TratadoAnalisis.Rationals.Field.ratInvGraph_classes
#print axioms TratadoAnalisis.Rationals.Field.ratInvGraph_classes_value_iff
#print axioms TratadoAnalisis.Rationals.Field.TA_PRO_00063_inverse_law
#print axioms TratadoAnalisis.Rationals.Field.exists_inverse_of_mem_ratNonzeroTA
#print axioms TratadoAnalisis.Rationals.Field.TA_THM_00028_field_package

-- TA-LEAN-0003 D0 — order prerequisites
#print axioms TratadoAnalisis.Rationals.OrderPrep.intAdd_exists_local
#print axioms TratadoAnalisis.Rationals.OrderPrep.intMul_exists_local
#print axioms TratadoAnalisis.Rationals.OrderPrep.intNeg_exists_local
#print axioms TratadoAnalisis.Rationals.OrderPrep.TA_LEM_00010_intLE_translation_iff
#print axioms TratadoAnalisis.Rationals.OrderPrep.TA_LEM_00011_intLE_mul_positive_iff
#print axioms TratadoAnalisis.Rationals.OrderPrep.TA_LEM_00012_positive_mul

-- TA-LEAN-0003 D1a — local positive-denominator representatives
#print axioms TratadoAnalisis.Rationals.PositiveDenominator.intPositiveForm_pos
#print axioms TratadoAnalisis.Rationals.PositiveDenominator.intNeg_symm_local
#print axioms TratadoAnalisis.Rationals.PositiveDenominator.TA_LEM_00013_positive_denominator

-- TA-LEAN-0003 D1b — representative-independent cross comparison
#print axioms TratadoAnalisis.Rationals.OrderWellDefined.mem_intNonzeroTA_of_positive
#print axioms TratadoAnalisis.Rationals.OrderWellDefined.cross_comparison_forward
#print axioms TratadoAnalisis.Rationals.OrderWellDefined.TA_LEM_00014_cross_comparison_well_defined

-- TA-LEAN-0003 D2a — existential set-coded rational order
#print axioms TratadoAnalisis.Rationals.OrderDefinition.RatLEWitness
#print axioms TratadoAnalisis.Rationals.OrderDefinition.ratOrderRel
#print axioms TratadoAnalisis.Rationals.OrderDefinition.RatLE
#print axioms TratadoAnalisis.Rationals.OrderDefinition.mem_ratOrderRel_iff
#print axioms TratadoAnalisis.Rationals.OrderDefinition.RatLE_iff_witness
#print axioms TratadoAnalisis.Rationals.OrderDefinition.TA_PRO_00064_ratLE_classes_iff

-- TA-LEAN-0003 D2b — total and strict rational order
#print axioms TratadoAnalisis.Rationals.TotalOrder.ratLE_refl
#print axioms TratadoAnalisis.Rationals.TotalOrder.ratLE_antisymm
#print axioms TratadoAnalisis.Rationals.TotalOrder.ratLE_trans
#print axioms TratadoAnalisis.Rationals.TotalOrder.ratLE_total
#print axioms TratadoAnalisis.Rationals.TotalOrder.TA_THM_00029_total_order
#print axioms TratadoAnalisis.Rationals.TotalOrder.RatLT
#print axioms TratadoAnalisis.Rationals.TotalOrder.TA_COR_00009_ratLT_classes_iff

-- TA-LEAN-0003 D2c — ordered-field compatibility
#print axioms TratadoAnalisis.Rationals.OrderedFieldCompatibility.ratLE_add_compat
#print axioms TratadoAnalisis.Rationals.OrderedFieldCompatibility.ratLE_mul_nonnegative_compat
#print axioms TratadoAnalisis.Rationals.OrderedFieldCompatibility.TA_PRO_00065_order_compatibility
#print axioms TratadoAnalisis.Rationals.OrderedFieldCompatibility.TA_PRO_00066_ratEmbed_order_iff

-- TA-LEAN-0003 D3 — rational positivity and strict scaling
#print axioms TratadoAnalisis.Rationals.NoZeroDivisors.TA_COR_00007_no_zero_divisors
#print axioms TratadoAnalisis.Rationals.StrictOrder.ratZero_lt_one
#print axioms TratadoAnalisis.Rationals.StrictOrder.ratPositive_mul
#print axioms TratadoAnalisis.Rationals.StrictOrder.ratInv_positive
#print axioms TratadoAnalisis.Rationals.StrictOrder.ratLT_mul_positive_right
#print axioms TratadoAnalisis.Rationals.StrictOrder.TA_LEM_00015_positivity_strict_scaling

-- TA-LEAN-0003 E1a — natural parity infrastructure
#print axioms TratadoAnalisis.Rationals.IrrationalityPrep.EvenTA
#print axioms TratadoAnalisis.Rationals.IrrationalityPrep.OddTA
#print axioms TratadoAnalisis.Rationals.IrrationalityPrep.EvenOmegaTA
#print axioms TratadoAnalisis.Rationals.IrrationalityPrep.OddOmegaTA
#print axioms TratadoAnalisis.Rationals.IrrationalityPrep.evenOmegaTA_natEncode_iff
#print axioms TratadoAnalisis.Rationals.IrrationalityPrep.oddOmegaTA_natEncode_iff
#print axioms TratadoAnalisis.Rationals.IrrationalityPrep.TA_LEM_00016_parity_dichotomy
#print axioms TratadoAnalisis.Rationals.IrrationalityPrep.TA_LEM_00017_even_square_implies_even

-- TA-LEAN-0003 E1b — no rational square root of two
#print axioms TratadoAnalisis.Rationals.IrrationalitySqrtTwo.natTwoTA_intEmbed
#print axioms TratadoAnalisis.Rationals.IrrationalitySqrtTwo.intTwoTA_ratEmbed
#print axioms TratadoAnalisis.Rationals.IrrationalitySqrtTwo.ratTwoTA_ne_zero
#print axioms TratadoAnalisis.Rationals.IrrationalitySqrtTwo.SqrtTwoDenominatorWitness
#print axioms TratadoAnalisis.Rationals.IrrationalitySqrtTwo.sqrtTwoWitness_descends
#print axioms TratadoAnalisis.Rationals.IrrationalitySqrtTwo.sqrtTwoWitness_wellFounded_empty
#print axioms TratadoAnalisis.Rationals.IrrationalitySqrtTwo.square_fraction_cross_eq
#print axioms TratadoAnalisis.Rationals.IrrationalitySqrtTwo.TA_THM_00032_no_rational_square_two

-- TA-LEAN-0003 E2a — square monotonicity on nonnegative rationals
#print axioms TratadoAnalisis.Rationals.SquareMonotonicity.ratLT_of_le_of_lt_local
#print axioms TratadoAnalisis.Rationals.SquareMonotonicity.TA_LEM_00018_square_strict_mono_nonnegative

-- TA-LEAN-0003 E2b — the rational set associated with q² < 2
#print axioms TratadoAnalisis.Rationals.SqrtTwoSet.sqrtTwoSet
#print axioms TratadoAnalisis.Rationals.SqrtTwoSet.TA_DEF_00066_mem_sqrtTwoSet_iff
#print axioms TratadoAnalisis.Rationals.SqrtTwoSet.ratOne_lt_two_local
#print axioms TratadoAnalisis.Rationals.SqrtTwoSet.ratZero_lt_two_local
#print axioms TratadoAnalisis.Rationals.SqrtTwoSet.ratOne_square_local
#print axioms TratadoAnalisis.Rationals.SqrtTwoSet.ratOne_mul_two_local
#print axioms TratadoAnalisis.Rationals.SqrtTwoSet.TA_PRO_00067_sqrtTwoSet_nonempty_bounded

-- TA-LEAN-0003 E3 — S₂ has no rational supremum
#print axioms TratadoAnalisis.Rationals.NoSupremumSqrtTwo.RatUpperBound
#print axioms TratadoAnalisis.Rationals.NoSupremumSqrtTwo.RatSupremum
#print axioms TratadoAnalisis.Rationals.NoSupremumSqrtTwo.ratLT_of_lt_of_le_local
#print axioms TratadoAnalisis.Rationals.NoSupremumSqrtTwo.ratAdd_cancel_right_local
#print axioms TratadoAnalisis.Rationals.NoSupremumSqrtTwo.ratLE_add_cancel_right_local
#print axioms TratadoAnalisis.Rationals.NoSupremumSqrtTwo.ratLT_add_cancel_right_local
#print axioms TratadoAnalisis.Rationals.NoSupremumSqrtTwo.ratLT_add_right_local
#print axioms TratadoAnalisis.Rationals.NoSupremumSqrtTwo.ratLT_add_left_local
#print axioms TratadoAnalisis.Rationals.NoSupremumSqrtTwo.ratLE_add_left_local
#print axioms TratadoAnalisis.Rationals.NoSupremumSqrtTwo.ratLT_mul_positive_left_local
#print axioms TratadoAnalisis.Rationals.NoSupremumSqrtTwo.ratOne_add_one_two_local
#print axioms TratadoAnalisis.Rationals.NoSupremumSqrtTwo.ratTwo_mul_as_add_local
#print axioms TratadoAnalisis.Rationals.NoSupremumSqrtTwo.square_add_expansion_local
#print axioms TratadoAnalisis.Rationals.NoSupremumSqrtTwo.ratLE_mul_nonnegative_left_local
#print axioms TratadoAnalisis.Rationals.NoSupremumSqrtTwo.ratSub_positive_local
#print axioms TratadoAnalisis.Rationals.NoSupremumSqrtTwo.ratSub_add_cancel_local
#print axioms TratadoAnalisis.Rationals.NoSupremumSqrtTwo.ratNeg_lt_zero_local
#print axioms TratadoAnalisis.Rationals.NoSupremumSqrtTwo.ratQuotient_mul_denominator_local
#print axioms TratadoAnalisis.Rationals.NoSupremumSqrtTwo.square_lt_two_gives_larger_member_local
#print axioms TratadoAnalisis.Rationals.NoSupremumSqrtTwo.two_lt_square_gives_smaller_upper_local
#print axioms TratadoAnalisis.Rationals.NoSupremumSqrtTwo.TA_THM_00033_sqrtTwoSet_no_rational_supremum

-- TA-LEAN-0004 B — definiciones conjuntistas de cortaduras
#print axioms TratadoAnalisis.Dedekind.Definition.TA_THM_00001_zfset_eq_iff_subset
#print axioms TratadoAnalisis.Dedekind.Definition.IsDedekindCut
#print axioms TratadoAnalisis.Dedekind.Definition.TA_DEF_00079_isDedekindCut_iff
#print axioms TratadoAnalisis.Dedekind.Definition.dedekindCutsTA
#print axioms TratadoAnalisis.Dedekind.Definition.TA_DEF_00080_dedekindCuts_eq_sep
#print axioms TratadoAnalisis.Dedekind.Definition.TA_PRO_00079_mem_dedekindCuts_iff
#print axioms TratadoAnalisis.Dedekind.Definition.rationalSection
#print axioms TratadoAnalisis.Dedekind.Definition.TA_DEF_00081_mem_rationalSection_iff
#print axioms TratadoAnalisis.Dedekind.Definition.alphaTwoCut
#print axioms TratadoAnalisis.Dedekind.Definition.TA_DEF_00082_mem_alphaTwoCut_iff
#print axioms TratadoAnalisis.Dedekind.Definition.DedLE
#print axioms TratadoAnalisis.Dedekind.Definition.TA_DEF_00083_dedLE_iff_subset

/-! ## TA-LEAN-0004 C: prerrequisitos racionales (incluye auxiliares).
TA-PRO-00172 se certifica solo en su lectura proposicional. -/
#print axioms TratadoAnalisis.Rationals.Signs.RatSub
#print axioms TratadoAnalisis.Rationals.Signs.TA_DEF_00056_ratSub_iff
#print axioms TratadoAnalisis.Rationals.Signs.ratSub_exists
#print axioms TratadoAnalisis.Rationals.Signs.RatSub_unique
#print axioms TratadoAnalisis.Rationals.Signs.ratSub_add_cancel
#print axioms TratadoAnalisis.Rationals.Signs.ratSub_positive
#print axioms TratadoAnalisis.Rationals.Signs.ratAdd_comm_rel
#print axioms TratadoAnalisis.Rationals.Signs.ratMul_comm_rel
#print axioms TratadoAnalisis.Rationals.Signs.ratAdd_neg_right_rel
#print axioms TratadoAnalisis.Rationals.Signs.ratNeg_of_add_zero
#print axioms TratadoAnalisis.Rationals.Signs.ratNeg_symm_rel
#print axioms TratadoAnalisis.Rationals.Signs.ratMul_neg_right_rel
#print axioms TratadoAnalisis.Rationals.Signs.ratMul_neg_neg_eq
#print axioms TratadoAnalisis.Rationals.Signs.TA_LEM_00020_clause3_zero_lt_one
#print axioms TratadoAnalisis.Rationals.Signs.TA_LEM_00020_clause4_square_nonnegative
#print axioms TratadoAnalisis.Rationals.Signs.TA_LEM_00020_clause5_positive_product
#print axioms TratadoAnalisis.Rationals.Signs.TA_LEM_00020_clause6_positive_inverse
#print axioms TratadoAnalisis.Rationals.Signs.TA_LEM_00020_clause8_translate_iff
#print axioms TratadoAnalisis.Rationals.Signs.ratLE_mul_positive_iff
#print axioms TratadoAnalisis.Rationals.Signs.TA_LEM_00020_clause9_scale_iff
#print axioms TratadoAnalisis.Rationals.Density.rational_midpoint_between
#print axioms TratadoAnalisis.Rationals.Density.rational_midpoint_exists
#print axioms TratadoAnalisis.Rationals.Density.TA_THM_00034_rational_density
#print axioms TratadoAnalisis.Rationals.OrderedField.TA_PRO_00068_ordered_field_package
#print axioms TratadoAnalisis.Rationals.Trichotomy.intLT_trichotomy_local
#print axioms TratadoAnalisis.Rationals.Trichotomy.TA_PRO_00172_rational_trichotomy

/-! ## TA-LEAN-0004 D: secciones racionales, sin hipótesis em. -/
#print axioms TratadoAnalisis.Dedekind.RationalSection.rationalSection_sub_one_mem
#print axioms TratadoAnalisis.Dedekind.RationalSection.rationalSection_self_not_mem
#print axioms TratadoAnalisis.Dedekind.RationalSection.rationalSection_isDedekindCut
#print axioms TratadoAnalisis.Dedekind.RationalSection.TA_PRO_00080_rationalSection_mem

/-! ## TA-LEAN-0004 F: orden, em explícito y envoltorios separados. -/
#print axioms TratadoAnalisis.Dedekind.Order.dedLE_refl
#print axioms TratadoAnalisis.Dedekind.Order.dedLE_antisymm
#print axioms TratadoAnalisis.Dedekind.Order.dedLE_trans
#print axioms TratadoAnalisis.Dedekind.Order.subset_failure_witness
#print axioms TratadoAnalisis.Dedekind.Order.cut_member_lt_nonmember
#print axioms TratadoAnalisis.Dedekind.Order.cut_reverse_subset_of_witness
#print axioms TratadoAnalisis.Dedekind.Order.TA_THM_00040_dedLE_total
#print axioms TratadoAnalisis.Dedekind.Order.TA_THM_00040_total_order_package
#print axioms TratadoAnalisis.Dedekind.Order.DedLT
#print axioms TratadoAnalisis.Dedekind.Order.TA_COR_00015_dedLT_iff_proper_subset
#print axioms TratadoAnalisis.Dedekind.Order.cut_inhabited
#print axioms TratadoAnalisis.Dedekind.Order.cut_exterior_inhabited
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappers.subset_failure_witness
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappers.TA_THM_00040_dedLE_total_classical
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappers.TA_THM_00040_total_order_package_classical
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappers.cut_inhabited
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappers.cut_exterior_inhabited

/-! ## TA-LEAN-0004 E1: la cortadura cuadrática, sin em ni supremos. -/
#print axioms TratadoAnalisis.Dedekind.AlphaTwo.ratLT_asymm_cut
#print axioms TratadoAnalisis.Dedekind.AlphaTwo.alphaTwoCut_mem_of_negative
#print axioms TratadoAnalisis.Dedekind.AlphaTwo.alphaTwoCut_zero_mem
#print axioms TratadoAnalisis.Dedekind.AlphaTwo.alphaTwoCut_one_mem
#print axioms TratadoAnalisis.Dedekind.AlphaTwo.alphaTwoCut_not_mem_of_square_above
#print axioms TratadoAnalisis.Dedekind.AlphaTwo.alphaTwoCut_two_not_mem
#print axioms TratadoAnalisis.Dedekind.AlphaTwo.alphaTwoCut_lower_closed
#print axioms TratadoAnalisis.Dedekind.AlphaTwo.alphaTwoCut_no_maximum
#print axioms TratadoAnalisis.Dedekind.AlphaTwo.alphaTwoCut_isDedekindCut
#print axioms TratadoAnalisis.Dedekind.AlphaTwo.TA_PRO_00081_alphaTwoCut_mem

/-! ## TA-LEAN-0004 E2: separador estricto y no racionalidad local. -/
#print axioms TratadoAnalisis.Dedekind.AlphaTwoPrep.positive_square_two_separator
#print axioms TratadoAnalisis.Dedekind.AlphaTwo.alphaTwoCut_ne_section_of_nonpositive
#print axioms TratadoAnalisis.Dedekind.AlphaTwo.TA_PRO_00082_alphaTwoCut_ne_rationalSection

/-! ## TA-LEAN-0004 G: grafo e incrustación racional, universo único. -/
#print axioms TratadoAnalisis.Dedekind.Embedding.dedekindEmbeddingGraph
#print axioms TratadoAnalisis.Dedekind.Embedding.TA_DEF_00084_mem_embeddingGraph_iff
#print axioms TratadoAnalisis.Dedekind.Embedding.TA_DEF_00084_embeddingGraph_isFunc
#print axioms TratadoAnalisis.Dedekind.Embedding.TA_PRO_00083_ratLE_iff_sections_subset
#print axioms TratadoAnalisis.Dedekind.Embedding.TA_COR_00016_rationalSection_injective
#print axioms TratadoAnalisis.Dedekind.Embedding.TA_COR_00016_ratLT_iff_sections_dedLT
#print axioms TratadoAnalisis.Dedekind.Embedding.TA_COR_00017_not_every_cut_is_section
#print axioms TratadoAnalisis.Dedekind.Embedding.TA_COR_00017_alphaTwo_outside_embedding_image

-- TA-LEAN-0005 P0
#print axioms TratadoAnalisis.Foundations.FunctionTriple.functionTriple_eq_iff
#print axioms TratadoAnalisis.Foundations.FunctionTriple.TA_DEF_00018_functionTriple_iff
#print axioms TratadoAnalisis.Foundations.FunctionTriple.functionTriple_graph_unique
#print axioms TratadoAnalisis.Dedekind.EmbeddingTriple.TA_DEF_00084_embeddingFunction_isTriple

-- TA-LEAN-0005 P1
#print axioms TratadoAnalisis.Rationals.Signs.ratNeg_le_reverse
#print axioms TratadoAnalisis.Rationals.Signs.TA_LEM_00020_clause2_neg_le_iff
#print axioms TratadoAnalisis.Rationals.Signs.TA_LEM_00020_clause2_neg_lt_iff
#print axioms TratadoAnalisis.Rationals.Division.TA_DEF_00061_ratDiv_iff
#print axioms TratadoAnalisis.Rationals.Division.ratDiv_exists
#print axioms TratadoAnalisis.Rationals.Division.RatDiv_unique
#print axioms TratadoAnalisis.Rationals.Division.TA_THM_00030_rational_density

-- TA-LEAN-0005 S
#print axioms TratadoAnalisis.Dedekind.Addition.TA_LEM_00021_member_lt_exterior
#print axioms TratadoAnalisis.Dedekind.Addition.TA_DEF_00085_mem_dedAdd_iff
#print axioms TratadoAnalisis.Dedekind.Addition.dedAdd_subset_rationals
#print axioms TratadoAnalisis.Dedekind.Addition.mem_dedAdd_of_add
#print axioms TratadoAnalisis.Dedekind.Addition.TA_PRO_00084_dedAdd_mem
#print axioms TratadoAnalisis.Dedekind.Addition.mem_dedAddGraph_iff
#print axioms TratadoAnalisis.Dedekind.Addition.TA_DEF_00086_dedAddGraph_isFunc
#print axioms TratadoAnalisis.Dedekind.Addition.TA_DEF_00086_dedAddFunction_isTriple
#print axioms TratadoAnalisis.Dedekind.Addition.TA_DEF_00087_dedZero_eq
#print axioms TratadoAnalisis.Dedekind.Addition.dedZero_mem
#print axioms TratadoAnalisis.Dedekind.Addition.TA_COR_00018_embedding_zero
#print axioms TratadoAnalisis.Dedekind.Addition.add_zero_right_rel
#print axioms TratadoAnalisis.Dedekind.Addition.add_zero_left_rel
#print axioms TratadoAnalisis.Dedekind.Addition.TA_PRO_00085_rationalSection_add
#print axioms TratadoAnalisis.Dedekind.Addition.dedAdd_comm_of_subsets
#print axioms TratadoAnalisis.Dedekind.Addition.TA_PRO_00086_dedZero_neutral
#print axioms TratadoAnalisis.Dedekind.Addition.dedAdd_assoc_of_subsets
#print axioms TratadoAnalisis.Dedekind.Addition.TA_THM_00041_dedAdd_assoc
#print axioms TratadoAnalisis.Dedekind.Addition.TA_THM_00042_dedAdd_comm

-- Envoltorios S (regla 13)
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersAdd.TA_PRO_00084_dedAdd_mem
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersAdd.TA_DEF_00086_dedAddGraph_isFunc
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersAdd.TA_DEF_00086_dedAddFunction_isTriple

-- TA-LEAN-0005 P2
#print axioms TratadoAnalisis.Rationals.NatEmbedding.natEmbeddingGraph
#print axioms TratadoAnalisis.Rationals.NatEmbedding.TA_DEF_00063_mem_natEmbeddingGraph_iff
#print axioms TratadoAnalisis.Rationals.NatEmbedding.TA_DEF_00063_natEmbeddingGraph_isFunc
#print axioms TratadoAnalisis.Rationals.NatEmbedding.natEmbeddingFunction
#print axioms TratadoAnalisis.Rationals.NatEmbedding.TA_DEF_00063_natEmbeddingFunction_isTriple
#print axioms TratadoAnalisis.Rationals.NatEmbedding.natRational
#print axioms TratadoAnalisis.Rationals.NatEmbedding.intEmbedding_canonical
#print axioms TratadoAnalisis.Rationals.NatEmbedding.natRational_graph
#print axioms TratadoAnalisis.Rationals.NatEmbedding.natRational_mem
#print axioms TratadoAnalisis.Rationals.NatEmbedding.natRational_value_iff
#print axioms TratadoAnalisis.Rationals.NatEmbedding.TA_COR_00008_natRational_injective
#print axioms TratadoAnalisis.Rationals.NatEmbedding.TA_COR_00008_natRational_zero
#print axioms TratadoAnalisis.Rationals.NatEmbedding.TA_COR_00008_natRational_one
#print axioms TratadoAnalisis.Rationals.NatEmbedding.natRational_add_nat
#print axioms TratadoAnalisis.Rationals.NatEmbedding.natRational_mul_nat
#print axioms TratadoAnalisis.Rationals.NatEmbedding.TA_COR_00008_natRational_add
#print axioms TratadoAnalisis.Rationals.NatEmbedding.TA_COR_00008_natRational_mul
#print axioms TratadoAnalisis.Rationals.NatEmbedding.TA_COR_00008_natRational_succ
#print axioms TratadoAnalisis.Rationals.NatEmbedding.TA_COR_00008_natRational_order_iff
#print axioms TratadoAnalisis.Rationals.NatEmbedding.TA_COR_00008_natRational_strict_order_iff

-- TA-LEAN-0005 P3
#print axioms TratadoAnalisis.Rationals.Archimedean.int_mul_one_right_rel
#print axioms TratadoAnalisis.Rationals.Archimedean.positive_form_lt_of_nat_lt
#print axioms TratadoAnalisis.Rationals.Archimedean.negative_form_lt_positive
#print axioms TratadoAnalisis.Rationals.Archimedean.fraction_lt_nat_of_cross
#print axioms TratadoAnalisis.Rationals.Archimedean.TA_THM_00031_rational_archimedean
#print axioms TratadoAnalisis.Rationals.Archimedean.TA_THM_00031_rational_archimedean_graph

-- TA-LEAN-0005 T
#print axioms TratadoAnalisis.Dedekind.Boundary.mul_one_left_rel
#print axioms TratadoAnalisis.Dedekind.Boundary.translated_natural_multiple_mem
#print axioms TratadoAnalisis.Dedekind.Boundary.TA_LEM_00022_boundary_approximation
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersAdd.TA_LEM_00022_boundary_approximation

-- TA-LEAN-0005 U
#print axioms TratadoAnalisis.Dedekind.Negation.dedNeg
#print axioms TratadoAnalisis.Dedekind.Negation.TA_DEF_00088_mem_dedNeg_iff
#print axioms TratadoAnalisis.Dedekind.Negation.dedNeg_subset_rationals
#print axioms TratadoAnalisis.Dedekind.Negation.TA_PRO_00087_dedNeg_mem
#print axioms TratadoAnalisis.Dedekind.Negation.dedNegGraph
#print axioms TratadoAnalisis.Dedekind.Negation.mem_dedNegGraph_iff
#print axioms TratadoAnalisis.Dedekind.Negation.TA_DEF_00089_dedNegGraph_isFunc
#print axioms TratadoAnalisis.Dedekind.Negation.dedNegFunction
#print axioms TratadoAnalisis.Dedekind.Negation.TA_DEF_00089_dedNegFunction_isTriple
#print axioms TratadoAnalisis.Dedekind.Negation.zero_neg_rel
#print axioms TratadoAnalisis.Dedekind.Negation.TA_PRO_00088_dedAdd_neg
#print axioms TratadoAnalisis.Dedekind.Negation.TA_COR_00019_rationalSection_neg
#print axioms TratadoAnalisis.Dedekind.AdditiveGroup.TA_COR_00020_dedAdd_neg_bilateral
#print axioms TratadoAnalisis.Dedekind.AdditiveGroup.TA_THM_00043_additive_group_package
#print axioms TratadoAnalisis.Dedekind.AdditiveGroup.TA_PRO_00089_dedAdd_cancel_right
#print axioms TratadoAnalisis.Dedekind.AdditiveGroup.TA_PRO_00089_dedAdd_cancel_left
#print axioms TratadoAnalisis.Dedekind.AdditiveGroup.dedSub
#print axioms TratadoAnalisis.Dedekind.AdditiveGroup.TA_DEF_00090_dedSub_eq
#print axioms TratadoAnalisis.Dedekind.AdditiveGroup.mem_dedSub_iff
#print axioms TratadoAnalisis.Dedekind.AdditiveGroup.dedSub_mem
#print axioms TratadoAnalisis.Dedekind.AdditiveGroup.dedSubGraph
#print axioms TratadoAnalisis.Dedekind.AdditiveGroup.mem_dedSubGraph_iff
#print axioms TratadoAnalisis.Dedekind.AdditiveGroup.dedSubGraph_isFunc
#print axioms TratadoAnalisis.Dedekind.AdditiveGroup.dedSubFunction
#print axioms TratadoAnalisis.Dedekind.AdditiveGroup.dedSubFunction_isTriple
#print axioms TratadoAnalisis.Dedekind.AdditiveGroup.TA_COR_00021_rationalSection_sub
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersAdd.TA_PRO_00087_dedNeg_mem
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersAdd.TA_DEF_00089_dedNegGraph_isFunc
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersAdd.TA_DEF_00089_dedNegFunction_isTriple
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersAdd.TA_PRO_00088_dedAdd_neg
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersAdd.TA_COR_00020_dedAdd_neg_bilateral
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersAdd.TA_THM_00043_additive_group_package
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersAdd.TA_PRO_00089_dedAdd_cancel_right
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersAdd.TA_PRO_00089_dedAdd_cancel_left
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersAdd.dedSub_mem
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersAdd.dedSubGraph_isFunc
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersAdd.dedSubFunction_isTriple

/- TA-LEAN-0006 P: interfaces racionales, sin em. -/
#print axioms TratadoAnalisis.Rationals.PositiveProducts.ratMul_value_mem
#print axioms TratadoAnalisis.Rationals.PositiveProducts.ratDiv_value_mem
#print axioms TratadoAnalisis.Rationals.PositiveProducts.ratMul_one_left_rel
#print axioms TratadoAnalisis.Rationals.PositiveProducts.ratDiv_mul_denominator
#print axioms TratadoAnalisis.Rationals.PositiveProducts.ratDiv_positive
#print axioms TratadoAnalisis.Rationals.PositiveProducts.ratDiv_lt_iff
#print axioms TratadoAnalisis.Rationals.PositiveProducts.ratLT_div_iff
#print axioms TratadoAnalisis.Rationals.PositiveProducts.ratDiv_le_iff
#print axioms TratadoAnalisis.Rationals.PositiveProducts.ratLE_div_iff
#print axioms TratadoAnalisis.Rationals.PositiveProducts.ratDiv_lt_one_iff
#print axioms TratadoAnalisis.Rationals.PositiveProducts.ratNeg_zero_rel
#print axioms TratadoAnalisis.Rationals.PositiveProducts.ratNeg_positive_iff
#print axioms TratadoAnalisis.Rationals.PositiveProducts.ratNeg_negative_iff
#print axioms TratadoAnalisis.Rationals.PositiveProducts.ratMul_neg_left_rel
#print axioms TratadoAnalisis.Rationals.PositiveProducts.ratMul_neg_neg_general
#print axioms TratadoAnalisis.Rationals.PositiveProducts.ratMul_negative_positive
#print axioms TratadoAnalisis.Rationals.PositiveProducts.ratMul_positive_negative
#print axioms TratadoAnalisis.Rationals.PositiveProducts.ratMul_negative_negative

/- TA-LEAN-0006 B: constructores y fragmentos de positividad. -/
#print axioms TratadoAnalisis.Dedekind.Positivity.IsPositiveCut
#print axioms TratadoAnalisis.Dedekind.Positivity.positiveCutsTA
#print axioms TratadoAnalisis.Dedekind.Positivity.TA_DEF_00091_isPositiveCut_iff
#print axioms TratadoAnalisis.Dedekind.Positivity.TA_DEF_00091_mem_positiveCuts_iff
#print axioms TratadoAnalisis.Dedekind.Positivity.IsNegativeCut
#print axioms TratadoAnalisis.Dedekind.Positivity.negativeCutsTA
#print axioms TratadoAnalisis.Dedekind.Positivity.TA_DEF_00095_isNegativeCut_iff
#print axioms TratadoAnalisis.Dedekind.Positivity.TA_DEF_00095_mem_negativeCuts_iff
#print axioms TratadoAnalisis.Dedekind.Positivity.positivePart
#print axioms TratadoAnalisis.Dedekind.Positivity.TA_DEF_00092_mem_positivePart_iff
#print axioms TratadoAnalisis.Dedekind.Positivity.dedPositiveMul
#print axioms TratadoAnalisis.Dedekind.Positivity.TA_DEF_00093_mem_positiveMul_iff
#print axioms TratadoAnalisis.Dedekind.Positivity.dedPositiveMul_subset_rationals
#print axioms TratadoAnalisis.Dedekind.Positivity.mem_positiveMul_of_witness
#print axioms TratadoAnalisis.Dedekind.Positivity.TA_LEM_00023_zero_mem_iff_positive_member
#print axioms TratadoAnalisis.Dedekind.Positivity.TA_LEM_00023_zero_mem_implies_positive
#print axioms TratadoAnalisis.Dedekind.Positivity.TA_LEM_00023_positive_member_implies_positive
#print axioms TratadoAnalisis.Dedekind.Positivity.TA_LEM_00023_positive_implies_zero_mem
#print axioms TratadoAnalisis.Dedekind.Positivity.TA_LEM_00023_positive_iff_zero_mem
#print axioms TratadoAnalisis.Dedekind.Positivity.TA_LEM_00023_characterizations
#print axioms TratadoAnalisis.Dedekind.Positivity.TA_PRO_00093_zero_signs_pairwise_incompatible

/- TA-LEAN-0006 C: producto positivo, grafo/triple y secciones. -/
#print axioms TratadoAnalisis.Dedekind.PositiveMultiplication.positive_product_lt_of_factor_bounds
#print axioms TratadoAnalisis.Dedekind.PositiveMultiplication.TA_PRO_00090_positiveMul_mem
#print axioms TratadoAnalisis.Dedekind.PositiveMultiplication.TA_PRO_00091_rationalSection_positive
#print axioms TratadoAnalisis.Dedekind.PositiveMultiplication.positiveMulGraph
#print axioms TratadoAnalisis.Dedekind.PositiveMultiplication.mem_positiveMulGraph_iff
#print axioms TratadoAnalisis.Dedekind.PositiveMultiplication.TA_DEF_00094_positiveMulGraph_isFunc
#print axioms TratadoAnalisis.Dedekind.PositiveMultiplication.positiveMulFunction
#print axioms TratadoAnalisis.Dedekind.PositiveMultiplication.TA_DEF_00094_positiveMulFunction_isTriple
#print axioms TratadoAnalisis.Dedekind.PositiveMultiplication.TA_PRO_00092_rationalSection_positiveMul

/- TA-LEAN-0006 D: signos e intercambio por opuesto. -/
#print axioms TratadoAnalisis.Dedekind.Signs.TA_PRO_00093_zero_sign_trichotomy
#print axioms TratadoAnalisis.Dedekind.Signs.TA_PRO_00093_zero_signs_exclusive
#print axioms TratadoAnalisis.Dedekind.Signs.TA_PRO_00093_zero_sign_package
#print axioms TratadoAnalisis.Dedekind.Signs.TA_LEM_00024_dedNeg_zero
#print axioms TratadoAnalisis.Dedekind.Signs.negative_implies_positive_neg
#print axioms TratadoAnalisis.Dedekind.Signs.positive_implies_negative_neg
#print axioms TratadoAnalisis.Dedekind.Signs.TA_LEM_00024_negative_iff_positive_neg
#print axioms TratadoAnalisis.Dedekind.Signs.TA_LEM_00024_positive_iff_negative_neg
#print axioms TratadoAnalisis.Dedekind.Signs.TA_LEM_00024_sign_negation_package

/- TA-LEAN-0006 E: cinco ramas, función y compatibilidad racional. -/
#print axioms TratadoAnalisis.Dedekind.Multiplication.dedSignedMul
#print axioms TratadoAnalisis.Dedekind.Multiplication.TA_DEF_00096_mem_dedSignedMul_iff
#print axioms TratadoAnalisis.Dedekind.Multiplication.dedSignedMul_subset_rationals
#print axioms TratadoAnalisis.Dedekind.Multiplication.cut_positive_ne_zero
#print axioms TratadoAnalisis.Dedekind.Multiplication.cut_negative_ne_zero
#print axioms TratadoAnalisis.Dedekind.Multiplication.cut_positive_not_negative
#print axioms TratadoAnalisis.Dedekind.Multiplication.cut_negative_not_positive
#print axioms TratadoAnalisis.Dedekind.Multiplication.zero_not_positive
#print axioms TratadoAnalisis.Dedekind.Multiplication.zero_not_negative
#print axioms TratadoAnalisis.Dedekind.Multiplication.dedZero_subset_rationals
#print axioms TratadoAnalisis.Dedekind.Multiplication.rational_guard_iff
#print axioms TratadoAnalisis.Dedekind.Multiplication.TA_DEF_00096_zero_left
#print axioms TratadoAnalisis.Dedekind.Multiplication.TA_DEF_00096_zero_right
#print axioms TratadoAnalisis.Dedekind.Multiplication.TA_DEF_00096_of_zero
#print axioms TratadoAnalisis.Dedekind.Multiplication.TA_DEF_00096_of_pos_pos
#print axioms TratadoAnalisis.Dedekind.Multiplication.TA_DEF_00096_of_neg_neg
#print axioms TratadoAnalisis.Dedekind.Multiplication.TA_DEF_00096_of_pos_neg
#print axioms TratadoAnalisis.Dedekind.Multiplication.TA_DEF_00096_of_neg_pos
#print axioms TratadoAnalisis.Dedekind.Multiplication.signedMul_positive_of_pos_pos
#print axioms TratadoAnalisis.Dedekind.Multiplication.signedMul_positive_of_neg_neg
#print axioms TratadoAnalisis.Dedekind.Multiplication.signedMul_negative_of_pos_neg
#print axioms TratadoAnalisis.Dedekind.Multiplication.signedMul_negative_of_neg_pos
#print axioms TratadoAnalisis.Dedekind.Multiplication.TA_PRO_00094_dedSignedMul_mem
#print axioms TratadoAnalisis.Dedekind.Multiplication.TA_PRO_00094_closure_sign_package
#print axioms TratadoAnalisis.Dedekind.Multiplication.dedMul
#print axioms TratadoAnalisis.Dedekind.Multiplication.TA_DEF_00097_dedMul_eq
#print axioms TratadoAnalisis.Dedekind.Multiplication.dedMulGraph
#print axioms TratadoAnalisis.Dedekind.Multiplication.mem_dedMulGraph_iff
#print axioms TratadoAnalisis.Dedekind.Multiplication.TA_DEF_00097_dedMulGraph_isFunc
#print axioms TratadoAnalisis.Dedekind.Multiplication.dedMulFunction
#print axioms TratadoAnalisis.Dedekind.Multiplication.TA_DEF_00097_dedMulFunction_isTriple
#print axioms TratadoAnalisis.Dedekind.Multiplication.section_positive_of_rational
#print axioms TratadoAnalisis.Dedekind.Multiplication.section_negative_of_rational
#print axioms TratadoAnalisis.Dedekind.Multiplication.section_mul_zero_left
#print axioms TratadoAnalisis.Dedekind.Multiplication.section_mul_zero_right
#print axioms TratadoAnalisis.Dedekind.Multiplication.section_mul_of_neg_neg
#print axioms TratadoAnalisis.Dedekind.Multiplication.section_mul_of_pos_neg
#print axioms TratadoAnalisis.Dedekind.Multiplication.section_mul_of_neg_pos
#print axioms TratadoAnalisis.Dedekind.Multiplication.TA_PRO_00095_rationalSection_mul

-- TA-LEAN-0006 F: unidad e involutividad.
#print axioms TratadoAnalisis.Dedekind.Unit.dedOne
#print axioms TratadoAnalisis.Dedekind.Unit.TA_DEF_00098_dedOne_eq
#print axioms TratadoAnalisis.Dedekind.Unit.dedOne_mem
#print axioms TratadoAnalisis.Dedekind.Unit.TA_PRO_00096_dedOne_positive
#print axioms TratadoAnalisis.Dedekind.Unit.TA_PRO_00096_zero_ne_one
#print axioms TratadoAnalisis.Dedekind.Unit.TA_PRO_00096_one_mem_positiveCuts
#print axioms TratadoAnalisis.Dedekind.Unit.TA_LEM_00025_dedNeg_involutive
#print axioms TratadoAnalisis.Dedekind.Unit.positiveMul_one_subset
#print axioms TratadoAnalisis.Dedekind.Unit.one_positiveMul_subset
#print axioms TratadoAnalisis.Dedekind.Unit.positive_one_witness
#print axioms TratadoAnalisis.Dedekind.Unit.TA_PRO_00097_positiveMul_one
#print axioms TratadoAnalisis.Dedekind.Unit.TA_THM_00044_dedMul_one

-- TA-LEAN-0006 G: envoltorios clásicos del producto y la unidad.
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersMul.TA_LEM_00023_positive_implies_zero_mem
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersMul.TA_LEM_00023_positive_iff_zero_mem
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersMul.TA_LEM_00023_characterizations
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersMul.TA_PRO_00090_positiveMul_mem
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersMul.TA_DEF_00094_positiveMulGraph_isFunc
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersMul.TA_DEF_00094_positiveMulFunction_isTriple
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersMul.TA_PRO_00093_zero_sign_trichotomy
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersMul.TA_PRO_00093_zero_sign_package
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersMul.TA_LEM_00024_negative_iff_positive_neg
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersMul.TA_LEM_00024_positive_iff_negative_neg
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersMul.TA_LEM_00024_sign_negation_package
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersMul.TA_PRO_00094_dedSignedMul_mem
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersMul.TA_PRO_00094_closure_sign_package
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersMul.TA_DEF_00097_dedMulGraph_isFunc
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersMul.TA_DEF_00097_dedMulFunction_isTriple
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersMul.TA_LEM_00025_dedNeg_involutive
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersMul.TA_PRO_00097_positiveMul_one
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersMul.TA_THM_00044_dedMul_one

-- TA-LEAN-0007 P
#print axioms TratadoAnalisis.Rationals.InverseOrder.positive_inv_le_iff
#print axioms TratadoAnalisis.Rationals.InverseOrder.positive_inv_lt_iff
#print axioms TratadoAnalisis.Rationals.InverseOrder.TA_LEM_00020_clause7_positive_inv_order
#print axioms TratadoAnalisis.Rationals.InverseOrder.TA_LEM_00020_clause7_positive_inv_le
#print axioms TratadoAnalisis.Rationals.DifferenceOrder.zero_add_rel
#print axioms TratadoAnalisis.Rationals.DifferenceOrder.TA_LEM_00020_clause1_sub_le_iff
#print axioms TratadoAnalisis.Rationals.DifferenceOrder.ratSub_lt_iff
#print axioms TratadoAnalisis.Rationals.PositiveBounds.rational_min_witness
#print axioms TratadoAnalisis.Rationals.PositiveBounds.rational_max_witness

-- TA-LEAN-0007 I0
#print axioms TratadoAnalisis.Dedekind.Nonzero.nonzeroCutsTA
#print axioms TratadoAnalisis.Dedekind.Nonzero.TA_DEF_00101_mem_nonzeroCuts_iff
#print axioms TratadoAnalisis.Dedekind.Nonzero.nonzeroCuts_subset
#print axioms TratadoAnalisis.Dedekind.Nonzero.zero_not_mem_nonzeroCuts

-- TA-LEAN-0007 I1
#print axioms TratadoAnalisis.Dedekind.PositiveInverse.dedPositiveInv
#print axioms TratadoAnalisis.Dedekind.PositiveInverse.TA_DEF_00099_mem_positiveInv_iff
#print axioms TratadoAnalisis.Dedekind.PositiveInverse.positiveInv_subset_rationals
#print axioms TratadoAnalisis.Dedekind.PositiveInverse.zero_mem_positiveInv
#print axioms TratadoAnalisis.Dedekind.PositiveInverse.positive_exterior_inverse
#print axioms TratadoAnalisis.Dedekind.PositiveInverse.TA_PRO_00098_positiveInv_mem
#print axioms TratadoAnalisis.Dedekind.PositiveInverse.TA_PRO_00099_rationalSection_positiveInv
#print axioms TratadoAnalisis.Dedekind.PositiveInverse.positiveInvGraph
#print axioms TratadoAnalisis.Dedekind.PositiveInverse.mem_positiveInvGraph_iff
#print axioms TratadoAnalisis.Dedekind.PositiveInverse.TA_DEF_00100_positiveInvGraph_isFunc
#print axioms TratadoAnalisis.Dedekind.PositiveInverse.positiveInvFunction
#print axioms TratadoAnalisis.Dedekind.PositiveInverse.TA_DEF_00100_positiveInvFunction_isTriple

-- TA-LEAN-0007 O1
#print axioms TratadoAnalisis.Dedekind.TranslationOrder.dedAdd_mono_right
#print axioms TratadoAnalisis.Dedekind.TranslationOrder.dedAdd_mono_left
#print axioms TratadoAnalisis.Dedekind.TranslationOrder.dedAdd_translate_restore
#print axioms TratadoAnalisis.Dedekind.TranslationOrder.TA_PRO_00101_dedLE_translate
#print axioms TratadoAnalisis.Dedekind.TranslationOrder.TA_PRO_00101_dedLT_translate
#print axioms TratadoAnalisis.Dedekind.TranslationOrder.TA_PRO_00101_translation_package
#print axioms TratadoAnalisis.Dedekind.TranslationOrder.TA_COR_00022_difference_positive_iff

-- TA-LEAN-0007 O2
#print axioms TratadoAnalisis.Dedekind.MultiplicativeOrder.positiveMul_mono
#print axioms TratadoAnalisis.Dedekind.MultiplicativeOrder.nonnegative_mul
#print axioms TratadoAnalisis.Dedekind.MultiplicativeOrder.TA_PRO_00103_order_compatible

-- TA-LEAN-0007 I2
#print axioms TratadoAnalisis.Dedekind.PositiveInversePrep.multiply_by_inverse_then_original
#print axioms TratadoAnalisis.Dedekind.PositiveInversePrep.quotient_lt_inverse_of_cross_bound
#print axioms TratadoAnalisis.Dedekind.PositiveInversePrep.boundary_cross_bound
#print axioms TratadoAnalisis.Dedekind.PositiveInversePrep.positive_inverse_product_witness
#print axioms TratadoAnalisis.Dedekind.PositiveInverseLaw.positive_inverse_product_lt_one
#print axioms TratadoAnalisis.Dedekind.PositiveInverseLaw.inverse_product_witness
#print axioms TratadoAnalisis.Dedekind.PositiveInverseLaw.TA_THM_00045_positive_inverse_law

-- TA-LEAN-0007 I3
#print axioms TratadoAnalisis.Dedekind.Inverse.dedSignedInv
#print axioms TratadoAnalisis.Dedekind.Inverse.TA_DEF_00102_mem_dedSignedInv_iff
#print axioms TratadoAnalisis.Dedekind.Inverse.signedInv_subset_rationals
#print axioms TratadoAnalisis.Dedekind.Inverse.TA_DEF_00102_of_positive
#print axioms TratadoAnalisis.Dedekind.Inverse.TA_DEF_00102_of_negative
#print axioms TratadoAnalisis.Dedekind.Inverse.signedInv_positive
#print axioms TratadoAnalisis.Dedekind.Inverse.signedInv_negative
#print axioms TratadoAnalisis.Dedekind.Inverse.TA_PRO_00100_signedInv_mem
#print axioms TratadoAnalisis.Dedekind.Inverse.TA_PRO_00100_sign_package
#print axioms TratadoAnalisis.Dedekind.Inverse.dedInvValue
#print axioms TratadoAnalisis.Dedekind.Inverse.TA_DEF_00103_dedInvValue_eq
#print axioms TratadoAnalisis.Dedekind.Inverse.dedInvGraph
#print axioms TratadoAnalisis.Dedekind.Inverse.mem_dedInvGraph_iff
#print axioms TratadoAnalisis.Dedekind.Inverse.TA_DEF_00103_dedInvGraph_isFunc
#print axioms TratadoAnalisis.Dedekind.Inverse.dedInvFunction
#print axioms TratadoAnalisis.Dedekind.Inverse.TA_DEF_00103_dedInvFunction_isTriple
#print axioms TratadoAnalisis.Dedekind.Inverse.TA_THM_00046_inverse_law

-- TA-LEAN-0007 I4
#print axioms TratadoAnalisis.Dedekind.Division.dedDiv
#print axioms TratadoAnalisis.Dedekind.Division.TA_DEF_00251_dedDiv_eq
#print axioms TratadoAnalisis.Dedekind.Division.dedDiv_mem
#print axioms TratadoAnalisis.Dedekind.Division.dedDivGraph
#print axioms TratadoAnalisis.Dedekind.Division.mem_dedDivGraph_iff
#print axioms TratadoAnalisis.Dedekind.Division.TA_DEF_00251_dedDivGraph_isFunc
#print axioms TratadoAnalisis.Dedekind.Division.dedDivFunction
#print axioms TratadoAnalisis.Dedekind.Division.TA_DEF_00251_dedDivFunction_isTriple

-- TA-LEAN-0007 CIERRE-I
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersInv.TA_PRO_00098_positiveInv_mem
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersInv.TA_DEF_00100_positiveInvGraph_isFunc
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersInv.TA_DEF_00100_positiveInvFunction_isTriple
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersInv.TA_PRO_00101_dedLE_translate
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersInv.TA_PRO_00101_dedLT_translate
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersInv.TA_PRO_00101_translation_package
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersInv.TA_COR_00022_difference_positive_iff
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersInv.TA_PRO_00103_order_compatible
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersInv.TA_THM_00045_positive_inverse_law
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersInv.TA_PRO_00100_signedInv_mem
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersInv.TA_PRO_00100_sign_package
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersInv.TA_DEF_00103_dedInvGraph_isFunc
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersInv.TA_DEF_00103_dedInvFunction_isTriple
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersInv.TA_THM_00046_inverse_law
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersInv.TA_DEF_00251_dedDivGraph_isFunc
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersInv.TA_DEF_00251_dedDivFunction_isTriple

-- TA-LEAN-0007 K1
#print axioms TratadoAnalisis.Dedekind.PositiveProductLaws.positiveMul_comm_of_subsets
#print axioms TratadoAnalisis.Dedekind.PositiveProductLaws.positive_factor_below
#print axioms TratadoAnalisis.Dedekind.PositiveProductLaws.positiveMul_assoc_subset
#print axioms TratadoAnalisis.Dedekind.PositiveProductLaws.positiveMul_assoc_of_subsets
#print axioms TratadoAnalisis.Dedekind.PositiveProductLaws.TA_THM_00047_positiveMul_comm
#print axioms TratadoAnalisis.Dedekind.PositiveProductLaws.TA_THM_00048_positiveMul_assoc

-- TA-LEAN-0007 K2
#print axioms TratadoAnalisis.Dedekind.PositiveDistributivity.positive_add
#print axioms TratadoAnalisis.Dedekind.PositiveDistributivity.positive_sum_repair_left
#print axioms TratadoAnalisis.Dedekind.PositiveDistributivity.positive_sum_witnesses
#print axioms TratadoAnalisis.Dedekind.PositiveDistributivity.strict_sum_split
#print axioms TratadoAnalisis.Dedekind.PositiveDistributivity.positiveMul_distrib_of_zero_mem
#print axioms TratadoAnalisis.Dedekind.PositiveDistributivity.TA_THM_00049_positiveMul_distrib

-- TA-LEAN-0007 S1
#print axioms TratadoAnalisis.Dedekind.AdditiveIdentities.dedAdd_interchange
#print axioms TratadoAnalisis.Dedekind.AdditiveIdentities.TA_LEM_00026_neg_add
#print axioms TratadoAnalisis.Dedekind.ProductSignLaws.TA_LEM_00027_product_signs
#print axioms TratadoAnalisis.Dedekind.ProductSignLaws.dedMul_zero_left
#print axioms TratadoAnalisis.Dedekind.ProductSignLaws.dedMul_zero_right
#print axioms TratadoAnalisis.Dedekind.ProductSignLaws.dedMul_neg_left
#print axioms TratadoAnalisis.Dedekind.ProductSignLaws.dedMul_neg_right
#print axioms TratadoAnalisis.Dedekind.ProductSignLaws.dedMul_neg_neg

-- TA-LEAN-0007 L1
#print axioms TratadoAnalisis.Dedekind.MultiplicativeLaws.signedMul_swap_subset
#print axioms TratadoAnalisis.Dedekind.MultiplicativeLaws.TA_THM_00050_dedMul_comm
#print axioms TratadoAnalisis.Dedekind.MultiplicativeLaws.positive_general_assoc
#print axioms TratadoAnalisis.Dedekind.MultiplicativeLaws.cut_zero_or_positive_magnitude
#print axioms TratadoAnalisis.Dedekind.MultiplicativeLaws.TA_THM_00051_dedMul_assoc

-- TA-LEAN-0007 L2
#print axioms TratadoAnalisis.Dedekind.Distributivity.add_left_neg_cancel
#print axioms TratadoAnalisis.Dedekind.Distributivity.solve_add_left
#print axioms TratadoAnalisis.Dedekind.Distributivity.solve_add_neg_right
#print axioms TratadoAnalisis.Dedekind.Distributivity.neg_add_sum_cancel
#print axioms TratadoAnalisis.Dedekind.Distributivity.add_neg_sum_eq
#print axioms TratadoAnalisis.Dedekind.Distributivity.positive_add_cut
#print axioms TratadoAnalisis.Dedekind.Distributivity.positive_general_distrib
#print axioms TratadoAnalisis.Dedekind.Distributivity.positive_factor_distrib_mixed
#print axioms TratadoAnalisis.Dedekind.Distributivity.positive_factor_distrib_negative_pair
#print axioms TratadoAnalisis.Dedekind.Distributivity.TA_PRO_00102_positive_factor_distrib
#print axioms TratadoAnalisis.Dedekind.Distributivity.dedMul_distrib_left
#print axioms TratadoAnalisis.Dedekind.Distributivity.TA_THM_00052_dedMul_distrib

-- TA-LEAN-0007 F1
#print axioms TratadoAnalisis.Dedekind.FieldPredicates.IsBinaryOperationFoundational
#print axioms TratadoAnalisis.Dedekind.FieldPredicates.RelAssociative
#print axioms TratadoAnalisis.Dedekind.FieldPredicates.RelCommutative
#print axioms TratadoAnalisis.Dedekind.FieldPredicates.RelUnit
#print axioms TratadoAnalisis.Dedekind.FieldPredicates.RelDistributive
#print axioms TratadoAnalisis.Dedekind.FieldPredicates.IsAbelianGroupFoundational
#print axioms TratadoAnalisis.Dedekind.FieldPredicates.IsFieldFoundational
#print axioms TratadoAnalisis.Dedekind.FieldPredicates.TA_CNV_00005_isField_iff
#print axioms TratadoAnalisis.Dedekind.FieldPredicates.IsTotalOrderFoundational
#print axioms TratadoAnalisis.Dedekind.FieldPredicates.IsOrderedFieldFoundational
#print axioms TratadoAnalisis.Dedekind.FieldPredicates.TA_DEF_00067_isOrderedField_iff
#print axioms TratadoAnalisis.Dedekind.FieldPredicates.IsOrderedFieldEmbeddingFoundational
#print axioms TratadoAnalisis.Dedekind.FieldPredicates.TA_DEF_00077_isEmbedding_iff
#print axioms TratadoAnalisis.Dedekind.Field.CutAdd
#print axioms TratadoAnalisis.Dedekind.Field.CutMul
#print axioms TratadoAnalisis.Dedekind.Field.cutAdd_isBinary
#print axioms TratadoAnalisis.Dedekind.Field.cutMul_isBinary
#print axioms TratadoAnalisis.Dedekind.Field.cutAdd_group
#print axioms TratadoAnalisis.Dedekind.Field.TA_THM_00053_dedekind_field
#print axioms TratadoAnalisis.Dedekind.OrderedField.TA_THM_00054_dedekind_orderedField

-- TA-LEAN-0007 E1
#print axioms TratadoAnalisis.Dedekind.EmbeddingField.rationalAdd_group
#print axioms TratadoAnalisis.Dedekind.EmbeddingField.rationals_field
#print axioms TratadoAnalisis.Dedekind.EmbeddingField.rationals_orderedField
#print axioms TratadoAnalisis.Dedekind.EmbeddingField.rationalSection_ratLE_iff
#print axioms TratadoAnalisis.Dedekind.EmbeddingField.TA_COR_00023_section_laws
#print axioms TratadoAnalisis.Dedekind.EmbeddingField.TA_COR_00023_orderedField_embedding
#print axioms TratadoAnalisis.Dedekind.EmbeddingField.dedMul_cancel_left
#print axioms TratadoAnalisis.Dedekind.EmbeddingField.rationalSection_nonzero
#print axioms TratadoAnalisis.Dedekind.EmbeddingField.TA_COR_00024_rationalSection_inv
#print axioms TratadoAnalisis.Dedekind.EmbeddingField.rationalSection_div

-- TA-LEAN-0007 CIERRE-II
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersField.TA_THM_00049_positiveMul_distrib
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersField.TA_LEM_00026_neg_add
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersField.TA_LEM_00027_product_signs
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersField.TA_THM_00051_dedMul_assoc
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersField.TA_PRO_00102_positive_factor_distrib
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersField.TA_THM_00052_dedMul_distrib
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersField.TA_THM_00053_dedekind_field
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersField.TA_THM_00054_dedekind_orderedField
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersField.TA_COR_00023_orderedField_embedding
#print axioms TratadoAnalisis.Dedekind.ClassicalWrappersField.TA_COR_00024_rationalSection_inv


-- TA-LEAN-0008 INTEGRACION CANONICA — 2026-11-22
-- 7 certificados experimentales E8-02; em explicito en las firmas pertinentes.
#print axioms TratadoAnalisis.AbstractCompleteness.Manual0008.TA_DEF_00068_exists_unique_graph_manual
#print axioms TratadoAnalisis.AbstractCompleteness.Manual0008.one_not_le_zero_manual
#print axioms TratadoAnalisis.AbstractCompleteness.Manual0008.TA_THM_00037_archimedean_graph_manual
#print axioms TratadoAnalisis.AbstractCompleteness.Manual0008.TA_THM_00037_archimedean_editorial_manual
#print axioms TratadoAnalisis.AbstractCompleteness.Manual0008.TA_PRO_00076_infimum_from_supremum_manual
#print axioms TratadoAnalisis.Dedekind.Manual0008.TA_PRO_00105_union_is_cut_manual
#print axioms TratadoAnalisis.Dedekind.Manual0008.TA_THM_00055_union_is_lub_manual
#check TratadoAnalisis.AbstractCompleteness.Manual0008.IsCanonicalNumeralGraphManual
#check TratadoAnalisis.AbstractCompleteness.Manual0008.IsArchimedeanGraphEditorialManual
-- FIN TA-LEAN-0008 INTEGRACION CANONICA


-- TA-LEAN-0009 INTEGRACION LOCAL I02 — 2026-11-23
-- Auditoria independiente I01: 15 modulos, 93 declaraciones y 34 SHA-256 conformes.
-- El parametro em permanece explicito; no hay nuevos axiomas ni eleccion global.
-- Este bloque selecciona 12 hitos; I01 conserva las 93 consultas completas.
#print axioms TratadoAnalisis.AbstractCompleteness.Density0009.rationalImageByGraph_eq_of_embedding_manual
#print axioms TratadoAnalisis.AbstractCompleteness.Density0009.rationalImageByGraph_isSubfield_manual
#print axioms TratadoAnalisis.AbstractCompleteness.Density0009.TA_PRO_00070_primeSubfield_manual
#print axioms TratadoAnalisis.AbstractCompleteness.Density0009.TA_COR_00011_numerals_in_prime_manual
#print axioms TratadoAnalisis.AbstractCompleteness.Density0009.prime_numeral_inverse_below_positive_manual
#print axioms TratadoAnalisis.AbstractCompleteness.Density0009.prime_small_mesh_cofinal_manual
#print axioms TratadoAnalisis.AbstractCompleteness.Density0009.prime_grid_first_crossing_manual
#print axioms TratadoAnalisis.AbstractCompleteness.Density0009.prime_shifted_small_mesh_successor_manual
#print axioms TratadoAnalisis.AbstractCompleteness.Density0009.TA_THM_00036_prime_dense_archimedean_manual
#print axioms TratadoAnalisis.AbstractCompleteness.Density0009.TA_THM_00036_prime_dense_complete_manual
#print axioms TratadoAnalisis.AbstractCompleteness.Density0009.TA_PRO_00078_rational_between_graph_manual
#print axioms TratadoAnalisis.AbstractCompleteness.Density0009.TA_PRO_00078_rational_graph_witness_manual
#check TratadoAnalisis.AbstractCompleteness.Density0009.RationalImageByGraphManual
#check TratadoAnalisis.AbstractCompleteness.Density0009.PrimeSubfieldCoreManual
#check TratadoAnalisis.AbstractCompleteness.Density0009.IsOrderDenseSubsetManual
-- FIN TA-LEAN-0009 INTEGRACION LOCAL I02

-- TA-LEAN-0010 / N05-I01-R4: cofinalidad de Pell y raiz positiva de dos.
#print axioms TratadoAnalisis.Chapter7_0010.N05A1.pell_invariant
#print axioms TratadoAnalisis.Chapter7_0010.N05A1.pell_numerator_positive
#print axioms TratadoAnalisis.Chapter7_0010.N05A1.pell_denominator_lower
#print axioms TratadoAnalisis.Chapter7_0010.N05A1.pell_denominator_ne_zero
#print axioms TratadoAnalisis.Chapter7_0010.N05A2.pell_rational_numerator_square
#print axioms TratadoAnalisis.Chapter7_0010.N05A2.pell_rational_denominator_square
#print axioms TratadoAnalisis.Chapter7_0010.N05A2.pell_rational_two_denominator_square
#print axioms TratadoAnalisis.Chapter7_0010.N05A2.pell_rational_balance
#print axioms TratadoAnalisis.Chapter7_0010.N05A2P02.pell_numerator_rational_mem
#print axioms TratadoAnalisis.Chapter7_0010.N05A2P02.pell_denominator_rational_mem
#print axioms TratadoAnalisis.Chapter7_0010.N05A2P02.pell_denominator_rational_nonzero
#print axioms TratadoAnalisis.Chapter7_0010.N05A2P02.pell_fraction_exists
#print axioms TratadoAnalisis.Chapter7_0010.N05A2P02.pell_fraction_unique
#print axioms TratadoAnalisis.Chapter7_0010.N05A2P03.pell_nat_rational_positive
#print axioms TratadoAnalisis.Chapter7_0010.N05A2P03.pell_numerator_rational_positive
#print axioms TratadoAnalisis.Chapter7_0010.N05A2P03.pell_denominator_rational_positive
#print axioms TratadoAnalisis.Chapter7_0010.N05A2P03.pell_fraction_positive
#print axioms TratadoAnalisis.Chapter7_0010.N05A2P03.pell_rational_square_gap
#print axioms TratadoAnalisis.Chapter7_0010.N05A2P03.pell_nat_two_eq_ratTwoTA
#print axioms TratadoAnalisis.Chapter7_0010.N05A2P03.pell_fraction_square_lt_two
#print axioms TratadoAnalisis.Chapter7_0010.N05A2P03.pell_fraction_in_sqrtTwoSet
#print axioms TratadoAnalisis.Chapter7_0010.N05A2P03.pell_fraction_square_cross
#print axioms TratadoAnalisis.Chapter7_0010.N05A3.rational_lt_nat_code_exists
#print axioms TratadoAnalisis.Chapter7_0010.N05A3.nat_rational_lt_of_nat_lt
#print axioms TratadoAnalisis.Chapter7_0010.N05A3.pell_denominator_square_unbounded
#print axioms TratadoAnalisis.Chapter7_0010.N05A3.pell_fraction_square_cofinal
#print axioms TratadoAnalisis.Chapter7_0010.N05A3.quadratic_cofinality_0010
#print axioms TratadoAnalisis.Chapter7_0010.section_two_subset_alphaTwo_square_of_cofinal_0010
#print axioms TratadoAnalisis.Chapter7_0010.alphaTwo_square_eq_section_two_of_cofinal_0010
#print axioms TratadoAnalisis.Chapter7_0010.quadratic_cofinality_proved_0010
#print axioms TratadoAnalisis.Chapter7_0010.section_two_subset_alphaTwo_square_0010
#print axioms TratadoAnalisis.Chapter7_0010.alphaTwo_square_eq_section_two_0010
#print axioms TratadoAnalisis.Chapter7_0010.alphaTwo_positive_irrational_square_two_0010
#print axioms TratadoAnalisis.Chapter7_0010.positive_cut_mem_iff_square_mem_0010
#print axioms TratadoAnalisis.Chapter7_0010.positive_cut_square_injective_0010
#print axioms TratadoAnalisis.Chapter7_0010.positive_square_two_eq_alphaTwo_0010
#print axioms TratadoAnalisis.Chapter7_0010.positive_square_two_exists_unique_0010


-- TA-LEAN-0010 I03: 31 existing declarations and 3 editorial bridges
#print axioms TratadoAnalisis.Chapter7_0010.alphaTwo_le_section_of_exterior_0010
#print axioms TratadoAnalisis.Chapter7_0010.alphaTwo_lt_section_of_exterior_0010
#print axioms TratadoAnalisis.Chapter7_0010.alphaTwo_lt_section_of_supercritical_square_0010
#print axioms TratadoAnalisis.Chapter7_0010.alphaTwo_strict_below_section_two_0010
#print axioms TratadoAnalisis.Chapter7_0010.alphaTwo_square_is_positive_product_0010
#print axioms TratadoAnalisis.Chapter7_0010.section_one_subset_alphaTwo_square_0010
#print axioms TratadoAnalisis.Chapter7_0010.section_one_le_alphaTwo_square_0010
#print axioms TratadoAnalisis.Chapter7_0010.section_one_lt_alphaTwo_square_0010
#print axioms TratadoAnalisis.Chapter7_0010.alphaTwo_square_bounds_0010
#print axioms TratadoAnalisis.Chapter7_0010.alphaTwo_square_subset_section_two_0010
#print axioms TratadoAnalisis.Chapter7_0010.alphaTwo_positive_member_square_lt_two_0010
#print axioms TratadoAnalisis.Chapter7_0010.alphaTwo_positive_members_product_lt_two_0010
#print axioms TratadoAnalisis.Chapter7_0010.alphaTwo_positive_product_subset_two_0010
#print axioms TratadoAnalisis.Chapter7_0010.alphaTwo_square_le_section_two_0010
#print axioms TratadoAnalisis.Chapter7_0010.TA_COR_00137_ded_neg_unique_0010
#print axioms TratadoAnalisis.Chapter7_0010.TA_COR_00138_rational_division_0010
#print axioms TratadoAnalisis.Chapter7_0010.TA_THM_00056_dedekind_complete_0010
#print axioms TratadoAnalisis.Chapter7_0010.IsOrderedCompletionRelational0010
#print axioms TratadoAnalisis.Chapter7_0010.TA_PRO_00106_dedekind_completion_0010
#print axioms TratadoAnalisis.Chapter7_0010.TA_COR_00027_rational_section_dense_0010
#print axioms TratadoAnalisis.Chapter7_0010.TA_PRO_00104_upper_iff_subset_0010
#print axioms TratadoAnalisis.Chapter7_0010.DedSupUnion0010
#print axioms TratadoAnalisis.Chapter7_0010.mem_dedSupUnion_iff_0010
#print axioms TratadoAnalisis.Chapter7_0010.TA_DEF_00104_union_eq_0010
#print axioms TratadoAnalisis.Chapter7_0010.TA_COR_00025_dedekind_infimum_0010
#print axioms TratadoAnalisis.Chapter7_0010.TA_COR_00026_dedekind_archimedean_0010
#print axioms TratadoAnalisis.Chapter7_0010.TA_LEM_00028_cut_mem_iff_section_lt_0010
#print axioms TratadoAnalisis.Chapter7_0010.alphaTwoCut_is_cut_0010
#print axioms TratadoAnalisis.Chapter7_0010.alphaTwoCut_positive_0010
#print axioms TratadoAnalisis.Chapter7_0010.alphaTwoCut_not_rational_0010
#print axioms TratadoAnalisis.Chapter7_0010.supremum_iff_dedekind_lub_0010
#print axioms TratadoAnalisis.Chapter7_0010.TA_DEF_00104_union_subset_rationals_0010
#print axioms TratadoAnalisis.Chapter7_0010.TA_COR_00027_rational_graph_image_dense_0010
#print axioms TratadoAnalisis.Chapter7_0010.TA_COR_00138_division_exists_unique_0010
