import TratadoAnalisis.Rationals.NatEmbedding
import TratadoAnalisis.Rationals.Division

namespace TratadoAnalisis.Rationals.Archimedean
universe u
open TratadoAnalisis.Naturals.Foundational
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Naturals.ArithmeticBridge
open TratadoAnalisis.Integers.Construction
open TratadoAnalisis.Integers.Operations
open TratadoAnalisis.Integers.Multiplication
open TratadoAnalisis.Integers.Algebra
open TratadoAnalisis.Integers.Domain
open TratadoAnalisis.Integers.Order
open TratadoAnalisis.Rationals.IntegerPrep
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.OrderPrep
open TratadoAnalisis.Rationals.PositiveDenominator
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.OrderedFieldCompatibility
open TratadoAnalisis.Rationals.NatEmbedding

theorem int_mul_one_right_rel {a : ZFSet.{u}} (ha : a ∈ integersTA) :
    IntMul a intOne a := by
  rcases intMul_exists_local ha intOne_mem_integersTA with ⟨r, _, hr⟩
  rw [intMul_one_right ha hr] at hr
  exact hr

theorem positive_form_lt_of_nat_lt {M N : Nat} (h : M < N) :
    IntLT (intPositiveForm M : ZFSet.{u}) (intPositiveForm N) := by
  refine ⟨(intEmbed_order_nat_iff M N).mp (Nat.le_of_lt h), ?_⟩
  intro he
  exact (Nat.ne_of_lt h) ((intPositiveForm_eq_iff M N).mp he)

theorem negative_form_lt_positive (M K : Nat) (hK : K ≠ 0) :
    IntLT (intNegativeForm M : ZFSet.{u}) (intPositiveForm K) := by
  refine ⟨(TA_PRO_00048_intLE_natEncode_classes_iff 0 M K 0).mpr (by omega), ?_⟩
  intro he
  have hh := (TA_PRO_00038_natEncode_class_eq_iff 0 M K 0).mp he
  omega

/-- Criterio cruzado con denominador positivo y la sección ν(N). -/
theorem fraction_lt_nat_of_cross {a : ZFSet.{u}} (ha : a ∈ integersTA)
    (K N : Nat) (hK : K ≠ 0)
    (hcross : IntLT a (intPositiveForm (K * N))) :
    RatLT (ratClass (ZFSet.pair a (intPositiveForm K)))
      (natRational (natEncode N : ZFSet.{u})) := by
  have hkNZ : (intPositiveForm K : ZFSet.{u}) ∈ intNonzeroTA :=
    mem_intNonzeroTA_iff.mpr
      ⟨intPositiveForm_mem_integersTA K, intPositiveForm_ne_zero hK⟩
  exact (TA_COR_00009_ratLT_classes_iff ha hkNZ
    (intPositiveForm_mem_integersTA N) intOne_mem_intNonzeroTA
    (intPositiveForm_pos hK) intOne_pos
    (int_mul_one_right_rel ha)
    (intEmbedGraph_mul_nat.{u, u, u, u} K N).2.2.2).mpr hcross

/-- TA-THM-00031: cota natural por representante de denominador positivo.
La cuantificación es sobre omegaTA; Nat sólo aporta códigos locales. -/
theorem TA_THM_00031_rational_archimedean {q : ZFSet.{u}}
    (hq : q ∈ rationalsTA) :
    ∃ n : ZFSet.{u}, n ∈ omegaTA ∧ RatLT q (natRational n) := by
  rcases TA_LEM_00013_positive_denominator.{u, u} hq with ⟨a, K, ha, hK, _, hqRep⟩
  rw [hqRep]
  rcases int_sign_normal_exists ha with ha0 | ⟨M, _, haM⟩ | ⟨M, _, haM⟩
  · refine ⟨natEncode 1, natEncode_mem_omegaTA 1,
      fraction_lt_nat_of_cross ha K 1 hK ?_⟩
    rw [ha0, Nat.mul_one]
    exact intPositiveForm_pos hK
  · refine ⟨natEncode (M + 1), natEncode_mem_omegaTA (M + 1),
      fraction_lt_nat_of_cross ha K (M + 1) hK ?_⟩
    rw [haM]
    apply positive_form_lt_of_nat_lt
    have hle : M + 1 ≤ K * (M + 1) := by
      simpa only [Nat.one_mul] using
        Nat.mul_le_mul_right (M + 1) (Nat.one_le_iff_ne_zero.mpr hK)
    omega
  · refine ⟨natEncode 1, natEncode_mem_omegaTA 1,
      fraction_lt_nat_of_cross ha K 1 hK ?_⟩
    rw [haM, Nat.mul_one]
    exact negative_form_lt_positive M K hK

/-- Forma completamente relacional: el valor está en el grafo conjuntista ν. -/
theorem TA_THM_00031_rational_archimedean_graph {q : ZFSet.{u}}
    (hq : q ∈ rationalsTA) :
    ∃ n : ZFSet.{u}, n ∈ omegaTA ∧
      ∃ nq : ZFSet.{u}, ZFSet.pair n nq ∈ natEmbeddingGraph ∧ RatLT q nq := by
  rcases TA_THM_00031_rational_archimedean hq with ⟨n, hn, hlt⟩
  exact ⟨n, hn, natRational n, natRational_graph hn, hlt⟩

end TratadoAnalisis.Rationals.Archimedean
