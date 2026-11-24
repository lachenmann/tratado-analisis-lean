import TratadoAnalisis.Rationals.OrderedFieldCompatibility
import TratadoAnalisis.Rationals.NoZeroDivisors

namespace TratadoAnalisis.Rationals.StrictOrder

open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Integers.Construction
open TratadoAnalisis.Integers.Operations
open TratadoAnalisis.Integers.Multiplication
open TratadoAnalisis.Integers.Algebra
open TratadoAnalisis.Rationals.IntegerPrep
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.Field
open TratadoAnalisis.Rationals.OrderPrep
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.OrderedFieldCompatibility
open TratadoAnalisis.Rationals.NoZeroDivisors

/-! # TA-LEM-00015 — positividad y escalamiento estricto en Q -/

theorem ratMul_zero_left
    {y : ZFSet} (hy : y ∈ rationalsTA) :
    RatMul ratZero y ratZero := by
  rcases exists_ratClass_pair_of_mem hy with ⟨c, d, hc, hd, rfl⟩
  have hdI := (mem_intNonzeroTA_iff.mp hd).1
  rcases intMul_exists intZero_mem_integersTA hc with ⟨zc, hzcI, hzc⟩
  rcases intMul_exists intOne_mem_integersTA hdI with ⟨od, _hodI, hod⟩
  have hodNZ := intNonzero_mul_closed intOne_mem_intNonzeroTA hd hod
  have hClassZero : ratClass (ZFSet.pair zc od) = ratZero :=
    (TA_PRO_00061_ratClass_eq_zero_iff hzcI hodNZ).mpr
      (intMul_zero_left hc hzc)
  have h := ratMulGraph_classes intZero_mem_integersTA
    intOne_mem_intNonzeroTA hc hd hzc hod
  rw [hClassZero] at h
  simpa [RatMul, ratZero] using h

theorem ratMul_zero_right
    {x : ZFSet} (hx : x ∈ rationalsTA) :
    RatMul x ratZero ratZero := by
  have hLeft := ratMul_zero_left hx
  rcases ratMul_exists hx ratZero_mem_rationalsTA with ⟨z, _hz, hz⟩
  have hEq : ratZero = z :=
    ratMul_comm ratZero_mem_rationalsTA hx hLeft hz
  rw [← hEq] at hz
  exact hz

theorem ratZero_lt_one : RatLT ratZero ratOne := by
  have hLE : RatLE ratZero ratOne :=
    (TA_PRO_00066_ratEmbed_order_iff
      intZero_mem_integersTA intOne_mem_integersTA
      ratEmbedGraph_zero ratEmbedGraph_one).mp intOne_pos.1
  exact ⟨hLE, TA_PRO_00059_ratZero_ne_one⟩

theorem ratPositive_mul
    {x y xy : ZFSet}
    (hx : x ∈ rationalsTA)
    (hy : y ∈ rationalsTA)
    (hxy : RatMul x y xy)
    (h0x : RatLT ratZero x)
    (h0y : RatLT ratZero y) :
    RatLT ratZero xy := by
  have hZeroMul := ratMul_zero_left hy
  have hNonnegative : RatLE ratZero xy :=
    ratLE_mul_nonnegative_compat
      ratZero_mem_rationalsTA hx hy h0x.1 h0y.1 hZeroMul hxy
  refine ⟨hNonnegative, ?_⟩
  intro hxyZero
  rcases TA_COR_00007_no_zero_divisors hx hy hxy hxyZero.symm with hxZero | hyZero
  · exact h0x.2 hxZero.symm
  · exact h0y.2 hyZero.symm

theorem ratInv_positive
    {x ix : ZFSet}
    (hx : x ∈ rationalsTA)
    (hix : RatInv x ix)
    (h0x : RatLT ratZero x) :
    RatLT ratZero ix := by
  have hxNZ : x ∈ ratNonzeroTA :=
    mem_ratNonzeroTA_iff.mpr ⟨hx, fun h => h0x.2 h.symm⟩
  have hLaw := TA_PRO_00063_inverse_law hxNZ hix
  have hixMem : ix ∈ rationalsTA :=
    (mem_ratNonzeroTA_iff.mp
      (funcFoundational_value_mem ratInvGraph_isFunc hix)).1
  have hixNZ : ix ≠ ratZero := by
    intro hixZero
    have hProductOne : RatMul x ratZero ratOne := by
      rw [← hixZero]
      exact hLaw.1
    have hProductZero := ratMul_zero_right hx
    have hOneZero : ratOne = ratZero :=
      RatMul_unique hx ratZero_mem_rationalsTA hProductOne hProductZero
    exact TA_PRO_00059_ratZero_ne_one hOneZero.symm
  have hZeroLE : RatLE ratZero ix := by
    rcases ratLE_total ratZero_mem_rationalsTA hixMem with h | h
    · exact h
    · have hOneLEZero : RatLE ratOne ratZero :=
        ratLE_mul_nonnegative_compat hixMem ratZero_mem_rationalsTA hx
          h h0x.1 hLaw.2 (ratMul_zero_left hx)
      have hZeroOne : ratZero = ratOne :=
        ratLE_antisymm ratZero_mem_rationalsTA ratOne_mem_rationalsTA
          ratZero_lt_one.1 hOneLEZero
      exact False.elim (TA_PRO_00059_ratZero_ne_one hZeroOne)
  exact ⟨hZeroLE, fun h => hixNZ h.symm⟩

theorem ratMul_cancel_right_of_nonzero
    {x y z xz yz : ZFSet}
    (hx : x ∈ rationalsTA)
    (hy : y ∈ rationalsTA)
    (hz : z ∈ rationalsTA)
    (hzNZ : z ≠ ratZero)
    (hxz : RatMul x z xz)
    (hyz : RatMul y z yz)
    (hEq : xz = yz) :
    x = y := by
  have hzNonzero : z ∈ ratNonzeroTA :=
    mem_ratNonzeroTA_iff.mpr ⟨hz, hzNZ⟩
  rcases exists_inverse_of_mem_ratNonzeroTA hzNonzero with
    ⟨iz, hizNonzero, _hInv, hZInv, _hInvZ⟩
  have hiz : iz ∈ rationalsTA := (mem_ratNonzeroTA_iff.mp hizNonzero).1
  have hxzMem : xz ∈ rationalsTA :=
    funcFoundational_value_mem ratMulGraph_isFunc hxz
  rcases ratMul_exists hxzMem hiz with ⟨tail, _htail, htail⟩
  rcases ratMul_exists hx ratOne_mem_rationalsTA with ⟨xOne, _hxOne, hxOne⟩
  rcases ratMul_exists hy ratOne_mem_rationalsTA with ⟨yOne, _hyOne, hyOne⟩
  have hyzAtXz : RatMul y z xz := by
    rw [hEq]
    exact hyz
  have hAssocX : tail = xOne :=
    ratMul_assoc hx hz hiz hxz htail hZInv hxOne
  have hAssocY : tail = yOne :=
    ratMul_assoc hy hz hiz hyzAtXz htail hZInv hyOne
  have hxOneValue : xOne = x := ratMul_one_right hx hxOne
  have hyOneValue : yOne = y := ratMul_one_right hy hyOne
  exact hxOneValue.symm.trans
    (hAssocX.symm.trans (hAssocY.trans hyOneValue))

theorem ratLT_mul_positive_right
    {x y z xz yz : ZFSet}
    (hx : x ∈ rationalsTA)
    (hy : y ∈ rationalsTA)
    (hz : z ∈ rationalsTA)
    (hxy : RatLT x y)
    (h0z : RatLT ratZero z)
    (hxz : RatMul x z xz)
    (hyz : RatMul y z yz) :
    RatLT xz yz := by
  have hLE : RatLE xz yz :=
    ratLE_mul_nonnegative_compat hx hy hz hxy.1 h0z.1 hxz hyz
  refine ⟨hLE, ?_⟩
  intro hEq
  exact hxy.2
    (ratMul_cancel_right_of_nonzero hx hy hz
      (fun h => h0z.2 h.symm) hxz hyz hEq)

theorem TA_LEM_00015_positivity_strict_scaling :
    (∀ {x y xy : ZFSet},
      x ∈ rationalsTA → y ∈ rationalsTA →
      RatMul x y xy →
      RatLT ratZero x → RatLT ratZero y →
      RatLT ratZero xy) ∧
    (∀ {x ix : ZFSet},
      x ∈ rationalsTA → RatInv x ix →
      RatLT ratZero x → RatLT ratZero ix) ∧
    (∀ {x y z xz yz : ZFSet},
      x ∈ rationalsTA → y ∈ rationalsTA → z ∈ rationalsTA →
      RatLT x y → RatLT ratZero z →
      RatMul x z xz → RatMul y z yz →
      RatLT xz yz) := by
  constructor
  · intro x y xy hx hy hxy h0x h0y
    exact ratPositive_mul hx hy hxy h0x h0y
  constructor
  · intro x ix hx hix h0x
    exact ratInv_positive hx hix h0x
  · intro x y z xz yz hx hy hz hxy h0z hxz hyz
    exact ratLT_mul_positive_right hx hy hz hxy h0z hxz hyz

end TratadoAnalisis.Rationals.StrictOrder
