import TratadoAnalisis.Rationals.Signs
import TratadoAnalisis.Rationals.Density

namespace TratadoAnalisis.Rationals.Division
universe u
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.Field
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.Density

/-- TA-DEF-00061: división como composición relacional, no selección de inverso. -/
def RatDiv (x y z : ZFSet.{u}) : Prop :=
  ∃ iy : ZFSet.{u}, RatInv y iy ∧ RatMul x iy z

theorem TA_DEF_00061_ratDiv_iff {x y z : ZFSet.{u}} :
    RatDiv x y z ↔ ∃ iy : ZFSet.{u}, RatInv y iy ∧ RatMul x iy z :=
  Iff.rfl

theorem ratDiv_exists {x y : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ ratNonzeroTA) :
    ∃ z : ZFSet.{u}, z ∈ rationalsTA ∧ RatDiv x y z := by
  rcases exists_inverse_of_mem_ratNonzeroTA hy with ⟨iy, hiy, hi, _, _⟩
  rcases ratMul_exists hx (mem_ratNonzeroTA_iff.mp hiy).1 with ⟨z, hz, hm⟩
  exact ⟨z, hz, iy, hi, hm⟩

theorem RatDiv_unique {x y z w : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ ratNonzeroTA)
    (hz : RatDiv x y z) (hw : RatDiv x y w) : z = w := by
  rcases hz with ⟨iy, hi, hm⟩
  rcases hw with ⟨iy', hi', hm'⟩
  have he := RatInv_unique hy hi' hi
  subst iy'
  exact RatMul_unique hx
    (mem_ratNonzeroTA_iff.mp (funcFoundational_value_mem ratInvGraph_isFunc hi)).1
    hm hm'

/-- TA-THM-00030: reutiliza la densidad 00034 ya especializada a Q. -/
theorem TA_THM_00030_rational_density {x y : ZFSet.{u}}
    (hx : x ∈ rationalsTA) (hy : y ∈ rationalsTA) (hxy : RatLT x y) :
    ∃ m : ZFSet.{u}, m ∈ rationalsTA ∧ RatLT x m ∧ RatLT m y :=
  TA_THM_00034_rational_density hx hy hxy

end TratadoAnalisis.Rationals.Division
