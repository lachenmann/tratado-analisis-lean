import TratadoAnalisis.Rationals.StrictOrder

namespace TratadoAnalisis.Rationals.SquareMonotonicity

open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.OrderedFieldCompatibility
open TratadoAnalisis.Rationals.StrictOrder

/-!
# E2a — estricta monotonía del cuadrado en Q_{\ge 0}

Certificación Lean de TA-LEM-00018.

El manuscrito demuestra el resultado mediante

  (y - x)(y + x) = y² - x².

Aquí certificamos el mismo enunciado usando directamente la
infraestructura relacional ya cerrada:

  x² ≤ xy < y².

No se introduce una operación funcional global de cuadrado,
ni una instancia estándar de cuerpo u orden.
-/

/--
Transitividad mixta local:

  a ≤ b ∧ b < c  →  a < c.

Helper técnico no numerado del tratado.
-/
theorem ratLT_of_le_of_lt_local
    {a b c : ZFSet}
    (ha : a ∈ rationalsTA)
    (hb : b ∈ rationalsTA)
    (hc : c ∈ rationalsTA)
    (hab : RatLE a b)
    (hbc : RatLT b c) :
    RatLT a c := by
  refine ⟨ratLE_trans ha hb hc hab hbc.1, ?_⟩
  intro hac
  have hcb : RatLE c b := by
    rw [← hac]
    exact hab
  have hbcEq : b = c :=
    ratLE_antisymm hb hc hbc.1 hcb
  exact hbc.2 hbcEq

/--
TA-LEM-00018 — Estricta monotonía del cuadrado
en los racionales no negativos.

Si

  0_Q ≤ x < y,

y `xx`, `yy` son respectivamente los valores relacionales
de `x*x` e `y*y`, entonces

  xx < yy.
-/
theorem TA_LEM_00018_square_strict_mono_nonnegative
    {x y xx yy : ZFSet}
    (hx : x ∈ rationalsTA)
    (hy : y ∈ rationalsTA)
    (h0x : RatLE ratZero x)
    (hxy : RatLT x y)
    (hxx : RatMul x x xx)
    (hyy : RatMul y y yy) :
    RatLT xx yy := by

  -- 0 ≤ y por transitividad: 0 ≤ x ≤ y.
  have h0yLE : RatLE ratZero y :=
    ratLE_trans
      ratZero_mem_rationalsTA hx hy
      h0x hxy.1

  -- La desigualdad es estricta: y ≠ 0.
  have h0yNE : ratZero ≠ y := by
    intro h0y
    have hxy0 : RatLT x ratZero := by
      rw [← h0y] at hxy
      exact hxy
    have hx0 : x = ratZero :=
      ratLE_antisymm
        hx ratZero_mem_rationalsTA
        hxy0.1 h0x
    exact hxy0.2 hx0

  have h0y : RatLT ratZero y :=
    ⟨h0yLE, h0yNE⟩

  -- Productos intermedios y*x y x*y.
  rcases ratMul_exists hy hx with
    ⟨yx, hyxMem, hyx⟩

  rcases ratMul_exists hx hy with
    ⟨xy, hxyMem, hxyMul⟩

  -- x² ≤ yx, multiplicando x ≤ y por x ≥ 0.
  have hxxLEyx : RatLE xx yx :=
    ratLE_mul_nonnegative_compat
      hx hy hx
      hxy.1 h0x
      hxx hyx

  -- yx = xy por conmutatividad.
  have hyxEqxy : yx = xy :=
    ratMul_comm hy hx hyx hxyMul

  have hxxLExy : RatLE xx xy := by
    rw [← hyxEqxy]
    exact hxxLEyx

  -- xy < y², multiplicando x < y por y > 0.
  have hxyLTyy : RatLT xy yy :=
    ratLT_mul_positive_right
      hx hy hy
      hxy h0y
      hxyMul hyy

  -- Membresía de los cuadrados por existencia + unicidad relacional.
  rcases ratMul_exists hx hx with
    ⟨xx', hxx'Mem, hxx'⟩

  have hxxEq : xx = xx' :=
    RatMul_unique hx hx hxx hxx'

  have hxxMem : xx ∈ rationalsTA := by
    rw [hxxEq]
    exact hxx'Mem

  rcases ratMul_exists hy hy with
    ⟨yy', hyy'Mem, hyy'⟩

  have hyyEq : yy = yy' :=
    RatMul_unique hy hy hyy hyy'

  have hyyMem : yy ∈ rationalsTA := by
    rw [hyyEq]
    exact hyy'Mem

  -- x² ≤ xy < y².
  exact ratLT_of_le_of_lt_local
    hxxMem hxyMem hyyMem
    hxxLExy hxyLTyy

end TratadoAnalisis.Rationals.SquareMonotonicity