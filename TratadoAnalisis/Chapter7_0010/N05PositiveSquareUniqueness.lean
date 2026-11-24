import TratadoAnalisis.Chapter7_0010.AlphaTwoSquareSandwich0010
import TratadoAnalisis.Rationals.Archimedean
import TratadoAnalisis.Rationals.PositiveProducts
import Mathlib.Tactic.Ring

/-!
TA-LEAN-0010 / N05-A1-P01: sonda aritmética de las aproximaciones de Pell.
No modifica ni amplía los resultados de los módulos racionales certificados.
Nat representa aquí códigos naturales locales. Su transporte a ZFSet,
NatEmbedding y RatMul será una obligación posterior de N05-A2.
-/

namespace TratadoAnalisis.Chapter7_0010.N05A1

set_option autoImplicit false

/-- Sucesión aritmética local: (a₀,b₀)=(1,1),
    (aₙ₊₁,bₙ₊₁)=(3aₙ+4bₙ, 2aₙ+3bₙ). -/
def pellPair : Nat → Nat × Nat
  | 0 => (1, 1)
  | n + 1 =>
      (3 * (pellPair n).1 + 4 * (pellPair n).2,
       2 * (pellPair n).1 + 3 * (pellPair n).2)

@[simp] theorem pellPair_zero : pellPair 0 = (1, 1) := rfl

@[simp] theorem pellPair_succ (n : Nat) :
    pellPair (n + 1) =
      (3 * (pellPair n).1 + 4 * (pellPair n).2,
       2 * (pellPair n).1 + 3 * (pellPair n).2) := rfl

/-- Identidad de balance polinómico, válida para cualesquiera a,b naturales.
    Las multiplicaciones conmutativas se normalizan antes de omega;
    se usa la táctica ring solo para una identidad de Nat, sin raíz cuadrada. -/
private theorem pell_step_balance (a b : Nat) :
    (3*a + 4*b) * (3*a + 4*b) + 1 + 2 * (b*b) =
      2 * ((2*a + 3*b) * (2*a + 3*b)) + (a*a + 1) := by
  ring

/-- El paso recurrente conserva a²+1=2b². -/
private theorem pell_step_invariant (a b : Nat)
    (h : a*a + 1 = 2 * (b*b)) :
    (3*a + 4*b) * (3*a + 4*b) + 1 =
      2 * ((2*a + 3*b) * (2*a + 3*b)) := by
  have hbalance := pell_step_balance a b
  omega

/-- Invariante de Pell para todos los índices naturales. -/
theorem pell_invariant (n : Nat) :
    (pellPair n).1 * (pellPair n).1 + 1 =
      2 * ((pellPair n).2 * (pellPair n).2) := by
  induction n with
  | zero => decide
  | succ n ih =>
      change
        (3 * (pellPair n).1 + 4 * (pellPair n).2) *
          (3 * (pellPair n).1 + 4 * (pellPair n).2) + 1 =
        2 * ((2 * (pellPair n).1 + 3 * (pellPair n).2) *
          (2 * (pellPair n).1 + 3 * (pellPair n).2))
      exact pell_step_invariant (pellPair n).1 (pellPair n).2 ih

/-- Todos los numeradores son positivos. -/
theorem pell_numerator_positive (n : Nat) :
    0 < (pellPair n).1 := by
  induction n with
  | zero => decide
  | succ n ih =>
      change 0 < 3 * (pellPair n).1 + 4 * (pellPair n).2
      omega

/-- El denominador supera n y, en particular, nunca es nulo. -/
theorem pell_denominator_lower (n : Nat) :
    n + 1 ≤ (pellPair n).2 := by
  induction n with
  | zero => decide
  | succ n ih =>
      change n + 1 + 1 ≤ 2 * (pellPair n).1 + 3 * (pellPair n).2
      omega

theorem pell_denominator_ne_zero (n : Nat) :
    (pellPair n).2 ≠ 0 := by
  have h := pell_denominator_lower n
  omega

#check pellPair
#check pell_invariant
#check pell_numerator_positive
#check pell_denominator_lower
#check pell_denominator_ne_zero
#print axioms pell_invariant
#print axioms pell_numerator_positive
#print axioms pell_denominator_lower
#print axioms pell_denominator_ne_zero

end TratadoAnalisis.Chapter7_0010.N05A1


/-!
TA-LEAN-0010 — N05-A2-P01: transporte algebraico de Pell a los racionales
conjuntistas del tratado, expresado mediante RatAdd y RatMul. La primera
parte del archivo es una copia byte a byte de la sonda N05-A1-R1 verificada.
No certifica todavía divisiones, desigualdades racionales, cofinalidad,
THM-00057 ni COR-00028.
-/

namespace TratadoAnalisis.Chapter7_0010.N05A2

universe u
set_option autoImplicit false

open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Naturals.Foundational
open TratadoAnalisis.Naturals.ArithmeticBridge
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.NatEmbedding
open TratadoAnalisis.Chapter7_0010.N05A1

/-- El cuadrado del numerador de Pell se transporta mediante el producto
relacional construido en el tratado, sin utilizar los racionales de Mathlib. -/
theorem pell_rational_numerator_square (n : Nat) :
    RatMul
      (natRational (natEncode (pellPair n).1 : ZFSet.{u}))
      (natRational (natEncode (pellPair n).1))
      (natRational (natEncode ((pellPair n).1 * (pellPair n).1))) := by
  exact natRational_mul_nat (pellPair n).1 (pellPair n).1

/-- Producto relacional del denominador por sí mismo. -/
theorem pell_rational_denominator_square (n : Nat) :
    RatMul
      (natRational (natEncode (pellPair n).2 : ZFSet.{u}))
      (natRational (natEncode (pellPair n).2))
      (natRational (natEncode ((pellPair n).2 * (pellPair n).2))) := by
  exact natRational_mul_nat (pellPair n).2 (pellPair n).2

/-- Producto relacional de 2 por el cuadrado natural del denominador. -/
theorem pell_rational_two_denominator_square (n : Nat) :
    RatMul
      (natRational (natEncode (2 : Nat) : ZFSet.{u}))
      (natRational (natEncode ((pellPair n).2 * (pellPair n).2)))
      (natRational (natEncode (2 * ((pellPair n).2 * (pellPair n).2)))) := by
  exact natRational_mul_nat 2 ((pellPair n).2 * (pellPair n).2)

/-- Traslado relacional de a_n² + 1 = 2 b_n². El resultado
mantiene la suma y los numerales en la construcción racional propia. -/
theorem pell_rational_balance (n : Nat) :
    RatAdd
      (natRational (natEncode ((pellPair n).1 * (pellPair n).1) : ZFSet.{u}))
      (natRational (natEncode (1 : Nat)))
      (natRational (natEncode (2 * ((pellPair n).2 * (pellPair n).2)))) := by
  rw [← pell_invariant n]
  exact natRational_add_nat ((pellPair n).1 * (pellPair n).1) 1

#check pell_rational_numerator_square
#check pell_rational_denominator_square
#check pell_rational_two_denominator_square
#check pell_rational_balance
#print axioms pell_rational_numerator_square
#print axioms pell_rational_denominator_square
#print axioms pell_rational_two_denominator_square
#print axioms pell_rational_balance

end TratadoAnalisis.Chapter7_0010.N05A2


/-!
TA-LEAN-0010 / N05-A2-P02 (sonda, sin integración):
El cociente a_n / b_n existe como relación RatDiv del tratado y es único.
La nueva obligación aritmética es que la imagen racional de b_n pertenece
al portador de racionales no nulos. No se afirma todavía p_n² < 2.
-/

namespace TratadoAnalisis.Chapter7_0010.N05A2P02

universe u
set_option autoImplicit false

open TratadoAnalisis.Naturals.Foundational
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Naturals.ArithmeticBridge
open TratadoAnalisis.Integers.Construction
open TratadoAnalisis.Integers.Operations
open TratadoAnalisis.Integers.Multiplication
open TratadoAnalisis.Integers.Algebra
open TratadoAnalisis.Integers.Domain
open TratadoAnalisis.Integers.Order
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.Field
open TratadoAnalisis.Rationals.NatEmbedding
open TratadoAnalisis.Rationals.Division
open TratadoAnalisis.Chapter7_0010.N05A1

/-- La imagen del numerador es un racional del tratado. -/
theorem pell_numerator_rational_mem (n : Nat) :
    natRational (natEncode (pellPair n).1 : ZFSet.{u}) ∈ rationalsTA := by
  exact natRational_mem (natEncode_mem_omegaTA (pellPair n).1)

/-- La imagen del denominador es un racional del tratado. -/
theorem pell_denominator_rational_mem (n : Nat) :
    natRational (natEncode (pellPair n).2 : ZFSet.{u}) ∈ rationalsTA := by
  exact natRational_mem (natEncode_mem_omegaTA (pellPair n).2)

/-- b_n ≥ n+1 implica que la imagen racional de b_n no es cero.
    Se usa la inyectividad de ν y de la forma entera positiva. -/
theorem pell_denominator_rational_nonzero (n : Nat) :
    natRational (natEncode (pellPair n).2 : ZFSet.{u}) ∈ ratNonzeroTA := by
  have hbQ :
      natRational (natEncode (pellPair n).2 : ZFSet.{u}) ∈ rationalsTA :=
    pell_denominator_rational_mem n
  refine mem_ratNonzeroTA_iff.mpr ⟨hbQ, ?_⟩
  intro hbZero
  have hZero :
      natRational (natEncode (0 : Nat) : ZFSet.{u}) = ratZero := by
    exact TA_COR_00008_natRational_zero
  have hCodes :
      (natEncode (pellPair n).2 : ZFSet.{u}) =
        natEncode (0 : Nat) :=
    TA_COR_00008_natRational_injective
      (natEncode_mem_omegaTA (pellPair n).2)
      (natEncode_mem_omegaTA 0)
      (hbZero.trans hZero.symm)
  have hPositiveForms :
      (intPositiveForm (pellPair n).2 : ZFSet.{u}) =
        intPositiveForm 0 := by
    simpa only [intPositiveForm] using
      (congrArg
        (fun z : ZFSet.{u} => intClass (ZFSet.pair z (natEncode (0 : Nat) : ZFSet.{u})))
        hCodes)
  have hbNatZero : (pellPair n).2 = 0 :=
    (intPositiveForm_eq_iff (pellPair n).2 0).mp hPositiveForms
  exact (pell_denominator_ne_zero n) hbNatZero

/-- Existencia relacional de a_n/b_n sin elección global de representantes. -/
theorem pell_fraction_exists (n : Nat) :
    ∃ p : ZFSet.{u}, p ∈ rationalsTA ∧
      RatDiv
        (natRational (natEncode (pellPair n).1))
        (natRational (natEncode (pellPair n).2)) p := by
  exact ratDiv_exists
    (pell_numerator_rational_mem n)
    (pell_denominator_rational_nonzero n)

/-- Unicidad del cociente relacional para un índice fijo. -/
theorem pell_fraction_unique (n : Nat) {p q : ZFSet.{u}}
    (hp : RatDiv
      (natRational (natEncode (pellPair n).1))
      (natRational (natEncode (pellPair n).2)) p)
    (hq : RatDiv
      (natRational (natEncode (pellPair n).1))
      (natRational (natEncode (pellPair n).2)) q) : p = q := by
  exact RatDiv_unique
    (pell_numerator_rational_mem n)
    (pell_denominator_rational_nonzero n) hp hq

#check pell_numerator_rational_mem
#check pell_denominator_rational_mem
#check pell_denominator_rational_nonzero
#check pell_fraction_exists
#check pell_fraction_unique
#print axioms pell_numerator_rational_mem
#print axioms pell_denominator_rational_mem
#print axioms pell_denominator_rational_nonzero
#print axioms pell_fraction_exists
#print axioms pell_fraction_unique

end TratadoAnalisis.Chapter7_0010.N05A2P02


/-!
TA-LEAN-0010 / N05-A2-P03 (sonda experimental).
Transporte del orden y del cuadrado para cualquier cociente relacional p=a_n/b_n.
N05-A1, N05-A2-P01 y N05-A2-P02-R2 se conservan exactamente,
salvo un nuevo import de PositiveProducts para reutilizar sus lemas.
No establece cofinalidad ni introduce una seleccion global de cocientes.
-/

namespace TratadoAnalisis.Chapter7_0010.N05A2P03

universe u
set_option autoImplicit false

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
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.Field
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.OrderedFieldCompatibility
open TratadoAnalisis.Rationals.StrictOrder
open TratadoAnalisis.Rationals.NatEmbedding
open TratadoAnalisis.Rationals.Archimedean
open TratadoAnalisis.Rationals.IrrationalitySqrtTwo
open TratadoAnalisis.Rationals.SqrtTwoSet
open TratadoAnalisis.Rationals.NoSupremumSqrtTwo
open TratadoAnalisis.Rationals.Signs
open TratadoAnalisis.Rationals.Division
open TratadoAnalisis.Rationals.PositiveProducts
open TratadoAnalisis.Chapter7_0010.N05A1
open TratadoAnalisis.Chapter7_0010.N05A2
open TratadoAnalisis.Chapter7_0010.N05A2P02

/-- Transporta la positividad de un natural local a su imagen racional
    mediante el orden entero y el embedding inyectivo; sin Nat cast a Q. -/
theorem pell_nat_rational_positive (k : Nat) (hk : 0 < k) :
    RatLT (ratZero : ZFSet.{u}) (natRational (natEncode k)) := by
  have hi :=
    TratadoAnalisis.Rationals.Archimedean.positive_form_lt_of_nat_lt.{u} hk
  have hz0 : (intPositiveForm (0 : Nat) : ZFSet.{u}) ∈ integersTA :=
    intPositiveForm_mem_integersTA 0
  have hzk : (intPositiveForm k : ZFSet.{u}) ∈ integersTA :=
    intPositiveForm_mem_integersTA k
  have hG0 :
      ZFSet.pair (intPositiveForm (0 : Nat) : ZFSet.{u})
        (natRational (natEncode (0 : Nat))) ∈ ratEmbedGraph :=
    ratEmbedGraph_value hz0
  have hGk :
      ZFSet.pair (intPositiveForm k : ZFSet.{u})
        (natRational (natEncode k)) ∈ ratEmbedGraph :=
    ratEmbedGraph_value hzk
  have hle :
      RatLE (natRational (natEncode (0 : Nat) : ZFSet.{u}))
        (natRational (natEncode k)) :=
    (TA_PRO_00066_ratEmbed_order_iff hz0 hzk hG0 hGk).mp hi.1
  have hne :
      (natRational (natEncode (0 : Nat) : ZFSet.{u})) ≠
        natRational (natEncode k) := by
    intro heq
    have hGk0 :
        ZFSet.pair (intPositiveForm k : ZFSet.{u})
          (natRational (natEncode (0 : Nat))) ∈ ratEmbedGraph := by
      rw [heq]
      exact hGk
    exact hi.2 (ratEmbedGraph_injective hG0 hGk0)
  have hlt :
      RatLT (natRational (natEncode (0 : Nat) : ZFSet.{u}))
        (natRational (natEncode k)) := ⟨hle, hne⟩
  have hZero :
      natRational (natEncode (0 : Nat) : ZFSet.{u}) = ratZero := by
    exact TA_COR_00008_natRational_zero
  rw [hZero] at hlt
  exact hlt

/-- El numerador de Pell es positivo también en Q construido. -/
theorem pell_numerator_rational_positive (n : Nat) :
    RatLT (ratZero : ZFSet.{u})
      (natRational (natEncode (pellPair n).1)) :=
  pell_nat_rational_positive (pellPair n).1 (pell_numerator_positive n)

/-- El denominador de Pell es positivo también en Q construido. -/
theorem pell_denominator_rational_positive (n : Nat) :
    RatLT (ratZero : ZFSet.{u})
      (natRational (natEncode (pellPair n).2)) := by
  have hb : 0 < (pellPair n).2 := by
    have h := pell_denominator_lower n
    omega
  exact pell_nat_rational_positive (pellPair n).2 hb

/-- Todo cociente relacional de Pell es racional positivo. -/
theorem pell_fraction_positive (n : Nat) {p : ZFSet.{u}}
    (hp : RatDiv
      (natRational (natEncode (pellPair n).1))
      (natRational (natEncode (pellPair n).2)) p) :
    RatLT ratZero p := by
  exact ratDiv_positive
    (pell_numerator_rational_mem n) (pell_denominator_rational_mem n)
    (pell_numerator_rational_positive n)
    (pell_denominator_rational_positive n) hp

/-- A_n² < 2 B_n², obtenido del balance A_n²+1=2B_n². -/
theorem pell_rational_square_gap (n : Nat) :
    RatLT
      (natRational (natEncode ((pellPair n).1 * (pellPair n).1) : ZFSet.{u}))
      (natRational (natEncode (2 * ((pellPair n).2 * (pellPair n).2)))) := by
  have haa :
      natRational (natEncode ((pellPair n).1 * (pellPair n).1) : ZFSet.{u}) ∈ rationalsTA :=
    natRational_mem (natEncode_mem_omegaTA _)
  have hOne :
      natRational (natEncode (1 : Nat) : ZFSet.{u}) ∈ rationalsTA :=
    natRational_mem (natEncode_mem_omegaTA 1)
  have hOnePos :
      RatLT (ratZero : ZFSet.{u}) (natRational (natEncode (1 : Nat))) :=
    pell_nat_rational_positive 1 (by decide)
  rcases ratAdd_exists haa ratZero_mem_rationalsTA with ⟨aaZero, _, hAA0⟩
  have hAAZeroEq : aaZero =
      natRational (natEncode ((pellPair n).1 * (pellPair n).1) : ZFSet.{u}) :=
    ratAdd_zero_right haa hAA0
  have hLT := ratLT_add_left_local
    ratZero_mem_rationalsTA hOne haa hOnePos hAA0
    (pell_rational_balance n)
  rw [hAAZeroEq] at hLT
  exact hLT

/-- Relación de cancelación para el cuadrado de cualquier cociente:
    p*b=a y p*p=pp, b*b=bb, a*a=aa implican pp*bb=aa. -/
private theorem ratDiv_square_cross
    {a b aa bb p pp : ZFSet.{u}}
    (ha : a ∈ rationalsTA) (hb : b ∈ rationalsTA)
    (h0b : RatLT ratZero b)
    (hd : RatDiv a b p) (hPP : RatMul p p pp)
    (hAA : RatMul a a aa) (hBB : RatMul b b bb) :
    RatMul pp bb aa := by
  have hpMem : p ∈ rationalsTA := ratDiv_value_mem hd
  have hppMem : pp ∈ rationalsTA := ratMul_value_mem hPP
  have hbbMem : bb ∈ rationalsTA := ratMul_value_mem hBB
  have hpB : RatMul p b a := ratDiv_mul_denominator ha hb h0b hd
  rcases ratMul_exists hpMem ha with ⟨pa, hpaMem, hpA⟩
  rcases ratMul_exists hppMem hb with ⟨ppb, _, hppB⟩
  have hEq1 : ppb = pa :=
    ratMul_assoc hpMem hpMem hb hPP hppB hpB hpA
  have hAp : RatMul a p pa := ratMul_comm_rel hpMem ha hpA
  rcases ratMul_exists hpaMem hb with ⟨pab, _, hpaB⟩
  have hEq2 : pab = aa :=
    ratMul_assoc ha hpMem hb hAp hpaB hpB hAA
  have hppBBAA : RatMul ppb b aa := by
    rw [hEq1, ← hEq2]
    exact hpaB
  rcases ratMul_exists hppMem hbbMem with ⟨ppbb, _, hppBB⟩
  have hEq3 : aa = ppbb :=
    ratMul_assoc hppMem hb hb hppB hppBBAA hBB hppBB
  rw [← hEq3] at hppBB
  exact hppBB

/-- El numeral racional 2 coincide con el numeral 2_Q certificado. -/
theorem pell_nat_two_eq_ratTwoTA :
    (natRational (natEncode (2 : Nat) : ZFSet.{u})) = ratTwoTA := by
  rfl

/-- El cuadrado de cualquier cociente de Pell es estrictamente menor que 2. -/
theorem pell_fraction_square_lt_two (n : Nat) {p pp : ZFSet.{u}}
    (hd : RatDiv
      (natRational (natEncode (pellPair n).1))
      (natRational (natEncode (pellPair n).2)) p)
    (hpp : RatMul p p pp) :
    RatLT pp ratTwoTA := by
  let a : ZFSet.{u} := natRational (natEncode (pellPair n).1)
  let b : ZFSet.{u} := natRational (natEncode (pellPair n).2)
  let aa : ZFSet.{u} := natRational (natEncode ((pellPair n).1 * (pellPair n).1))
  let bb : ZFSet.{u} := natRational (natEncode ((pellPair n).2 * (pellPair n).2))
  let c : ZFSet.{u} := natRational (natEncode (2 * ((pellPair n).2 * (pellPair n).2)))
  have ha : a ∈ rationalsTA := pell_numerator_rational_mem n
  have hb : b ∈ rationalsTA := pell_denominator_rational_mem n
  have h0b : RatLT ratZero b := pell_denominator_rational_positive n
  have hbb : RatMul b b bb := pell_rational_denominator_square n
  have haa : RatMul a a aa := pell_rational_numerator_square n
  have hbbMem : bb ∈ rationalsTA := ratMul_value_mem hbb
  have hppMem : pp ∈ rationalsTA := ratMul_value_mem hpp
  have h0bb : RatLT ratZero bb :=
    ratPositive_mul hb hb hbb h0b h0b
  have hscaled : RatMul pp bb aa :=
    ratDiv_square_cross ha hb h0b hd hpp haa hbb
  have h2bb : RatMul ratTwoTA bb c := by
    rw [← pell_nat_two_eq_ratTwoTA]
    exact pell_rational_two_denominator_square n
  have hcLt : RatLT aa c := pell_rational_square_gap n
  exact (TA_LEM_00020_clause9_scale_iff
    hppMem ratTwoTA_mem_rationalsTA hbbMem h0bb hscaled h2bb).mpr hcLt

/-- Los cocientes de Pell tienen los requisitos de S_2. -/
theorem pell_fraction_in_sqrtTwoSet (n : Nat) {p : ZFSet.{u}}
    (hd : RatDiv
      (natRational (natEncode (pellPair n).1))
      (natRational (natEncode (pellPair n).2)) p) :
    p ∈ sqrtTwoSet := by
  have hpQ : p ∈ rationalsTA := ratDiv_value_mem hd
  have hpPos : RatLT ratZero p := pell_fraction_positive n hd
  rcases ratMul_exists hpQ hpQ with ⟨pp, _, hpp⟩
  exact TA_DEF_00066_mem_sqrtTwoSet_iff.mpr
    ⟨hpQ, hpPos.1, pp, hpp, pell_fraction_square_lt_two n hd hpp⟩

#check pell_nat_rational_positive
#check pell_numerator_rational_positive
#check pell_denominator_rational_positive
#check pell_fraction_positive
#check pell_rational_square_gap
#check pell_nat_two_eq_ratTwoTA
#check pell_fraction_square_lt_two
#check pell_fraction_in_sqrtTwoSet
#print axioms pell_nat_rational_positive
#print axioms pell_numerator_rational_positive
#print axioms pell_denominator_rational_positive
#print axioms pell_fraction_positive
#print axioms pell_rational_square_gap
#print axioms pell_nat_two_eq_ratTwoTA
#print axioms pell_fraction_square_lt_two
#print axioms pell_fraction_in_sqrtTwoSet

end TratadoAnalisis.Chapter7_0010.N05A2P03


/-!
TA-LEAN-0010 / N05-A3-P01: cofinalidad racional de los cuadrados de Pell.
El prefijo N05-A2-P03-P01-R1 se conserva integro.
Primero se expone la consecuencia de un auxiliar ya probado en ese prefijo;
despues se combinan la propiedad arquimediana y el balance de Pell.
Esta sonda no integra resultados en Audit.lean.
-/

namespace TratadoAnalisis.Chapter7_0010.N05A2P03

universe u
set_option autoImplicit false

open TratadoAnalisis.Naturals.Foundational
open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Naturals.ArithmeticBridge
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.NatEmbedding
open TratadoAnalisis.Rationals.Division
open TratadoAnalisis.Chapter7_0010.N05A1
open TratadoAnalisis.Chapter7_0010.N05A2
open TratadoAnalisis.Chapter7_0010.N05A2P02

/-- Consecuencia publica del auxiliar de P03, en el mismo archivo:
    p=a_n/b_n y pp=p*p implican pp*nu(b_n*b_n)=nu(a_n*a_n). -/
theorem pell_fraction_square_cross (n : Nat) {p pp : ZFSet.{u}}
    (hd : RatDiv
      (natRational (natEncode (pellPair n).1))
      (natRational (natEncode (pellPair n).2)) p)
    (hpp : RatMul p p pp) :
    RatMul pp
      (natRational (natEncode ((pellPair n).2 * (pellPair n).2)))
      (natRational (natEncode ((pellPair n).1 * (pellPair n).1))) := by
  exact ratDiv_square_cross
    (pell_numerator_rational_mem n)
    (pell_denominator_rational_mem n)
    (pell_denominator_rational_positive n)
    hd hpp
    (pell_rational_numerator_square n)
    (pell_rational_denominator_square n)

#check pell_fraction_square_cross
#print axioms pell_fraction_square_cross

end TratadoAnalisis.Chapter7_0010.N05A2P03

namespace TratadoAnalisis.Chapter7_0010.N05A3

universe u
set_option autoImplicit false

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
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.Field
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.OrderedFieldCompatibility
open TratadoAnalisis.Rationals.StrictOrder
open TratadoAnalisis.Rationals.NatEmbedding
open TratadoAnalisis.Rationals.Archimedean
open TratadoAnalisis.Rationals.IrrationalitySqrtTwo
open TratadoAnalisis.Rationals.SqrtTwoSet
open TratadoAnalisis.Rationals.NoSupremumSqrtTwo
open TratadoAnalisis.Rationals.Signs
open TratadoAnalisis.Rationals.Division
open TratadoAnalisis.Rationals.PositiveProducts
open TratadoAnalisis.Chapter7_0010.N05A1
open TratadoAnalisis.Chapter7_0010.N05A2
open TratadoAnalisis.Chapter7_0010.N05A2P02
open TratadoAnalisis.Chapter7_0010.N05A2P03

/-- La cota arquimediana conjuntista admite un codigo natural local. -/
theorem rational_lt_nat_code_exists
    {q : ZFSet.{u}} (hq : q ∈ rationalsTA) :
    ∃ N : Nat, RatLT q (natRational (natEncode N : ZFSet.{u})) := by
  rcases TratadoAnalisis.Rationals.Archimedean.TA_THM_00031_rational_archimedean hq
    with ⟨m, hm, hqm⟩
  rcases exists_natEncode_eq_of_mem hm with ⟨N, rfl⟩
  exact ⟨N, hqm⟩

/-- Transporte estricto entre dos codigos naturales, por los grafos propios. -/
theorem nat_rational_lt_of_nat_lt
    (M N : Nat) (hMN : M < N) :
    RatLT (natRational (natEncode M : ZFSet.{u}))
      (natRational (natEncode N)) := by
  have hi :=
    TratadoAnalisis.Rationals.Archimedean.positive_form_lt_of_nat_lt.{u} hMN
  have hM : (intPositiveForm M : ZFSet.{u}) ∈ integersTA :=
    intPositiveForm_mem_integersTA M
  have hN : (intPositiveForm N : ZFSet.{u}) ∈ integersTA :=
    intPositiveForm_mem_integersTA N
  have hGM :
      ZFSet.pair (intPositiveForm M : ZFSet.{u})
        (natRational (natEncode M)) ∈ ratEmbedGraph :=
    ratEmbedGraph_value hM
  have hGN :
      ZFSet.pair (intPositiveForm N : ZFSet.{u})
        (natRational (natEncode N)) ∈ ratEmbedGraph :=
    ratEmbedGraph_value hN
  have hle :
      RatLE (natRational (natEncode M : ZFSet.{u}))
        (natRational (natEncode N)) :=
    (TA_PRO_00066_ratEmbed_order_iff hM hN hGM hGN).mp hi.1
  refine ⟨hle, ?_⟩
  intro heq
  have hGNM :
      ZFSet.pair (intPositiveForm N : ZFSet.{u})
        (natRational (natEncode M)) ∈ ratEmbedGraph := by
    rw [heq]
    exact hGN
  exact hi.2 (ratEmbedGraph_injective hGM hGNM)

/-- Los cuadrados racionales de los denominadores superan cualquier racional. -/
theorem pell_denominator_square_unbounded
    {q : ZFSet.{u}} (hq : q ∈ rationalsTA) :
    ∃ n : Nat,
      RatLT q
        (natRational
          (natEncode ((pellPair n).2 * (pellPair n).2) : ZFSet.{u})) := by
  rcases rational_lt_nat_code_exists hq with ⟨N, hqN⟩
  have hbLower := pell_denominator_lower N
  have h1b : 1 ≤ (pellPair N).2 := by
    omega
  have hbSquare :
      (pellPair N).2 ≤ (pellPair N).2 * (pellPair N).2 := by
    simpa only [Nat.mul_one] using
      Nat.mul_le_mul_left (pellPair N).2 h1b
  have hNSquare :
      N < (pellPair N).2 * (pellPair N).2 := by
    omega
  have hNbb := nat_rational_lt_of_nat_lt.{u}
    N ((pellPair N).2 * (pellPair N).2) hNSquare
  refine ⟨N, ?_⟩
  exact ratLT_of_lt_of_le_local
    hq
    (natRational_mem (natEncode_mem_omegaTA N))
    (natRational_mem
      (natEncode_mem_omegaTA ((pellPair N).2 * (pellPair N).2)))
    hqN hNbb.1

/-- Para todo q<2 hay un cociente de Pell positivo cuyo cuadrado supera q.
    Todos los testigos se eliminan y producen dentro de Prop. -/
theorem pell_fraction_square_cofinal
    {q : ZFSet.{u}} (hq : q ∈ rationalsTA)
    (hqTwo : RatLT q (ratTwoTA : ZFSet.{u})) :
    ∃ n : Nat, ∃ p pp : ZFSet.{u},
      RatDiv
        (natRational (natEncode (pellPair n).1))
        (natRational (natEncode (pellPair n).2)) p ∧
      p ∈ sqrtTwoSet ∧ RatLT ratZero p ∧ RatMul p p pp ∧
      RatLT q pp ∧ RatLT pp ratTwoTA := by
  -- delta=2-q es positivo; su inverso proporciona la cota arquimediana.
  rcases ratNeg_exists hq with ⟨nq, hnqMem, hnq⟩
  rcases ratAdd_exists
      (ratTwoTA_mem_rationalsTA : (ratTwoTA : ZFSet.{u}) ∈ rationalsTA)
      hnqMem with ⟨delta, hdeltaMem, hdelta⟩
  have h0delta : RatLT (ratZero : ZFSet.{u}) delta :=
    ratSub_positive_local ratTwoTA_mem_rationalsTA hq hqTwo hnq hdelta
  have hDeltaQ : RatAdd delta q (ratTwoTA : ZFSet.{u}) :=
    ratSub_add_cancel_local ratTwoTA_mem_rationalsTA hq hnq hdelta
  have hdeltaNZ : delta ∈ ratNonzeroTA :=
    mem_ratNonzeroTA_iff.mpr
      ⟨hdeltaMem, fun h => h0delta.2 h.symm⟩
  rcases exists_inverse_of_mem_ratNonzeroTA hdeltaNZ with
    ⟨invDelta, hinvNZ, _, hDeltaInv, _⟩
  have hinvMem : invDelta ∈ rationalsTA :=
    (mem_ratNonzeroTA_iff.mp hinvNZ).1
  rcases pell_denominator_square_unbounded hinvMem with ⟨n, hinvLTbb⟩

  -- a, b, aa, bb y c son las imagenes racionales de a_n, b_n, a_n^2,
  -- b_n^2 y 2*b_n^2. Se conserva el producto relacional del tratado.
  let a : ZFSet.{u} := natRational (natEncode (pellPair n).1)
  let b : ZFSet.{u} := natRational (natEncode (pellPair n).2)
  let aa : ZFSet.{u} := natRational (natEncode ((pellPair n).1 * (pellPair n).1))
  let bb : ZFSet.{u} := natRational (natEncode ((pellPair n).2 * (pellPair n).2))
  let c : ZFSet.{u} := natRational (natEncode (2 * ((pellPair n).2 * (pellPair n).2)))
  have hb : b ∈ rationalsTA := pell_denominator_rational_mem n
  have hAA : RatMul a a aa := pell_rational_numerator_square n
  have hBB : RatMul b b bb := pell_rational_denominator_square n
  have haaMem : aa ∈ rationalsTA := ratMul_value_mem hAA
  have hbbMem : bb ∈ rationalsTA := ratMul_value_mem hBB
  have h0b : RatLT (ratZero : ZFSet.{u}) b := pell_denominator_rational_positive n
  have h0bb : RatLT (ratZero : ZFSet.{u}) bb :=
    ratPositive_mul hb hb hBB h0b h0b
  have hTwoBB : RatMul (ratTwoTA : ZFSet.{u}) bb c := by
    rw [← pell_nat_two_eq_ratTwoTA]
    exact pell_rational_two_denominator_square n
  have hOne :
      natRational (natEncode (1 : Nat) : ZFSet.{u}) = ratOne := by
    exact TA_COR_00008_natRational_one
  have hBalance : RatAdd aa (ratOne : ZFSet.{u}) c := by
    have h := pell_rational_balance.{u} n
    rw [hOne] at h
    exact h

  -- El cociente y su cuadrado existen por las relaciones ya verificadas.
  rcases pell_fraction_exists.{u} n with ⟨p, hpMem, hd⟩
  rcases ratMul_exists hpMem hpMem with ⟨pp, hppMem, hPP⟩
  have hPPBB : RatMul pp bb aa := pell_fraction_square_cross n hd hPP

  -- invDelta < bb implica 1 < delta*bb.
  rcases ratMul_exists hdeltaMem hbbMem with
    ⟨deltaBB, hdeltaBBMem, hDeltaBB⟩
  have hOneDeltaBB : RatLT (ratOne : ZFSet.{u}) deltaBB :=
    ratLT_mul_positive_left_local hinvMem hbbMem hdeltaMem
      hinvLTbb h0delta hDeltaInv hDeltaBB

  -- Distributividad: delta*bb + q*bb = (delta+q)*bb = 2*bb.
  rcases ratMul_exists hq hbbMem with ⟨qBB, hqBBMem, hQBB⟩
  rcases ratAdd_exists hdeltaBBMem hqBBMem with ⟨sum, _, hSum⟩
  have hDist : c = sum :=
    ratAdd_mul_right hdeltaMem hq hbbMem
      hDeltaQ hTwoBB hDeltaBB hQBB hSum
  have hDeltaBBQBB : RatAdd deltaBB qBB c := by
    rw [hDist]
    exact hSum
  have hQBBDeltaBB : RatAdd qBB deltaBB c :=
    ratAdd_comm_rel hdeltaBBMem hqBBMem hDeltaBBQBB

  -- q*bb+1 < aa+1 permite cancelar 1; bb>0 permite cancelar bb.
  rcases ratAdd_exists hqBBMem ratOne_mem_rationalsTA with
    ⟨qBBOne, _, hQBBOne⟩
  have hSumLT : RatLT qBBOne c :=
    ratLT_add_left_local ratOne_mem_rationalsTA hdeltaBBMem hqBBMem
      hOneDeltaBB hQBBOne hQBBDeltaBB
  have hQBBLTAA : RatLT qBB aa :=
    ratLT_add_cancel_right_local hqBBMem haaMem ratOne_mem_rationalsTA
      hQBBOne hBalance hSumLT
  have hqPP : RatLT q pp :=
    (TA_LEM_00020_clause9_scale_iff
      hq hppMem hbbMem h0bb hQBB hPPBB).mpr hQBBLTAA
  exact ⟨n, p, pp, hd,
    pell_fraction_in_sqrtTwoSet n hd,
    pell_fraction_positive n hd, hPP, hqPP,
    pell_fraction_square_lt_two n hd hPP⟩

/-- Cofinalidad cuadratica con el enunciado racional del puente condicional.
    No se supone una hipotesis de cofinalidad. -/
theorem quadratic_cofinality_0010
    (q : ZFSet.{u}) (hq : q ∈ rationalsTA)
    (hqTwo : RatLT q (ratTwoTA : ZFSet.{u})) :
    ∃ p pp : ZFSet.{u},
      p ∈ sqrtTwoSet ∧ RatLT ratZero p ∧ RatMul p p pp ∧ RatLT q pp := by
  rcases pell_fraction_square_cofinal hq hqTwo with
    ⟨_n, p, pp, _, hpSet, hpPositive, hPP, hqPP, _⟩
  exact ⟨p, pp, hpSet, hpPositive, hPP, hqPP⟩

#check rational_lt_nat_code_exists
#check nat_rational_lt_of_nat_lt
#check pell_denominator_square_unbounded
#check pell_fraction_square_cofinal
#check quadratic_cofinality_0010
#print axioms rational_lt_nat_code_exists
#print axioms nat_rational_lt_of_nat_lt
#print axioms pell_denominator_square_unbounded
#print axioms pell_fraction_square_cofinal
#print axioms quadratic_cofinality_0010

end TratadoAnalisis.Chapter7_0010.N05A3



/-!
TA-LEAN-0010 / N05-P01 — Sonda condicional de la interfaz del producto.
Este archivo NO demuestra la cofinalidad ni afirma el cierre de N05.
Solo verifica que la cofinalidad, UNA VEZ DEMOSTRADA en Lean,
implica 2_D ≤ alphaTwoCut² y, junto con N04, la igualdad.
No contiene axiomas nuevos, sorry, admit ni modificaciones de fuente.
-/
namespace TratadoAnalisis.Chapter7_0010

set_option autoImplicit false

universe u

open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.IrrationalitySqrtTwo
open TratadoAnalisis.Rationals.StrictOrder
open TratadoAnalisis.Rationals.SqrtTwoSet
open TratadoAnalisis.Dedekind.Definition
open TratadoAnalisis.Dedekind.AlphaTwo
open TratadoAnalisis.Dedekind.Positivity
open TratadoAnalisis.Dedekind.RationalSection
open TratadoAnalisis.Dedekind.Multiplication

/-- OBLIGACIÓN ABIERTA N05-A; una definición de Prop, no un axioma.
Para cada q racional menor que 2, hay un p positivo de S₂ con q < p². -/
def QuadraticCofinality0010 : Prop :=
  ∀ q : ZFSet.{u}, q ∈ rationalsTA → RatLT q (TratadoAnalisis.Rationals.IrrationalitySqrtTwo.ratTwoTA : ZFSet.{u}) →
    ∃ p pp : ZFSet.{u},
      p ∈ sqrtTwoSet ∧ RatLT ratZero p ∧
      RatMul p p pp ∧ RatLT q pp

/-- N05-B condicional: se usa el mismo p en los dos factores positivos. -/
theorem section_two_subset_alphaTwo_square_of_cofinal_0010
    (em : ∀ p : Prop, p ∨ ¬p)
    (hcofinal : QuadraticCofinality0010.{u}) :
    rationalSection (TratadoAnalisis.Rationals.IrrationalitySqrtTwo.ratTwoTA : ZFSet.{u}) ⊆
      dedMul alphaTwoCut alphaTwoCut := by
  intro q hq
  obtain ⟨hqQ, hqTwo⟩ := TA_DEF_00081_mem_rationalSection_iff.mp hq
  obtain ⟨p, pp, hpSet, h0p, hpp, hqpp⟩ := hcofinal q hqQ hqTwo
  have hpQ : p ∈ rationalsTA :=
    (TA_DEF_00066_mem_sqrtTwoSet_iff.mp hpSet).1
  have hpAlpha : p ∈ alphaTwoCut :=
    TA_DEF_00082_mem_alphaTwoCut_iff.mpr ⟨hpQ, Or.inr hpSet⟩
  have hprod : q ∈ dedPositiveMul alphaTwoCut alphaTwoCut :=
    mem_positiveMul_of_witness hqQ hpAlpha h0p hpAlpha h0p hpp hqpp
  rw [alphaTwo_square_is_positive_product_0010 em]
  exact hprod

/-- N05-C condicional: la igualdad se obtiene por extensionalidad y N04. -/
theorem alphaTwo_square_eq_section_two_of_cofinal_0010
    (em : ∀ p : Prop, p ∨ ¬p)
    (hcofinal : QuadraticCofinality0010.{u}) :
    dedMul (alphaTwoCut : ZFSet.{u}) alphaTwoCut =
      rationalSection (TratadoAnalisis.Rationals.IrrationalitySqrtTwo.ratTwoTA : ZFSet.{u}) := by
  apply ZFSet.ext
  intro q
  constructor
  · intro hq
    exact (alphaTwo_square_subset_section_two_0010 em) hq
  · intro hq
    exact (section_two_subset_alphaTwo_square_of_cofinal_0010 em hcofinal) hq

#check QuadraticCofinality0010
#check section_two_subset_alphaTwo_square_of_cofinal_0010
#check alphaTwo_square_eq_section_two_of_cofinal_0010
#print axioms section_two_subset_alphaTwo_square_of_cofinal_0010
#print axioms alphaTwo_square_eq_section_two_of_cofinal_0010

end TratadoAnalisis.Chapter7_0010


/-!
TA-LEAN-0010 / N05-A4-P01: aplicacion de la cofinalidad al puente R2.
Las demostraciones de A3 y del puente se conservan literalmente.
La cofinalidad ya no es una hipotesis de la inclusion ni de la igualdad.
El parametro logico em del puente se mantiene explicito.
No se afirma unicidad ni se integran resultados en Audit.lean.
-/

namespace TratadoAnalisis.Chapter7_0010

universe u
set_option autoImplicit false

open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.IrrationalitySqrtTwo
open TratadoAnalisis.Dedekind.Definition
open TratadoAnalisis.Dedekind.AlphaTwo
open TratadoAnalisis.Dedekind.Positivity
open TratadoAnalisis.Dedekind.Multiplication

/-- La obligacion racional del puente dispone ahora de una demostracion. -/
theorem quadratic_cofinality_proved_0010 :
    QuadraticCofinality0010.{u} := by
  intro q hq hqTwo
  exact TratadoAnalisis.Chapter7_0010.N05A3.quadratic_cofinality_0010
    q hq hqTwo

/-- Inclusion inferior del cuadrado, sin hipotesis de cofinalidad. -/
theorem section_two_subset_alphaTwo_square_0010
    (em : ∀ p : Prop, p ∨ ¬p) :
    rationalSection (ratTwoTA : ZFSet.{u}) ⊆
      dedMul (alphaTwoCut : ZFSet.{u}) alphaTwoCut := by
  exact section_two_subset_alphaTwo_square_of_cofinal_0010.{u}
    em quadratic_cofinality_proved_0010

/-- Identidad del cuadrado de la cortadura construida, con em explicito. -/
theorem alphaTwo_square_eq_section_two_0010
    (em : ∀ p : Prop, p ∨ ¬p) :
    dedMul (alphaTwoCut : ZFSet.{u}) alphaTwoCut =
      rationalSection (ratTwoTA : ZFSet.{u}) := by
  exact alphaTwo_square_eq_section_two_of_cofinal_0010.{u}
    em quadratic_cofinality_proved_0010

/-- Testigo concreto: cortadura positiva de cuadrado dos y no racional.
    Este enunciado no incluye una afirmacion de unicidad. -/
theorem alphaTwo_positive_irrational_square_two_0010
    (em : ∀ p : Prop, p ∨ ¬p) :
    (alphaTwoCut : ZFSet.{u}) ∈ dedekindCutsTA ∧
    IsPositiveCut (alphaTwoCut : ZFSet.{u}) ∧
    dedMul (alphaTwoCut : ZFSet.{u}) alphaTwoCut =
      rationalSection (ratTwoTA : ZFSet.{u}) ∧
    (∀ q : ZFSet.{u}, q ∈ rationalsTA →
      (alphaTwoCut : ZFSet.{u}) ≠ rationalSection q) := by
  refine ⟨TA_PRO_00081_alphaTwoCut_mem, ?_,
    alphaTwo_square_eq_section_two_0010 em, ?_⟩
  · exact TratadoAnalisis.Dedekind.Positivity.TA_LEM_00023_zero_mem_implies_positive
      TA_PRO_00081_alphaTwoCut_mem alphaTwoCut_zero_mem
  · intro q hq
    exact TratadoAnalisis.Dedekind.AlphaTwo.TA_PRO_00082_alphaTwoCut_ne_rationalSection hq

#check quadratic_cofinality_proved_0010
#check section_two_subset_alphaTwo_square_0010
#check alphaTwo_square_eq_section_two_0010
#check alphaTwo_positive_irrational_square_two_0010
#print axioms quadratic_cofinality_proved_0010
#print axioms section_two_subset_alphaTwo_square_0010
#print axioms alphaTwo_square_eq_section_two_0010
#print axioms alphaTwo_positive_irrational_square_two_0010

end TratadoAnalisis.Chapter7_0010


/-!
TA-LEAN-0010 / N05-A5-P01: unicidad por pertenencia a cuadrados positivos.
Se trabaja con los productos y las cortaduras conjuntistas del tratado.
La logica em permanece explicita; no se eligen representantes globales.
Esta extension no asigna aun IDs definitivos del manuscrito ni modifica Audit.
-/

namespace TratadoAnalisis.Chapter7_0010

universe u
set_option autoImplicit false

open TratadoAnalisis.Naturals.Recursion
open TratadoAnalisis.Rationals.Construction
open TratadoAnalisis.Rationals.Additive
open TratadoAnalisis.Rationals.Multiplicative
open TratadoAnalisis.Rationals.Algebra
open TratadoAnalisis.Rationals.Field
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.Trichotomy
open TratadoAnalisis.Rationals.OrderedFieldCompatibility
open TratadoAnalisis.Rationals.StrictOrder
open TratadoAnalisis.Rationals.SquareMonotonicity
open TratadoAnalisis.Rationals.NoSupremumSqrtTwo
open TratadoAnalisis.Rationals.Signs
open TratadoAnalisis.Rationals.Division
open TratadoAnalisis.Rationals.PositiveProducts
open TratadoAnalisis.Rationals.IrrationalitySqrtTwo
open TratadoAnalisis.Dedekind.Definition
open TratadoAnalisis.Dedekind.Order
open TratadoAnalisis.Dedekind.RationalSection
open TratadoAnalisis.Dedekind.Addition
open TratadoAnalisis.Dedekind.AlphaTwo
open TratadoAnalisis.Dedekind.Positivity
open TratadoAnalisis.Dedekind.PositiveMultiplication
open TratadoAnalisis.Dedekind.Multiplication
open TratadoAnalisis.Foundations.FunctionTriple

/-- Para q>0, pertenecer a una cortadura positiva equivale a que q*q
    pertenezca a su cuadrado. La vuelta usa em para la pertenencia de q. -/
theorem positive_cut_mem_iff_square_mem_0010
    (em : ∀ p : Prop, p ∨ ¬p)
    {α q qq : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) (hposα : IsPositiveCut α)
    (hqQ : q ∈ rationalsTA) (h0q : RatLT (ratZero : ZFSet.{u}) q)
    (hqq : RatMul q q qq) :
    q ∈ α ↔ qq ∈ dedMul α α := by
  have ca := TA_PRO_00079_mem_dedekindCuts_iff.mp hα
  have hqqQ : qq ∈ rationalsTA := ratMul_value_mem hqq
  have hMul : dedMul α α = dedPositiveMul α α := by
    change dedSignedMul α α = dedPositiveMul α α
    exact TA_DEF_00096_of_pos_pos hposα hposα
  constructor
  · intro hqα
    rcases ca.2.2.2.2 q hqα with ⟨r, hrα, hqr⟩
    have hrQ : r ∈ rationalsTA := ca.1 hrα
    have h0r : RatLT (ratZero : ZFSet.{u}) r :=
      ratLT_of_lt_of_le_local ratZero_mem_rationalsTA hqQ hrQ h0q hqr.1
    rcases ratMul_exists hrQ hrQ with ⟨rr, _, hrr⟩
    have hqqrr : RatLT qq rr :=
      TA_LEM_00018_square_strict_mono_nonnegative hqQ hrQ h0q.1 hqr hqq hrr
    rw [hMul]
    exact mem_positiveMul_of_witness hqqQ hrα h0r hrα h0r hrr hqqrr
  · intro hqqIn
    rcases em (q ∈ α) with hqα | hqOut
    · exact hqα
    · exfalso
      rw [hMul] at hqqIn
      rcases TA_DEF_00093_mem_positiveMul_iff.mp hqqIn with
        ⟨_, a, haPart, b, hbPart, ab, hab, hqqab⟩
      rcases TA_DEF_00092_mem_positivePart_iff.mp haPart with ⟨haα, _⟩
      rcases TA_DEF_00092_mem_positivePart_iff.mp hbPart with ⟨hbα, h0b⟩
      have habqq : RatLT ab qq :=
        positive_product_lt_of_factor_bounds
          (ca.1 haα) (ca.1 hbα) hqQ hqQ h0b h0q
          (cut_member_lt_nonmember ca hqQ hqOut haα)
          (cut_member_lt_nonmember ca hqQ hqOut hbα)
          hab hqq
      exact (ratLT_of_lt_of_le_local hqqQ (ratMul_value_mem hab) hqqQ
        hqqab habqq.1).2 rfl

/-- La igualdad de cuadrados permite trasladar cada miembro de una
    cortadura positiva a la otra. Los casos q≤0 se tratan por separado. -/
private theorem positive_cut_subset_of_square_eq_0010
    (em : ∀ p : Prop, p ∨ ¬p)
    {α β : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) (hβ : β ∈ dedekindCutsTA)
    (hposα : IsPositiveCut α) (hposβ : IsPositiveCut β)
    (hsq : dedMul α α = dedMul β β) :
    α ⊆ β := by
  have ca := TA_PRO_00079_mem_dedekindCuts_iff.mp hα
  have cb := TA_PRO_00079_mem_dedekindCuts_iff.mp hβ
  have h0β : (ratZero : ZFSet.{u}) ∈ β :=
    TA_LEM_00023_positive_implies_zero_mem em hβ hposβ
  intro q hqα
  have hqQ : q ∈ rationalsTA := ca.1 hqα
  rcases TA_PRO_00172_rational_trichotomy hqQ ratZero_mem_rationalsTA with
    hqNeg | hqZero | h0q
  · exact cb.2.2.2.1 ratZero h0β q hqQ hqNeg
  · rw [hqZero]
    exact h0β
  · rcases ratMul_exists hqQ hqQ with ⟨qq, _, hqq⟩
    have hqqα : qq ∈ dedMul α α :=
      (positive_cut_mem_iff_square_mem_0010 em hα hposα hqQ h0q hqq).mp hqα
    have hqqβ : qq ∈ dedMul β β := by
      rw [← hsq]
      exact hqqα
    exact (positive_cut_mem_iff_square_mem_0010 em hβ hposβ hqQ h0q hqq).mpr hqqβ

/-- El cuadrado es inyectivo entre las cortaduras estrictamente positivas. -/
theorem positive_cut_square_injective_0010
    (em : ∀ p : Prop, p ∨ ¬p)
    {α β : ZFSet.{u}}
    (hα : α ∈ dedekindCutsTA) (hβ : β ∈ dedekindCutsTA)
    (hposα : IsPositiveCut α) (hposβ : IsPositiveCut β)
    (hsq : dedMul α α = dedMul β β) :
    α = β := by
  have hAB := positive_cut_subset_of_square_eq_0010 em hα hβ hposα hposβ hsq
  have hBA := positive_cut_subset_of_square_eq_0010 em hβ hα hposβ hposα hsq.symm
  apply ZFSet.ext
  intro q
  exact ⟨fun h => hAB h, fun h => hBA h⟩

/-- Toda cortadura positiva cuyo cuadrado es dos coincide con alphaTwoCut. -/
theorem positive_square_two_eq_alphaTwo_0010
    (em : ∀ p : Prop, p ∨ ¬p)
    {β : ZFSet.{u}}
    (hβ : β ∈ dedekindCutsTA) (hposβ : IsPositiveCut β)
    (hsq : dedMul β β = rationalSection (ratTwoTA : ZFSet.{u})) :
    β = (alphaTwoCut : ZFSet.{u}) := by
  have hAlpha := alphaTwo_positive_irrational_square_two_0010.{u} em
  exact positive_cut_square_injective_0010 em
    hβ hAlpha.1 hposβ hAlpha.2.1
    (hsq.trans hAlpha.2.2.1.symm)

/-- Existe una unica cortadura positiva cuyo cuadrado es la seccion de dos.
    La existencia usa el testigo construido y la unicidad el lema general. -/
theorem positive_square_two_exists_unique_0010
    (em : ∀ p : Prop, p ∨ ¬p) :
    ∃! α : ZFSet.{u},
      α ∈ dedekindCutsTA ∧ IsPositiveCut α ∧
      dedMul α α = rationalSection (ratTwoTA : ZFSet.{u}) := by
  have hAlpha := alphaTwo_positive_irrational_square_two_0010.{u} em
  refine ⟨(alphaTwoCut : ZFSet.{u}), ⟨hAlpha.1, hAlpha.2.1, hAlpha.2.2.1⟩, ?_⟩
  intro β hβ
  exact positive_square_two_eq_alphaTwo_0010 em hβ.1 hβ.2.1 hβ.2.2

#check TratadoAnalisis.Chapter7_0010.positive_cut_mem_iff_square_mem_0010
#check TratadoAnalisis.Chapter7_0010.positive_cut_square_injective_0010
#check TratadoAnalisis.Chapter7_0010.positive_square_two_eq_alphaTwo_0010
#check TratadoAnalisis.Chapter7_0010.positive_square_two_exists_unique_0010
#print axioms TratadoAnalisis.Chapter7_0010.positive_cut_mem_iff_square_mem_0010
#print axioms TratadoAnalisis.Chapter7_0010.positive_cut_square_injective_0010
#print axioms TratadoAnalisis.Chapter7_0010.positive_square_two_eq_alphaTwo_0010
#print axioms TratadoAnalisis.Chapter7_0010.positive_square_two_exists_unique_0010

end TratadoAnalisis.Chapter7_0010
