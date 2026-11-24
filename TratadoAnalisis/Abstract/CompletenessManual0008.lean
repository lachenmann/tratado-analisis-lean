import TratadoAnalisis.Dedekind.FieldPredicates

/-!
TA-LEAN-0008 — ESPECIFICACIÓN PRELIMINAR para el capítulo 4.
Estado: DEFINICIONES NO COMPILADAS. No demuestra TA-PRO-00076.

Ubicación sugerida:
  TratadoAnalisis/Abstract/CompletenessManual0008.lean

La capa es RELACIONAL y fundada en ZFSet. No usa Field, ℝ, ℚ
como sustitutos de las construcciones propias del tratado.
-/


namespace TratadoAnalisis.AbstractCompleteness.Manual0008

universe u

open TratadoAnalisis.Dedekind.FieldPredicates

/-- Un b del portador es cota superior de los elementos de A. -/
def IsUpperBound (F A : ZFSet.{u})
    (le : ZFSet.{u} → ZFSet.{u} → Prop) (b : ZFSet.{u}) : Prop :=
  b ∈ F ∧ ∀ a : ZFSet.{u}, a ∈ A → le a b

/-- Un b del portador es cota inferior de los elementos de A. -/
def IsLowerBound (F A : ZFSet.{u})
    (le : ZFSet.{u} → ZFSet.{u} → Prop) (b : ZFSet.{u}) : Prop :=
  b ∈ F ∧ ∀ a : ZFSet.{u}, a ∈ A → le b a

/-- s es supremo: es cota superior y la menor de todas. -/
def IsSupremum (F A : ZFSet.{u})
    (le : ZFSet.{u} → ZFSet.{u} → Prop) (s : ZFSet.{u}) : Prop :=
  IsUpperBound F A le s ∧
    ∀ b : ZFSet.{u}, IsUpperBound F A le b → le s b

/-- i es ínfimo: es cota inferior y la mayor de todas. -/
def IsInfimum (F A : ZFSet.{u})
    (le : ZFSet.{u} → ZFSet.{u} → Prop) (i : ZFSet.{u}) : Prop :=
  IsLowerBound F A le i ∧
    ∀ b : ZFSet.{u}, IsLowerBound F A le b → le b i

/-- TA-DEF-00074: propiedad del supremo sobre subconjuntos conjuntistas.
    La no vaciedad de A se deja NEGATIVA, como en el manuscrito. -/
def HasSupremumProperty (F : ZFSet.{u})
    (le : ZFSet.{u} → ZFSet.{u} → Prop) : Prop :=
  ∀ A : ZFSet.{u}, A ⊆ F → A ≠ ∅ →
    (∃ b : ZFSet.{u}, IsUpperBound F A le b) →
    ∃ s : ZFSet.{u}, IsSupremum F A le s

/-- Cuerpo ordenado completo: estructura ya transcrita en el proyecto
    más propiedad del supremo, todavía SIN DEMOSTRACIÓN abstracta. -/
def IsCompleteOrderedFieldFoundational
    (F zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop) : Prop :=
  IsOrderedFieldFoundational F zero one add mul le ∧
    HasSupremumProperty F le

/-- Un opuesto es un RELACIÓN, no una elección global de función. -/
def IsAdditiveOpposite (F zero : ZFSet.{u})
    (add : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (x nx : ZFSet.{u}) : Prop :=
  x ∈ F ∧ nx ∈ F ∧ add x nx zero ∧ add nx x zero

/-- Conjunto de opuestos obtenido por Separación en F, sin elegir
    un representante/opuesto para cada x. -/
def NegativeImage (F zero A : ZFSet.{u})
    (add : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop) : ZFSet.{u} :=
  ZFSet.sep (fun y =>
    ∃ x : ZFSet.{u}, x ∈ A ∧ IsAdditiveOpposite F zero add x y) F

/-- Lema de infraestructura inmediato de Separación. -/
theorem mem_negativeImage_iff
    (F zero A : ZFSet.{u})
    (add : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (y : ZFSet.{u}) :
    y ∈ NegativeImage F zero A add ↔
      y ∈ F ∧ ∃ x : ZFSet.{u}, x ∈ A ∧
        IsAdditiveOpposite F zero add x y := by
  exact ZFSet.mem_sep

#check IsCompleteOrderedFieldFoundational
#check NegativeImage
#print axioms mem_negativeImage_iff

end TratadoAnalisis.AbstractCompleteness.Manual0008
