import TratadoAnalisis.Dedekind.Distributivity
import TratadoAnalisis.Dedekind.Division

namespace TratadoAnalisis.Dedekind.FieldPredicates
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

/-- Operación relacional total y unívoca sobre el portador; no elige valores. -/
def IsBinaryOperationFoundational (A : ZFSet.{u})
    (op : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop) : Prop :=
  ∀ x : ZFSet.{u}, x ∈ A → ∀ y : ZFSet.{u}, y ∈ A →
    ∃! z : ZFSet.{u}, z ∈ A ∧ op x y z

def RelAssociative (A : ZFSet.{u}) (op : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop) : Prop :=
  ∀ x y z xy lhs yz rhs : ZFSet.{u}, x ∈ A → y ∈ A → z ∈ A →
    op x y xy → op xy z lhs → op y z yz → op x yz rhs → lhs = rhs

def RelCommutative (A : ZFSet.{u}) (op : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop) : Prop :=
  ∀ x y xy yx : ZFSet.{u}, x ∈ A → y ∈ A → op x y xy → op y x yx → xy = yx

def RelUnit (A e : ZFSet.{u}) (op : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop) : Prop :=
  ∀ x : ZFSet.{u}, x ∈ A → op x e x ∧ op e x x

def RelDistributive (A : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop) : Prop :=
  (∀ x y z yz lhs xy xz rhs : ZFSet.{u}, x ∈ A → y ∈ A → z ∈ A →
    add y z yz → mul x yz lhs → mul x y xy → mul x z xz → add xy xz rhs → lhs = rhs) ∧
  (∀ x y z xy lhs xz yz rhs : ZFSet.{u}, x ∈ A → y ∈ A → z ∈ A →
    add x y xy → mul xy z lhs → mul x z xz → mul y z yz → add xz yz rhs → lhs = rhs)

/-- Desarrollo de la convención de grupo abeliano y anillo de TA-CNV-00004. -/
def IsAbelianGroupFoundational (A zero : ZFSet.{u})
    (add : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop) : Prop :=
  IsBinaryOperationFoundational A add ∧ zero ∈ A ∧
    RelAssociative A add ∧ RelCommutative A add ∧ RelUnit A zero add ∧
    ∀ x : ZFSet.{u}, x ∈ A → ∃ nx : ZFSet.{u}, nx ∈ A ∧ add x nx zero ∧ add nx x zero

/-- TA-CNV-00005: anillo conmutativo unitario, 0 ≠ 1 e inversos no nulos. -/
def IsFieldFoundational (A zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop) : Prop :=
  IsAbelianGroupFoundational A zero add ∧ IsBinaryOperationFoundational A mul ∧ one ∈ A ∧
    RelAssociative A mul ∧ RelCommutative A mul ∧ RelUnit A one mul ∧
    RelDistributive A add mul ∧ zero ≠ one ∧
    ∀ x : ZFSet.{u}, x ∈ A → x ≠ zero →
      ∃ ix : ZFSet.{u}, ix ∈ A ∧ mul x ix one ∧ mul ix x one

theorem TA_CNV_00005_isField_iff (A zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop) :
    IsFieldFoundational A zero one add mul ↔
      IsAbelianGroupFoundational A zero add ∧ IsBinaryOperationFoundational A mul ∧ one ∈ A ∧
        RelAssociative A mul ∧ RelCommutative A mul ∧ RelUnit A one mul ∧
        RelDistributive A add mul ∧ zero ≠ one ∧
        ∀ x : ZFSet.{u}, x ∈ A → x ≠ zero →
          ∃ ix : ZFSet.{u}, ix ∈ A ∧ mul x ix one ∧ mul ix x one := Iff.rfl

def IsTotalOrderFoundational (A : ZFSet.{u}) (le : ZFSet.{u} → ZFSet.{u} → Prop) : Prop :=
  (∀ x : ZFSet.{u}, x ∈ A → le x x) ∧
  (∀ x y : ZFSet.{u}, x ∈ A → y ∈ A → le x y → le y x → x = y) ∧
  (∀ x y z : ZFSet.{u}, x ∈ A → y ∈ A → z ∈ A → le x y → le y z → le x z) ∧
  (∀ x y : ZFSet.{u}, x ∈ A → y ∈ A → le x y ∨ le y x)

/-- TA-DEF-00067: cuerpo, orden total y las dos compatibilidades exactas. -/
def IsOrderedFieldFoundational (A zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop) : Prop :=
  IsFieldFoundational A zero one add mul ∧ IsTotalOrderFoundational A le ∧
    (∀ x y z xz yz : ZFSet.{u}, x ∈ A → y ∈ A → z ∈ A →
      le x y → add x z xz → add y z yz → le xz yz) ∧
    (∀ x y xy : ZFSet.{u}, x ∈ A → y ∈ A → le zero x → le zero y → mul x y xy → le zero xy)

theorem TA_DEF_00067_isOrderedField_iff (A zero one : ZFSet.{u})
    (add mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (le : ZFSet.{u} → ZFSet.{u} → Prop) :
    IsOrderedFieldFoundational A zero one add mul le ↔
      IsFieldFoundational A zero one add mul ∧ IsTotalOrderFoundational A le ∧
        (∀ x y z xz yz : ZFSet.{u}, x ∈ A → y ∈ A → z ∈ A →
          le x y → add x z xz → add y z yz → le xz yz) ∧
        (∀ x y xy : ZFSet.{u}, x ∈ A → y ∈ A → le zero x → le zero y → mul x y xy → le zero xy) := Iff.rfl

/-- TA-DEF-00077: función conjuntista e inyectividad, unidades, operaciones y orden. -/
def IsOrderedFieldEmbeddingFoundational
    (F E zeroF oneF zeroE oneE : ZFSet.{u})
    (addF mulF addE mulE : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (leF leE : ZFSet.{u} → ZFSet.{u} → Prop)
    (ι : ZFSet.{u} → ZFSet.{u}) (G f : ZFSet.{u}) : Prop :=
  IsOrderedFieldFoundational F zeroF oneF addF mulF leF ∧
  IsOrderedFieldFoundational E zeroE oneE addE mulE leE ∧
  f = functionTriple F E G ∧ IsFunctionTriple F E f ∧
  (∀ x : ZFSet.{u}, x ∈ F → ZFSet.pair x (ι x) ∈ G) ∧
  (∀ x y : ZFSet.{u}, x ∈ F → y ∈ F → ι x = ι y → x = y) ∧
  ι zeroF = zeroE ∧ ι oneF = oneE ∧
  (∀ x y z : ZFSet.{u}, x ∈ F → y ∈ F → z ∈ F → addF x y z → addE (ι x) (ι y) (ι z)) ∧
  (∀ x y z : ZFSet.{u}, x ∈ F → y ∈ F → z ∈ F → mulF x y z → mulE (ι x) (ι y) (ι z)) ∧
  (∀ x y : ZFSet.{u}, x ∈ F → y ∈ F → (leF x y ↔ leE (ι x) (ι y)))

theorem TA_DEF_00077_isEmbedding_iff
    (F E zeroF oneF zeroE oneE : ZFSet.{u})
    (addF mulF addE mulE : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (leF leE : ZFSet.{u} → ZFSet.{u} → Prop)
    (ι : ZFSet.{u} → ZFSet.{u}) (G f : ZFSet.{u}) :
    IsOrderedFieldEmbeddingFoundational F E zeroF oneF zeroE oneE addF mulF addE mulE leF leE ι G f ↔
    (IsOrderedFieldFoundational F zeroF oneF addF mulF leF ∧
  IsOrderedFieldFoundational E zeroE oneE addE mulE leE ∧
  f = functionTriple F E G ∧ IsFunctionTriple F E f ∧
  (∀ x : ZFSet.{u}, x ∈ F → ZFSet.pair x (ι x) ∈ G) ∧
  (∀ x y : ZFSet.{u}, x ∈ F → y ∈ F → ι x = ι y → x = y) ∧
  ι zeroF = zeroE ∧ ι oneF = oneE ∧
  (∀ x y z : ZFSet.{u}, x ∈ F → y ∈ F → z ∈ F → addF x y z → addE (ι x) (ι y) (ι z)) ∧
  (∀ x y z : ZFSet.{u}, x ∈ F → y ∈ F → z ∈ F → mulF x y z → mulE (ι x) (ι y) (ι z)) ∧
  (∀ x y : ZFSet.{u}, x ∈ F → y ∈ F → (leF x y ↔ leE (ι x) (ι y)))) := Iff.rfl


end TratadoAnalisis.Dedekind.FieldPredicates
