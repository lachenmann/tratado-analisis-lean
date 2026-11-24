import TratadoAnalisis.Rationals.OrderedFieldCompatibility

namespace TratadoAnalisis.Rationals.OrderedField

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
open TratadoAnalisis.Rationals.OrderPrep
open TratadoAnalisis.Rationals.PositiveDenominator
open TratadoAnalisis.Rationals.OrderWellDefined
open TratadoAnalisis.Rationals.OrderDefinition
open TratadoAnalisis.Rationals.TotalOrder
open TratadoAnalisis.Rationals.OrderedFieldCompatibility

/-- TA-PRO-00068: certificado conjunto del cuerpo y su orden racional. -/
theorem TA_PRO_00068_ordered_field_package :
    (((∀ {x y z xy lhs yz rhs : ZFSet},
      x ∈ rationalsTA → y ∈ rationalsTA → z ∈ rationalsTA →
      RatAdd x y xy → RatAdd xy z lhs → RatAdd y z yz →
      RatAdd x yz rhs → lhs = rhs) ∧
    (∀ {x y xy yx : ZFSet}, x ∈ rationalsTA → y ∈ rationalsTA →
      RatAdd x y xy → RatAdd y x yx → xy = yx) ∧
    (∀ {x z : ZFSet}, x ∈ rationalsTA → RatAdd ratZero x z → z = x) ∧
    (∀ {x z : ZFSet}, x ∈ rationalsTA → RatAdd x ratZero z → z = x) ∧
    (∀ {x nx z : ZFSet}, x ∈ rationalsTA → RatNeg x nx →
      RatAdd nx x z → z = ratZero) ∧
    (∀ {x nx z : ZFSet}, x ∈ rationalsTA → RatNeg x nx →
      RatAdd x nx z → z = ratZero)) ∧
    ((∀ {x y z xy lhs yz rhs : ZFSet},
      x ∈ rationalsTA → y ∈ rationalsTA → z ∈ rationalsTA →
      RatMul x y xy → RatMul xy z lhs → RatMul y z yz →
      RatMul x yz rhs → lhs = rhs) ∧
    (∀ {x y xy yx : ZFSet}, x ∈ rationalsTA → y ∈ rationalsTA →
      RatMul x y xy → RatMul y x yx → xy = yx) ∧
    (∀ {x z : ZFSet}, x ∈ rationalsTA → RatMul ratOne x z → z = x) ∧
    (∀ {x z : ZFSet}, x ∈ rationalsTA → RatMul x ratOne z → z = x) ∧
    (∀ {x y z yz lhs xy xz rhs : ZFSet},
      x ∈ rationalsTA → y ∈ rationalsTA → z ∈ rationalsTA →
      RatAdd y z yz → RatMul x yz lhs → RatMul x y xy →
      RatMul x z xz → RatAdd xy xz rhs → lhs = rhs) ∧
    (∀ {x y z xy lhs xz yz rhs : ZFSet},
      x ∈ rationalsTA → y ∈ rationalsTA → z ∈ rationalsTA →
      RatAdd x y xy → RatMul xy z lhs → RatMul x z xz →
      RatMul y z yz → RatAdd xz yz rhs → lhs = rhs)) ∧
    ratZero ≠ ratOne ∧
    (∀ q : ZFSet, q ∈ ratNonzeroTA →
      ∃ qi : ZFSet, qi ∈ ratNonzeroTA ∧
        RatMul q qi ratOne ∧ RatMul qi q ratOne)) ∧
    ((∀ q : ZFSet, q ∈ rationalsTA → RatLE q q) ∧
    (∀ q r : ZFSet,
      q ∈ rationalsTA → r ∈ rationalsTA →
      RatLE q r → RatLE r q → q = r) ∧
    (∀ q r s : ZFSet,
      q ∈ rationalsTA → r ∈ rationalsTA → s ∈ rationalsTA →
      RatLE q r → RatLE r s → RatLE q s) ∧
    (∀ q r : ZFSet,
      q ∈ rationalsTA → r ∈ rationalsTA →
      RatLE q r ∨ RatLE r q)) ∧
    ((∀ {x y z xz yz : ZFSet},
      x ∈ rationalsTA → y ∈ rationalsTA → z ∈ rationalsTA →
      RatLE x y →
      RatAdd x z xz → RatAdd y z yz →
      RatLE xz yz) ∧
    (∀ {x y z xz yz : ZFSet},
      x ∈ rationalsTA → y ∈ rationalsTA → z ∈ rationalsTA →
      RatLE x y → RatLE ratZero z →
      RatMul x z xz → RatMul y z yz →
      RatLE xz yz)) := by
  exact ⟨TA_THM_00028_field_package,
    TA_THM_00029_total_order, TA_PRO_00065_order_compatibility⟩

end TratadoAnalisis.Rationals.OrderedField
