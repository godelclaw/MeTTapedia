import Mathlib.Data.Rat.Defs

/-! Generated sparse data for the exact eight-field trace-rank replay. -/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceRankCertificateData

structure EncodedRelationDescriptor where
  kind : Nat
  carrier : Array Nat
  first : Nat
  second : Nat
  third : Nat
deriving DecidableEq

abbrev IntegerSparseRow := Array (Nat × Int)
abbrev RationalSparseRow := Array (Nat × Int × Nat)

@[reducible] def ambientColumnCount : Nat := 11654
@[reducible] def selectedRowCount : Nat := 11556

end HypercubicDimension16TraceRankCertificateData
end YangMills
end QuantumTheory
end Mettapedia
