import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartCore
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitProductSignatureData

/-!
# Transparent product-signature rank tables

These definitions expose the generated representative signatures, their
sorted ranks, and the inverse rank table to bounded kernel replay.
-/

set_option autoImplicit false

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceOrbitProductSignatureTable

open HypercubicDimension16TraceOrbitChartCore
open HypercubicDimension16TraceOrbitProductSignatureData

@[reducible] def expectedProductSignature
    (index : PositiveRepresentativeIndex) : Nat :=
  (representativeCanonicalProductSignatureCode? index.1).getD 0

@[reducible] def productSignatureRank
    (index : PositiveRepresentativeIndex) : PositiveRepresentativeIndex :=
  Fin.ofNat 11654 ((productSignatureRankCode? index.1).getD 0)

@[reducible] def representativeAtProductSignatureRank
    (rank : PositiveRepresentativeIndex) : PositiveRepresentativeIndex :=
  Fin.ofNat 11654
    ((representativeAtProductSignatureRankCode? rank.1).getD 0)

@[reducible] def sortedProductSignature
    (rank : PositiveRepresentativeIndex) : Nat :=
  (sortedCanonicalProductSignatureCode? rank.1).getD 0

@[reducible] def sortedProductSignatureAt (index : Nat) : Nat :=
  sortedProductSignature (Fin.ofNat 11654 index)

end HypercubicDimension16TraceOrbitProductSignatureTable
end YangMills
end QuantumTheory
end Mettapedia
