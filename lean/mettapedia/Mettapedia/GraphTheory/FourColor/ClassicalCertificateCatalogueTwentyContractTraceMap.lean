import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractTraceMapData
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyLayers

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwenty

open ClassicalCertificateCatalogueTwentyLayers
open ClassicalCertificateIndexedLayeredKempe
open ClassicalCertificateIndexedTraceMap
open ClassicalCertificateTraceDag
open ClassicalCertificateTraceTree

/-- The checked relation carried by each contract-trace-map leaf. -/
def twentiethCatalogueContractTraceTarget
    (layer : Nat) (word : List TraceSymbol) : Bool :=
  decide
      (layer < twentiethCatalogueIndexedKempeCertificate.deltaRoots.length) &&
    ClassicalCertificateTraceDag.accepts 12
      twentiethCatalogueIndexedKempeCertificate.traceCode
        (twentiethCatalogueIndexedKempeCertificate.rootAt layer) word

/-- A two-symbol branch of the contract trace map. -/
def twentiethCatalogueContractTraceMapBranch
    (first second : TraceSymbol) : ClassicalCertificateIndexedTraceMap.Tree :=
  (twentiethCatalogueContractTraceMap.child first).child second

end ClassicalCertificateCatalogueTwenty

end Mettapedia.GraphTheory.FourColor
