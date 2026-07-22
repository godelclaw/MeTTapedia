import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractTraceMap
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitProofDagContractTraceMap

open ClassicalCertificateCatalogueTwenty
open ClassicalCertificateCatalogueTwentyOrbitProofDagData
open ClassicalCertificateIndexedTraceMap
open ClassicalCertificateOrbitProofDagReduction
open ClassicalCertificateTraceTree

/-- A contract-trace-map leaf is accepted when its boundary word names a
semantically matching color-orbit target in the proof DAG. -/
def twentiethCatalogueOrbitProofDagContractTraceTarget
    (_ : Nat) (word : List TraceSymbol) : Bool :=
  targetBoolean 12 twentiethCatalogueOrbitProofDagCode word

def twentiethCatalogueOrbitProofDagContractTraceMapBranch
    (first second : TraceSymbol) : ClassicalCertificateIndexedTraceMap.Tree :=
  (twentiethCatalogueContractTraceMap.child first).child second

end ClassicalCertificateCatalogueTwentyOrbitProofDagContractTraceMap

end Mettapedia.GraphTheory.FourColor
