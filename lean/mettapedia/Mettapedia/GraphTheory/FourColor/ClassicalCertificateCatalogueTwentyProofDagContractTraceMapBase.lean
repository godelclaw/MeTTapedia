import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractTraceMap
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagContractTraceMap

open ClassicalCertificateCatalogueTwenty
open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateIndexedTraceMap
open ClassicalCertificateProofDagReduction
open ClassicalCertificateTraceTree

/-- A contract-trace-map leaf is accepted exactly when its boundary word
names a semantically matching target in the proof DAG. -/
def twentiethCatalogueProofDagContractTraceTarget
    (_ : Nat) (word : List TraceSymbol) : Bool :=
  TargetTreeCode.targetBoolean 12 twentiethCatalogueProofDagCode word

def twentiethCatalogueProofDagContractTraceMapBranch
    (first second : TraceSymbol) : ClassicalCertificateIndexedTraceMap.Tree :=
  (twentiethCatalogueContractTraceMap.child first).child second

end ClassicalCertificateCatalogueTwentyProofDagContractTraceMap

end Mettapedia.GraphTheory.FourColor
