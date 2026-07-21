import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractSearchData
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractTraceMapChecks

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwenty

open ClassicalCertificateContractColorSearch
open ClassicalCertificateIndexedTraceMap
open ClassicalCertificateTraceTree

def twentiethCatalogueHasContractTrace (word : List TraceSymbol) : Bool :=
  (twentiethCatalogueContractTraceMap.lookup word).isSome

def twentiethCatalogueContractSearchFirstBranch
    (color : ClassicalCertificateTraceWitness.FaceColorCode) : SearchTree :=
  twentiethCatalogueContractSearch.tree.child color

def twentiethCatalogueContractSearchBranch
    (first second : ClassicalCertificateTraceWitness.FaceColorCode) :
    SearchTree :=
  (twentiethCatalogueContractSearchFirstBranch first).child second

def twentiethCatalogueContractSearchFirstComponent : Fin 16 := 1

def twentiethCatalogueContractSearchSecondComponent : Fin 16 := 5

def twentiethCatalogueContractSearchRemaining : List (Fin 16) :=
  [5, 8, 14, 11, 13, 7, 10, 12, 15, 2, 3, 6, 9, 0, 4]

def twentiethCatalogueContractSearchTail : List (Fin 16) :=
  [8, 14, 11, 13, 7, 10, 12, 15, 2, 3, 6, 9, 0, 4]

end ClassicalCertificateCatalogueTwenty

end Mettapedia.GraphTheory.FourColor
