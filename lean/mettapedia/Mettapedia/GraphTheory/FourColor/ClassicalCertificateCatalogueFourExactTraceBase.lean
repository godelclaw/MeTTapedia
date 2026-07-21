import Mettapedia.GraphTheory.FourColor.ClassicalCertificateExactTraceEnumeration
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueFourLayered

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueFourExactTrace

open ClassicalCertificateCatalogueFour
open ClassicalCertificateExactTraceEnumeration
open ClassicalCertificateContractColorSearch
open ClassicalCertificateTraceTree
open ClassicalCertificateTraceWitness

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

private def fourthCatalogueComponent : Fin 8 →
    Fin fourthCatalogueComponents.componentCount :=
  Fin.cast (by rfl)

def fourthCatalogueExactTraceFirst :
    Fin fourthCatalogueComponents.componentCount :=
  fourthCatalogueComponent 1

def fourthCatalogueExactTraceRemaining :
    List (Fin fourthCatalogueComponents.componentCount) :=
  [fourthCatalogueComponent 4, fourthCatalogueComponent 2,
    fourthCatalogueComponent 3, fourthCatalogueComponent 5,
    fourthCatalogueComponent 6, fourthCatalogueComponent 0,
    fourthCatalogueComponent 7]

def fourthCatalogueExactTraceAssigned (code : FaceColorCode) :
    List (AssignedColor fourthCatalogueComponents.componentCount) :=
  [(fourthCatalogueExactTraceFirst, code)]

theorem fourthCatalogueExactTraceAllCovered (code : FaceColorCode) :
    @ClassicalCertificateContractColorSearch.AllCovered
      fourthCatalogueComponents.componentCount
        (fourthCatalogueExactTraceAssigned code)
          fourthCatalogueExactTraceRemaining := by
  intro component
  fin_cases component <;>
    simp [fourthCatalogueExactTraceAssigned,
      fourthCatalogueExactTraceFirst,
      fourthCatalogueExactTraceRemaining, fourthCatalogueComponent,
      Fin.ext_iff]

/-- Exact contracted traces after fixing the first component color. -/
def fourthCatalogueExactTraceBranch (code : FaceColorCode) : TraceTree :=
  enumerateAux fourthCatalogueComponentsValid fourthCatalogueRing
    (fourthCatalogueExactTraceAssigned code)
      fourthCatalogueExactTraceRemaining

theorem fourthCatalogueExactTraceBranch_uniform (code : FaceColorCode) :
    ClassicalCertificateExactTraceEnumeration.TraceTree.Uniform 8
      (fourthCatalogueExactTraceBranch code) := by
  simpa [fourthCatalogueExactTraceBranch, fourthCatalogueRing] using
    enumerateAux_uniform fourthCatalogueComponentsValid fourthCatalogueRing
      (fourthCatalogueExactTraceAssigned code)
        fourthCatalogueExactTraceRemaining

def fourthCatalogueExactTraceBranchChecker (code : FaceColorCode) : Bool :=
  ClassicalCertificateExactTraceEnumeration.TraceTree.subset
    (fourthCatalogueExactTraceBranch code) fourthCoveredTraceTree

theorem fourthCatalogueExactTraceBranch_subset
    (code : FaceColorCode)
    (hchecker : fourthCatalogueExactTraceBranchChecker code = true)
    (word : List TraceSymbol)
    (haccepts : (fourthCatalogueExactTraceBranch code).accepts word = true) :
    fourthCoveredTraceTree.accepts word = true :=
  ClassicalCertificateExactTraceEnumeration.TraceTree.accepts_of_subset
    (fourthCatalogueExactTraceBranch code) fourthCoveredTraceTree hchecker
      word haccepts

end ClassicalCertificateCatalogueFourExactTrace

end Mettapedia.GraphTheory.FourColor
