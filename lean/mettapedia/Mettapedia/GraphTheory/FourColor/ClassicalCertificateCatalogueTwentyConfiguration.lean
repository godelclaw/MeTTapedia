import Mettapedia.GraphTheory.FourColor.ClassicalCertificateContractColorSearch

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwenty

open ClassicalCertificateColorTrace
open ClassicalCertificateConfiguration
open ClassicalCertificateContractColorSearch
open ClassicalCertificateContractComponents
open ClassicalCertificateFacePartition
open ClassicalCertificateHypermap
open ClassicalCertificateRankedKempe
open ClassicalCertificateTraceTree

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The twentieth entry of the classical reducible-configuration catalogue. -/
def twentiethCatalogueSample : Configuration where
  symmetric := false
  contractReferences := [1, 2, 8, 9]
  program :=
    [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1,
      .yellow, .rotate 8, .hexagon, .rotate 7, .hexagon, .rotate 2, .hexagon, .rotate 9,
      .yellow, .rotate 5, .yellow, .rotate 3, .hexagon, .rotate 7, .hexagon, .rotate 7,
      .yellow, .yellow, .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 2,
      .yellow]

/-- Materialized finite hypermap for catalogue configuration `cf020`. -/
def twentiethCatalogueSampleCode : HypermapCode where
  dartCount := 90
  edge :=
    #[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22,
    25, 24, 27, 26, 29, 28, 31, 30, 33, 32, 35, 34, 37, 36, 39, 38, 41, 40, 43, 42, 45, 44,
    47, 46, 49, 48, 51, 50, 53, 52, 55, 54, 57, 56, 59, 58, 61, 60, 63, 62, 65, 64, 67, 66,
    69, 68, 71, 70, 73, 72, 75, 74, 77, 76, 79, 78, 81, 80, 83, 82, 85, 84, 87, 86, 89, 88]
  node :=
    #[5, 15, 1, 58, 3, 52, 11, 25, 7, 12, 9, 0, 10, 51, 13, 2, 21, 68, 17, 22, 19, 6, 20,
    48, 23, 8, 31, 43, 27, 72, 29, 16, 37, 57, 33, 44, 35, 38, 26, 47, 39, 83, 41, 28, 36,
    79, 45, 40, 24, 64, 49, 14, 32, 63, 53, 76, 55, 34, 4, 67, 59, 87, 61, 54, 50, 71, 65,
    60, 18, 75, 69, 66, 30, 84, 73, 70, 56, 80, 77, 46, 78, 89, 81, 42, 74, 88, 85, 62, 86,
    82]
  face :=
    #[2, 11, 4, 15, 0, 58, 8, 21, 10, 25, 6, 12, 14, 9, 1, 51, 18, 31, 20, 68, 16, 22, 24,
    19, 7, 48, 28, 38, 30, 43, 26, 72, 34, 52, 36, 57, 32, 44, 40, 37, 42, 47, 27, 83, 46,
    35, 39, 79, 50, 23, 13, 64, 54, 5, 56, 63, 33, 76, 60, 3, 62, 67, 53, 87, 66, 49, 59,
    71, 70, 17, 65, 75, 74, 29, 69, 84, 78, 55, 45, 80, 82, 77, 41, 89, 86, 73, 61, 88, 81,
    85]

theorem twentiethCatalogueSampleCode_checker :
    twentiethCatalogueSampleCode.checker = true := by
  decide

private def twentiethCatalogueDart : Fin 90 →
    Fin twentiethCatalogueSampleCode.dartCount :=
  Fin.cast (by rfl)

/-- The twelve outer-ring darts of `cf020`, in boundary-trace order. -/
def twentiethCatalogueRing :
    List (Fin twentiethCatalogueSampleCode.dartCount) :=
  [twentiethCatalogueDart 52, twentiethCatalogueDart 32, twentiethCatalogueDart 37, twentiethCatalogueDart 38, twentiethCatalogueDart 26, twentiethCatalogueDart 31, twentiethCatalogueDart 16, twentiethCatalogueDart 21, twentiethCatalogueDart 6, twentiethCatalogueDart 11, twentiethCatalogueDart 0, twentiethCatalogueDart 5]

/-- Face-orbit quotient of `cf020` into twenty face variables. -/
def twentiethCatalogueFacePartition : ClassicalCertificateFacePartition.Code where
  faceCount := 20
  classOf :=
    #[0, 1, 0, 2, 0, 3, 4, 5, 4, 6, 4, 1, 1, 6, 1, 2, 7, 8, 7, 9, 7, 5, 5, 9, 5, 6, 10, 11,
    10, 12, 10, 8, 13, 14, 13, 15, 13, 16, 11, 16, 11, 17, 11, 12, 16, 15, 16, 17, 6, 9, 6,
    2, 14, 3, 14, 18, 14, 15, 3, 2, 3, 19, 3, 18, 2, 9, 2, 19, 9, 8, 9, 19, 8, 12, 8, 19,
    15, 18, 15, 17, 17, 18, 17, 12, 19, 12, 19, 18, 18, 12]
  representative :=
    #[0, 1, 3, 5, 6, 7, 9, 16, 17, 19, 26, 27, 29, 32, 33, 35, 37, 41, 55, 61]
  distance :=
    #[0, 0, 2, 0, 1, 0, 0, 0, 2, 0, 1, 3, 2, 1, 1, 5, 0, 0, 2, 0, 1, 3, 2, 1, 1, 4, 0, 0, 2,
    0, 1, 4, 0, 0, 2, 0, 1, 0, 3, 1, 2, 0, 1, 5, 3, 1, 2, 4, 3, 2, 2, 4, 3, 1, 2, 0, 1, 4,
    4, 1, 3, 0, 2, 5, 3, 3, 2, 5, 5, 1, 4, 4, 3, 1, 2, 3, 3, 1, 2, 3, 2, 2, 1, 4, 2, 2, 1,
    4, 3, 3]

theorem twentiethCatalogueFacePartition_checker :
    ClassicalCertificateFacePartition.checker twentiethCatalogueSampleCode
      twentiethCatalogueFacePartition = true := by
  decide

def twentiethCataloguePartitionValid :
    ClassicalCertificateFacePartition.Valid twentiethCatalogueSampleCode
      twentiethCatalogueFacePartition :=
  ClassicalCertificateFacePartition.valid_of_checker_true
    twentiethCatalogueSampleCode twentiethCatalogueFacePartition
      twentiethCatalogueFacePartition_checker

/-- The four-edge contraction selected by `cf020`. -/
def twentiethCatalogueContract :
    Finset (Fin twentiethCatalogueSampleCode.dartCount) :=
  {twentiethCatalogueDart 58, twentiethCatalogueDart 15, twentiethCatalogueDart 22, twentiethCatalogueDart 68}

theorem twentiethCatalogueRing_reverseBoundaryCycle :
    RawReverseBoundaryCycle twentiethCatalogueSampleCode
      twentiethCatalogueRing := by
  decide

theorem twentiethCatalogueContract_avoidsBoundary :
    ContractAvoidsBoundary twentiethCatalogueContract
      twentiethCatalogueRing := by
  decide

theorem twentiethCatalogue_contractAssignment_trace_symbols
    (assignment : Fin twentiethCatalogueFacePartition.faceCount → Color)
    (hcontract : IsContractAssignment twentiethCataloguePartitionValid
      twentiethCatalogueContract assignment) :
    ∃! symbols : List TraceSymbol,
      symbols.map TraceSymbol.toColor =
        ringTraceOfAssignment twentiethCataloguePartitionValid
          twentiethCatalogueRing assignment := by
  apply existsUnique_traceSymbolWord
  exact cyclicallyDistinct_ringColorWord_of_contract
    twentiethCataloguePartitionValid twentiethCatalogueContract
      twentiethCatalogueRing assignment hcontract
        twentiethCatalogueRing_reverseBoundaryCycle
          twentiethCatalogueContract_avoidsBoundary

/-- Equality components induced by the selected contract edges, with a
contract dart certifying every nontrivial forest link. -/
def twentiethCatalogueComponents :
    ClassicalCertificateContractComponents.Code where
  componentCount := 16
  componentOfFace :=
    #[0, 1, 1, 1, 2, 5, 3, 4, 5, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
  representative :=
    #[0, 1, 4, 6, 7, 5, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]
  parent :=
    #[0, 1, 1, 2, 4, 5, 6, 7, 9, 5, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]
  linkDart :=
    #[0, 0, 14, 58, 0, 0, 0, 0, 68, 22, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  depth :=
    #[0, 0, 1, 2, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem twentiethCatalogueComponents_checker :
    ClassicalCertificateContractComponents.checker
      twentiethCataloguePartitionValid twentiethCatalogueContract
        twentiethCatalogueComponents = true := by
  decide

def twentiethCatalogueComponentsValid :
    ClassicalCertificateContractComponents.Valid
      twentiethCataloguePartitionValid twentiethCatalogueContract
        twentiethCatalogueComponents :=
  ClassicalCertificateContractComponents.valid_of_checker_true
    twentiethCataloguePartitionValid twentiethCatalogueContract
      twentiethCatalogueComponents twentiethCatalogueComponents_checker

end ClassicalCertificateCatalogueTwenty

end Mettapedia.GraphTheory.FourColor
