import Mettapedia.GraphTheory.FourColor.ClassicalCertificateContractColorSearch
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateEvenTraceKempe

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueFour

open ClassicalCertificateColorTrace
open ClassicalCertificateConfiguration
open ClassicalCertificateContractColorSearch
open ClassicalCertificateContractComponents
open ClassicalCertificateEvenTraceKempe
open ClassicalCertificateFacePartition
open ClassicalCertificateHypermap
open ClassicalCertificateHypermapColoring
open ClassicalCertificateKempeClosure
open ClassicalCertificateRankedKempe
open ClassicalCertificateTraceTree
open ClassicalCertificateTraceWitness
open ClassicalCertificateTreeRankedKempe

/-- The fourth entry of the classical reducible-configuration catalogue. -/
def fourthCatalogueSample : Configuration where
  symmetric := true
  contractReferences := [1, 2, 12, 13]
  program :=
    [.hexagon, .rotate 2, .hexagon, .rotate 7, .yellow, .rotate 5, .hexagon, .rotate 1,
      .yellow, .rotate 4, .hexagon, .rotate 1, .yellow, .rotate 4, .yellow, .rotate 2,
      .yellow, .rotate 2, .yellow]

/-- Materialized finite hypermap for catalogue configuration `cf004`. -/
def fourthCatalogueSampleCode : HypermapCode where
  dartCount := 50
  edge :=
    #[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22,
    25, 24, 27, 26, 29, 28, 31, 30, 33, 32, 35, 34, 37, 36, 39, 38, 41, 40, 43, 42, 45, 44,
    47, 46, 49, 48]
  node :=
    #[5, 25, 1, 12, 3, 6, 11, 15, 7, 36, 9, 26, 4, 44, 13, 8, 21, 35, 17, 22, 19, 0, 20, 43,
    23, 2, 31, 39, 27, 32, 29, 16, 30, 40, 33, 18, 10, 47, 37, 28, 34, 49, 41, 24, 14, 48,
    45, 38, 46, 42]
  face :=
    #[2, 21, 4, 25, 0, 12, 8, 5, 10, 15, 6, 36, 14, 3, 7, 44, 18, 31, 20, 35, 16, 22, 24,
    19, 1, 43, 28, 11, 30, 39, 26, 32, 34, 29, 17, 40, 38, 9, 27, 47, 42, 33, 23, 49, 46,
    13, 37, 48, 41, 45]

theorem fourthCatalogueSampleCode_checker :
    fourthCatalogueSampleCode.checker = true := by
  decide

private def fourthCatalogueDart : Fin 50 →
    Fin fourthCatalogueSampleCode.dartCount :=
  Fin.cast (by rfl)

/-- The eight outer-ring darts of `cf004`, in boundary-trace order. -/
def fourthCatalogueRing : List (Fin fourthCatalogueSampleCode.dartCount) :=
  [fourthCatalogueDart 6, fourthCatalogueDart 11, fourthCatalogueDart 26, fourthCatalogueDart 31, fourthCatalogueDart 16, fourthCatalogueDart 21, fourthCatalogueDart 0, fourthCatalogueDart 5]

/-- Face-orbit quotient of `cf004` into twelve face variables. -/
def fourthCatalogueFacePartition : ClassicalCertificateFacePartition.Code where
  faceCount := 12
  classOf :=
    #[0, 1, 0, 2, 0, 3, 4, 3, 4, 5, 4, 6, 3, 2, 3, 5, 7, 8, 7, 9, 7, 1, 1, 9, 1, 2, 10, 6,
    10, 11, 10, 8, 8, 11, 8, 9, 6, 5, 6, 11, 9, 11, 9, 2, 5, 2, 5, 11, 11, 2]
  representative :=
    #[0, 1, 3, 5, 6, 9, 11, 16, 17, 19, 26, 29]
  distance :=
    #[0, 0, 2, 0, 1, 0, 0, 1, 2, 0, 1, 0, 3, 1, 2, 4, 0, 0, 2, 0, 1, 3, 2, 1, 1, 5, 0, 1, 2,
    0, 1, 3, 2, 1, 1, 4, 3, 1, 2, 5, 3, 2, 2, 4, 3, 2, 2, 4, 3, 3]

theorem fourthCatalogueFacePartition_checker :
    ClassicalCertificateFacePartition.checker fourthCatalogueSampleCode
      fourthCatalogueFacePartition = true := by
  decide

def fourthCataloguePartitionValid :
    ClassicalCertificateFacePartition.Valid fourthCatalogueSampleCode
      fourthCatalogueFacePartition :=
  ClassicalCertificateFacePartition.valid_of_checker_true
    fourthCatalogueSampleCode fourthCatalogueFacePartition
      fourthCatalogueFacePartition_checker

/-- The four-edge contraction selected by `cf004`. -/
def fourthCatalogueContract :
    Finset (Fin fourthCatalogueSampleCode.dartCount) :=
  {fourthCatalogueDart 12, fourthCatalogueDart 25, fourthCatalogueDart 32, fourthCatalogueDart 39}

theorem fourthCatalogueRing_reverseBoundaryCycle :
    RawReverseBoundaryCycle fourthCatalogueSampleCode fourthCatalogueRing := by
  decide

theorem fourthCatalogueContract_avoidsBoundary :
    ContractAvoidsBoundary fourthCatalogueContract fourthCatalogueRing := by
  decide

theorem fourthCatalogue_contractAssignment_trace_symbols
    (assignment : Fin fourthCatalogueFacePartition.faceCount → Color)
    (hcontract : IsContractAssignment fourthCataloguePartitionValid
      fourthCatalogueContract assignment) :
    ∃! symbols : List TraceSymbol,
      symbols.map TraceSymbol.toColor =
        ringTraceOfAssignment fourthCataloguePartitionValid
          fourthCatalogueRing assignment := by
  apply existsUnique_traceSymbolWord
  exact cyclicallyDistinct_ringColorWord_of_contract
    fourthCataloguePartitionValid fourthCatalogueContract fourthCatalogueRing
      assignment hcontract fourthCatalogueRing_reverseBoundaryCycle
        fourthCatalogueContract_avoidsBoundary

def fourthCatalogueRingVector :
    List.Vector (Fin fourthCatalogueSampleCode.dartCount) 8 :=
  ⟨fourthCatalogueRing, by decide⟩

/-- Eighty-one ordinary-coloring witnesses, one per global-color orbit of
extendable boundary traces for `cf004`. -/
def fourthCatalogueWitnessCertificate : Certificate 12 8 where
  witnesses :=
    [
      { colors := ⟨[.zero, .blue, .purple, .red, .purple, .zero, .blue, .purple, .blue, .zero, .purple, .red], rfl⟩,
        word := ⟨[.red, .red, .red, .red, .red, .blue, .red, .blue], rfl⟩ },
      { colors := ⟨[.zero, .blue, .purple, .blue, .purple, .zero, .blue, .purple, .blue, .zero, .purple, .red], rfl⟩,
        word := ⟨[.red, .red, .red, .red, .red, .blue, .blue, .red], rfl⟩ },
      { colors := ⟨[.zero, .red, .blue, .red, .purple, .zero, .blue, .purple, .blue, .zero, .purple, .red], rfl⟩,
        word := ⟨[.red, .red, .red, .red, .blue, .red, .red, .blue], rfl⟩ },
      { colors := ⟨[.zero, .red, .purple, .blue, .purple, .zero, .blue, .purple, .blue, .zero, .purple, .red], rfl⟩,
        word := ⟨[.red, .red, .red, .red, .blue, .red, .blue, .red], rfl⟩ },
      { colors := ⟨[.zero, .blue, .red, .blue, .zero, .purple, .red, .zero, .red, .purple, .zero, .blue], rfl⟩,
        word := ⟨[.red, .red, .red, .red, .blue, .blue, .blue, .blue], rfl⟩ },
      { colors := ⟨[.zero, .purple, .red, .purple, .red, .blue, .zero, .red, .zero, .blue, .red, .purple], rfl⟩,
        word := ⟨[.red, .red, .red, .red, .blue, .purple, .purple, .blue], rfl⟩ },
      { colors := ⟨[.zero, .red, .blue, .red, .purple, .zero, .blue, .zero, .blue, .purple, .purple, .red], rfl⟩,
        word := ⟨[.red, .red, .red, .blue, .red, .red, .red, .blue], rfl⟩ },
      { colors := ⟨[.zero, .blue, .red, .blue, .zero, .purple, .red, .purple, .red, .zero, .zero, .blue], rfl⟩,
        word := ⟨[.red, .red, .red, .blue, .red, .blue, .blue, .blue], rfl⟩ },
      { colors := ⟨[.zero, .blue, .red, .purple, .zero, .blue, .red, .purple, .red, .zero, .zero, .purple], rfl⟩,
        word := ⟨[.red, .red, .red, .blue, .red, .blue, .purple, .purple], rfl⟩ },
      { colors := ⟨[.zero, .blue, .purple, .blue, .purple, .red, .blue, .zero, .blue, .red, .purple, .zero], rfl⟩,
        word := ⟨[.red, .red, .red, .blue, .blue, .blue, .blue, .red], rfl⟩ },
      { colors := ⟨[.zero, .purple, .blue, .red, .blue, .zero, .purple, .red, .purple, .zero, .blue, .red], rfl⟩,
        word := ⟨[.red, .red, .red, .blue, .blue, .purple, .red, .purple], rfl⟩ },
      { colors := ⟨[.zero, .purple, .blue, .purple, .blue, .zero, .purple, .red, .purple, .zero, .blue, .red], rfl⟩,
        word := ⟨[.red, .red, .red, .blue, .blue, .purple, .purple, .red], rfl⟩ },
      { colors := ⟨[.zero, .blue, .purple, .red, .blue, .zero, .purple, .red, .purple, .zero, .blue, .red], rfl⟩,
        word := ⟨[.red, .red, .red, .blue, .purple, .blue, .red, .purple], rfl⟩ },
      { colors := ⟨[.zero, .red, .purple, .blue, .purple, .red, .blue, .zero, .red, .blue, .purple, .zero], rfl⟩,
        word := ⟨[.red, .red, .blue, .red, .red, .red, .blue, .red], rfl⟩ },
      { colors := ⟨[.zero, .blue, .red, .purple, .zero, .blue, .red, .purple, .blue, .zero, .zero, .purple], rfl⟩,
        word := ⟨[.red, .red, .blue, .red, .red, .blue, .purple, .purple], rfl⟩ },
      { colors := ⟨[.zero, .purple, .red, .blue, .red, .purple, .zero, .blue, .purple, .zero, .red, .blue], rfl⟩,
        word := ⟨[.red, .red, .blue, .red, .red, .purple, .blue, .purple], rfl⟩ },
      { colors := ⟨[.zero, .red, .purple, .blue, .purple, .red, .blue, .purple, .red, .blue, .purple, .zero], rfl⟩,
        word := ⟨[.red, .red, .blue, .blue, .blue, .red, .blue, .red], rfl⟩ },
      { colors := ⟨[.zero, .purple, .red, .blue, .red, .purple, .zero, .red, .purple, .zero, .red, .blue], rfl⟩,
        word := ⟨[.red, .red, .blue, .blue, .blue, .purple, .blue, .purple], rfl⟩ },
      { colors := ⟨[.zero, .red, .blue, .red, .blue, .zero, .purple, .blue, .zero, .purple, .blue, .red], rfl⟩,
        word := ⟨[.red, .red, .blue, .blue, .purple, .red, .red, .purple], rfl⟩ },
      { colors := ⟨[.zero, .red, .blue, .purple, .blue, .zero, .purple, .blue, .zero, .purple, .blue, .red], rfl⟩,
        word := ⟨[.red, .red, .blue, .blue, .purple, .red, .purple, .red], rfl⟩ },
      { colors := ⟨[.zero, .blue, .red, .blue, .red, .purple, .zero, .red, .purple, .zero, .red, .blue], rfl⟩,
        word := ⟨[.red, .red, .blue, .blue, .purple, .blue, .blue, .purple], rfl⟩ },
      { colors := ⟨[.zero, .red, .purple, .red, .blue, .zero, .purple, .purple, .zero, .blue, .blue, .red], rfl⟩,
        word := ⟨[.red, .red, .blue, .purple, .blue, .red, .red, .purple], rfl⟩ },
      { colors := ⟨[.zero, .purple, .red, .purple, .zero, .blue, .red, .red, .blue, .zero, .zero, .purple], rfl⟩,
        word := ⟨[.red, .red, .blue, .purple, .blue, .purple, .purple, .purple], rfl⟩ },
      { colors := ⟨[.zero, .blue, .red, .purple, .zero, .blue, .red, .red, .blue, .zero, .zero, .purple], rfl⟩,
        word := ⟨[.red, .red, .blue, .purple, .purple, .blue, .purple, .purple], rfl⟩ },
      { colors := ⟨[.zero, .blue, .purple, .red, .zero, .blue, .red, .purple, .blue, .red, .purple, .zero], rfl⟩,
        word := ⟨[.red, .blue, .red, .red, .red, .blue, .red, .red], rfl⟩ },
      { colors := ⟨[.zero, .blue, .red, .purple, .blue, .zero, .purple, .red, .zero, .purple, .red, .blue], rfl⟩,
        word := ⟨[.red, .blue, .red, .red, .purple, .blue, .purple, .red], rfl⟩ },
      { colors := ⟨[.zero, .purple, .red, .blue, .purple, .zero, .blue, .zero, .red, .blue, .zero, .purple], rfl⟩,
        word := ⟨[.red, .blue, .red, .red, .purple, .purple, .blue, .red], rfl⟩ },
      { colors := ⟨[.zero, .red, .blue, .red, .zero, .purple, .red, .zero, .blue, .purple, .purple, .zero], rfl⟩,
        word := ⟨[.red, .blue, .red, .blue, .red, .red, .red, .red], rfl⟩ },
      { colors := ⟨[.zero, .blue, .red, .blue, .purple, .zero, .blue, .purple, .red, .zero, .zero, .purple], rfl⟩,
        word := ⟨[.red, .blue, .red, .blue, .red, .blue, .blue, .red], rfl⟩ },
      { colors := ⟨[.zero, .red, .blue, .red, .purple, .zero, .blue, .purple, .red, .zero, .zero, .purple], rfl⟩,
        word := ⟨[.red, .blue, .red, .blue, .blue, .red, .red, .blue], rfl⟩ },
      { colors := ⟨[.zero, .blue, .purple, .red, .zero, .blue, .red, .zero, .blue, .red, .purple, .zero], rfl⟩,
        word := ⟨[.red, .blue, .red, .blue, .blue, .blue, .red, .red], rfl⟩ },
      { colors := ⟨[.zero, .blue, .red, .blue, .zero, .purple, .red, .zero, .blue, .purple, .purple, .zero], rfl⟩,
        word := ⟨[.red, .blue, .red, .blue, .blue, .blue, .blue, .blue], rfl⟩ },
      { colors := ⟨[.zero, .blue, .red, .purple, .zero, .blue, .red, .zero, .blue, .purple, .purple, .zero], rfl⟩,
        word := ⟨[.red, .blue, .red, .blue, .blue, .blue, .purple, .purple], rfl⟩ },
      { colors := ⟨[.zero, .purple, .blue, .red, .zero, .purple, .red, .zero, .blue, .red, .purple, .zero], rfl⟩,
        word := ⟨[.red, .blue, .red, .blue, .purple, .purple, .red, .red], rfl⟩ },
      { colors := ⟨[.zero, .blue, .purple, .red, .blue, .zero, .purple, .purple, .zero, .red, .red, .blue], rfl⟩,
        word := ⟨[.red, .blue, .red, .purple, .red, .blue, .red, .purple], rfl⟩ },
      { colors := ⟨[.zero, .purple, .blue, .red, .purple, .zero, .blue, .blue, .red, .zero, .zero, .purple], rfl⟩,
        word := ⟨[.red, .blue, .red, .purple, .red, .purple, .red, .blue], rfl⟩ },
      { colors := ⟨[.zero, .purple, .red, .blue, .purple, .zero, .blue, .blue, .red, .zero, .zero, .purple], rfl⟩,
        word := ⟨[.red, .blue, .red, .purple, .red, .purple, .blue, .red], rfl⟩ },
      { colors := ⟨[.zero, .red, .blue, .red, .purple, .zero, .blue, .blue, .red, .zero, .zero, .purple], rfl⟩,
        word := ⟨[.red, .blue, .red, .purple, .purple, .red, .red, .blue], rfl⟩ },
      { colors := ⟨[.zero, .blue, .red, .blue, .zero, .purple, .red, .red, .blue, .purple, .purple, .zero], rfl⟩,
        word := ⟨[.red, .blue, .red, .purple, .purple, .blue, .blue, .blue], rfl⟩ },
      { colors := ⟨[.zero, .blue, .red, .purple, .zero, .blue, .red, .red, .blue, .purple, .purple, .zero], rfl⟩,
        word := ⟨[.red, .blue, .red, .purple, .purple, .blue, .purple, .purple], rfl⟩ },
      { colors := ⟨[.zero, .red, .blue, .red, .zero, .purple, .red, .zero, .red, .purple, .purple, .zero], rfl⟩,
        word := ⟨[.red, .blue, .blue, .red, .red, .red, .red, .red], rfl⟩ },
      { colors := ⟨[.zero, .blue, .purple, .red, .purple, .zero, .blue, .purple, .blue, .zero, .zero, .red], rfl⟩,
        word := ⟨[.red, .blue, .blue, .red, .red, .blue, .red, .blue], rfl⟩ },
      { colors := ⟨[.zero, .blue, .red, .blue, .purple, .zero, .blue, .purple, .blue, .zero, .zero, .purple], rfl⟩,
        word := ⟨[.red, .blue, .blue, .red, .red, .blue, .blue, .red], rfl⟩ },
      { colors := ⟨[.zero, .purple, .red, .purple, .blue, .zero, .purple, .blue, .purple, .zero, .red, .blue], rfl⟩,
        word := ⟨[.red, .blue, .blue, .red, .red, .purple, .purple, .red], rfl⟩ },
      { colors := ⟨[.zero, .red, .blue, .red, .purple, .zero, .blue, .purple, .blue, .zero, .zero, .red], rfl⟩,
        word := ⟨[.red, .blue, .blue, .red, .blue, .red, .red, .blue], rfl⟩ },
      { colors := ⟨[.zero, .red, .purple, .blue, .purple, .zero, .blue, .purple, .blue, .zero, .zero, .red], rfl⟩,
        word := ⟨[.red, .blue, .blue, .red, .blue, .red, .blue, .red], rfl⟩ },
      { colors := ⟨[.zero, .blue, .red, .blue, .zero, .purple, .red, .zero, .red, .purple, .purple, .zero], rfl⟩,
        word := ⟨[.red, .blue, .blue, .red, .blue, .blue, .blue, .blue], rfl⟩ },
      { colors := ⟨[.zero, .blue, .red, .purple, .zero, .blue, .red, .zero, .red, .purple, .purple, .zero], rfl⟩,
        word := ⟨[.red, .blue, .blue, .red, .blue, .blue, .purple, .purple], rfl⟩ },
      { colors := ⟨[.zero, .purple, .red, .purple, .red, .blue, .zero, .red, .zero, .blue, .blue, .purple], rfl⟩,
        word := ⟨[.red, .blue, .blue, .red, .blue, .purple, .purple, .blue], rfl⟩ },
      { colors := ⟨[.zero, .red, .purple, .red, .blue, .zero, .purple, .blue, .purple, .zero, .red, .blue], rfl⟩,
        word := ⟨[.red, .blue, .blue, .red, .purple, .red, .red, .purple], rfl⟩ },
      { colors := ⟨[.zero, .purple, .red, .blue, .zero, .purple, .red, .zero, .red, .blue, .purple, .zero], rfl⟩,
        word := ⟨[.red, .blue, .blue, .red, .purple, .purple, .blue, .blue], rfl⟩ },
      { colors := ⟨[.zero, .purple, .red, .purple, .zero, .blue, .red, .zero, .red, .blue, .purple, .zero], rfl⟩,
        word := ⟨[.red, .blue, .blue, .red, .purple, .purple, .purple, .purple], rfl⟩ },
      { colors := ⟨[.zero, .red, .blue, .red, .purple, .zero, .blue, .zero, .blue, .purple, .zero, .red], rfl⟩,
        word := ⟨[.red, .blue, .blue, .blue, .red, .red, .red, .blue], rfl⟩ },
      { colors := ⟨[.zero, .blue, .red, .blue, .zero, .purple, .red, .purple, .red, .zero, .purple, .blue], rfl⟩,
        word := ⟨[.red, .blue, .blue, .blue, .red, .blue, .blue, .blue], rfl⟩ },
      { colors := ⟨[.zero, .red, .purple, .red, .zero, .blue, .red, .purple, .red, .blue, .purple, .zero], rfl⟩,
        word := ⟨[.red, .blue, .blue, .blue, .blue, .red, .red, .red], rfl⟩ },
      { colors := ⟨[.zero, .purple, .red, .purple, .blue, .zero, .purple, .red, .purple, .zero, .red, .blue], rfl⟩,
        word := ⟨[.red, .blue, .blue, .blue, .blue, .purple, .purple, .red], rfl⟩ },
      { colors := ⟨[.zero, .blue, .purple, .red, .blue, .zero, .purple, .red, .purple, .zero, .red, .blue], rfl⟩,
        word := ⟨[.red, .blue, .blue, .blue, .purple, .blue, .red, .purple], rfl⟩ },
      { colors := ⟨[.zero, .blue, .red, .purple, .blue, .zero, .purple, .red, .purple, .zero, .red, .blue], rfl⟩,
        word := ⟨[.red, .blue, .blue, .blue, .purple, .blue, .purple, .red], rfl⟩ },
      { colors := ⟨[.zero, .purple, .blue, .red, .purple, .zero, .blue, .zero, .blue, .red, .zero, .purple], rfl⟩,
        word := ⟨[.red, .blue, .blue, .blue, .purple, .purple, .red, .blue], rfl⟩ },
      { colors := ⟨[.zero, .purple, .red, .blue, .zero, .purple, .red, .blue, .red, .zero, .purple, .blue], rfl⟩,
        word := ⟨[.red, .blue, .blue, .purple, .red, .purple, .blue, .blue], rfl⟩ },
      { colors := ⟨[.zero, .blue, .purple, .red, .blue, .zero, .purple, .zero, .purple, .red, .red, .blue], rfl⟩,
        word := ⟨[.red, .blue, .blue, .purple, .blue, .blue, .red, .purple], rfl⟩ },
      { colors := ⟨[.zero, .purple, .blue, .red, .purple, .zero, .blue, .red, .blue, .zero, .zero, .red], rfl⟩,
        word := ⟨[.red, .blue, .blue, .purple, .blue, .purple, .red, .blue], rfl⟩ },
      { colors := ⟨[.zero, .purple, .red, .blue, .purple, .zero, .blue, .red, .blue, .zero, .zero, .purple], rfl⟩,
        word := ⟨[.red, .blue, .blue, .purple, .blue, .purple, .blue, .red], rfl⟩ },
      { colors := ⟨[.zero, .red, .blue, .red, .zero, .purple, .red, .blue, .red, .purple, .purple, .zero], rfl⟩,
        word := ⟨[.red, .blue, .blue, .purple, .purple, .red, .red, .red], rfl⟩ },
      { colors := ⟨[.zero, .blue, .purple, .red, .purple, .zero, .blue, .red, .blue, .zero, .zero, .red], rfl⟩,
        word := ⟨[.red, .blue, .blue, .purple, .purple, .blue, .red, .blue], rfl⟩ },
      { colors := ⟨[.zero, .blue, .red, .blue, .purple, .zero, .blue, .red, .blue, .zero, .zero, .purple], rfl⟩,
        word := ⟨[.red, .blue, .blue, .purple, .purple, .blue, .blue, .red], rfl⟩ },
      { colors := ⟨[.zero, .purple, .blue, .purple, .blue, .red, .purple, .zero, .purple, .red, .red, .zero], rfl⟩,
        word := ⟨[.red, .blue, .blue, .purple, .purple, .purple, .purple, .red], rfl⟩ },
      { colors := ⟨[.zero, .purple, .blue, .red, .purple, .zero, .blue, .blue, .purple, .zero, .zero, .red], rfl⟩,
        word := ⟨[.red, .blue, .purple, .red, .red, .purple, .red, .blue], rfl⟩ },
      { colors := ⟨[.zero, .red, .blue, .red, .purple, .zero, .blue, .blue, .purple, .zero, .zero, .red], rfl⟩,
        word := ⟨[.red, .blue, .purple, .red, .purple, .red, .red, .blue], rfl⟩ },
      { colors := ⟨[.zero, .red, .purple, .blue, .purple, .zero, .blue, .blue, .purple, .zero, .zero, .red], rfl⟩,
        word := ⟨[.red, .blue, .purple, .red, .purple, .red, .blue, .red], rfl⟩ },
      { colors := ⟨[.zero, .blue, .red, .blue, .zero, .purple, .red, .red, .zero, .purple, .purple, .blue], rfl⟩,
        word := ⟨[.red, .blue, .purple, .red, .purple, .blue, .blue, .blue], rfl⟩ },
      { colors := ⟨[.zero, .purple, .red, .purple, .red, .blue, .zero, .zero, .red, .blue, .blue, .purple], rfl⟩,
        word := ⟨[.red, .blue, .purple, .red, .purple, .purple, .purple, .blue], rfl⟩ },
      { colors := ⟨[.zero, .red, .blue, .purple, .blue, .red, .purple, .zero, .blue, .purple, .red, .zero], rfl⟩,
        word := ⟨[.red, .blue, .purple, .blue, .red, .red, .purple, .red], rfl⟩ },
      { colors := ⟨[.zero, .blue, .red, .purple, .red, .blue, .zero, .purple, .red, .zero, .blue, .purple], rfl⟩,
        word := ⟨[.red, .blue, .purple, .blue, .red, .blue, .purple, .blue], rfl⟩ },
      { colors := ⟨[.zero, .purple, .blue, .red, .purple, .zero, .blue, .red, .purple, .zero, .zero, .red], rfl⟩,
        word := ⟨[.red, .blue, .purple, .blue, .blue, .purple, .red, .blue], rfl⟩ },
      { colors := ⟨[.zero, .blue, .purple, .red, .purple, .zero, .blue, .red, .purple, .zero, .zero, .red], rfl⟩,
        word := ⟨[.red, .blue, .purple, .blue, .purple, .blue, .red, .blue], rfl⟩ },
      { colors := ⟨[.zero, .blue, .purple, .blue, .purple, .zero, .blue, .red, .purple, .zero, .zero, .red], rfl⟩,
        word := ⟨[.red, .blue, .purple, .blue, .purple, .blue, .blue, .red], rfl⟩ },
      { colors := ⟨[.zero, .purple, .blue, .purple, .blue, .red, .purple, .zero, .blue, .red, .red, .zero], rfl⟩,
        word := ⟨[.red, .blue, .purple, .blue, .purple, .purple, .purple, .red], rfl⟩ },
      { colors := ⟨[.zero, .red, .purple, .red, .purple, .zero, .blue, .zero, .purple, .blue, .zero, .red], rfl⟩,
        word := ⟨[.red, .blue, .purple, .purple, .red, .red, .red, .blue], rfl⟩ },
      { colors := ⟨[.zero, .red, .purple, .blue, .purple, .zero, .blue, .zero, .purple, .blue, .zero, .red], rfl⟩,
        word := ⟨[.red, .blue, .purple, .purple, .red, .red, .blue, .red], rfl⟩ },
      { colors := ⟨[.zero, .purple, .red, .purple, .red, .blue, .zero, .blue, .red, .zero, .blue, .purple], rfl⟩,
        word := ⟨[.red, .blue, .purple, .purple, .red, .purple, .purple, .blue], rfl⟩ }
    ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem fourthCatalogueWitnessCertificate_checker :
    fourthCatalogueWitnessCertificate.checker fourthCataloguePartitionValid
      fourthCatalogueRingVector = true := by
  decide

theorem fourthCatalogue_witnessWord_is_ringTrace
    (word : TraceWord 8)
    (hword : word ∈ fourthCatalogueWitnessCertificate.words) :
    ∃ assignment : Fin fourthCatalogueFacePartition.faceCount → Color,
      IsProperAssignment fourthCataloguePartitionValid assignment ∧
        word.toList.map TraceSymbol.toColor =
          ringTraceOfAssignment fourthCataloguePartitionValid
            fourthCatalogueRing assignment := by
  simpa [fourthCatalogueRingVector] using
    fourthCatalogueWitnessCertificate.exists_properAssignment_of_mem_words
      fourthCataloguePartitionValid fourthCatalogueRingVector
      fourthCatalogueWitnessCertificate_checker word hword

/-- The equality components induced by the four selected contract edges,
with an actual contracted dart certifying every forest link. -/
def fourthCatalogueComponents : ClassicalCertificateContractComponents.Code where
  componentCount := 8
  componentOfFace :=
    #[0, 1, 1, 1, 2, 3, 4, 5, 4, 6, 7, 4]
  representative :=
    #[0, 1, 4, 5, 6, 7, 9, 10]
  parent :=
    #[0, 1, 1, 2, 4, 5, 6, 7, 11, 9, 10, 6]
  linkDart :=
    #[0, 0, 24, 12, 0, 0, 0, 0, 32, 0, 0, 38]
  depth :=
    #[0, 0, 1, 2, 0, 0, 0, 0, 2, 0, 0, 1]

theorem fourthCatalogueComponents_checker :
    ClassicalCertificateContractComponents.checker
      fourthCataloguePartitionValid fourthCatalogueContract
        fourthCatalogueComponents = true := by
  decide

def fourthCatalogueComponentsValid :
    ClassicalCertificateContractComponents.Valid fourthCataloguePartitionValid
      fourthCatalogueContract fourthCatalogueComponents :=
  ClassicalCertificateContractComponents.valid_of_checker_true
    fourthCataloguePartitionValid fourthCatalogueContract
      fourthCatalogueComponents fourthCatalogueComponents_checker

/-- Constructor-normal trie of the 150 contract roots needed by the ranked
Kempe dependency graph. -/
def fourthCoveredTraceTree : TraceTree :=
  (.node
    (.node
          (.node
                  (.node
                            (.node
                                        .empty
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                    )
                                                    )
                                      )
                            (.node
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                        (.node
                                                      .empty
                                                      .empty
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                        .empty
                                      )
                            (.node
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                    )
                                                    )
                                        .empty
                                        .empty
                                      )
                          )
                  (.node
                            .empty
                            .empty
                            (.node
                                        .empty
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      .empty
                                                      .empty
                                                    )
                                        .empty
                                      )
                          )
                  .empty
                )
          (.node
                  (.node
                            .empty
                            (.node
                                        (.node
                                                      .empty
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      .empty
                                                    )
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      .empty
                                                      .empty
                                                    )
                                        .empty
                                      )
                            (.node
                                        (.node
                                                      .empty
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      .empty
                                                    )
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      .empty
                                                      .empty
                                                    )
                                        .empty
                                      )
                          )
                  (.node
                            (.node
                                        (.node
                                                      .empty
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      .empty
                                                    )
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                    )
                                                    )
                                      )
                            (.node
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                        (.node
                                                      .empty
                                                      .empty
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                        .empty
                                      )
                            (.node
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                    )
                                                    )
                                        (.node
                                                      .empty
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      .empty
                                                    )
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                      )
                          )
                  (.node
                            .empty
                            (.node
                                        (.node
                                                      .empty
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                    )
                                                      .empty
                                                    )
                                        .empty
                                        .empty
                                      )
                            (.node
                                        (.node
                                                      .empty
                                                      .empty
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                        .empty
                                        .empty
                                      )
                          )
                )
          (.node
                  (.node
                            .empty
                            .empty
                            (.node
                                        .empty
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      .empty
                                                      .empty
                                                    )
                                        .empty
                                      )
                          )
                  .empty
                  (.node
                            (.node
                                        .empty
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                    )
                                                    )
                                      )
                            (.node
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                        .empty
                                        .empty
                                      )
                            (.node
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                    )
                                                    )
                                        .empty
                                        .empty
                                      )
                          )
                )
        )
    (.node
          (.node
                  (.node
                            (.node
                                        .empty
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                        .empty
                                      )
                            (.node
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                        (.node
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      .empty
                                                      .empty
                                                    )
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                    )
                                                    )
                                      )
                            (.node
                                        (.node
                                                      .empty
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      .empty
                                                    )
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                    )
                                                    )
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                      )
                          )
                  (.node
                            (.node
                                        .empty
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      .empty
                                                      .empty
                                                    )
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      .empty
                                                      .empty
                                                    )
                                      )
                            .empty
                            .empty
                          )
                  (.node
                            (.node
                                        .empty
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      .empty
                                                      .empty
                                                    )
                                        .empty
                                      )
                            .empty
                            .empty
                          )
                )
          (.node
                  .empty
                  (.node
                            (.node
                                        .empty
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                        .empty
                                      )
                            (.node
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                        .empty
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                    )
                                                    )
                                      )
                            (.node
                                        .empty
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                    )
                                                    )
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      .empty
                                                      .empty
                                                    )
                                      )
                          )
                  (.node
                            (.node
                                        .empty
                                        .empty
                                        (.node
                                                      .empty
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      .empty
                                                    )
                                      )
                            .empty
                            .empty
                          )
                )
          (.node
                  .empty
                  (.node
                            (.node
                                        .empty
                                        (.node
                                                      .empty
                                                      .empty
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                    )
                                        .empty
                                      )
                            .empty
                            (.node
                                        (.node
                                                      .empty
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                        .empty
                                        .empty
                                      )
                          )
                  (.node
                            (.node
                                        .empty
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                        (.node
                                                      .empty
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                    )
                                      )
                            (.node
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                        .empty
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                    )
                                                    )
                                      )
                            (.node
                                        .empty
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                    )
                                                    )
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      .empty
                                                      .empty
                                                    )
                                      )
                          )
                )
        )
    (.node
          (.node
                  (.node
                            (.node
                                        .empty
                                        .empty
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                      )
                            (.node
                                        .empty
                                        .empty
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                      )
                            (.node
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                        .empty
                                      )
                          )
                  .empty
                  .empty
                )
          (.node
                  .empty
                  (.node
                            (.node
                                        .empty
                                        .empty
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                      )
                            (.node
                                        .empty
                                        .empty
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                      )
                            (.node
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                        .empty
                                      )
                          )
                  (.node
                            (.node
                                        .empty
                                        (.node
                                                      .empty
                                                      .empty
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                        .empty
                                      )
                            .empty
                            .empty
                          )
                )
          (.node
                  .empty
                  .empty
                  (.node
                            (.node
                                        .empty
                                        .empty
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                      )
                            (.node
                                        .empty
                                        .empty
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                      )
                            (.node
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                        .empty
                                      )
                          )
                )
        )
  )

/-- Constructor-normal trie of the 81 witnessed extendable words. -/
def fourthExtendableTraceTree : TraceTree :=
  (.node
    (.node
          (.node
                  (.node
                            (.node
                                        (.node
                                                      .empty
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      .empty
                                                    )
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                        .empty
                                      )
                            (.node
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                    )
                                                      .empty
                                                    )
                                        (.node
                                                      .empty
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                        (.node
                                                      .empty
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      .empty
                                                    )
                                      )
                            .empty
                          )
                  (.node
                            (.node
                                        (.node
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                    )
                                                    )
                                        .empty
                                        .empty
                                      )
                            (.node
                                        .empty
                                        (.node
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      .empty
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                    )
                                                    )
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                    )
                                                      .empty
                                                    )
                                      )
                            (.node
                                        .empty
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      .empty
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                    )
                                                    )
                                        (.node
                                                      .empty
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                    )
                                                      .empty
                                                    )
                                      )
                          )
                  .empty
                )
          (.node
                  (.node
                            (.node
                                        (.node
                                                      .empty
                                                      (.node
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      .empty
                                                    )
                                        .empty
                                        (.node
                                                      .empty
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                    )
                                      )
                            (.node
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      .empty
                                                    )
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                    )
                                                      .empty
                                                    )
                                        (.node
                                                      .empty
                                                      .empty
                                                      (.node
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                    )
                                      )
                            (.node
                                        (.node
                                                      .empty
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                    )
                                        .empty
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                    )
                                                      .empty
                                                    )
                                      )
                          )
                  (.node
                            (.node
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      .empty
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                    )
                                                    )
                                      )
                            (.node
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      .empty
                                                    )
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      .empty
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                        (.node
                                                      .empty
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                    )
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                    )
                                      )
                            (.node
                                        (.node
                                                      .empty
                                                      .empty
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                    )
                                        (.node
                                                      .empty
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .empty
                                                                                        .leaf
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                    )
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                      )
                          )
                  (.node
                            (.node
                                        (.node
                                                      .empty
                                                      .empty
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                    )
                                        .empty
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                      )
                            (.node
                                        (.node
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                    )
                                                      .empty
                                                    )
                                        (.node
                                                      .empty
                                                      .empty
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                      .empty
                                                                    )
                                                    )
                                        (.node
                                                      .empty
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                      )
                            (.node
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                      (.node
                                                                                        .leaf
                                                                                        .empty
                                                                                        .empty
                                                                                      )
                                                                      .empty
                                                                    )
                                                      .empty
                                                      (.node
                                                                      .empty
                                                                      .empty
                                                                      (.node
                                                                                        .empty
                                                                                        .leaf
                                                                                        .empty
                                                                                      )
                                                                    )
                                                    )
                                        .empty
                                        .empty
                                      )
                          )
                )
          .empty
        )
    .empty
    .empty
  )

def fourthExtendableWordList : List (TraceWord 8) :=
  fourthCatalogueWitnessCertificate.witnesses.map Witness.word

theorem acceptedWords_fourthExtendableTraceTree :
    acceptedWords 8 fourthExtendableTraceTree = fourthExtendableWordList := by
  rfl

/-- Discovery ranks on the root-directed dependency graph. -/
def fourthRankEntries : List (Nat × Nat) :=
  [(10, 0), (12, 0), (20, 1), (24, 1), (28, 0), (30, 0), (40, 0), (44, 8), (50, 7), (52, 0),
    (56, 1), (60, 1), (68, 1), (70, 7), (76, 8), (80, 1), (82, 0), (94, 0), (98, 0), (104, 4),
    (106, 3), (120, 0), (128, 0), (132, 0), (140, 9), (146, 0), (164, 1), (176, 3), (178, 4),
    (184, 1), (188, 1), (196, 9), (208, 1), (226, 1), (228, 1), (240, 1), (246, 0), (260, 0),
    (266, 0), (336, 3), (352, 3), (354, 0), (368, 10), (374, 0), (380, 0), (384, 0), (392, 0),
    (396, 11), (404, 9), (434, 0), (458, 0), (460, 3), (476, 0), (492, 1), (502, 1), (508, 1),
    (596, 3), (616, 1), (622, 1), (634, 1), (672, 3), (676, 1), (678, 1), (684, 11), (688, 9),
    (700, 1), (704, 3), (708, 1), (718, 1), (724, 10), (738, 0), (798, 0), (804, 0), (810, 0),
    (822, 0), (838, 0), (840, 3), (846, 0), (850, 0), (854, 0), (866, 6), (878, 7), (882, 0),
    (890, 6), (902, 0), (910, 0), (912, 0), (920, 5), (944, 5), (946, 0), (958, 0), (962, 0),
    (972, 0), (976, 3), (982, 0), (984, 0), (996, 0), (1000, 0), (1002, 0), (1008, 3),
    (1012, 0), (1016, 0), (1022, 7), (1024, 0), (1028, 0), (1040, 8), (1042, 7), (1048, 0),
    (1052, 0), (1054, 0), (1066, 0), (1078, 3), (1080, 0), (1104, 0), (1112, 9), (1114, 5),
    (1118, 0), (1122, 0), (1126, 0), (1136, 3), (1148, 11), (1150, 4), (1156, 0), (1160, 3),
    (1166, 5), (1168, 3), (1172, 0), (1176, 1), (1180, 0), (1182, 0), (1188, 0), (1192, 3),
    (1198, 0), (1200, 0), (1212, 0), (1234, 0), (1244, 1), (1256, 8), (1268, 8), (1270, 0),
    (1272, 0), (1282, 0), (1294, 0), (1298, 4), (1302, 0), (1310, 4), (1312, 0), (1342, 0),
    (1360, 0), (1362, 0), (1374, 0), (1378, 0), (1380, 0), (1402, 0), (1428, 1), (1476, 1),
    (1500, 1), (1506, 1), (1550, 1), (1554, 1), (1558, 1), (1568, 1), (1588, 1), (1592, 1),
    (1594, 5), (1606, 5), (1620, 1), (1644, 1), (1648, 6), (1656, 1), (1660, 6), (1672, 7),
    (1676, 1), (1680, 3), (1692, 1), (1696, 1), (1700, 1), (1712, 1), (1730, 1), (1734, 1),
    (1742, 1), (1754, 1), (1756, 1), (1768, 8), (1780, 8), (1784, 1), (1788, 1), (1796, 1),
    (1848, 1), (1864, 4), (1866, 1), (1886, 1), (1888, 4), (1902, 1), (1910, 1), (1914, 1),
    (1928, 1), (1944, 1), (1952, 3), (1956, 1), (1964, 1), (1968, 1), (1972, 1), (1984, 1),
    (1988, 1), (1994, 7), (1996, 8), (2000, 1), (2004, 1), (2012, 1), (2014, 7), (2016, 3),
    (2020, 1), (2024, 1), (2026, 3), (2038, 3), (2042, 1), (2048, 4), (2050, 11), (2052, 1),
    (2060, 3), (2064, 1), (2072, 1), (2076, 1), (2084, 3), (2086, 5), (2090, 1), (2094, 1),
    (2098, 1), (2100, 1), (2108, 1), (2120, 3), (2132, 1), (2138, 5), (2140, 9), (2144, 1),
    (2152, 1), (2154, 1), (2160, 1), (2172, 1), (2200, 1), (2212, 1), (2214, 1), (2226, 1),
    (2238, 3), (2246, 1), (2248, 1), (2252, 9), (2256, 4), (2262, 1), (2268, 1), (2272, 3),
    (2276, 1), (2278, 1), (2280, 1), (2288, 6), (2292, 1), (2296, 1), (2298, 1), (2304, 3),
    (2308, 1), (2320, 1), (2324, 9), (2328, 6), (2336, 1), (2340, 1), (2348, 1), (2354, 1),
    (2356, 2), (2360, 5), (2364, 2), (2368, 1), (2370, 1), (2378, 10), (2382, 5), (2390, 2),
    (2394, 1), (2402, 2), (2404, 1), (2406, 1), (2412, 3), (2416, 1), (2428, 1), (2430, 1),
    (2434, 1), (2438, 1), (2440, 3), (2442, 1), (2458, 1), (2470, 1), (2486, 6), (2498, 7),
    (2506, 1), (2510, 6), (2542, 1), (2572, 1), (2584, 1), (2606, 5), (2618, 5), (2624, 1),
    (2638, 1), (2640, 1), (2646, 1), (2654, 1), (2658, 1), (2694, 1), (2702, 5), (2706, 1),
    (2714, 5), (2716, 1), (2728, 1), (2730, 1), (2752, 1), (2756, 9), (2768, 2), (2780, 9),
    (2802, 1), (2808, 1), (2818, 1), (2820, 1), (2832, 1), (2860, 2), (2872, 1), (2874, 1),
    (2886, 1), (2924, 11), (2926, 1), (2928, 3), (2936, 1), (2944, 3), (2972, 1), (2984, 1),
    (2986, 1), (2992, 10), (2996, 9), (3032, 1), (3034, 1), (3044, 1), (3092, 1), (3104, 1),
    (3140, 1), (3144, 3), (3160, 1), (3182, 1), (3184, 1), (3186, 1), (3194, 1), (3198, 1),
    (3206, 5), (3210, 3), (3218, 1), (3224, 9), (3240, 1), (3248, 9), (3250, 1), (3252, 1),
    (3260, 6), (3264, 1), (3268, 1), (3270, 1), (3290, 1), (3292, 1), (3296, 1), (3300, 6),
    (3308, 1), (3310, 1), (3312, 9), (3320, 1), (3336, 8), (3342, 1), (3350, 2), (3354, 5),
    (3362, 1), (3366, 1), (3374, 1), (3376, 1), (3378, 1), (3400, 1), (3416, 2), (3420, 1),
    (3456, 1), (3468, 1), (3516, 1), (3526, 1), (3528, 1), (3564, 8), (3568, 10), (3574, 1),
    (3576, 1), (3588, 1), (3616, 2), (3624, 1), (3632, 2), (3634, 1), (3636, 10), (3674, 1),
    (3686, 1), (3688, 1), (3700, 2), (3728, 1), (3740, 1), (3742, 1), (3752, 1), (3758, 1),
    (3780, 9), (3792, 2), (3804, 9), (3808, 1), (3830, 1), (3832, 1), (3844, 1), (3846, 5),
    (3854, 1), (3858, 5), (3866, 1), (3902, 1), (3906, 1), (3914, 1), (3920, 1), (3922, 1),
    (3936, 1), (3942, 4), (3954, 4), (3976, 1), (3988, 1), (4018, 1), (4050, 7), (4054, 1),
    (4062, 7), (4074, 7), (4090, 1), (4102, 1), (4118, 1), (4120, 2), (4122, 1), (4126, 1),
    (4130, 1), (4132, 1), (4144, 1), (4148, 2), (4154, 1), (4156, 1), (4158, 3), (4166, 1),
    (4170, 3), (4178, 5), (4182, 11), (4190, 1), (4192, 1), (4196, 3), (4200, 4), (4204, 2),
    (4206, 1), (4212, 1), (4220, 1), (4224, 1), (4232, 7), (4236, 8), (4240, 1), (4252, 1),
    (4256, 2), (4262, 1), (4264, 1), (4268, 1), (4272, 7), (4280, 1), (4282, 1), (4284, 1),
    (4288, 2), (4292, 1), (4298, 1), (4304, 5), (4308, 8), (4312, 1), (4314, 1), (4322, 2),
    (4334, 1), (4346, 1), (4348, 1), (4360, 1), (4388, 1), (4400, 1), (4406, 1), (4408, 1),
    (4416, 1), (4420, 9), (4422, 4), (4428, 1), (4440, 3), (4452, 1), (4460, 2), (4462, 1),
    (4466, 1), (4470, 1), (4474, 5), (4476, 2), (4484, 1), (4488, 1), (4496, 1), (4500, 3),
    (4508, 1), (4510, 10), (4512, 5), (4518, 1), (4522, 2), (4534, 2), (4536, 1), (4540, 1),
    (4544, 3), (4546, 6), (4548, 1), (4556, 1), (4560, 1), (4564, 9), (4566, 6), (4572, 1),
    (4576, 1), (4588, 1), (4592, 1), (4596, 1), (4604, 1), (4608, 3), (4616, 1), (4632, 1),
    (4646, 1), (4650, 1), (4658, 1), (4672, 5), (4674, 1), (4694, 1), (4696, 5), (4712, 2),
    (4764, 1), (4772, 1), (4776, 1), (4780, 9), (4792, 9), (4804, 2), (4806, 1), (4818, 1),
    (4826, 1), (4830, 1), (4848, 1), (4860, 1), (4864, 1), (4868, 1), (4880, 3), (4884, 1),
    (4888, 6), (4900, 6), (4904, 1), (4912, 7), (4916, 1), (4940, 1), (4954, 5), (4966, 5),
    (4968, 1), (4972, 1), (4992, 1), (5002, 1), (5006, 1), (5010, 1), (5054, 1), (5060, 1),
    (5084, 1), (5132, 2), (5158, 1), (5180, 1), (5182, 1), (5186, 1), (5198, 1), (5200, 1),
    (5218, 1), (5248, 1), (5250, 5), (5258, 1), (5262, 5), (5266, 1), (5278, 1), (5288, 1),
    (5290, 1), (5292, 9), (5304, 9), (5316, 2), (5326, 1), (5348, 1), (5360, 1), (5362, 1),
    (5368, 2), (5372, 1), (5378, 1), (5380, 1), (5384, 2), (5388, 1), (5392, 3), (5394, 4),
    (5400, 3), (5404, 1), (5410, 5), (5412, 11), (5424, 3), (5434, 1), (5438, 1), (5442, 1),
    (5446, 5), (5448, 8), (5456, 1), (5480, 1), (5482, 2), (5494, 1), (5506, 1), (5508, 1),
    (5512, 1), (5518, 7), (5520, 8), (5532, 1), (5536, 1), (5538, 7), (5544, 1), (5548, 1),
    (5552, 2), (5558, 1), (5560, 1), (5564, 1), (5576, 1), (5578, 1), (5584, 2), (5588, 1),
    (5598, 1), (5602, 1), (5614, 1), (5616, 4), (5640, 4), (5648, 1), (5650, 1), (5658, 1),
    (5670, 7), (5678, 1), (5682, 7), (5694, 7), (5706, 1), (5710, 1), (5714, 1), (5720, 2),
    (5722, 1), (5738, 1), (5750, 1), (5756, 1), (5762, 1), (5822, 1), (5836, 11), (5842, 1),
    (5852, 1), (5856, 3), (5860, 1), (5872, 9), (5876, 10), (5882, 1), (5884, 1), (5888, 3),
    (5926, 1), (5938, 1), (5944, 1), (5964, 3), (6052, 1), (6058, 1), (6068, 1), (6084, 1),
    (6100, 2), (6102, 1), (6126, 1), (6156, 8), (6164, 10), (6168, 1), (6176, 1), (6180, 1),
    (6186, 1), (6192, 10), (6206, 1), (6208, 2), (6224, 2), (6294, 1), (6300, 1), (6314, 1),
    (6320, 1), (6332, 1), (6334, 1), (6352, 1), (6364, 9), (6372, 1), (6376, 1), (6382, 5),
    (6384, 3), (6396, 1), (6414, 1), (6420, 8), (6428, 1), (6432, 1), (6440, 1), (6454, 2),
    (6456, 5), (6462, 1), (6466, 1), (6478, 1), (6480, 1), (6484, 9), (6490, 6), (6492, 1),
    (6500, 1), (6504, 1), (6508, 1), (6510, 6), (6516, 9), (6520, 1), (6530, 1), (6532, 1),
    (6536, 1), (6540, 1), (6548, 1), (6550, 1)]

def fourthCatalogueRank (word : TraceWord 8) : Nat :=
  match fourthRankEntries.find? fun entry => entry.1 == wordIndex word with
  | some entry => entry.2
  | none => 0

def fourthWordOfIndex (index : Nat) : TraceWord 8 :=
  ⟨[symbolOfDigit (index / 2187), symbolOfDigit (index / 729),
    symbolOfDigit (index / 243), symbolOfDigit (index / 81),
    symbolOfDigit (index / 27), symbolOfDigit (index / 9),
    symbolOfDigit (index / 3), symbolOfDigit index], rfl⟩

def fourthGramIndex (gram : GramWord 8) : Nat :=
  gram.toList.foldl (fun index step => index * 4 + gramStepDigit step) 0

/-- The 54 source-independent responses used by all chromogram rules in the
root-directed dependency graph. -/
def fourthResponseEntries : List (Nat × Nat) :=
  [(445, 3210), (505, 4170), (727, 3296), (877, 4074), (919, 4268), (2173, 3264),
    (2263, 3296), (2365, 3210), (2509, 4206), (2633, 3252), (2839, 3376), (3385, 3468),
    (3529, 3468), (4567, 2702), (5167, 2348), (5179, 2336), (5239, 2360), (5323, 2336),
    (5335, 2324), (5341, 2382), (5347, 2336), (5362, 2348), (5657, 2298), (5702, 2278),
    (5899, 2416), (5911, 2404), (5923, 2428), (5938, 2416), (6422, 2458), (8407, 3296),
    (8983, 3376), (12409, 4062), (12502, 4268), (12601, 3936), (12685, 3936), (12745, 4170),
    (12823, 4348), (13129, 4224), (16495, 1160), (16510, 1078), (16699, 1022), (16843, 1052),
    (16867, 1042), (17227, 1160), (17230, 1156), (17251, 1312), (17623, 920), (17942, 838),
    (18511, 1156), (18547, 1078), (18698, 1012), (18739, 1024), (19531, 1402), (19555, 1312)]

def fourthResponseTarget (gram : Nat) : Nat :=
  match fourthResponseEntries.find? fun entry => entry.1 == gram with
  | some entry => entry.2
  | none => 0

def fourthLowerPermutation (word : TraceWord 8) : Option PermutationCode :=
  permutationCodes.find? fun permutation =>
    decide (fourthCatalogueRank (permute permutation word) <
      fourthCatalogueRank word)

def fourthLowerResponse (_word : TraceWord 8) (gram : GramWord 8) :
    TraceWord 8 :=
  fourthWordOfIndex (fourthResponseTarget (fourthGramIndex gram))

def fourthCatalogueRule (word : TraceWord 8) : RuleCode 8 :=
  if word ∈ fourthCatalogueWitnessCertificate.words then .member
  else
    match fourthLowerPermutation word with
    | some permutation => .permutation permutation
    | none => .chromograms (fourthLowerResponse word)

/-- Root-directed ranked Kempe certificate for `cf004`. -/
def fourthCatalogueTreeKempeCertificate :
    ClassicalCertificateTreeRankedKempe.Certificate 8 where
  covered := fourthCoveredTraceTree
  extendable := fourthExtendableTraceTree
  rank := fourthCatalogueRank
  rule := fourthCatalogueRule

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem fourthCatalogueTreeKempeCertificate_checker :
    fourthCatalogueTreeKempeCertificate.checker = true := by
  rfl

theorem fourthCatalogueTree_root_kempeCoclosure
    (word : TraceWord 8)
    (hcovered : fourthCoveredTraceTree.accepts word.toList = true) :
    KempeCoclosure
      fourthCatalogueTreeKempeCertificate.ExtendableFamily word.toList := by
  exact fourthCatalogueTreeKempeCertificate.kempeCoclosure_of_checker_true
    fourthCatalogueTreeKempeCertificate_checker word hcovered

/-- A 305-node pruned search covers every coloring of the eight contract
components and accepts exactly at ranked roots. -/
def fourthCatalogueContractSearch :
    ClassicalCertificateContractColorSearch.Certificate 8 where
  order := [1, 4, 2, 3, 5, 6, 0, 7]
  tree :=
    (.node
    (.node
          .reject
          (.node
                  .reject
                  .reject
                  (.node
                            .reject
                            .reject
                            .reject
                            (.node
                                        .reject
                                        .reject
                                        (.node
                                                      .reject
                                                      .reject
                                                      .reject
                                                      (.node
                                                                      .reject
                                                                      (.node
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                    )
                                                    )
                                        (.node
                                                      .reject
                                                      .reject
                                                      (.node
                                                                      .reject
                                                                      (.node
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                    )
                                                      .reject
                                                    )
                                      )
                          )
                  (.node
                            .reject
                            .reject
                            (.node
                                        .reject
                                        .reject
                                        (.node
                                                      .reject
                                                      .reject
                                                      .reject
                                                      (.node
                                                                      .reject
                                                                      (.node
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                    )
                                                    )
                                        (.node
                                                      .reject
                                                      .reject
                                                      (.node
                                                                      .reject
                                                                      (.node
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                    )
                                                      .reject
                                                    )
                                      )
                            .reject
                          )
                )
          (.node
                  .reject
                  (.node
                            .reject
                            .reject
                            .reject
                            (.node
                                        .reject
                                        (.node
                                                      .reject
                                                      .reject
                                                      .reject
                                                      (.node
                                                                      .reject
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                      )
                                                                    )
                                                    )
                                        .reject
                                        (.node
                                                      .reject
                                                      (.node
                                                                      .reject
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                      )
                                                                    )
                                                      .reject
                                                      .reject
                                                    )
                                      )
                          )
                  .reject
                  (.node
                            .reject
                            (.node
                                        .reject
                                        (.node
                                                      .reject
                                                      .reject
                                                      .reject
                                                      (.node
                                                                      .reject
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                      )
                                                                    )
                                                    )
                                        .reject
                                        (.node
                                                      .reject
                                                      (.node
                                                                      .reject
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                      )
                                                                    )
                                                      .reject
                                                      .reject
                                                    )
                                      )
                            .reject
                            .reject
                          )
                )
          (.node
                  .reject
                  (.node
                            .reject
                            .reject
                            (.node
                                        .reject
                                        (.node
                                                      .reject
                                                      .reject
                                                      (.node
                                                                      .reject
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                      )
                                                                    )
                                                      .reject
                                                    )
                                        (.node
                                                      .reject
                                                      (.node
                                                                      .reject
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                      )
                                                                    )
                                                      .reject
                                                      .reject
                                                    )
                                        .reject
                                      )
                            .reject
                          )
                  (.node
                            .reject
                            (.node
                                        .reject
                                        (.node
                                                      .reject
                                                      .reject
                                                      (.node
                                                                      .reject
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                      )
                                                                    )
                                                      .reject
                                                    )
                                        (.node
                                                      .reject
                                                      (.node
                                                                      .reject
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                      )
                                                                    )
                                                      .reject
                                                      .reject
                                                    )
                                        .reject
                                      )
                            .reject
                            .reject
                          )
                  .reject
                )
        )
    (.node
          (.node
                  .reject
                  .reject
                  (.node
                            .reject
                            .reject
                            .reject
                            (.node
                                        .reject
                                        .reject
                                        (.node
                                                      .reject
                                                      .reject
                                                      .reject
                                                      (.node
                                                                      (.node
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      .reject
                                                                      (.node
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                    )
                                                    )
                                        (.node
                                                      .reject
                                                      .reject
                                                      (.node
                                                                      (.node
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      .reject
                                                                      (.node
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                    )
                                                      .reject
                                                    )
                                      )
                          )
                  (.node
                            .reject
                            .reject
                            (.node
                                        .reject
                                        .reject
                                        (.node
                                                      .reject
                                                      .reject
                                                      .reject
                                                      (.node
                                                                      (.node
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      .reject
                                                                      (.node
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                    )
                                                    )
                                        (.node
                                                      .reject
                                                      .reject
                                                      (.node
                                                                      (.node
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      .reject
                                                                      (.node
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                    )
                                                      .reject
                                                    )
                                      )
                            .reject
                          )
                )
          .reject
          (.node
                  (.node
                            .reject
                            .reject
                            .reject
                            (.node
                                        (.node
                                                      .reject
                                                      .reject
                                                      .reject
                                                      (.node
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                      )
                                                                      .reject
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                      )
                                                                    )
                                                    )
                                        .reject
                                        .reject
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                      )
                                                                      .reject
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                      )
                                                                    )
                                                      .reject
                                                      .reject
                                                      .reject
                                                    )
                                      )
                          )
                  .reject
                  .reject
                  (.node
                            (.node
                                        (.node
                                                      .reject
                                                      .reject
                                                      .reject
                                                      (.node
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                      )
                                                                      .reject
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                      )
                                                                    )
                                                    )
                                        .reject
                                        .reject
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                      )
                                                                      .reject
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                      )
                                                                    )
                                                      .reject
                                                      .reject
                                                      .reject
                                                    )
                                      )
                            .reject
                            .reject
                            .reject
                          )
                )
          (.node
                  (.node
                            .reject
                            .reject
                            (.node
                                        (.node
                                                      .reject
                                                      .reject
                                                      (.node
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                      )
                                                                      .reject
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                      )
                                                                    )
                                                      .reject
                                                    )
                                        .reject
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                      )
                                                                      .reject
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                      )
                                                                    )
                                                      .reject
                                                      .reject
                                                      .reject
                                                    )
                                        .reject
                                      )
                            .reject
                          )
                  .reject
                  (.node
                            (.node
                                        (.node
                                                      .reject
                                                      .reject
                                                      (.node
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                      )
                                                                      .reject
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                      )
                                                                    )
                                                      .reject
                                                    )
                                        .reject
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                      )
                                                                      .reject
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                      )
                                                                    )
                                                      .reject
                                                      .reject
                                                      .reject
                                                    )
                                        .reject
                                      )
                            .reject
                            .reject
                            .reject
                          )
                  .reject
                )
        )
    (.node
          (.node
                  .reject
                  (.node
                            .reject
                            .reject
                            .reject
                            (.node
                                        .reject
                                        (.node
                                                      .reject
                                                      .reject
                                                      .reject
                                                      (.node
                                                                      (.node
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      .reject
                                                                      (.node
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                    )
                                                    )
                                        .reject
                                        (.node
                                                      .reject
                                                      (.node
                                                                      (.node
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      .reject
                                                                      (.node
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                    )
                                                      .reject
                                                      .reject
                                                    )
                                      )
                          )
                  .reject
                  (.node
                            .reject
                            (.node
                                        .reject
                                        (.node
                                                      .reject
                                                      .reject
                                                      .reject
                                                      (.node
                                                                      (.node
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      .reject
                                                                      (.node
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                    )
                                                    )
                                        .reject
                                        (.node
                                                      .reject
                                                      (.node
                                                                      (.node
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      .reject
                                                                      (.node
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                    )
                                                      .reject
                                                      .reject
                                                    )
                                      )
                            .reject
                            .reject
                          )
                )
          (.node
                  (.node
                            .reject
                            .reject
                            .reject
                            (.node
                                        (.node
                                                      .reject
                                                      .reject
                                                      .reject
                                                      (.node
                                                                      (.node
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      .reject
                                                                      (.node
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                    )
                                                    )
                                        .reject
                                        .reject
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      .reject
                                                                      (.node
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                    )
                                                      .reject
                                                      .reject
                                                      .reject
                                                    )
                                      )
                          )
                  .reject
                  .reject
                  (.node
                            (.node
                                        (.node
                                                      .reject
                                                      .reject
                                                      .reject
                                                      (.node
                                                                      (.node
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      .reject
                                                                      (.node
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                    )
                                                    )
                                        .reject
                                        .reject
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      .reject
                                                                      (.node
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                    )
                                                      .reject
                                                      .reject
                                                      .reject
                                                    )
                                      )
                            .reject
                            .reject
                            .reject
                          )
                )
          .reject
          (.node
                  (.node
                            .reject
                            (.node
                                        (.node
                                                      .reject
                                                      (.node
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                      )
                                                                      .reject
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                      )
                                                                    )
                                                      .reject
                                                      .reject
                                                    )
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                      )
                                                                      .reject
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                      )
                                                                    )
                                                      .reject
                                                      .reject
                                                      .reject
                                                    )
                                        .reject
                                        .reject
                                      )
                            .reject
                            .reject
                          )
                  (.node
                            (.node
                                        (.node
                                                      .reject
                                                      (.node
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                      )
                                                                      .reject
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                      )
                                                                    )
                                                      .reject
                                                      .reject
                                                    )
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                      )
                                                                      .reject
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                      )
                                                                    )
                                                      .reject
                                                      .reject
                                                      .reject
                                                    )
                                        .reject
                                        .reject
                                      )
                            .reject
                            .reject
                            .reject
                          )
                  .reject
                  .reject
                )
        )
    (.node
          (.node
                  .reject
                  (.node
                            .reject
                            .reject
                            (.node
                                        .reject
                                        (.node
                                                      .reject
                                                      .reject
                                                      (.node
                                                                      (.node
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      .reject
                                                                    )
                                                      .reject
                                                    )
                                        (.node
                                                      .reject
                                                      (.node
                                                                      (.node
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      .reject
                                                                    )
                                                      .reject
                                                      .reject
                                                    )
                                        .reject
                                      )
                            .reject
                          )
                  (.node
                            .reject
                            (.node
                                        .reject
                                        (.node
                                                      .reject
                                                      .reject
                                                      (.node
                                                                      (.node
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      .reject
                                                                    )
                                                      .reject
                                                    )
                                        (.node
                                                      .reject
                                                      (.node
                                                                      (.node
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      .reject
                                                                    )
                                                      .reject
                                                      .reject
                                                    )
                                        .reject
                                      )
                            .reject
                            .reject
                          )
                  .reject
                )
          (.node
                  (.node
                            .reject
                            .reject
                            (.node
                                        (.node
                                                      .reject
                                                      .reject
                                                      (.node
                                                                      (.node
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      .reject
                                                                    )
                                                      .reject
                                                    )
                                        .reject
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      .reject
                                                                    )
                                                      .reject
                                                      .reject
                                                      .reject
                                                    )
                                        .reject
                                      )
                            .reject
                          )
                  .reject
                  (.node
                            (.node
                                        (.node
                                                      .reject
                                                      .reject
                                                      (.node
                                                                      (.node
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      .reject
                                                                    )
                                                      .reject
                                                    )
                                        .reject
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                        .accept
                                                                                      )
                                                                      .reject
                                                                    )
                                                      .reject
                                                      .reject
                                                      .reject
                                                    )
                                        .reject
                                      )
                            .reject
                            .reject
                            .reject
                          )
                  .reject
                )
          (.node
                  (.node
                            .reject
                            (.node
                                        (.node
                                                      .reject
                                                      (.node
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                      )
                                                                      .reject
                                                                    )
                                                      .reject
                                                      .reject
                                                    )
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                      )
                                                                      .reject
                                                                    )
                                                      .reject
                                                      .reject
                                                      .reject
                                                    )
                                        .reject
                                        .reject
                                      )
                            .reject
                            .reject
                          )
                  (.node
                            (.node
                                        (.node
                                                      .reject
                                                      (.node
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                      )
                                                                      .reject
                                                                    )
                                                      .reject
                                                      .reject
                                                    )
                                        (.node
                                                      (.node
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                      )
                                                                      (.node
                                                                                        .accept
                                                                                        .accept
                                                                                        .reject
                                                                                        .accept
                                                                                      )
                                                                      .reject
                                                                    )
                                                      .reject
                                                      .reject
                                                      .reject
                                                    )
                                        .reject
                                        .reject
                                      )
                            .reject
                            .reject
                            .reject
                          )
                  .reject
                  .reject
                )
          .reject
        )
  )

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem fourthCatalogueContractSearch_checker :
    fourthCatalogueContractSearch.checker fourthCatalogueComponentsValid
      fourthCatalogueRing fourthCoveredTraceTree = true := by
  rfl

/-- Standard semantic family of boundary traces induced by ordinary
colorings of `cf004`. -/
def FourthCatalogueExtendableTrace (word : List TraceSymbol) : Prop :=
  FiniteHypermap.RingTrace
    (checkedHypermap fourthCataloguePartitionValid) fourthCatalogueRing
      (word.map TraceSymbol.toColor)

theorem fourthCatalogue_extendableFamily_sound
    (word : List TraceSymbol)
    (hextendable :
      fourthCatalogueTreeKempeCertificate.ExtendableFamily word) :
    FourthCatalogueExtendableTrace word := by
  rcases hextendable with ⟨fixedWord, hfixed, haccepted⟩
  have hmemAccepted : fixedWord ∈
      acceptedWords 8 fourthExtendableTraceTree :=
    (mem_acceptedWords_iff fourthExtendableTraceTree fixedWord).2 (by
      simpa [fourthCatalogueTreeKempeCertificate] using haccepted)
  have hmemList : fixedWord ∈ fourthExtendableWordList := by
    simpa [acceptedWords_fourthExtendableTraceTree] using hmemAccepted
  have hmem : fixedWord ∈ fourthCatalogueWitnessCertificate.words := by
    simpa [fourthExtendableWordList, Certificate.words] using hmemList
  subst word
  obtain ⟨assignment, hproper, htrace⟩ :=
    fourthCatalogue_witnessWord_is_ringTrace fixedWord hmem
  exact (ringTrace_iff_exists_assignment fourthCataloguePartitionValid
    fourthCatalogueRing _).2 ⟨assignment, hproper, htrace⟩

/-- Every contracted `cf004` boundary trace lies in the Kempe co-closure of
a genuine ordinary boundary trace. -/
theorem fourthCatalogue_contractTrace_kempeCoclosure
    (word : List TraceSymbol)
    (hcontract : FiniteHypermap.ContractRingTrace
      (checkedHypermap fourthCataloguePartitionValid) fourthCatalogueContract
        fourthCatalogueRing (word.map TraceSymbol.toColor)) :
    KempeCoclosure FourthCatalogueExtendableTrace word := by
  obtain ⟨assignment, hassignment, htrace⟩ :=
    (contractRingTrace_iff_exists_assignment fourthCataloguePartitionValid
      fourthCatalogueContract fourthCatalogueRing _).1 hcontract
  have hlength : word.length = 8 := by
    calc
      word.length = (word.map TraceSymbol.toColor).length := by simp
      _ = (ringTraceOfAssignment fourthCataloguePartitionValid
          fourthCatalogueRing assignment).length :=
        congrArg List.length htrace
      _ = 8 := by
        simp [ringTraceOfAssignment, FiniteHypermap.ringColorWord,
          length_trace, fourthCatalogueRing]
  let fixedWord : TraceWord 8 := ⟨word, hlength⟩
  have hroot : fourthCoveredTraceTree.accepts fixedWord.toList = true := by
    apply fourthCatalogueContractSearch.accepts_of_contractWord
      fourthCatalogueComponentsValid fourthCatalogueRing
        fourthCoveredTraceTree fourthCatalogueContractSearch_checker
          fourthCatalogueRing_reverseBoundaryCycle
            fourthCatalogueContract_avoidsBoundary assignment hassignment
    exact htrace
  have hcoclosure :=
    fourthCatalogueTree_root_kempeCoclosure fixedWord hroot
  exact hcoclosure.mono fourthCatalogue_extendableFamily_sound

/-- Color-valued reducibility theorem for the fourth classical catalogue
configuration. -/
theorem fourthCatalogue_contractRingTrace_reduces
    (boundaryTrace : List Color)
    (hcontract : FiniteHypermap.ContractRingTrace
      (checkedHypermap fourthCataloguePartitionValid) fourthCatalogueContract
        fourthCatalogueRing boundaryTrace) :
    ∃ symbols : List TraceSymbol,
      symbols.map TraceSymbol.toColor = boundaryTrace ∧
        KempeCoclosure FourthCatalogueExtendableTrace symbols := by
  obtain ⟨assignment, hassignment, htrace⟩ :=
    (contractRingTrace_iff_exists_assignment fourthCataloguePartitionValid
      fourthCatalogueContract fourthCatalogueRing boundaryTrace).1 hcontract
  obtain ⟨symbols, hsymbols, _⟩ :=
    fourthCatalogue_contractAssignment_trace_symbols assignment hassignment
  have hsymbolsBoundary :
      symbols.map TraceSymbol.toColor = boundaryTrace :=
    hsymbols.trans htrace.symm
  refine ⟨symbols, hsymbolsBoundary, ?_⟩
  apply fourthCatalogue_contractTrace_kempeCoclosure
  simpa [hsymbolsBoundary] using hcontract

end ClassicalCertificateCatalogueFour

end Mettapedia.GraphTheory.FourColor
