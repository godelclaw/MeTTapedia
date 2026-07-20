import Mettapedia.GraphTheory.FourColor.ClassicalCertificateEvenTraceKempe

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwo

open ClassicalCertificateColorTrace
open ClassicalCertificateConfiguration
open ClassicalCertificateEvenTraceKempe
open ClassicalCertificateFacePartition
open ClassicalCertificateHypermap
open ClassicalCertificateHypermapColoring
open ClassicalCertificateKempeClosure
open ClassicalCertificateRankedKempe
open ClassicalCertificateTraceTree
open ClassicalCertificateTraceWitness
open ClassicalCertificateTreeRankedKempe

/-- The second entry of the classical reducible-configuration catalogue. -/
def secondCatalogueSample : Configuration where
  symmetric := true
  contractReferences := [6]
  program :=
    [.hexagon, .rotate 2, .hexagon, .rotate 6, .yellow, .rotate 4,
      .hexagon, .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 4,
      .yellow, .rotate 2, .yellow, .yellow]

/-- Materialized finite hypermap for catalogue configuration `cf002`. -/
def secondCatalogueSampleCode : HypermapCode where
  dartCount := 46
  edge :=
    #[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23,
    22, 25, 24, 27, 26, 29, 28, 31, 30, 33, 32, 35, 34, 37, 36, 39, 38, 41, 40, 43, 42,
    45, 44]
  node :=
    #[5, 25, 1, 12, 3, 6, 11, 15, 7, 32, 9, 26, 4, 45, 13, 8, 21, 31, 17, 22, 19, 0, 20,
    39, 23, 2, 16, 35, 27, 36, 29, 18, 10, 40, 33, 28, 30, 43, 37, 24, 34, 44, 41, 38,
    42, 14]
  face :=
    #[2, 21, 4, 25, 0, 12, 8, 5, 10, 15, 6, 32, 14, 3, 7, 45, 18, 26, 20, 31, 16, 22,
    24, 19, 1, 39, 28, 11, 30, 35, 17, 36, 34, 9, 27, 40, 38, 29, 23, 43, 42, 33, 37,
    44, 13, 41]

theorem secondCatalogueSampleCode_checker :
    secondCatalogueSampleCode.checker = true := by
  decide

def secondCatalogueContractDarts : List Nat := [45]

private def secondCatalogueDart : Fin 46 →
    Fin secondCatalogueSampleCode.dartCount :=
  Fin.cast (by rfl)

/-- The seven outer-ring darts of `cf002`, in boundary-trace order. -/
def secondCatalogueRing : List (Fin secondCatalogueSampleCode.dartCount) :=
  [secondCatalogueDart 6, secondCatalogueDart 11, secondCatalogueDart 26,
    secondCatalogueDart 16, secondCatalogueDart 21, secondCatalogueDart 0,
    secondCatalogueDart 5]

/-- Face-orbit quotient of `cf002`'s 46 darts into eleven face variables. -/
def secondCatalogueFacePartition : Code where
  faceCount := 11
  classOf :=
    #[0, 1, 0, 2, 0, 3, 4, 3, 4, 5, 4, 6, 3, 2, 3, 5, 7, 8, 7, 9, 7, 1, 1, 9, 1, 2, 8,
    6, 8, 10, 8, 9, 6, 5, 6, 10, 9, 10, 9, 2, 10, 5, 10, 2, 2, 5]
  representative :=
    #[0, 1, 3, 5, 6, 9, 11, 16, 17, 19, 29]
  distance :=
    #[0, 0, 2, 0, 1, 0, 0, 1, 2, 0, 1, 0, 3, 1, 2, 4, 0, 0, 2, 0, 1, 3, 2, 1, 1, 5, 3,
    1, 2, 0, 1, 4, 3, 1, 2, 4, 3, 1, 2, 4, 3, 2, 2, 3, 2, 3]

theorem secondCatalogueFacePartition_checker :
    checker secondCatalogueSampleCode secondCatalogueFacePartition = true := by
  decide

def secondCataloguePartitionValid :
    Valid secondCatalogueSampleCode secondCatalogueFacePartition :=
  valid_of_checker_true secondCatalogueSampleCode
    secondCatalogueFacePartition secondCatalogueFacePartition_checker

private def secondCatalogueContractDart :
    Fin secondCatalogueSampleCode.dartCount :=
  Fin.cast (by rfl) (45 : Fin 46)

/-- The contract edge selected by catalogue entry `cf002`. -/
def secondCatalogueContract :
    Finset (Fin secondCatalogueSampleCode.dartCount) :=
  {secondCatalogueContractDart}

theorem secondCatalogueContract_values :
    secondCatalogueContract.toList.map Fin.val =
      secondCatalogueContractDarts := by
  rw [show secondCatalogueContract = {secondCatalogueContractDart} from rfl,
    Finset.toList_singleton]
  simp only [List.map_singleton, secondCatalogueContractDarts,
    List.cons.injEq]
  exact ⟨Fin.val_cast _ _, True.intro⟩

theorem secondCatalogueRing_reverseBoundaryCycle :
    RawReverseBoundaryCycle secondCatalogueSampleCode secondCatalogueRing := by
  decide

theorem secondCatalogueContract_avoidsBoundary :
    ContractAvoidsBoundary secondCatalogueContract secondCatalogueRing := by
  decide

theorem secondCatalogue_contractAssignment_trace_symbols
    (assignment : Fin secondCatalogueFacePartition.faceCount → Color)
    (hcontract : IsContractAssignment secondCataloguePartitionValid
      secondCatalogueContract assignment) :
    ∃! symbols : List TraceSymbol,
      symbols.map TraceSymbol.toColor =
        ringTraceOfAssignment secondCataloguePartitionValid
          secondCatalogueRing assignment := by
  apply existsUnique_traceSymbolWord
  exact cyclicallyDistinct_ringColorWord_of_contract
    secondCataloguePartitionValid secondCatalogueContract secondCatalogueRing
      assignment hcontract secondCatalogueRing_reverseBoundaryCycle
        secondCatalogueContract_avoidsBoundary

def secondCatalogueRingVector :
    List.Vector (Fin secondCatalogueSampleCode.dartCount) 7 :=
  ⟨secondCatalogueRing, by decide⟩

/-- Thirty-nine ordinary-coloring witnesses, one per global-color orbit of
extendable boundary traces for `cf002`. -/
def secondCatalogueWitnessCertificate : Certificate 11 7 where
  witnesses :=
    [
      { colors := ⟨[.zero, .blue, .purple, .red, .blue, .zero, .purple, .purple, .blue, .zero, .red], rfl⟩,
        word := ⟨[.red, .red, .red, .red, .blue, .red, .purple], rfl⟩ },
      { colors := ⟨[.zero, .red, .blue, .red, .blue, .zero, .purple, .purple, .blue, .zero, .red], rfl⟩,
        word := ⟨[.red, .red, .red, .blue, .red, .red, .purple], rfl⟩ },
      { colors := ⟨[.zero, .red, .blue, .purple, .blue, .zero, .purple, .purple, .blue, .zero, .red], rfl⟩,
        word := ⟨[.red, .red, .red, .blue, .red, .purple, .red], rfl⟩ },
      { colors := ⟨[.zero, .blue, .red, .blue, .red, .purple, .zero, .zero, .red, .purple, .blue], rfl⟩,
        word := ⟨[.red, .red, .red, .blue, .blue, .blue, .purple], rfl⟩ },
      { colors := ⟨[.zero, .purple, .red, .purple, .zero, .blue, .red, .red, .zero, .blue, .purple], rfl⟩,
        word := ⟨[.red, .red, .red, .blue, .purple, .purple, .purple], rfl⟩ },
      { colors := ⟨[.zero, .red, .blue, .red, .blue, .zero, .purple, .zero, .blue, .purple, .red], rfl⟩,
        word := ⟨[.red, .red, .blue, .red, .red, .red, .purple], rfl⟩ },
      { colors := ⟨[.zero, .red, .blue, .purple, .blue, .red, .purple, .zero, .blue, .purple, .zero], rfl⟩,
        word := ⟨[.red, .red, .blue, .red, .red, .purple, .red], rfl⟩ },
      { colors := ⟨[.zero, .blue, .red, .blue, .red, .purple, .zero, .purple, .red, .zero, .blue], rfl⟩,
        word := ⟨[.red, .red, .blue, .red, .blue, .blue, .purple], rfl⟩ },
      { colors := ⟨[.zero, .blue, .red, .purple, .red, .blue, .zero, .purple, .red, .zero, .purple], rfl⟩,
        word := ⟨[.red, .red, .blue, .red, .blue, .purple, .blue], rfl⟩ },
      { colors := ⟨[.zero, .purple, .blue, .red, .purple, .zero, .blue, .red, .purple, .zero, .red], rfl⟩,
        word := ⟨[.red, .red, .blue, .blue, .purple, .red, .blue], rfl⟩ },
      { colors := ⟨[.zero, .blue, .purple, .red, .purple, .zero, .blue, .red, .purple, .zero, .red], rfl⟩,
        word := ⟨[.red, .red, .blue, .purple, .blue, .red, .blue], rfl⟩ },
      { colors := ⟨[.zero, .blue, .purple, .blue, .purple, .zero, .blue, .red, .purple, .zero, .red], rfl⟩,
        word := ⟨[.red, .red, .blue, .purple, .blue, .blue, .red], rfl⟩ },
      { colors := ⟨[.zero, .purple, .blue, .purple, .blue, .red, .purple, .zero, .blue, .red, .zero], rfl⟩,
        word := ⟨[.red, .red, .blue, .purple, .purple, .purple, .red], rfl⟩ },
      { colors := ⟨[.zero, .red, .blue, .purple, .blue, .red, .purple, .zero, .red, .purple, .zero], rfl⟩,
        word := ⟨[.red, .blue, .red, .red, .red, .purple, .red], rfl⟩ },
      { colors := ⟨[.zero, .blue, .red, .purple, .red, .blue, .zero, .purple, .blue, .zero, .purple], rfl⟩,
        word := ⟨[.red, .blue, .red, .red, .blue, .purple, .blue], rfl⟩ },
      { colors := ⟨[.zero, .purple, .blue, .red, .zero, .purple, .red, .blue, .purple, .red, .zero], rfl⟩,
        word := ⟨[.red, .blue, .red, .red, .purple, .red, .red], rfl⟩ },
      { colors := ⟨[.zero, .purple, .red, .blue, .zero, .purple, .red, .blue, .purple, .zero, .blue], rfl⟩,
        word := ⟨[.red, .blue, .red, .red, .purple, .blue, .blue], rfl⟩ },
      { colors := ⟨[.zero, .blue, .red, .purple, .blue, .zero, .purple, .zero, .red, .purple, .blue], rfl⟩,
        word := ⟨[.red, .blue, .red, .blue, .blue, .purple, .red], rfl⟩ },
      { colors := ⟨[.zero, .purple, .red, .blue, .purple, .zero, .blue, .red, .zero, .blue, .purple], rfl⟩,
        word := ⟨[.red, .blue, .red, .blue, .purple, .blue, .red], rfl⟩ },
      { colors := ⟨[.zero, .blue, .purple, .red, .blue, .zero, .purple, .purple, .red, .zero, .blue], rfl⟩,
        word := ⟨[.red, .blue, .blue, .red, .blue, .red, .purple], rfl⟩ },
      { colors := ⟨[.zero, .blue, .red, .purple, .blue, .zero, .purple, .purple, .red, .zero, .blue], rfl⟩,
        word := ⟨[.red, .blue, .blue, .red, .blue, .purple, .red], rfl⟩ },
      { colors := ⟨[.zero, .purple, .blue, .red, .purple, .zero, .blue, .blue, .zero, .red, .purple], rfl⟩,
        word := ⟨[.red, .blue, .blue, .red, .purple, .red, .blue], rfl⟩ },
      { colors := ⟨[.zero, .red, .purple, .red, .blue, .zero, .purple, .purple, .red, .zero, .blue], rfl⟩,
        word := ⟨[.red, .blue, .blue, .blue, .red, .red, .purple], rfl⟩ },
      { colors := ⟨[.zero, .purple, .red, .blue, .zero, .purple, .red, .red, .purple, .zero, .blue], rfl⟩,
        word := ⟨[.red, .blue, .blue, .blue, .purple, .blue, .blue], rfl⟩ },
      { colors := ⟨[.zero, .purple, .red, .purple, .zero, .blue, .red, .red, .purple, .blue, .zero], rfl⟩,
        word := ⟨[.red, .blue, .blue, .blue, .purple, .purple, .purple], rfl⟩ },
      { colors := ⟨[.zero, .red, .blue, .red, .purple, .zero, .blue, .blue, .zero, .purple, .red], rfl⟩,
        word := ⟨[.red, .blue, .blue, .purple, .red, .red, .blue], rfl⟩ },
      { colors := ⟨[.zero, .blue, .red, .blue, .zero, .purple, .red, .red, .purple, .zero, .blue], rfl⟩,
        word := ⟨[.red, .blue, .blue, .purple, .blue, .blue, .blue], rfl⟩ },
      { colors := ⟨[.zero, .red, .purple, .red, .zero, .blue, .red, .zero, .purple, .blue, .zero], rfl⟩,
        word := ⟨[.red, .blue, .purple, .red, .red, .red, .red], rfl⟩ },
      { colors := ⟨[.zero, .purple, .red, .purple, .blue, .zero, .purple, .blue, .red, .zero, .blue], rfl⟩,
        word := ⟨[.red, .blue, .purple, .red, .purple, .purple, .red], rfl⟩ },
      { colors := ⟨[.zero, .red, .purple, .red, .purple, .zero, .blue, .purple, .zero, .blue, .red], rfl⟩,
        word := ⟨[.red, .blue, .purple, .blue, .red, .red, .blue], rfl⟩ },
      { colors := ⟨[.zero, .red, .purple, .blue, .purple, .zero, .blue, .purple, .zero, .blue, .red], rfl⟩,
        word := ⟨[.red, .blue, .purple, .blue, .red, .blue, .red], rfl⟩ },
      { colors := ⟨[.zero, .blue, .purple, .red, .zero, .blue, .red, .zero, .purple, .red, .zero], rfl⟩,
        word := ⟨[.red, .blue, .purple, .blue, .blue, .red, .red], rfl⟩ },
      { colors := ⟨[.zero, .purple, .red, .purple, .red, .blue, .zero, .red, .blue, .zero, .purple], rfl⟩,
        word := ⟨[.red, .blue, .purple, .blue, .purple, .purple, .blue], rfl⟩ },
      { colors := ⟨[.zero, .red, .purple, .red, .blue, .zero, .purple, .blue, .red, .zero, .blue], rfl⟩,
        word := ⟨[.red, .blue, .purple, .purple, .red, .red, .purple], rfl⟩ },
      { colors := ⟨[.zero, .red, .blue, .purple, .blue, .red, .purple, .blue, .red, .purple, .zero], rfl⟩,
        word := ⟨[.red, .blue, .purple, .purple, .red, .purple, .red], rfl⟩ },
      { colors := ⟨[.zero, .blue, .red, .purple, .red, .blue, .zero, .red, .blue, .zero, .purple], rfl⟩,
        word := ⟨[.red, .blue, .purple, .purple, .blue, .purple, .blue], rfl⟩ },
      { colors := ⟨[.zero, .purple, .blue, .red, .zero, .purple, .red, .zero, .purple, .red, .zero], rfl⟩,
        word := ⟨[.red, .blue, .purple, .purple, .purple, .red, .red], rfl⟩ },
      { colors := ⟨[.zero, .purple, .red, .blue, .zero, .purple, .red, .zero, .purple, .blue, .zero], rfl⟩,
        word := ⟨[.red, .blue, .purple, .purple, .purple, .blue, .blue], rfl⟩ },
      { colors := ⟨[.zero, .purple, .red, .purple, .zero, .blue, .red, .zero, .purple, .blue, .zero], rfl⟩,
        word := ⟨[.red, .blue, .purple, .purple, .purple, .purple, .purple], rfl⟩ }
    ]

theorem secondCatalogueWitnessCertificate_checker :
    secondCatalogueWitnessCertificate.checker secondCataloguePartitionValid
      secondCatalogueRingVector = true := by
  decide

theorem secondCatalogue_witnessWord_is_ringTrace
    (word : TraceWord 7)
    (hword : word ∈ secondCatalogueWitnessCertificate.words) :
    ∃ assignment : Fin secondCatalogueFacePartition.faceCount → Color,
      IsProperAssignment secondCataloguePartitionValid assignment ∧
        word.toList.map TraceSymbol.toColor =
          ringTraceOfAssignment secondCataloguePartitionValid
            secondCatalogueRing assignment := by
  simpa [secondCatalogueRingVector] using
    secondCatalogueWitnessCertificate.exists_properAssignment_of_mem_words
      secondCataloguePartitionValid secondCatalogueRingVector
      secondCatalogueWitnessCertificate_checker word hword

/-- A compressed ternary lookup table. Constant suffix
subtrees are represented by one value constructor. -/
inductive TernaryTable (α : Type) where
  | value (result : α)
  | node (red blue purple : TernaryTable α)

namespace TernaryTable

def lookup (fallback : α) : TernaryTable α → List TraceSymbol → α
  | .value result, _ => result
  | .node _ _ _, [] => fallback
  | .node red _ _, .red :: rest => red.lookup fallback rest
  | .node _ blue _, .blue :: rest => blue.lookup fallback rest
  | .node _ _ purple, .purple :: rest => purple.lookup fallback rest

end TernaryTable

/-- Compressed discovery ranks for all seven-symbol words. -/
def secondCatalogueRankTree : TernaryTable Nat :=
  (.node
  (.node
    (.node
      (.node
        (.node
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 7)
            )
            (.node
              (.value 0)
              (.value 7)
              (.value 0)
            )
          )
          (.node
            (.value 0)
            (.value 0)
            (.node
              (.value 6)
              (.value 0)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 6)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
        )
        (.node
          (.value 0)
          (.node
            (.value 0)
            (.value 0)
            (.node
              (.value 0)
              (.value 9)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 7)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 9)
              (.value 0)
            )
            (.value 0)
          )
        )
        (.node
          (.node
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
          (.node
            (.node
              (.value 7)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 9)
            )
          )
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 9)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
          )
        )
      )
      (.node
        (.node
          (.value 0)
          (.value 0)
          (.node
            (.node
              (.value 9)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 9)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 10)
            )
          )
        )
        (.node
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 5)
            )
            (.node
              (.value 0)
              (.value 4)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 7)
            )
            (.value 0)
            (.node
              (.value 4)
              (.value 0)
              (.value 0)
            )
          )
          (.node
            (.value 0)
            (.node
              (.value 3)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
        )
        (.node
          (.node
            (.node
              (.value 11)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 12)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 11)
            )
          )
          (.value 0)
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 8)
            )
            (.value 0)
            (.value 0)
          )
        )
      )
      (.node
        (.node
          (.node
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
          (.node
            (.node
              (.value 9)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 10)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 9)
            )
          )
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
          )
        )
        (.node
          (.node
            (.node
              (.value 11)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 11)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 12)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 8)
              (.value 0)
            )
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.value 0)
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
          )
        )
        (.node
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 4)
            )
            (.node
              (.value 0)
              (.value 5)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.value 0)
            (.node
              (.value 3)
              (.value 0)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 7)
              (.value 0)
            )
            (.node
              (.value 4)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
        )
      )
    )
    (.node
      (.node
        (.node
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 11)
            )
            (.value 0)
            (.value 0)
          )
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 7)
            )
            (.value 0)
          )
          (.node
            (.value 0)
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 8)
            )
          )
        )
        (.node
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 7)
            )
            (.node
              (.value 0)
              (.value 3)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 13)
            )
            (.value 0)
            (.value 0)
          )
          (.node
            (.node
              (.value 0)
              (.value 3)
              (.value 0)
            )
            (.value 0)
            (.value 0)
          )
        )
        (.node
          (.node
            (.node
              (.value 11)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 13)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 13)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 7)
              (.value 0)
            )
            (.node
              (.value 7)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 13)
            )
            (.value 0)
            (.node
              (.value 8)
              (.value 0)
              (.value 0)
            )
          )
        )
      )
      (.node
        (.node
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 13)
            )
            (.node
              (.value 0)
              (.value 9)
              (.value 0)
            )
          )
          (.value 0)
          (.node
            (.value 0)
            (.node
              (.value 4)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
        )
        (.node
          (.node
            (.value 0)
            (.value 0)
            (.node
              (.value 3)
              (.value 0)
              (.value 0)
            )
          )
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 10)
            )
            (.node
              (.value 0)
              (.value 9)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 5)
              (.value 0)
              (.value 0)
            )
            (.value 0)
            (.value 0)
          )
        )
        (.node
          (.node
            (.value 0)
            (.node
              (.value 4)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
          (.node
            (.node
              (.value 6)
              (.value 0)
              (.value 0)
            )
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 9)
            )
          )
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 10)
            )
            (.node
              (.value 0)
              (.value 10)
              (.value 0)
            )
          )
        )
      )
      (.node
        (.node
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 11)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 13)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 9)
              (.value 0)
            )
            (.node
              (.value 3)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 10)
            )
            (.value 0)
            (.value 0)
          )
        )
        (.node
          (.value 0)
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 10)
            )
          )
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 9)
            )
            (.value 0)
          )
        )
        (.node
          (.value 0)
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.value 0)
          )
          (.value 0)
        )
      )
    )
    (.node
      (.node
        (.node
          (.node
            (.node
              (.value 0)
              (.value 11)
              (.value 0)
            )
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
          (.node
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 8)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
          )
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.node
              (.value 0)
              (.value 7)
              (.value 0)
            )
          )
        )
        (.node
          (.node
            (.node
              (.value 11)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 13)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 13)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 13)
              (.value 0)
            )
            (.node
              (.value 8)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 7)
            )
            (.value 0)
            (.node
              (.value 7)
              (.value 0)
              (.value 0)
            )
          )
        )
        (.node
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 3)
            )
            (.node
              (.value 0)
              (.value 7)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 3)
            )
            (.value 0)
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 13)
              (.value 0)
            )
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
        )
      )
      (.node
        (.node
          (.node
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 13)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 11)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 10)
              (.value 0)
            )
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 9)
            )
            (.value 0)
            (.node
              (.value 3)
              (.value 0)
              (.value 0)
            )
          )
        )
        (.node
          (.node
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
          (.node
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
          )
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
          )
        )
        (.node
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.value 0)
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
          )
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.node
              (.value 0)
              (.value 9)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 10)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
          )
        )
      )
      (.node
        (.node
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 9)
            )
            (.node
              (.value 0)
              (.value 13)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.value 0)
            (.node
              (.value 4)
              (.value 0)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
        )
        (.node
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.value 0)
            (.node
              (.value 4)
              (.value 0)
              (.value 0)
            )
          )
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 10)
            )
            (.node
              (.value 0)
              (.value 10)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 6)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 9)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
          )
        )
        (.node
          (.node
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 3)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
          (.node
            (.node
              (.value 5)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
          )
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 9)
            )
            (.node
              (.value 0)
              (.value 10)
              (.value 0)
            )
          )
        )
      )
    )
  )
  (.node
    (.node
      (.node
        (.node
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 11)
            )
            (.value 0)
            (.node
              (.value 9)
              (.value 0)
              (.value 0)
            )
          )
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.node
              (.value 0)
              (.value 3)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 4)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
          )
        )
        (.node
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 12)
            )
            (.value 0)
            (.node
              (.value 9)
              (.value 0)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 5)
              (.value 0)
            )
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
        )
        (.node
          (.node
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 7)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 8)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 5)
              (.value 0)
            )
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 11)
            )
            (.value 0)
            (.node
              (.value 10)
              (.value 0)
              (.value 0)
            )
          )
        )
      )
      (.node
        (.node
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 12)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 7)
            )
            (.value 0)
            (.node
              (.value 3)
              (.value 0)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 3)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
        )
        (.node
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 7)
            )
            (.value 0)
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
          )
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 10)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 9)
            )
          )
        )
        (.node
          (.node
            (.node
              (.value 0)
              (.value 7)
              (.value 0)
            )
            (.node
              (.value 7)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
          (.node
            (.node
              (.value 12)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 10)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 12)
            )
          )
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 12)
            )
            (.node
              (.value 0)
              (.value 9)
              (.value 0)
            )
          )
        )
      )
      (.node
        (.node
          (.node
            (.node
              (.value 2)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 11)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 8)
            )
            (.value 0)
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
          )
        )
        (.node
          (.node
            (.node
              (.value 0)
              (.value 3)
              (.value 0)
            )
            (.node
              (.value 8)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
          (.node
            (.node
              (.value 11)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 12)
            )
          )
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 11)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
          )
        )
        (.node
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 2)
            )
            (.value 0)
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
          )
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
          )
        )
      )
    )
    (.node
      (.node
        (.node
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 6)
            )
            (.node
              (.value 0)
              (.value 5)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 4)
            )
            (.value 0)
            (.node
              (.value 3)
              (.value 0)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 3)
              (.value 0)
            )
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
        )
        (.node
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.value 0)
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
          )
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 9)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 9)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 10)
            )
          )
        )
        (.node
          (.node
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
          (.node
            (.node
              (.value 13)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 10)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 10)
            )
          )
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 9)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
          )
        )
      )
      (.node
        (.node
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.value 0)
            (.node
              (.value 9)
              (.value 0)
              (.value 0)
            )
          )
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 9)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 6)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
          )
        )
        (.node
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.node
              (.value 0)
              (.value 6)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 7)
            )
            (.value 0)
            (.node
              (.value 6)
              (.value 0)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 5)
              (.value 0)
            )
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
        )
        (.node
          (.node
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 7)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 8)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 8)
            )
            (.value 0)
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
          )
        )
      )
      (.node
        (.node
          (.node
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 9)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
          (.node
            (.node
              (.value 11)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 11)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 12)
            )
          )
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
          )
        )
        (.node
          (.node
            (.node
              (.value 10)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 8)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 8)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.value 0)
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
          )
        )
        (.node
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.node
              (.value 0)
              (.value 2)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 4)
            )
            (.value 0)
            (.node
              (.value 5)
              (.value 0)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 5)
              (.value 0)
            )
            (.node
              (.value 6)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
        )
      )
    )
    (.node
      (.node
        (.node
          (.node
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.value 0)
            (.node
              (.value 2)
              (.value 0)
              (.value 0)
            )
          )
        )
        (.node
          (.node
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 10)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
          (.node
            (.node
              (.value 13)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 10)
            )
          )
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 9)
            )
            (.node
              (.value 0)
              (.value 2)
              (.value 0)
            )
          )
        )
        (.node
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.value 0)
            (.node
              (.value 9)
              (.value 0)
              (.value 0)
            )
          )
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 11)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 2)
            )
          )
        )
      )
      (.node
        (.node
          (.node
            (.node
              (.value 0)
              (.value 9)
              (.value 0)
            )
            (.node
              (.value 12)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
          (.node
            (.node
              (.value 12)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 11)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 12)
            )
          )
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 6)
            )
            (.node
              (.value 0)
              (.value 6)
              (.value 0)
            )
          )
        )
        (.node
          (.node
            (.node
              (.value 9)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 11)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.value 0)
            (.node
              (.value 6)
              (.value 0)
              (.value 0)
            )
          )
        )
        (.node
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 2)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 2)
            )
            (.value 0)
            (.node
              (.value 6)
              (.value 0)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 12)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
        )
      )
      (.node
        (.node
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 10)
            )
            (.value 0)
            (.node
              (.value 11)
              (.value 0)
              (.value 0)
            )
          )
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.node
              (.value 0)
              (.value 5)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 9)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 6)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
          )
        )
        (.node
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.node
              (.value 0)
              (.value 5)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 8)
            )
            (.value 0)
            (.node
              (.value 12)
              (.value 0)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
        )
        (.node
          (.node
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 5)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 2)
              (.value 0)
            )
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 8)
            )
            (.value 0)
            (.node
              (.value 11)
              (.value 0)
              (.value 0)
            )
          )
        )
      )
    )
  )
  (.node
    (.node
      (.node
        (.node
          (.node
            (.node
              (.value 0)
              (.value 11)
              (.value 0)
            )
            (.node
              (.value 9)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
          (.node
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 4)
            )
          )
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 3)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
          )
        )
        (.node
          (.node
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 8)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 7)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 11)
              (.value 0)
            )
            (.node
              (.value 10)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 5)
            )
            (.value 0)
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
          )
        )
        (.node
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 5)
            )
            (.value 0)
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 12)
              (.value 0)
            )
            (.node
              (.value 9)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
        )
      )
      (.node
        (.node
          (.node
            (.node
              (.value 2)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 11)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 8)
              (.value 0)
            )
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.value 0)
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
          )
        )
        (.node
          (.node
            (.node
              (.value 0)
              (.value 2)
              (.value 0)
            )
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
          (.node
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
          )
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
          )
        )
        (.node
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 3)
            )
            (.value 0)
            (.node
              (.value 8)
              (.value 0)
              (.value 0)
            )
          )
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.node
              (.value 0)
              (.value 11)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 11)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 12)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
          )
        )
      )
      (.node
        (.node
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.node
              (.value 0)
              (.value 12)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.value 0)
            (.node
              (.value 3)
              (.value 0)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 7)
              (.value 0)
            )
            (.node
              (.value 3)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
        )
        (.node
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 7)
            )
            (.value 0)
            (.node
              (.value 7)
              (.value 0)
              (.value 0)
            )
          )
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 9)
            )
            (.node
              (.value 0)
              (.value 12)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 12)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 12)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 10)
            )
          )
        )
        (.node
          (.node
            (.node
              (.value 0)
              (.value 7)
              (.value 0)
            )
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
          (.node
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 9)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
          )
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.node
              (.value 0)
              (.value 10)
              (.value 0)
            )
          )
        )
      )
    )
    (.node
      (.node
        (.node
          (.node
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 2)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.value 0)
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
          )
        )
        (.node
          (.node
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 9)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
          (.node
            (.node
              (.value 11)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 2)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
          )
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
          )
        )
        (.node
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.value 0)
            (.node
              (.value 10)
              (.value 0)
              (.value 0)
            )
          )
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 2)
            )
            (.node
              (.value 0)
              (.value 9)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 13)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 10)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
          )
        )
      )
      (.node
        (.node
          (.node
            (.node
              (.value 0)
              (.value 10)
              (.value 0)
            )
            (.node
              (.value 11)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
          (.node
            (.node
              (.value 9)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 6)
            )
          )
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 5)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
          )
        )
        (.node
          (.node
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 5)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 8)
              (.value 0)
            )
            (.node
              (.value 11)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 2)
            )
            (.value 0)
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
          )
        )
        (.node
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 5)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.value 0)
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 8)
              (.value 0)
            )
            (.node
              (.value 12)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
        )
      )
      (.node
        (.node
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 9)
            )
            (.value 0)
            (.node
              (.value 12)
              (.value 0)
              (.value 0)
            )
          )
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 6)
            )
            (.node
              (.value 0)
              (.value 6)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 12)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 12)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 11)
            )
          )
        )
        (.node
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.node
              (.value 0)
              (.value 2)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.value 0)
            (.node
              (.value 12)
              (.value 0)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 2)
              (.value 0)
            )
            (.node
              (.value 6)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
        )
        (.node
          (.node
            (.node
              (.value 9)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 6)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.value 0)
            (.node
              (.value 11)
              (.value 0)
              (.value 0)
            )
          )
        )
      )
    )
    (.node
      (.node
        (.node
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 5)
            )
            (.node
              (.value 0)
              (.value 6)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 3)
            )
            (.value 0)
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 4)
              (.value 0)
            )
            (.node
              (.value 3)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
        )
        (.node
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.value 0)
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
          )
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.node
              (.value 0)
              (.value 9)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 13)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 10)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 10)
            )
          )
        )
        (.node
          (.node
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
          (.node
            (.node
              (.value 9)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 10)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 9)
            )
          )
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
          )
        )
      )
      (.node
        (.node
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.value 0)
            (.node
              (.value 9)
              (.value 0)
              (.value 0)
            )
          )
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 11)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 12)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 11)
            )
          )
        )
        (.node
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 2)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 5)
            )
            (.value 0)
            (.node
              (.value 6)
              (.value 0)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 4)
              (.value 0)
            )
            (.node
              (.value 5)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
        )
        (.node
          (.node
            (.node
              (.value 10)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 8)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 8)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.value 0)
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
          )
        )
      )
      (.node
        (.node
          (.node
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 9)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
          (.node
            (.node
              (.value 9)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 6)
            )
          )
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
          )
        )
        (.node
          (.node
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 8)
              (.value 0)
            )
            (.node
              (.value 0)
              (.value 0)
              (.value 7)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 8)
              (.value 0)
            )
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 1)
            )
            (.value 0)
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
          )
        )
        (.node
          (.node
            (.value 0)
            (.node
              (.value 0)
              (.value 0)
              (.value 6)
            )
            (.node
              (.value 0)
              (.value 1)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 0)
              (.value 5)
            )
            (.value 0)
            (.node
              (.value 1)
              (.value 0)
              (.value 0)
            )
          )
          (.node
            (.node
              (.value 0)
              (.value 7)
              (.value 0)
            )
            (.node
              (.value 6)
              (.value 0)
              (.value 0)
            )
            (.value 0)
          )
        )
      )
    )
  )
)

def secondCatalogueRank (word : TraceWord 7) : Nat :=
  secondCatalogueRankTree.lookup 0 word.toList

def secondWordOfIndex (index : Nat) : TraceWord 7 :=
  ⟨[symbolOfDigit (index / 729), symbolOfDigit (index / 243),
    symbolOfDigit (index / 81), symbolOfDigit (index / 27),
    symbolOfDigit (index / 9), symbolOfDigit (index / 3),
    symbolOfDigit index], rfl⟩

def secondGramIndex (gram : GramWord 7) : Nat :=
  gram.toList.foldl (fun index step => index * 4 + gramStepDigit step) 0

abbrev ResponsePair := Nat × Nat

/-- Source-indexed targets for the 494 chromogram fibers not discharged by a
global color permutation. -/
def secondCatalogueResponseTree : TernaryTable (List ResponsePair) :=
  (.node
  (.node
    (.node
      (.value [])
      (.node
        (.node
          (.value [])
          (.value [])
          (.node
            (.value [])
            (.value [])
            (.node
              (.value [])
              (.value [])
              (.value [(5195, 95), (5234, 103)])
            )
          )
        )
        (.node
          (.value [])
          (.node
            (.value [])
            (.value [])
            (.node
              (.value [(5165, 159), (5261, 129)])
              (.value [])
              (.value [])
            )
          )
          (.value [])
        )
        (.node
          (.node
            (.value [])
            (.node
              (.value [])
              (.value [(5150, 115), (5330, 143)])
              (.value [])
            )
            (.value [])
          )
          (.value [])
          (.node
            (.node
              (.value [])
              (.value [])
              (.value [(5159, 119), (5318, 145)])
            )
            (.value [])
            (.value [])
          )
        )
      )
      (.node
        (.node
          (.value [])
          (.node
            (.value [])
            (.node
              (.value [])
              (.value [(5195, 95), (5234, 103)])
              (.value [])
            )
            (.value [])
          )
          (.value [])
        )
        (.node
          (.node
            (.value [])
            (.value [])
            (.node
              (.value [])
              (.value [])
              (.value [(5150, 115), (5330, 143)])
            )
          )
          (.node
            (.node
              (.value [])
              (.value [(5159, 119), (5318, 145)])
              (.value [])
            )
            (.value [])
            (.value [])
          )
          (.value [])
        )
        (.node
          (.value [])
          (.value [])
          (.node
            (.value [])
            (.node
              (.value [(5165, 159), (5261, 129)])
              (.value [])
              (.value [])
            )
            (.value [])
          )
        )
      )
    )
    (.node
      (.node
        (.node
          (.value [])
          (.value [])
          (.node
            (.value [])
            (.value [])
            (.node
              (.value [])
              (.value [])
              (.value [(4427, 257), (4466, 265)])
            )
          )
        )
        (.value [])
        (.node
          (.value [])
          (.value [])
          (.node
            (.value [])
            (.value [])
            (.node
              (.value [(4397, 285), (4553, 309)])
              (.value [])
              (.value [])
            )
          )
        )
      )
      (.node
        (.node
          (.value [])
          (.value [])
          (.node
            (.value [])
            (.node
              (.value [(4217, 417), (4685, 339)])
              (.value [])
              (.value [])
            )
            (.value [])
          )
        )
        (.node
          (.value [])
          (.node
            (.value [])
            (.node
              (.value [])
              (.value [])
              (.value [(4139, 485), (4235, 377), (4259, 475), (4619, 377), (4643, 367)])
            )
            (.value [])
          )
          (.value [])
        )
        (.node
          (.node
            (.value [])
            (.node
              (.value [(4313, 435), (4637, 357)])
              (.value [])
              (.value [])
            )
            (.value [])
          )
          (.node
            (.node
              (.value [(4325, 441), (4661, 369)])
              (.value [])
              (.value [])
            )
            (.value [])
            (.value [])
          )
          (.node
            (.value [])
            (.node
              (.value [])
              (.value [])
              (.value [(4139, 485), (4303, 395), (4339, 457), (4622, 373), (4643, 367)])
            )
            (.node
              (.value [])
              (.value [(4142, 481), (4298, 391), (4339, 457), (4619, 377), (4643, 367)])
              (.value [])
            )
          )
        )
      )
      (.node
        (.node
          (.value [])
          (.value [])
          (.node
            (.node
              (.value [])
              (.value [])
              (.value [(4199, 335), (4934, 415)])
            )
            (.value [])
            (.value [])
          )
        )
        (.node
          (.value [])
          (.node
            (.value [])
            (.node
              (.value [])
              (.value [(4142, 481), (4298, 391), (4322, 391), (4874, 457), (4898, 481)])
              (.value [])
            )
            (.node
              (.value [])
              (.value [])
              (.value [(4139, 485), (4303, 395), (4322, 391), (4879, 475), (4898, 481)])
            )
          )
          (.value [])
        )
        (.node
          (.value [])
          (.node
            (.value [])
            (.node
              (.value [])
              (.value [])
              (.value [(4159, 377), (4235, 377), (4259, 475), (4874, 457), (4915, 457)])
            )
            (.value [])
          )
          (.value [])
        )
      )
    )
    (.node
      (.node
        (.node
          (.value [])
          (.node
            (.value [])
            (.node
              (.value [])
              (.value [(4427, 257), (4466, 265)])
              (.value [])
            )
            (.value [])
          )
          (.value [])
        )
        (.node
          (.value [])
          (.node
            (.value [])
            (.node
              (.value [(4397, 285), (4553, 309)])
              (.value [])
              (.value [])
            )
            (.value [])
          )
          (.value [])
        )
        (.value [])
      )
      (.node
        (.node
          (.value [])
          (.node
            (.node
              (.value [])
              (.value [(4199, 335), (4934, 415)])
              (.value [])
            )
            (.value [])
            (.value [])
          )
          (.value [])
        )
        (.node
          (.value [])
          (.value [])
          (.node
            (.value [])
            (.value [])
            (.node
              (.value [])
              (.value [(4159, 377), (4235, 377), (4259, 475), (4874, 457), (4915, 457)])
              (.value [])
            )
          )
        )
        (.node
          (.value [])
          (.value [])
          (.node
            (.value [])
            (.node
              (.value [])
              (.value [(4139, 485), (4303, 395), (4322, 391), (4879, 475), (4898, 481)])
              (.value [])
            )
            (.node
              (.value [])
              (.value [])
              (.value [(4142, 481), (4298, 391), (4322, 391), (4874, 457), (4898, 481)])
            )
          )
        )
      )
      (.node
        (.node
          (.value [])
          (.node
            (.value [])
            (.value [])
            (.node
              (.value [(4217, 417), (4685, 339)])
              (.value [])
              (.value [])
            )
          )
          (.value [])
        )
        (.node
          (.node
            (.value [])
            (.value [])
            (.node
              (.value [(4313, 435), (4637, 357)])
              (.value [])
              (.value [])
            )
          )
          (.node
            (.value [])
            (.node
              (.value [])
              (.value [])
              (.value [(4142, 481), (4298, 391), (4339, 457), (4619, 377), (4643, 367)])
            )
            (.node
              (.value [])
              (.value [(4139, 485), (4303, 395), (4339, 457), (4622, 373), (4643, 367)])
              (.value [])
            )
          )
          (.node
            (.node
              (.value [(4325, 441), (4661, 369)])
              (.value [])
              (.value [])
            )
            (.value [])
            (.value [])
          )
        )
        (.node
          (.value [])
          (.value [])
          (.node
            (.value [])
            (.value [])
            (.node
              (.value [])
              (.value [(4139, 485), (4235, 377), (4259, 475), (4619, 377), (4643, 367)])
              (.value [])
            )
          )
        )
      )
    )
  )
  (.node
    (.node
      (.node
        (.node
          (.value [])
          (.value [])
          (.node
            (.value [])
            (.node
              (.value [])
              (.value [(1358, 745), (1394, 755)])
              (.value [])
            )
            (.value [])
          )
        )
        (.node
          (.value [])
          (.node
            (.node
              (.value [])
              (.value [])
              (.value [(1319, 803), (1415, 775)])
            )
            (.value [])
            (.value [])
          )
          (.value [])
        )
        (.node
          (.node
            (.value [])
            (.value [])
            (.node
              (.value [])
              (.value [])
              (.value [(1307, 761), (1490, 787)])
            )
          )
          (.value [])
          (.node
            (.value [])
            (.value [])
            (.node
              (.value [(1325, 771), (1481, 795)])
              (.value [])
              (.value [])
            )
          )
        )
      )
      (.node
        (.node
          (.node
            (.value [])
            (.node
              (.value [])
              (.value [])
              (.value [(1115, 899), (1619, 817)])
            )
            (.value [])
          )
          (.value [])
          (.value [])
        )
        (.node
          (.value [])
          (.node
            (.value [])
            (.node
              (.value [])
              (.value [])
              (.value [(1067, 971), (1163, 959), (1187, 853), (1547, 863), (1571, 853)])
            )
            (.value [])
          )
          (.value [])
        )
        (.node
          (.value [])
          (.node
            (.node
              (.value [(1253, 927), (1589, 855)])
              (.value [])
              (.value [])
            )
            (.node
              (.value [])
              (.value [(1082, 859), (1226, 931), (1250, 931), (1547, 863), (1586, 859)])
              (.value [])
            )
            (.node
              (.value [])
              (.value [])
              (.value [(1087, 959), (1231, 941), (1250, 931), (1550, 853), (1586, 859)])
            )
          )
          (.node
            (.value [])
            (.node
              (.value [])
              (.value [])
              (.value [(1067, 971), (1231, 941), (1267, 943), (1550, 853), (1571, 853)])
            )
            (.value [])
          )
        )
      )
      (.node
        (.node
          (.value [])
          (.value [])
          (.node
            (.node
              (.value [])
              (.value [])
              (.value [(1127, 821), (1862, 901)])
            )
            (.value [])
            (.value [])
          )
        )
        (.node
          (.node
            (.value [])
            (.node
              (.value [(1241, 867), (1817, 951)])
              (.value [])
              (.value [])
            )
            (.value [])
          )
          (.node
            (.value [])
            (.value [])
            (.node
              (.value [])
              (.value [])
              (.value [(1067, 971), (1231, 941), (1250, 931), (1807, 961), (1826, 931)])
            )
          )
          (.value [])
        )
        (.value [])
      )
    )
    (.node
      (.node
        (.node
          (.node
            (.value [])
            (.node
              (.value [])
              (.value [])
              (.value [(347, 1223), (2387, 979)])
            )
            (.value [])
          )
          (.node
            (.node
              (.value [])
              (.value [])
              (.value [(359, 1235), (2375, 991)])
            )
            (.value [])
            (.node
              (.value [(365, 1239), (2381, 993)])
              (.value [])
              (.value [])
            )
          )
          (.value [])
        )
        (.node
          (.value [])
          (.value [])
          (.node
            (.value [])
            (.value [])
            (.node
              (.value [])
              (.value [])
              (.value [(319, 1283), (395, 1013), (434, 1291), (2315, 1013), (2354, 1021)])
            )
          )
        )
        (.node
          (.value [])
          (.node
            (.value [])
            (.node
              (.value [])
              (.value [(314, 1285), (458, 1051), (482, 1255), (2315, 1013), (2354, 1021)])
              (.value [])
            )
            (.node
              (.value [])
              (.value [])
              (.value [(319, 1283), (463, 1049), (482, 1255), (2318, 1015), (2354, 1021)])
            )
          )
          (.value [])
        )
      )
      (.node
        (.node
          (.value [])
          (.value [])
          (.node
            (.value [])
            (.node
              (.value [])
              (.value [(122, 1393), (590, 1069), (626, 1079), (2126, 1069), (2162, 1079)])
              (.value [])
            )
            (.value [])
          )
        )
        (.node
          (.value [])
          (.node
            (.value [])
            (.value [])
            (.node
              (.value [(173, 1203), (557, 1131), (653, 1101), (2093, 1131), (2189, 1101)])
              (.value [])
              (.value [])
            )
          )
          (.node
            (.node
              (.value [])
              (.value [(182, 1333), (566, 1117), (647, 1423), (2102, 1117), (2183, 1199)])
              (.value [])
            )
            (.value [])
            (.value [])
          )
        )
        (.node
          (.node
            (.value [])
            (.value [])
            (.node
              (.value [])
              (.value [])
              (.value [(223, 1409), (539, 1085), (722, 1439), (2075, 1085), (2258, 1111)])
            )
          )
          (.value [])
          (.node
            (.node
              (.value [])
              (.value [])
              (.value [(247, 1181), (551, 1091), (710, 1117), (2087, 1171), (2246, 1117)])
            )
            (.value [])
            (.value [])
          )
        )
      )
      (.node
        (.node
          (.value [])
          (.node
            (.value [])
            (.value [])
            (.node
              (.value [])
              (.value [])
              (.value [(127, 1079), (847, 1157), (866, 1147), (2126, 1069), (2162, 1079)])
            )
          )
          (.value [])
        )
        (.node
          (.node
            (.node
              (.value [(917, 1323), (2261, 1107)])
              (.value [])
              (.value [])
            )
            (.node
              (.value [])
              (.value [(218, 1357), (794, 1327), (914, 1327), (2075, 1085), (2258, 1111)])
              (.value [])
            )
            (.node
              (.value [])
              (.value [])
              (.value [(223, 1409), (799, 1193), (914, 1327), (2078, 1193), (2258, 1111)])
            )
          )
          (.value [])
          (.value [])
        )
        (.node
          (.node
            (.value [])
            (.value [])
            (.node
              (.value [])
              (.value [(158, 1327), (794, 1327), (979, 1193), (2075, 1085), (2195, 1085)])
              (.value [])
            )
          )
          (.value [])
          (.node
            (.value [])
            (.node
              (.value [(185, 1101), (809, 1173), (973, 1203), (2093, 1131), (2189, 1101)])
              (.value [])
              (.value [])
            )
            (.value [])
          )
        )
      )
    )
    (.node
      (.node
        (.value [])
        (.node
          (.node
            (.value [])
            (.node
              (.value [(473, 1029), (3353, 1275)])
              (.value [])
              (.value [])
            )
            (.value [])
          )
          (.node
            (.value [])
            (.value [])
            (.node
              (.value [])
              (.value [])
              (.value [(299, 1013), (463, 1049), (482, 1255), (3343, 1285), (3362, 1255)])
            )
          )
          (.node
            (.value [])
            (.value [])
            (.node
              (.value [])
              (.value [(314, 1285), (458, 1051), (499, 1051), (3338, 1255), (3379, 1283)])
              (.value [])
            )
          )
        )
        (.value [])
      )
      (.node
        (.node
          (.node
            (.value [])
            (.node
              (.value [(857, 1137), (3161, 1383)])
              (.value [])
              (.value [])
            )
            (.value [])
          )
          (.node
            (.node
              (.value [(869, 1143), (3173, 1395)])
              (.value [])
              (.value [])
            )
            (.value [])
            (.node
              (.value [])
              (.value [])
              (.value [(107, 1067), (847, 1157), (866, 1147), (3151, 1393), (3170, 1403)])
            )
          )
          (.node
            (.value [])
            (.node
              (.value [])
              (.value [])
              (.value [(127, 1079), (847, 1157), (883, 1157), (3151, 1393), (3187, 1391)])
            )
            (.node
              (.value [])
              (.value [(122, 1393), (842, 1159), (883, 1157), (3146, 1391), (3187, 1391)])
              (.value [])
            )
          )
        )
        (.node
          (.value [])
          (.value [])
          (.node
            (.value [])
            (.value [])
            (.node
              (.value [(173, 1203), (829, 1185), (905, 1173), (3133, 1425), (3209, 1443)])
              (.value [])
              (.value [])
            )
          )
        )
        (.node
          (.node
            (.value [])
            (.node
              (.value [])
              (.value [])
              (.value [(223, 1409), (799, 1193), (979, 1193), (3103, 1331), (3283, 1357)])
            )
            (.value [])
          )
          (.node
            (.node
              (.value [])
              (.value [])
              (.value [(247, 1181), (823, 1181), (967, 1369), (3127, 1343), (3271, 1369)])
            )
            (.value [])
            (.node
              (.value [(253, 1131), (829, 1185), (973, 1203), (3133, 1425), (3277, 1425)])
              (.value [])
              (.value [])
            )
          )
          (.node
            (.value [])
            (.node
              (.value [(233, 1119), (809, 1173), (973, 1203), (3113, 1335), (3277, 1425)])
              (.value [])
              (.value [])
            )
            (.value [])
          )
        )
      )
      (.node
        (.node
          (.node
            (.node
              (.value [])
              (.value [])
              (.value [(599, 1055), (3158, 1297)])
            )
            (.value [])
            (.value [])
          )
          (.value [])
          (.node
            (.value [])
            (.node
              (.value [])
              (.value [(110, 1069), (590, 1069), (626, 1079), (3151, 1393), (3170, 1403)])
              (.value [])
            )
            (.value [])
          )
        )
        (.node
          (.value [])
          (.node
            (.node
              (.value [])
              (.value [])
              (.value [(247, 1181), (551, 1091), (647, 1423), (3110, 1333), (3271, 1369)])
            )
            (.value [])
            (.node
              (.value [(253, 1131), (557, 1131), (653, 1101), (3113, 1335), (3277, 1425)])
              (.value [])
              (.value [])
            )
          )
          (.value [])
        )
        (.node
          (.value [])
          (.node
            (.node
              (.value [])
              (.value [(182, 1333), (566, 1117), (710, 1117), (3127, 1343), (3206, 1333)])
              (.value [])
            )
            (.value [])
            (.value [])
          )
          (.node
            (.node
              (.value [])
              (.value [])
              (.value [(167, 1343), (551, 1091), (710, 1117), (3110, 1333), (3206, 1333)])
            )
            (.value [])
            (.value [])
          )
        )
      )
    )
  )
  (.node
    (.node
      (.node
        (.node
          (.value [])
          (.node
            (.value [])
            (.value [])
            (.node
              (.value [])
              (.value [])
              (.value [(1358, 745), (1394, 755)])
            )
          )
          (.value [])
        )
        (.node
          (.node
            (.value [])
            (.node
              (.value [])
              (.value [(1307, 761), (1490, 787)])
              (.value [])
            )
            (.value [])
          )
          (.node
            (.value [])
            (.node
              (.value [(1325, 771), (1481, 795)])
              (.value [])
              (.value [])
            )
            (.value [])
          )
          (.value [])
        )
        (.node
          (.value [])
          (.value [])
          (.node
            (.node
              (.value [])
              (.value [(1319, 803), (1415, 775)])
              (.value [])
            )
            (.value [])
            (.value [])
          )
        )
      )
      (.node
        (.node
          (.value [])
          (.node
            (.node
              (.value [])
              (.value [(1127, 821), (1862, 901)])
              (.value [])
            )
            (.value [])
            (.value [])
          )
          (.value [])
        )
        (.value [])
        (.node
          (.node
            (.value [])
            (.value [])
            (.node
              (.value [(1241, 867), (1817, 951)])
              (.value [])
              (.value [])
            )
          )
          (.value [])
          (.node
            (.value [])
            (.node
              (.value [])
              (.value [(1067, 971), (1231, 941), (1250, 931), (1807, 961), (1826, 931)])
              (.value [])
            )
            (.value [])
          )
        )
      )
      (.node
        (.node
          (.node
            (.value [])
            (.value [])
            (.node
              (.value [])
              (.value [(1115, 899), (1619, 817)])
              (.value [])
            )
          )
          (.value [])
          (.value [])
        )
        (.node
          (.value [])
          (.node
            (.value [])
            (.value [])
            (.node
              (.value [])
              (.value [(1067, 971), (1231, 941), (1267, 943), (1550, 853), (1571, 853)])
              (.value [])
            )
          )
          (.node
            (.node
              (.value [(1253, 927), (1589, 855)])
              (.value [])
              (.value [])
            )
            (.node
              (.value [])
              (.value [(1087, 959), (1231, 941), (1250, 931), (1550, 853), (1586, 859)])
              (.value [])
            )
            (.node
              (.value [])
              (.value [])
              (.value [(1082, 859), (1226, 931), (1250, 931), (1547, 863), (1586, 859)])
            )
          )
        )
        (.node
          (.value [])
          (.value [])
          (.node
            (.value [])
            (.value [])
            (.node
              (.value [])
              (.value [(1067, 971), (1163, 959), (1187, 853), (1547, 863), (1571, 853)])
              (.value [])
            )
          )
        )
      )
    )
    (.node
      (.node
        (.value [])
        (.value [])
        (.node
          (.node
            (.value [])
            (.value [])
            (.node
              (.value [(473, 1029), (3353, 1275)])
              (.value [])
              (.value [])
            )
          )
          (.node
            (.value [])
            (.node
              (.value [])
              (.value [])
              (.value [(314, 1285), (458, 1051), (499, 1051), (3338, 1255), (3379, 1283)])
            )
            (.value [])
          )
          (.node
            (.value [])
            (.node
              (.value [])
              (.value [(299, 1013), (463, 1049), (482, 1255), (3343, 1285), (3362, 1255)])
              (.value [])
            )
            (.value [])
          )
        )
      )
      (.node
        (.node
          (.node
            (.node
              (.value [])
              (.value [(599, 1055), (3158, 1297)])
              (.value [])
            )
            (.value [])
            (.value [])
          )
          (.node
            (.value [])
            (.value [])
            (.node
              (.value [])
              (.value [])
              (.value [(110, 1069), (590, 1069), (626, 1079), (3151, 1393), (3170, 1403)])
            )
          )
          (.value [])
        )
        (.node
          (.value [])
          (.node
            (.node
              (.value [])
              (.value [(167, 1343), (551, 1091), (710, 1117), (3110, 1333), (3206, 1333)])
              (.value [])
            )
            (.value [])
            (.value [])
          )
          (.node
            (.node
              (.value [])
              (.value [])
              (.value [(182, 1333), (566, 1117), (710, 1117), (3127, 1343), (3206, 1333)])
            )
            (.value [])
            (.value [])
          )
        )
        (.node
          (.value [])
          (.value [])
          (.node
            (.node
              (.value [])
              (.value [(247, 1181), (551, 1091), (647, 1423), (3110, 1333), (3271, 1369)])
              (.value [])
            )
            (.node
              (.value [(253, 1131), (557, 1131), (653, 1101), (3113, 1335), (3277, 1425)])
              (.value [])
              (.value [])
            )
            (.value [])
          )
        )
      )
      (.node
        (.node
          (.node
            (.value [])
            (.value [])
            (.node
              (.value [(857, 1137), (3161, 1383)])
              (.value [])
              (.value [])
            )
          )
          (.node
            (.value [])
            (.node
              (.value [])
              (.value [])
              (.value [(122, 1393), (842, 1159), (883, 1157), (3146, 1391), (3187, 1391)])
            )
            (.node
              (.value [])
              (.value [(127, 1079), (847, 1157), (883, 1157), (3151, 1393), (3187, 1391)])
              (.value [])
            )
          )
          (.node
            (.node
              (.value [(869, 1143), (3173, 1395)])
              (.value [])
              (.value [])
            )
            (.node
              (.value [])
              (.value [(107, 1067), (847, 1157), (866, 1147), (3151, 1393), (3170, 1403)])
              (.value [])
            )
            (.value [])
          )
        )
        (.node
          (.node
            (.value [])
            (.value [])
            (.node
              (.value [])
              (.value [(223, 1409), (799, 1193), (979, 1193), (3103, 1331), (3283, 1357)])
              (.value [])
            )
          )
          (.node
            (.value [])
            (.value [])
            (.node
              (.value [(233, 1119), (809, 1173), (973, 1203), (3113, 1335), (3277, 1425)])
              (.value [])
              (.value [])
            )
          )
          (.node
            (.node
              (.value [])
              (.value [(247, 1181), (823, 1181), (967, 1369), (3127, 1343), (3271, 1369)])
              (.value [])
            )
            (.node
              (.value [(253, 1131), (829, 1185), (973, 1203), (3133, 1425), (3277, 1425)])
              (.value [])
              (.value [])
            )
            (.value [])
          )
        )
        (.node
          (.value [])
          (.node
            (.value [])
            (.node
              (.value [(173, 1203), (829, 1185), (905, 1173), (3133, 1425), (3209, 1443)])
              (.value [])
              (.value [])
            )
            (.value [])
          )
          (.value [])
        )
      )
    )
    (.node
      (.node
        (.node
          (.node
            (.value [])
            (.value [])
            (.node
              (.value [])
              (.value [(347, 1223), (2387, 979)])
              (.value [])
            )
          )
          (.value [])
          (.node
            (.node
              (.value [])
              (.value [(359, 1235), (2375, 991)])
              (.value [])
            )
            (.node
              (.value [(365, 1239), (2381, 993)])
              (.value [])
              (.value [])
            )
            (.value [])
          )
        )
        (.node
          (.value [])
          (.value [])
          (.node
            (.value [])
            (.node
              (.value [])
              (.value [(319, 1283), (463, 1049), (482, 1255), (2318, 1015), (2354, 1021)])
              (.value [])
            )
            (.node
              (.value [])
              (.value [])
              (.value [(314, 1285), (458, 1051), (482, 1255), (2315, 1013), (2354, 1021)])
            )
          )
        )
        (.node
          (.value [])
          (.node
            (.value [])
            (.node
              (.value [])
              (.value [(319, 1283), (395, 1013), (434, 1291), (2315, 1013), (2354, 1021)])
              (.value [])
            )
            (.value [])
          )
          (.value [])
        )
      )
      (.node
        (.node
          (.value [])
          (.value [])
          (.node
            (.value [])
            (.node
              (.value [])
              (.value [(127, 1079), (847, 1157), (866, 1147), (2126, 1069), (2162, 1079)])
              (.value [])
            )
            (.value [])
          )
        )
        (.node
          (.node
            (.value [])
            (.node
              (.value [])
              (.value [])
              (.value [(158, 1327), (794, 1327), (979, 1193), (2075, 1085), (2195, 1085)])
            )
            (.value [])
          )
          (.node
            (.value [])
            (.value [])
            (.node
              (.value [(185, 1101), (809, 1173), (973, 1203), (2093, 1131), (2189, 1101)])
              (.value [])
              (.value [])
            )
          )
          (.value [])
        )
        (.node
          (.node
            (.node
              (.value [(917, 1323), (2261, 1107)])
              (.value [])
              (.value [])
            )
            (.node
              (.value [])
              (.value [(223, 1409), (799, 1193), (914, 1327), (2078, 1193), (2258, 1111)])
              (.value [])
            )
            (.node
              (.value [])
              (.value [])
              (.value [(218, 1357), (794, 1327), (914, 1327), (2075, 1085), (2258, 1111)])
            )
          )
          (.value [])
          (.value [])
        )
      )
      (.node
        (.node
          (.value [])
          (.node
            (.value [])
            (.value [])
            (.node
              (.value [])
              (.value [])
              (.value [(122, 1393), (590, 1069), (626, 1079), (2126, 1069), (2162, 1079)])
            )
          )
          (.value [])
        )
        (.node
          (.node
            (.value [])
            (.node
              (.value [])
              (.value [(223, 1409), (539, 1085), (722, 1439), (2075, 1085), (2258, 1111)])
              (.value [])
            )
            (.value [])
          )
          (.node
            (.node
              (.value [])
              (.value [(247, 1181), (551, 1091), (710, 1117), (2087, 1171), (2246, 1117)])
              (.value [])
            )
            (.value [])
            (.value [])
          )
          (.value [])
        )
        (.node
          (.value [])
          (.node
            (.node
              (.value [])
              (.value [])
              (.value [(182, 1333), (566, 1117), (647, 1423), (2102, 1117), (2183, 1199)])
            )
            (.value [])
            (.value [])
          )
          (.node
            (.value [])
            (.node
              (.value [(173, 1203), (557, 1131), (653, 1101), (2093, 1131), (2189, 1101)])
              (.value [])
              (.value [])
            )
            (.value [])
          )
        )
      )
    )
  )
)

def secondResponseTarget (source : TraceWord 7) (gram : Nat) : Nat :=
  match secondCatalogueResponseTree.lookup [] source.toList |>.find? fun entry =>
      entry.1 == gram with
  | some entry => entry.2
  | none => 0

def secondLowerPermutation (word : TraceWord 7) : Option PermutationCode :=
  permutationCodes.find? fun permutation =>
    decide (secondCatalogueRank (permute permutation word) <
      secondCatalogueRank word)

def secondLowerResponse (word : TraceWord 7) (gram : GramWord 7) :
    TraceWord 7 :=
  secondWordOfIndex
    (secondResponseTarget word (secondGramIndex gram))

def secondCatalogueRule (word : TraceWord 7) : RuleCode 7 :=
  if word ∈ secondCatalogueWitnessCertificate.words then .member
  else
    match secondLowerPermutation word with
    | some permutation => .permutation permutation
    | none => .chromograms (secondLowerResponse word)

/-- Ternary trace tree that accepts exactly the words whose accumulated
`𝔽₂²` sum is zero after the prescribed number of symbols. -/
def zeroSumTraceTree : Nat → Color → TraceTree
  | 0, total => if total = 0 then .leaf else .empty
  | length + 1, total =>
      .node
        (zeroSumTraceTree length (total + FourColor.red))
        (zeroSumTraceTree length (total + FourColor.blue))
        (zeroSumTraceTree length (total + FourColor.purple))

theorem zeroSumTraceTree_accepts (word : List TraceSymbol) (total : Color) :
    (zeroSumTraceTree word.length total).accepts word = true ↔
      total + (word.map TraceSymbol.toColor).sum = 0 := by
  induction word generalizing total with
  | nil =>
      by_cases htotal : total = 0 <;>
        simp [zeroSumTraceTree, TraceTree.accepts, htotal]
  | cons symbol word ih =>
      cases symbol <;>
        simp [zeroSumTraceTree, TraceTree.accepts, TraceTree.child,
          ih, add_assoc]

def secondEvenTraceTree : TraceTree :=
  zeroSumTraceTree 7 0

def secondEvenTraceWordList : List (TraceWord 7) :=
  acceptedWords 7 secondEvenTraceTree

@[simp] theorem mem_secondEvenTraceWordList (word : TraceWord 7) :
    word ∈ secondEvenTraceWordList ↔ IsEvenTraceWord word := by
  change word ∈ acceptedWords 7 secondEvenTraceTree ↔ IsEvenTraceWord word
  rw [mem_acceptedWords_iff]
  simpa [secondEvenTraceTree, IsEvenTraceWord, word.2] using
    zeroSumTraceTree_accepts word.toList 0

def secondExtendableWordList : List (TraceWord 7) :=
  secondCatalogueWitnessCertificate.witnesses.map Witness.word

/-- Constructor-normal trie of the 39 witnessed extendable words. -/
def secondExtendableTraceTree : TraceTree :=
  (.node
  (.node
    (.node
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
      .empty
    )
    (.node
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
            .empty
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
              .leaf
              .empty
              .empty
            )
            .empty
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
        )
      )
    )
    .empty
  )
  .empty
  .empty
)

theorem acceptedWords_secondExtendableTraceTree :
    acceptedWords 7 secondExtendableTraceTree = secondExtendableWordList := by
  rfl

/-- A tree-indexed ranked certificate for every zero-sum seven-symbol trace. -/
def secondCatalogueTreeKempeCertificate :
    ClassicalCertificateTreeRankedKempe.Certificate 7 where
  covered := secondEvenTraceTree
  extendable := secondExtendableTraceTree
  rank := secondCatalogueRank
  rule := secondCatalogueRule

/-- Thirteen bounded blocks cover the 546 zero-sum seven-symbol words. -/
def secondCatalogueWordChunk (index : Nat) : List (TraceWord 7) :=
  secondEvenTraceWordList.drop (index * 42) |>.take 42

def secondCatalogueChunkedWords : List (TraceWord 7) :=
  secondCatalogueWordChunk 0 ++ secondCatalogueWordChunk 1 ++
    secondCatalogueWordChunk 2 ++ secondCatalogueWordChunk 3 ++
    secondCatalogueWordChunk 4 ++ secondCatalogueWordChunk 5 ++
    secondCatalogueWordChunk 6 ++ secondCatalogueWordChunk 7 ++
    secondCatalogueWordChunk 8 ++ secondCatalogueWordChunk 9 ++
    secondCatalogueWordChunk 10 ++ secondCatalogueWordChunk 11 ++
    secondCatalogueWordChunk 12

set_option maxRecDepth 100000 in
theorem secondCatalogueChunkedWords_eq :
    secondCatalogueChunkedWords = secondEvenTraceWordList := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem secondCatalogueWordChunk_zero_checker :
    (secondCatalogueWordChunk 0).all
      secondCatalogueTreeKempeCertificate.ruleBoolean = true := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem secondCatalogueWordChunk_one_checker :
    (secondCatalogueWordChunk 1).all
      secondCatalogueTreeKempeCertificate.ruleBoolean = true := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem secondCatalogueWordChunk_two_checker :
    (secondCatalogueWordChunk 2).all
      secondCatalogueTreeKempeCertificate.ruleBoolean = true := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem secondCatalogueWordChunk_three_checker :
    (secondCatalogueWordChunk 3).all
      secondCatalogueTreeKempeCertificate.ruleBoolean = true := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem secondCatalogueWordChunk_four_checker :
    (secondCatalogueWordChunk 4).all
      secondCatalogueTreeKempeCertificate.ruleBoolean = true := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem secondCatalogueWordChunk_five_checker :
    (secondCatalogueWordChunk 5).all
      secondCatalogueTreeKempeCertificate.ruleBoolean = true := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem secondCatalogueWordChunk_six_checker :
    (secondCatalogueWordChunk 6).all
      secondCatalogueTreeKempeCertificate.ruleBoolean = true := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem secondCatalogueWordChunk_seven_checker :
    (secondCatalogueWordChunk 7).all
      secondCatalogueTreeKempeCertificate.ruleBoolean = true := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem secondCatalogueWordChunk_eight_checker :
    (secondCatalogueWordChunk 8).all
      secondCatalogueTreeKempeCertificate.ruleBoolean = true := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem secondCatalogueWordChunk_nine_checker :
    (secondCatalogueWordChunk 9).all
      secondCatalogueTreeKempeCertificate.ruleBoolean = true := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem secondCatalogueWordChunk_ten_checker :
    (secondCatalogueWordChunk 10).all
      secondCatalogueTreeKempeCertificate.ruleBoolean = true := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem secondCatalogueWordChunk_eleven_checker :
    (secondCatalogueWordChunk 11).all
      secondCatalogueTreeKempeCertificate.ruleBoolean = true := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem secondCatalogueWordChunk_twelve_checker :
    (secondCatalogueWordChunk 12).all
      secondCatalogueTreeKempeCertificate.ruleBoolean = true := by
  rfl

theorem secondCatalogueRuleChecker :
    secondEvenTraceWordList.all
      secondCatalogueTreeKempeCertificate.ruleBoolean = true := by
  rw [← secondCatalogueChunkedWords_eq]
  simp only [secondCatalogueChunkedWords, List.all_append,
    secondCatalogueWordChunk_zero_checker,
    secondCatalogueWordChunk_one_checker,
    secondCatalogueWordChunk_two_checker,
    secondCatalogueWordChunk_three_checker,
    secondCatalogueWordChunk_four_checker,
    secondCatalogueWordChunk_five_checker,
    secondCatalogueWordChunk_six_checker,
    secondCatalogueWordChunk_seven_checker,
    secondCatalogueWordChunk_eight_checker,
    secondCatalogueWordChunk_nine_checker,
    secondCatalogueWordChunk_ten_checker,
    secondCatalogueWordChunk_eleven_checker,
    secondCatalogueWordChunk_twelve_checker, Bool.and_self]

theorem secondCatalogueTreeKempeCertificate_valid :
    secondCatalogueTreeKempeCertificate.Valid := by
  intro word hcovered
  apply secondCatalogueTreeKempeCertificate.ruleValid_of_ruleBoolean_eq_true word
  apply (List.all_eq_true.mp secondCatalogueRuleChecker) word
  apply (mem_acceptedWords_iff secondEvenTraceTree word).2
  simpa [secondCatalogueTreeKempeCertificate] using hcovered

theorem secondCatalogueTreeKempeCertificate_checker :
    secondCatalogueTreeKempeCertificate.checker = true :=
  secondCatalogueTreeKempeCertificate.checker_eq_true_of_valid
    secondCatalogueTreeKempeCertificate_valid

theorem secondCatalogueTree_evenTrace_kempeCoclosure
    (word : TraceWord 7) (heven : IsEvenTraceWord word) :
    KempeCoclosure
      secondCatalogueTreeKempeCertificate.ExtendableFamily word.toList := by
  apply secondCatalogueTreeKempeCertificate.kempeCoclosure_of_checker_true
    secondCatalogueTreeKempeCertificate_checker word
  change secondEvenTraceTree.accepts word.toList = true
  apply (mem_acceptedWords_iff secondEvenTraceTree word).1
  exact (mem_secondEvenTraceWordList word).2 heven

/-- Standard semantic family of boundary traces induced by ordinary
colorings of `cf002`. -/
def SecondCatalogueExtendableTrace (word : List TraceSymbol) : Prop :=
  FiniteHypermap.RingTrace
    (checkedHypermap secondCataloguePartitionValid) secondCatalogueRing
      (word.map TraceSymbol.toColor)

theorem secondCatalogue_extendableFamily_sound
    (word : List TraceSymbol)
    (hextendable :
      secondCatalogueTreeKempeCertificate.ExtendableFamily word) :
    SecondCatalogueExtendableTrace word := by
  rcases hextendable with ⟨fixedWord, hfixed, haccepted⟩
  have hmemAccepted : fixedWord ∈
      acceptedWords 7 secondExtendableTraceTree :=
    (mem_acceptedWords_iff secondExtendableTraceTree fixedWord).2 (by
      simpa [secondCatalogueTreeKempeCertificate] using haccepted)
  have hmemList : fixedWord ∈ secondExtendableWordList := by
    simpa [acceptedWords_secondExtendableTraceTree] using hmemAccepted
  have hmem : fixedWord ∈ secondCatalogueWitnessCertificate.words := by
    simpa [secondExtendableWordList, Certificate.words] using hmemList
  subst word
  obtain ⟨assignment, hproper, htrace⟩ :=
    secondCatalogue_witnessWord_is_ringTrace fixedWord hmem
  exact (ringTrace_iff_exists_assignment secondCataloguePartitionValid
    secondCatalogueRing _).2 ⟨assignment, hproper, htrace⟩

/-- Every contracted `cf002` boundary trace lies in the Kempe co-closure of
a genuine ordinary boundary trace. -/
theorem secondCatalogue_contractTrace_kempeCoclosure
    (word : List TraceSymbol)
    (hcontract : FiniteHypermap.ContractRingTrace
      (checkedHypermap secondCataloguePartitionValid) secondCatalogueContract
        secondCatalogueRing (word.map TraceSymbol.toColor)) :
    KempeCoclosure SecondCatalogueExtendableTrace word := by
  obtain ⟨assignment, hassignment, htrace⟩ :=
    (contractRingTrace_iff_exists_assignment secondCataloguePartitionValid
      secondCatalogueContract secondCatalogueRing _).1 hcontract
  have hlength : word.length = 7 := by
    calc
      word.length = (word.map TraceSymbol.toColor).length := by simp
      _ = (ringTraceOfAssignment secondCataloguePartitionValid
          secondCatalogueRing assignment).length :=
        congrArg List.length htrace
      _ = 7 := by
        simp [ringTraceOfAssignment, FiniteHypermap.ringColorWord,
          length_trace, secondCatalogueRing]
  let fixedWord : TraceWord 7 := ⟨word, hlength⟩
  have heven : IsEvenTraceWord fixedWord := by
    unfold IsEvenTraceWord
    change (word.map TraceSymbol.toColor).sum = 0
    rw [htrace]
    exact sum_trace _
  have hcoclosure :=
    secondCatalogueTree_evenTrace_kempeCoclosure fixedWord heven
  exact hcoclosure.mono secondCatalogue_extendableFamily_sound

/-- Color-valued reducibility theorem for the second classical catalogue
configuration. -/
theorem secondCatalogue_contractRingTrace_reduces
    (boundaryTrace : List Color)
    (hcontract : FiniteHypermap.ContractRingTrace
      (checkedHypermap secondCataloguePartitionValid) secondCatalogueContract
        secondCatalogueRing boundaryTrace) :
    ∃ symbols : List TraceSymbol,
      symbols.map TraceSymbol.toColor = boundaryTrace ∧
        KempeCoclosure SecondCatalogueExtendableTrace symbols := by
  obtain ⟨assignment, hassignment, htrace⟩ :=
    (contractRingTrace_iff_exists_assignment secondCataloguePartitionValid
      secondCatalogueContract secondCatalogueRing boundaryTrace).1 hcontract
  obtain ⟨symbols, hsymbols, _⟩ :=
    secondCatalogue_contractAssignment_trace_symbols assignment hassignment
  have hsymbolsBoundary :
      symbols.map TraceSymbol.toColor = boundaryTrace :=
    hsymbols.trans htrace.symm
  refine ⟨symbols, hsymbolsBoundary, ?_⟩
  apply secondCatalogue_contractTrace_kempeCoclosure
  simpa [hsymbolsBoundary] using hcontract

end ClassicalCertificateCatalogueTwo

end Mettapedia.GraphTheory.FourColor
