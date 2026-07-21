import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadata
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueFourExactTraceBase
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceChunk00

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueFourReductionMetadata

open ClassicalCertificateCatalogueFour
open ClassicalCertificateCatalogueFourExactTrace
open ClassicalCertificateCatalogueHypermaps
open ClassicalCertificateCataloguePrograms
open ClassicalCertificateConfigurationProvenance
open ClassicalCertificateReductionMetadata

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

/-- Complete checked reduction metadata for catalogue configuration `cf004`. -/
def fourthCatalogueReductionCode :
    ClassicalCertificateReductionMetadata.Code where
  hypermap := fourthCatalogueSampleCode
  ringValues := [6, 11, 26, 31, 16, 21, 0, 5]
  contractValues := [12, 25, 32, 39]
  partition := fourthCatalogueFacePartition
  components := fourthCatalogueComponents
  orderValues := [1, 4, 2, 3, 5, 6, 0, 7]

theorem fourthCatalogue_materialized_eq :
    materialized fourthCatalogueSample = fourthCatalogueSampleCode := by
  calc
    materialized fourthCatalogueSample =
        classicalHypermapChunk00[3].hypermap := by
      exact materialize_eq_of_entryBoolean_true 3
        classicalConfigurationProvenance_cf004 fourthCatalogueSample (by rfl)
          classicalHypermapChunk00[3] (by rfl)
    _ = fourthCatalogueSampleCode := by rfl

theorem fourthCatalogueReductionCode_checker :
    ClassicalCertificateReductionMetadata.checker
      fourthCatalogueReductionCode = true := by
  rfl

def fourthCatalogueReductionValid :
    ClassicalCertificateReductionMetadata.Valid fourthCatalogueReductionCode :=
  ClassicalCertificateReductionMetadata.valid_of_checker_true
    fourthCatalogueReductionCode
      fourthCatalogueReductionCode_checker

theorem fourthCatalogueReduction_ringValues_eq_compile :
    fourthCatalogueReductionCode.ringValues =
      fourthCatalogueSample.compile.forwardRing := by
  rfl

theorem fourthCatalogueReduction_contractValues_eq_compile :
    fourthCatalogueReductionCode.contractValues =
      fourthCatalogueSample.contractDarts := by
  rfl

def fourthCatalogueReductionLink :
    ClassicalCertificateReductionMetadata.ProgramLink fourthCatalogueSample
      fourthCatalogueReductionCode where
  hypermap_eq := fourthCatalogue_materialized_eq
  ringValues_eq := fourthCatalogueReduction_ringValues_eq_compile
  contractValues_eq := fourthCatalogueReduction_contractValues_eq_compile

def fourthCatalogueReductionCertified :
    ClassicalCertificateReductionMetadata.Certified fourthCatalogueSample
      fourthCatalogueReductionCode where
  valid := fourthCatalogueReductionValid
  link := fourthCatalogueReductionLink

theorem fourthCatalogueReduction_ring_eq :
    ring fourthCatalogueReductionCode = fourthCatalogueRing := by
  rfl

theorem fourthCatalogueReduction_contract_eq :
    contract fourthCatalogueReductionCode = fourthCatalogueContract := by
  rfl

theorem fourthCatalogueReduction_order_eq :
    order fourthCatalogueReductionCode =
      fourthCatalogueExactTraceFirst ::
        fourthCatalogueExactTraceRemaining := by
  rfl

/-- The generic exact enumerator instantiated solely from the checked `cf004`
metadata. -/
theorem fourthCatalogueReduction_enumerate_accepts_iff_contractRingTrace
    (word : List ClassicalCertificateTraceTree.TraceSymbol) :
    (ClassicalCertificateExactTraceEnumeration.enumerate
      (ClassicalCertificateReductionMetadata.Valid.componentsValid
        fourthCatalogueReductionValid)
      (ring fourthCatalogueReductionCode)
        (order fourthCatalogueReductionCode)).accepts word = true ↔
      ClassicalCertificateHypermapColoring.FiniteHypermap.ContractRingTrace
        (ClassicalCertificateFacePartition.checkedHypermap
          (ClassicalCertificateReductionMetadata.Valid.partitionValid
            fourthCatalogueReductionValid))
        (contract fourthCatalogueReductionCode)
          (ring fourthCatalogueReductionCode)
          (word.map ClassicalCertificateTraceTree.TraceSymbol.toColor) := by
  exact
    ClassicalCertificateReductionMetadata.Valid.enumerate_accepts_iff_contractRingTrace
      fourthCatalogueReductionValid word

end ClassicalCertificateCatalogueFourReductionMetadata

end Mettapedia.GraphTheory.FourColor
