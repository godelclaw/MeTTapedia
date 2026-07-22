import Mettapedia.GraphTheory.FourColor.ClassicalCertificateExactTraceEnumeration

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateOrdinaryTraceEnumeration

open ClassicalCertificateConfiguration
open ClassicalCertificateContractComponents
open ClassicalCertificateExactTraceEnumeration
open ClassicalCertificateFacePartition
open ClassicalCertificateHypermapColoring
open ClassicalCertificateTraceTree

variable {hypermap : HypermapCode}
  {partition : ClassicalCertificateFacePartition.Code}

/-- With no contracted edges, every face class is its own contract
component.  The otherwise unused link table is populated by the already
checked face representatives. -/
def singletonComponents
    (partitionValid : ClassicalCertificateFacePartition.Valid
      hypermap partition) : ClassicalCertificateContractComponents.Code where
  componentCount := partition.faceCount
  componentOfFace := Array.ofFn fun face : Fin partition.faceCount => face.val
  representative := Array.ofFn fun face : Fin partition.faceCount => face.val
  parent := Array.ofFn fun face : Fin partition.faceCount => face.val
  linkDart := partition.representative
  depth := Array.ofFn fun _ : Fin partition.faceCount => 0

/-- The singleton component quotient is valid for the empty contract. -/
def singletonComponentsValid
    (partitionValid : ClassicalCertificateFacePartition.Valid
      hypermap partition) :
    ClassicalCertificateContractComponents.Valid partitionValid ∅
      (singletonComponents partitionValid) where
  componentOfFaceSize := by simp [singletonComponents]
  representativeSize := by simp [singletonComponents]
  parentSize := by simp [singletonComponents]
  linkDartSize := by
    simpa [singletonComponents] using partitionValid.representativeSize
  depthSize := by simp [singletonComponents]
  componentInRange := by
    intro face
    simpa [singletonComponents,
      ClassicalCertificateContractComponents.Code.componentAt,
      HypermapCode.lookup] using face.isLt
  representativeInRange := by
    intro component
    simpa [singletonComponents,
      ClassicalCertificateContractComponents.Code.representativeAt,
      HypermapCode.lookup] using component.isLt
  parentInRange := by
    intro face
    simpa [singletonComponents,
      ClassicalCertificateContractComponents.Code.parentAt,
      HypermapCode.lookup] using face.isLt
  linkDartInRange := by
    intro face
    simpa [singletonComponents,
      ClassicalCertificateContractComponents.Code.linkDartAt,
      ClassicalCertificateFacePartition.Code.representativeAt] using
        partitionValid.representativeInRange face
  representativeComponent := by
    intro component
    simp [singletonComponents,
      ClassicalCertificateContractComponents.Code.componentAt,
      ClassicalCertificateContractComponents.Code.representativeAt,
      HypermapCode.lookup]
  rootOrLink := by
    intro face
    left
    simp [singletonComponents,
      ClassicalCertificateContractComponents.Code.componentAt,
      ClassicalCertificateContractComponents.Code.representativeAt,
      HypermapCode.lookup]

/-- Canonical exhaustive order of the singleton face components. -/
def singletonOrder (partition : ClassicalCertificateFacePartition.Code) :
    List (Fin partition.faceCount) :=
  List.ofFn fun face : Fin partition.faceCount => face

theorem mem_singletonOrder
    (face : Fin partition.faceCount) : face ∈ singletonOrder partition := by
  simp [singletonOrder]

/-- Exact ordinary boundary language, obtained by specializing the contract
enumerator to the empty contract. -/
def enumerate
    (partitionValid : ClassicalCertificateFacePartition.Valid
      hypermap partition)
    (ring : List (Fin hypermap.dartCount)) : TraceTree :=
  ClassicalCertificateExactTraceEnumeration.enumerate
    (singletonComponentsValid partitionValid) ring (singletonOrder partition)

/-- The reflected ordinary-language enumerator is exactly the standard
face-coloring boundary-trace predicate. -/
theorem enumerate_accepts_iff_ringTrace
    (partitionValid : ClassicalCertificateFacePartition.Valid
      hypermap partition)
    (ring : List (Fin hypermap.dartCount))
    (hcycle : RawReverseBoundaryCycle hypermap ring)
    (word : List TraceSymbol) :
    (enumerate partitionValid ring).accepts word = true ↔
      FiniteHypermap.RingTrace (checkedHypermap partitionValid) ring
        (word.map TraceSymbol.toColor) := by
  rw [FiniteHypermap.ringTrace_iff_contractRingTrace_empty]
  exact
    ClassicalCertificateExactTraceEnumeration.enumerate_accepts_iff_contractRingTrace
      (singletonComponentsValid partitionValid) ring
        (singletonOrder partition) mem_singletonOrder hcycle (by
          simp [ContractAvoidsBoundary, InRawContract]) word

end ClassicalCertificateOrdinaryTraceEnumeration

end Mettapedia.GraphTheory.FourColor
