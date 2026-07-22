import Mettapedia.GraphTheory.FourColor.ClassicalCertificateIndexedLayeredKempe
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateIndexedTraceWitness

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateOrbitBaseWitness

open ClassicalCertificateConfiguration
open ClassicalCertificateFacePartition
open ClassicalCertificateHypermap
open ClassicalCertificateHypermapColoring
open ClassicalCertificateIndexedLayeredKempe
open ClassicalCertificateIndexedTraceWitness
open ClassicalCertificateTraceTree

variable {hypermap : HypermapCode}
variable {partition : ClassicalCertificateFacePartition.Code}
variable {traceLength : Nat}

/-- A checked witness map turns the abstract base language of an indexed
Kempe certificate into genuine ordinary boundary traces. -/
theorem extendableFamily_subset_ringTrace
    (valid : ClassicalCertificateFacePartition.Valid hypermap partition)
    (ring : List.Vector (Fin hypermap.dartCount) traceLength)
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate
      traceLength)
    (witnesses : ClassicalCertificateIndexedTraceWitness.Certificate
      partition.faceCount traceLength)
    (htable : witnesses.witnessTableBoolean valid ring = true)
    (hmap : witnesses.mapBoolean = true)
    (hcoverage : witnesses.coversDagBoolean certificate.traceCode
      certificate.extendableRoot = true)
    (word : List TraceSymbol)
    (hextendable : certificate.ExtendableFamily word) :
    FiniteHypermap.RingTrace (checkedHypermap valid) ring.toList
      (word.map TraceSymbol.toColor) := by
  obtain ⟨fixedWord, rfl, haccepted⟩ := hextendable
  obtain ⟨assignment, hproper, htrace⟩ :=
    witnesses.exists_properAssignment_of_dag_accepts valid ring
      certificate.traceCode certificate.extendableRoot htable hmap hcoverage
        fixedWord (by
          simpa [ClassicalCertificateIndexedLayeredKempe.Certificate.acceptsExtendable]
            using haccepted)
  exact (ringTrace_iff_exists_assignment valid ring.toList _).2
    ⟨assignment, hproper, htrace⟩

end ClassicalCertificateOrbitBaseWitness

end Mettapedia.GraphTheory.FourColor
