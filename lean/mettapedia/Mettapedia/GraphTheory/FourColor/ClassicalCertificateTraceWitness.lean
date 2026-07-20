import Mettapedia.GraphTheory.FourColor.ClassicalCertificateFacePartition
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateRankedKempe

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateTraceWitness

open ClassicalCertificateFacePartition
open ClassicalCertificateConfiguration
open ClassicalCertificateTraceTree
open ClassicalCertificateRankedKempe

/-- Compact four-value syntax for face-color assignments. -/
inductive FaceColorCode where
  | zero
  | red
  | blue
  | purple
  deriving DecidableEq, Fintype, Repr

namespace FaceColorCode

def toColor : FaceColorCode → Color
  | .zero => 0
  | .red => FourColor.red
  | .blue => FourColor.blue
  | .purple => FourColor.purple

end FaceColorCode

/-- One ordinary-coloring witness for a normalized boundary trace. -/
structure Witness (faceCount traceLength : Nat) where
  colors : List.Vector FaceColorCode faceCount
  word : TraceWord traceLength
  deriving DecidableEq

namespace Witness

def assignment {faceCount traceLength : Nat}
    (witness : Witness faceCount traceLength) : Fin faceCount → Color :=
  fun face => (witness.colors.get face).toColor

def Valid {hypermap : ClassicalCertificateConfiguration.HypermapCode}
    {partition : Code} {traceLength : Nat}
    (valid : ClassicalCertificateFacePartition.Valid hypermap partition)
    (ring : List.Vector (Fin hypermap.dartCount) traceLength)
    (witness : Witness partition.faceCount traceLength) : Prop :=
  IsProperAssignment valid witness.assignment ∧
    witness.word.toList.map TraceSymbol.toColor =
      ringTraceOfAssignment valid ring.toList witness.assignment

instance {hypermap : ClassicalCertificateConfiguration.HypermapCode}
    {partition : Code} {traceLength : Nat}
    (valid : ClassicalCertificateFacePartition.Valid hypermap partition)
    (ring : List.Vector (Fin hypermap.dartCount) traceLength)
    (witness : Witness partition.faceCount traceLength) :
    Decidable (witness.Valid valid ring) := by
  unfold Valid
  infer_instance

end Witness

/-- A finite family of witnessed extendable traces. -/
structure Certificate (faceCount traceLength : Nat) where
  witnesses : List (Witness faceCount traceLength)
  deriving DecidableEq

namespace Certificate

def words {faceCount traceLength : Nat}
    (certificate : Certificate faceCount traceLength) :
    Finset (TraceWord traceLength) :=
  (certificate.witnesses.map Witness.word).toFinset

def Valid {hypermap : ClassicalCertificateConfiguration.HypermapCode}
    {partition : Code} {traceLength : Nat}
    (valid : ClassicalCertificateFacePartition.Valid hypermap partition)
    (ring : List.Vector (Fin hypermap.dartCount) traceLength)
    (certificate : Certificate partition.faceCount traceLength) : Prop :=
  ∀ witness ∈ certificate.witnesses, witness.Valid valid ring

instance {hypermap : ClassicalCertificateConfiguration.HypermapCode}
    {partition : Code} {traceLength : Nat}
    (valid : ClassicalCertificateFacePartition.Valid hypermap partition)
    (ring : List.Vector (Fin hypermap.dartCount) traceLength)
    (certificate : Certificate partition.faceCount traceLength) :
    Decidable (certificate.Valid valid ring) := by
  unfold Valid
  infer_instance

def checker {hypermap : ClassicalCertificateConfiguration.HypermapCode}
    {partition : Code} {traceLength : Nat}
    (valid : ClassicalCertificateFacePartition.Valid hypermap partition)
    (ring : List.Vector (Fin hypermap.dartCount) traceLength)
    (certificate : Certificate partition.faceCount traceLength) : Bool :=
  decide (certificate.Valid valid ring)

theorem valid_of_checker_true
    {hypermap : ClassicalCertificateConfiguration.HypermapCode}
    {partition : Code} {traceLength : Nat}
    (valid : ClassicalCertificateFacePartition.Valid hypermap partition)
    (ring : List.Vector (Fin hypermap.dartCount) traceLength)
    (certificate : Certificate partition.faceCount traceLength)
    (haccepted : certificate.checker valid ring = true) :
    certificate.Valid valid ring := by
  exact Bool.of_decide_true (by simpa [checker] using haccepted)

/-- Every word exported by an accepted witness certificate is induced by a
genuine proper face-class assignment. -/
theorem exists_properAssignment_of_mem_words
    {hypermap : ClassicalCertificateConfiguration.HypermapCode}
    {partition : Code} {traceLength : Nat}
    (valid : ClassicalCertificateFacePartition.Valid hypermap partition)
    (ring : List.Vector (Fin hypermap.dartCount) traceLength)
    (certificate : Certificate partition.faceCount traceLength)
    (haccepted : certificate.checker valid ring = true)
    (word : TraceWord traceLength) (hword : word ∈ certificate.words) :
    ∃ assignment : Fin partition.faceCount → Color,
      IsProperAssignment valid assignment ∧
        word.toList.map TraceSymbol.toColor =
          ringTraceOfAssignment valid ring.toList assignment := by
  have hvalid := certificate.valid_of_checker_true valid ring haccepted
  simp only [words, List.mem_toFinset, List.mem_map] at hword
  obtain ⟨witness, hwitness, rfl⟩ := hword
  exact ⟨witness.assignment, (hvalid witness hwitness).1,
    (hvalid witness hwitness).2⟩

end Certificate

def firstCatalogueRingVector :
    List.Vector (Fin firstCatalogueSampleCode.dartCount) 6 :=
  ⟨firstCatalogueRing, by decide⟩

/-- Sixteen representatives, one from each global-color orbit of ordinary
boundary traces for `cf001`. -/
def firstCatalogueWitnessCertificate : Certificate 10 6 where
  witnesses :=
    [
      { colors := ⟨[.zero, .red, .purple, .blue, .red, .zero, .purple,
          .zero, .red, .blue], rfl⟩,
        word := ⟨[.red, .red, .red, .red, .blue, .blue], rfl⟩ },
      { colors := ⟨[.zero, .blue, .purple, .red, .blue, .purple, .zero,
          .purple, .blue, .red], rfl⟩,
        word := ⟨[.red, .red, .red, .blue, .red, .blue], rfl⟩ },
      { colors := ⟨[.zero, .red, .purple, .red, .blue, .purple, .red,
          .purple, .zero, .blue], rfl⟩,
        word := ⟨[.red, .red, .blue, .red, .red, .blue], rfl⟩ },
      { colors := ⟨[.zero, .red, .purple, .blue, .blue, .purple, .zero,
          .purple, .red, .blue], rfl⟩,
        word := ⟨[.red, .red, .blue, .red, .blue, .red], rfl⟩ },
      { colors := ⟨[.zero, .blue, .purple, .red, .red, .zero, .purple,
          .zero, .blue, .red], rfl⟩,
        word := ⟨[.red, .red, .blue, .blue, .red, .red], rfl⟩ },
      { colors := ⟨[.zero, .purple, .red, .blue, .zero, .red, .blue,
          .red, .purple, .zero], rfl⟩,
        word := ⟨[.red, .red, .blue, .purple, .blue, .purple], rfl⟩ },
      { colors := ⟨[.zero, .purple, .red, .purple, .zero, .red, .purple,
          .red, .zero, .blue], rfl⟩,
        word := ⟨[.red, .red, .blue, .purple, .purple, .blue], rfl⟩ },
      { colors := ⟨[.zero, .red, .blue, .red, .blue, .purple, .red,
          .zero, .zero, .purple], rfl⟩,
        word := ⟨[.red, .blue, .red, .red, .red, .blue], rfl⟩ },
      { colors := ⟨[.zero, .red, .purple, .blue, .blue, .purple, .red,
          .zero, .zero, .blue], rfl⟩,
        word := ⟨[.red, .blue, .red, .red, .blue, .red], rfl⟩ },
      { colors := ⟨[.zero, .blue, .red, .blue, .red, .zero, .blue,
          .purple, .purple, .zero], rfl⟩,
        word := ⟨[.red, .blue, .red, .blue, .blue, .blue], rfl⟩ },
      { colors := ⟨[.zero, .purple, .red, .purple, .zero, .red, .purple,
          .blue, .blue, .zero], rfl⟩,
        word := ⟨[.red, .blue, .red, .purple, .purple, .blue], rfl⟩ },
      { colors := ⟨[.zero, .red, .blue, .red, .red, .zero, .blue,
          .purple, .purple, .zero], rfl⟩,
        word := ⟨[.red, .blue, .blue, .red, .red, .red], rfl⟩ },
      { colors := ⟨[.zero, .red, .purple, .blue, .red, .zero, .blue,
          .purple, .red, .zero], rfl⟩,
        word := ⟨[.red, .blue, .blue, .red, .blue, .blue], rfl⟩ },
      { colors := ⟨[.zero, .red, .blue, .purple, .red, .zero, .blue,
          .purple, .red, .zero], rfl⟩,
        word := ⟨[.red, .blue, .blue, .red, .purple, .purple], rfl⟩ },
      { colors := ⟨[.zero, .blue, .red, .blue, .blue, .purple, .red,
          .zero, .zero, .purple], rfl⟩,
        word := ⟨[.red, .blue, .blue, .blue, .blue, .red], rfl⟩ },
      { colors := ⟨[.zero, .purple, .red, .blue, .blue, .purple, .red,
          .zero, .zero, .blue], rfl⟩,
        word := ⟨[.red, .blue, .purple, .purple, .blue, .red], rfl⟩ }
    ]

theorem firstCatalogueWitnessCertificate_checker :
    firstCatalogueWitnessCertificate.checker firstCataloguePartitionValid
      firstCatalogueRingVector = true := by
  decide

theorem firstCatalogue_witnessWord_is_ringTrace
    (word : TraceWord 6)
    (hword : word ∈ firstCatalogueWitnessCertificate.words) :
    ∃ assignment : Fin firstCatalogueFacePartition.faceCount → Color,
      IsProperAssignment firstCataloguePartitionValid assignment ∧
        word.toList.map TraceSymbol.toColor =
          ringTraceOfAssignment firstCataloguePartitionValid
            firstCatalogueRing assignment := by
  simpa [firstCatalogueRingVector] using
    firstCatalogueWitnessCertificate.exists_properAssignment_of_mem_words
      firstCataloguePartitionValid firstCatalogueRingVector
      firstCatalogueWitnessCertificate_checker word hword

end ClassicalCertificateTraceWitness

end Mettapedia.GraphTheory.FourColor
