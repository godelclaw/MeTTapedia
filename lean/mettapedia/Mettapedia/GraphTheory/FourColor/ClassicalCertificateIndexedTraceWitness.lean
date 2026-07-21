import Mettapedia.GraphTheory.FourColor.ClassicalCertificateIndexedTraceMap
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateTraceDag
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateTraceWitness

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateIndexedTraceWitness

open ClassicalCertificateConfiguration
open ClassicalCertificateFacePartition
open ClassicalCertificateIndexedTraceMap
open ClassicalCertificateRankedKempe
open ClassicalCertificateTraceDag
open ClassicalCertificateTraceTree
open ClassicalCertificateTraceWitness

/-- A trace-indexed family of ordinary-coloring witnesses.  Fixed-size table
chunks keep validation and lookup local. -/
structure Certificate (faceCount traceLength : Nat) where
  chunks : Array (Array (Witness faceCount traceLength))
  tree : ClassicalCertificateIndexedTraceMap.Tree
  deriving DecidableEq

namespace Certificate

variable {faceCount traceLength : Nat}

def chunkSize : Nat := 64

def witnessAt? (certificate : Certificate faceCount traceLength)
    (index : Nat) : Option (Witness faceCount traceLength) :=
  (certificate.chunks[index / chunkSize]?).bind fun chunk =>
    chunk[index % chunkSize]?

def valueBound (certificate : Certificate faceCount traceLength) : Nat :=
  certificate.chunks.size * chunkSize

def witnessChunkBoolean {hypermap : HypermapCode}
    {partition : ClassicalCertificateFacePartition.Code}
    (valid : ClassicalCertificateFacePartition.Valid hypermap partition)
    (ring : List.Vector (Fin hypermap.dartCount) traceLength)
    (certificate : Certificate partition.faceCount traceLength)
    (chunk : Nat) : Bool :=
  (List.range chunkSize).all fun offset =>
    let index := chunk * chunkSize + offset
    match certificate.witnessAt? index with
    | some witness => decide (witness.Valid valid ring)
    | none => true

def witnessTableBoolean {hypermap : HypermapCode}
    {partition : ClassicalCertificateFacePartition.Code}
    (valid : ClassicalCertificateFacePartition.Valid hypermap partition)
    (ring : List.Vector (Fin hypermap.dartCount) traceLength)
    (certificate : Certificate partition.faceCount traceLength) : Bool :=
  (List.range certificate.chunks.size).all fun chunk =>
    certificate.witnessChunkBoolean valid ring chunk

theorem witnessTableBoolean_sound {hypermap : HypermapCode}
    {partition : ClassicalCertificateFacePartition.Code}
    (valid : ClassicalCertificateFacePartition.Valid hypermap partition)
    (ring : List.Vector (Fin hypermap.dartCount) traceLength)
    (certificate : Certificate partition.faceCount traceLength)
    (htable : certificate.witnessTableBoolean valid ring = true)
    (index : Nat) (hindex : index < certificate.valueBound)
    (witness : Witness partition.faceCount traceLength)
    (hvalue : certificate.witnessAt? index = some witness) :
    witness.Valid valid ring := by
  have hchunk : index / chunkSize < certificate.chunks.size := by
    have hpositive : 0 < chunkSize := by decide
    exact (Nat.div_lt_iff_lt_mul hpositive).2 (by
      simpa [valueBound, Nat.mul_comm] using hindex)
  have hchunkValid := (List.all_eq_true.1 htable)
    (index / chunkSize) (List.mem_range.2 hchunk)
  have hoffset : index % chunkSize < chunkSize :=
    Nat.mod_lt _ (by decide)
  have hvalid := (List.all_eq_true.1 hchunkValid)
    (index % chunkSize) (List.mem_range.2 hoffset)
  have hindexEq : index / chunkSize * chunkSize + index % chunkSize = index :=
    by simpa [Nat.mul_comm] using Nat.div_add_mod index chunkSize
  simp [hindexEq, hvalue] at hvalid
  exact hvalid

def mapEntryBoolean (certificate : Certificate faceCount traceLength)
    (index : Nat) (word : List TraceSymbol) : Bool :=
  if index < certificate.valueBound then
    match certificate.witnessAt? index with
    | some witness => decide (witness.word.toList = word)
    | none => false
  else false

def mapBoolean (certificate : Certificate faceCount traceLength) : Bool :=
  certificate.tree.checker traceLength certificate.mapEntryBoolean

def hasWitness (certificate : Certificate faceCount traceLength)
    (word : List TraceSymbol) : Bool :=
  (certificate.tree.lookup word).isSome

theorem mapEntry_of_lookup
    (certificate : Certificate faceCount traceLength)
    (hmap : certificate.mapBoolean = true)
    (word : List TraceSymbol) (index : Nat)
    (hlength : word.length = traceLength)
    (hlookup : certificate.tree.lookup word = some index) :
    ∃ witness : Witness faceCount traceLength,
      index < certificate.valueBound ∧
        certificate.witnessAt? index = some witness ∧
          witness.word.toList = word := by
  have hentry := certificate.tree.lookup_sound_of_checker_true traceLength
    certificate.mapEntryBoolean hmap word index hlength hlookup
  unfold mapEntryBoolean at hentry
  split at hentry
  · rename_i hindex
    cases hvalue : certificate.witnessAt? index with
    | none => simp [hvalue] at hentry
    | some witness =>
        exact ⟨witness, hindex, rfl, of_decide_eq_true (by
          simpa [hvalue] using hentry)⟩
  · simp at hentry

theorem exists_validWitness_of_lookup {hypermap : HypermapCode}
    {partition : ClassicalCertificateFacePartition.Code}
    (valid : ClassicalCertificateFacePartition.Valid hypermap partition)
    (ring : List.Vector (Fin hypermap.dartCount) traceLength)
    (certificate : Certificate partition.faceCount traceLength)
    (htable : certificate.witnessTableBoolean valid ring = true)
    (hmap : certificate.mapBoolean = true)
    (word : List TraceSymbol) (index : Nat)
    (hlength : word.length = traceLength)
    (hlookup : certificate.tree.lookup word = some index) :
    ∃ witness : Witness partition.faceCount traceLength,
      witness.word.toList = word ∧ witness.Valid valid ring := by
  obtain ⟨witness, hindex, hvalue, hword⟩ :=
    certificate.mapEntry_of_lookup hmap word index hlength hlookup
  exact ⟨witness, hword,
    certificate.witnessTableBoolean_sound valid ring htable index hindex
      witness hvalue⟩

theorem exists_properAssignment_of_hasWitness {hypermap : HypermapCode}
    {partition : ClassicalCertificateFacePartition.Code}
    (valid : ClassicalCertificateFacePartition.Valid hypermap partition)
    (ring : List.Vector (Fin hypermap.dartCount) traceLength)
    (certificate : Certificate partition.faceCount traceLength)
    (htable : certificate.witnessTableBoolean valid ring = true)
    (hmap : certificate.mapBoolean = true)
    (word : TraceWord traceLength)
    (hhas : certificate.hasWitness word.toList = true) :
    ∃ assignment : Fin partition.faceCount → Color,
      IsProperAssignment valid assignment ∧
        word.toList.map TraceSymbol.toColor =
          ringTraceOfAssignment valid ring.toList assignment := by
  obtain ⟨index, hlookup⟩ :
      ∃ index, certificate.tree.lookup word.toList = some index :=
    Option.isSome_iff_exists.1 (by simpa [hasWitness] using hhas)
  obtain ⟨witness, hword, hvalid⟩ :=
    certificate.exists_validWitness_of_lookup valid ring htable hmap
      word.toList index word.2 hlookup
  refine ⟨witness.assignment, hvalid.1, ?_⟩
  calc
    word.toList.map TraceSymbol.toColor =
        witness.word.toList.map TraceSymbol.toColor := by rw [hword]
    _ = ringTraceOfAssignment valid ring.toList witness.assignment :=
      hvalid.2

def coversDagBoolean (certificate : Certificate faceCount traceLength)
    (traceCode : ClassicalCertificateTraceDag.Code) (root : Nat) : Bool :=
  (ClassicalCertificateTraceDag.acceptedWords traceLength traceCode root).all
    fun word => certificate.hasWitness word.toList

theorem exists_properAssignment_of_dag_accepts {hypermap : HypermapCode}
    {partition : ClassicalCertificateFacePartition.Code}
    (valid : ClassicalCertificateFacePartition.Valid hypermap partition)
    (ring : List.Vector (Fin hypermap.dartCount) traceLength)
    (certificate : Certificate partition.faceCount traceLength)
    (traceCode : ClassicalCertificateTraceDag.Code) (root : Nat)
    (htable : certificate.witnessTableBoolean valid ring = true)
    (hmap : certificate.mapBoolean = true)
    (hcoverage : certificate.coversDagBoolean traceCode root = true)
    (word : TraceWord traceLength)
    (haccepted : ClassicalCertificateTraceDag.accepts traceLength traceCode
      root word.toList = true) :
    ∃ assignment : Fin partition.faceCount → Color,
      IsProperAssignment valid assignment ∧
        word.toList.map TraceSymbol.toColor =
          ringTraceOfAssignment valid ring.toList assignment := by
  have hmem : word ∈
      ClassicalCertificateTraceDag.acceptedWords traceLength traceCode root :=
    (ClassicalCertificateTraceDag.mem_acceptedWords_iff_accepts
      traceCode root word).2 haccepted
  have hhas := (List.all_eq_true.1 hcoverage) word hmem
  exact certificate.exists_properAssignment_of_hasWitness valid ring htable
    hmap word hhas

end Certificate

end ClassicalCertificateIndexedTraceWitness

end Mettapedia.GraphTheory.FourColor
