import Mettapedia.GraphTheory.FourColor.ClassicalCertificateIndexedLayeredKempe

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateOrbitResponseTable

open ClassicalCertificateEvenTraceKempe
open ClassicalCertificateIndexedLayeredKempe
open ClassicalCertificateKempeClosure
open ClassicalCertificateRankedKempe
open ClassicalCertificateResponseDag

variable {length : Nat}

/-- Find a global color permutation carrying a stored response spelling to
its represented orbit word at the declared rank. -/
def responsePermutation?
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (value : ClassicalCertificateResponseDag.ValueCode) :
    Option PermutationCode :=
  permutationCodes.find? fun permutation =>
    certificate.acceptsAt value.rank
      (permute permutation (decodedTraceWord length value.wordCode))

theorem responsePermutation?_sound
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (value : ClassicalCertificateResponseDag.ValueCode)
    (permutation : PermutationCode)
    (hfound : responsePermutation? certificate value = some permutation) :
    certificate.acceptsAt value.rank
      (permute permutation (decodedTraceWord length value.wordCode)) = true :=
  by
    have hselected := List.find?_some hfound
    simpa [responsePermutation?] using hselected

def responseValueBoolean
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (value : ClassicalCertificateResponseDag.ValueCode) : Bool :=
  (responsePermutation? certificate value).isSome

def responseValueChunkBoolean
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (chunk : Nat) : Bool :=
  (List.range ClassicalCertificateResponseDag.chunkSize).all fun offset =>
    let index := chunk * ClassicalCertificateResponseDag.chunkSize + offset
    match ClassicalCertificateResponseDag.valueAt?
        certificate.responseCode index with
    | some value => responseValueBoolean certificate value
    | none => true

def responseValueTableBoolean
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length) :
    Bool :=
  (List.range certificate.responseCode.values.size).all
    (responseValueChunkBoolean certificate)

theorem responseValueTableBoolean_sound
    (certificate : ClassicalCertificateIndexedLayeredKempe.Certificate length)
    (htable : responseValueTableBoolean certificate = true)
    (index : Nat)
    (hindex : index <
      ClassicalCertificateResponseDag.valueBound certificate.responseCode)
    (value : ClassicalCertificateResponseDag.ValueCode)
    (hvalue : ClassicalCertificateResponseDag.valueAt?
      certificate.responseCode index = some value) :
    ∃ permutation,
      certificate.acceptsAt value.rank
        (permute permutation
          (decodedTraceWord length value.wordCode)) = true := by
  have hchunk : index / ClassicalCertificateResponseDag.chunkSize <
      certificate.responseCode.values.size := by
    have hpositive : 0 < ClassicalCertificateResponseDag.chunkSize := by
      decide
    exact (Nat.div_lt_iff_lt_mul hpositive).2 (by
      simpa [ClassicalCertificateResponseDag.valueBound,
        Nat.mul_comm] using hindex)
  have hchunkValid := (List.all_eq_true.1 htable)
    (index / ClassicalCertificateResponseDag.chunkSize)
      (List.mem_range.2 hchunk)
  have hoffset : index % ClassicalCertificateResponseDag.chunkSize <
      ClassicalCertificateResponseDag.chunkSize :=
    Nat.mod_lt _ (by decide)
  have hvalid := (List.all_eq_true.1 hchunkValid)
    (index % ClassicalCertificateResponseDag.chunkSize)
      (List.mem_range.2 hoffset)
  have hindexEq : index / ClassicalCertificateResponseDag.chunkSize *
        ClassicalCertificateResponseDag.chunkSize +
          index % ClassicalCertificateResponseDag.chunkSize = index :=
    by simpa [Nat.mul_comm] using
      Nat.div_add_mod index ClassicalCertificateResponseDag.chunkSize
  have hsome : responseValueBoolean certificate value = true := by
    simpa [responseValueChunkBoolean, hindexEq, hvalue] using hvalid
  obtain ⟨permutation, hpermutation⟩ := Option.isSome_iff_exists.1 hsome
  exact ⟨permutation,
    responsePermutation?_sound certificate value permutation hpermutation⟩

end ClassicalCertificateOrbitResponseTable

end Mettapedia.GraphTheory.FourColor
