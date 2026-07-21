import Mettapedia.GraphTheory.FourColor.ClassicalCertificateFastHypermapCheck

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateHypermapCatalogue

open ClassicalCertificateConfiguration
open ClassicalCertificateFastHypermapCheck

/-- A fixed-chunk table of materialized finite-hypermap certificates. -/
structure Certificate where
  chunks : Array (Array InverseCode)
  deriving DecidableEq

namespace Certificate

def chunkSize : Nat := 16

def codeAt? (certificate : Certificate) (index : Nat) :
    Option InverseCode :=
  (certificate.chunks[index / chunkSize]?).bind fun chunk =>
    chunk[index % chunkSize]?

def valueBound (certificate : Certificate) : Nat :=
  certificate.chunks.size * chunkSize

def chunkBoolean (certificate : Certificate) (chunk : Nat) : Bool :=
  (List.range chunkSize).all fun offset =>
    let index := chunk * chunkSize + offset
    match certificate.codeAt? index with
    | some code => code.checker
    | none => true

def checker (certificate : Certificate) : Bool :=
  (List.range certificate.chunks.size).all certificate.chunkBoolean

def populatedPrefixBoolean (certificate : Certificate) (count : Nat) : Bool :=
  (List.range count).all fun index => (certificate.codeAt? index).isSome

theorem exists_code_of_populatedPrefixBoolean
    (certificate : Certificate) (count : Nat)
    (hpopulated : certificate.populatedPrefixBoolean count = true)
    (index : Nat) (hindex : index < count) :
    ∃ code, certificate.codeAt? index = some code := by
  have hsome := (List.all_eq_true.1 hpopulated) index
    (List.mem_range.2 hindex)
  exact Option.isSome_iff_exists.1 hsome

/-- Every selected entry in an accepted table is an actual finite hypermap. -/
theorem accepted_of_checker_true
    (certificate : Certificate) (hchecker : certificate.checker = true)
    (index : Nat) (hindex : index < certificate.valueBound)
    (code : InverseCode) (hcode : certificate.codeAt? index = some code) :
    code.hypermap.Accepted := by
  have hchunk : index / chunkSize < certificate.chunks.size := by
    have hpositive : 0 < chunkSize := by decide
    exact (Nat.div_lt_iff_lt_mul hpositive).2 (by
      simpa [valueBound, Nat.mul_comm] using hindex)
  have hchunkValid := (List.all_eq_true.1 hchecker)
    (index / chunkSize) (List.mem_range.2 hchunk)
  have hoffset : index % chunkSize < chunkSize :=
    Nat.mod_lt _ (by decide)
  have hvalid := (List.all_eq_true.1 hchunkValid)
    (index % chunkSize) (List.mem_range.2 hoffset)
  have hindexEq : index / chunkSize * chunkSize + index % chunkSize = index :=
    by simpa [Nat.mul_comm] using Nat.div_add_mod index chunkSize
  simp [hindexEq, hcode] at hvalid
  exact code.accepted_of_checker_true hvalid

end Certificate

end ClassicalCertificateHypermapCatalogue

end Mettapedia.GraphTheory.FourColor
