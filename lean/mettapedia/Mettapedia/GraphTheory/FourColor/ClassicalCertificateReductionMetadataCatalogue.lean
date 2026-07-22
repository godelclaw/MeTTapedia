import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadata

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataCatalogue

open ClassicalCertificateReductionMetadata

/-- A fixed-chunk table of complete reduction-metadata records. -/
structure Certificate where
  chunks : Array (Array Code)
  deriving DecidableEq

namespace Certificate

def chunkSize : Nat := 16

def blockSize : Nat := 4

def blocksPerChunk : Nat := chunkSize / blockSize

def codeAt? (certificate : Certificate) (index : Nat) : Option Code :=
  (certificate.chunks[index / chunkSize]?).bind fun chunk =>
    chunk[index % chunkSize]?

def valueBound (certificate : Certificate) : Nat :=
  certificate.chunks.size * chunkSize

/-- Padding positions in the last fixed-size chunk carry no claim. -/
def chunkBoolean (certificate : Certificate) (chunk : Nat) : Bool :=
  (List.range chunkSize).all fun offset =>
    let index := chunk * chunkSize + offset
    match certificate.codeAt? index with
    | some code => ClassicalCertificateReductionMetadata.checker code
    | none => true

/-- Four-entry checker blocks bound kernel proof size while covering the same
fixed-chunk table. -/
def blockBoolean (certificate : Certificate) (block : Nat) : Bool :=
  (List.range blockSize).all fun offset =>
    let index := block * blockSize + offset
    match certificate.codeAt? index with
    | some code => ClassicalCertificateReductionMetadata.checker code
    | none => true

/-- The same four-entry check on one already selected data chunk. -/
def localBlockBoolean (chunk : Array Code) (block : Nat) : Bool :=
  (List.range blockSize).all fun offset =>
    match chunk[block * blockSize + offset]? with
    | some code => ClassicalCertificateReductionMetadata.checker code
    | none => true

def blockCount (certificate : Certificate) : Nat :=
  certificate.chunks.size * blocksPerChunk

theorem blockBoolean_of_localBlockBoolean
    (certificate : Certificate) (chunkIndex : Nat) (chunk : Array Code)
    (hchunk : certificate.chunks[chunkIndex]? = some chunk)
    (subblock : Nat) (hsubblock : subblock < blocksPerChunk)
    (hlocal : localBlockBoolean chunk subblock = true) :
    certificate.blockBoolean
      (chunkIndex * blocksPerChunk + subblock) = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hoffset_lt : offset < blockSize := List.mem_range.1 hoffset
  have hlocalEntry := (List.all_eq_true.1 hlocal) offset hoffset
  have hdiv :
      ((chunkIndex * blocksPerChunk + subblock) * blockSize + offset) /
          chunkSize = chunkIndex := by
    simp only [blocksPerChunk, blockSize, chunkSize] at hsubblock hoffset_lt ⊢
    omega
  have hmod :
      ((chunkIndex * blocksPerChunk + subblock) * blockSize + offset) %
          chunkSize = subblock * blockSize + offset := by
    simp only [blocksPerChunk, blockSize, chunkSize] at hsubblock hoffset_lt ⊢
    omega
  simpa [blockBoolean, localBlockBoolean, codeAt?, hdiv, hmod, hchunk]
    using hlocalEntry

def checker (certificate : Certificate) : Bool :=
  (List.range certificate.blockCount).all certificate.blockBoolean

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

/-- Every selected entry in an accepted table is semantically valid reduction
metadata. -/
theorem valid_of_checker_true
    (certificate : Certificate) (hchecker : certificate.checker = true)
    (index : Nat) (hindex : index < certificate.valueBound)
    (code : Code) (hcode : certificate.codeAt? index = some code) :
    ClassicalCertificateReductionMetadata.Valid code := by
  have hblock : index / blockSize < certificate.blockCount := by
    simp only [blockSize, blockCount, blocksPerChunk, chunkSize,
      valueBound] at hindex ⊢
    omega
  have hblockValid := (List.all_eq_true.1 hchecker)
    (index / blockSize) (List.mem_range.2 hblock)
  have hoffset : index % blockSize < blockSize :=
    Nat.mod_lt _ (by decide)
  have hvalid := (List.all_eq_true.1 hblockValid)
    (index % blockSize) (List.mem_range.2 hoffset)
  have hindexEq : index / blockSize * blockSize + index % blockSize = index :=
    by simpa [Nat.mul_comm] using Nat.div_add_mod index blockSize
  simp [hindexEq, hcode] at hvalid
  exact ClassicalCertificateReductionMetadata.valid_of_checker_true code hvalid

end Certificate

end ClassicalCertificateReductionMetadataCatalogue

end Mettapedia.GraphTheory.FourColor
