import Mettapedia.GraphTheory.FourColor.ClassicalCertificateContractValidity
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataCatalogue

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateContractValidityCatalogue

open ClassicalCertificateContractValidity
open ClassicalCertificateReductionMetadata

/-- Fixed-size storage for contract-validity witnesses aligned with the
reduction-metadata catalogue. -/
structure Catalogue where
  chunks : Array (Array ClassicalCertificateContractValidity.Certificate)
  deriving DecidableEq

namespace Catalogue

def chunkSize : Nat := 16

def blockSize : Nat := 4

def blocksPerChunk : Nat := chunkSize / blockSize

def certificateAt? (catalogue : Catalogue) (index : Nat) :
    Option ClassicalCertificateContractValidity.Certificate :=
  (catalogue.chunks[index / chunkSize]?).bind fun chunk =>
    chunk[index % chunkSize]?

def valueBound (catalogue : Catalogue) : Nat :=
  catalogue.chunks.size * chunkSize

/-- Four aligned metadata/witness entries checked without selecting through
the complete catalogues. -/
def localBlockBoolean
    (metadataChunk : Array ClassicalCertificateReductionMetadata.Code)
    (validityChunk : Array ClassicalCertificateContractValidity.Certificate)
    (block : Nat) : Bool :=
  (List.range blockSize).all fun offset =>
    let localIndex := block * blockSize + offset
    match metadataChunk[localIndex]?, validityChunk[localIndex]? with
    | some metadata, some certificate => certificate.checker metadata
    | none, none => true
    | _, _ => false

/-- Four aligned entries selected through the complete catalogues. -/
def blockBoolean
    (metadataCatalogue :
      ClassicalCertificateReductionMetadataCatalogue.Certificate)
    (validityCatalogue : Catalogue) (block : Nat) : Bool :=
  (List.range blockSize).all fun offset =>
    let index := block * blockSize + offset
    match metadataCatalogue.codeAt? index,
        validityCatalogue.certificateAt? index with
    | some metadata, some certificate => certificate.checker metadata
    | none, none => true
    | _, _ => false

def blockCount (catalogue : Catalogue) : Nat :=
  catalogue.chunks.size * blocksPerChunk

/-- Catalogue-wide contract-validity checker. -/
def checker
    (metadataCatalogue :
      ClassicalCertificateReductionMetadataCatalogue.Certificate)
    (validityCatalogue : Catalogue) : Bool :=
  decide (metadataCatalogue.chunks.size = validityCatalogue.chunks.size) &&
    (List.range validityCatalogue.blockCount).all
      (blockBoolean metadataCatalogue validityCatalogue)

def populatedPrefixBoolean (catalogue : Catalogue) (count : Nat) : Bool :=
  (List.range count).all fun index => (catalogue.certificateAt? index).isSome

theorem exists_certificate_of_populatedPrefixBoolean
    (catalogue : Catalogue) (count : Nat)
    (hpopulated : catalogue.populatedPrefixBoolean count = true)
    (index : Nat) (hindex : index < count) :
    ∃ certificate, catalogue.certificateAt? index = some certificate := by
  have hsome := (List.all_eq_true.1 hpopulated) index
    (List.mem_range.2 hindex)
  exact Option.isSome_iff_exists.1 hsome

theorem blockBoolean_of_localBlockBoolean
    (metadataCatalogue :
      ClassicalCertificateReductionMetadataCatalogue.Certificate)
    (validityCatalogue : Catalogue)
    (chunkIndex : Nat)
    (metadataChunk : Array ClassicalCertificateReductionMetadata.Code)
    (validityChunk :
      Array ClassicalCertificateContractValidity.Certificate)
    (hmetadataChunk :
      metadataCatalogue.chunks[chunkIndex]? = some metadataChunk)
    (hvalidityChunk :
      validityCatalogue.chunks[chunkIndex]? = some validityChunk)
    (subblock : Nat) (hsubblock : subblock < blocksPerChunk)
    (hlocal : localBlockBoolean metadataChunk validityChunk subblock = true) :
    blockBoolean metadataCatalogue validityCatalogue
      (chunkIndex * blocksPerChunk + subblock) = true := by
  apply List.all_eq_true.2
  intro offset hoffset
  have hoffsetLt : offset < blockSize := List.mem_range.1 hoffset
  have hlocalEntry := (List.all_eq_true.1 hlocal) offset hoffset
  have hdiv :
      ((chunkIndex * blocksPerChunk + subblock) * blockSize + offset) /
          chunkSize = chunkIndex := by
    simp only [blocksPerChunk, blockSize, chunkSize] at hsubblock hoffsetLt ⊢
    omega
  have hmod :
      ((chunkIndex * blocksPerChunk + subblock) * blockSize + offset) %
          chunkSize = subblock * blockSize + offset := by
    simp only [blocksPerChunk, blockSize, chunkSize] at hsubblock hoffsetLt ⊢
    omega
  have hmetadataDiv :
      ((chunkIndex * blocksPerChunk + subblock) * blockSize + offset) /
          ClassicalCertificateReductionMetadataCatalogue.Certificate.chunkSize =
        chunkIndex := by
    simpa [ClassicalCertificateReductionMetadataCatalogue.Certificate.chunkSize,
      chunkSize] using hdiv
  have hmetadataMod :
      ((chunkIndex * blocksPerChunk + subblock) * blockSize + offset) %
          ClassicalCertificateReductionMetadataCatalogue.Certificate.chunkSize =
        subblock * blockSize + offset := by
    simpa [ClassicalCertificateReductionMetadataCatalogue.Certificate.chunkSize,
      chunkSize] using hmod
  simpa [blockBoolean, localBlockBoolean,
    ClassicalCertificateReductionMetadataCatalogue.Certificate.codeAt?,
    certificateAt?, hmetadataDiv, hmetadataMod, hdiv, hmod,
    hmetadataChunk, hvalidityChunk]
      using hlocalEntry

/-- An accepted aligned witness table proves standard contract validity at
every populated entry whose reduction metadata has already been accepted. -/
theorem validContract_of_checker_true
    (metadataCatalogue :
      ClassicalCertificateReductionMetadataCatalogue.Certificate)
    (validityCatalogue : Catalogue)
    (hchecker : checker metadataCatalogue validityCatalogue = true)
    (index : Nat) (hindex : index < validityCatalogue.valueBound)
    (metadata : ClassicalCertificateReductionMetadata.Code)
    (hmetadata : metadataCatalogue.codeAt? index = some metadata)
    (certificate : ClassicalCertificateContractValidity.Certificate)
    (hcertificate : validityCatalogue.certificateAt? index = some certificate)
    (valid : ClassicalCertificateReductionMetadata.Valid metadata) :
    (ClassicalCertificateFacePartition.checkedHypermap
      valid.partitionValid).ValidContract
        (ClassicalCertificateReductionMetadata.ring metadata)
        (ClassicalCertificateContractValidity.selectedDarts metadata) := by
  have hparts :
      decide
          (metadataCatalogue.chunks.size = validityCatalogue.chunks.size) =
            true ∧
        (List.range validityCatalogue.blockCount).all
          (blockBoolean metadataCatalogue validityCatalogue) = true := by
    simpa [checker] using hchecker
  have hblock : index / blockSize < validityCatalogue.blockCount := by
    simp only [blockSize, blockCount, blocksPerChunk, chunkSize,
      valueBound] at hindex ⊢
    omega
  have hblockValid := (List.all_eq_true.1 hparts.2)
    (index / blockSize) (List.mem_range.2 hblock)
  have hoffset : index % blockSize < blockSize :=
    Nat.mod_lt _ (by decide)
  have hentry := (List.all_eq_true.1 hblockValid)
    (index % blockSize) (List.mem_range.2 hoffset)
  have hindexEq : index / blockSize * blockSize + index % blockSize = index :=
    by simpa [Nat.mul_comm] using Nat.div_add_mod index blockSize
  have hcertificateCheck : certificate.checker metadata = true := by
    simpa [blockBoolean, hindexEq, hmetadata, hcertificate] using hentry
  exact ClassicalCertificateContractValidity.validContract_of_checker_true
    metadata valid certificate hcertificateCheck

end Catalogue

end ClassicalCertificateContractValidityCatalogue

end Mettapedia.GraphTheory.FourColor
