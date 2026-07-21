import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfiguration

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationCatalogue

open ClassicalCertificateConfiguration

/-- A fixed-chunk table of classical configuration programs. -/
structure ProgramCatalogue where
  chunks : Array (Array Configuration)
  deriving DecidableEq

namespace ProgramCatalogue

def chunkSize : Nat := 16

def programAt? (catalogue : ProgramCatalogue) (index : Nat) :
    Option Configuration :=
  (catalogue.chunks[index / chunkSize]?).bind fun chunk =>
    chunk[index % chunkSize]?

def valueBound (catalogue : ProgramCatalogue) : Nat :=
  catalogue.chunks.size * chunkSize

/-- Check the compiled finite-hypermap equations for one fixed-size chunk. -/
def programChunkBoolean (catalogue : ProgramCatalogue) (chunk : Nat) : Bool :=
  (List.range chunkSize).all fun offset =>
    let index := chunk * chunkSize + offset
    match catalogue.programAt? index with
    | some configuration =>
        configuration.compile.pointee.wellFormedChecker
    | none => true

def checker (catalogue : ProgramCatalogue) : Bool :=
  (List.range catalogue.chunks.size).all catalogue.programChunkBoolean

def populatedPrefixBoolean (catalogue : ProgramCatalogue) (count : Nat) :
    Bool :=
  (List.range count).all fun index =>
    (catalogue.programAt? index).isSome

theorem exists_program_of_populatedPrefixBoolean
    (catalogue : ProgramCatalogue) (count : Nat)
    (hpopulated : catalogue.populatedPrefixBoolean count = true)
    (index : Nat) (hindex : index < count) :
    ∃ configuration,
      catalogue.programAt? index = some configuration := by
  have hsome := (List.all_eq_true.1 hpopulated) index
    (List.mem_range.2 hindex)
  exact Option.isSome_iff_exists.1 hsome

/-- Every selected entry in an accepted program table compiles to a genuine
finite hypermap. -/
theorem wellFormed_of_checker_true
    (catalogue : ProgramCatalogue) (hchecker : catalogue.checker = true)
    (index : Nat) (hindex : index < catalogue.valueBound)
    (configuration : Configuration)
    (hprogram : catalogue.programAt? index = some configuration) :
    configuration.compile.pointee.WellFormed := by
  have hchunk : index / chunkSize < catalogue.chunks.size := by
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
  simp [hindexEq, hprogram] at hvalid
  exact ClassicalCertificateConfiguration.RawHypermap.wellFormed_of_checker_true
    configuration.compile.pointee hvalid

end ProgramCatalogue

end ClassicalCertificateConfigurationCatalogue

end Mettapedia.GraphTheory.FourColor
