import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueProgramsData
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueHypermapsData
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateNormalizedConfiguration

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateConfigurationProvenance

open ClassicalCertificateCatalogueHypermaps
open ClassicalCertificateCataloguePrograms
open ClassicalCertificateConfiguration
open ClassicalCertificateNormalizedConfiguration

/-- Check that one indexed construction program materializes to the indexed
finite-hypermap table. -/
def entryBoolean (index : Nat) : Bool :=
  match classicalConfigurationCatalogue.programAt? index,
      classicalHypermapCatalogue.codeAt? index with
  | some configuration, some code =>
      decide
        ((compileNormalized configuration.program).pointee =
          code.hypermap)
  | _, _ => false

def chunkSize : Nat := 16

def catalogueCount : Nat := 633

/-- A fixed-size provenance shard; indices beyond the 633-entry prefix are
padding rather than catalogue claims. -/
def chunkBoolean (chunk : Nat) : Bool :=
  (List.range chunkSize).all fun offset =>
    let index := chunk * chunkSize + offset
    if index < catalogueCount then entryBoolean index else true

def checker : Bool :=
  (List.range 40).all chunkBoolean

/-- The aggregate Boolean checker exposes the local provenance fact at every
published catalogue index. -/
theorem entryBoolean_of_checker_true
    (hchecker : checker = true) (index : Nat)
    (hindex : index < catalogueCount) :
    entryBoolean index = true := by
  have hchunk : index / chunkSize < 40 := by
    simp only [chunkSize, catalogueCount] at hindex ⊢
    omega
  have hchunkValid := (List.all_eq_true.1 hchecker)
    (index / chunkSize) (List.mem_range.2 hchunk)
  have hoffset : index % chunkSize < chunkSize :=
    Nat.mod_lt _ (by decide)
  have hvalid := (List.all_eq_true.1 hchunkValid)
    (index % chunkSize) (List.mem_range.2 hoffset)
  have hindexEq : index / chunkSize * chunkSize + index % chunkSize = index :=
    by simpa [Nat.mul_comm] using Nat.div_add_mod index chunkSize
  simp [hindexEq, hindex] at hvalid
  exact hvalid

/-- A successful indexed provenance check relates the original recursive
configuration semantics, not merely the normalized evaluator, to the exported
hypermap certificate. -/
theorem materialize_eq_of_entryBoolean_true
    (index : Nat) (hentry : entryBoolean index = true)
    (configuration : Configuration)
    (hconfiguration :
      classicalConfigurationCatalogue.programAt? index = some configuration)
    (code : ClassicalCertificateFastHypermapCheck.InverseCode)
    (hcode : classicalHypermapCatalogue.codeAt? index = some code) :
    HypermapCode.materialize configuration.compile.pointee =
      code.hypermap := by
  simp only [entryBoolean, hconfiguration, hcode] at hentry
  have hnormalized :
      (compileNormalized configuration.program).pointee =
        code.hypermap := Bool.of_decide_true hentry
  rw [compileNormalized_pointee] at hnormalized
  exact hnormalized

/-- A successful indexed check contains both catalogue entries and their exact
construction provenance. -/
theorem exists_materialized_eq_of_entryBoolean_true
    (index : Nat) (hentry : entryBoolean index = true) :
    ∃ configuration code,
      classicalConfigurationCatalogue.programAt? index = some configuration ∧
        classicalHypermapCatalogue.codeAt? index = some code ∧
        HypermapCode.materialize configuration.compile.pointee =
          code.hypermap := by
  cases hconfiguration :
      classicalConfigurationCatalogue.programAt? index with
  | none =>
      simp [entryBoolean, hconfiguration] at hentry
  | some configuration =>
      cases hcode : classicalHypermapCatalogue.codeAt? index with
      | none =>
          simp [entryBoolean, hconfiguration, hcode] at hentry
      | some code =>
          exact ⟨configuration, code, rfl, rfl,
            materialize_eq_of_entryBoolean_true index hentry configuration
              hconfiguration code hcode⟩

/-- Aggregate provenance yields a construction program and its exact exported
map at every published index. -/
theorem exists_materialized_eq_of_checker_true
    (hchecker : checker = true) (index : Nat)
    (hindex : index < catalogueCount) :
    ∃ configuration code,
      classicalConfigurationCatalogue.programAt? index = some configuration ∧
        classicalHypermapCatalogue.codeAt? index = some code ∧
        HypermapCode.materialize configuration.compile.pointee =
          code.hypermap :=
  exists_materialized_eq_of_entryBoolean_true index
    (entryBoolean_of_checker_true hchecker index hindex)

end ClassicalCertificateConfigurationProvenance

end Mettapedia.GraphTheory.FourColor
