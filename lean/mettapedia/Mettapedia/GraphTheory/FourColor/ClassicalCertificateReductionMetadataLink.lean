import Mettapedia.GraphTheory.FourColor.ClassicalCertificateNormalizedContract
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadataData
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationProvenanceCheck

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateReductionMetadataLink

open ClassicalCertificateCatalogueHypermaps
open ClassicalCertificateCataloguePrograms
open ClassicalCertificateConfiguration
open ClassicalCertificateConfigurationProvenance
open ClassicalCertificateNormalizedContract
open ClassicalCertificateReductionMetadata
open ClassicalCertificateReductionMetadataCatalogue
open ClassicalCertificateReductionMetadataData

/-- Exact indexwise agreement between one reduction record, its normalized
program interpretation, and the independently exported hypermap. -/
def LinkConditions (configuration : Configuration)
    (inverseCode : ClassicalCertificateFastHypermapCheck.InverseCode)
    (code : ClassicalCertificateReductionMetadata.Code) : Prop :=
  code.hypermap = inverseCode.hypermap ∧
    code.ringValues = configurationForwardRing configuration ∧
    code.contractValues =
      ClassicalCertificateNormalizedContract.contractDarts configuration

instance (configuration : Configuration)
    (inverseCode : ClassicalCertificateFastHypermapCheck.InverseCode)
    (code : ClassicalCertificateReductionMetadata.Code) :
    Decidable (LinkConditions configuration inverseCode code) := by
  unfold LinkConditions
  infer_instance

def entryBoolean (index : Nat) : Bool :=
  match classicalConfigurationCatalogue.programAt? index,
      classicalHypermapCatalogue.codeAt? index,
      classicalReductionMetadataCatalogue.codeAt? index with
  | some configuration, some inverseCode, some code =>
      decide (LinkConditions configuration inverseCode code)
  | _, _, _ => false

def chunkSize : Nat := 4

def chunkBoolean (chunk : Nat) : Bool :=
  (List.range chunkSize).all fun offset =>
    let index := chunk * chunkSize + offset
    if index < 633 then entryBoolean index else true

def checker : Bool :=
  (List.range 159).all chunkBoolean

theorem conditions_of_entryBoolean_true
    (index : Nat) (hentry : entryBoolean index = true)
    (configuration : Configuration)
    (hconfiguration :
      classicalConfigurationCatalogue.programAt? index = some configuration)
    (inverseCode : ClassicalCertificateFastHypermapCheck.InverseCode)
    (hinverse :
      classicalHypermapCatalogue.codeAt? index = some inverseCode)
    (code : ClassicalCertificateReductionMetadata.Code)
    (hcode :
      classicalReductionMetadataCatalogue.codeAt? index = some code) :
    LinkConditions configuration inverseCode code := by
  simp only [entryBoolean, hconfiguration, hinverse, hcode] at hentry
  exact Bool.of_decide_true hentry

theorem programLink_of_conditions
    (configuration : Configuration)
    (inverseCode : ClassicalCertificateFastHypermapCheck.InverseCode)
    (code : ClassicalCertificateReductionMetadata.Code)
    (hmaterialized :
      materialized configuration = inverseCode.hypermap)
    (hconditions : LinkConditions configuration inverseCode code) :
    ProgramLink configuration code where
  hypermap_eq := hmaterialized.trans hconditions.1.symm
  ringValues_eq := hconditions.2.1.trans
    (configurationForwardRing_eq configuration)
  contractValues_eq := hconditions.2.2.trans
    (ClassicalCertificateNormalizedContract.contractDarts_eq configuration)

theorem entryBoolean_of_checker_true
    (hchecker : checker = true) (index : Nat) (hindex : index < 633) :
    entryBoolean index = true := by
  have hchunk : index / chunkSize < 159 := by
    simp only [chunkSize] at hindex ⊢
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

end ClassicalCertificateReductionMetadataLink

end Mettapedia.GraphTheory.FourColor
