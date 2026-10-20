import Mettapedia.GSLT.LanguageDef.IndexedInductiveGuestDeclarations
import Mettapedia.GSLT.LanguageDef.IndexedInductiveGuestTypedControls
import Mettapedia.GSLT.LanguageDef.IndexedInductiveExamples

/-!
# Prefix admission controls for generated indexed declarations

The parameterized vector inventory is compared with the independent cumulative
declaration library. A second, executable instance generates a tagged mutual
even/odd family. Both use the existing prefix checker; no generated iota rule
is enabled while admitting declarations or checking computation endpoints.

The mutual tags are encoded by zero and successor-zero in the guest natural
index sort. These controls establish declaration and endpoint formation, not a
full semantic equivalence between the Boolean and natural index universes.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.DeclarationControls

open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Declaration Declarations

abbrev baseDecoder := Tower.Checking.decoder

def choices : Declarations.Choices Tower.rules baseDecoder where
  headType head := some (StructuralTypingReplay.TowerDecisions.headTarget head)
  join first second := match first, second with
    | .sort first, .sort second => some (.sort (.max first second))
    | _, _ => none
  cumulative first second := decide (Tower.rules.cumulative first second)
  normalize := fun _ term => term
  conversion := fun _ left right =>
    if left = right then some (.refl left)
    else match left, right with
      | .head first, .head second => some (.single (.head first second))
      | _, _ => none

def accepted (prior source : List (DeclName × Entry Tower.Head)) : Bool :=
  (Declarations.elaborate Tower.rules baseDecoder choices 64 prior source).isSome

theorem accepted_sound (prior source : List (DeclName × Entry Tower.Head))
    (checked : accepted prior source = true) :
    DeclarationAdmissionReplay.Admitted Tower.rules prior source := by
  obtain ⟨certificates, produced⟩ := Option.isSome_iff_exists.mp checked
  exact Declarations.elaborate_sound _ _ _ _ _ _ certificates produced

def vectorNames : Names where
  family := NativeNaturalVectorFamilies.vecName
  constructor name := if name = "Nil" then NativeNaturalVectorFamilies.vnilName
    else NativeNaturalVectorFamilies.vconsName
  eliminator := NativeNaturalVectorFamilies.vecEliminateName

def vectorParameters (A : Type) :
    Parameters (IndexedInductiveNatVec.Vectors.interface A) Tower.Head 1 where
  context := NativeNaturalVectorFamilies.vecContextA
  dataType := (TypedControls.types A).dataType
  indexType := NativeNaturalVectorFamilies.natTm
  familyUniverse := .sort NativeNaturalVectorFamilies.elementLevel
  motiveUniverse := .sort NativeNaturalVectorFamilies.motiveLevel

theorem vector_types (A : Type) :
    (vectorParameters A).types vectorNames = TypedControls.types A := rfl

noncomputable def vectorEntries (A : Type) :=
  entries (TypedControls.indexSyntax A) (vectorParameters A) vectorNames
    (IndexedInductiveNatVec.Vectors.admitted A)

theorem vector_entries_reference (A : Type) :
    vectorEntries A = NativeNaturalVectorFamilies.declarations.drop 4 := by
  change ([(NativeNaturalVectorFamilies.vecName, ⟨NativeNaturalVectorFamilies.vecType, none⟩),
    (NativeNaturalVectorFamilies.vnilName, ⟨.pi
      (.head (.sort NativeNaturalVectorFamilies.elementLevel))
      (Types.constructorType (TypedControls.indexSyntax A) (IndexedInductiveNatVec.Vectors.nilCode A)
        (TypedControls.types A) PUnit.unit), none⟩),
    (NativeNaturalVectorFamilies.vconsName, ⟨.pi
      (.head (.sort NativeNaturalVectorFamilies.elementLevel))
      (Types.constructorType (TypedControls.indexSyntax A) (IndexedInductiveNatVec.Vectors.consCode A)
        (TypedControls.types A) PUnit.unit), none⟩),
    (NativeNaturalVectorFamilies.vecEliminateName, ⟨.pi
      (.head (.sort NativeNaturalVectorFamilies.elementLevel))
      (Types.eliminatorType (TypedControls.indexSyntax A) (IndexedInductiveNatVec.Vectors.admitted A)
        (TypedControls.types A)), none⟩)] : List (DeclName × Entry Tower.Head)) = _
  rw [TypedControls.generated_nil_type, TypedControls.generated_cons_type,
    TypedControls.generated_eliminator_type]
  rfl

namespace Mutual

abbrev sourceInterface := IndexedInductiveExamples.Mutual.interface
abbrev admitted := IndexedInductiveExamples.Mutual.admitted

def tag {n : Nat} (value : Bool) : Tower.Tm n :=
  if value then NativeNaturalVectorFamilies.succApp NativeNaturalVectorFamilies.zeroTm
  else NativeNaturalVectorFamilies.zeroTm

def indices : IndexSyntax sourceInterface Tower.Head where
  term expression _ := tag expression
  substitute := by
    intro context n m expression environment substitution
    cases expression <;> rfl

def names : Names where
  family := `Generated.Mutual
  constructor name := .str `Generated.Mutual name
  eliminator := `Generated.Mutual.eliminate

def parameters : Parameters sourceInterface Tower.Head 0 where
  context := .nil
  dataType := Empty.elim
  indexType := NativeNaturalVectorFamilies.natTm
  familyUniverse := .sort Tower.zero
  motiveUniverse := .sort Tower.zero

def generated := entries indices parameters names admitted
def prior := NativeNaturalVectorFamilies.declarations.take 3
def library := prior ++ generated
abbrev rules := extendRules Tower.rules (Signature.ofList library)
def decoder := DeclarationConversionCode.ofList Tower.rules baseDecoder library

instance : DecidableRel rules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
instance : DecidablePred rules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
instance : ∀ u v w, Decidable (rules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
instance : DecidableRel rules.cumulative :=
  fun u v => inferInstanceAs (Decidable (Tower.rules.cumulative u v))
instance : DecidableRel rules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

def termAccepted {n : Nat} (context : Tower.Ctx n) (term type : Tower.Tm n) : Bool :=
  (FormationSensitiveElaboration.elaborate rules decoder choices 64 context term type).isSome

def zero : Tower.Tm 0 := .const (names.constructor "zero")
def odd (child : Tower.Tm 0) : Tower.Tm 0 := .app (.const (names.constructor "odd")) child
def even (child : Tower.Tm 0) : Tower.Tm 0 := .app (.const (names.constructor "even")) child
def fibre (index : Bool) : Tower.Tm 0 := .app (.const names.family) (tag index)

def rowsChecked : Bool := Formation.check rules decoder choices 64 indices admitted
  (parameters.types names) .nil (.const names.eliminator)

def emptyFamily : Admitted sourceInterface [] := ⟨[], by simp⟩
def emptyEntries := entries indices parameters names emptyFamily

def badEmptyEntries := entries indices
  { parameters with indexType := .const `Undeclared.Index } names emptyFamily

def duplicateNames : Names := { names with constructor := fun _ => `Generated.Duplicate }
def duplicateEntries := entries indices parameters duplicateNames admitted

end Mutual

def verdicts : List (String × Bool) := [
  ("independent Nat prefix and generated Vec inventory form", accepted [] NativeNaturalVectorFamilies.declarations),
  ("Vec admits against its actual Nat prefix", accepted (NativeNaturalVectorFamilies.declarations.take 4)
    (NativeNaturalVectorFamilies.declarations.drop 4)),
  ("Vec cannot precede its Nat dependency", !(accepted [] (NativeNaturalVectorFamilies.declarations.drop 4))),
  ("reversed declaration dependencies fail", !(accepted [] NativeNaturalVectorFamilies.declarations.reverse)),
  ("generated mutual declarations form", accepted [] Mutual.library),
  ("all mutual computation endpoints form without iota", Mutual.rowsChecked),
  ("mutual odd constructor accepts even child", Mutual.termAccepted .nil (Mutual.odd Mutual.zero) (Mutual.fibre true)),
  ("mutual even constructor accepts odd child", Mutual.termAccepted .nil (Mutual.even (Mutual.odd Mutual.zero)) (Mutual.fibre false)),
  ("mutual odd constructor refuses odd child", !(Mutual.termAccepted .nil
    (Mutual.odd (Mutual.odd Mutual.zero)) (Mutual.fibre true))),
  ("constructor names cannot alias after lowering", !(accepted Mutual.prior Mutual.duplicateEntries)),
  ("empty inductive still checks family and eliminator", accepted Mutual.prior Mutual.emptyEntries),
  ("empty inductive cannot hide an unformed index", !(accepted Mutual.prior Mutual.badEmptyEntries)),
  ("missing certificates cannot truncate the inventory", !(DeclarationAdmissionReplay.check
    Tower.rules baseDecoder Mutual.prior Mutual.generated [])),
  ("zero production budget does not publish", !(Declarations.elaborate Tower.rules baseDecoder choices 0
    Mutual.prior Mutual.generated).isSome),
  ("mutual source document feeds checked declarations", (Declarations.admitSource Tower.rules
    baseDecoder choices 64 Mutual.prior Mutual.indices Mutual.parameters Mutual.names
    IndexedInductiveExamples.Mutual.source).isSome)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem all_verdicts : verdicts.all Prod.snd = true := by decide +kernel

private theorem checkedAt (index : Fin verdicts.length) : (verdicts.get index).2 = true :=
  (List.all_eq_true.mp all_verdicts) _ (List.get_mem verdicts index)

/-- The source-generated dependent vector declarations, including their
parameter binder, are admitted against the real preceding Nat inventory. -/
theorem vector_prefix_admitted (A : Type) :
    DeclarationAdmissionReplay.Admitted Tower.rules
      (NativeNaturalVectorFamilies.declarations.take 4) (vectorEntries A) := by
  rw [vector_entries_reference]
  exact accepted_sound _ _ (checkedAt ⟨1, by decide⟩)

theorem vector_library_formed (A : Type) :
    (Signature.ofList (NativeNaturalVectorFamilies.declarations.take 4 ++ vectorEntries A)).Formed
      Tower.rules := by
  rw [vector_entries_reference, List.take_append_drop]
  apply opaque_formed Tower.rules NativeNaturalVectorFamilies.declarations
    (accepted_sound [] NativeNaturalVectorFamilies.declarations (checkedAt ⟨0, by decide⟩))
  intro item member
  simp only [NativeNaturalVectorFamilies.declarations, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem mutual_library_admitted :
    DeclarationAdmissionReplay.Admitted Tower.rules [] Mutual.library :=
  accepted_sound _ _ (checkedAt ⟨4, by decide⟩)

theorem mutual_library_formed : (Signature.ofList Mutual.library).Formed Tower.rules := by
  apply opaque_formed Tower.rules _ mutual_library_admitted
  intro item member
  simp only [Mutual.library, List.mem_append] at member
  rcases member with prior | generated
  · simp only [Mutual.prior, NativeNaturalVectorFamilies.declarations, List.take_succ_cons,
      List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at prior
    rcases prior with rfl | rfl | rfl <;> rfl
  · exact entries_opaque Mutual.indices Mutual.parameters Mutual.names Mutual.admitted item generated

/-- Every mutual constructor's computation endpoints are formed without
using the computation rule that will eventually relate them. -/
theorem mutual_rows_formed (occurrence : Fin Mutual.admitted.constructors.length) :
    FormationSensitive.Judgment Mutual.rules
      (Types.iotaContext Mutual.indices Mutual.admitted occurrence
        (Mutual.parameters.types Mutual.names) .nil)
      (Types.iotaSchema Mutual.indices Mutual.admitted occurrence
        (Mutual.parameters.types Mutual.names) (.const Mutual.names.eliminator)).1
      (Types.iotaType Mutual.indices Mutual.admitted occurrence
        (Mutual.parameters.types Mutual.names)) ∧
    FormationSensitive.Judgment Mutual.rules
      (Types.iotaContext Mutual.indices Mutual.admitted occurrence
        (Mutual.parameters.types Mutual.names) .nil)
      (Types.iotaSchema Mutual.indices Mutual.admitted occurrence
        (Mutual.parameters.types Mutual.names) (.const Mutual.names.eliminator)).2
      (Types.iotaType Mutual.indices Mutual.admitted occurrence
        (Mutual.parameters.types Mutual.names)) := by
  exact Formation.check_sound _ _ _ _ _ _ _ _ _ (checkedAt ⟨5, by decide⟩) occurrence

theorem mutual_source_admission :
    ∃ admitted certificates,
      Declarations.admitSource Tower.rules baseDecoder choices 64 Mutual.prior
        Mutual.indices Mutual.parameters Mutual.names IndexedInductiveExamples.Mutual.source =
          some ⟨admitted, certificates⟩ ∧
      admitted.constructors.map quoteConstructor = IndexedInductiveExamples.Mutual.source.values ∧
      DeclarationAdmissionReplay.Admitted Tower.rules Mutual.prior
        (entries Mutual.indices Mutual.parameters Mutual.names admitted) := by
  have accepted : (Declarations.admitSource Tower.rules baseDecoder choices 64 Mutual.prior
      Mutual.indices Mutual.parameters Mutual.names IndexedInductiveExamples.Mutual.source).isSome = true :=
    checkedAt ⟨14, by decide⟩
  obtain ⟨⟨admitted, certificates⟩, produced⟩ := Option.isSome_iff_exists.mp accepted
  exact ⟨admitted, certificates, produced, Declarations.admitSource_sound _ _ _ _ _ _ _ _ _ _ _ produced⟩

#print axioms vector_library_formed
#print axioms mutual_library_formed
#print axioms mutual_rows_formed
#print axioms mutual_source_admission

#eval verdicts

end Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.DeclarationControls
