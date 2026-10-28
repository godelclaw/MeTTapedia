import Mettapedia.GSLT.LanguageDef.ModuleSource.InductiveMeTTaPackageControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedPolynomialGeneratedReceipts

/-!
# Authored Nat declarations through the simple-inductive generator

The source admission checks the family, its universe profile, constructor
names and recursive field binding. The admitted source fields then feed the
existing simple-inductive constructor, recursor and computation generators.
Both MeTTa authoring forms traverse this path. The independent native Nat
declaration library is used only as the comparison target.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.InductiveMeTTaNaturalPackage

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open TypedEquality Normalization Annotated
open Declaration Declaration.IndexedFamily
open InductiveMeTTaData

variable {Head : Type}

def fields (family : String) : List InductiveSyntax.Binder → Option (List (Normalization.Field Head))
  | [] => some []
  | field :: rest => if field.type = .name family then
      (fields family rest).map (.recursive :: ·) else none

def generated (family recursor : DeclName) (sortHead motiveUniverse : Head)
    (constructors : List (DeclName × List (Normalization.Field Head))) :=
  let entries : List (DeclName × Entry Head) :=
    [(family, ⟨.head sortHead, none⟩)] ++
      constructors.map (fun (name, fields) => (name, ⟨ctorType family fields, none⟩)) ++
      [(recursor, ⟨recType family motiveUniverse constructors, none⟩)]
  let rows : List (Data.Row Head) :=
    (IndexedPolynomialGenerated.origins constructors).map fun origin =>
      ⟨origin.arity, iotaTele family motiveUniverse constructors origin.fields,
        origin.left recursor, origin.right recursor,
        .app (.var ⟨constructors.length + origin.fields.length, by
          simp only [IndexedPolynomialGenerated.Origin.arity]; omega⟩)
          (appSpine (.const origin.constructor)
            ((metaVars origin.arity).drop (1 + constructors.length)))⟩
  (entries, rows)

def fromFamily (names : IndexedNatVecSource.Names) (resolve : String → DeclName)
    (recursor : DeclName) (sortHead motiveUniverse : Head) (family : InductiveSyntax.Family) :
    Option (List (DeclName × Entry Head) × List (Data.Row Head)) := do
  let _ ← IndexedNatVecSource.admitNatural names family
  let constructors ← family.constructors.mapM fun (constructor : InductiveSyntax.Constructor) => do
    return (resolve constructor.name, ← fields family.name constructor.fields)
  pure (generated (resolve family.name) recursor sortHead motiveUniverse constructors)

def fromBuilder (names : IndexedNatVecSource.Names) (resolve : String → DeclName)
    (recursor : DeclName) (sortHead motiveUniverse : Head) (input : Atom) := do
  fromFamily names resolve recursor sortHead motiveUniverse (← readFamily input)

def fromBlock (names : IndexedNatVecSource.Names) (resolve : String → DeclName)
    (recursor : DeclName) (sortHead motiveUniverse : Head) (input : Atom) := do
  fromFamily names resolve recursor sortHead motiveUniverse (← readBlock input)

theorem authoring_forms_agree (names : IndexedNatVecSource.Names) (resolve : String → DeclName)
    (recursor : DeclName) (sortHead motiveUniverse : Head) (family : InductiveSyntax.Family) :
    fromBuilder names resolve recursor sortHead motiveUniverse (familyData family) =
      fromBlock names resolve recursor sortHead motiveUniverse (blockData family) := by
  simp [fromBuilder, fromBlock]

open IndexedNatVecSourceControls
open NativeNaturalVectorFamilies

def resolve (name : String) : DeclName :=
  if name = names.natural then natName
  else if name = names.zero then zeroName
  else if name = names.successor then succName
  else .str .anonymous name

def naturalConstructors : List (DeclName × List (Normalization.Field Tower.Head)) :=
  [(zeroName, []), (succName, [.recursive])]

def naturalGenerated := generated natName natEliminateName
  (.sort natLevel) (.sort motiveLevel) naturalConstructors

theorem generated_reference : naturalGenerated = InductiveMeTTaPackageControls.naturalReference := by
  apply Prod.ext
  · rfl
  · decide +kernel

theorem builder_generated :
    fromBuilder (Head := Tower.Head) names resolve natEliminateName (.sort natLevel) (.sort motiveLevel)
      (familyData natural) = some naturalGenerated := by
  simp only [fromBuilder, readFamily_familyData, fromFamily, text_natural_admitted,
    Bind.bind, Option.bind]
  rfl

theorem block_generated :
    fromBlock (Head := Tower.Head) names resolve natEliminateName (.sort natLevel) (.sort motiveLevel)
      (blockData natural) = some naturalGenerated := by
  rw [← authoring_forms_agree]
  exact builder_generated

def wrongNatural : InductiveSyntax.Family :=
  { natural with constructors := natural.constructors.take 1 }

theorem missing_constructor_refused :
    fromBlock (Head := Tower.Head) names resolve natEliminateName (.sort natLevel) (.sort motiveLevel)
      (blockData wrongNatural) = none := by
  have gate : IndexedNatVecSource.admitNatural names wrongNatural = none := rfl
  simp [fromBlock, fromFamily, gate]

def capturedNatural : InductiveSyntax.Family :=
  { natural with constructors := [natural.constructors[0],
    { natural.constructors[1] with fields := [⟨names.natural, .name names.natural⟩] }] }

theorem captured_field_refused :
    fromBuilder (Head := Tower.Head) names resolve natEliminateName (.sort natLevel) (.sort motiveLevel)
      (familyData capturedNatural) = none := by
  have gate : IndexedNatVecSource.admitNatural names capturedNatural = none := rfl
  simp [fromBuilder, fromFamily, gate]

theorem generated_inventory : naturalGenerated.1.length = 4 ∧
    naturalGenerated.2.map Sigma.fst = [3, 4] := by decide +kernel


/-- The generated rows recover the independent library's checked receipts,
including their full dependent contexts and result types. -/
theorem generated_receipts {row : Data.Row Tower.Head} (member : row ∈ naturalGenerated.2) :
    Nonempty (ComputationAuthority.ProofRelevantStepReceipt Tower.rules rawSignature
      proofRelevantIotaComputation row.2.1 row.2.2.1 row.2.2.2.1 row.2.2.2.2) := by
  rw [generated_reference] at member
  exact Data.inspected_row_has_receipt (Checking.schemas.take 2) member

#print axioms authoring_forms_agree
#print axioms generated_reference
#print axioms generated_receipts
#print axioms builder_generated
#print axioms block_generated
#print axioms missing_constructor_refused
#print axioms captured_field_refused

end Mettapedia.GSLT.LanguageDef.ModuleSource.InductiveMeTTaNaturalPackage
