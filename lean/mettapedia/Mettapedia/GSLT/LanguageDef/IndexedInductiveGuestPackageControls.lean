import Mettapedia.GSLT.LanguageDef.IndexedInductiveGuestPackage
import Mettapedia.GSLT.LanguageDef.IndexedInductiveGuestDeclarationControls
import Mettapedia.GSLT.LanguageDef.ModuleSource.IndexedNatVecSourceControls

/-!
# Generated typed schema checks for vectors and a tagged mutual family

These examples use the shared indexed-family checker, with tables generated
from the source inventory. Canonical endpoints check without their own iota
rules. The vector table is compared with the independently authored reference
library, and the textual declaration fixture selects that same vector source.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.PackageControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Declaration Declaration.IndexedFamily
open DeclarationControls

abbrev vectorPrior := NativeNaturalVectorFamilies.declarations.take 4

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem vector_rows :
    Package.checkRows (TypedControls.indexSyntax Bool) (vectorParameters Bool) vectorNames
      (IndexedInductiveNatVec.Vectors.admitted Bool) Tower.rules baseDecoder choices 64 vectorPrior = true := by
  decide +kernel

noncomputable def vectorSchemas :=
  Package.schemas (TypedControls.indexSyntax Bool) (vectorParameters Bool) vectorNames
    (IndexedInductiveNatVec.Vectors.admitted Bool) Tower.rules baseDecoder choices 64 vectorPrior vector_rows

theorem vector_table_reference :
    Checking.table vectorSchemas = NativeNaturalVectorFamilies.Checking.table.drop 2 := by
  rw [vectorSchemas, Package.schemas_table]
  rfl

theorem vector_schema_count : vectorSchemas.length = 2 := by
  simp only [vectorSchemas, Package.schemas_length]
  rfl

theorem mutual_rows :
    Package.checkRows Mutual.indices Mutual.parameters Mutual.names Mutual.admitted
      Tower.rules baseDecoder choices 64 Mutual.prior = true := by
  exact (List.all_eq_true.mp DeclarationControls.all_verdicts) _
    (List.get_mem DeclarationControls.verdicts ⟨5, by decide⟩)

def mutualSchemas := Package.schemas Mutual.indices Mutual.parameters Mutual.names Mutual.admitted
  Tower.rules baseDecoder choices 64 Mutual.prior mutual_rows

theorem mutual_schema_count : mutualSchemas.length = 3 := by
  rw [mutualSchemas, Package.schemas_length]
  rfl

theorem mutual_signature_formed :
    (Package.signature Mutual.indices Mutual.parameters Mutual.names Mutual.admitted Mutual.prior).Formed
      Tower.rules := by
  apply Package.formed _ _ _ _ Tower.rules _ mutual_library_admitted
  intro item member
  simp only [Mutual.prior, NativeNaturalVectorFamilies.declarations, List.take_succ_cons,
    List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> rfl

private theorem vector_indices_free :
    Types.IndexFree (TypedControls.indexSyntax Bool) vectorNames.family := by
  intro context n expression environment free
  induction expression with
  | zero => exact .const (by decide)
  | «variable» reference =>
      induction reference with
      | here => exact free.1
      | there reference ih => exact ih environment.2 free.2
  | successor expression ih => exact .app (.const (by decide)) ih
  | addition left right ihLeft ihRight =>
      exact .app (.app (.const (by decide)) ihLeft) ihRight

private theorem vector_library_admitted :
    DeclarationAdmissionReplay.Admitted Tower.rules []
      (Package.library (TypedControls.indexSyntax Bool) (vectorParameters Bool) vectorNames
        (IndexedInductiveNatVec.Vectors.admitted Bool) vectorPrior) := by
  change DeclarationAdmissionReplay.Admitted Tower.rules [] (vectorPrior ++ vectorEntries Bool)
  rw [vector_entries_reference, List.take_append_drop]
  exact accepted_sound _ _ ((List.all_eq_true.mp DeclarationControls.all_verdicts) _
    (List.get_mem DeclarationControls.verdicts ⟨0, by decide⟩))

/-- The source generator now supplies the existing full informative
candidate, with positivity and complete constructor computation coverage. -/
noncomputable def vectorCandidate : Candidate Tower.rules :=
  Package.candidate (TypedControls.indexSyntax Bool) (vectorParameters Bool) vectorNames
    (IndexedInductiveNatVec.Vectors.admitted Bool) Tower.rules baseDecoder choices 64 vectorPrior
    vector_library_admitted
    (by
      intro item member
      simp only [vectorPrior, NativeNaturalVectorFamilies.declarations, List.take_succ_cons,
        List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> rfl)
    (by decide +kernel) vector_indices_free
    ⟨trivial, .head _⟩
    (by intro sort; cases sort; exact .const (by decide); exact .var 0)
    vector_rows

private theorem mutual_indices_free : Types.IndexFree Mutual.indices Mutual.names.family := by
  intro context n expression environment free
  cases expression
  · exact .const (by decide)
  · exact .app (.const (by decide)) (.const (by decide))

noncomputable def mutualCandidate : Candidate Tower.rules :=
  Package.candidate Mutual.indices Mutual.parameters Mutual.names Mutual.admitted
    Tower.rules baseDecoder choices 64 Mutual.prior mutual_library_admitted
    (by
      intro item member
      simp only [Mutual.prior, NativeNaturalVectorFamilies.declarations, List.take_succ_cons,
        List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> rfl)
    (by decide +kernel) mutual_indices_free trivial (fun sort => Empty.elim sort) mutual_rows

theorem candidate_vector_table_reference :
    Checking.table (Checking.candidateSchemas vectorCandidate) =
      NativeNaturalVectorFamilies.Checking.table.drop 2 := rfl

theorem candidate_mutual_inventory :
    mutualCandidate.iotaRules.map IotaRule.constructorName =
      [`Generated.Mutual.zero, `Generated.Mutual.odd, `Generated.Mutual.even] := rfl

private theorem mutual_prior_opaque : ∀ item ∈ Mutual.prior, item.2.value? = none := by
  intro item member
  simp only [Mutual.prior, NativeNaturalVectorFamilies.declarations, List.take_succ_cons,
    List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> rfl

noncomputable def publishMutual (fuel : Nat) :=
  Package.fromSource Mutual.indices Mutual.parameters Mutual.names Tower.rules baseDecoder choices
    fuel Mutual.prior mutual_prior_opaque mutual_indices_free trivial (fun sort => Empty.elim sort)
    IndexedInductiveExamples.Mutual.source

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem mutual_publication : (publishMutual 64).isSome = true := by decide +kernel

theorem mutual_publication_zero : publishMutual 0 = none := by
  have absent : (publishMutual 0).isSome = false := by decide +kernel
  cases found : publishMutual 0 with
  | none => rfl
  | some output => simp [found] at absent

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem aliased_names_not_published :
    (Package.fromSource Mutual.indices Mutual.parameters Mutual.duplicateNames Tower.rules baseDecoder choices
      64 Mutual.prior mutual_prior_opaque mutual_indices_free trivial (fun sort => Empty.elim sort)
      IndexedInductiveExamples.Mutual.source).isSome = false := by decide +kernel

theorem published_mutual_preserves_source (shape : Admitted Mutual.sourceInterface [])
    (output : Candidate Tower.rules) (accepted : publishMutual 64 = some (shape, output)) :
    shape.constructors.map quoteConstructor = IndexedInductiveExamples.Mutual.source.values ∧
      Checking.table (Checking.candidateSchemas output) =
        Package.table Mutual.indices Mutual.parameters Mutual.names shape :=
  Package.fromSource_sound Mutual.indices Mutual.parameters Mutual.names Tower.rules baseDecoder choices
    64 Mutual.prior mutual_prior_opaque mutual_indices_free trivial (fun sort => Empty.elim sort)
    IndexedInductiveExamples.Mutual.source shape output accepted

open ModuleSource in
/-- The actual textual fixture selects the admitted source behind this
candidate. This statement does not assert general parser completeness. -/
theorem text_candidate_source :
    (IndexedNatVecSource.admitModule Bool IndexedNatVecSourceControls.names
      IndexedNatVecSourceControls.IndexedNatVec.module).map
        (Package.table (TypedControls.indexSyntax Bool) (vectorParameters Bool) vectorNames) =
      some (Checking.table (Checking.candidateSchemas vectorCandidate)) := by
  rw [IndexedNatVecSourceControls.text_admitted]
  rfl

abbrev runtimeTable := NativeNaturalVectorFamilies.Checking.table.drop 2

/-- The executable specialization uses independently represented reference
syntax; its equality to the full generated typed table is proved above. -/
def replay (enabled : Fin runtimeTable.length → Bool) {n : Nat}
    (row : Nat) (arguments : List (Tower.Tm n)) :=
  SchemaTableConversionCode.decode runtimeTable enabled ⟨row, arguments⟩

def nilArguments : List (Tower.Tm 4) := List.ofFn (fun i : Fin 4 => .var i)
def consArguments : List (Tower.Tm 7) := List.ofFn (fun i : Fin 7 => .var i)

def verdicts : List (String × Bool) := [
  ("nil complete receipt", (replay (fun _ => true) 0 nilArguments).isSome),
  ("cons complete receipt retains explicit parameter", (replay (fun _ => true) 1 consArguments).isSome),
  ("profile-disabled nil refused", (replay (fun _ => false) 0 nilArguments).isNone),
  ("profile can enable nil without renumbering cons", (replay (fun i => i.val == 0) 1 consArguments).isNone),
  ("profile can enable cons at original position", (replay (fun i => i.val == 1) 1 consArguments).isSome),
  ("missing payload assignment refused", (replay (fun _ => true) 1 (consArguments.take 6)).isNone),
  ("extra assignment refused", (replay (fun _ => true) 0 (nilArguments ++ [.var 0])).isNone),
  ("unknown occurrence refused", (replay (fun _ => true) 2 nilArguments).isNone),
  ("nil assignment cannot cite cons", (replay (fun _ => true) 1 nilArguments).isNone),
  ("cons assignment cannot cite nil", (replay (fun _ => true) 0 consArguments).isNone),
  ("mutual rows formed before iota", Package.checkRows Mutual.indices Mutual.parameters Mutual.names
    Mutual.admitted Tower.rules baseDecoder choices 64 Mutual.prior),
  ("zero budget does not certify mutual rows", !(Package.checkRows Mutual.indices Mutual.parameters Mutual.names
    Mutual.admitted Tower.rules baseDecoder choices 0 Mutual.prior))]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem all_verdicts : verdicts.all Prod.snd = true := by decide +kernel

#eval verdicts
#print axioms vector_rows
#print axioms vector_table_reference
#print axioms mutual_signature_formed
#print axioms all_verdicts
#print axioms vectorCandidate
#print axioms mutualCandidate
#print axioms text_candidate_source
#print axioms mutual_publication
#print axioms published_mutual_preserves_source

end Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.PackageControls
