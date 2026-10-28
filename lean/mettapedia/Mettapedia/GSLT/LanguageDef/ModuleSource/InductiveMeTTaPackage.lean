import Mettapedia.GSLT.LanguageDef.ModuleSource.InductiveMeTTaData
import Mettapedia.GSLT.LanguageDef.IndexedInductiveGuestPackage
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedFamilyData

/-!
# Complete generated declaration observations for both authoring forms

The package contains the family, every constructor and the eliminator, and
one typed computation request per constructor occurrence. Its construction
uses the existing indexed generators. Checking those requests earns the
existing iota receipts; constructing or reading the data does not.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.InductiveMeTTaPackage

open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open IndexedInductive IndexedInductive.Guest
open Declaration Declaration.IndexedFamily

universe u
variable {I : Interface.{u}} {Head : Type} {n : Nat}

/-- Generate every displayed computation judgment before the checks that
earn its receipt. The parameter telescope remains part of each context. -/
def rows (indices : IndexSyntax I Head) (parameters : Declarations.Parameters I Head n)
    (names : Declarations.Names) (admitted : Admitted I []) : List (Data.Row Head) :=
  List.ofFn fun occurrence : Fin admitted.constructors.length =>
    ⟨arity admitted occurrence + n,
      Types.iotaContext indices admitted occurrence (parameters.types names) parameters.context,
      (Types.iotaSchema indices admitted occurrence (parameters.types names)
        (Package.recursor parameters names)).1,
      (Types.iotaSchema indices admitted occurrence (parameters.types names)
        (Package.recursor parameters names)).2,
      Types.iotaType indices admitted occurrence (parameters.types names)⟩

theorem rows_length (indices : IndexSyntax I Head) (parameters : Declarations.Parameters I Head n)
    (names : Declarations.Names) (admitted : Admitted I []) :
    (rows indices parameters names admitted).length = admitted.constructors.length := by
  simp [rows]

def generated (indices : IndexSyntax I Head) (parameters : Declarations.Parameters I Head n)
    (names : Declarations.Names) (admitted : Admitted I []) :=
  (Declarations.entries indices parameters names admitted, rows indices parameters names admitted)

section Checking
variable (indices : IndexSyntax I Head) (parameters : Declarations.Parameters I Head n)
    (names : Declarations.Names) (admitted : Admitted I [])
variable (base : Rules Head) [DecidableEq Head]
    [DecidableRel base.headTyping] [DecidablePred base.isUniverse]
    [∀ u v w, Decidable (base.join u v w)] [DecidableRel base.cumulative]
    [DecidableRel base.headEq]
variable (decoder : StructuralConversionCode.RootDecoder base.computation)
    (choices : Declarations.Choices base decoder) (fuel : Nat)
    (prior : List (DeclName × Entry Head))

/-- All fields, including context and displayed type, agree with the
independently checked schemas. Comparing endpoints alone would be weaker. -/
theorem rows_checked
    (accepted : Package.checkRows indices parameters names admitted base decoder choices fuel prior = true) :
    rows indices parameters names admitted =
      Data.schemaRows (Package.schemas indices parameters names admitted base decoder choices fuel prior accepted) := by
  simp only [rows, Data.schemaRows, Package.schemas, List.map_ofFn, Package.schema,
    Function.comp_def]

theorem generated_row_has_receipt
    (accepted : Package.checkRows indices parameters names admitted base decoder choices fuel prior = true)
    {row : Data.Row Head} (member : row ∈ rows indices parameters names admitted) :
    Nonempty (ComputationAuthority.ProofRelevantStepReceipt base
      (Package.signature indices parameters names admitted prior)
      (Package.computation indices parameters names admitted)
      row.2.1 row.2.2.1 row.2.2.2.1 row.2.2.2.2) := by
  rw [rows_checked indices parameters names admitted base decoder choices fuel prior accepted] at member
  exact Data.inspected_row_has_receipt _ member

end Checking

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open InductiveMeTTaData IndexedInductiveNatVec

/-- Interpret the authored declaration through the existing Nat/Vec
admission, then generate the complete guest package with the selected
universe, index interpretation, parameter telescope and public names. -/
noncomputable def fromBuilder (A : Type) (sourceNames : IndexedNatVecSource.Names)
    (indices : IndexSyntax (Vectors.interface A) Head)
    (parameters : Declarations.Parameters (Vectors.interface A) Head n)
    (names : Declarations.Names) (natural vector : Atom) := do
  let admitted ← admitBuilder A sourceNames natural vector
  pure (generated indices parameters names admitted)

noncomputable def fromBlock (A : Type) (sourceNames : IndexedNatVecSource.Names)
    (indices : IndexSyntax (Vectors.interface A) Head)
    (parameters : Declarations.Parameters (Vectors.interface A) Head n)
    (names : Declarations.Names) (natural vector : Atom) := do
  let admitted ← admitBlock A sourceNames natural vector
  pure (generated indices parameters names admitted)

theorem authoring_forms_agree (A : Type) (sourceNames : IndexedNatVecSource.Names)
    (indices : IndexSyntax (Vectors.interface A) Head)
    (parameters : Declarations.Parameters (Vectors.interface A) Head n)
    (names : Declarations.Names) (natural vector : InductiveSyntax.Family) :
    fromBlock A sourceNames indices parameters names (blockData natural) (blockData vector) =
      fromBuilder A sourceNames indices parameters names (familyData natural) (familyData vector) := by
  unfold fromBlock fromBuilder
  rw [two_forms_same_admission]

#print axioms rows_checked
#print axioms generated_row_has_receipt
#print axioms authoring_forms_agree

end Mettapedia.GSLT.LanguageDef.ModuleSource.InductiveMeTTaPackage
