import Mettapedia.GSLT.LanguageDef.IndexedInductiveGuestTypes
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveElaboration

/-!
# Checked formation of every generated indexed computation row

The admitted constructor inventory fixes the telescope, endpoints and displayed
type of each request. The existing elaborator produces finite evidence and the
existing formation-sensitive checker replays it. No endpoint typing is supplied
as an input, and producer choices carry no proof authority.

Acceptance covers every source occurrence, including constructors with no
recursive fields. Failure, including exhausted fuel, only means that this
producer did not return accepted evidence; it does not establish nontypability.
These formed endpoints do not alone grant a declared computation rule authority.
An empty inventory checks vacuously; formation of the family and eliminator
declarations remains a separate obligation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.Formation

open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

universe u
variable {I : Interface.{u}} {Head : Type} {n : Nat}
variable (R : Rules Head) [DecidableEq Head]
    [DecidableRel R.headTyping] [DecidablePred R.isUniverse]
    [∀ u v w, Decidable (R.join u v w)] [DecidableRel R.cumulative]
    [DecidableRel R.headEq]
variable (decoder : StructuralConversionCode.RootDecoder R.computation)
    (choices : FormationSensitiveElaboration.Choices Head decoder.Code)
    (fuel : Nat) (indices : IndexSyntax I Head) (admitted : Admitted I [])
    (types : Types.TypeSyntax I Head n) (ambient : Ctx Head n) (recursor : Tm Head n)

/-- Both submissions are checked at the generated dependent context and type.
The occurrence selects an actual admitted constructor rather than a caller's
replacement schema. -/
def elaborateRow (occurrence : Fin admitted.constructors.length) :
    Option (FormationSensitiveElaboration.Submission Head decoder.Code
        (arity admitted occurrence + n) ×
      FormationSensitiveElaboration.Submission Head decoder.Code
        (arity admitted occurrence + n)) := do
  let context := Types.iotaContext indices admitted occurrence types ambient
  let endpoints := Types.iotaSchema indices admitted occurrence types recursor
  let expected := Types.iotaType indices admitted occurrence types
  let source ← FormationSensitiveElaboration.elaborate R decoder choices fuel
    context endpoints.1 expected
  let target ← FormationSensitiveElaboration.elaborate R decoder choices fuel
    context endpoints.2 expected
  return (source, target)

def rowCheck (occurrence : Fin admitted.constructors.length) : Bool :=
  (elaborateRow R decoder choices fuel indices admitted types ambient recursor occurrence).isSome

/-- Row publication is precisely the conjunction of the two existing
elaboration verdicts at the generated context and displayed type. -/
theorem rowCheck_eq (occurrence : Fin admitted.constructors.length) :
    rowCheck R decoder choices fuel indices admitted types ambient recursor occurrence =
      ((FormationSensitiveElaboration.elaborate R decoder choices fuel
        (Types.iotaContext indices admitted occurrence types ambient)
        (Types.iotaSchema indices admitted occurrence types recursor).1
        (Types.iotaType indices admitted occurrence types)).isSome &&
      (FormationSensitiveElaboration.elaborate R decoder choices fuel
        (Types.iotaContext indices admitted occurrence types ambient)
        (Types.iotaSchema indices admitted occurrence types recursor).2
        (Types.iotaType indices admitted occurrence types)).isSome) := by
  cases source : FormationSensitiveElaboration.elaborate R decoder choices fuel
      (Types.iotaContext indices admitted occurrence types ambient)
      (Types.iotaSchema indices admitted occurrence types recursor).1
      (Types.iotaType indices admitted occurrence types) <;>
    cases target : FormationSensitiveElaboration.elaborate R decoder choices fuel
      (Types.iotaContext indices admitted occurrence types ambient)
      (Types.iotaSchema indices admitted occurrence types recursor).2
      (Types.iotaType indices admitted occurrence types) <;>
    simp [rowCheck, elaborateRow, source, target]

/-- The finite inventory retains source ordinals even if two rows happen to
have equal endpoints or equal verdicts. -/
def inventory : List (Fin admitted.constructors.length × Bool) :=
  List.ofFn fun occurrence =>
    (occurrence, rowCheck R decoder choices fuel indices admitted types ambient recursor occurrence)

def check : Bool :=
  (inventory R decoder choices fuel indices admitted types ambient recursor).all Prod.snd

theorem inventory_length :
    (inventory R decoder choices fuel indices admitted types ambient recursor).length =
      admitted.constructors.length := by
  simp [inventory]

/-- Enumeration covers every constructor and preserves its exact ordinal. -/
theorem inventory_origins :
    (inventory R decoder choices fuel indices admitted types ambient recursor).map Prod.fst =
      List.ofFn (fun occurrence : Fin admitted.constructors.length => occurrence) := by
  simp [inventory, List.map_ofFn, Function.comp_def]

theorem inventory_contains (occurrence : Fin admitted.constructors.length) :
    (occurrence, rowCheck R decoder choices fuel indices admitted types ambient recursor occurrence) ∈
      inventory R decoder choices fuel indices admitted types ambient recursor :=
  List.mem_ofFn.mpr ⟨occurrence, rfl⟩

theorem check_iff :
    check R decoder choices fuel indices admitted types ambient recursor = true ↔
      ∀ occurrence, rowCheck R decoder choices fuel indices admitted types ambient recursor occurrence = true := by
  simp [check, inventory, List.all_eq_true, List.mem_ofFn]

theorem elaborateRow_sound (occurrence : Fin admitted.constructors.length)
    (submissions : FormationSensitiveElaboration.Submission Head decoder.Code
        (arity admitted occurrence + n) ×
      FormationSensitiveElaboration.Submission Head decoder.Code
        (arity admitted occurrence + n))
    (produced : elaborateRow R decoder choices fuel indices admitted types ambient recursor occurrence =
      some submissions) :
    FormationSensitive.Judgment R
        (Types.iotaContext indices admitted occurrence types ambient)
        (Types.iotaSchema indices admitted occurrence types recursor).1
        (Types.iotaType indices admitted occurrence types) ∧
      FormationSensitive.Judgment R
        (Types.iotaContext indices admitted occurrence types ambient)
        (Types.iotaSchema indices admitted occurrence types recursor).2
        (Types.iotaType indices admitted occurrence types) := by
  cases source : FormationSensitiveElaboration.elaborate R decoder choices fuel
      (Types.iotaContext indices admitted occurrence types ambient)
      (Types.iotaSchema indices admitted occurrence types recursor).1
      (Types.iotaType indices admitted occurrence types) with
  | none => simp [elaborateRow, source] at produced
  | some sourceSubmission =>
      cases target : FormationSensitiveElaboration.elaborate R decoder choices fuel
          (Types.iotaContext indices admitted occurrence types ambient)
          (Types.iotaSchema indices admitted occurrence types recursor).2
          (Types.iotaType indices admitted occurrence types) with
      | none => simp [elaborateRow, source, target] at produced
      | some targetSubmission =>
          exact ⟨FormationSensitiveElaboration.elaborate_sound R decoder choices fuel
            _ _ _ sourceSubmission source,
            FormationSensitiveElaboration.elaborate_sound R decoder choices fuel
              _ _ _ targetSubmission target⟩

/-- Successful inventory checking establishes both original judgments at
every generated row, with its entire dependent telescope retained. -/
theorem check_sound
    (accepted : check R decoder choices fuel indices admitted types ambient recursor = true)
    (occurrence : Fin admitted.constructors.length) :
    FormationSensitive.Judgment R
        (Types.iotaContext indices admitted occurrence types ambient)
        (Types.iotaSchema indices admitted occurrence types recursor).1
        (Types.iotaType indices admitted occurrence types) ∧
      FormationSensitive.Judgment R
        (Types.iotaContext indices admitted occurrence types ambient)
        (Types.iotaSchema indices admitted occurrence types recursor).2
        (Types.iotaType indices admitted occurrence types) := by
  have acceptedRow := (check_iff R decoder choices fuel indices admitted types ambient recursor).mp
    accepted occurrence
  cases produced : elaborateRow R decoder choices fuel indices admitted types ambient recursor occurrence with
  | none => simp [rowCheck, produced] at acceptedRow
  | some submissions =>
      exact elaborateRow_sound R decoder choices fuel indices admitted types
        ambient recursor occurrence submissions produced

/-- A zero budget produces no evidence even when the row is well-typed. -/
theorem elaborateRow_zero (occurrence : Fin admitted.constructors.length) :
    elaborateRow R decoder choices 0 indices admitted types ambient recursor occurrence = none := by
  simp [elaborateRow, FormationSensitiveElaboration.elaborate,
    FormationSensitiveElaboration.check]

#print axioms check_sound
#print axioms inventory_origins

end Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.Formation
