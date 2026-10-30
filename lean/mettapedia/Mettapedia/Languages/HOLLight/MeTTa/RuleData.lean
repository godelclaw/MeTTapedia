import Mettapedia.Languages.HOLLight.MeTTa.InferenceSchedule

/-!
# Reading and rebuilding the ten authored HOL Light requests

The data reader uses the existing request constructor and scheduler. Reading
selects a rule kind and retains its actual operands and ordered premise keys;
it does not establish the side conditions of an admitted invocation. Those
remain the source reader, cache authorization and original rule semantics.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.RuleData

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open InferenceSchedule

/-- Unused tuple positions have one canonical inert value. -/
def readRequest : Atom → Option (InferenceKind × Atom × Atom × Atom)
  | .expression [.symbol "REFL", term] => some (.refl, term, .symbol "None", .symbol "None")
  | .expression [.symbol "TRANS", first, second] => some (.trans, .symbol "None", first, second)
  | .expression [.symbol "MK_COMB", first, second] => some (.mkComb, .symbol "None", first, second)
  | .expression [.symbol "ABS", needle, first] => some (.abs, needle, first, .symbol "None")
  | .expression [.symbol "BETA", term] => some (.beta, term, .symbol "None", .symbol "None")
  | .expression [.symbol "ASSUME", term] => some (.assume, term, .symbol "None", .symbol "None")
  | .expression [.symbol "EQ_MP", first, second] => some (.eqMp, .symbol "None", first, second)
  | .expression [.symbol "DEDUCT_ANTISYM_RULE", first, second] =>
      some (.deductAntisym, .symbol "None", first, second)
  | .expression [.symbol "INST_TYPE", entries, first] => some (.instType, entries, first, .symbol "None")
  | .expression [.symbol "INST", entries, first] => some (.inst, entries, first, .symbol "None")
  | _ => none

def rebuild (view : InferenceKind × Atom × Atom × Atom) : Atom :=
  Premises.request view.1 view.2.1 view.2.2.1 view.2.2.2

/-- Rendering after reading preserves the complete submitted request. -/
theorem rebuild_readRequest {request : Atom} {view : InferenceKind × Atom × Atom × Atom}
    (read : readRequest request = some view) : rebuild view = request := by
  unfold readRequest at read
  split at read <;> cases read <;> rfl

theorem read_rebuild_request (kind : InferenceKind) (payload first second : Atom) :
    (readRequest (Premises.request kind payload first second)).map rebuild =
      some (Premises.request kind payload first second) := by
  cases kind <;> rfl

/-- Every actual invocation already uses the canonical unused fields. All
ten cases therefore recover the entire view, not just the displayed name. -/
theorem read_invocation_request {frame : Frame} {cache : CacheAuthorization.Cache}
    (invocation : Invocation frame cache) :
    readRequest invocation.request =
      some (invocation.kind, invocation.payload, invocation.first, invocation.second) := by
  cases invocation <;> rfl

def readPremises (request : Atom) : Option (List Atom) := do
  let view ← readRequest request
  return Premises.occurrences view.1 view.2.2.1 view.2.2.2

theorem readPremises_request (kind : InferenceKind) (payload first second : Atom) :
    readPremises (Premises.request kind payload first second) =
      some (Premises.occurrences kind first second) := by
  cases kind <;> rfl

theorem readPremises_invocation {frame : Frame} {cache : CacheAuthorization.Cache}
    (invocation : Invocation frame cache) :
    readPremises invocation.request = some invocation.occurrences :=
  readPremises_request invocation.kind invocation.payload invocation.first invocation.second

theorem repeated_premise_is_two_occurrences (key : Atom) :
    readPremises (.expression [.symbol "TRANS", key, key]) = some [key, key] := rfl

/-- Theory extension is not an eleventh primitive inference. -/
theorem axiom_is_not_primitive_request (label statement : Atom) :
    readRequest (.expression [.symbol "AXIOM", label, statement]) = none := by simp [readRequest]

theorem extra_operand_refused (term extra : Atom) :
    readRequest (.expression [.symbol "REFL", term, extra]) = none := by simp [readRequest]

#print axioms rebuild_readRequest
#print axioms read_invocation_request
#print axioms readPremises_invocation

end Mettapedia.Languages.HOLLight.MeTTa.RuleData
