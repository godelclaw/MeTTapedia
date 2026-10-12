import Mettapedia.GSLT.Core.StepFree
import Mettapedia.GSLT.Logic.SaturatedRelativeBisimilarity
import Mettapedia.Machines.ReadCertifiedQueryReuse
import Mathlib.Algebra.Group.Action.End

/-!
# Read-certified reuse is observationally invisible under updates

States change by the action of a monoid of updates.  A configuration is a state
together with an optional cache entry; an update acts on the state and keeps
the entry, whose reads are validated when it is used.  A configuration answers
each query through its entry when the entry is admissible, and by fresh
evaluation otherwise.

* **Invisibility** (`cached_relEquiv_fresh`).  A recorded entry gives exactly
  the fresh answers after every sequence of updates, so a configuration that
  keeps the entry is related to the same state without it.  The proof is the
  reuse law `Supported.reuse_exact` read in every context.
* **Absence is a read** (`PositiveOnly.positiveOnly_separated`).  A validator
  that ignores lookups which found nothing keeps a stale answer once a later
  update supplies the missing value, so that configuration is separated from
  fresh evaluation by one insertion.  The validator that keeps every read,
  absent ones included, is related (`PositiveOnly.full_validator_related`).
  Complete reads of matching rows have the same shape: appending a matching
  row invalidates them (`RevisionDependencySet.matching_append_invalidates_complete_read`).

Under this contract the necessity of recording absence is not a choice of
cache layout: the states are separated by a permitted future update, so no
sound merge may identify them.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Bridges.Machines.ReadCertifiedQueryReuse

open Mettapedia.GSLT
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence
open Mettapedia.Machines.ReadOnlyQuery
open Mettapedia.Machines.ReadCertifiedQueryReuse

universe uM uState uCache

/-- Updates act on the state of a configuration and keep its cache. -/
def updateRules (M : Type uM) (State : Type uState) (Cache : Type uCache)
    [Monoid M] [MulAction M State] :
    ContextualRules.{uM, 0} (GSLT.stepFree (State × Cache)) where
  Context := M
  identity := 1
  compose := (· * ·)
  plug update configuration := (update • configuration.1, configuration.2)
  plug_identity configuration := by
    show ((1 : M) • configuration.1, configuration.2) = configuration
    rw [one_smul]
  plug_compose outer inner configuration := by
    show ((outer * inner) • configuration.1, configuration.2) =
      (outer • inner • configuration.1, configuration.2)
    rw [mul_smul]
  plug_resp _ := by
    intro left right equal
    have equal' : left = right := equal
    subst equal'
    rfl
  Rule := Empty
  fires _ _ _ := False
  fires_resp_left := fun _ impossible => impossible.elim
  fires_resp_right := fun impossible _ => impossible.elim
  fires_step := fun impossible => impossible.elim

section Invisibility

variable {Authority Query Key Value Answer : Type}
variable {M : Type uM} {State : Type uState} [Monoid M] [MulAction M State]
variable [DecidableEq Authority] [DecidableEq Query] [DecidableEq Value]

/-- The answer a configuration gives to a query: through its entry when it
has one, by fresh evaluation otherwise. -/
def answerOf (family : Supported.Family State Authority Query Key Value Answer) (query : Query) :
    State × Option (Entry Authority Query Key Value Answer) → Answer
  | (state, none) => (family.observe state query).answer
  | (state, some entry) => (Supported.reuse family state query entry).1

/-- The answers to every query, as observations of configurations. -/
def answerObservations (family : Supported.Family State Authority Query Key Value Answer) :
    ContextualRules.Observations (GSLT.stepFree
      (State × Option (Entry Authority Query Key Value Answer))) :=
  valueObservations (S := GSLT.stepFree (State × Option (Entry Authority Query Key Value Answer)))
    (answerOf family) (fun _ _ _ equal => congrArg _ (show _ = _ from equal))

/-- **A recorded entry is invisible.**  After every update, the configuration
that keeps the entry answers every query exactly as fresh evaluation does. -/
theorem cached_relEquiv_fresh (family : Supported.Family State Authority Query Key Value Answer)
    (state : State) (entry : Entry Authority Query Key Value Answer)
    (recorded : Supported.Recorded family entry) :
    (⊤ : AdmissibleClass (updateRules M State (Option (Entry Authority Query Key Value Answer)))).RelEquiv
      (answerObservations family) (state, some entry) (state, none) := by
  refine ((⊤ : AdmissibleClass (updateRules M State _)).relEquiv_valueObservations_iff_of_stepFree
    (answerOf family) (fun _ _ _ equal => congrArg _ (show _ = _ from equal))
    (GSLT.stepFree_not_step _)).mpr ?_
  intro (update : M) _ query
  exact Supported.reuse_exact family (update • state) query entry recorded

end Invisibility

/-! ## Controls: a lookup that found nothing -/

namespace PositiveOnly

/-- The store holds at most one value under its single key. -/
abbrev Store := Option Nat

/-- Answer `0` when the lookup finds nothing, `1` otherwise. -/
def lookupProgram : Program Unit (Option Nat) Nat :=
  .read () fun found => match found with
    | none => .pure 0
    | some _ => .pure 1

def memoryOf (store : Store) : Unit → Option Nat := fun _ => store

def freshAnswer (store : Store) : Nat := (run (memoryOf store) lookupProgram).answer

/-- A validator that checks only the reads which found a value. -/
def positiveOnlyAnswer (store : Store) (cached : Observation Unit (Option Nat) Nat) : Nat :=
  if checkReads (memoryOf store) (cached.reads.filter fun read => read.2.isSome) then cached.answer
  else freshAnswer store

/-- The validator that checks every read, absent lookups included. -/
def fullAnswer (store : Store) (cached : Observation Unit (Option Nat) Nat) : Nat :=
  if checkReads (memoryOf store) cached.reads then cached.answer else freshAnswer store

/-- The answer of a configuration under a validator. -/
def readout (validate : Store → Observation Unit (Option Nat) Nat → Nat) :
    Unit → Store × Option (Observation Unit (Option Nat) Nat) → Nat
  | _, (store, none) => freshAnswer store
  | _, (store, some cached) => validate store cached

def observationsOf (validate : Store → Observation Unit (Option Nat) Nat → Nat) :
    ContextualRules.Observations (GSLT.stepFree
      (Store × Option (Observation Unit (Option Nat) Nat))) :=
  valueObservations (S := GSLT.stepFree (Store × Option (Observation Unit (Option Nat) Nat)))
    (readout validate) (fun _ _ _ equal => congrArg _ (show _ = _ from equal))

/-- Updates are arbitrary functions on the store. -/
abbrev Update := Function.End Store

/-- The observation recorded on the empty store: answer `0`, read `none`. -/
def cachedAtEmpty : Observation Unit (Option Nat) Nat := run (memoryOf none) lookupProgram

abbrev rules := updateRules Update Store (Option (Observation Unit (Option Nat) Nat))

/-- **Dropping absent reads is unsound.**  One insertion separates the
positive-only cache from fresh evaluation. -/
theorem positiveOnly_separated :
    ¬ (⊤ : AdmissibleClass rules).RelEquiv (observationsOf positiveOnlyAnswer)
      (none, some cachedAtEmpty) (none, none) := by
  intro related
  have agree := ((⊤ : AdmissibleClass rules).relEquiv_valueObservations_iff_of_stepFree
    (readout positiveOnlyAnswer) (fun _ _ _ equal => congrArg _ (show _ = _ from equal))
    (GSLT.stepFree_not_step _)).mp related
  have inserted := agree (fun _ => some 5 : Update) (AdmissibleClass.top_admissible _) ()
  revert inserted
  decide

/-- **Keeping absent reads is sound.**  The validator that checks every read is
related to fresh evaluation under every update. -/
theorem full_validator_related :
    (⊤ : AdmissibleClass rules).RelEquiv (observationsOf fullAnswer)
      (none, some cachedAtEmpty) (none, none) := by
  refine ((⊤ : AdmissibleClass rules).relEquiv_valueObservations_iff_of_stepFree
    (readout fullAnswer) (fun _ _ _ equal => congrArg _ (show _ = _ from equal))
    (GSLT.stepFree_not_step _)).mpr ?_
  intro (update : Update) _ _
  show fullAnswer (update • (none : Store)) cachedAtEmpty = freshAnswer (update • (none : Store))
  generalize update • (none : Store) = store
  cases store with
  | none => decide
  | some _ => rfl

end PositiveOnly

end Mettapedia.GSLT.Bridges.Machines.ReadCertifiedQueryReuse
