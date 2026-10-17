import Mettapedia.GSLT.Contracts.AuthorityControls
import Mettapedia.GSLT.Core.NonFactorization
import Mathlib.Data.Finset.Basic

/-!
# Six contract dimensions are independent

A contract for a component can be read along six dimensions: what it visibly
does (behaviour), what it costs, what authority it exports, what it does to
shared state that others may observe (interaction), how its commit decisions
depend on what others do (transaction), and whether it can stutter forever
(progress).  A dimension can be deleted from a contract only if the other
dimensions determine it.  This module shows that none can: over one fixed
semantics, for each dimension there are two programs that agree on the other
five and differ on it (`independent`, `not_factors`).

## The semantics

`Prog` is a small language of service programs over a shared store of items:
visible events, administrative work, an administrative loop, internal choice,
exported access rights, writes to the store, and a presence test.  `runs`
gives every maximal run of a program from a store, with an environment that
acts on the store before each step.  A run records its visible trace, its work,
the access it exports, its own store changes, and whether it diverges.  This is
the traces-and-divergences reading of nondeterministic processes, enriched
with work, authority and writes.  Internal choice is demonic: a program that
may loop may diverge.

## The readouts

* **behaviour**: every prefix of every visible trace, in isolation;
* **cost**: the work of every completed run;
* **authority**: the access exported by every completed run;
* **interaction**: the store changes made by every completed run;
* **transaction**: the commit and abort decisions of every completed run while
  the environment inserts the probed item;
* **progress**: the traces after which a run may diverge.

## The separating pairs

* behaviour: a fault before the answer, against administration before it;
* cost: the answer, against administration and then the answer;
* authority: the same answer exporting a read right or the consume right;
* interaction: writing and removing a scratch item, against administration of
  the same work; both leave the store as it was;
* transaction: validating the absence of the probed item, against validating
  only the presence of the returned item; both commit in isolation;
* progress: an answer or a loop, against an answer either way.

Interaction and transaction are the guarantee and the rely of one
rely–guarantee claim, and authority lives in the same kind of separation
algebra (`Mettapedia.GSLT.Contracts.RelyGuaranteeClaims`); independence of the
dimensions does not require a separate kind of structure for each.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.Dimensions

open Mettapedia.GSLT.Core.NonFactorization

/-- Visible events. -/
inductive Event where
  | served
  | fault
  | commit
  | abort
  deriving DecidableEq, Repr

/-- Items of the shared store. -/
inductive Item where
  | base
  | probe
  | scratch
  deriving DecidableEq, Repr

/-- The shared store. -/
abbrev Store := List Item

/-- **Service programs.** -/
inductive Prog where
  | done
  | emit (event : Event) (next : Prog)
  | tick (next : Prog)
  | spin
  | choose (left right : Prog)
  | grant (right : Access) (next : Prog)
  | put (item : Item) (next : Prog)
  | drop (item : Item) (next : Prog)
  | ifPresent (item : Item) (yes no : Prog)
  deriving DecidableEq, Repr

/-- One maximal run. -/
structure Outcome where
  trace : List Event
  work : ℕ
  exported : Access
  writes : List (Store × Store)
  diverged : Bool
  deriving DecidableEq, Repr

/-- Every maximal run of a program; the environment acts on the store before
each step. -/
def runs (environment : Store → Store) : Prog → Store → List Outcome
  | .done, _ => [⟨[], 0, 0, [], false⟩]
  | .emit event next, s =>
      (runs environment next (environment s)).map fun o =>
        { o with trace := event :: o.trace, work := o.work + 1 }
  | .tick next, s =>
      (runs environment next (environment s)).map fun o => { o with work := o.work + 1 }
  | .spin, _ => [⟨[], 0, 0, [], true⟩]
  | .choose left right, s => runs environment left s ++ runs environment right s
  | .grant right next, s =>
      (runs environment next s).map fun o => { o with exported := right + o.exported }
  | .put item next, s =>
      (runs environment next (environment s ++ [item])).map fun o =>
        { o with work := o.work + 1, writes := (environment s, environment s ++ [item]) :: o.writes }
  | .drop item next, s =>
      (runs environment next ((environment s).erase item)).map fun o =>
        { o with work := o.work + 1,
                 writes := (environment s, (environment s).erase item) :: o.writes }
  | .ifPresent item yes no, s =>
      (if item ∈ environment s then runs environment yes (environment s)
        else runs environment no (environment s)).map fun o => { o with work := o.work + 1 }

/-- Every prefix of a list. -/
def prefixes {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: rest => [] :: (prefixes rest).map (x :: ·)

/-- The store a component starts from: the item it returns is present. -/
def initial : Store := [.base]

/-- No interference. -/
def isolated (s : Store) : Store := s

/-- The environment inserts the probed item. -/
def insertProbe (s : Store) : Store := if Item.probe ∈ s then s else s ++ [.probe]

/-- Commit decisions. -/
def isVerdict : Event → Bool
  | .commit | .abort => true
  | _ => false

def completed (environment : Store → Store) (p : Prog) : List Outcome :=
  (runs environment p initial).filter fun o => !o.diverged

/-- **The six readouts.** -/
structure Readouts where
  behaviour : Finset (List Event)
  cost : Finset ℕ
  authority : Finset Access
  interaction : Finset (List (Store × Store))
  transaction : Finset (List Event)
  progress : Finset (List Event)

/-- Readouts are compared component by component. -/
instance : DecidableEq Readouts := fun r s =>
  decidable_of_iff
    (r.behaviour = s.behaviour ∧ r.cost = s.cost ∧ r.authority = s.authority ∧
      r.interaction = s.interaction ∧ r.transaction = s.transaction ∧ r.progress = s.progress)
    (by
      constructor
      · rintro ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩
        cases r
        cases s
        simp only at h₁ h₂ h₃ h₄ h₅ h₆
        subst h₁ h₂ h₃ h₄ h₅ h₆
        rfl
      · rintro rfl
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

def readouts (p : Prog) : Readouts where
  behaviour := ((runs isolated p initial).flatMap fun o => prefixes o.trace).toFinset
  cost := ((completed isolated p).map Outcome.work).toFinset
  authority := ((completed isolated p).map Outcome.exported).toFinset
  interaction := ((completed isolated p).map Outcome.writes).toFinset
  transaction := ((completed insertProbe p).map fun o => o.trace.filter isVerdict).toFinset
  progress := (((runs isolated p initial).filter Outcome.diverged).map Outcome.trace).toFinset

/-- The six dimensions. -/
inductive Dimension where
  | behaviour
  | cost
  | authority
  | interaction
  | transaction
  | progress
  deriving DecidableEq, Repr

/-- The readouts with one dimension deleted. -/
def Readouts.delete : Dimension → Readouts → Readouts
  | .behaviour, r => { r with behaviour := ∅ }
  | .cost, r => { r with cost := ∅ }
  | .authority, r => { r with authority := ∅ }
  | .interaction, r => { r with interaction := ∅ }
  | .transaction, r => { r with transaction := ∅ }
  | .progress, r => { r with progress := ∅ }

/-! ## The separating pairs -/

def faultFirst : Prog := .emit .fault (.emit .served .done)
def adminFirst : Prog := .tick (.emit .served .done)

def answer : Prog := .emit .served .done

def readAnswer : Prog := .grant .read answer
def consumeAnswer : Prog := .grant .consume answer

def scratchWrite : Prog := .put .scratch (.drop .scratch answer)
def quietWork : Prog := .tick (.tick answer)

def validatesAbsence : Prog := .ifPresent .probe (.emit .abort .done) (.emit .commit .done)
def validatesReturned : Prog := .ifPresent .base (.emit .commit .done) (.emit .abort .done)

def mayLoop : Prog := .choose answer .spin
def answersEither : Prog := .choose answer answer

/-- The pair separating one dimension. -/
def separatingPair : Dimension → Prog × Prog
  | .behaviour => (faultFirst, adminFirst)
  | .cost => (answer, adminFirst)
  | .authority => (readAnswer, consumeAnswer)
  | .interaction => (scratchWrite, quietWork)
  | .transaction => (validatesAbsence, validatesReturned)
  | .progress => (mayLoop, answersEither)

/-- **Each pair agrees on the other five dimensions and differs on its own.** -/
theorem separatingPair_spec (d : Dimension) :
    (readouts (separatingPair d).1).delete d = (readouts (separatingPair d).2).delete d ∧
      readouts (separatingPair d).1 ≠ readouts (separatingPair d).2 := by
  cases d <;> decide

/-- **No dimension is determined by the other five.** -/
def independent (d : Dimension) :
    NonTrivialFiber (fun p => (readouts p).delete d) readouts where
  left := (separatingPair d).1
  right := (separatingPair d).2
  sameShadow := (separatingPair_spec d).1
  differentValue := (separatingPair_spec d).2

theorem not_factors (d : Dimension) : ¬ Factors (fun p => (readouts p).delete d) readouts :=
  (independent d).not_factors

/-- The interaction pair leaves the store as it found it. -/
theorem interaction_pair_same_final_store :
    (runs isolated scratchWrite initial).length = 1 ∧
      ((runs isolated scratchWrite initial).map Outcome.writes).map
        (fun writes => writes.getLast?.map Prod.snd) = [some initial] := by
  decide

/-- The authority pair is separated by the frame order: the exported read right
cannot update to the consume right. -/
theorem authority_pair_frame :
    readouts readAnswer ≠ readouts consumeAnswer ∧ ¬ FrameUpdate Access.read Access.consume :=
  ⟨(separatingPair_spec .authority).2, Access.not_frameUpdate_read_consume⟩

/-! ## Axiom audit -/

#print axioms separatingPair_spec
#print axioms not_factors
#print axioms interaction_pair_same_final_store

end Mettapedia.GSLT.Contracts.Dimensions
