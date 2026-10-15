import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.Policies

/-!
# The grain of a location decides what is a wave

A wave is admitted by footprints, and a footprint is a set of locations.  So the
grain at which a store is read as locations decides which proposals are a wave.

A space can be read as one location that holds a bag, or by kinds, as one
location for each atom that holds its multiplicity
(`FootprintedSpaceTransactions.marking`, `markingRule`).  Local rules over
multiplicities with a decidable guard are steps (`Step.ofCountRule`), so the
development applies to both readings.

* **One location for the space.**  Two siblings that each add an atom to the
  space and answer without reading it write the same location.  The wave policy
  reports a conflict and publishes nothing
  (`AddOnly.space_grain_additions_conflict`), although the two additions replay in
  both orders with one result (`AddOnly.space_grain_additions_replay`).
* **One location for each kind.**  The same two siblings write two locations.
  They are independent, and the wave policy publishes both
  (`AddOnly.kind_grain_additions_are_a_wave`).
* **A sibling that reads the space after its addition** reads every kind it may
  see.  At the grain of kinds the two siblings are still not independent, and
  the wave policy reports the conflict (`AddOnly.kind_grain_readers_conflict`):
  the answers they gave from the snapshot are not the answers of any serial run.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction
open Mettapedia.GSLT.SeparationAlgebra

universe u

variable {Location : Type u} [DecidableEq Location]

/-- **Every local rule over multiplicities with a decidable guard is a step.**
The rule fires when its guard holds and every written location holds at least
what it consumes; the frame is the difference. -/
def Step.ofCountRule (rule : LocalRule Location ℕ) (decideGuard : DecidablePred rule.guard) :
    Step Location ℕ where
  rule := rule
  fire source :=
    if rule.guard source ∧ ∀ location ∈ rule.writes, rule.consumed location ≤ source location then
      some fun location => source location - rule.consumed location + rule.produced location
    else none
  fire_eq_some_iff := by
    intro source target
    constructor
    · intro fires
      split at fires
      · next enabled =>
        cases fires
        refine ⟨enabled.1, fun location => source location - rule.consumed location,
          fun _ => trivial, fun _ => trivial, ?_, ?_⟩
        · funext location
          show source location = rule.consumed location + (source location - rule.consumed location)
          by_cases written : location ∈ rule.writes
          · exact (add_tsub_cancel_of_le (enabled.2 location written)).symm
          · rw [rule.consumed_outside location written, tsub_zero, zero_add]
        · funext location
          show source location - rule.consumed location + rule.produced location =
            rule.produced location + (source location - rule.consumed location)
          exact add_comm _ _
      · cases fires
    · rintro ⟨guarded, frame, -, -, rfl, rfl⟩
      have enabled : rule.guard (rule.consumed + frame) ∧
          ∀ location ∈ rule.writes, rule.consumed location ≤ (rule.consumed + frame) location :=
        ⟨guarded, fun location _ => le_add_right le_rfl⟩
      rw [if_pos enabled]
      congr 1
      funext location
      show rule.consumed location + frame location - rule.consumed location +
          rule.produced location = rule.produced location + frame location
      rw [add_tsub_cancel_left, add_comm]

/-! ## Controls: two siblings that add an atom -/

namespace AddOnly

open Controls (Store empty)

/-- The atoms the two siblings add; at the grain of kinds, also the locations. -/
inductive Kind where
  | a
  | b
  deriving DecidableEq

/-- Add one occurrence of an atom, the space read by kinds. -/
def addKind (atom : Kind) : Step Kind ℕ :=
  Step.ofCountRule (markingRule 0 {atom}) fun _ => isTrue trivial

/-- A sibling at the grain of kinds: add its atom and answer with it. -/
def kindSibling (atom : Kind) : Region Kind ℕ Kind :=
  .step (addKind atom) (.answer (Readout.const atom))

/-- A sibling at the grain of kinds that reads the space after its addition: the
answer is the multiplicity of both kinds. -/
def kindReader (atom : Kind) : Region Kind ℕ (ℕ × ℕ) :=
  .step (addKind atom)
    (.answer ⟨{.a, .b}, fun state => (state .a, state .b),
      fun agrees => by rw [agrees Kind.a (by decide), agrees Kind.b (by decide)]⟩)

/-- The empty space, read by kinds. -/
def noKinds : Kind → ℕ := fun _ => 0

/-- A sibling with the space as one location: add its atom and answer with it. -/
def spaceSibling (atom : Kind) : Region Store (Multiset Kind) Kind :=
  .step (Step.addAtom .space atom) (.answer (Readout.const atom))

/-- The empty space, as one location. -/
def noAtoms : Network Store Kind := fun _ => 0

/-- **Positive, a wave at the grain of kinds**: the two additions write two
locations, they are independent, and the wave policy publishes both. -/
theorem kind_grain_additions_are_a_wave :
    (((Region.alternatives [kindSibling .a, kindSibling .b]).branchLocal noKinds).map
        Prod.snd).Pairwise Proposal.Independent ∧
      ((Region.alternatives [kindSibling .a, kindSibling .b]).observe Policy.publishWave
        noKinds).1 = [.a, .b] ∧
      ((Region.alternatives [kindSibling .a, kindSibling .b]).observe Policy.publishWave
        noKinds).2.map (fun world => (world .a, world .b)) = some (1, 1) := by
  decide

/-- **Negative, the same additions with the space as one location**: both write
that location, and the wave policy reports a conflict and publishes nothing. -/
theorem space_grain_additions_conflict :
    ¬ (((Region.alternatives [spaceSibling .a, spaceSibling .b]).branchLocal noAtoms).map
        Prod.snd).Pairwise Proposal.Independent ∧
      ((Region.alternatives [spaceSibling .a, spaceSibling .b]).observe Policy.publishWave
        noAtoms).2.isNone = true := by
  decide

/-- And yet the two additions replay in both orders with one result: the
conflict comes from the grain of the footprint and not from the additions. -/
theorem space_grain_additions_replay :
    (publishInOrder ((Region.alternatives [spaceSibling .a, spaceSibling .b]).branchLocal noAtoms)
        noAtoms).map (fun world => world .space) = some {.a, .b} ∧
      (publishInOrder ((Region.alternatives [spaceSibling .b, spaceSibling .a]).branchLocal noAtoms)
        noAtoms).map (fun world => world .space) = some {.a, .b} := by
  decide

/-- **Siblings that read the space after their addition conflict at the grain of
kinds too.**  Each answers with its own atom only, from the snapshot; each reads
the kind the other writes, so they are not independent and the wave policy
reports the conflict. -/
theorem kind_grain_readers_conflict :
    ((Region.alternatives [kindReader .a, kindReader .b]).observe Policy.publishWave noKinds).1 =
        [(1, 0), (0, 1)] ∧
      ((Region.alternatives [kindReader .a, kindReader .b]).observe Policy.publishWave
        noKinds).2.isNone = true := by
  decide

end AddOnly

#print axioms AddOnly.kind_grain_additions_are_a_wave
#print axioms AddOnly.space_grain_additions_conflict
#print axioms AddOnly.space_grain_additions_replay
#print axioms AddOnly.kind_grain_readers_conflict

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions
