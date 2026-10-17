import Mettapedia.GSLT.Contracts.ReifiedActions

/-!
# Rely–guarantee claims as authority

Jones's rely–guarantee method (*Tentative steps toward a development method
for interfering programs*, TOPLAS 1983) specifies a component by an assertion,
a rely relation bounding what the environment may do, and a guarantee relation
bounding what the component itself does.  Two components may run in parallel
when each guarantee lies within the other's rely.

The Views framework (Dinsdale-Young et al., POPL 2013, Definition 23 and
Lemma 1) reads such triples as authority.  Here they are a separation
algebra (`RGClaim.instSepAlgebra`):

* a claim is an assertion stable under its rely;
* claims combine by intersecting assertions and relies and joining guarantees;
* two claims are **separate exactly when they coexist** in Jones's sense
  (`separate_iff_coexist`): each guarantee lies within the other's rely;
* the empty claim asserts nothing, tolerates everything and does nothing.

A claim is reified to its assertion.  **Rely–guarantee axiom soundness**
(`actionPreserves_of_guarantee`): an action that stays within the claim's
guarantee and establishes a new stable assertion satisfies the action
judgement of `Mettapedia.GSLT.Contracts.ReifiedActions`.  Jones's parallel
rule is then the interleaving theorem `parallel` of that module, instantiated
at rely–guarantee claims.

So interference is not a separate kind of structure from ownership: both are
authority in a separation algebra, reified to states, with frame-preserving
actions.  They remain different *components* of a contract.  Ownership says
what a party holds; the rely says what it tolerates from others; the guarantee
says what it may do to them.  The product of two separation algebras
(`SeparationAlgebra.instProd`) carries both at once.

## Controls, on two Boolean cells

* Writers of different cells coexist (`writers_coexist`), and each write
  satisfies the judgement (`writeFirst_preserves`).
* A writer whose guarantee includes the other cell does not coexist with a
  reader that relies on that cell (`not_coexist_overlapping`).
* An action outside its own guarantee breaks a coexisting frame
  (`outside_guarantee_not_preserves`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts

open Mettapedia.GSLT.SeparationAlgebra
open scoped Mettapedia.GSLT.SeparationAlgebra

universe u

/-- **A rely–guarantee claim**: an assertion that is stable under the rely,
with a rely and a guarantee relation. -/
structure RGClaim (S : Type u) where
  assertion : Set S
  rely : S → S → Prop
  guarantee : S → S → Prop
  stable : ∀ s s', s ∈ assertion → rely s s' → s' ∈ assertion

namespace RGClaim

variable {S : Type u}

@[ext]
theorem ext {x y : RGClaim S} (assertion : x.assertion = y.assertion) (rely : x.rely = y.rely)
    (guarantee : x.guarantee = y.guarantee) : x = y := by
  cases x
  cases y
  cases assertion
  cases rely
  cases guarantee
  rfl

/-- The empty claim: asserts nothing, tolerates everything, does nothing. -/
instance : Zero (RGClaim S) :=
  ⟨{ assertion := Set.univ
     rely := fun _ _ => True
     guarantee := fun _ _ => False
     stable := fun _ _ _ _ => trivial }⟩

/-- Claims combine as threads composed in parallel. -/
instance : Add (RGClaim S) :=
  ⟨fun x y =>
    { assertion := x.assertion ∩ y.assertion
      rely := fun s s' => x.rely s s' ∧ y.rely s s'
      guarantee := fun s s' => x.guarantee s s' ∨ y.guarantee s s'
      stable := fun s s' holds relies =>
        ⟨x.stable s s' holds.1 relies.1, y.stable s s' holds.2 relies.2⟩ }⟩

@[simp] theorem zero_assertion : (0 : RGClaim S).assertion = Set.univ := rfl
@[simp] theorem zero_rely (s s' : S) : (0 : RGClaim S).rely s s' = True := rfl
@[simp] theorem zero_guarantee (s s' : S) : (0 : RGClaim S).guarantee s s' = False := rfl
@[simp] theorem add_assertion (x y : RGClaim S) :
    (x + y).assertion = x.assertion ∩ y.assertion := rfl
@[simp] theorem add_rely (x y : RGClaim S) (s s' : S) :
    (x + y).rely s s' = (x.rely s s' ∧ y.rely s s') := rfl
@[simp] theorem add_guarantee (x y : RGClaim S) (s s' : S) :
    (x + y).guarantee s s' = (x.guarantee s s' ∨ y.guarantee s s') := rfl

/-- **Jones's coexistence condition**: each guarantee lies within the other's
rely. -/
def Coexist (x y : RGClaim S) : Prop :=
  (∀ s s', x.guarantee s s' → y.rely s s') ∧ (∀ s s', y.guarantee s s' → x.rely s s')

/-- **Rely–guarantee claims form a separation algebra** whose separateness is
coexistence. -/
instance instSepAlgebra : SepAlgebra (RGClaim S) where
  Separate := Coexist
  separate_zero _ := ⟨fun _ _ _ => trivial, fun _ _ impossible => impossible.elim⟩
  separate_symm coexist := ⟨coexist.2, coexist.1⟩
  add_zero x := RGClaim.ext (Set.inter_univ _)
    (funext fun _ => funext fun _ => and_true _)
    (funext fun _ => funext fun _ => or_false _)
  add_comm _ := RGClaim.ext (Set.inter_comm _ _)
    (funext fun _ => funext fun _ => propext and_comm)
    (funext fun _ => funext fun _ => propext or_comm)
  add_assoc _ _ _ := RGClaim.ext (Set.inter_assoc _ _ _)
    (funext fun _ => funext fun _ => propext and_assoc)
    (funext fun _ => funext fun _ => propext or_assoc)
  separate_of_separate_add := by
    intro x y z coexist _
    exact ⟨fun s s' step => (coexist.1 s s' step).1,
      fun s s' step => coexist.2 s s' (Or.inl step)⟩
  separate_add_of_separate_add := by
    intro x y z coexist coexistYZ
    refine ⟨?_, ?_⟩
    · rintro s s' (step | step)
      · exact (coexist.1 s s' step).2
      · exact coexistYZ.1 s s' step
    · intro s s' step
      exact ⟨coexist.2 s s' (Or.inr step), coexistYZ.2 s s' step⟩

theorem separate_iff_coexist {x y : RGClaim S} : x ## y ↔ Coexist x y := Iff.rfl

/-- A claim is reified to its assertion. -/
def reify (x : RGClaim S) : Set S := x.assertion

/-- Replace the assertion of a claim, keeping its rely and guarantee. -/
def withAssertion (x : RGClaim S) (Q : Set S)
    (stableQ : ∀ s s', s ∈ Q → x.rely s s' → s' ∈ Q) : RGClaim S :=
  { assertion := Q, rely := x.rely, guarantee := x.guarantee, stable := stableQ }

/-- **Rely–guarantee axiom soundness**: an action that stays within the
claim's guarantee and establishes a stable assertion preserves every
coexisting frame. -/
theorem actionPreserves_of_guarantee (x : RGClaim S) (Q : Set S)
    (stableQ : ∀ s s', s ∈ Q → x.rely s s' → s' ∈ Q) (act : S → S → Prop)
    (within : ∀ s ∈ x.assertion, ∀ s', act s s' → x.guarantee s s')
    (establishes : ∀ s ∈ x.assertion, ∀ s', act s s' → s' ∈ Q) :
    ActionPreserves reify act x (x.withAssertion Q stableQ) := by
  intro r coexist s holds s' step
  refine ⟨coexist, establishes s holds.1 s' step, ?_⟩
  exact r.stable s s' holds.2 (coexist.1 s s' (within s holds.1 s' step))

end RGClaim

/-! ## Controls on two Boolean cells -/

namespace RGControls

open RGClaim

/-- Two Boolean cells. -/
abbrev State := Bool × Bool

/-- Only the first cell may change. -/
def firstOnly (s s' : State) : Prop := s'.2 = s.2

/-- Only the second cell may change. -/
def secondOnly (s s' : State) : Prop := s'.1 = s.1

/-- A writer of the first cell: it relies on nobody changing the first cell. -/
def writerFirst : RGClaim State :=
  { assertion := Set.univ, rely := secondOnly, guarantee := firstOnly,
    stable := fun _ _ _ _ => trivial }

/-- A reader of the second cell holding the value `false`: it relies on nobody
changing the second cell. -/
def readerSecond : RGClaim State :=
  { assertion := {s | s.2 = false}, rely := firstOnly, guarantee := fun s s' => s' = s,
    stable := fun s s' holds relies => by
      change s'.2 = false
      rw [relies]
      exact holds }

/-- A writer that may change both cells. -/
def writerBoth : RGClaim State :=
  { assertion := Set.univ, rely := fun s s' => s' = s, guarantee := fun _ _ => True,
    stable := fun _ _ _ _ => trivial }

/-- **Positive control**: a writer of the first cell and a reader of the second
coexist. -/
theorem writers_coexist : writerFirst ## readerSecond := by
  refine ⟨fun _ _ step => step, ?_⟩
  rintro s s' rfl
  rfl

/-- Write `true` into the first cell. -/
def writeFirst (s s' : State) : Prop := s' = (true, s.2)

/-- **Positive control**: the first-cell write satisfies the judgement and
establishes its own result. -/
theorem writeFirst_preserves :
    ActionPreserves reify writeFirst writerFirst
      (writerFirst.withAssertion Set.univ fun _ _ _ _ => trivial) :=
  actionPreserves_of_guarantee writerFirst Set.univ (fun _ _ _ _ => trivial) writeFirst
    (by rintro s - s' rfl; rfl) (fun _ _ _ _ => trivial)

/-- **Negative control**: a writer of both cells does not coexist with a
reader of the second cell. -/
theorem not_coexist_overlapping : ¬ writerBoth ## readerSecond := by
  rintro ⟨guaranteeWithinRely, -⟩
  have wrong := guaranteeWithinRely (false, false) (false, true) trivial
  cases wrong

/-- Write `true` into the second cell. -/
def writeSecond (s s' : State) : Prop := s' = (s.1, true)

/-- **Negative control**: an action outside its own guarantee breaks a
coexisting frame, although the frame relies only on what the guarantee
promised. -/
theorem outside_guarantee_not_preserves :
    ¬ ActionPreserves reify writeSecond writerFirst
      (writerFirst.withAssertion Set.univ fun _ _ _ _ => trivial) := by
  intro judgement
  obtain ⟨-, after⟩ := judgement readerSecond writers_coexist (false, false)
    ⟨trivial, rfl⟩ (false, true) rfl
  have wrong : (true : Bool) = false := after.2
  cases wrong

end RGControls

/-! ## Axiom audit -/

#print axioms RGClaim.instSepAlgebra
#print axioms RGClaim.actionPreserves_of_guarantee
#print axioms RGControls.writers_coexist
#print axioms RGControls.not_coexist_overlapping
#print axioms RGControls.outside_guarantee_not_preserves

end Mettapedia.GSLT.Contracts
