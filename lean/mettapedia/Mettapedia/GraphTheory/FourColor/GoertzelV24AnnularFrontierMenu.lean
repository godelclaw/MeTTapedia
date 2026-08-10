import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebRadialComponents

/-!
# Menu-B seed counts for annular frontier fibers

Addendum XXV of the current source reduces the frontier step to a statement
about a fixed good inner word: every nonempty fiber contains a Menu-B state.
Addendum VII gives the concrete graph formulation used here: for a majority
color pair, Menu B means that at least two distinct selected-pair components
meet the five-edge cap.

This file makes that condition a finite count of actual Tait edge colorings.
It deliberately records no externally chosen configuration data and does not
assert the Seed Lemma itself; the later corridor argument must prove its
positivity.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularFrontierMenu

open SimpleGraph
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebGoodWordCounts
open GoertzelV24ClosedWebRadialComponents

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

/-- The color names and exact multiplicities of a `(3,1,1)` good inner word.
The source calls the first color the majority color and the remaining two its
singleton colors. -/
def AnnularFrontierMajorityTriple (word : CAP5BoundaryWord)
    (majority singletonFirst singletonSecond : Color) : Prop :=
  IsTaitColorTriple majority singletonFirst singletonSecond ∧
    cap5BoundaryColorCount word majority = 3 ∧
    cap5BoundaryColorCount word singletonFirst = 1 ∧
    cap5BoundaryColorCount word singletonSecond = 1

/-- Extract the source's majority/singleton names from a good CAP5 word. -/
theorem exists_annularFrontierMajorityTriple_of_goodWord
    {word : CAP5BoundaryWord}
    (hgood : CAP5BoundaryWordHasColoredBlock311 word) :
    ∃ majority singletonFirst singletonSecond : Color,
      AnnularFrontierMajorityTriple word majority singletonFirst singletonSecond := by
  rcases exists_exact_colorCounts_of_coloredBlock311 hgood with
    ⟨majority, singletonFirst, singletonSecond, htriple,
      hmajority, hfirst, hsecond⟩
  exact ⟨majority, singletonFirst, singletonSecond,
    htriple, hmajority, hfirst, hsecond⟩

/-- A majority/singleton pair has the four active cap ports required by the
source's Menu-A/Menu-B dichotomy. -/
theorem AnnularFrontierMajorityTriple.activeSupport_majority_singletonFirst_card
    {word : CAP5BoundaryWord} {majority singletonFirst singletonSecond : Color}
    (htriple : AnnularFrontierMajorityTriple
      word majority singletonFirst singletonSecond) :
    (cap5ActiveSupport majority singletonFirst word).card = 4 := by
  rcases htriple with ⟨hcolors, hmajority, hfirst, _hsecond⟩
  have hne : majority ≠ singletonFirst := hcolors.2.2.2.1
  rw [cap5ActiveSupport_card_eq_add_colorCounts hne, hmajority, hfirst]

/-- The other majority/singleton pair likewise has four active cap ports. -/
theorem AnnularFrontierMajorityTriple.activeSupport_majority_singletonSecond_card
    {word : CAP5BoundaryWord} {majority singletonFirst singletonSecond : Color}
    (htriple : AnnularFrontierMajorityTriple
      word majority singletonFirst singletonSecond) :
    (cap5ActiveSupport majority singletonSecond word).card = 4 := by
  rcases htriple with ⟨hcolors, hmajority, _hfirst, hsecond⟩
  have hne : majority ≠ singletonSecond := hcolors.2.2.2.2.1
  rw [cap5ActiveSupport_card_eq_add_colorCounts hne, hmajority, hsecond]

/-- Addendum VII's component formulation of Menu B for one selected color
pair: two distinct components of the selected bichromatic support graph meet
the inner cap. -/
def AnnularFrontierMenuBForPair
    (data : AnnularBoundaryData G outerCount)
    (coloring : G.EdgeColoring Color) (first second : Color) : Prop :=
  ∃ left right : (colorPairSupportGraph coloring first second).ConnectedComponent,
    left ≠ right ∧
      (∃ inner : Fin 5,
        ComponentContainsInnerStub data coloring first second left inner) ∧
      ∃ inner : Fin 5,
        ComponentContainsInnerStub data coloring first second right inner

/-- A concrete Menu-B state of a coloring at the actual inner boundary word.
The disjunction is exactly the source's “some majority pair.” -/
def AnnularFrontierMenuBState
    (data : AnnularBoundaryData G outerCount)
    (coloring : G.EdgeColoring Color) : Prop :=
  ∃ majority singletonFirst singletonSecond : Color,
    AnnularFrontierMajorityTriple (data.innerBoundaryWord coloring)
      majority singletonFirst singletonSecond ∧
      (AnnularFrontierMenuBForPair data coloring majority singletonFirst ∨
        AnnularFrontierMenuBForPair data coloring majority singletonSecond)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A Menu-B state supplies a majority pair with its literal four active
inner cap ports, rather than a freely supplied finite interface datum. -/
theorem AnnularFrontierMenuBState.exists_majorityPair_activeSupport_card
    (data : AnnularBoundaryData G outerCount)
    (coloring : G.EdgeColoring Color)
    (hmenu : AnnularFrontierMenuBState data coloring) :
    ∃ majority singleton : Color,
      (cap5ActiveSupport majority singleton (data.innerBoundaryWord coloring)).card = 4 ∧
        AnnularFrontierMenuBForPair data coloring majority singleton := by
  rcases hmenu with ⟨majority, singletonFirst, singletonSecond,
    htriple, hfirst | hsecond⟩
  · exact ⟨majority, singletonFirst,
      htriple.activeSupport_majority_singletonFirst_card, hfirst⟩
  · exact ⟨majority, singletonSecond,
      htriple.activeSupport_majority_singletonSecond_card, hsecond⟩

/-- The finite fiber of actual Tait edge colorings with one fixed inner word.
This is the `F(w)` quantified by the Seed Lemma. -/
noncomputable def annularFrontierTaitFiber
    (data : AnnularBoundaryData G outerCount) (word : CAP5BoundaryWord) :
    Finset (G.EdgeColoring Color) := by
  classical
  exact Finset.univ.filter fun coloring =>
    IsTaitEdgeColoring G coloring ∧ data.innerBoundaryWord coloring = word

omit [DecidableEq V] in
/-- Membership in the literal source fiber is exactly proper Tait coloring
together with the fixed inner-word equation. -/
theorem mem_annularFrontierTaitFiber_iff
    (data : AnnularBoundaryData G outerCount) (word : CAP5BoundaryWord)
    (coloring : G.EdgeColoring Color) :
    coloring ∈ annularFrontierTaitFiber data word ↔
      IsTaitEdgeColoring G coloring ∧ data.innerBoundaryWord coloring = word := by
  classical
  simp [annularFrontierTaitFiber]

/-- The literal subset of a fiber consisting of its Menu-B seeds. -/
noncomputable def annularFrontierMenuBSeedFiber
    (data : AnnularBoundaryData G outerCount) (word : CAP5BoundaryWord) :
    Finset (G.EdgeColoring Color) := by
  classical
  exact (annularFrontierTaitFiber data word).filter
    (AnnularFrontierMenuBState data)

omit [DecidableEq V] in
/-- Membership in the seed fiber is the source's conjunction: a coloring is
in the fixed fiber and realizes Menu B for some majority pair. -/
theorem mem_annularFrontierMenuBSeedFiber_iff
    (data : AnnularBoundaryData G outerCount) (word : CAP5BoundaryWord)
    (coloring : G.EdgeColoring Color) :
    coloring ∈ annularFrontierMenuBSeedFiber data word ↔
      coloring ∈ annularFrontierTaitFiber data word ∧
        AnnularFrontierMenuBState data coloring := by
  classical
  simp [annularFrontierMenuBSeedFiber]

/-- The finite number of source-meaningful Menu-B seeds in one fixed fiber. -/
noncomputable def annularFrontierMenuBSeedCount
    (data : AnnularBoundaryData G outerCount) (word : CAP5BoundaryWord) : Nat :=
  (annularFrontierMenuBSeedFiber data word).card

omit [DecidableEq V] in
@[simp] theorem annularFrontierMenuBSeedCount_apply
    (data : AnnularBoundaryData G outerCount) (word : CAP5BoundaryWord) :
    annularFrontierMenuBSeedCount data word =
      (annularFrontierMenuBSeedFiber data word).card :=
  rfl

omit [DecidableEq V] in
/-- Positivity of the literal seed count is exactly the Seed Lemma's target
for this fiber: an actual Tait coloring at `word` realizing Menu B. -/
theorem annularFrontierMenuBSeedCount_pos_iff
    (data : AnnularBoundaryData G outerCount) (word : CAP5BoundaryWord) :
    0 < annularFrontierMenuBSeedCount data word ↔
      ∃ coloring : G.EdgeColoring Color,
        coloring ∈ annularFrontierTaitFiber data word ∧
          AnnularFrontierMenuBState data coloring := by
  constructor
  · intro hpositive
    rcases Finset.card_pos.mp hpositive with ⟨coloring, hcoloring⟩
    rcases (mem_annularFrontierMenuBSeedFiber_iff data word coloring).mp hcoloring with
      ⟨hfiber, hmenu⟩
    exact ⟨coloring, hfiber, hmenu⟩
  · rintro ⟨coloring, hfiber, hmenu⟩
    apply Finset.card_pos.mpr
    exact ⟨coloring,
      (mem_annularFrontierMenuBSeedFiber_iff data word coloring).mpr
        ⟨hfiber, hmenu⟩⟩

omit [DecidableEq V] in
/-- Count zero is the exact counterexample predicate used by the minimal
counterexample descent: the fixed fiber has no Menu-B state. -/
theorem annularFrontierMenuBSeedCount_eq_zero_iff
    (data : AnnularBoundaryData G outerCount) (word : CAP5BoundaryWord) :
    annularFrontierMenuBSeedCount data word = 0 ↔
      ∀ coloring : G.EdgeColoring Color,
        coloring ∈ annularFrontierTaitFiber data word →
          ¬ AnnularFrontierMenuBState data coloring := by
  constructor
  · intro hzero coloring hfiber hmenu
    have hpositive : 0 < annularFrontierMenuBSeedCount data word :=
      (annularFrontierMenuBSeedCount_pos_iff data word).mpr
        ⟨coloring, hfiber, hmenu⟩
    omega
  · intro hnone
    by_contra hne
    have hpositive : 0 < annularFrontierMenuBSeedCount data word :=
      Nat.pos_of_ne_zero hne
    rcases (annularFrontierMenuBSeedCount_pos_iff data word).mp hpositive with
      ⟨coloring, hfiber, hmenu⟩
    exact hnone coloring hfiber hmenu

/-- The boundary-level finite target of Addendum XXV.  A later construction
must supply the full annular-frontier hypotheses from the source before this
target can be discharged; this declaration only fixes the literal fiber and
count that those hypotheses must govern. -/
def AnnularFrontierBoundarySeedTarget
    (data : AnnularBoundaryData G outerCount) (word : CAP5BoundaryWord) : Prop :=
  CAP5BoundaryWordHasColoredBlock311 word →
    0 < outerCount →
      (annularFrontierTaitFiber data word).Nonempty →
        0 < annularFrontierMenuBSeedCount data word

end

end GoertzelV24AnnularFrontierMenu

end Mettapedia.GraphTheory.FourColor
