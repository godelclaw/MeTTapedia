import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularFrontierMenuProfileSemantics
import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularFrontierMenuCapRestoration

/-!
# The cap-correct Menu predicate on the finite annular profile

The older profile predicate asks whether two active ports belong to different
components of the *open* tangle.  On a realizable good fibre that condition is
automatic and therefore cannot be the source's terminal test.

The source restores the pentagonal cap first.  The uniform profile already
contains everything needed to perform that finite operation: the boundary word
and the open selected-pair component table.  This file defines the corrected
profile predicate by composing that table with the cap pairing, and proves that
it agrees with the literal restored reachability relation.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularFrontierCapComposedProfileSemantics

open SimpleGraph
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24AnnularFrontierMenu
open GoertzelV24AnnularFrontierMenuCapMatching
open GoertzelV24AnnularFrontierMenuCapComposed
open GoertzelV24AnnularFrontierMenuCapRestoration

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

/-- The open-strand relation read from the finite Boolean component table. -/
def ProfileStrand (profile : AnnularFrontierMenuUniformProfile)
    (first second : Color) (i j : Fin 5) : Prop :=
  profile.connectionTable first second i j = true

/-- The source-correct Menu-B predicate for one colour pair, read solely from
the finite profile.  The witness `v` is the unique inactive cap position. -/
def CapComposedMenuBForPairOfProfile
    (profile : AnnularFrontierMenuUniformProfile)
    (first second : Color) : Prop :=
  ∃ v : Fin 5,
    InactivePosition profile.word first second v ∧
      CapComposedMenuB (ProfileStrand profile first second) v

/-- The complete cap-correct terminal predicate: one of the two
majority/singleton pairs has Menu B after cap restoration. -/
def CapComposedMenuBStateOfProfile
    (profile : AnnularFrontierMenuUniformProfile) : Prop :=
  ∃ majority singletonFirst singletonSecond : Color,
    AnnularFrontierMajorityTriple profile.word
      majority singletonFirst singletonSecond ∧
      (CapComposedMenuBForPairOfProfile profile majority singletonFirst ∨
        CapComposedMenuBForPairOfProfile profile majority singletonSecond)

/-- A four-element active support in `Fin 5` has a unique inactive position. -/
theorem exists_inactivePosition_of_activeSupport_card_four
    {word : CAP5BoundaryWord} {first second : Color}
    (hcard : (cap5ActiveSupport first second word).card = 4) :
    ∃ v : Fin 5, InactivePosition word first second v := by
  let active := cap5ActiveSupport first second word
  have hcompl : activeᶜ.card = 1 := by
    rw [Finset.card_compl, show Fintype.card (Fin 5) = 5 by decide, hcard]
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcompl
  refine ⟨v, ?_⟩
  constructor
  · have hvmem : v ∈ activeᶜ := by simp [hv]
    simpa [active, cap5ActiveSupport] using hvmem
  · intro i hfirst hsecond
    have himem : i ∈ activeᶜ := by
      simp [active, cap5ActiveSupport, hfirst, hsecond]
    rw [hv] at himem
    simpa using himem

/-- The first majority pair of a good `(3,1,1)` word has its cap-inactive
position. -/
theorem AnnularFrontierMajorityTriple.exists_inactive_first
    {word : CAP5BoundaryWord} {majority singletonFirst singletonSecond : Color}
    (htriple : AnnularFrontierMajorityTriple
      word majority singletonFirst singletonSecond) :
    ∃ v : Fin 5, InactivePosition word majority singletonFirst v :=
  exists_inactivePosition_of_activeSupport_card_four
    htriple.activeSupport_majority_singletonFirst_card

/-- The second majority pair likewise has its cap-inactive position. -/
theorem AnnularFrontierMajorityTriple.exists_inactive_second
    {word : CAP5BoundaryWord} {majority singletonFirst singletonSecond : Color}
    (htriple : AnnularFrontierMajorityTriple
      word majority singletonFirst singletonSecond) :
    ∃ v : Fin 5, InactivePosition word majority singletonSecond v :=
  exists_inactivePosition_of_activeSupport_card_four
    htriple.activeSupport_majority_singletonSecond_card

/-- Every true entry of a realizable profile's open-strand table joins active
positions, hence avoids the unique inactive position. -/
theorem profileStrand_active_of_uniformProfile
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (coloring : G.EdgeColoring Color) (first second : Color) {v : Fin 5}
    (hv : InactivePosition (data.innerBoundaryWord coloring) first second v)
    {i j : Fin 5}
    (hstrand : ProfileStrand
      (annularFrontierMenuUniformProfile data hdata coloring)
        first second i j) :
    i ≠ v ∧ j ≠ v := by
  have htrue :
      annularFrontierMenuConnectionTable data hdata coloring
        first second i j = true := by
    simpa [ProfileStrand, annularFrontierMenuUniformProfile] using hstrand
  obtain ⟨hi, hj, -⟩ :=
    (annularFrontierMenuConnectionTable_eq_true_iff
      data hdata coloring first second i j).mp htrue
  have hiActive : data.innerBoundaryWord coloring i = first ∨
      data.innerBoundaryWord coloring i = second := by
    simpa [cap5ActiveSupport] using hi
  have hjActive : data.innerBoundaryWord coloring j = first ∨
      data.innerBoundaryWord coloring j = second := by
    simpa [cap5ActiveSupport] using hj
  constructor
  · intro hiv
    subst i
    exact hiActive.elim hv.not_active.1 hv.not_active.2
  · intro hjv
    subst j
    exact hjActive.elim hv.not_active.1 hv.not_active.2

/-- The literal restored-cap predicate for an actual colouring, expressed at
the boundary-relation level: open selected components are read from the graph,
and the five cap edges are then restored literally. -/
def RestoredMenuBForPair
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (coloring : G.EdgeColoring Color) (first second : Color) : Prop :=
  ∃ v : Fin 5,
    InactivePosition (data.innerBoundaryWord coloring) first second v ∧
      RestoredMenuB
        (ProfileStrand (annularFrontierMenuUniformProfile data hdata coloring)
          first second) v

/-- **Cap-correct profile semantics for one pair.**  The corrected finite
profile predicate agrees exactly with the literal restored-cap reachability
predicate on every actual colouring. -/
theorem restoredMenuBForPair_iff_capComposedOfUniformProfile
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (coloring : G.EdgeColoring Color) (first second : Color) :
    RestoredMenuBForPair data hdata coloring first second ↔
      CapComposedMenuBForPairOfProfile
        (annularFrontierMenuUniformProfile data hdata coloring)
        first second := by
  constructor
  · rintro ⟨v, hv, hmenu⟩
    refine ⟨v, ?_, ?_⟩
    · simpa [annularFrontierMenuUniformProfile] using hv
    · exact (restoredMenuB_iff_capComposedMenuB
        (fun _ _ hs => profileStrand_active_of_uniformProfile
          data hdata coloring first second hv hs)).mp hmenu
  · rintro ⟨v, hv, hmenu⟩
    have hv' : InactivePosition
        (data.innerBoundaryWord coloring) first second v := by
      simpa [annularFrontierMenuUniformProfile] using hv
    refine ⟨v, hv', ?_⟩
    exact (restoredMenuB_iff_capComposedMenuB
      (fun _ _ hs => profileStrand_active_of_uniformProfile
        data hdata coloring first second hv' hs)).mpr hmenu

/-- Literal restored-cap Menu B for one of the two majority pairs. -/
def RestoredMenuBState
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (coloring : G.EdgeColoring Color) : Prop :=
  ∃ majority singletonFirst singletonSecond : Color,
    AnnularFrontierMajorityTriple (data.innerBoundaryWord coloring)
      majority singletonFirst singletonSecond ∧
      (RestoredMenuBForPair data hdata coloring majority singletonFirst ∨
        RestoredMenuBForPair data hdata coloring majority singletonSecond)

/-- **The source's corrected terminal test is a finite-profile predicate.** -/
theorem restoredMenuBState_iff_capComposedOfUniformProfile
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (coloring : G.EdgeColoring Color) :
    RestoredMenuBState data hdata coloring ↔
      CapComposedMenuBStateOfProfile
        (annularFrontierMenuUniformProfile data hdata coloring) := by
  constructor
  · rintro ⟨majority, singletonFirst, singletonSecond, htriple,
      hfirst | hsecond⟩
    · exact ⟨majority, singletonFirst, singletonSecond,
        by simpa [annularFrontierMenuUniformProfile] using htriple,
        Or.inl ((restoredMenuBForPair_iff_capComposedOfUniformProfile
          data hdata coloring majority singletonFirst).mp hfirst)⟩
    · exact ⟨majority, singletonFirst, singletonSecond,
        by simpa [annularFrontierMenuUniformProfile] using htriple,
        Or.inr ((restoredMenuBForPair_iff_capComposedOfUniformProfile
          data hdata coloring majority singletonSecond).mp hsecond)⟩
  · rintro ⟨majority, singletonFirst, singletonSecond, htriple,
      hfirst | hsecond⟩
    · exact ⟨majority, singletonFirst, singletonSecond,
        by simpa [annularFrontierMenuUniformProfile] using htriple,
        Or.inl ((restoredMenuBForPair_iff_capComposedOfUniformProfile
          data hdata coloring majority singletonFirst).mpr hfirst)⟩
    · exact ⟨majority, singletonFirst, singletonSecond,
        by simpa [annularFrontierMenuUniformProfile] using htriple,
        Or.inr ((restoredMenuBForPair_iff_capComposedOfUniformProfile
          data hdata coloring majority singletonSecond).mpr hsecond)⟩

/-- Equality of finite uniform profiles preserves the corrected source
terminal predicate. -/
theorem restoredMenuBState_iff_of_uniformProfile_eq
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (leftColoring rightColoring : G.EdgeColoring Color)
    (hprofile : annularFrontierMenuUniformProfile data hdata leftColoring =
      annularFrontierMenuUniformProfile data hdata rightColoring) :
    RestoredMenuBState data hdata leftColoring ↔
      RestoredMenuBState data hdata rightColoring := by
  rw [restoredMenuBState_iff_capComposedOfUniformProfile,
    restoredMenuBState_iff_capComposedOfUniformProfile, hprofile]

end

end GoertzelV24AnnularFrontierCapComposedProfileSemantics

end Mettapedia.GraphTheory.FourColor
