import Mettapedia.GraphTheory.FourColor.GoertzelV24PhysicalClosedCountBridge

/-!
# The target boundary of physical right-language minimization

Restricting Myhill--Nerode suffix experiments from arbitrary supports to
physically realized tangles can collapse many raw support states.  This file
records the exact logical boundary of that optimization.  For a family of
literal open tangles, membership in the physical right language is equivalent
both to Tait colorability of the sewn rotation system and to nonempty
intersection of the two exact support sets.

Consequently the assertion that every physical right language is universal is
not an independent compression theorem: it is exactly the assertion that every
sewn member of the chosen family is Tait-colorable.  A small physical quotient
may still be computed and used, but its soundness cannot be inferred merely
from the fact that the suffixes are physical.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24PhysicalRightLanguageBoundary

open GoertzelV24ClosedCountReplacement
open GoertzelV24OpenTangleComposition
open GoertzelV24PhysicalClosedCountBridge

universe u

variable {A B V W I J L R : Type u}
  [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

/-- The physical right language of one inner tangle relative to a chosen
family of outside tangles.  A tester accepts precisely when the literal sewn
rotation system has a Tait coloring. -/
def physicalRightLanguage
    (left : A → OpenTangleData V I L)
    (right : B → OpenTangleData W J R)
    (matching : L ≃ R) (inner : B) : Set A :=
  {outer | ∃ coloring :
      ((left outer).composeRotationSystem (right inner) matching).EdgeColoring Color,
    ((left outer).composeRotationSystem (right inner) matching).IsTaitEdgeColoring
      coloring}

@[simp] theorem mem_physicalRightLanguage
    (left : A → OpenTangleData V I L)
    (right : B → OpenTangleData W J R)
    (matching : L ≃ R) (outer : A) (inner : B) :
    outer ∈ physicalRightLanguage left right matching inner ↔
      ∃ coloring :
        ((left outer).composeRotationSystem (right inner) matching).EdgeColoring Color,
      ((left outer).composeRotationSystem (right inner) matching).IsTaitEdgeColoring
        coloring :=
  Iff.rfl

/-- Physical right-language membership is exactly intersection of the literal
outside and inside Count supports. -/
theorem mem_physicalRightLanguage_iff_supports_meet
    (left : A → OpenTangleData V I L)
    (right : B → OpenTangleData W J R)
    (matching : L ≃ R) (outer : A) (inner : B) :
    outer ∈ physicalRightLanguage left right matching inner ↔
      ∃ word : L → Color,
        word ∈ outerSupport (leftClosedPortTangle (left outer)) ∧
          word ∈ innerSupport
            (rightClosedPortTangle (right inner) matching) := by
  calc
    outer ∈ physicalRightLanguage left right matching inner ↔
        ∃ coloring :
          ((left outer).composeRotationSystem (right inner) matching).EdgeColoring Color,
        ((left outer).composeRotationSystem (right inner) matching).IsTaitEdgeColoring
          coloring := Iff.rfl
    _ ↔ ClosedColorable (leftClosedPortTangle (left outer))
        (rightClosedPortTangle (right inner) matching) :=
      (closedColorable_iff_composeRotationSystem_taitColorable
        (left outer) (right inner) matching).symm
    _ ↔ ∃ word : L → Color,
        word ∈ outerSupport (leftClosedPortTangle (left outer)) ∧
          word ∈ innerSupport
            (rightClosedPortTangle (right inner) matching) :=
      closedColorable_iff _ _

/-- A physical right language is universal exactly when every tester in the
chosen outside family gives a Tait-colorable literal splice. -/
theorem physicalRightLanguage_eq_univ_iff
    (left : A → OpenTangleData V I L)
    (right : B → OpenTangleData W J R)
    (matching : L ≃ R) (inner : B) :
    physicalRightLanguage left right matching inner = Set.univ ↔
      ∀ outer, ∃ coloring :
        ((left outer).composeRotationSystem (right inner) matching).EdgeColoring Color,
      ((left outer).composeRotationSystem (right inner) matching).IsTaitEdgeColoring
        coloring := by
  simp only [Set.eq_univ_iff_forall, mem_physicalRightLanguage]

/-- **Circularity boundary.**  Universality of every physical right language
is exactly pairwise Tait colorability of every literal splice in the two
chosen families. -/
theorem all_physicalRightLanguages_universal_iff_all_splices_taitColorable
    (left : A → OpenTangleData V I L)
    (right : B → OpenTangleData W J R)
    (matching : L ≃ R) :
    (∀ inner,
        physicalRightLanguage left right matching inner = Set.univ) ↔
      ∀ outer inner, ∃ coloring :
        ((left outer).composeRotationSystem (right inner) matching).EdgeColoring Color,
      ((left outer).composeRotationSystem (right inner) matching).IsTaitEdgeColoring
        coloring := by
  constructor
  · intro huniversal outer inner
    exact (physicalRightLanguage_eq_univ_iff
      left right matching inner).1 (huniversal inner) outer
  · intro hcolorable inner
    exact (physicalRightLanguage_eq_univ_iff
      left right matching inner).2 (fun outer => hcolorable outer inner)

/-- The same boundary stated entirely in support language. -/
theorem all_physicalRightLanguages_universal_iff_all_supports_meet
    (left : A → OpenTangleData V I L)
    (right : B → OpenTangleData W J R)
    (matching : L ≃ R) :
    (∀ inner,
        physicalRightLanguage left right matching inner = Set.univ) ↔
      ∀ outer inner, ∃ word : L → Color,
        word ∈ outerSupport (leftClosedPortTangle (left outer)) ∧
          word ∈ innerSupport
            (rightClosedPortTangle (right inner) matching) := by
  constructor
  · intro huniversal outer inner
    apply (mem_physicalRightLanguage_iff_supports_meet
      left right matching outer inner).1
    rw [huniversal inner]
    exact Set.mem_univ outer
  · intro hmeet inner
    apply Set.eq_univ_iff_forall.mpr
    intro outer
    exact (mem_physicalRightLanguage_iff_supports_meet
      left right matching outer inner).2 (hmeet outer inner)

/-- If every physical splice in the family is colorable, all inner tangles
have the same (universal) right language.  Thus a one-state quotient under
this hypothesis is a consequence of the target assertion. -/
theorem physicalRightLanguages_eq_of_all_splices_taitColorable
    (left : A → OpenTangleData V I L)
    (right : B → OpenTangleData W J R)
    (matching : L ≃ R)
    (hcolorable : ∀ outer inner, ∃ coloring :
      ((left outer).composeRotationSystem (right inner) matching).EdgeColoring Color,
      ((left outer).composeRotationSystem (right inner) matching).IsTaitEdgeColoring
        coloring)
    (first second : B) :
    physicalRightLanguage left right matching first =
      physicalRightLanguage left right matching second := by
  rw [(physicalRightLanguage_eq_univ_iff left right matching first).2
      (fun outer => hcolorable outer first),
    (physicalRightLanguage_eq_univ_iff left right matching second).2
      (fun outer => hcolorable outer second)]

end GoertzelV24PhysicalRightLanguageBoundary

end Mettapedia.GraphTheory.FourColor
