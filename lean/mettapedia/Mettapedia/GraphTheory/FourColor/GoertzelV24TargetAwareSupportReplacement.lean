import Mettapedia.GraphTheory.FourColor.GoertzelV24PhysicalClosedCountBridge

/-!
# Target-aware support replacement

Exact support equality is sufficient for a context-independent splice, but it
is stronger than zero-Count descent requires.  If the replacement's inner
support is merely contained in that of the removed piece, then every colouring
of the replacement splice would already colour the original splice.  Hence
non-colourability is preserved monotonically.

For one fixed exterior the sharp condition is weaker still: the replacement
support need only be disjoint from that exterior support.  The results below
record both statements and their literal `OpenTangleData` form.  They isolate
the target-aware two-dimensional construction that remains after exact
single-cell replacement fails.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24TargetAwareSupportReplacement

open GoertzelV24ClosedCountReplacement
open GoertzelV24OpenTangleComposition
open GoertzelV24PortTangleGluing
open GoertzelV24PhysicalClosedCountBridge

universe u

variable {V W W' I K K' J : Type u}

/-- Colourability is monotone in the support of the inner piece. -/
theorem closedColorable_of_innerSupport_subset
    (outside : PortTangle V I (PEmpty.{u + 1} ⊕ J))
    (original : PortTangle W K (J ⊕ PEmpty.{u + 1}))
    (replacement : PortTangle W' K' (J ⊕ PEmpty.{u + 1}))
    (hsubset : innerSupport replacement ⊆ innerSupport original) :
    ClosedColorable outside replacement → ClosedColorable outside original := by
  intro hcolorable
  apply (closedColorable_iff outside original).2
  obtain ⟨word, houtside, hreplacement⟩ :=
    (closedColorable_iff outside replacement).1 hcolorable
  exact ⟨word, houtside, hsubset hreplacement⟩

/-- **Monotone zero-Count replacement.**  Support inclusion, not equality,
already preserves non-colourability. -/
theorem not_closedColorable_of_innerSupport_subset
    (outside : PortTangle V I (PEmpty.{u + 1} ⊕ J))
    (original : PortTangle W K (J ⊕ PEmpty.{u + 1}))
    (replacement : PortTangle W' K' (J ⊕ PEmpty.{u + 1}))
    (hsubset : innerSupport replacement ⊆ innerSupport original)
    (hzero : ¬ ClosedColorable outside original) :
    ¬ ClosedColorable outside replacement :=
  fun hcolorable => hzero
    (closedColorable_of_innerSupport_subset outside original replacement
      hsubset hcolorable)

/-- The sharp fixed-exterior criterion: a closed splice has zero Count exactly
when its two support sets are disjoint. -/
theorem not_closedColorable_iff_disjoint
    (outside : PortTangle V I (PEmpty.{u + 1} ⊕ J))
    (inside : PortTangle W K (J ⊕ PEmpty.{u + 1})) :
    ¬ ClosedColorable outside inside ↔
      Disjoint (outerSupport outside) (innerSupport inside) := by
  rw [Set.disjoint_left]
  constructor
  · intro hzero word houtside hinside
    exact hzero ((closedColorable_iff outside inside).2
      ⟨word, houtside, hinside⟩)
  · intro hdisjoint hcolorable
    obtain ⟨word, houtside, hinside⟩ :=
      (closedColorable_iff outside inside).1 hcolorable
    exact hdisjoint houtside hinside

/-- If an admissible candidate is known to colour against the fixed exterior
while the original does not, its support cannot be contained in the original
support.  This is the exact witness forced by minimality. -/
theorem not_innerSupport_subset_of_original_zero_of_replacement_colorable
    (outside : PortTangle V I (PEmpty.{u + 1} ⊕ J))
    (original : PortTangle W K (J ⊕ PEmpty.{u + 1}))
    (replacement : PortTangle W' K' (J ⊕ PEmpty.{u + 1}))
    (hzero : ¬ ClosedColorable outside original)
    (hcolorable : ClosedColorable outside replacement) :
    ¬ innerSupport replacement ⊆ innerSupport original := by
  intro hsubset
  exact (not_closedColorable_of_innerSupport_subset
    outside original replacement hsubset hzero) hcolorable

/-! ## Genuine Tait-word and physical forms -/

variable {W'' K'' L : Type u}

/-- Inclusion of the finite genuine-word supports implies inclusion of the
raw colour-word supports. -/
theorem innerSupport_subset_of_taitInnerSupport_subset
    (original : PortTangle W K (L ⊕ EmptyPort.{u}))
    (replacement : PortTangle W'' K'' (L ⊕ EmptyPort.{u}))
    (hsubset : taitInnerSupport replacement ⊆ taitInnerSupport original) :
    innerSupport replacement ⊆ innerSupport original := by
  intro word hword
  obtain ⟨taitWord, htait, hforget⟩ :=
    exists_cutWord_of_mem_innerSupport replacement hword
  have horiginal := hsubset htait
  change cutWordColor taitWord ∈ innerSupport original at horiginal
  simpa [hforget] using horiginal

variable {X Y I' J' R R' : Type u}
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype I'] [DecidableEq I'] [Fintype J'] [DecidableEq J']
  [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
  [Fintype R'] [DecidableEq R']

/-- **Physical monotone replacement.**  A literal replacement whose genuine
Tait-word support is contained in the removed side's support preserves
non-colourability of the sewn rotation system. -/
theorem not_composeRotationSystem_taitColorable_of_taitInnerSupport_subset
    (left : OpenTangleData X I' L)
    (right : OpenTangleData Y J' R) (matching : L ≃ R)
    {Y' J'' : Type u} [Fintype Y'] [DecidableEq Y']
      [Fintype J''] [DecidableEq J'']
    (right' : OpenTangleData Y' J'' R') (matching' : L ≃ R')
    (hsupport :
      taitInnerSupport (rightClosedPortTangle right' matching') ⊆
        taitInnerSupport (rightClosedPortTangle right matching))
    (hzero : ¬ ∃ coloring :
        (left.composeRotationSystem right matching).EdgeColoring Color,
      (left.composeRotationSystem right matching).IsTaitEdgeColoring coloring) :
    ¬ ∃ coloring :
        (left.composeRotationSystem right' matching').EdgeColoring Color,
      (left.composeRotationSystem right' matching').IsTaitEdgeColoring coloring := by
  have habstractZero :
      ¬ ClosedColorable (leftClosedPortTangle left)
        (rightClosedPortTangle right matching) := by
    intro hcolorable
    exact hzero
      ((closedColorable_iff_composeRotationSystem_taitColorable
        left right matching).1 hcolorable)
  have habstractZero' :
      ¬ ClosedColorable (leftClosedPortTangle left)
        (rightClosedPortTangle right' matching') :=
    not_closedColorable_of_innerSupport_subset
      (leftClosedPortTangle left)
      (rightClosedPortTangle right matching)
      (rightClosedPortTangle right' matching')
      (innerSupport_subset_of_taitInnerSupport_subset
        (rightClosedPortTangle right matching)
        (rightClosedPortTangle right' matching') hsupport)
      habstractZero
  intro hcolorable
  exact habstractZero'
    ((closedColorable_iff_composeRotationSystem_taitColorable
      left right' matching').2 hcolorable)

end GoertzelV24TargetAwareSupportReplacement

end Mettapedia.GraphTheory.FourColor
