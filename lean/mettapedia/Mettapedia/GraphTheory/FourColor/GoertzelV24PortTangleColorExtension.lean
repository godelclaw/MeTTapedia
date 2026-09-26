import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedCountReplacement

/-!
# Extending a colouring through a larger boundary support

An inclusion of inner supports gives a map on actual closed colourings. Split
the given colouring along the seam, retain its exterior colouring and boundary
word, choose a realization of that word in the target piece, and glue.

The exterior is preserved pointwise. Thus an extension of an open piece works
inside every already-coloured exterior, without a width bound or a Kempe
reachability assumption. This is the forward colouring construction underlying
one-sided support descent. The choice of an inner realization is noncomputable;
the gluing and restriction operations themselves are explicit.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelV24PortTangleColorExtension

open GoertzelV24PortTangleGluing
open GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24ClosedCountReplacement

universe u

variable {V W W' I K K' J : Type u}

/-- Enlarge the inner piece while retaining the given exterior colouring.
Support inclusion supplies an inner realization of the same seam word. -/
noncomputable def extendClosedColoring
    (outside : PortTangle V I (PEmpty.{u + 1} ⊕ J))
    (source : PortTangle W K (J ⊕ PEmpty.{u + 1}))
    (target : PortTangle W' K' (J ⊕ PEmpty.{u + 1}))
    (hsupport : innerSupport source ⊆ innerSupport target)
    (coloring : Col (series outside source) (Sum.elim PEmpty.elim PEmpty.elim)) :
    Col (series outside target) (Sum.elim PEmpty.elim PEmpty.elim) :=
  let parts := gluingEquiv outside source PEmpty.elim PEmpty.elim coloring
  let inside := Classical.choice (hsupport (show parts.1 ∈ innerSupport source from
    ⟨parts.2.2⟩))
  (gluingEquiv outside target PEmpty.elim PEmpty.elim).symm
    ⟨parts.1, parts.2.1, inside⟩

/-- The construction keeps the entire exterior colouring, including its seam
darts, rather than merely finding some colouring of the new composite. -/
theorem extendClosedColoring_preserves_exterior
    (outside : PortTangle V I (PEmpty.{u + 1} ⊕ J))
    (source : PortTangle W K (J ⊕ PEmpty.{u + 1}))
    (target : PortTangle W' K' (J ⊕ PEmpty.{u + 1}))
    (hsupport : innerSupport source ⊆ innerSupport target)
    (coloring : Col (series outside source) (Sum.elim PEmpty.elim PEmpty.elim)) :
    restrict₁ outside target (extendClosedColoring outside source target hsupport coloring).1 =
      restrict₁ outside source coloring.1 := by
  apply restrict₁_glueColoring

/-- Forward colourability transport is obtained from the actual colouring
extension, with no need to assume that the original graph is uncolourable. -/
theorem closedColorable_of_innerSupport_subset
    (outside : PortTangle V I (PEmpty.{u + 1} ⊕ J))
    (source : PortTangle W K (J ⊕ PEmpty.{u + 1}))
    (target : PortTangle W' K' (J ⊕ PEmpty.{u + 1}))
    (hsupport : innerSupport source ⊆ innerSupport target)
    (hcolorable : ClosedColorable outside source) :
    ClosedColorable outside target := by
  obtain ⟨coloring⟩ := hcolorable
  exact ⟨extendClosedColoring outside source target hsupport coloring⟩

end GoertzelV24PortTangleColorExtension
end Mettapedia.GraphTheory.FourColor
