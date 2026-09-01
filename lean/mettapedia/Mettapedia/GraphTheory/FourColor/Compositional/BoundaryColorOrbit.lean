import Mettapedia.GraphTheory.FourColor.Compositional.BoundaryKempeSwitch

/-!
# Boundary words modulo global colour names

Two exact boundary supports compose whenever they realize words in the same
orbit under a global equivalence of colours fixing zero.  The equivalence can
be applied to the realizing colouring on one side, producing a literal common
word.  This is independent of the number and order of boundary ports.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace BoundaryColorOrbit

open BoundaryKempeSwitch
open GoertzelV24PortTangleGluing
open GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24PortTanglePhysicalKempeClosure

universe u v w

variable {V I P : Type u} {Q : Type v}
  [Fintype V] [Fintype I] [Fintype P] [Fintype Q]
  [DecidableEq V] [DecidableEq I] [DecidableEq P] [DecidableEq Q]

/-- Apply one zero-fixing global colour equivalence coordinatewise. -/
def relabelBoundaryWord
    (relabel : Color ≃ Color) (hzero : relabel 0 = 0)
    (word : Q → {color : Color // color ≠ 0}) :
    Q → {color : Color // color ≠ 0} :=
  fun coordinate =>
    ⟨relabel (word coordinate).1, fun h =>
      (word coordinate).2 (relabel.injective (h.trans hzero.symm))⟩

/-- Two boundary words differ only by one global renaming of the three
nonzero Tait colours. -/
def Equivalent
    (left right : Q → {color : Color // color ≠ 0}) : Prop :=
  ∃ (relabel : Color ≃ Color) (hzero : relabel 0 = 0),
    relabelBoundaryWord relabel hzero left = right

theorem equivalent_refl
    (word : Q → {color : Color // color ≠ 0}) :
    Equivalent word word := by
  refine ⟨Equiv.refl Color, rfl, ?_⟩
  funext coordinate
  apply Subtype.ext
  rfl

/-- Exact support in arbitrary coordinates is invariant under global
zero-fixing colour equivalence. -/
theorem relabelBoundaryWord_mem_supportInCoordinates_iff
    (order : Q ≃ P) (T : PortTangle V I P)
    (relabel : Color ≃ Color) (hzero : relabel 0 = 0)
    (word : Q → {color : Color // color ≠ 0}) :
    relabelBoundaryWord relabel hzero word ∈ supportInCoordinates order T ↔
      word ∈ supportInCoordinates order T := by
  change (fun port => relabelBoundaryWord relabel hzero word
      (order.symm port)) ∈ GoertzelV24PortTangleCutParity.taitSupport T ↔
    (fun port => word (order.symm port)) ∈
      GoertzelV24PortTangleCutParity.taitSupport T
  let physicalWord := fun port : P => word (order.symm port)
  have heq : (fun port => relabelBoundaryWord relabel hzero word
      (order.symm port)) =
      GoertzelV24PortTanglePhysicalKempeClosure.relabelTaitWord
        relabel hzero physicalWord := by
    funext port
    apply Subtype.ext
    rfl
  rw [heq]
  exact GoertzelV24PortTanglePhysicalKempeClosure.relabelTaitWord_mem_taitSupport_iff
    T relabel hzero physicalWord

/-- If two exact supports realize colour-orbit-equivalent boundary words,
then they contain a literal common word after globally relabelling one
realizing colouring. -/
theorem exists_common_word_of_equivalent
    (leftOrder : Q ≃ P) (leftTangle : PortTangle V I P)
    {V' I' P' : Type w}
    [Fintype V'] [Fintype I'] [Fintype P']
    [DecidableEq V'] [DecidableEq I'] [DecidableEq P']
    (rightOrder : Q ≃ P') (rightTangle : PortTangle V' I' P')
    {left right : Q → {color : Color // color ≠ 0}}
    (hleft : left ∈ supportInCoordinates leftOrder leftTangle)
    (hright : right ∈ supportInCoordinates rightOrder rightTangle)
    (horbit : Equivalent left right) :
    ∃ common,
      common ∈ supportInCoordinates leftOrder leftTangle ∧
      common ∈ supportInCoordinates rightOrder rightTangle := by
  rcases horbit with ⟨relabel, hzero, heq⟩
  refine ⟨right, ?_, hright⟩
  rw [← heq]
  exact (relabelBoundaryWord_mem_supportInCoordinates_iff
    leftOrder leftTangle relabel hzero left).2 hleft

end BoundaryColorOrbit

end Mettapedia.GraphTheory.FourColor.Compositional
