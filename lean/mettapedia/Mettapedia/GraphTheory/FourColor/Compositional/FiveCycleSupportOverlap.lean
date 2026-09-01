import Mettapedia.GraphTheory.FourColor.Compositional.FiveCycleBoundaryClosure
import Mettapedia.GraphTheory.FourColor.Compositional.FiveCycleColorClass

/-!
# Exact support overlap from five-cycle closure

This file is the consumer-facing semantic assembly of the short five-cycle
argument.  A shore realizes a primary or secondary behaviour when its exact
Tait support contains a boundary word in the corresponding colour orbit.  If
both shore languages satisfy the two abstract closure laws, the five-cycle
propagation theorem produces a common behaviour; colour-orbit invariance then
upgrades that behaviour to a literal common supported word.

The planar Kempe argument and the smaller-side surgery belong upstream: their
job is precisely to construct the two `Closure` values consumed here.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace FiveCycleSupportOverlap

open BoundaryColorOrbit
open BoundaryKempeSwitch
open FiveCycleBoundaryClosure
open FiveCycleColorClass
open GoertzelV24PortTangleGluing
open GoertzelV24PortTangleGluing.PortTangle

universe u

/-- An exact five-port support realizes the primary colour orbit at one cyclic
position. -/
def RealizesPrimary
    (support : Set (Fin 5 → {color : Color // color ≠ 0}))
    (index : Fin 5) : Prop :=
  ∃ word, word ∈ support ∧ Primary index (colorsOfBoundaryWord word)

/-- An exact five-port support realizes the secondary colour orbit at one
cyclic position. -/
def RealizesSecondary
    (support : Set (Fin 5 → {color : Color // color ≠ 0}))
    (index : Fin 5) : Prop :=
  ∃ word, word ∈ support ∧ Secondary index (colorsOfBoundaryWord word)

/-- **Five-cycle closure implies literal exact-support overlap.**

The only non-semantic inputs are the two closure structures and one realized
primary behaviour on each side.  In particular, no boundary-word catalogue is
part of this theorem. -/
theorem exists_common_word_of_closure
    {V I P V' I' P' : Type u}
    [Fintype V] [Fintype I] [Fintype P]
    [DecidableEq V] [DecidableEq I] [DecidableEq P]
    [Fintype V'] [Fintype I'] [Fintype P']
    [DecidableEq V'] [DecidableEq I'] [DecidableEq P']
    (leftOrder : Fin 5 ≃ P) (leftTangle : PortTangle V I P)
    (rightOrder : Fin 5 ≃ P') (rightTangle : PortTangle V' I' P')
    (leftClosure : Closure
      (RealizesPrimary (supportInCoordinates leftOrder leftTangle))
      (RealizesSecondary (supportInCoordinates leftOrder leftTangle)))
    (rightClosure : Closure
      (RealizesPrimary (supportInCoordinates rightOrder rightTangle))
      (RealizesSecondary (supportInCoordinates rightOrder rightTangle)))
    (leftNonempty : ∃ index,
      RealizesPrimary (supportInCoordinates leftOrder leftTangle) index)
    (rightNonempty : ∃ index,
      RealizesPrimary (supportInCoordinates rightOrder rightTangle) index) :
    ∃ common,
      common ∈ supportInCoordinates leftOrder leftTangle ∧
      common ∈ supportInCoordinates rightOrder rightTangle := by
  by_contra hcommon
  apply not_pointwise_disjoint leftClosure rightClosure
      leftNonempty rightNonempty
  constructor
  · intro index hoverlap
    rcases hoverlap with
      ⟨⟨left, hleftSupport, hleftClass⟩,
       ⟨right, hrightSupport, hrightClass⟩⟩
    exact hcommon (exists_common_word_of_equivalent
      leftOrder leftTangle rightOrder rightTangle
      hleftSupport hrightSupport
      (equivalent_of_primary hleftClass hrightClass))
  · intro index hoverlap
    rcases hoverlap with
      ⟨⟨left, hleftSupport, hleftClass⟩,
       ⟨right, hrightSupport, hrightClass⟩⟩
    exact hcommon (exists_common_word_of_equivalent
      leftOrder leftTangle rightOrder rightTangle
      hleftSupport hrightSupport
      (equivalent_of_secondary hleftClass hrightClass))

end FiveCycleSupportOverlap

end Mettapedia.GraphTheory.FourColor.Compositional
