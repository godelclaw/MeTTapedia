import Mettapedia.OSLF.Framework.IndexedModalFunctor
import Mettapedia.GSLT.Logic.ObservationSpans

/-!
# Span maps as modal maps

The OSLF modalities of a reduction span form a modal predicate theory (`spanTheory`): the diamond is
step-possibility, and the box is its right adjoint, the incoming universal. A span map pulls predicates
back, and this is a lax modal map from the target's theory to the source's (`SpanMap.laxModal`):
- the source diamond of a pulled-back predicate lies in the pulled-back diamond;
- a pulled-back box lies in the source box of the pulled-back predicate.

No lifting is needed. With both liftings, pullback commutes with the two modalities
(`diamond_pullback`, `box_pullback`), and the map is a morphism of modal predicate theories
(`SpanMap.exactModal`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ObservationSpans

open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor (ModalPredicateTheory)
open Mettapedia.OSLF.Framework.IndexedModalFunctor (ForwardModalPredicateTheory)

universe u e f

/-- The OSLF modalities of a reduction span. -/
def spanTheory {X : Type u} (span : ReductionSpan.{u, e} X) : ModalPredicateTheory.{u} where
  State := X
  diamond := derivedDiamond span
  box := derivedBox span
  galois := derived_galois span

namespace SpanMap

variable {X Y : Type u} {A : ReductionSpan.{u, e} X} {B : ReductionSpan.{u, f} Y}

/-- **A span map is a lax modal map**, pulling the target's predicates back to the source. -/
def laxModal (observation : SpanMap A B) :
    ForwardModalPredicateTheory.Hom ⟨spanTheory B⟩ ⟨spanTheory A⟩ where
  mapPred := CompleteLatticeHom.setPreimage observation.states
  map_diamond_lax predicate := by
    rintro state ⟨event, starts, holds⟩
    refine ⟨observation.events event, (observation.source_comm event).trans (congrArg _ starts), ?_⟩
    change predicate (B.target (observation.events event))
    rw [observation.target_comm]
    exact holds
  map_box_lax predicate := by
    intro state holds event ends
    have observed := holds (observation.events event)
      ((observation.target_comm event).trans (congrArg _ ends))
    change predicate (B.source (observation.events event)) at observed
    rw [observation.source_comm] at observed
    exact observed

/-- **With both liftings, a span map is a morphism of modal predicate theories.** -/
def exactModal (observation : SpanMap A B) (outgoing : observation.SourceLifts)
    (incoming : observation.TargetLifts) : ModalPredicateTheory.Hom (spanTheory B) (spanTheory A) where
  mapPred := CompleteLatticeHom.setPreimage observation.states
  map_diamond predicate := by
    ext state
    exact observation.diamond_pullback outgoing predicate state
  map_box predicate := by
    ext state
    exact observation.box_pullback incoming predicate state

end SpanMap

end Mettapedia.GSLT.ObservationSpans
