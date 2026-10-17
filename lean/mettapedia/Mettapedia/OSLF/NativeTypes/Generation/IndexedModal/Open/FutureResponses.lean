import Mettapedia.GSLT.Topos.PresheafPredicateHeyting
import Mettapedia.GSLT.Topos.PresheafPredicateQuantifierBaseChange

/-!
# Future-sensitive universal response classifiers

Requests lie over classifier parameters and a focus. A response is an
actual event lying over its request; a separate predicate imposes the
dependent target condition. Universal may membership retains the event
existential and quantifies over every future request. It does not assert
the existence of a natural section selecting response events.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.FutureResponses

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.GSLT.Topos

universe u v w

variable {C : Type u} [Category.{v} C]
variable {events requests parameters : C ⥤ Type w}

/-- The event image establishes existence without identifying different
events that share a request in the retained event carrier. -/
noncomputable def classifier (observe : events ⟶ requests) (project : requests ⟶ parameters)
    (rely : Subfunctor requests) (post : Subfunctor events) : Subfunctor parameters :=
  forallAlong project (rely ⇨ post.image observe)

/-- Independent response-family specification over every restriction. -/
def SourceMeaning (observe : events ⟶ requests) (project : requests ⟶ parameters)
    (rely : Subfunctor requests) (post : Subfunctor events)
    (world : C) (parameter : parameters.obj world) : Prop :=
  ∀ (future : C) (restriction : world ⟶ future) (request : requests.obj future),
    project.app future request = parameters.map restriction parameter →
    request ∈ rely.obj future →
    ∃ event : events.obj future, event ∈ post.obj future ∧ observe.app future event = request

theorem classifier_iff_source (observe : events ⟶ requests) (project : requests ⟶ parameters)
    (rely : Subfunctor requests) (post : Subfunctor events)
    (world : C) (parameter : parameters.obj world) :
    parameter ∈ (classifier observe project rely post).obj world ↔
      SourceMeaning observe project rely post world parameter := by
  constructor
  · intro holds future restriction request over requested
    have response := holds future restriction request over
    rw [← himpPointwise_eq_himp] at response
    have now := response future (𝟙 future)
    rw [Functor.map_id_apply] at now
    exact now requested
  · intro source future restriction request over
    rw [← himpPointwise_eq_himp]
    intro next further requested
    apply source next (restriction ≫ further) (requests.map further request) ?_ requested
    exact (project.naturality_apply further request).trans
      ((congrArg (parameters.map further) over).trans
        (parameters.map_comp_apply restriction further parameter).symm)

/-- Present requests are among the quantified future requests. -/
theorem current (observe : events ⟶ requests) (project : requests ⟶ parameters)
    (rely : Subfunctor requests) (post : Subfunctor events)
    {world : C} {parameter : parameters.obj world}
    (holds : parameter ∈ (classifier observe project rely post).obj world)
    (request : requests.obj world) (over : project.app world request = parameter)
    (requested : request ∈ rely.obj world) :
    ∃ event : events.obj world, event ∈ post.obj world ∧ observe.app world event = request := by
  apply (classifier_iff_source observe project rely post world parameter).mp holds
    world (𝟙 world) request ?_ requested
  simpa only [Functor.map_id_apply] using over

/-- Arbitrary context restrictions preserve the classifier. -/
theorem restrict (observe : events ⟶ requests) (project : requests ⟶ parameters)
    (rely : Subfunctor requests) (post : Subfunctor events)
    {world future : C} (restriction : world ⟶ future)
    {parameter : parameters.obj world}
    (holds : parameter ∈ (classifier observe project rely post).obj world) :
    parameters.map restriction parameter ∈ (classifier observe project rely post).obj future :=
  (classifier observe project rely post).map restriction holds

theorem source_restrict (observe : events ⟶ requests) (project : requests ⟶ parameters)
    (rely : Subfunctor requests) (post : Subfunctor events)
    {world future : C} (restriction : world ⟶ future)
    {parameter : parameters.obj world}
    (holds : SourceMeaning observe project rely post world parameter) :
    SourceMeaning observe project rely post future (parameters.map restriction parameter) :=
  (classifier_iff_source observe project rely post _ _).mp
    (restrict observe project rely post restriction
      ((classifier_iff_source observe project rely post _ _).mpr holds))

/-- Genuine displayed pullbacks transport the complete request and event
fibres. A commuting square without their lifting property is insufficient. -/
theorem baseChange {C : Type u} [Category.{v} C]
    {events requests parameters events' requests' parameters' : Cᵒᵖ ⥤ Type w}
    (observe : events ⟶ requests) (project : requests ⟶ parameters)
    (observe' : events' ⟶ requests') (project' : requests' ⟶ parameters')
    (eventMap : events' ⟶ events) (requestMap : requests' ⟶ requests)
    (parameterMap : parameters' ⟶ parameters)
    (eventSquare : IsPullback eventMap observe' observe requestMap)
    (requestSquare : IsPullback requestMap project' project parameterMap)
    (rely : Subfunctor requests) (post : Subfunctor events) :
    (classifier observe project rely post).preimage parameterMap =
      classifier observe' project' (rely.preimage requestMap) (post.preimage eventMap) := by
  unfold classifier
  rw [forallAlong_beckChevalley _ _ _ _ requestSquare, preimage_himp,
    image_beckChevalley _ _ _ _ eventSquare]

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.FutureResponses
