import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.FutureResponses

/-!
# Substitution of universal response classifiers by actual pullbacks

Changing the parameter context pulls back requests, then their complete
event fibres. The classifier assembled from those changed carriers equals
inverse image of the original classifier. The squares are constructed
pullbacks, not assumptions about a pair of commuting readouts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.FutureResponses

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w
variable {C : Type u} [Category.{v} C]
variable {events requests parameters context : Cᵒᵖ ⥤ Type w}

noncomputable def changedRequests (project : requests ⟶ parameters)
    (incoming : context ⟶ parameters) : Cᵒᵖ ⥤ Type w := pullback project incoming

noncomputable def requestMap (project : requests ⟶ parameters)
    (incoming : context ⟶ parameters) : changedRequests project incoming ⟶ requests :=
  pullback.fst project incoming

noncomputable def changedProject (project : requests ⟶ parameters)
    (incoming : context ⟶ parameters) : changedRequests project incoming ⟶ context :=
  pullback.snd project incoming

noncomputable def changedEvents (observe : events ⟶ requests) (project : requests ⟶ parameters)
    (incoming : context ⟶ parameters) : Cᵒᵖ ⥤ Type w :=
  pullback observe (requestMap project incoming)

noncomputable def eventMap (observe : events ⟶ requests) (project : requests ⟶ parameters)
    (incoming : context ⟶ parameters) : changedEvents observe project incoming ⟶ events :=
  pullback.fst observe (requestMap project incoming)

noncomputable def changedObserve (observe : events ⟶ requests) (project : requests ⟶ parameters)
    (incoming : context ⟶ parameters) :
    changedEvents observe project incoming ⟶ changedRequests project incoming :=
  pullback.snd observe (requestMap project incoming)

noncomputable def changedClassifier (observe : events ⟶ requests) (project : requests ⟶ parameters)
    (incoming : context ⟶ parameters) (rely : Subfunctor requests) (post : Subfunctor events) :
    Subfunctor context :=
  classifier (changedObserve observe project incoming) (changedProject project incoming)
    (rely.preimage (requestMap project incoming))
    (post.preimage (eventMap observe project incoming))

/-- All request and receipt matching pairs exist in the changed context,
because both required squares are the actual chosen pullbacks. -/
theorem changedClassifier_exact (observe : events ⟶ requests) (project : requests ⟶ parameters)
    (incoming : context ⟶ parameters) (rely : Subfunctor requests) (post : Subfunctor events) :
    changedClassifier observe project incoming rely post =
      (classifier observe project rely post).preimage incoming := by
  symm
  exact baseChange observe project (changedObserve observe project incoming)
    (changedProject project incoming) (eventMap observe project incoming)
    (requestMap project incoming) incoming (IsPullback.of_hasPullback _ _)
    (IsPullback.of_hasPullback _ _) rely post

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.FutureResponses
