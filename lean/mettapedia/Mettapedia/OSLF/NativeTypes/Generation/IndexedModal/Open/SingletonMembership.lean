import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.ExpressionControls
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.BindingObservations

/-!
# Independent singleton requests and source-event witnesses

A singleton classifier is the diagonal of an operational value map. It is
defined before any successful response is selected. Membership forces an
arbitrary native code to be precisely that operational value, including
when the request telescope also admits nonoperational codes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.SingletonMembership

open _root_.CategoryTheory
open Mettapedia.TypeTheory Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Semantics
open Classifier Families Operations CertifiedProjection
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)

universe u
variable {D : Presheaf.CubeEnrichment.Signature} {W : Type u} [Category.{u} W]
variable (operational : D.Carrier → Wᵒᵖ ⥤ Type u)

noncomputable section

def singleton {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier)
    (value : P ⟶ operational carrier) :
    Subfunctor (FunctorToTypes.prod (operational carrier) P) :=
  ExpressionControls.identityPostcondition operational carrier value

def singletonName {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier) (kind : HSort)
    (value : P ⟶ operational carrier) : P ⟶ Carrier.presheaf operational carrier :=
  CertifiedSections.predicateName operational carrier kind (singleton operational carrier value) ≫
    validInclusion operational carrier kind

/-- The independent diagonal forces even a full native-code request to be
the specified operational value. Classifier and sort codes are excluded. -/
theorem singleton_member_iff {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier) (kind : HSort)
    (value : P ⟶ operational carrier) (world : Wᵒᵖ) (parameter : P.obj world)
    (code : Code operational carrier world) :
    Code.Member code ((singletonName operational carrier kind value).app world parameter) ↔
      code = .operational (value.app world parameter) := by
  cases code with
  | operational actual =>
      have precise := FamilyNaming.member_name (singleton operational carrier value)
        world actual parameter
      change Code.Member (.operational actual)
        (.classifier kind ((FamilyNaming.name (singleton operational carrier value)).app world parameter)) ↔ _
      rw [Code.operational.injEq]
      exact precise
  | sort actual =>
      simp only [singletonName, NatTrans.comp_app, types_comp_apply,
        CertifiedSections.predicateName, validInclusion, Code.Member]
      simp
  | classifier actual predicate =>
      simp only [singletonName, NatTrans.comp_app, types_comp_apply,
        CertifiedSections.predicateName, validInclusion, Code.Member]
      simp

theorem singleton_requested {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier) (kind : HSort)
    (value : P ⟶ operational carrier) (world : Wᵒᵖ) (parameter : P.obj world) :
    Code.Member (.operational (value.app world parameter))
      ((singletonName operational carrier kind value).app world parameter) :=
  (singleton_member_iff operational carrier kind value world parameter _).mpr rfl

theorem false_target_empty {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier) (kind : HSort)
    (world : Wᵒᵖ) (parameter : P.obj world) (value : (operational carrier).obj world) :
    ¬ Code.Member (.operational value)
      ((ExpressionControls.targetName operational carrier kind
        (⊥ : Subfunctor (FunctorToTypes.prod (operational carrier) P))).app world parameter) := by
  exact fun member => (FamilyNaming.member_name
    (⊥ : Subfunctor (FunctorToTypes.prod (operational carrier) P)) world value parameter).mp member

variable {interface : Interface D.Carrier}
variable (requests : ResponseSemantics.Requests operational interface)
    (observed : ResponseSemantics.Observations operational interface)

/-- The witness remains the original supplied event, rather than merely an
endpoint with forgotten provenance. The singletons do not mention responses. -/
theorem source_response_of_singletons {world : Wᵒᵖ}
    (request : requests.values.obj world) (event : observed.events.obj world)
    (indices : ∀ position, (requests.indices position).app world request =
      .operational ((observed.indices position).app world event))
    (relies : ∀ position, Code.Member ((requests.relies position).app world request)
      ((singletonName operational interface.relies[position].1 interface.relies[position].2
        (observed.relies position)).app world event))
    (target : Code.Member (.operational (observed.target.app world event))
      (requests.target.app world request)) :
    ResponseSemantics.SourceResponse requests observed request
      (observed.focus.app world event) event := by
  refine ⟨rfl, indices, ?_, target⟩
  intro position
  exact (singleton_member_iff operational _ _ (observed.relies position) world event _).mp
    (relies position)

/-- Earned telescope readouts suffice for a source-event family at every
future restriction. The classifier itself is absent from the hypotheses. -/
theorem source_meaning_of_singleton_fibres
    (parameters : observed.events ⟶ requests.parameters.1)
    (indices : ∀ world (event : observed.events.obj world) (request : requests.values.obj world),
      requests.project.app world request = parameters.app world event →
      ∀ position, (requests.indices position).app world request =
        .operational ((observed.indices position).app world event))
    (relies : ∀ world (event : observed.events.obj world) (request : requests.values.obj world),
      requests.project.app world request = parameters.app world event →
      ∀ position, Code.Member ((requests.relies position).app world request)
        ((singletonName operational interface.relies[position].1 interface.relies[position].2
          (observed.relies position)).app world event))
    (target : ∀ world (event : observed.events.obj world) (request : requests.values.obj world),
      requests.project.app world request = parameters.app world event →
      Code.Member (.operational (observed.target.app world event))
        (requests.target.app world request))
    (world : Wᵒᵖ) (event : observed.events.obj world) :
    ResponseSemantics.SourceMeaning requests observed world
      (observed.focus.app world event) (parameters.app world event) := by
  intro future restriction request lyingOver
  let next := observed.events.map restriction event
  have overNext : requests.project.app future request = parameters.app future next :=
    lyingOver.trans (parameters.naturality_apply restriction event).symm
  refine ⟨next, ?_⟩
  have response := source_response_of_singletons operational requests observed request next
    (indices future next request overNext) (relies future next request overNext)
    (target future next request overNext)
  rw [observed.focus.naturality_apply restriction event] at response
  exact response

/-- A false target cannot be hidden behind an empty universal domain: one
actual request over the parameter point already refutes membership. -/
theorem false_target_excludes_nonempty_request {P : Wᵒᵖ ⥤ Type u}
    (world : Wᵒᵖ) (focus : (operational interface.focus).obj world)
    (parameters : requests.parameters.1.obj world)
    (request : requests.values.obj world)
    (lyingOver : requests.project.app world request = parameters)
    (parameter : P.obj world)
    (target : requests.target.app world request =
      (ExpressionControls.targetName operational interface.target interface.resultSort
        (⊥ : Subfunctor (FunctorToTypes.prod (operational interface.target) P))).app world parameter) :
    ¬ ResponseSemantics.SourceMeaning requests observed world focus parameters := by
  intro meaning
  obtain ⟨event, _, _, _, member⟩ :=
    ResponseSemantics.current_response requests observed focus parameters meaning request lyingOver
  rw [target] at member
  exact false_target_empty operational _ _ world parameter _ member

end
end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.SingletonMembership
