import Mettapedia.PLN.WorldModel.WorldModelInstitution
import Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelHyperdoctrine

/-!
# WM Categorical Bridge Endpoint

This module connects the institution layer (`WorldModelInstitution`) and
the hyperdoctrine layer (`PLNWorldModelHyperdoctrine`).

* **The endpoint** (`EndpointStatement`, `EndpointContract`) is Beck–Chevalley
  at the evidence layer: reindexing an existential query has, at a state, the
  evidence of the existential of the reindexed query.  It holds on every pullback
  square where the predicate Beck–Chevalley law applies, because evidence factors
  through interpretation (`institution_beckChevalley_endpoint`); it fails on
  commuting squares that are not pullbacks.
* **The institution view of reindexing.** Each object gives a one-sort
  signature and reindexing gives signature morphisms (`singletonSig`,
  `singletonReindexSigMorphism`).  With the state carrier fixed, the
  satisfaction condition along such a morphism says that reindexing does not
  change evidence (`singletonReindex_satisfactionAlong_iff`).  Substitution
  refutes that on counting instances, so it is not part of the endpoint.
-/

namespace Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelCategoricalBridge

open _root_.CategoryTheory
open Mettapedia.PLN.WorldModel
open Mettapedia.PLN.WorldModel.WorldModelInstitution
open Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelHyperdoctrine
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.Evidence

universe u v w x

variable {State : Type x} [EvidenceType State]

namespace WMHyperdoctrine

variable (H : WMHyperdoctrine State)

/-- One-sort WM signature wrapper around queries at object `X`. -/
def singletonSig (X : H.Obj) : WMSignature where
  Srt := PUnit
  Query := fun _ => H.query X

/-- Singleton-signature morphism induced by query reindexing along `f`. -/
def singletonReindexSigMorphism {X Y : H.Obj} (f : X ⟶ Y) :
    WMSigMorphism (singletonSig (H := H) Y) (singletonSig (H := H) X) where
  mapSort := fun _ => PUnit.unit
  mapQuery := by
    intro _ q
    exact H.reindexQuery f q

/-- WM semantics on singleton signatures, induced from `H.worldModel`. -/
@[instance_reducible] def singletonWorldModelSigma (X : H.Obj) :
    WorldModelSigma State PUnit (fun _ => H.query X) where
  evidence := fun W q =>
    letI : WorldModelSigma State H.Obj H.query := H.worldModel
    WorldModelSigma.evidenceAt (State := State) (Srt := H.Obj) (Query := H.query) W q.2
  evidence_add := by
    intro W₁ W₂ q
    exact H.evidenceAt_add W₁ W₂ q.2
  evidence_zero q := @WorldModelSigma.evidence_zero State H.Obj H.query _ H.worldModel ⟨X, q.2⟩

/-- **The institution view of reindexing is evidence invariance.** With the
state carrier fixed, the satisfaction condition along the singleton morphism
of `f` holds exactly when reindexing along `f` does not change evidence. -/
theorem singletonReindex_satisfactionAlong_iff {X Y : H.Obj} (f : X ⟶ Y) :
    SatisfactionAlong (singletonReindexSigMorphism (H := H) f)
        (singletonWorldModelSigma (H := H) Y) (singletonWorldModelSigma (H := H) X) ↔
      ∀ (W : State) (φ : H.query Y), H.evidenceAt W φ = H.evidenceAt W (H.reindexQuery f φ) :=
  ⟨fun h W φ => h W ⟨PUnit.unit, φ⟩, fun h W φ => h W φ.2⟩

/-- **The categorical endpoint**: Beck–Chevalley at the evidence layer for one
square, one state and one query.  The statement formerly paired an institution
transport that holds for every bundle with Beck–Chevalley on interpreted
predicates; it now states the evidence equation. -/
abbrev EndpointStatement
    {P A B D : H.Obj}
    (π₁ : P ⟶ A) (π₂ : P ⟶ B) (f : A ⟶ D) (g : B ⟶ D)
    (W : State) (φ : H.query B) : Prop :=
  H.evidenceAt W (H.reindexQuery f (H.existsQuery g φ)) =
    H.evidenceAt W (H.existsQuery π₁ (H.reindexQuery π₂ φ))

/-- The endpoint on every pullback square where the predicate Beck–Chevalley
law applies. -/
abbrev EndpointContract (H : WMHyperdoctrine State) : Prop :=
  ∀ {P A B D : H.Obj}
    (π₁ : P ⟶ A) (π₂ : P ⟶ B) (f : A ⟶ D) (g : B ⟶ D)
    (_hpb : IsPullback π₁ π₂ f g)
    [Mono f] [Mono π₂]
    (W : State) (φ : H.query B),
    EndpointStatement (H := H) π₁ π₂ f g W φ

/-- **The endpoint holds on pullback squares**: evidence factors through
interpretation and interpreted predicates satisfy Beck–Chevalley.  The
institution half of the former statement is dropped: along reindexing with a
fixed carrier the satisfaction condition is evidence invariance
(`singletonReindex_satisfactionAlong_iff`), which substitution refutes on
counting instances. -/
theorem institution_beckChevalley_endpoint
    {P A B D : H.Obj}
    (π₁ : P ⟶ A) (π₂ : P ⟶ B) (f : A ⟶ D) (g : B ⟶ D)
    (hpb : IsPullback π₁ π₂ f g)
    [Mono f] [Mono π₂]
    (W : State) (φ : H.query B) :
    EndpointStatement (H := H) π₁ π₂ f g W φ :=
  H.evidenceAt_beckChevalley_exists π₁ π₂ f g hpb W φ

/-- Every WM hyperdoctrine satisfies the endpoint contract. -/
theorem endpointContract_of_hyperdoctrine
    (H : WMHyperdoctrine State) :
    EndpointContract (H := H) :=
  institution_beckChevalley_endpoint (H := H)

end WMHyperdoctrine

end Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelCategoricalBridge
