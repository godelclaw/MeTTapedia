import Mettapedia.PLN.WorldModel.PLNWorldModel
import Mettapedia.GSLT.Topos.PredicateFibration

/-!
# WM Hyperdoctrine Layer (Typed Queries + Change-of-Base)

This module provides a conservative hyperdoctrine-style wrapper for the WM
typed query layer (`WorldModelSigma`), linked to the existing GSLT
change-of-base interface and Beck-Chevalley condition.

The design is intentionally explicit:
- typed queries indexed by base objects,
- reindexing / existential / universal query operators,
- interpretation into a predicate fibration,
- compatibility laws (query-operator ↔ change-of-base),
- the evidence law `evidence_factors`: queries with the same interpreted
  predicate have the same evidence at every state
  (`EvidenceFactorsThroughInterpretation`),
- Beck-Chevalley transport at the query interpretation layer
  (`beckChevalley_transport_exists`) and, through the evidence law, at the
  evidence layer (`evidenceAt_beckChevalley_exists`),
- presentations (`Presents`): a hyperdoctrine presents a world model on its own
  state type at an object when encoded queries carry the world model's
  evidence.

States that vary by object and move forward along arrows are the lawful
extension `IndexedWorldModel`: the evidence of a reindexed query at a state is
the evidence of the query at the moved state.  With one state type for all
objects and identity moves this law says that reindexing does not change
evidence, which substitution refutes on counting instances.
-/

namespace Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelHyperdoctrine

open _root_.CategoryTheory
open Mettapedia.PLN.WorldModel.PLNWorldModel
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.GSLT.Core
open Mettapedia.GSLT.Topos
open scoped ENNReal

universe u v w w' x

section Law

variable {State : Type x} [EvidenceType State]

/-- **Evidence factors through interpretation.** At every state and object, two
queries with the same interpreted predicate have the same evidence. Stated for
the raw data of a bundle, so that data violating it can be named. -/
def EvidenceFactorsThroughInterpretation {Obj : Type u} {Sub : Obj → Type w'}
    {query : Obj → Type w} (worldModel : WorldModelSigma State Obj query)
    (interpret : ∀ {X : Obj}, query X → Sub X) : Prop :=
  ∀ (W : State) {X : Obj},
    Function.FactorsThrough
      (fun φ : query X => @WorldModelSigma.evidence State Obj query _ worldModel W ⟨X, φ⟩)
      (interpret (X := X))

end Law

/-- Hyperdoctrine-style WM bundle over a categorical base.

    Universe parameters:
    - `u` : base objects, `v` : base morphisms,
    - `w` : object-indexed typed queries,
    - `w'` : predicate-fibration fibers (independent of the query universe),
    - `x` : the evidence state type. -/
structure WMHyperdoctrine (State : Type x) [EvidenceType State] where
  /-- Base objects (contexts/sorts). -/
  Obj : Type u
  /-- Base category structure. -/
  instCategory : _root_.CategoryTheory.Category.{v} Obj
  /-- Predicate fibration over the base. -/
  predFib : PredicateFib.{u, v, w'} Obj
  /-- Typed query family indexed by base objects. -/
  query : Obj → Type w
  /-- WM semantics over object-indexed typed queries. -/
  worldModel : WorldModelSigma State Obj query
  /-- Reindexing (pullback) on queries. -/
  reindexQuery : ∀ {X Y : Obj}, (X ⟶ Y) → query Y → query X
  /-- Existential transport on queries. -/
  existsQuery : ∀ {X Y : Obj}, (X ⟶ Y) → query X → query Y
  /-- Universal transport on queries. -/
  forallQuery : ∀ {X Y : Obj}, (X ⟶ Y) → query X → query Y
  /-- Interpretation of queries into fibration predicates. -/
  interpret : ∀ {X : Obj}, query X → predFib.Sub X
  /-- Concrete change-of-base structure reused from GSLT. -/
  cob : ChangeOfBase (PredicateFib.toSubobjectFibration predFib)
  /-- Beck-Chevalley law at the fibration level. -/
  beckChevalley : BeckChevalleyCondition predFib cob
  /-- Reindexing compatibility with pullback. -/
  reindex_interp :
    ∀ {X Y : Obj} (f : X ⟶ Y) (φ : query Y),
      interpret (reindexQuery f φ) = cob.pullback f (interpret φ)
  /-- Existential compatibility with direct image. -/
  exists_interp :
    ∀ {X Y : Obj} (f : X ⟶ Y) (φ : query X),
      interpret (existsQuery f φ) = cob.directImage f (interpret φ)
  /-- Universal compatibility with universal image. -/
  forall_interp :
    ∀ {X Y : Obj} (f : X ⟶ Y) (φ : query X),
      interpret (forallQuery f φ) = cob.universalImage f (interpret φ)
  /-- Evidence is joined to the query operations through interpretation: two
  queries with the same interpreted predicate have the same evidence at every
  state. -/
  evidence_factors : EvidenceFactorsThroughInterpretation worldModel interpret

attribute [instance] WMHyperdoctrine.instCategory

namespace WMHyperdoctrine

variable {State : Type x} [EvidenceType State]
variable (H : WMHyperdoctrine State)

/-- BinaryEvidence extracted for an object-indexed query. -/
def evidenceAt (W : State) {X : H.Obj} (φ : H.query X) : BinaryEvidence := by
  letI : WorldModelSigma State H.Obj H.query := H.worldModel
  exact WorldModelSigma.evidenceAt (State := State) (Srt := H.Obj) (Query := H.query) W φ

/-- Strength view for an object-indexed query. -/
noncomputable def queryStrengthAt (W : State) {X : H.Obj} (φ : H.query X) : ℝ≥0∞ := by
  letI : WorldModelSigma State H.Obj H.query := H.worldModel
  exact WorldModelSigma.queryStrengthAt (State := State) (Srt := H.Obj) (Query := H.query) W φ

/-- Context-sensitive strength view for an object-indexed query. -/
noncomputable def queryStrengthWithAt
    (ctx : BinaryContext) (W : State) {X : H.Obj} (φ : H.query X) : ℝ≥0∞ := by
  letI : WorldModelSigma State H.Obj H.query := H.worldModel
  exact WorldModelSigma.queryStrengthWithAt
    (State := State) (Srt := H.Obj) (Query := H.query) ctx W φ

/-- Confidence view for an object-indexed query. -/
noncomputable def queryConfidenceAt
    (κ : ℝ≥0∞) (W : State) {X : H.Obj} (φ : H.query X) : ℝ≥0∞ := by
  letI : WorldModelSigma State H.Obj H.query := H.worldModel
  exact WorldModelSigma.queryConfidenceAt
    (State := State) (Srt := H.Obj) (Query := H.query) κ W φ

/-- Additivity transport of evidence in the hyperdoctrine WM bundle. -/
theorem evidenceAt_add
    (W₁ W₂ : State) {X : H.Obj} (φ : H.query X) :
    H.evidenceAt (W₁ + W₂) φ = H.evidenceAt W₁ φ + H.evidenceAt W₂ φ :=
  @WorldModelSigma.evidenceAt_add State H.Obj H.query _ H.worldModel W₁ W₂ X φ

/-- Reindex-then-existential transport obeys Beck-Chevalley at query interpretation level. -/
theorem beckChevalley_transport_exists
    {P A B D : H.Obj}
    (π₁ : P ⟶ A) (π₂ : P ⟶ B) (f : A ⟶ D) (g : B ⟶ D)
    (hpb : IsPullback π₁ π₂ f g)
    [Mono f] [Mono π₂]
    (φ : H.query B) :
    H.interpret (H.reindexQuery f (H.existsQuery g φ)) =
      H.interpret (H.existsQuery π₁ (H.reindexQuery π₂ φ)) := by
  -- Rewrite both query operators through their fibration-interpretation laws,
  -- reducing the goal to the Beck-Chevalley base-change identity at the
  -- change-of-base level (`f* ∘ ∃g = ∃π₁ ∘ π₂*`).
  simp only [H.reindex_interp, H.exists_interp]
  exact H.beckChevalley π₁ π₂ f g hpb (H.interpret φ)

/-- Queries with the same interpreted predicate have the same evidence. -/
theorem evidenceAt_eq_of_interpret_eq (W : State) {X : H.Obj} {φ ψ : H.query X}
    (same : H.interpret φ = H.interpret ψ) : H.evidenceAt W φ = H.evidenceAt W ψ :=
  H.evidence_factors W same

/-- **Beck–Chevalley at the evidence layer.** On a pullback square where the
predicate Beck–Chevalley law applies, reindexing an existential query has, at
every state, the evidence of the existential of the reindexed query. -/
theorem evidenceAt_beckChevalley_exists
    {P A B D : H.Obj}
    (π₁ : P ⟶ A) (π₂ : P ⟶ B) (f : A ⟶ D) (g : B ⟶ D)
    (hpb : IsPullback π₁ π₂ f g)
    [Mono f] [Mono π₂]
    (W : State) (φ : H.query B) :
    H.evidenceAt W (H.reindexQuery f (H.existsQuery g φ)) =
      H.evidenceAt W (H.existsQuery π₁ (H.reindexQuery π₂ φ)) :=
  H.evidenceAt_eq_of_interpret_eq W (H.beckChevalley_transport_exists π₁ π₂ f g hpb φ)

/-- Beck–Chevalley for the strength view. -/
theorem queryStrengthAt_beckChevalley_exists
    {P A B D : H.Obj}
    (π₁ : P ⟶ A) (π₂ : P ⟶ B) (f : A ⟶ D) (g : B ⟶ D)
    (hpb : IsPullback π₁ π₂ f g)
    [Mono f] [Mono π₂]
    (W : State) (φ : H.query B) :
    H.queryStrengthAt W (H.reindexQuery f (H.existsQuery g φ)) =
      H.queryStrengthAt W (H.existsQuery π₁ (H.reindexQuery π₂ φ)) :=
  congrArg BinaryEvidence.toStrength (H.evidenceAt_beckChevalley_exists π₁ π₂ f g hpb W φ)

/-! ## Presentations of world models -/

/-- `H` **presents** a world model on its state type at the object `X` through
`enc` when every encoded query has, at every state, the world model's evidence. -/
def Presents (X : H.Obj) {Query : Type*} [BinaryWorldModel State Query]
    (enc : Query → H.query X) : Prop :=
  ∀ (W : State) (q : Query), H.evidenceAt W (enc q) = BinaryWorldModel.evidence W q

/-- Under a presentation the strength views agree. -/
theorem Presents.queryStrengthAt_eq {X : H.Obj} {Query : Type*} [BinaryWorldModel State Query]
    {enc : Query → H.query X} (presents : H.Presents X enc) (W : State) (q : Query) :
    H.queryStrengthAt W (enc q) = BinaryWorldModel.queryStrength W q :=
  congrArg BinaryEvidence.toStrength (presents W q)

/-- Under a presentation, queries whose encodings have the same interpreted
predicate have the same evidence in the presented world model. -/
theorem Presents.evidence_eq_of_interpret_eq {X : H.Obj} {Query : Type*}
    [BinaryWorldModel State Query] {enc : Query → H.query X} (presents : H.Presents X enc)
    (W : State) {q₁ q₂ : Query} (same : H.interpret (enc q₁) = H.interpret (enc q₂)) :
    BinaryWorldModel.evidence W q₁ = BinaryWorldModel.evidence (State := State) W q₂ := by
  rw [← presents W q₁, ← presents W q₂]
  exact H.evidenceAt_eq_of_interpret_eq W same

/-! ## States that vary by object -/

/-- **An indexed world model over the queries of `H`.** A state monoid at every
object, pushed forward along arrows, with additive evidence at each object; the
law `evidence_reindex` says that a reindexed query has, at a state, the
evidence of the query at the pushed state.  `H`'s own world model, with one
state type for all objects, is the special case of constant states; with
identity pushes the law then says that reindexing does not change evidence. -/
structure IndexedWorldModel where
  /-- The states at each object, in the universe of the queries. -/
  St : H.Obj → Type w
  /-- Revision of states at each object. -/
  addCommMonoid : ∀ X, AddCommMonoid (St X)
  /-- States move forward along arrows. -/
  push : ∀ {X Y : H.Obj}, (X ⟶ Y) → St X →+ St Y
  /-- Moving along an identity does nothing. -/
  push_id : ∀ (X : H.Obj) (W : St X), push (𝟙 X) W = W
  /-- Moving along a composite is moving twice. -/
  push_comp : ∀ {X Y Z : H.Obj} (f : X ⟶ Y) (g : Y ⟶ Z) (W : St X),
    push (f ≫ g) W = push g (push f W)
  /-- Evidence at each object. -/
  evidence : ∀ X, St X →+ (H.query X → BinaryEvidence)
  /-- **The satisfaction law**: reindexed queries read the moved state. -/
  evidence_reindex : ∀ {X Y : H.Obj} (f : X ⟶ Y) (W : St X) (φ : H.query Y),
    evidence X W (H.reindexQuery f φ) = evidence Y (push f W) φ

attribute [instance] IndexedWorldModel.addCommMonoid

end WMHyperdoctrine

end Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelHyperdoctrine
