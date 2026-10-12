import Mettapedia.Logic.WorldModel.Indexed.FixedQueryBridge
import Mettapedia.Logic.WorldModel.Indexed.Gluing
import Mettapedia.Logic.WorldModel.Indexed.Survival
import Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelHyperdoctrine
import Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelCountingHyperdoctrine

/-!
# The world-model hyperdoctrine and the doctrine

`WMHyperdoctrine` carries a single state type, typed queries indexed by base
objects, one typed world model over all of them, query operators, a predicate
fibration with Beck–Chevalley, and the evidence law: evidence factors through
interpretation.

* Its world model is an object of the fibre over the one-world base, with the
  question type `Σ X, query X` (`pointModel`).
* **Evidence through interpretation, the bundle's law, is the consumer law of
  the doctrine.** Evidence factors through interpretation exactly when it is
  kept by every query map that keeps interpretations
  (`evidenceFactors_iff_endo_invariant`).
* **The indexed satisfaction law is the doctrine's presheaf of states.** With
  functorial reindexing (`QueryFunctorial`), an indexed world model is an
  object of the slice of presheaves over the profile functor
  (`IndexedWorldModel.toStatePresheaf`), and every such object is one
  (`IndexedWorldModel.ofStatePresheaf`): the satisfaction law is the
  naturality of extraction.  Its world model at each object is the doctrine's
  fibre model there (`toStatePresheaf_at`).
* **Evidence invariance, evidence unchanged by reindexing at one state, is the
  special case of the indexed law with one state type and identity moves**
  (`constantIndexed`), and it is the condition for the identity of the state to
  be a doctrine morphism over every arrow (`compatibleHom`,
  `evidenceCompatible_of_homs`).  Substitution refutes it on the counting
  hyperdoctrine (`countingHyperdoctrine_not_compatible`).
* **Negative for the indexed law.** The presheaf hyperdoctrine whose evidence
  reads the state exactly on the top predicate satisfies evidence through
  interpretation and has no state transport at all making the indexed law hold
  (`counterHyperdoctrine_no_transport`).

**Where the bundle still differs from the doctrine.** The bundle's own world
model has one state type, so it is an object of the doctrine only through
evidence invariance or after choosing indexed states.  The doctrine's
quantifiers act on evidence-valued profiles along question maps, while the
bundle's act on predicates; the two meet only through evidence through
interpretation: the evidence of an existential query is determined by its
predicate, not computed from the evidence of its witnesses.
-/

set_option autoImplicit false

open CategoryTheory Opposite

namespace Mettapedia.Logic.WorldModel.Indexed.HyperdoctrineBridge

open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.WorldModel.PLNWorldModel
open Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelHyperdoctrine

universe u v x

section PointModel

variable {State : Type} [EvidenceType State]

/-- The hyperdoctrine's world model, over all typed queries at once, is a
binary world model over one world. -/
def pointModel (H : WMHyperdoctrine.{0, 0, 0} State) : FixedQuery.BinaryModel (Σ X : H.Obj, H.query X) :=
  letI : WorldModelSigma State H.Obj H.query := H.worldModel
  { State := State
    worldModel := WorldModelSigma.toWorldModelSigma State H.Obj H.query }

end PointModel

section Laws

variable {State : Type x} [EvidenceType State]

/-- Reindexing of queries is functorial. -/
def QueryFunctorial (H : WMHyperdoctrine.{u, v, 0} State) : Prop :=
  (∀ (X : H.Obj) (φ : H.query X), H.reindexQuery (𝟙 X) φ = φ) ∧
    ∀ {X Y Z : H.Obj} (f : X ⟶ Y) (g : Y ⟶ Z) (φ : H.query Z),
      H.reindexQuery (f ≫ g) φ = H.reindexQuery f (H.reindexQuery g φ)

/-- **Evidence invariance**: reindexing a query does not change its evidence at a
state. -/
def EvidenceCompatible (H : WMHyperdoctrine State) : Prop :=
  ∀ {X Y : H.Obj} (f : X ⟶ Y) (φ : H.query Y) (W : State),
    H.evidenceAt W (H.reindexQuery f φ) = H.evidenceAt W φ

/-- **Evidence through interpretation is the consumer law.** Evidence factors
through interpretation exactly when, at every state, it is kept by every query
map that keeps interpretations. -/
theorem evidenceFactors_iff_endo_invariant {Obj : Type*} {Sub : Obj → Type*}
    {query : Obj → Type*} (wm : WorldModelSigma State Obj query)
    (interpret : ∀ {X : Obj}, query X → Sub X) :
    EvidenceFactorsThroughInterpretation wm interpret ↔
      ∀ (W : State) (X : Obj) (h : query X → query X),
        interpret ∘ h = interpret (X := X) →
          (fun φ => @WorldModelSigma.evidence State Obj query _ wm W ⟨X, φ⟩) ∘ h =
            fun φ => @WorldModelSigma.evidence State Obj query _ wm W ⟨X, φ⟩ := by
  constructor
  · intro factors W X
    exact (factorsThrough_iff_endo_invariant _ _).1 (factors W)
  · intro invariant W X
    exact (factorsThrough_iff_endo_invariant _ _).2 (invariant W X)

/-- With functorial reindexing, the queries form a query functor on the
opposite base. -/
def queryFunctor (H : WMHyperdoctrine.{u, v, 0} State) (functorial : QueryFunctorial H) :
    H.Objᵒᵖ ⥤ Type where
  obj X := H.query X.unop
  map f := ↾(H.reindexQuery f.unop)
  map_id X := by
    show (↾(H.reindexQuery (𝟙 X.unop)) : H.query X.unop ⟶ H.query X.unop) = 𝟙 _
    rw [show H.reindexQuery (𝟙 X.unop) = fun φ => φ from funext (functorial.1 X.unop)]
    rfl
  map_comp f g := by
    show (↾(H.reindexQuery (g.unop ≫ f.unop)) : _ ⟶ _) =
      ↾(H.reindexQuery f.unop) ≫ ↾(H.reindexQuery g.unop)
    rw [show H.reindexQuery (g.unop ≫ f.unop) = fun φ => H.reindexQuery g.unop
      (H.reindexQuery f.unop φ) from funext (functorial.2 g.unop f.unop)]
    rfl

/-- Binary evidence at every object. -/
noncomputable def binaryEvidence (H : WMHyperdoctrine.{u, v, 0} State) :
    (H.Objᵒᵖ)ᵒᵖ ⥤ AddCommMonCat :=
  (Functor.const _).obj (AddCommMonCat.of BinaryEvidence)

/-- The profile functor of a functorial hyperdoctrine. -/
noncomputable abbrev profiles (H : WMHyperdoctrine.{u, v, 0} State) (functorial : QueryFunctorial H) :
    (H.Objᵒᵖ)ᵒᵖ ⥤ AddCommMonCat :=
  profileFunctor (queryFunctor H functorial) (binaryEvidence H)

end Laws

/-! ## Indexed world models are presheaves of states -/

section Indexed

variable {State : Type x} [EvidenceType State]
variable (H : WMHyperdoctrine.{u, v, 0} State)

/-- The states of an indexed world model, as a presheaf on the opposite base. -/
def IndexedWorldModel.stateFunctor (M : H.IndexedWorldModel) :
    (H.Objᵒᵖ)ᵒᵖ ⥤ AddCommMonCat where
  obj X := AddCommMonCat.of (M.St X.unop.unop)
  map f := AddCommMonCat.ofHom (M.push f.unop.unop)
  map_id X := by
    ext W
    exact M.push_id X.unop.unop W
  map_comp f g := by
    ext W
    exact M.push_comp f.unop.unop g.unop.unop W

/-- The extraction of an indexed world model is natural into the profiles:
its naturality is the satisfaction law. -/
noncomputable def IndexedWorldModel.extraction (M : H.IndexedWorldModel)
    (functorial : QueryFunctorial H) : IndexedWorldModel.stateFunctor H M ⟶ profiles H functorial where
  app X := AddCommMonCat.ofHom (M.evidence X.unop.unop)
  naturality X Y f := by
    ext W
    funext φ
    exact (M.evidence_reindex f.unop.unop W φ).symm

/-- **An indexed world model is a presheaf of states over the profiles.** -/
noncomputable def IndexedWorldModel.toStatePresheaf (M : H.IndexedWorldModel)
    (functorial : QueryFunctorial H) : Over (profiles H functorial) :=
  Over.mk (IndexedWorldModel.extraction H M functorial)

/-- Its world model at an object is the extraction there. -/
theorem IndexedWorldModel.toStatePresheaf_at (M : H.IndexedWorldModel)
    (functorial : QueryFunctorial H) (X : H.Obj) :
    (StatePresheaf.at (IndexedWorldModel.toStatePresheaf H M functorial) (op X)).hom =
      AddCommMonCat.ofHom (M.evidence X) :=
  rfl

/-- **Every presheaf of states over the profiles is an indexed world model**:
naturality of the extraction gives the satisfaction law. -/
noncomputable def IndexedWorldModel.ofStatePresheaf (functorial : QueryFunctorial H)
    (S : Over (profiles H functorial)) : H.IndexedWorldModel where
  St X := S.left.obj (op (op X))
  addCommMonoid _ := inferInstance
  push f := (S.left.map f.op.op).hom
  push_id X W := by
    rw [show (𝟙 X).op.op = 𝟙 (op (op X)) from rfl, S.left.map_id]
    rfl
  push_comp f g W := by
    rw [show (f ≫ g).op.op = f.op.op ≫ g.op.op from rfl, S.left.map_comp]
    rfl
  evidence X := (S.hom.app (op (op X))).hom
  evidence_reindex f W φ := by
    have := congrArg (fun k => (k.hom W) φ) (S.hom.naturality f.op.op)
    exact this.symm

/-- The round trip from an indexed world model keeps its states, moves and
evidence. -/
theorem IndexedWorldModel.ofStatePresheaf_toStatePresheaf
    (M : H.IndexedWorldModel) (functorial : QueryFunctorial H)
    (X : H.Obj) (W : M.St X) (φ : H.query X) :
    (IndexedWorldModel.ofStatePresheaf H functorial
      (IndexedWorldModel.toStatePresheaf H M functorial)).evidence X W φ =
      M.evidence X W φ :=
  rfl

end Indexed

section Constant

variable {State : Type} [EvidenceType State]

/-- **Evidence invariance is the constant special case of the indexed law.**
One state type at every object, moved by the identity, is an indexed world
model when reindexing does not change evidence. -/
noncomputable def constantIndexed (H : WMHyperdoctrine.{u, v, 0} State)
    (compatible : EvidenceCompatible H) : H.IndexedWorldModel where
  St _ := State
  addCommMonoid _ := inferInstance
  push _ := AddMonoidHom.id State
  push_id _ _ := rfl
  push_comp _ _ _ := rfl
  evidence X :=
    { toFun := fun W φ => H.evidenceAt W φ
      map_zero' := funext fun φ =>
        @WorldModelSigma.evidence_zero State H.Obj H.query _ H.worldModel ⟨X, φ⟩
      map_add' := fun W₁ W₂ => funext fun φ => H.evidenceAt_add W₁ W₂ φ }
  evidence_reindex f W φ := compatible f φ W

/-- Conversely, the satisfaction law for the constant states with identity
moves is evidence invariance. -/
theorem evidenceCompatible_of_constant_law (H : WMHyperdoctrine.{u, v, 0} State)
    (law : ∀ {X Y : H.Obj} (f : X ⟶ Y) (W : State) (φ : H.query Y),
      H.evidenceAt W (H.reindexQuery f φ) = H.evidenceAt (AddMonoidHom.id State W) φ) :
    EvidenceCompatible H :=
  fun f φ W => law f W φ

/-- The hyperdoctrine's world model, read at one object. -/
noncomputable def modelAt (H : WMHyperdoctrine.{u, v, 0} State) (functorial : QueryFunctorial H)
    (X : H.Obj) : Over ((profiles H functorial).obj (op (op X))) :=
  Over.mk (AddCommMonCat.ofHom
    { toFun := fun W φ => H.evidenceAt W φ
      map_zero' := funext fun _ =>
        @WorldModelSigma.evidence_zero State H.Obj H.query _ H.worldModel _
      map_add' := fun W₁ W₂ => funext fun φ => H.evidenceAt_add W₁ W₂ φ } :
    AddCommMonCat.of State ⟶ (profiles H functorial).obj (op (op X)))

/-- **Compatible hyperdoctrines are doctrine instances.** Under evidence
compatibility, the identity of the state is a morphism of the doctrine over
every arrow of the opposite base. -/
noncomputable def compatibleHom (H : WMHyperdoctrine.{u, v, 0} State) (functorial : QueryFunctorial H)
    (compatible : EvidenceCompatible H) {X Y : H.Obj} (f : X ⟶ Y) :
    Total.mk (profiles H functorial) (op Y) (modelAt H functorial Y) ⟶
      Total.mk (profiles H functorial) (op X) (modelAt H functorial X) :=
  homOver (profiles H functorial) f.op (𝟙 _)
    ((overArrow_iff (queryFunctor H functorial) (binaryEvidence H) f.op _ _ _).2
      (fun W φ => compatible f φ W))

/-- Conversely, identity morphisms over every arrow force evidence
compatibility. -/
theorem evidenceCompatible_of_homs (H : WMHyperdoctrine.{u, v, 0} State)
    (functorial : QueryFunctorial H)
    (homs : ∀ {X Y : H.Obj} (f : X ⟶ Y),
      𝟙 (AddCommMonCat.of State) ≫ (modelAt H functorial X).hom ≫
        (profiles H functorial).map f.op.op = (modelAt H functorial Y).hom) :
    EvidenceCompatible H := by
  intro X Y f φ W
  exact (overArrow_iff (queryFunctor H functorial) (binaryEvidence H) f.op
    (modelAt H functorial Y) (modelAt H functorial X) (𝟙 _)).1 (homs f) W φ

end Constant

/-! ## The counting hyperdoctrine -/

section Counting

open Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelCountingHyperdoctrine

/-- Substitution into predicate codes is functorial. -/
theorem countingHyperdoctrine_queryFunctorial : QueryFunctorial countingHyperdoctrine :=
  ⟨fun _ c => PredicateCode.subst_id c, fun f g c => PredicateCode.subst_comp f g c⟩

/-- **Evidence invariance is refuted on the counting hyperdoctrine.** -/
theorem countingHyperdoctrine_not_compatible : ¬ EvidenceCompatible countingHyperdoctrine :=
  fun compatible => counting_reindex_changes_evidence (compatible swap (.atom isTrue) oneTrue)

/-- **The indexed counting world model is a doctrine object**: the bags of
points at all contexts, as a presheaf of states over the profiles. -/
noncomputable def countingStatePresheaf :
    Over (profiles countingHyperdoctrine countingHyperdoctrine_queryFunctorial) :=
  IndexedWorldModel.toStatePresheaf countingHyperdoctrine countingIndexed
    countingHyperdoctrine_queryFunctorial

end Counting

/-! ## A presheaf hyperdoctrine without state transport -/

section Counter

open Mettapedia.GSLT.Topos

/-- Presheaves on a point. -/
abbrev Psh := (Discrete PUnit.{1})ᵒᵖ ⥤ Type

/-- The constant Boolean presheaf. -/
def boolPsh : Psh := (Functor.const _).obj Bool

/-- The constant one-point presheaf. -/
def unitPsh : Psh := (Functor.const _).obj PUnit

/-- The section `true`. -/
def pickTrue : unitPsh ⟶ boolPsh where
  app _ := ↾(fun _ => true)

/-- The predicate "is `true`". -/
def trueSub : Subfunctor boolPsh where
  obj _ := {true}
  map _ _ h := h

theorem trueSub_ne_top : trueSub ≠ ⊤ := by
  intro h
  have := congrArg (fun S : Subfunctor boolPsh => false ∈ S.obj (op ⟨PUnit.unit⟩)) h
  simp only [trueSub, Subfunctor.top_obj, Set.top_eq_univ, eq_iff_iff] at this
  have hmem : false ∈ ({true} : Set Bool) := this.2 (Set.mem_univ false)
  exact absurd (Set.mem_singleton_iff.mp hmem) (by decide)

theorem preimage_trueSub_eq_top : trueSub.preimage pickTrue = ⊤ := by
  ext U x
  simp only [Subfunctor.preimage, Subfunctor.top_obj, Set.top_eq_univ, Set.mem_univ, iff_true]
  exact Set.mem_singleton true

open Classical in
/-- Evidence that reads the state exactly on the top predicate. -/
@[instance_reducible] noncomputable def topReading :
    WorldModelSigma BinaryEvidence Psh (fun X => Subfunctor X) where
  evidence W q := if q.2 = ⊤ then W else 0
  evidence_add W₁ W₂ q := by
    by_cases h : q.2 = ⊤ <;> simp [h]
  evidence_zero q := by
    by_cases h : q.2 = ⊤ <;> simp [h]

/-- A hyperdoctrine on presheaves over a point: queries are predicates,
reindexing is preimage, the quantifiers are image and universal image,
Beck–Chevalley is the existing presheaf theorem, and evidence reads the state
on the top predicate.  Interpretation is the identity, so evidence factors
through interpretation. -/
noncomputable def counterHyperdoctrine : WMHyperdoctrine BinaryEvidence where
  Obj := Psh
  instCategory := inferInstance
  predFib := presheafPredicateFib (Discrete PUnit.{1})
  query X := Subfunctor X
  worldModel := topReading
  reindexQuery f φ := φ.preimage f
  existsQuery f φ := φ.image f
  forallQuery f φ := (presheafChangeOfBase (Discrete PUnit.{1})).universalImage f φ
  interpret φ := φ
  cob := presheafChangeOfBase (Discrete PUnit.{1})
  beckChevalley := beckChevalleyCondition_presheafChangeOfBase (Discrete PUnit.{1})
  reindex_interp _ _ := rfl
  exists_interp _ _ := rfl
  forall_interp _ _ := rfl
  evidence_factors := by
    intro W X φ ψ same
    change φ = ψ at same
    rw [same]

open Classical in
/-- **Evidence invariance fails on the top reading.** -/
theorem counterHyperdoctrine_not_compatible :
    ¬ EvidenceCompatible (State := BinaryEvidence) counterHyperdoctrine := by
  intro compatible
  have := compatible (X := unitPsh) (Y := boolPsh) pickTrue trueSub ⟨1, 0⟩
  change (if trueSub.preimage pickTrue = ⊤ then (⟨1, 0⟩ : BinaryEvidence) else 0) =
    (if trueSub = ⊤ then (⟨1, 0⟩ : BinaryEvidence) else 0) at this
  rw [if_pos preimage_trueSub_eq_top, if_neg trueSub_ne_top] at this
  have pos := congrArg BinaryEvidence.pos this
  exact one_ne_zero pos

open Classical in
/-- **Negative for the indexed law.** No transport of the one state type along
arrows, additive or not, makes the top reading satisfy the satisfaction law:
the reindexed predicate is top while the original is not. -/
theorem counterHyperdoctrine_no_transport
    (push : ∀ {X Y : Psh}, (X ⟶ Y) → BinaryEvidence → BinaryEvidence) :
    ¬ ∀ {X Y : Psh} (f : X ⟶ Y) (W : BinaryEvidence) (φ : Subfunctor Y),
        counterHyperdoctrine.evidenceAt W (counterHyperdoctrine.reindexQuery f φ) =
          counterHyperdoctrine.evidenceAt (push f W) φ := by
  intro law
  have := law pickTrue ⟨1, 0⟩ trueSub
  change (if trueSub.preimage pickTrue = ⊤ then (⟨1, 0⟩ : BinaryEvidence) else 0) =
    (if trueSub = ⊤ then push pickTrue ⟨1, 0⟩ else 0) at this
  rw [if_pos preimage_trueSub_eq_top, if_neg trueSub_ne_top] at this
  exact one_ne_zero (congrArg BinaryEvidence.pos this)

end Counter

end Mettapedia.Logic.WorldModel.Indexed.HyperdoctrineBridge
