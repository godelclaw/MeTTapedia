import Mathlib.Data.Multiset.Filter
import Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelCategoricalBridge

/-!
# A counting WM hyperdoctrine

A concrete WM hyperdoctrine over presheaves on a point, that is, over sets of
individuals with all functions as substitutions.

* **Queries** are predicate codes: atomic predicates and conjunctions
  (`PredicateCode`).  A code means a subfunctor (`PredicateCode.interpret`);
  different codes can mean the same predicate (`and_self_interpret`).
* **Reindexing** is substitution: atoms are pulled back, conjunctions kept
  (`PredicateCode.subst`).  The quantifiers name the image and the universal
  image of the meaning as a new atom.
* **Evidence counts points**: a bag of points of a context gives, for a code,
  the number of points satisfying its meaning and the number refuting it
  (`countEvidence`).

The candidate laws relating evidence to the query operations, tested here:

* **Evidence invariance**, reindexing does not change evidence at a fixed
  state, is **refuted**: the substitution that swaps the two Booleans moves the
  counted point (`counting_reindex_changes_evidence`).
* **Evidence through interpretation**, queries with one meaning have one
  evidence, **holds** (`countingHyperdoctrine`, field `evidence_factors`).
  Negative: the pooling reader, which adds the evidence of the two conjuncts of
  a conjunction, gives `p ∧ p` twice the evidence of `p`
  (`pooling_not_evidenceFactors`).
* **The indexed satisfaction law**, states vary by context and move forward
  along substitutions and a reindexed query read at a state has the evidence of
  the query at the moved state, **holds** with the points moved by the
  substitution (`countingIndexed`).  The pooling reader satisfies it too
  (`poolingIndexed`), so the indexed law does not imply evidence through
  interpretation.

The single state type of `countingHyperdoctrine` is the product of the bags at
all contexts (`CountingState`).  The endpoint, Beck–Chevalley at the evidence
layer, fails on a commuting square that is not a pullback
(`endpointStatement_fails_off_pullback`).
-/

set_option autoImplicit false

namespace Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelCountingHyperdoctrine

open _root_.CategoryTheory Opposite
open Mettapedia.GSLT.Topos
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.Evidence
open Mettapedia.PLN.WorldModel
open Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelHyperdoctrine
open Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelCategoricalBridge
open scoped ENNReal

/-- Contexts: presheaves on a point. -/
abbrev Ctx := (Discrete PUnit.{1})ᵒᵖ ⥤ Type

/-- The only stage of a presheaf on a point. -/
abbrev stage : (Discrete PUnit.{1})ᵒᵖ := op ⟨PUnit.unit⟩

/-- The points of a context. -/
abbrev Pt (X : Ctx) : Type := X.obj stage

/-! ## Predicate codes -/

/-- Predicate codes over a context: atomic predicates and conjunctions. -/
inductive PredicateCode (X : Ctx) : Type
  /-- An atomic predicate. -/
  | atom (S : Subfunctor X)
  /-- A conjunction. -/
  | and (a b : PredicateCode X)

namespace PredicateCode

/-- The predicate a code means. -/
def interpret {X : Ctx} : PredicateCode X → Subfunctor X
  | atom S => S
  | and a b => interpret a ⊓ interpret b

/-- Substitution into a code along `f`: atoms are pulled back, conjunctions
kept. -/
def subst {X Y : Ctx} (f : X ⟶ Y) : PredicateCode Y → PredicateCode X
  | atom S => atom (S.preimage f)
  | and a b => and (subst f a) (subst f b)

/-- Substitution means pulling the meaning back. -/
theorem interpret_subst {X Y : Ctx} (f : X ⟶ Y) (c : PredicateCode Y) :
    (subst f c).interpret = c.interpret.preimage f := by
  induction c with
  | atom S => rfl
  | and a b iha ihb =>
      show (subst f a).interpret ⊓ (subst f b).interpret = (a.interpret ⊓ b.interpret).preimage f
      rw [iha, ihb]
      rfl

theorem subst_id {X : Ctx} (c : PredicateCode X) : subst (𝟙 X) c = c := by
  induction c with
  | atom S => simp [subst]
  | and a b iha ihb => simp [subst, iha, ihb]

theorem subst_comp {X Y Z : Ctx} (f : X ⟶ Y) (g : Y ⟶ Z) (c : PredicateCode Z) :
    subst (f ≫ g) c = subst f (subst g c) := by
  induction c with
  | atom S => simp [subst, Subfunctor.preimage_comp]
  | and a b iha ihb => simp [subst, iha, ihb]

/-- Different codes with one meaning: `p ∧ p` means `p`. -/
theorem and_self_interpret {X : Ctx} (S : Subfunctor X) :
    (and (atom S) (atom S)).interpret = (atom S).interpret := inf_idem _

theorem and_self_ne {X : Ctx} (S : Subfunctor X) : and (atom S) (atom S) ≠ atom S := by
  intro h
  cases h

end PredicateCode

open PredicateCode

/-! ## Counting evidence -/

open Classical in
/-- Evidence of a predicate in a bag of points: the points satisfying it count
positively, the others negatively. -/
noncomputable def countEvidence {X : Ctx} (W : Multiset (Pt X)) (S : Subfunctor X) :
    BinaryEvidence :=
  ⟨(W.countP (· ∈ S.obj stage) : ℝ≥0∞), (W.countP (· ∉ S.obj stage) : ℝ≥0∞)⟩

theorem countEvidence_add {X : Ctx} (W₁ W₂ : Multiset (Pt X)) (S : Subfunctor X) :
    countEvidence (W₁ + W₂) S = countEvidence W₁ S + countEvidence W₂ S := by
  apply BinaryEvidence.ext' <;>
    simp [countEvidence, Multiset.countP_add, BinaryEvidence.hplus_def]

theorem countEvidence_zero {X : Ctx} (S : Subfunctor X) : countEvidence 0 S = 0 := by
  apply BinaryEvidence.ext' <;> simp [countEvidence]

open Classical in
/-- **Counting along a substitution**: counting the pulled-back predicate in a
bag is counting the predicate in the moved bag. -/
theorem countEvidence_map {X Y : Ctx} (f : X ⟶ Y) (W : Multiset (Pt X)) (S : Subfunctor Y) :
    countEvidence (W.map (f.app stage)) S = countEvidence W (S.preimage f) := by
  apply BinaryEvidence.ext'
  · simp only [countEvidence]
    rw [Multiset.countP_map, ← Multiset.countP_eq_card_filter]
    rfl
  · simp only [countEvidence]
    rw [Multiset.countP_map, ← Multiset.countP_eq_card_filter]
    rfl

/-- Counting evidence of one point inside a predicate. -/
theorem countEvidence_singleton_mem {X : Ctx} {x : Pt X} {S : Subfunctor X}
    (hx : x ∈ S.obj stage) : countEvidence {x} S = ⟨1, 0⟩ := by
  classical
  apply BinaryEvidence.ext' <;> simp [countEvidence, ← Multiset.cons_zero, hx]

/-- Counting evidence of one point outside a predicate. -/
theorem countEvidence_singleton_not_mem {X : Ctx} {x : Pt X} {S : Subfunctor X}
    (hx : x ∉ S.obj stage) : countEvidence {x} S = ⟨0, 1⟩ := by
  classical
  apply BinaryEvidence.ext' <;> simp [countEvidence, ← Multiset.cons_zero, hx]

/-! ## The hyperdoctrine -/

/-- One bag of points at every context. -/
abbrev CountingState := ∀ X : Ctx, Multiset (Pt X)

instance : EvidenceType CountingState where

/-- Counting evidence over all contexts at once: a code at `X` reads the bag
at `X`. -/
@[instance_reducible] noncomputable def countingWorldModel :
    WorldModelSigma CountingState Ctx PredicateCode where
  evidence W q := countEvidence (W q.1) q.2.interpret
  evidence_add W₁ W₂ q := countEvidence_add (W₁ q.1) (W₂ q.1) q.2.interpret
  evidence_zero q := countEvidence_zero q.2.interpret

/-- **The counting WM hyperdoctrine.** Presheaves on a point with their
subfunctor predicates, predicate codes as queries, substitution as reindexing,
image and universal image as quantifiers, and counting evidence. -/
noncomputable def countingHyperdoctrine : WMHyperdoctrine CountingState where
  Obj := Ctx
  instCategory := inferInstance
  predFib := presheafPredicateFib (Discrete PUnit.{1})
  query := PredicateCode
  worldModel := countingWorldModel
  reindexQuery f c := c.subst f
  existsQuery f c := .atom (c.interpret.image f)
  forallQuery f c := .atom ((presheafChangeOfBase (Discrete PUnit.{1})).universalImage f c.interpret)
  interpret c := c.interpret
  cob := presheafChangeOfBase (Discrete PUnit.{1})
  beckChevalley := beckChevalleyCondition_presheafChangeOfBase (Discrete PUnit.{1})
  reindex_interp f c := interpret_subst f c
  exists_interp _ _ := rfl
  forall_interp _ _ := rfl
  evidence_factors := by
    intro W X a b same
    change countEvidence (W X) a.interpret = countEvidence (W X) b.interpret
    change a.interpret = b.interpret at same
    rw [same]

theorem countingHyperdoctrine_evidenceAt (W : CountingState) {X : Ctx} (c : PredicateCode X) :
    countingHyperdoctrine.evidenceAt W c = countEvidence (W X) c.interpret :=
  rfl

/-- **Evidence through interpretation has content here**: the distinct codes
`p ∧ p` and `p` have the same evidence at every state, because they mean the
same predicate. -/
theorem counting_and_self_evidence (W : CountingState) {X : Ctx} (S : Subfunctor X) :
    countingHyperdoctrine.evidenceAt W (PredicateCode.and (.atom S) (.atom S)) =
      countingHyperdoctrine.evidenceAt W (PredicateCode.atom S) :=
  countingHyperdoctrine.evidenceAt_eq_of_interpret_eq W (and_self_interpret S)

/-! ## The indexed counting world model -/

/-- Moving a bag of points along a substitution. -/
noncomputable def pushPoints {X Y : Ctx} (f : X ⟶ Y) : Multiset (Pt X) →+ Multiset (Pt Y) where
  toFun W := W.map (f.app stage)
  map_zero' := Multiset.map_zero _
  map_add' := Multiset.map_add _

/-- The counting evidence of a bag, as one additive map into profiles. -/
noncomputable def countProfile (X : Ctx) : Multiset (Pt X) →+ (PredicateCode X → BinaryEvidence) where
  toFun W c := countEvidence W c.interpret
  map_zero' := funext fun c => countEvidence_zero c.interpret
  map_add' W₁ W₂ := funext fun c => countEvidence_add W₁ W₂ c.interpret

/-- **The indexed satisfaction law holds on the counting instance.** Bags of
points at each context, moved forward by the substitution; a substituted code
read at a bag has the evidence of the code at the moved bag. -/
noncomputable def countingIndexed : countingHyperdoctrine.IndexedWorldModel where
  St X := Multiset (Pt X)
  addCommMonoid _ := inferInstance
  push f := pushPoints f
  push_id X W := (Multiset.map_congr rfl fun _ _ => rfl).trans (Multiset.map_id' W)
  push_comp f g W := by
    change W.map ((f ≫ g).app stage) = (W.map (f.app stage)).map (g.app stage)
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun _ _ => rfl
  evidence X := countProfile X
  evidence_reindex f W c := by
    change countEvidence W (c.subst f).interpret = countEvidence (W.map (f.app stage)) c.interpret
    exact (congrArg (countEvidence W) (interpret_subst f c)).trans
      (countEvidence_map f W c.interpret).symm

/-! ## Evidence invariance is refuted: substitution moves points -/

/-- The context of the two Booleans. -/
abbrev boolCtx : Ctx := (Functor.const _).obj Bool

/-- The substitution that swaps the two Booleans. -/
def swap : boolCtx ⟶ boolCtx where
  app _ := ↾(fun b : Bool => !b)

/-- The predicate "is `true`". -/
def isTrue : Subfunctor boolCtx where
  obj _ := {true}
  map _ _ h := h

/-- The state with the one point `true` in the Boolean context. -/
noncomputable def oneTrue : CountingState :=
  open Classical in Function.update (0 : CountingState) boolCtx ({true} : Multiset (Pt boolCtx))

theorem oneTrue_bool : oneTrue boolCtx = ({true} : Multiset (Pt boolCtx)) := by
  classical
  simp [oneTrue]

/-- **Evidence invariance refuted.** Reindexing "is `true`" along the swap
turns the counted point `true` from a confirmation into a refutation. -/
theorem counting_reindex_changes_evidence :
    countingHyperdoctrine.evidenceAt oneTrue
        (countingHyperdoctrine.reindexQuery swap (PredicateCode.atom isTrue)) ≠
      countingHyperdoctrine.evidenceAt oneTrue (PredicateCode.atom isTrue) := by
  intro h
  change countEvidence (oneTrue boolCtx) (isTrue.preimage swap) =
    countEvidence (oneTrue boolCtx) isTrue at h
  rw [oneTrue_bool,
    countEvidence_singleton_not_mem (X := boolCtx) (x := true) (S := isTrue.preimage swap) (by
      change (!true) ∉ ({true} : Set Bool)
      decide),
    countEvidence_singleton_mem (X := boolCtx) (x := true) (S := isTrue) (by
      change true ∈ ({true} : Set Bool)
      exact Set.mem_singleton true)] at h
  exact zero_ne_one (congrArg BinaryEvidence.pos h)

/-- One confirming point for the top predicate. -/
theorem countEvidence_true_top :
    countEvidence ({true} : Multiset (Pt boolCtx)) (⊤ : Subfunctor boolCtx) = ⟨1, 0⟩ :=
  countEvidence_singleton_mem (Set.mem_univ true)

/-! ## Negative for evidence through interpretation: the pooling reader -/

/-- The pooling reader: atoms are counted, and a conjunction gets the sum of
the evidence of its conjuncts. -/
noncomputable def poolEvidence {X : Ctx} (W : Multiset (Pt X)) : PredicateCode X → BinaryEvidence
  | .atom S => countEvidence W S
  | .and a b => poolEvidence W a + poolEvidence W b

theorem poolEvidence_add {X : Ctx} (W₁ W₂ : Multiset (Pt X)) (c : PredicateCode X) :
    poolEvidence (W₁ + W₂) c = poolEvidence W₁ c + poolEvidence W₂ c := by
  induction c with
  | atom S => exact countEvidence_add W₁ W₂ S
  | and a b iha ihb =>
      simp only [poolEvidence, iha, ihb]
      exact add_add_add_comm _ _ _ _

theorem poolEvidence_zero {X : Ctx} (c : PredicateCode X) : poolEvidence 0 c = 0 := by
  induction c with
  | atom S => exact countEvidence_zero S
  | and a b iha ihb => simp only [poolEvidence, iha, ihb, add_zero]

theorem poolEvidence_subst {X Y : Ctx} (f : X ⟶ Y) (W : Multiset (Pt X)) (c : PredicateCode Y) :
    poolEvidence W (c.subst f) = poolEvidence (W.map (f.app stage)) c := by
  induction c with
  | atom S => exact (countEvidence_map f W S).symm
  | and a b iha ihb => simp only [subst, poolEvidence, iha, ihb]

/-- The pooling reader over all contexts at once. -/
@[instance_reducible] noncomputable def poolingWorldModel :
    WorldModelSigma CountingState Ctx PredicateCode where
  evidence W q := poolEvidence (W q.1) q.2
  evidence_add W₁ W₂ q := poolEvidence_add (W₁ q.1) (W₂ q.1) q.2
  evidence_zero q := poolEvidence_zero q.2

/-- **Negative for evidence through interpretation.** The pooling reader gives
`p ∧ p` twice the evidence of `p`, although both mean the same predicate. -/
theorem pooling_not_evidenceFactors :
    ¬ EvidenceFactorsThroughInterpretation poolingWorldModel
      (fun {X : Ctx} (c : PredicateCode X) => c.interpret) := by
  intro factors
  have h := @factors oneTrue boolCtx (.and (.atom ⊤) (.atom ⊤)) (.atom ⊤) (and_self_interpret ⊤)
  change countEvidence (oneTrue boolCtx) ⊤ + countEvidence (oneTrue boolCtx) ⊤ =
    countEvidence (oneTrue boolCtx) ⊤ at h
  rw [oneTrue_bool, countEvidence_true_top] at h
  have two := congrArg BinaryEvidence.pos h
  simp [BinaryEvidence.hplus_def] at two

/-- The pooling reader satisfies the indexed satisfaction law: pooling commutes
with substitution. -/
noncomputable def poolingIndexed : countingHyperdoctrine.IndexedWorldModel where
  St X := Multiset (Pt X)
  addCommMonoid _ := inferInstance
  push f := pushPoints f
  push_id := countingIndexed.push_id
  push_comp := countingIndexed.push_comp
  evidence _ :=
    { toFun := fun W c => poolEvidence W c
      map_zero' := funext poolEvidence_zero
      map_add' := fun W₁ W₂ => funext (poolEvidence_add W₁ W₂) }
  evidence_reindex f W c := poolEvidence_subst f W c

/-- **The indexed law does not imply evidence through interpretation.** The
pooling reader satisfies the indexed law and gives two codes with one meaning
different evidence. -/
theorem poolingIndexed_not_evidenceFactors :
    ∃ (X : Ctx) (W : Multiset (Pt X)) (a b : PredicateCode X),
      a.interpret = b.interpret ∧ poolingIndexed.evidence X W a ≠ poolingIndexed.evidence X W b := by
  refine ⟨boolCtx, ({true} : Multiset (Pt boolCtx)), .and (.atom ⊤) (.atom ⊤), .atom ⊤,
    and_self_interpret ⊤, fun h => ?_⟩
  change countEvidence ({true} : Multiset (Pt boolCtx)) ⊤ +
      countEvidence ({true} : Multiset (Pt boolCtx)) ⊤ =
    countEvidence ({true} : Multiset (Pt boolCtx)) ⊤ at h
  rw [countEvidence_true_top] at h
  have two := congrArg BinaryEvidence.pos h
  simp [BinaryEvidence.hplus_def] at two

/-! ## The endpoint on a pullback and off it -/

/-- The context with one point. -/
abbrev unitCtx : Ctx := (Functor.const _).obj PUnit

/-- The substitution that selects `true`. -/
def selectTrue : unitCtx ⟶ boolCtx where
  app _ := ↾(fun _ => true)

instance : Mono (C := countingHyperdoctrine.Obj) selectTrue := by
  have : ∀ U, Mono (selectTrue.app U) := fun _ => (mono_iff_injective _).2 fun _ _ _ => rfl
  exact NatTrans.mono_of_mono_app selectTrue

/-- The state with the one point of the one-point context. -/
noncomputable def onePoint : CountingState :=
  open Classical in Function.update (0 : CountingState) unitCtx ({PUnit.unit} : Multiset (Pt unitCtx))

theorem onePoint_unit : onePoint unitCtx = ({PUnit.unit} : Multiset (Pt unitCtx)) := by
  classical
  simp [onePoint]

/-- **The endpoint on a pullback, with its value.** On the pullback of
`selectTrue` along itself, reindexing the existential of "is `true`" and taking
the existential of its reindexing both confirm the one point. -/
theorem counting_endpoint_selectTrue :
    countingHyperdoctrine.evidenceAt onePoint
        (countingHyperdoctrine.reindexQuery selectTrue
          (countingHyperdoctrine.existsQuery (𝟙 boolCtx) (PredicateCode.atom isTrue))) = ⟨1, 0⟩ ∧
      countingHyperdoctrine.evidenceAt onePoint
        (countingHyperdoctrine.existsQuery (𝟙 unitCtx)
          (countingHyperdoctrine.reindexQuery selectTrue (PredicateCode.atom isTrue))) = ⟨1, 0⟩ := by
  have bc := countingHyperdoctrine.evidenceAt_beckChevalley_exists (𝟙 unitCtx) selectTrue
    selectTrue (𝟙 boolCtx) (IsPullback.id_horiz selectTrue) onePoint (PredicateCode.atom isTrue)
  have left : countingHyperdoctrine.evidenceAt onePoint
      (countingHyperdoctrine.reindexQuery selectTrue
        (countingHyperdoctrine.existsQuery (𝟙 boolCtx) (PredicateCode.atom isTrue))) = ⟨1, 0⟩ := by
    change countEvidence (onePoint unitCtx) ((isTrue.image (𝟙 boolCtx)).preimage selectTrue) = _
    rw [onePoint_unit]
    refine countEvidence_singleton_mem (X := unitCtx) (x := PUnit.unit) ?_
    show true ∈ ((𝟙 boolCtx : boolCtx ⟶ boolCtx).app stage) '' ({true} : Set Bool)
    exact Set.mem_image_of_mem _ (Set.mem_singleton true)
  exact ⟨left, bc.symm.trans left⟩

/-! ## The endpoint fails off pullbacks -/

/-- The context with no points. -/
abbrev emptyCtx : Ctx := (Functor.const _).obj PEmpty

/-- The substitution out of the empty context. -/
def fromEmpty : emptyCtx ⟶ unitCtx where
  app _ := ↾(fun e : PEmpty => e.elim)

/-- **The endpoint has content.** On the commuting square with the empty
corner over the one-point context, which is not a pullback, reindexing the
existential of the top predicate keeps the point while the existential of the
reindexed predicate loses it. -/
theorem endpointStatement_fails_off_pullback :
    ¬ WMHyperdoctrine.EndpointStatement (H := countingHyperdoctrine)
        fromEmpty fromEmpty (𝟙 unitCtx) (𝟙 unitCtx) onePoint (PredicateCode.atom ⊤) := by
  intro h
  change countEvidence (onePoint unitCtx) (((⊤ : Subfunctor unitCtx).image (𝟙 unitCtx)).preimage
      (𝟙 unitCtx)) =
    countEvidence (onePoint unitCtx) (((⊤ : Subfunctor unitCtx).preimage fromEmpty).image fromEmpty)
    at h
  rw [onePoint_unit,
    countEvidence_singleton_mem (X := unitCtx) (x := PUnit.unit)
      (S := ((⊤ : Subfunctor unitCtx).image (𝟙 unitCtx)).preimage
      (𝟙 unitCtx)) (by
        show PUnit.unit ∈ ((𝟙 unitCtx : unitCtx ⟶ unitCtx).app stage) '' Set.univ
        exact Set.mem_image_of_mem _ (Set.mem_univ _)),
    countEvidence_singleton_not_mem (X := unitCtx) (x := PUnit.unit)
      (S := ((⊤ : Subfunctor unitCtx).preimage fromEmpty).image fromEmpty) (by
        show PUnit.unit ∉ (fromEmpty.app stage) '' ((⊤ : Subfunctor unitCtx).preimage fromEmpty).obj stage
        rintro ⟨e, _, _⟩
        exact e.elim)] at h
  exact one_ne_zero (congrArg BinaryEvidence.pos h)

/-! ## A presentation -/

/-- The counting world model of the Boolean context, on the product state. -/
@[instance_reducible] noncomputable def boolCounting :
    BinaryWorldModel CountingState (PredicateCode boolCtx) where
  evidence W c := countEvidence (W boolCtx) c.interpret
  evidence_add W₁ W₂ c := countEvidence_add (W₁ boolCtx) (W₂ boolCtx) c.interpret
  evidence_zero c := countEvidence_zero c.interpret

/-- **Positive.** The counting hyperdoctrine presents the Boolean counting
world model at the Boolean context. -/
theorem countingHyperdoctrine_presents_boolCounting :
    @WMHyperdoctrine.Presents CountingState _ countingHyperdoctrine boolCtx _ boolCounting id :=
  fun _ _ => rfl

/-- The pooling reader of the Boolean context. -/
@[instance_reducible] noncomputable def boolPooling :
    BinaryWorldModel CountingState (PredicateCode boolCtx) where
  evidence W c := poolEvidence (W boolCtx) c
  evidence_add W₁ W₂ c := poolEvidence_add (W₁ boolCtx) (W₂ boolCtx) c
  evidence_zero c := poolEvidence_zero c

/-- **Negative.** The counting hyperdoctrine does not present the pooling
reader: a presentation forces evidence to factor through interpretation. -/
theorem countingHyperdoctrine_not_presents_boolPooling :
    ¬ @WMHyperdoctrine.Presents CountingState _ countingHyperdoctrine boolCtx _ boolPooling id := by
  intro presents
  have h := @WMHyperdoctrine.Presents.evidence_eq_of_interpret_eq CountingState _
    countingHyperdoctrine boolCtx _ boolPooling id presents oneTrue
    (.and (.atom ⊤) (.atom ⊤)) (.atom ⊤) (and_self_interpret ⊤)
  change poolEvidence (oneTrue boolCtx) (.and (.atom ⊤) (.atom ⊤)) =
    poolEvidence (oneTrue boolCtx) (.atom ⊤) at h
  simp only [poolEvidence] at h
  rw [oneTrue_bool, countEvidence_true_top] at h
  have two := congrArg BinaryEvidence.pos h
  simp [BinaryEvidence.hplus_def] at two

end Mettapedia.PLN.Bridges.CategoryTheory.WorldModel.PLNWorldModelCountingHyperdoctrine
