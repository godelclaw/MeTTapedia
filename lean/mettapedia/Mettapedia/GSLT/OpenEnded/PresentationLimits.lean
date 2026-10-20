import Mettapedia.GSLT.OpenEnded.ClosureSystems
import Mathlib.Computability.Halting
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Preorder.Finite

/-!
# What Horn presentations decide, approximate and detect

This file compares the Horn presentation of a closure system with the other
presentations of `ClosureSystems`, and records what Horn theories give for
families that are not closed under intersections.

* **Horn and dual Horn are exchanged by complement.** Complementing bubbles
  turns intersection-closed families into union-closed ones
  (`intersectionClosed_iff_unionClosed_compl`), and the models of a Horn theory
  into the models of the dual Horn clauses "if the conclusion is retained, one
  of the premises is" (`compl_image_hornModels`, `dualHornModels_unionClosed`).
  Union-closed families are exactly the families with a greatest member below
  every bound (`greatestBelow_iff_unionClosed`).
* **Closure access makes least bubbles cheap.** Two families `{T, univ}` and
  `{T', univ}`, both intersection-closed, answer every membership query other
  than `T` and `T'` alike and have different least members
  (`pairFamily_indistinguishable`, `pairFamily_least_ne`): from membership
  queries alone, finding the least bubble may require querying it. One query
  to the closure at the empty seed answers (`closureIn_pairFamily`). A Horn
  theory provides that access: its closure is computed by forward chaining
  (`ChaoticIteration.fair_firing_computes_hornClosure`).
* **Horn queries are monotone.** Membership in a Horn closure built
  monotonically from a database is monotone in the database
  (`hornQuery_monotone`). Non-reachability is not monotone
  (`nonReachability_not_monotone`), so no such Horn query expresses it
  (`nonReachability_not_hornQuery`); it is the complement of a least fixed
  point (`OpenTopPresentations.compl_cone_eq_gfp`).
* **Hypothetical goals depend on the closure operator.** A goal may add
  assumptions before it is proved. Provability is monotone along extensions of
  the theory (`proves_mono`); assuming facts is applying the closure operator
  to them (`proves_assuming_facts_iff`). Two theories with the same closure of
  the empty seed can differ on a hypothetical goal
  (`same_closure_different_goal`), while two theories with the same Horn models
  agree on every goal (`proves_congr_hornModels`, `chain_proves_iff`).
* **The Horn envelope.** The models of the Horn theory of an arbitrary family
  are its closure under intersections (`hornEnvelope_eq_intersectionClosure`),
  the least Horn-definable family containing it (`hornEnvelope_least`); it
  equals the family exactly when the family is intersection-closed
  (`hornEnvelope_eq_self_iff`). This is the Horn least upper bound of
  knowledge compilation (Selman and Kautz 1996) for definite clauses; allowing
  goal clauses as well only drops the full bubble when the family does not
  contain it. Subfamilies closed under nonempty meets, the model classes of
  Horn theories with goal clauses, are Horn lower bounds, and over finitely
  many generators every member of a family lies in a maximal one
  (`exists_hornGLB_of_mem`, `entails_iff_forall_hornGLB`).
  Entailment by the envelope implies entailment by the family
  (`entails_of_hornEnvelope`), and failure of entailment by a lower bound
  implies failure by the family (`not_entails_of_subset`). For the family
  "retain `true` or retain `false`" the envelope is sound but incomplete, and a
  lower bound's positive answers are not sound (`either_envelope`,
  `either_lowerBound`). Selman and Kautz also show that the envelope of a
  theory can need exponentially more clauses than the theory; that is not
  formalized here.
* **Detecting meet-closure.** For a finite family, closure under nonempty
  meets is closure under pairwise intersections (`meetClosed_iff_inter_mem`),
  which an explicitly given family can be checked for. Adding the requirement
  `x ∨ y` on two fresh generators gives a family that is meet-closed exactly
  when the original family is empty (`withEither_meetClosed_iff`). Read on the
  model sets of propositional formulas, with the classical characterization of
  Horn-equivalence by closure of the models under pairwise intersection, this
  reduces unsatisfiability to equivalence with a Horn formula. For sufficiency computed from programs,
  meet-closure is not decidable: the family "retain `false`, or retain `true`
  and the program halts" is meet-closed exactly when the program does not halt
  (`haltingFamily_meetClosed_iff`, `not_computable_meetClosed`).
* **Sound portfolios.** A strategy that answers only correctly, and otherwise
  gives up, for instance at the end of its budget (`SoundAnswer`), can be run in
  a portfolio with others: under every schedule the portfolio's answer is
  correct (`portfolio_sound`), and two schedules that both answer agree
  (`portfolio_agree`). The Horn envelope gives a sound positive strategy
  (`envelopeAnswer_sound`), exact on intersection-closed families
  (`envelopeAnswer_exact`), and every subfamily gives a sound negative strategy
  (`lowerBoundAnswer_sound`); their portfolio is sound under every schedule
  (`hornPortfolio_sound`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.OpenEnded.PresentationLimits

open Set
open Mettapedia.GSLT.OpenEnded.SufficientBubbles
open Mettapedia.GSLT.OpenEnded.ClosureSystems

universe u v

variable {G : Type u}

/-! ## Horn and dual Horn clauses -/

/-- Closed under all unions, including the empty one. -/
def UnionClosed (F : Set (Set G)) : Prop :=
  ∀ F' ⊆ F, ⋃₀ F' ∈ F

theorem intersectionClosed_iff_unionClosed_compl (F : Set (Set G)) :
    IntersectionClosed F ↔ UnionClosed (compl '' F) := by
  constructor
  · intro closed F' included
    have back : compl '' F' ⊆ F := by
      rintro _ ⟨S, member, rfl⟩
      obtain ⟨T, memberT, rfl⟩ := included member
      rw [compl_compl]
      exact memberT
    refine ⟨⋂₀ (compl '' F'), closed _ back, ?_⟩
    rw [compl_sInter, image_image]
    simp only [compl_compl, image_id']
  · intro closed F' included
    have mapped : compl '' F' ⊆ compl '' F := image_mono included
    obtain ⟨S, member, same⟩ := closed _ mapped
    have equal : S = ⋂₀ F' := by
      rw [← compl_compl S, same, compl_sUnion, image_image]
      simp only [compl_compl, image_id']
    exact equal ▸ member

/-- The models of the dual Horn clauses of a theory: if the conclusion is
retained, one of the premises is. -/
def dualHornModels (theory : Set (HornClause G)) : Set (Set G) :=
  {S | ∀ clause ∈ theory, clause.conclusion ∈ S → ∃ p ∈ clause.premises, p ∈ S}

/-- **Complementing turns Horn models into dual Horn models.** -/
theorem compl_image_hornModels (theory : Set (HornClause G)) :
    compl '' hornModels theory = dualHornModels theory := by
  ext S
  constructor
  · rintro ⟨T, closed, rfl⟩ clause member retained
    by_contra none
    exact retained (closed clause member fun p inPremises => by
      by_contra absent
      exact none ⟨p, inPremises, absent⟩)
  · intro dual
    refine ⟨Sᶜ, fun clause member premisesIn => ?_, compl_compl S⟩
    by_contra inS
    rw [mem_compl_iff, not_not] at inS
    obtain ⟨p, inPremises, inS'⟩ := dual clause member inS
    exact premisesIn inPremises inS'

theorem dualHornModels_unionClosed (theory : Set (HornClause G)) :
    UnionClosed (dualHornModels theory) := by
  intro F' included clause member ⟨S, memberS, inS⟩
  obtain ⟨p, inPremises, inP⟩ := included memberS clause member inS
  exact ⟨p, inPremises, S, memberS, inP⟩

def GreatestBelowEvery (F : Set (Set G)) : Prop :=
  ∀ A : Set G, ∃ greatest, IsGreatest {S | S ∈ F ∧ S ⊆ A} greatest

/-- **Greatest bubbles below every bound exist exactly for union-closed
families.** -/
theorem greatestBelow_iff_unionClosed (F : Set (Set G)) :
    GreatestBelowEvery F ↔ UnionClosed F := by
  constructor
  · intro greatestBelow F' included
    obtain ⟨greatest, ⟨memberF, below⟩, upper⟩ := greatestBelow (⋃₀ F')
    have outside : ⋃₀ F' ⊆ greatest :=
      sUnion_subset fun S member => upper ⟨included member, subset_sUnion_of_mem member⟩
    exact (subset_antisymm below outside) ▸ memberF
  · intro closed A
    refine ⟨⋃₀ {S | S ∈ F ∧ S ⊆ A}, ⟨closed _ fun _ member => member.1,
      sUnion_subset fun _ member => member.2⟩, fun _ member => subset_sUnion_of_mem member⟩

/-! ## Computing the least bubble needs closure access -/

/-- A family with one hidden least member. -/
def pairFamily (T : Set G) : Set (Set G) :=
  {T, univ}

theorem pairFamily_intersectionClosed (T : Set G) : IntersectionClosed (pairFamily T) := by
  intro F' included
  by_cases hidden : T ∈ F'
  · left
    apply subset_antisymm (sInter_subset_of_mem hidden)
    intro g member S memberS
    rcases included memberS with rfl | rfl
    · exact member
    · exact mem_univ g
  · right
    apply eq_univ_of_forall
    intro g S memberS
    rcases included memberS with rfl | rfl
    · exact absurd memberS hidden
    · exact mem_univ g

theorem pairFamily_least (T : Set G) : IsLeast (pairFamily T) T :=
  ⟨Or.inl rfl, fun S member => by
    rcases member with rfl | rfl
    · exact subset_rfl
    · exact subset_univ T⟩

/-- **Membership queries other than the hidden members cannot tell two
families apart.** -/
theorem pairFamily_indistinguishable {Q : Set (Set G)} {T T' : Set G} (notT : T ∉ Q)
    (notT' : T' ∉ Q) : ∀ S ∈ Q, S ∈ pairFamily T ↔ S ∈ pairFamily T' := by
  intro S member
  have differentT : S ≠ T := fun same => notT (same ▸ member)
  have differentT' : S ≠ T' := fun same => notT' (same ▸ member)
  constructor
  · rintro (same | same)
    · exact absurd same differentT
    · exact Or.inr same
  · rintro (same | same)
    · exact absurd same differentT'
    · exact Or.inr same

/-- The two families have different least members. -/
theorem pairFamily_least_ne {T T' : Set G} (different : T ≠ T') :
    ∀ m m', IsLeast (pairFamily T) m → IsLeast (pairFamily T') m' → m ≠ m' :=
  fun _ _ least least' same =>
    different ((least.unique (pairFamily_least T)).symm.trans
      (same.trans (least'.unique (pairFamily_least T'))))

/-- **One closure query answers.** -/
theorem closureIn_pairFamily (T : Set G) : closureIn (pairFamily T) ∅ = T := by
  apply subset_antisymm
  · exact sInter_subset_of_mem ⟨Or.inl rfl, empty_subset T⟩
  · intro g member S ⟨memberS, _⟩
    exact (pairFamily_least T).2 memberS member

/-! ## Horn queries are monotone -/

theorem hornClosure_mono {A : Type u} {theory theory' : Set (HornClause A)}
    {seeds seeds' : Set A} (moreRules : theory ⊆ theory') (moreSeeds : seeds ⊆ seeds') :
    hornClosure theory seeds ⊆ hornClosure theory' seeds' := by
  intro g generated
  induction generated with
  | seed member => exact HornDerivable.seed (moreSeeds member)
  | rule clause member _ ih => exact HornDerivable.rule clause (moreRules member) ih

/-- A query of a database that survives adding facts. -/
def MonotoneQuery {E : Type v} (query : Set E → Prop) : Prop :=
  ∀ ⦃D D' : Set E⦄, D ⊆ D' → query D → query D'

/-- **Membership in a Horn closure built monotonically from a database is a
monotone query.** -/
theorem hornQuery_monotone {E : Type v} {A : Type u}
    (theoryOf : Set E → Set (HornClause A)) (seedsOf : Set E → Set A)
    (monotoneTheory : Monotone theoryOf) (monotoneSeeds : Monotone seedsOf) (g : A) :
    MonotoneQuery (fun D => g ∈ hornClosure (theoryOf D) (seedsOf D)) :=
  fun _ _ included member =>
    hornClosure_mono (monotoneTheory included) (monotoneSeeds included) member

/-- The edges of a graph as Horn clauses. -/
def edgeTheory {V : Type u} (D : Set (V × V)) : Set (HornClause V) :=
  {clause | ∃ e ∈ D, clause = ⟨{e.1}, e.2⟩}

theorem reach_of_edge {V : Type u} {D : Set (V × V)} {a b : V} (edge : (a, b) ∈ D) :
    b ∈ hornClosure (edgeTheory D) {a} :=
  HornDerivable.rule ⟨{a}, b⟩ ⟨(a, b), edge, rfl⟩ fun _ member =>
    HornDerivable.seed member

theorem not_reach_without_edges {V : Type u} {a b : V} (different : a ≠ b) :
    b ∉ hornClosure (edgeTheory (∅ : Set (V × V))) {a} := by
  intro generated
  generalize same : b = target at generated
  induction generated with
  | seed member => exact different ((mem_singleton_iff.mp member).symm.trans same.symm)
  | rule clause member _ _ =>
      obtain ⟨_, absurd, _⟩ := member
      exact absurd

/-- **Non-reachability is not a monotone query.** -/
theorem nonReachability_not_monotone :
    ¬ MonotoneQuery (fun D : Set (Bool × Bool) => true ∉ hornClosure (edgeTheory D) {false}) := by
  intro monotone
  have before : true ∉ hornClosure (edgeTheory (∅ : Set (Bool × Bool))) {false} :=
    not_reach_without_edges (by decide)
  exact monotone (empty_subset {(false, true)}) before (reach_of_edge (mem_singleton _))

/-- **No Horn closure built monotonically from the edges expresses
non-reachability.** -/
theorem nonReachability_not_hornQuery (A : Type u) :
    ¬ ∃ (theoryOf : Set (Bool × Bool) → Set (HornClause A)) (seedsOf : Set (Bool × Bool) → Set A),
        Monotone theoryOf ∧ Monotone seedsOf ∧ ∃ g : A, ∀ D,
          (g ∈ hornClosure (theoryOf D) (seedsOf D) ↔
            true ∉ hornClosure (edgeTheory D) {false}) := by
  rintro ⟨theoryOf, seedsOf, monotoneTheory, monotoneSeeds, g, expresses⟩
  apply nonReachability_not_monotone
  intro D D' included holds
  exact (expresses D').mp (hornQuery_monotone theoryOf seedsOf monotoneTheory
    monotoneSeeds g included ((expresses D).mpr holds))

/-! ## Hypothetical goals depend on the closure operator -/

/-- Goals that may add assumptions before they are proved. -/
inductive Goal (A : Type u)
  | atom (a : A)
  | both (first second : Goal A)
  | assuming (extra : Set (HornClause A)) (goal : Goal A)

/-- Provability of a goal from a theory: an atom is in the Horn closure of the
empty seed; assumptions extend the theory. -/
def proves {A : Type u} : Set (HornClause A) → Goal A → Prop
  | theory, .atom a => a ∈ hornClosure theory ∅
  | theory, .both first second => proves theory first ∧ proves theory second
  | theory, .assuming extra goal => proves (theory ∪ extra) goal

/-- **Provability is monotone along extensions of the theory.** -/
theorem proves_mono {A : Type u} (goal : Goal A) :
    ∀ {theory theory' : Set (HornClause A)}, theory ⊆ theory' → proves theory goal →
      proves theory' goal := by
  induction goal with
  | atom a =>
      intro theory theory' included holds
      exact hornClosure_mono included subset_rfl holds
  | both first second ihFirst ihSecond =>
      intro theory theory' included holds
      exact ⟨ihFirst included holds.1, ihSecond included holds.2⟩
  | assuming extra goal ih =>
      intro theory theory' included holds
      exact ih (union_subset_union_left extra included) holds

/-- Facts as Horn clauses without premises. -/
def factsOf {A : Type u} (E : Set A) : Set (HornClause A) :=
  {clause | clause.premises = ∅ ∧ clause.conclusion ∈ E}

theorem hornClosure_union_facts {A : Type u} (theory : Set (HornClause A)) (E : Set A) :
    hornClosure (theory ∪ factsOf E) ∅ = hornClosure theory E := by
  have same : {S | S ∈ hornModels (theory ∪ factsOf E) ∧ (∅ : Set A) ⊆ S} =
      {S | S ∈ hornModels theory ∧ E ⊆ S} := by
    ext S
    constructor
    · rintro ⟨closed, _⟩
      refine ⟨fun clause member => closed clause (Or.inl member), fun e member => ?_⟩
      exact closed ⟨∅, e⟩ (Or.inr ⟨rfl, member⟩) (empty_subset S)
    · rintro ⟨closed, seedsIn⟩
      refine ⟨fun clause member premisesIn => ?_, empty_subset S⟩
      rcases member with inTheory | ⟨_, inE⟩
      · exact closed clause inTheory premisesIn
      · exact seedsIn inE
  have least := isLeast_hornClosure (theory ∪ factsOf E) ∅
  rw [same] at least
  exact least.unique (isLeast_hornClosure theory E)

/-- **Assuming facts is applying the closure operator to them.** -/
theorem proves_assuming_facts_iff {A : Type u} (theory : Set (HornClause A)) (E : Set A) (a : A) :
    proves theory (.assuming (factsOf E) (.atom a)) ↔ a ∈ hornClosure theory E := by
  change a ∈ hornClosure (theory ∪ factsOf E) ∅ ↔ _
  rw [hornClosure_union_facts]

/-- Two atoms for the hypothetical example. -/
inductive Letter
  | a
  | b
  deriving DecidableEq

section LetterExample

open Letter

/-- **The closure of one seed does not determine provability.** The empty
theory and the theory "`a` requires `b`" generate nothing from the empty seed,
and differ on the goal "assuming `a`, prove `b`". -/
theorem same_closure_different_goal :
    hornClosure (∅ : Set (HornClause Letter)) ∅ =
        hornClosure ({⟨{a}, b⟩} : Set (HornClause Letter)) ∅ ∧
      ¬ proves (∅ : Set (HornClause Letter)) (.assuming (factsOf {a}) (.atom b)) ∧
      proves ({⟨{a}, b⟩} : Set (HornClause Letter)) (.assuming (factsOf {a}) (.atom b)) := by
  have emptyClosure : ∀ theory : Set (HornClause Letter),
      (∀ clause ∈ theory, clause.premises.Nonempty) → hornClosure theory ∅ = ∅ := by
    intro theory premised
    apply eq_empty_of_forall_notMem
    intro g generated
    induction generated with
    | seed member => exact member
    | rule clause member _ ih =>
        obtain ⟨p, inPremises⟩ := premised clause member
        exact ih p inPremises
  refine ⟨?_, ?_, ?_⟩
  · rw [emptyClosure ∅ (fun _ member => absurd member (notMem_empty _)),
      emptyClosure {⟨{a}, b⟩} (fun _ member => by rw [mem_singleton_iff.mp member]; exact ⟨a, rfl⟩)]
  · rw [proves_assuming_facts_iff]
    intro generated
    generalize same : b = target at generated
    induction generated with
    | seed member =>
        have isA : _ = a := member
        rw [isA] at same
        cases same
    | rule clause member _ _ => exact member
  · rw [proves_assuming_facts_iff]
    exact HornDerivable.rule ⟨{a}, b⟩ rfl fun _ member => HornDerivable.seed member

end LetterExample

/-- The Horn models of a union of theories are the common models. -/
theorem hornModels_union {A : Type u} (theory extra : Set (HornClause A)) :
    hornModels (theory ∪ extra) = hornModels theory ∩ hornModels extra := by
  ext S
  constructor
  · intro holds
    exact ⟨fun clause member => holds clause (Or.inl member),
      fun clause member => holds clause (Or.inr member)⟩
  · rintro ⟨holds, holds'⟩ clause (member | member)
    · exact holds clause member
    · exact holds' clause member

/-- **Provability of hypothetical goals depends only on the Horn models of the
theory.** -/
theorem proves_congr_hornModels {A : Type u} (goal : Goal A) :
    ∀ {theory theory' : Set (HornClause A)}, hornModels theory = hornModels theory' →
      (proves theory goal ↔ proves theory' goal) := by
  induction goal with
  | atom a =>
      intro theory theory' same
      have closure : hornClosure theory ∅ = hornClosure theory' ∅ := by
        have least := isLeast_hornClosure theory ∅
        rw [same] at least
        exact least.unique (isLeast_hornClosure theory' ∅)
      change a ∈ hornClosure theory ∅ ↔ a ∈ hornClosure theory' ∅
      rw [closure]
  | both first second ihFirst ihSecond =>
      intro theory theory' same
      exact and_congr (ihFirst same) (ihSecond same)
  | assuming extra goal ih =>
      intro theory theory' same
      apply ih
      rw [hornModels_union, hornModels_union, same]

/-- A positive example: the two Horn theories of `ClosureSystems` with the same
models agree on every goal. -/
theorem chain_proves_iff (goal : Goal ClosureSystems.Tri) :
    proves chainTheory goal ↔ proves chainTheory' goal :=
  proves_congr_hornModels goal chain_hornModels_eq

/-! ## The Horn envelope -/

/-- The Horn envelope of a family of bubbles: the models of its Horn theory. -/
def hornEnvelope (F : Set (Set G)) : Set (Set G) :=
  hornModels (hornTheoryOf F)

/-- A bubble is in the envelope exactly when every generator that lies in all
members of the family above it is already in it. -/
theorem mem_hornEnvelope_iff {F : Set (Set G)} {S : Set G} :
    S ∈ hornEnvelope F ↔ closureIn F S ⊆ S := by
  constructor
  · intro holds g member
    exact holds ⟨S, g⟩ member subset_rfl
  · intro closed clause valid premisesIn
    exact closed (closureIn_mono F premisesIn valid)

/-- **The Horn envelope of a family is its closure under intersections.** -/
theorem hornEnvelope_eq_intersectionClosure (F : Set (Set G)) :
    hornEnvelope F = {S | ∃ F' ⊆ F, ⋂₀ F' = S} := by
  ext S
  rw [mem_hornEnvelope_iff]
  constructor
  · intro closed
    refine ⟨{T | T ∈ F ∧ S ⊆ T}, fun T member => member.1, ?_⟩
    exact subset_antisymm closed (subset_closureIn F S)
  · rintro ⟨F', included, rfl⟩
    exact sInter_subset_sInter fun T member => ⟨included member, sInter_subset_of_mem member⟩

theorem subset_hornEnvelope (F : Set (Set G)) : F ⊆ hornEnvelope F :=
  subset_hornModels_hornTheoryOf F

/-- **The Horn envelope is the least Horn-definable family containing the
family.** -/
theorem hornEnvelope_least {F : Set (Set G)} {theory : Set (HornClause G)}
    (included : F ⊆ hornModels theory) : hornEnvelope F ⊆ hornModels theory := by
  rw [hornEnvelope_eq_intersectionClosure]
  rintro _ ⟨F', inside, rfl⟩
  exact hornModels_sInter_mem theory F' (inside.trans included)

/-- **A family is its own Horn envelope exactly when it is intersection-closed.** -/
theorem hornEnvelope_eq_self_iff (F : Set (Set G)) :
    hornEnvelope F = F ↔ IntersectionClosed F := by
  constructor
  · intro same F' included
    rw [← same]
    exact hornModels_sInter_mem _ F' (included.trans (subset_hornEnvelope F))
  · exact models_hornTheoryOf

/-- A family entails a property of bubbles when every member has it. -/
def Entails (F : Set (Set G)) (q : Set G → Prop) : Prop :=
  ∀ S ∈ F, q S

/-- **Entailment by the Horn envelope is sound for the family.** -/
theorem entails_of_hornEnvelope {F : Set (Set G)} {q : Set G → Prop}
    (entails : Entails (hornEnvelope F) q) : Entails F q :=
  fun S member => entails S (subset_hornEnvelope F member)

/-- **Failure of entailment by a subfamily is sound for the family.** -/
theorem not_entails_of_subset {F H : Set (Set G)} {q : Set G → Prop} (lower : H ⊆ F)
    (fails : ¬ Entails H q) : ¬ Entails F q :=
  fun entails => fails fun S member => entails S (lower member)

/-- A Horn lower bound of a family: a subfamily closed under nonempty meets. -/
def IsHornLowerBound (F H : Set (Set G)) : Prop :=
  H ⊆ F ∧ MeetClosed (· ∈ H)

/-- A Horn greatest lower bound: a maximal Horn lower bound. -/
def IsHornGLB (F H : Set (Set G)) : Prop :=
  Maximal (IsHornLowerBound F) H

theorem isHornLowerBound_singleton {F : Set (Set G)} {S : Set G} (member : S ∈ F) :
    IsHornLowerBound F {S} := by
  refine ⟨singleton_subset_iff.mpr member, fun F' nonempty allIn => ?_⟩
  have same : F' = {S} := (Set.Nonempty.subset_singleton_iff nonempty).mp allIn
  rw [same, sInter_singleton]
  exact mem_singleton S

/-- **Over finitely many generators every member of a family lies in a Horn
greatest lower bound.** -/
theorem exists_hornGLB_of_mem [Finite G] {F : Set (Set G)} {S : Set G} (member : S ∈ F) :
    ∃ H, S ∈ H ∧ IsHornGLB F H := by
  obtain ⟨H, below, maximal⟩ := _root_.Finite.exists_le_maximal (isHornLowerBound_singleton member)
  exact ⟨H, below (mem_singleton S), maximal⟩

/-- **Over finitely many generators a family entails a property exactly when
all of its Horn greatest lower bounds do.** -/
theorem entails_iff_forall_hornGLB [Finite G] (F : Set (Set G)) (q : Set G → Prop) :
    Entails F q ↔ ∀ H, IsHornGLB F H → Entails H q := by
  constructor
  · intro entails H glb S member
    exact entails S (glb.prop.1 member)
  · intro each S member
    obtain ⟨H, inH, glb⟩ := exists_hornGLB_of_mem member
    exact each H glb S inH

/-- Retain `true`, or retain `false`. -/
def eitherFamily : Set (Set Bool) :=
  {{true}, {false}}

theorem sInter_eitherFamily : ⋂₀ eitherFamily = ∅ := by
  rw [eitherFamily, sInter_pair]
  ext b
  cases b <;> simp

theorem empty_not_mem_eitherFamily : (∅ : Set Bool) ∉ eitherFamily := by
  rintro (same | same)
  · exact singleton_ne_empty true same.symm
  · exact singleton_ne_empty false (show (∅ : Set Bool) = {false} from same).symm

/-- **The either-family is not closed under nonempty meets.** -/
theorem eitherFamily_not_meetClosed : ¬ MeetClosed (· ∈ eitherFamily) := fun closed => by
  have meet := closed eitherFamily ⟨{true}, Or.inl rfl⟩ fun _ member => member
  rw [sInter_eitherFamily] at meet
  exact empty_not_mem_eitherFamily meet

/-- **The envelope of the either-family is sound but incomplete**: the family
entails "something is retained", the envelope, which contains the empty
bubble, does not. -/
theorem either_envelope :
    Entails eitherFamily Set.Nonempty ∧ ∅ ∈ hornEnvelope eitherFamily ∧
      ¬ Entails (hornEnvelope eitherFamily) Set.Nonempty := by
  have empty : ∅ ∈ hornEnvelope eitherFamily := by
    rw [hornEnvelope_eq_intersectionClosure]
    exact ⟨eitherFamily, subset_rfl, sInter_eitherFamily⟩
  refine ⟨?_, empty, fun entails => (entails ∅ empty).ne_empty rfl⟩
  rintro S (rfl | rfl)
  · exact singleton_nonempty true
  · exact singleton_nonempty false

/-- **Lower bounds answer "no" soundly and "yes" unsoundly.** The lower bound
`{{true}}` entails "`true` is retained", which the family does not; the lower
bound `{{false}}` does not entail it, and neither does the family. -/
theorem either_lowerBound :
    IsHornLowerBound eitherFamily {{true}} ∧ Entails {{true}} (true ∈ ·) ∧
      IsHornLowerBound eitherFamily {{false}} ∧ ¬ Entails {{false}} (true ∈ ·) ∧
      ¬ Entails eitherFamily (true ∈ ·) := by
  have notTrue : ¬ Entails ({{false}} : Set (Set Bool)) (true ∈ ·) := fun entails => by
    have retained : true ∈ ({false} : Set Bool) := entails {false} (mem_singleton _)
    simp at retained
  refine ⟨isHornLowerBound_singleton (Or.inl rfl), fun S member => ?_,
    isHornLowerBound_singleton (Or.inr rfl), notTrue,
    not_entails_of_subset (singleton_subset_iff.mpr (Or.inr rfl)) notTrue⟩
  rw [mem_singleton_iff.mp member]
  exact mem_singleton true

/-! ## Detecting meet-closure -/

/-- **For a finite family, closure under nonempty meets is closure under
pairwise intersections.** -/
theorem meetClosed_iff_inter_mem {H : Set (Set G)} (finite : H.Finite) :
    MeetClosed (· ∈ H) ↔ ∀ S ∈ H, ∀ T ∈ H, S ∩ T ∈ H := by
  constructor
  · intro closed S memberS T memberT
    have meet := closed {S, T} ⟨S, mem_insert S _⟩ (by rintro U (rfl | rfl) <;> assumption)
    rwa [sInter_pair] at meet
  · intro pairwise F nonempty allIn
    refine Set.Finite.induction_on
      (motive := fun F _ => F.Nonempty → (∀ S ∈ F, S ∈ H) → ⋂₀ F ∈ H) F
      (finite.subset allIn) ?_ ?_ nonempty allIn
    · rintro ⟨_, absurd⟩
      exact absurd.elim
    · intro a s _ _ ih _ inH
      rw [sInter_insert]
      by_cases empty : s = ∅
      · rw [empty, sInter_empty, inter_univ]
        exact inH a (mem_insert a s)
      · exact pairwise a (inH a (mem_insert a s)) _
          (ih (nonempty_iff_ne_empty.mpr empty) fun S member => inH S (mem_insert_of_mem a member))

/-- Adding the requirement `x ∨ y` on two fresh generators `x`, `y`. -/
def withEither (F : Set (Set G)) : Set (Set (G ⊕ Bool)) :=
  {S | Sum.inl ⁻¹' S ∈ F ∧ (Sum.inr true ∈ S ∨ Sum.inr false ∈ S)}

theorem preimage_inl_image_union (S : Set G) (b : Bool) :
    Sum.inl ⁻¹' (Sum.inl '' S ∪ {Sum.inr b} : Set (G ⊕ Bool)) = S := by
  ext g
  simp

/-- **The gadget is meet-closed exactly when the family is empty.** -/
theorem withEither_meetClosed_iff (F : Set (Set G)) :
    MeetClosed (· ∈ withEither F) ↔ F = ∅ := by
  constructor
  · intro closed
    apply eq_empty_of_forall_notMem
    intro S member
    have leftIn : (Sum.inl '' S ∪ {Sum.inr true} : Set (G ⊕ Bool)) ∈ withEither F := by
      refine ⟨?_, Or.inl (Or.inr rfl)⟩
      rw [preimage_inl_image_union]
      exact member
    have rightIn : (Sum.inl '' S ∪ {Sum.inr false} : Set (G ⊕ Bool)) ∈ withEither F := by
      refine ⟨?_, Or.inr (Or.inr rfl)⟩
      rw [preimage_inl_image_union]
      exact member
    have meet := closed {Sum.inl '' S ∪ {Sum.inr true}, Sum.inl '' S ∪ {Sum.inr false}}
      ⟨_, mem_insert _ _⟩ (by rintro T (rfl | rfl) <;> assumption)
    rw [sInter_pair] at meet
    rcases meet.2 with inBoth | inBoth
    · simp at inBoth
    · simp at inBoth
  · rintro rfl F' ⟨T, memberT⟩ allIn
    exact (allIn T memberT).1.elim

/-- Sufficiency computed from a program: retain `false`, or retain `true` and
the program halts on input `0`. -/
def haltingFamily (c : Nat.Partrec.Code) (S : Set Bool) : Prop :=
  false ∈ S ∨ (true ∈ S ∧ (Nat.Partrec.Code.eval c 0).Dom)

/-- **The program's family is meet-closed exactly when the program does not
halt.** -/
theorem haltingFamily_meetClosed_iff (c : Nat.Partrec.Code) :
    MeetClosed (haltingFamily c) ↔ ¬ (Nat.Partrec.Code.eval c 0).Dom := by
  constructor
  · intro closed halts
    have meet := closed {{false}, {true}} ⟨{false}, mem_insert _ _⟩ (by
      rintro S (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr ⟨rfl, halts⟩)
    rw [sInter_pair] at meet
    rcases meet with inBoth | ⟨inBoth, _⟩
    · simp at inBoth
    · simp at inBoth
  · intro loops F _ allSufficient
    left
    intro S member
    rcases allSufficient S member with retained | ⟨_, halts⟩
    · exact retained
    · exact absurd halts loops

/-- **Meet-closure of sufficiency computed from programs is not decidable.** -/
theorem not_computable_meetClosed :
    ¬ ComputablePred fun c : Nat.Partrec.Code => MeetClosed (haltingFamily c) := by
  intro computable
  have same : (fun c : Nat.Partrec.Code => MeetClosed (haltingFamily c)) =
      fun c => ¬ (Nat.Partrec.Code.eval c 0).Dom :=
    funext fun c => propext (haltingFamily_meetClosed_iff c)
  rw [same] at computable
  have halting := computable.not
  have doubleNegation : (fun c : Nat.Partrec.Code => ¬ ¬ (Nat.Partrec.Code.eval c 0).Dom) =
      fun c => (Nat.Partrec.Code.eval c 0).Dom :=
    funext fun c => propext not_not
  rw [doubleNegation] at halting
  exact ComputablePred.halting_problem 0 halting

/-! ## Sound portfolios -/

/-- An answer about a proposition is sound when every answer it gives is
correct; `none` means that the strategy gave up. -/
def SoundAnswer (p : Prop) (answer : Option Bool) : Prop :=
  ∀ b, answer = some b → (b = true ↔ p)

/-- The first answer of the strategies, in the order of a schedule. -/
def portfolio : List (Option Bool) → Option Bool
  | [] => none
  | some b :: _ => some b
  | none :: rest => portfolio rest

/-- **A portfolio of sound strategies is sound.** -/
theorem portfolio_sound {p : Prop} :
    ∀ {answers : List (Option Bool)}, (∀ a ∈ answers, SoundAnswer p a) →
      SoundAnswer p (portfolio answers)
  | [], _ => fun _ absurd => by cases absurd
  | some b :: _, sound => sound (some b) List.mem_cons_self
  | none :: rest, sound =>
      portfolio_sound (answers := rest) fun a member => sound a (List.mem_cons_of_mem _ member)

/-- **Two schedules of sound strategies that both answer give the same
answer.** -/
theorem portfolio_agree {p : Prop} {first second : List (Option Bool)}
    (soundFirst : ∀ a ∈ first, SoundAnswer p a) (soundSecond : ∀ a ∈ second, SoundAnswer p a)
    {b b' : Bool} (answered : portfolio first = some b) (answered' : portfolio second = some b') :
    b = b' :=
  Bool.eq_iff_iff.mpr ((portfolio_sound soundFirst b answered).trans
    (portfolio_sound soundSecond b' answered').symm)

open Classical in
/-- The envelope strategy: answer "yes" when the Horn envelope entails the
property, otherwise give up. -/
noncomputable def envelopeAnswer (F : Set (Set G)) (q : Set G → Prop) : Option Bool :=
  if Entails (hornEnvelope F) q then some true else none

open Classical in
/-- A lower-bound strategy: answer "no" when the subfamily fails the property,
otherwise give up. -/
noncomputable def lowerBoundAnswer (H : Set (Set G)) (q : Set G → Prop) : Option Bool :=
  if Entails H q then none else some false

theorem envelopeAnswer_sound (F : Set (Set G)) (q : Set G → Prop) :
    SoundAnswer (Entails F q) (envelopeAnswer F q) := by
  intro b answered
  by_cases entails : Entails (hornEnvelope F) q
  · rw [envelopeAnswer, if_pos entails] at answered
    cases answered
    exact ⟨fun _ => entails_of_hornEnvelope entails, fun _ => rfl⟩
  · rw [envelopeAnswer, if_neg entails] at answered
    cases answered

theorem lowerBoundAnswer_sound {F H : Set (Set G)} (lower : H ⊆ F) (q : Set G → Prop) :
    SoundAnswer (Entails F q) (lowerBoundAnswer H q) := by
  intro b answered
  by_cases entails : Entails H q
  · rw [lowerBoundAnswer, if_pos entails] at answered
    cases answered
  · rw [lowerBoundAnswer, if_neg entails] at answered
    cases answered
    exact ⟨fun absurd => (by cases absurd), fun entailsF => absurd entailsF
      (not_entails_of_subset lower entails)⟩

/-- **On an intersection-closed family the envelope strategy is exact.** -/
theorem envelopeAnswer_exact {F : Set (Set G)} (closed : IntersectionClosed F)
    (q : Set G → Prop) : envelopeAnswer F q = some true ↔ Entails F q := by
  rw [envelopeAnswer, (hornEnvelope_eq_self_iff F).mpr closed]
  by_cases entails : Entails F q
  · rw [if_pos entails]
    exact ⟨fun _ => entails, fun _ => rfl⟩
  · rw [if_neg entails]
    exact ⟨fun absurd => (by cases absurd), fun entailsF => absurd entailsF entails⟩

/-- **The Horn portfolio is sound under every schedule**: the envelope
strategy, a lower-bound strategy and any other sound strategies, in any
order. -/
theorem hornPortfolio_sound {F H : Set (Set G)} {q : Set G → Prop} (lower : H ⊆ F)
    {others schedule : List (Option Bool)}
    (soundOthers : ∀ a ∈ others, SoundAnswer (Entails F q) a)
    (reordered : schedule.Perm (envelopeAnswer F q :: lowerBoundAnswer H q :: others)) :
    SoundAnswer (Entails F q) (portfolio schedule) := by
  refine portfolio_sound fun a member => ?_
  rcases List.mem_cons.mp (reordered.mem_iff.mp member) with rfl | rest
  · exact envelopeAnswer_sound F q
  · rcases List.mem_cons.mp rest with rfl | other
    · exact lowerBoundAnswer_sound lower q
    · exact soundOthers a other

/-- On the either-family, the envelope gives up on "`true` is retained" and the
lower bound `{{false}}` answers "no", correctly. -/
theorem either_portfolio :
    portfolio [envelopeAnswer eitherFamily (true ∈ ·), lowerBoundAnswer {{false}} (true ∈ ·)] =
      some false := by
  have notEnvelope : ¬ Entails (hornEnvelope eitherFamily) (true ∈ ·) := fun entails =>
    either_lowerBound.2.2.2.2 (entails_of_hornEnvelope entails)
  have notLower : ¬ Entails ({{false}} : Set (Set Bool)) (true ∈ ·) := either_lowerBound.2.2.2.1
  classical
  simp only [envelopeAnswer, lowerBoundAnswer, if_neg notEnvelope, if_neg notLower, portfolio]

#print axioms intersectionClosed_iff_unionClosed_compl
#print axioms compl_image_hornModels
#print axioms dualHornModels_unionClosed
#print axioms greatestBelow_iff_unionClosed
#print axioms pairFamily_intersectionClosed
#print axioms pairFamily_indistinguishable
#print axioms pairFamily_least_ne
#print axioms closureIn_pairFamily
#print axioms hornQuery_monotone
#print axioms nonReachability_not_monotone
#print axioms nonReachability_not_hornQuery
#print axioms proves_mono
#print axioms proves_assuming_facts_iff
#print axioms same_closure_different_goal
#print axioms proves_congr_hornModels
#print axioms chain_proves_iff
#print axioms hornEnvelope_eq_intersectionClosure
#print axioms hornEnvelope_least
#print axioms hornEnvelope_eq_self_iff
#print axioms entails_of_hornEnvelope
#print axioms not_entails_of_subset
#print axioms exists_hornGLB_of_mem
#print axioms entails_iff_forall_hornGLB
#print axioms eitherFamily_not_meetClosed
#print axioms either_envelope
#print axioms either_lowerBound
#print axioms meetClosed_iff_inter_mem
#print axioms withEither_meetClosed_iff
#print axioms haltingFamily_meetClosed_iff
#print axioms not_computable_meetClosed
#print axioms portfolio_sound
#print axioms portfolio_agree
#print axioms envelopeAnswer_sound
#print axioms lowerBoundAnswer_sound
#print axioms envelopeAnswer_exact
#print axioms hornPortfolio_sound
#print axioms either_portfolio

end Mettapedia.GSLT.OpenEnded.PresentationLimits
