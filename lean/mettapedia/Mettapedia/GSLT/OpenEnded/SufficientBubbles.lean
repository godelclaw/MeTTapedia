import Mathlib.Data.Set.Lattice
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Minimal

/-!
# Least sufficient bubbles: when meets exist and why they fail

Fix a presentation whose generators (rules, declarations, computation rules)
form a type `G`. A *bubble* of the presentation is a sub-presentation, here a
set of generators `S : Set G`. A *sufficiency condition* says which bubbles are
good enough for a request: they must still derive a judgment, preserve the
retained computation, and preserve and reflect a family of observations.

The question is whether the sufficient bubbles have a least element, the
"weakest sufficient layer". This file answers it at the level of generators,
before any particular calculus is chosen.

* **Monotone sufficiency.** When adding generators never destroys sufficiency
  (`UpClosed`), a least sufficient bubble exists exactly when sufficiency is
  closed under meets of nonempty families (`exists_least_iff_meetClosed`).
  The only candidate is the *deletion core*: the generators each of whose
  single removal destroys sufficiency (`least_eq_core`). A least sufficient
  bubble exists exactly when that core is itself sufficient
  (`exists_least_iff_core_sufficient`). So one oracle call per generator,
  plus one, decides the question.
* **Derivation supports.** A judgment with several derivations is sufficient
  in every bubble that contains the support of one of them (`SupportedBy`).
  A least bubble exists exactly when one support is contained in every other
  (`isLeast_supportedBy_iff`). Two incomparable supports have two minimal
  bubbles and no least (`supportedBy_pair_minimal_left`,
  `no_least_of_incomparable_supports`).
* **Horn clauses and closure systems.** When sufficiency is presented by Horn
  clauses between generators (a set of premises requires one generator), the
  sufficient bubbles are closed under arbitrary intersections
  (`hornModels_sInter_mem`), and the least sufficient bubble above any seed is
  the Horn closure of the seed (`isLeast_hornClosure`). Conversely every
  intersection-closed family of bubbles is the family of models of its own
  Horn theory (`models_hornTheoryOf`). So least bubbles above every seed exist
  exactly for the Horn-definable families (`leastAbove_iff_intersectionClosed`,
  `leastAbove_iff_hornDefinable`): this is the propositional, definite form of
  the classical correspondence between Horn axiomatizability and closure under
  intersections (McKinsey 1943, Horn 1951). `ClosureSystems`
  proves that the same closure systems are presented by closure operators,
  monads on the bubble order, reflective sub-orders and prefixed points of
  monotone operators, that every monotone operator on bubbles is the one-step
  operator of a Horn theory, and that finitary Horn theories present exactly
  the algebraic closure systems. `ChaoticIteration` proves that every fair
  order of clause applications computes the same Horn closure.
* **Disjunction is the obstruction.** A clause whose conclusion is a choice
  between alternative generator sets (a geometric clause) can express every
  family of bubbles (`models_geometricTheoryOf`). Disjunction arises from
  several derivations of one judgment, from several ways to type a reduct,
  and from several paths witnessing one observation.
* **Computation preservation is not monotone.** A Horn clause with premises
  ("if this computation rule is retained, the declaration typing its reduct
  must be too") makes sufficiency non-monotone. The least sufficient bubble
  still exists (`pkgSuff_isLeast`), but sufficiency is not upward closed
  (`pkgSuff_not_upClosed`) and the deletion core is not the least bubble
  (`pkgSuff_core_ne_least`). Top-down deletion decides monotone sufficiency;
  the Horn closure computes intersection-closed sufficiency. For sufficiency
  that is neither, `DisjunctiveBubbles` gives the canonical upset of
  sufficient bubbles and `PresentationLimits` its Horn envelope.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.OpenEnded.SufficientBubbles

open Set

universe u

variable {G : Type u}

/-! ## Monotone sufficiency and meets -/

/-- Adding generators never destroys sufficiency. -/
def UpClosed (Suff : Set G → Prop) : Prop :=
  ∀ ⦃S T : Set G⦄, S ⊆ T → Suff S → Suff T

/-- Sufficiency is closed under meets of nonempty families of bubbles. -/
def MeetClosed (Suff : Set G → Prop) : Prop :=
  ∀ F : Set (Set G), F.Nonempty → (∀ S ∈ F, Suff S) → Suff (⋂₀ F)

/-- Meet-closed sufficiency with some sufficient bubble has a least sufficient
bubble: the meet of all of them. -/
theorem isLeast_sInter_of_meetClosed {Suff : Set G → Prop} (closed : MeetClosed Suff)
    (inhabited : ∃ S, Suff S) :
    IsLeast {S | Suff S} (⋂₀ {S | Suff S}) := by
  obtain ⟨S, sufficient⟩ := inhabited
  exact ⟨closed _ ⟨S, sufficient⟩ (fun _ member => member),
    fun _ member => sInter_subset_of_mem member⟩

/-- For monotone sufficiency, a least sufficient bubble forces closure under
all nonempty meets. -/
theorem meetClosed_of_isLeast {Suff : Set G → Prop} (up : UpClosed Suff) {least : Set G}
    (isLeast : IsLeast {S | Suff S} least) : MeetClosed Suff := by
  intro F _ allSufficient
  exact up (subset_sInter fun S member => isLeast.2 (allSufficient S member)) isLeast.1

/-- **Monotone sufficiency has a least bubble exactly when it is meet-closed.** -/
theorem exists_least_iff_meetClosed {Suff : Set G → Prop} (up : UpClosed Suff) :
    (∃ least, IsLeast {S | Suff S} least) ↔ (∃ S, Suff S) ∧ MeetClosed Suff := by
  constructor
  · rintro ⟨least, isLeast⟩
    exact ⟨⟨least, isLeast.1⟩, meetClosed_of_isLeast up isLeast⟩
  · rintro ⟨inhabited, closed⟩
    exact ⟨_, isLeast_sInter_of_meetClosed closed inhabited⟩

/-! ## The deletion core -/

/-- The generators whose removal alone destroys sufficiency. -/
def core (Suff : Set G → Prop) : Set G :=
  {g | ¬ Suff ({g}ᶜ)}

private theorem subset_compl_singleton {S : Set G} {g : G} (absent : g ∉ S) :
    S ⊆ {g}ᶜ := by
  intro x member same
  exact absent (same ▸ member)

/-- **The only possible least bubble is the deletion core.** -/
theorem least_eq_core {Suff : Set G → Prop} (up : UpClosed Suff) {least : Set G}
    (isLeast : IsLeast {S | Suff S} least) : least = core Suff := by
  ext g
  constructor
  · intro member sufficient
    exact (isLeast.2 sufficient member) rfl
  · intro inCore
    by_contra absent
    exact inCore (up (subset_compl_singleton absent) isLeast.1)

/-- A sufficient deletion core is the least sufficient bubble. -/
theorem isLeast_core_of_sufficient {Suff : Set G → Prop} (up : UpClosed Suff)
    (sufficient : Suff (core Suff)) : IsLeast {S | Suff S} (core Suff) := by
  refine ⟨sufficient, fun S sufficientS g inCore => ?_⟩
  by_contra absent
  exact inCore (up (subset_compl_singleton absent) sufficientS)

/-- **Deciding existence by deletion.** For monotone sufficiency, a least
sufficient bubble exists exactly when the deletion core is sufficient. -/
theorem exists_least_iff_core_sufficient {Suff : Set G → Prop} (up : UpClosed Suff) :
    (∃ least, IsLeast {S | Suff S} least) ↔ Suff (core Suff) := by
  constructor
  · rintro ⟨least, isLeast⟩
    exact least_eq_core up isLeast ▸ isLeast.1
  · intro sufficient
    exact ⟨_, isLeast_core_of_sufficient up sufficient⟩

/-! ## Sufficiency generated by derivation supports -/

/-- A bubble is sufficient when it contains one of the given supports, for
instance the rule support of one derivation of a judgment. -/
def SupportedBy (supports : Set (Set G)) (S : Set G) : Prop :=
  ∃ A ∈ supports, A ⊆ S

theorem supportedBy_upClosed (supports : Set (Set G)) :
    UpClosed (SupportedBy supports) := by
  rintro S T included ⟨A, member, contained⟩
  exact ⟨A, member, contained.trans included⟩

/-- **A least bubble exists exactly when one support lies inside every
other one,** and then it is that support. -/
theorem isLeast_supportedBy_iff {supports : Set (Set G)} {least : Set G} :
    IsLeast {S | SupportedBy supports S} least ↔
      least ∈ supports ∧ ∀ A ∈ supports, least ⊆ A := by
  constructor
  · rintro ⟨⟨A, member, contained⟩, lower⟩
    have below : least ⊆ A := lower ⟨A, member, subset_rfl⟩
    have same : least = A := subset_antisymm below contained
    exact ⟨same ▸ member, fun B memberB => lower ⟨B, memberB, subset_rfl⟩⟩
  · rintro ⟨member, smallest⟩
    refine ⟨⟨least, member, subset_rfl⟩, ?_⟩
    rintro S ⟨A, memberA, contained⟩
    exact (smallest A memberA).trans contained

/-- A judgment whose derivations all share one support has a least bubble. -/
theorem isLeast_supportedBy_singleton (A : Set G) :
    IsLeast {S | SupportedBy {A} S} A :=
  isLeast_supportedBy_iff.mpr ⟨rfl, fun _ member => member ▸ subset_rfl⟩

/-- With two incomparable supports, each support is a minimal sufficient
bubble. -/
theorem supportedBy_pair_minimal_left {A B : Set G} (notBA : ¬ B ⊆ A) :
    Minimal (SupportedBy {A, B}) A := by
  refine ⟨⟨A, Or.inl rfl, subset_rfl⟩, ?_⟩
  rintro S ⟨C, member, contained⟩ included
  rcases member with rfl | rfl
  · exact contained
  · exact absurd (contained.trans included) notBA

theorem supportedBy_pair_minimal_right {A B : Set G} (notAB : ¬ A ⊆ B) :
    Minimal (SupportedBy {A, B}) B := by
  have swapped : ({B, A} : Set (Set G)) = {A, B} := Set.pair_comm B A
  have minimal := supportedBy_pair_minimal_left (A := B) (B := A) notAB
  rwa [swapped] at minimal

/-- **Two incomparable supports: no least sufficient bubble.** -/
theorem no_least_of_incomparable_supports {A B : Set G} (notAB : ¬ A ⊆ B)
    (notBA : ¬ B ⊆ A) : ¬ ∃ least, IsLeast {S | SupportedBy {A, B} S} least := by
  rintro ⟨least, isLeast⟩
  obtain ⟨member, smallest⟩ := isLeast_supportedBy_iff.mp isLeast
  rcases member with rfl | rfl
  · exact notAB (smallest B (Or.inr rfl))
  · exact notBA (smallest _ (Or.inl rfl))

/-- The meet of the two incomparable minimal bubbles is not sufficient. -/
theorem inter_not_supportedBy_of_incomparable {A B : Set G} (notAB : ¬ A ⊆ B)
    (notBA : ¬ B ⊆ A) : ¬ SupportedBy {A, B} (A ∩ B) := by
  rintro ⟨C, member, contained⟩
  rcases member with rfl | rfl
  · exact notAB (contained.trans inter_subset_right)
  · exact notBA (contained.trans inter_subset_left)

/-! ## Horn sufficiency: closure systems presented by Horn clauses -/

/-- A definite Horn clause between generators: when all premises are retained,
the conclusion must be retained. A clause without premises is a fact. With
finite premise sets these are the definite Horn clauses `p₁ ∧ … ∧ pₙ → c` of
propositional logic; finitary Horn theories present exactly the algebraic
closure systems (`ClosureSystems.hornModels_finitary_iff`). With arbitrary
premise sets they are the infinitary Horn clauses, the rules of an inductive
definition, and they present every monotone operator on bubbles
(`ClosureSystems.oneStep_rulesOf`). -/
structure HornClause (G : Type u) where
  premises : Set G
  conclusion : G

def HornClause.Holds (clause : HornClause G) (S : Set G) : Prop :=
  clause.premises ⊆ S → clause.conclusion ∈ S

/-- The models of a Horn theory: the bubbles closed under every clause. -/
def hornModels (theory : Set (HornClause G)) : Set (Set G) :=
  {S | ∀ clause ∈ theory, clause.Holds S}

/-- **The models of a Horn theory are closed under arbitrary intersections**,
including the empty one. -/
theorem hornModels_sInter_mem (theory : Set (HornClause G)) (F : Set (Set G))
    (models : F ⊆ hornModels theory) : ⋂₀ F ∈ hornModels theory := by
  intro clause member premisesIn S memberS
  exact models memberS clause member (premisesIn.trans (sInter_subset_of_mem memberS))

/-- Derivability from seeds by Horn clauses (forward chaining): a generator
is derivable when it is a seed or the conclusion of a clause whose premises
are all derivable. -/
inductive HornDerivable (theory : Set (HornClause G)) (seeds : Set G) : G → Prop
  | seed {g : G} : g ∈ seeds → HornDerivable theory seeds g
  | rule (clause : HornClause G) : clause ∈ theory →
      (∀ p ∈ clause.premises, HornDerivable theory seeds p) →
      HornDerivable theory seeds clause.conclusion

/-- The Horn closure of the seeds: everything derivable from them. -/
def hornClosure (theory : Set (HornClause G)) (seeds : Set G) : Set G :=
  {g | HornDerivable theory seeds g}

/-- **The least model of a Horn theory above a seed is the Horn closure of the
seed** (van Emden and Kowalski 1976, for finitely many finitary clauses). -/
theorem isLeast_hornClosure (theory : Set (HornClause G)) (seeds : Set G) :
    IsLeast {S | S ∈ hornModels theory ∧ seeds ⊆ S} (hornClosure theory seeds) := by
  refine ⟨⟨fun clause member premisesIn => HornDerivable.rule clause member premisesIn,
    fun _ member => HornDerivable.seed member⟩, ?_⟩
  rintro S ⟨models, seedsIn⟩ g derivable
  induction derivable with
  | seed member => exact seedsIn member
  | rule clause member _ ih => exact models clause member ih

/-! ## Intersection-closed families are exactly the Horn-definable ones -/

/-- The meet of the members of a family above a seed; the least member above
the seed when the family is intersection-closed. -/
def closureIn (F : Set (Set G)) (A : Set G) : Set G :=
  ⋂₀ {S | S ∈ F ∧ A ⊆ S}

/-- The Horn theory of a family of bubbles: the clauses `A → g` with `g` in
every member of the family that contains `A`, which are exactly the clauses
true in every member (`mem_hornTheoryOf_iff`). -/
def hornTheoryOf (F : Set (Set G)) : Set (HornClause G) :=
  {clause | clause.conclusion ∈ closureIn F clause.premises}

/-- **The Horn theory of a family consists of the clauses true in all of its
members.** -/
theorem mem_hornTheoryOf_iff {F : Set (Set G)} {clause : HornClause G} :
    clause ∈ hornTheoryOf F ↔ ∀ S ∈ F, clause.Holds S := by
  constructor
  · intro valid S member premisesIn
    exact valid S ⟨member, premisesIn⟩
  · intro valid S ⟨member, premisesIn⟩
    exact valid S member premisesIn

/-- Every member of a family is a model of the family's Horn theory. -/
theorem subset_hornModels_hornTheoryOf (F : Set (Set G)) : F ⊆ hornModels (hornTheoryOf F) :=
  fun S member _ valid => mem_hornTheoryOf_iff.mp valid S member

def IntersectionClosed (F : Set (Set G)) : Prop :=
  ∀ F' ⊆ F, ⋂₀ F' ∈ F

/-- **Every intersection-closed family of bubbles is the family of models of
its Horn theory.** -/
theorem models_hornTheoryOf {F : Set (Set G)} (closed : IntersectionClosed F) :
    hornModels (hornTheoryOf F) = F := by
  ext S
  constructor
  · intro models
    have inside : closureIn F S ⊆ S := fun g member =>
      models ⟨S, g⟩ member subset_rfl
    have outside : S ⊆ closureIn F S := subset_sInter fun _ member => member.2
    have same : closureIn F S = S := subset_antisymm inside outside
    exact same ▸ closed _ (fun _ member => member.1)
  · intro memberF clause member premisesIn
    exact member S ⟨memberF, premisesIn⟩

def LeastAboveEverySeed (F : Set (Set G)) : Prop :=
  ∀ A : Set G, ∃ least, IsLeast {S | S ∈ F ∧ A ⊆ S} least

/-- **Least bubbles above every seed exist exactly for intersection-closed
families.** -/
theorem leastAbove_iff_intersectionClosed (F : Set (Set G)) :
    LeastAboveEverySeed F ↔ IntersectionClosed F := by
  constructor
  · intro leastAbove F' included
    obtain ⟨least, ⟨memberF, seedIn⟩, lower⟩ := leastAbove (⋂₀ F')
    have inside : least ⊆ ⋂₀ F' :=
      subset_sInter fun S member => lower ⟨included member, sInter_subset_of_mem member⟩
    exact (subset_antisymm inside seedIn) ▸ memberF
  · intro closed A
    refine ⟨closureIn F A, ⟨closed _ (fun _ member => member.1),
      subset_sInter fun _ member => member.2⟩, fun _ member => sInter_subset_of_mem member⟩

/-- **Least bubbles above every seed exist exactly when sufficiency is
Horn-definable.** -/
theorem leastAbove_iff_hornDefinable (F : Set (Set G)) :
    LeastAboveEverySeed F ↔ ∃ theory : Set (HornClause G), hornModels theory = F := by
  rw [leastAbove_iff_intersectionClosed]
  constructor
  · intro closed
    exact ⟨hornTheoryOf F, models_hornTheoryOf closed⟩
  · rintro ⟨theory, rfl⟩ F' included
    exact hornModels_sInter_mem theory F' included

/-! ## Geometric clauses: disjunction makes every family expressible -/

/-- A geometric requirement: when all premises are retained, one of the
alternative generator sets must be retained in full. -/
structure GeometricClause (G : Type u) where
  premises : Set G
  alternatives : Set (Set G)

def GeometricClause.Holds (clause : GeometricClause G) (S : Set G) : Prop :=
  clause.premises ⊆ S → ∃ A ∈ clause.alternatives, A ⊆ S

def geometricModels (theory : Set (GeometricClause G)) : Set (Set G) :=
  {S | ∀ clause ∈ theory, clause.Holds S}

/-- A clause excluding exactly one bubble. -/
def excludeClause (S : Set G) : GeometricClause G :=
  ⟨S, {A | ∃ g, g ∉ S ∧ A = {g}}⟩

theorem excludeClause_holds_iff (S X : Set G) :
    (excludeClause S).Holds X ↔ X ≠ S := by
  constructor
  · intro holds same
    subst same
    obtain ⟨A, ⟨g, absent, rfl⟩, contained⟩ := holds subset_rfl
    exact absent (contained rfl)
  · intro different premisesIn
    have notInside : ¬ X ⊆ S := fun inside => different (subset_antisymm inside premisesIn)
    obtain ⟨g, member, absent⟩ := not_subset.mp notInside
    exact ⟨{g}, ⟨g, absent, rfl⟩, singleton_subset_iff.mpr member⟩

def geometricTheoryOf (F : Set (Set G)) : Set (GeometricClause G) :=
  {clause | ∃ S, S ∉ F ∧ clause = excludeClause S}

/-- **Every family of bubbles is the model set of a geometric theory.** -/
theorem models_geometricTheoryOf (F : Set (Set G)) :
    geometricModels (geometricTheoryOf F) = F := by
  ext X
  constructor
  · intro models
    by_contra absent
    exact (excludeClause_holds_iff X X).mp (models _ ⟨X, absent, rfl⟩) rfl
  · rintro memberF clause ⟨S, absent, rfl⟩
    exact (excludeClause_holds_iff S X).mpr fun same => absent (same ▸ memberF)

/-- Clauses without premises define monotone sufficiency. -/
theorem geometricModels_upClosed_of_no_premises (theory : Set (GeometricClause G))
    (noPremises : ∀ clause ∈ theory, clause.premises = ∅) :
    UpClosed (· ∈ geometricModels theory) := by
  intro S T included models clause member _
  obtain ⟨A, alternative, contained⟩ :=
    models clause member (by rw [noPremises clause member]; exact empty_subset S)
  exact ⟨A, alternative, contained.trans included⟩

/-! ## Cost against inclusion

"Weakest" should mean cheapest under a declared cost model. When a least
sufficient bubble exists, every inclusion-monotone cost (rule-table size,
load time of the retained rules) agrees with it (`isLeast_minimizes_monotone_cost`),
and a strictly monotone cost only ever selects inclusion-minimal bubbles
(`minimal_of_cost_minimal`). Costs measured on certificates are not monotone:
a larger bubble can check the same judgment with a smaller certificate.
That disagreement is exhibited on a validated certificate-GSLT definition in
`CertificateBubbles.cost_inclusion_disagree`. -/

/-- A least sufficient bubble minimizes every inclusion-monotone cost. -/
theorem isLeast_minimizes_monotone_cost {α : Type*} [Preorder α] {Suff : Set G → Prop}
    {least : Set G} (isLeast : IsLeast {S | Suff S} least) {cost : Set G → α}
    (monotone : Monotone cost) {S : Set G} (sufficient : Suff S) : cost least ≤ cost S :=
  monotone (isLeast.2 sufficient)

/-- Under a strictly monotone cost, a cheapest sufficient bubble is minimal. -/
theorem minimal_of_cost_minimal {α : Type*} [PartialOrder α] {Suff : Set G → Prop}
    {cost : Set G → α} (strict : StrictMono cost) {S : Set G} (sufficient : Suff S)
    (cheapest : ∀ T, Suff T → cost S ≤ cost T) : Minimal Suff S := by
  refine ⟨sufficient, fun T sufficientT included => ?_⟩
  by_contra notBack
  have smaller : T < S := lt_of_le_not_ge included notBack
  exact lt_irrefl _ (lt_of_lt_of_le (strict smaller) (cheapest T sufficientT))

/-! ## A non-monotone Horn condition: retained computation needs the
reduct's declaration

Three generators: the declaration of a constant, the computation rule that
unfolds it, and the declaration of the constant it unfolds to. The judgment
needs the first declaration; preserving the retained computation needs the
second declaration whenever the computation rule is retained. -/

inductive PkgGen
  | sourceDecl
  | unfold
  | reductDecl
  deriving DecidableEq

open PkgGen

/-- The judgment holds, and every retained computation step stays typed. -/
def pkgSuff (S : Set PkgGen) : Prop :=
  sourceDecl ∈ S ∧ (unfold ∈ S → reductDecl ∈ S)

/-- The same condition as a Horn theory: one fact and one clause with a
premise. -/
def pkgTheory : Set (HornClause PkgGen) :=
  {⟨∅, sourceDecl⟩, ⟨{unfold}, reductDecl⟩}

theorem pkgSuff_iff_mem_hornModels (S : Set PkgGen) : pkgSuff S ↔ S ∈ hornModels pkgTheory := by
  constructor
  · rintro ⟨source, preserve⟩ clause member premisesIn
    rcases member with rfl | rfl
    · exact source
    · exact preserve (premisesIn rfl)
  · intro closed
    refine ⟨closed ⟨∅, sourceDecl⟩ (Or.inl rfl) (empty_subset S), fun retained => ?_⟩
    exact closed ⟨{unfold}, reductDecl⟩ (Or.inr rfl) (singleton_subset_iff.mpr retained)

theorem pkgSuff_isLeast : IsLeast {S | pkgSuff S} {sourceDecl} := by
  refine ⟨⟨rfl, fun retained => by cases retained⟩, ?_⟩
  rintro S ⟨source, _⟩ g member
  rw [mem_singleton_iff] at member
  exact member ▸ source

/-- Retaining the computation rule alone breaks preservation, although the
smaller bubble was sufficient: sufficiency is not monotone. -/
theorem pkgSuff_not_upClosed : ¬ UpClosed pkgSuff := by
  intro up
  have bigger : pkgSuff {sourceDecl, unfold} :=
    up (singleton_subset_iff.mpr (Or.inl rfl)) pkgSuff_isLeast.1
  obtain ⟨_, preserve⟩ := bigger
  rcases preserve (Or.inr rfl) with absurd | absurd <;> cases absurd

theorem pkgSuff_core : core pkgSuff = {sourceDecl, reductDecl} := by
  ext g
  cases g with
  | sourceDecl =>
      simp only [core, mem_ofPred_eq, pkgSuff, mem_compl_iff, mem_singleton_iff,
        not_true_eq_false, false_and, not_false_eq_true, mem_insert_iff, true_or]
  | unfold =>
      simp only [core, mem_ofPred_eq, pkgSuff, mem_compl_iff, mem_singleton_iff,
        mem_insert_iff]
      decide
  | reductDecl =>
      simp only [core, mem_ofPred_eq, pkgSuff, mem_compl_iff, mem_singleton_iff,
        mem_insert_iff]
      decide

/-- **Deletion finds the wrong bubble for non-monotone sufficiency.** -/
theorem pkgSuff_core_ne_least : core pkgSuff ≠ {sourceDecl} := by
  rw [pkgSuff_core]
  intro same
  have member : reductDecl ∈ ({sourceDecl} : Set PkgGen) := same ▸ Or.inr rfl
  cases member

#print axioms exists_least_iff_meetClosed
#print axioms least_eq_core
#print axioms exists_least_iff_core_sufficient
#print axioms isLeast_supportedBy_iff
#print axioms no_least_of_incomparable_supports
#print axioms inter_not_supportedBy_of_incomparable
#print axioms isLeast_hornClosure
#print axioms mem_hornTheoryOf_iff
#print axioms subset_hornModels_hornTheoryOf
#print axioms models_hornTheoryOf
#print axioms leastAbove_iff_intersectionClosed
#print axioms leastAbove_iff_hornDefinable
#print axioms models_geometricTheoryOf
#print axioms isLeast_minimizes_monotone_cost
#print axioms minimal_of_cost_minimal
#print axioms pkgSuff_isLeast
#print axioms pkgSuff_not_upClosed
#print axioms pkgSuff_core_ne_least

end Mettapedia.GSLT.OpenEnded.SufficientBubbles
