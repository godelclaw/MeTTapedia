import Mettapedia.GSLT.Core.Composition
import Mettapedia.GSLT.OpenEnded.SufficientBubbles
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis
import Mathlib.Data.Set.Finite.Basic

/-!
# Carrier bubbles of a GSLT and reachability observers

A second kind of bubble keeps the rules and cuts the language: a set of terms
`B` of a GSLT, with the equations and steps among them. When `B` is closed
under steps, it is again a GSLT (`restrictCarrier`) and its inclusion is a
structural embedding that preserves and reflects equations and steps
(`carrierEmbedding`).

An observer here is a family of reachability observations: OSLF's native
type "reaches a term satisfying `φ`" (`semanticReach`). A carrier preserves
and reflects the reachability observations of a set of seeds when every
reachability path in the full GSLT from a seed can be taken inside the
carrier (`ReachSufficient`).

* **The full observer has a least bubble: the reachable cone.** A carrier is
  sufficient exactly when it contains the cone of the seeds
  (`reachSufficient_iff`), so the cone is the least sufficient carrier
  (`isLeast_cone`). The cone is closed under steps (`cone_stepClosed`); as a
  sub-GSLT it computes the same reachability native types as the full GSLT
  (`semanticReach_cone`).
* **A single observation can have no least bubble.** In a diamond
  `a → b → d`, `a → c → d`, the single observation "`a` reaches `d`" has two
  minimal carriers, through `b` and through `c`, and no least one
  (`single_minimal`, `single_no_least`). Enlarging the observer to every
  reachability observation of `a` creates a least carrier, the whole cone
  (`full_isLeast`): least bubbles are not monotone in the observer.
* **Least computation bubbles need not be compact.** For the successor steps
  on the natural numbers, the least carrier sufficient for the reachability
  observations of `0` is all of the naturals (`succ_cone_infinite`). A finite
  proof has a finite least bubble (`RuleTables.least_bubble_finite`); an
  unbounded computation's least bubble can be infinite.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.OpenEnded.CarrierBubbles

open Set
open Mettapedia.GSLT
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.GSLT.OpenEnded.SufficientBubbles

universe u

variable (S : GSLT.{u})

/-- A carrier closed under the steps of the GSLT. -/
def StepClosed (B : Set S.Term) : Prop :=
  ∀ ⦃t t' : S.Term⦄, t ∈ B → S.Step t t' → t' ∈ B

/-- The sub-GSLT on a step-closed carrier. -/
def restrictCarrier (B : Set S.Term) (closed : StepClosed S B) : GSLT.{u} where
  Term := B
  equations :=
    ⟨fun first second => S.Equiv first.1 second.1,
      ⟨fun term => S.equations.iseqv.refl term.1,
        fun equivalent => S.equations.iseqv.symm equivalent,
        fun first second => S.equations.iseqv.trans first second⟩⟩
  rewrites := fun first second => S.Step first.1 second.1
  rewrites_resp_left := by
    intro t t' target equivalent step
    obtain ⟨next, step', equivalent'⟩ := S.rewrites_resp_left equivalent step
    exact ⟨⟨next, closed t'.2 step'⟩, step', equivalent'⟩
  rewrites_resp_right := fun step equivalent => S.rewrites_resp_right step equivalent

/-- **The inclusion of a step-closed carrier is a structural embedding.** -/
def carrierEmbedding (B : Set S.Term) (closed : StepClosed S B) :
    GSLT.Embedding (restrictCarrier S B closed) S where
  toFun := Subtype.val
  injective := Subtype.val_injective
  equiv_iff := fun _ _ => Iff.rfl
  step_iff := fun _ _ => Iff.rfl

variable {S}

theorem multiStep_val {B : Set S.Term} {closed : StepClosed S B}
    {first second : (restrictCarrier S B closed).Term}
    (path : (restrictCarrier S B closed).MultiStep first second) :
    S.MultiStep first.1 second.1 := by
  induction path with
  | refl => exact .refl _
  | step step _ ih => exact .step step ih

theorem multiStep_lift {B : Set S.Term} (closed : StepClosed S B) {t t' : S.Term}
    (path : S.MultiStep t t') (member : t ∈ B) :
    ∃ member' : t' ∈ B, (restrictCarrier S B closed).MultiStep ⟨t, member⟩ ⟨t', member'⟩ := by
  induction path with
  | refl => exact ⟨member, .refl _⟩
  | @step first middle last step _ ih =>
      obtain ⟨member', rest⟩ := ih (closed member step)
      exact ⟨member', .step (S := restrictCarrier S B closed) (u := ⟨middle, closed member step⟩)
        step rest⟩

/-- Pull an OSLF predicate back to a carrier. -/
def pullPredicate (B : Set S.Term) (closed : StepClosed S B) (predicate : EquationPredicate S) :
    EquationPredicate (restrictCarrier S B closed) :=
  ⟨fun term => predicate.1 term.1, fun _ _ equivalent => predicate.2 equivalent⟩

/-- **A step-closed carrier computes the full GSLT's reachability native
types on its own terms.** -/
theorem semanticReach_restrict {B : Set S.Term} (closed : StepClosed S B)
    (predicate : EquationPredicate S) (term : (restrictCarrier S B closed).Term) :
    (semanticReach (restrictCarrier S B closed) (pullPredicate B closed predicate)).1 term ↔
      (semanticReach S predicate).1 term.1 := by
  rw [semanticReach_spec, semanticReach_spec]
  constructor
  · rintro ⟨last, path, holds⟩
    exact ⟨last.1, multiStep_val path, holds⟩
  · rintro ⟨last, path, holds⟩
    obtain ⟨member, lifted⟩ := multiStep_lift closed path term.2
    exact ⟨⟨last, member⟩, lifted, holds⟩

/-! ## Reachability observers -/

/-- Reachability that visits only terms of a carrier. -/
inductive ReachWithin (B : Set S.Term) : S.Term → S.Term → Prop
  | refl {t : S.Term} : t ∈ B → ReachWithin B t t
  | step {t t' t'' : S.Term} : t ∈ B → S.Step t t' → ReachWithin B t' t'' → ReachWithin B t t''

theorem ReachWithin.source_mem {B : Set S.Term} {t t' : S.Term} (path : ReachWithin B t t') :
    t ∈ B := by
  cases path with
  | refl member => exact member
  | step member _ _ => exact member

theorem ReachWithin.target_mem {B : Set S.Term} {t t' : S.Term} (path : ReachWithin B t t') :
    t' ∈ B := by
  induction path with
  | refl member => exact member
  | step _ _ _ ih => exact ih

/-- Reflection is automatic: a path inside a carrier is a path of the GSLT. -/
theorem ReachWithin.multiStep {B : Set S.Term} {t t' : S.Term} (path : ReachWithin B t t') :
    S.MultiStep t t' := by
  induction path with
  | refl _ => exact .refl _
  | step _ step _ ih => exact .step step ih

/-- A carrier preserves and reflects every reachability observation of the
seeds. -/
def ReachSufficient (seeds B : Set S.Term) : Prop :=
  ∀ t ∈ seeds, ∀ t', S.MultiStep t t' ↔ ReachWithin B t t'

variable (S) in
/-- The terms reachable from the seeds. -/
def cone (seeds : Set S.Term) : Set S.Term :=
  {t' | ∃ t ∈ seeds, S.MultiStep t t'}

private theorem multiStep_append {t t' t'' : S.Term} (first : S.MultiStep t t')
    (second : S.MultiStep t' t'') : S.MultiStep t t'' := by
  induction first with
  | refl => exact second
  | step step _ ih => exact .step step (ih second)

theorem cone_stepClosed (seeds : Set S.Term) : StepClosed S (cone S seeds) := by
  rintro t t' ⟨source, member, path⟩ step
  exact ⟨source, member, multiStep_append path (.step step (.refl _))⟩

private theorem reachWithin_of_cone {seeds B : Set S.Term} (contained : cone S seeds ⊆ B)
    {t t' : S.Term} (inCone : t ∈ cone S seeds) (path : S.MultiStep t t') :
    ReachWithin B t t' := by
  induction path with
  | refl => exact .refl (contained inCone)
  | step step _ ih => exact .step (contained inCone) step (ih (cone_stepClosed seeds inCone step))

/-- **A carrier is sufficient exactly when it contains the cone.** -/
theorem reachSufficient_iff (seeds B : Set S.Term) :
    ReachSufficient seeds B ↔ cone S seeds ⊆ B := by
  constructor
  · rintro sufficient t' ⟨t, member, path⟩
    exact ((sufficient t member t').mp path).target_mem
  · intro contained t member t'
    exact ⟨fun path => reachWithin_of_cone contained ⟨t, member, .refl _⟩ path,
      fun path => path.multiStep⟩

/-- **The reachable cone is the least sufficient carrier.** -/
theorem isLeast_cone (seeds : Set S.Term) :
    IsLeast {B | ReachSufficient seeds B} (cone S seeds) :=
  ⟨(reachSufficient_iff seeds _).mpr subset_rfl,
    fun _ sufficient => (reachSufficient_iff seeds _).mp sufficient⟩

/-- The least sufficient carrier as a sub-GSLT computes the full reachability
native types on its terms. -/
theorem semanticReach_cone (seeds : Set S.Term) (predicate : EquationPredicate S)
    (term : (restrictCarrier S (cone S seeds) (cone_stepClosed seeds)).Term) :
    (semanticReach _ (pullPredicate _ (cone_stepClosed seeds) predicate)).1 term ↔
      (semanticReach S predicate).1 term.1 :=
  semanticReach_restrict (cone_stepClosed seeds) predicate term

/-! ## A single observation: two minimal carriers -/

inductive Node
  | a
  | b
  | c
  | d
  deriving DecidableEq

open Node

inductive DiamondStep : Node → Node → Prop
  | ab : DiamondStep a b
  | ac : DiamondStep a c
  | bd : DiamondStep b d
  | cd : DiamondStep c d

/-- The diamond as a GSLT. -/
def diamond : GSLT := equalityGSLT Node DiamondStep

/-- The single observation "`a` reaches `d`". -/
def SingleSufficient (B : Set Node) : Prop :=
  ReachWithin (S := diamond) B a d

theorem single_through_b : SingleSufficient {a, b, d} :=
  .step (Or.inl rfl) (show DiamondStep a b from .ab)
    (.step (Or.inr (Or.inl rfl)) (show DiamondStep b d from .bd) (.refl (Or.inr (Or.inr rfl))))

theorem single_through_c : SingleSufficient {a, c, d} :=
  .step (Or.inl rfl) (show DiamondStep a c from .ac)
    (.step (Or.inr (Or.inl rfl)) (show DiamondStep c d from .cd) (.refl (Or.inr (Or.inr rfl))))

private theorem single_middle {B : Set diamond.Term} {t t' : diamond.Term}
    (path : ReachWithin B t t') : t = a → t' = d → b ∈ B ∨ c ∈ B := by
  induction path with
  | refl _ =>
      intro source target
      exact absurd (source.symm.trans target) (show (a : Node) ≠ d by decide)
  | step _ step rest _ =>
      intro source _
      subst source
      change DiamondStep a _ at step
      cases step with
      | ab => exact Or.inl rest.source_mem
      | ac => exact Or.inr rest.source_mem

/-- Any carrier for the single observation contains `a`, `d`, and `b` or `c`. -/
theorem single_needs {B : Set Node} (sufficient : SingleSufficient B) :
    a ∈ B ∧ d ∈ B ∧ (b ∈ B ∨ c ∈ B) :=
  ⟨sufficient.source_mem, sufficient.target_mem, single_middle sufficient rfl rfl⟩

/-- **The single observation has two minimal carriers.** -/
theorem single_minimal :
    Minimal SingleSufficient {a, b, d} ∧ Minimal SingleSufficient {a, c, d} := by
  constructor
  · refine ⟨single_through_b, fun B sufficient included => ?_⟩
    obtain ⟨memberA, memberD, middle⟩ := single_needs sufficient
    have memberB : b ∈ B := by
      rcases middle with memberB | memberC
      · exact memberB
      · rcases included memberC with absurd | absurd | absurd <;> cases absurd
    rintro x (rfl | rfl | rfl)
    · exact memberA
    · exact memberB
    · exact memberD
  · refine ⟨single_through_c, fun B sufficient included => ?_⟩
    obtain ⟨memberA, memberD, middle⟩ := single_needs sufficient
    have memberC : c ∈ B := by
      rcases middle with memberB | memberC
      · rcases included memberB with absurd | absurd | absurd <;> cases absurd
      · exact memberC
    rintro x (rfl | rfl | rfl)
    · exact memberA
    · exact memberC
    · exact memberD

/-- **The single observation has no least carrier.** -/
theorem single_no_least : ¬ ∃ least, IsLeast {B | SingleSufficient B} least := by
  rintro ⟨least, sufficient, smallest⟩
  obtain ⟨_, _, middle⟩ := single_needs sufficient
  rcases middle with memberB | memberC
  · rcases smallest single_through_c memberB with absurd | absurd | absurd <;> cases absurd
  · rcases smallest single_through_b memberC with absurd | absurd | absurd <;> cases absurd

theorem diamond_cone (x : Node) : x ∈ cone diamond ({a} : Set Node) := by
  refine ⟨a, rfl, ?_⟩
  cases x with
  | a => exact .refl _
  | b => exact .step (show DiamondStep a b from .ab) (.refl _)
  | c => exact .step (show DiamondStep a c from .ac) (.refl _)
  | d => exact .step (show DiamondStep a b from .ab) (.step (show DiamondStep b d from .bd) (.refl _))

/-- **Every reachability observation of `a` together has a least carrier**,
the whole diamond. -/
theorem full_isLeast :
    IsLeast {B | ReachSufficient (S := diamond) ({a} : Set Node) B} (cone diamond ({a} : Set Node)) ∧
      ∀ x : Node, x ∈ cone diamond ({a} : Set Node) :=
  ⟨isLeast_cone _, diamond_cone⟩

/-! ## An unbounded computation has an infinite least carrier -/

/-- Successor steps on the natural numbers. -/
def succGSLT : GSLT := equalityGSLT ℕ (fun n m => m = n + 1)

theorem succ_cone (n : ℕ) : n ∈ cone succGSLT ({0} : Set ℕ) := by
  refine ⟨(0 : ℕ), rfl, ?_⟩
  induction n with
  | zero => exact .refl _
  | succ n ih =>
      exact multiStep_append (S := succGSLT) ih (.step (show n + 1 = n + 1 from rfl) (.refl _))

/-- **The least carrier for the reachability observations of `0` is
infinite.** -/
theorem succ_cone_infinite :
    IsLeast {B | ReachSufficient (S := succGSLT) ({0} : Set ℕ) B} (cone succGSLT ({0} : Set ℕ)) ∧
      Set.Infinite (cone succGSLT ({0} : Set ℕ) : Set ℕ) :=
  ⟨isLeast_cone _, (Set.infinite_univ (α := ℕ)).mono (fun n _ => succ_cone n)⟩

#print axioms carrierEmbedding
#print axioms semanticReach_restrict
#print axioms reachSufficient_iff
#print axioms isLeast_cone
#print axioms semanticReach_cone
#print axioms single_minimal
#print axioms single_no_least
#print axioms full_isLeast
#print axioms succ_cone_infinite

end Mettapedia.GSLT.OpenEnded.CarrierBubbles
