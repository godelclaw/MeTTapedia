import Mettapedia.GSLT.OpenEnded.SufficientBubbles
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis
import Mathlib.Logic.Relation

/-!
# Computation preservation and least sufficient bubbles

A bubble of a typed rewriting package keeps some declarations and some
computation rules. A request asks the bubble to

* replay a retained proof (here: the declaration typing the request's subject),
* exhibit one observation, the OSLF native type "steps to this target" of the
  package's own GSLT (`observes`), and
* preserve its retained computation: a retained step from a typed term
  reaches a typed term (`Preserves`).

The package has three constants, `top → mid → low`, a declaration for each,
and the two unfolding rules. The source package satisfies every request
(`source_sufficient`): any failure is introduced by restriction.

**Syntax-directed typing** (a constant is typed by its own declaration). The
preservation obligations are Horn clauses ("unfolding `top` while `top` is
declared needs `mid` declared"), so the sufficient bubbles are the models of a
Horn theory (`syntactic_suff_iff_mem_hornModels`) and a least sufficient bubble
exists: the repair `{decl top, unfold top, decl mid}` (`syntactic_isLeast`),
which is the Horn closure of the empty seed (`repair_eq_hornClosure`). Without the observation, sufficiency is not monotone
and not even convex (`syntactic_not_convex`): keeping the unfolding without
the reduct's declaration loses preservation, adding the declaration repairs
it.

**Typing by evaluation** (a term is typed when retained computation takes it
to a declared constant). The reduct `mid` can be typed in two ways: by its own
declaration, or by retaining its unfolding together with the declaration of
`low`. There are two minimal repairs (`evaluation_repairs_minimal`), and their
meet replays the proof and exhibits the observation while losing
preservation (`evaluation_meet_loses_preservation`). No least sufficient
bubble exists (`evaluation_no_least`).

This is the shape of the restriction-preservation example in the formation-
sensitive Π-Σ-Id development: a smaller package replays the source judgment
and supports the conversion observation, yet loses preservation, and the
repair adds the reduct's declaration. Constant typing there is syntax-directed,
so its repair is the least sufficient bubble for that request; a discipline
that also types terms through computation admits incomparable repairs.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.OpenEnded.ComputationBubbles

open Set
open Mettapedia.GSLT
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.GSLT.OpenEnded.SufficientBubbles

/-- Three constants of the package. -/
inductive Const
  | top
  | mid
  | low
  deriving DecidableEq

/-- Generators: one declaration per constant and two unfolding rules. -/
inductive Gen
  | decl (c : Const)
  | unfoldTop
  | unfoldMid
  deriving DecidableEq

open Const Gen

/-- The step each unfolding rule licenses. -/
inductive RuleStep : Gen → Const → Const → Prop
  | top : RuleStep unfoldTop top mid
  | mid : RuleStep unfoldMid mid low

/-- The retained computation of a bubble. -/
def PkgStep (S : Set Gen) (a b : Const) : Prop :=
  ∃ g ∈ S, RuleStep g a b

theorem pkgStep_iff (S : Set Gen) (a b : Const) :
    PkgStep S a b ↔ (a = top ∧ b = mid ∧ unfoldTop ∈ S) ∨ (a = mid ∧ b = low ∧ unfoldMid ∈ S) := by
  constructor
  · rintro ⟨g, member, step⟩
    cases step with
    | top => exact Or.inl ⟨rfl, rfl, member⟩
    | mid => exact Or.inr ⟨rfl, rfl, member⟩
  · rintro (⟨rfl, rfl, member⟩ | ⟨rfl, rfl, member⟩)
    · exact ⟨_, member, .top⟩
    · exact ⟨_, member, .mid⟩

/-- The GSLT of a bubble: constants, syntactic equality, retained steps. -/
def pkgGSLT (S : Set Gen) : GSLT := equalityGSLT Const (PkgStep S)

/-- The observation of the request: `top` steps to `mid`, as an OSLF native type. -/
def observes (S : Set Gen) : Prop :=
  (gsltOSLF (pkgGSLT S)).satisfies (S := ()) top (exactTargetNativeType (pkgGSLT S) mid).pred

theorem observes_iff (S : Set Gen) : observes S ↔ unfoldTop ∈ S := by
  unfold observes
  refine (satisfies_exactTargetNativeType_iff_step (pkgGSLT S) top mid).trans ?_
  change PkgStep S top mid ↔ _
  rw [pkgStep_iff]
  constructor
  · rintro (⟨_, _, member⟩ | ⟨absurd, _, _⟩)
    · exact member
    · cases absurd
  · intro member
    exact Or.inl ⟨rfl, rfl, member⟩

/-- The positive observation is monotone: a bubble's observation is an
observation of every larger bubble, in particular of the source. -/
theorem observes_mono {S T : Set Gen} (included : S ⊆ T) (observed : observes S) : observes T :=
  (observes_iff T).mpr (included ((observes_iff S).mp observed))

/-- Computation preservation for a typing discipline. -/
def Preserves (Typed : Set Gen → Const → Prop) (S : Set Gen) : Prop :=
  ∀ a b, Typed S a → PkgStep S a b → Typed S b

/-- A request: replay the retained proof, exhibit the observation, preserve
the retained computation. -/
def Suff (Typed : Set Gen → Const → Prop) (S : Set Gen) : Prop :=
  decl top ∈ S ∧ observes S ∧ Preserves Typed S

/-! ## Syntax-directed typing -/

/-- A constant is typed by its own declaration. -/
def TypedSyn (S : Set Gen) (c : Const) : Prop := decl c ∈ S

theorem preservesSyn_iff (S : Set Gen) :
    Preserves TypedSyn S ↔
      (unfoldTop ∈ S → decl top ∈ S → decl mid ∈ S) ∧
        (unfoldMid ∈ S → decl mid ∈ S → decl low ∈ S) := by
  constructor
  · intro preserves
    exact ⟨fun unfold declared => preserves top mid declared ⟨_, unfold, .top⟩,
      fun unfold declared => preserves mid low declared ⟨_, unfold, .mid⟩⟩
  · rintro ⟨first, second⟩ a b typed step
    rcases (pkgStep_iff S a b).mp step with ⟨rfl, rfl, unfold⟩ | ⟨rfl, rfl, unfold⟩
    · exact first unfold typed
    · exact second unfold typed

/-- The syntax-directed request as a Horn theory. -/
def synTheory : Set (HornClause Gen) :=
  {⟨∅, decl top⟩, ⟨∅, unfoldTop⟩, ⟨{unfoldTop, decl top}, decl mid⟩,
    ⟨{unfoldMid, decl mid}, decl low⟩}

private theorem pair_subset_iff {x y : Gen} {S : Set Gen} : ({x, y} : Set Gen) ⊆ S ↔ x ∈ S ∧ y ∈ S :=
  insert_subset_iff.trans (and_congr Iff.rfl singleton_subset_iff)

/-- **Syntax-directed sufficiency is Horn-definable.** -/
theorem syntactic_suff_iff_mem_hornModels (S : Set Gen) : Suff TypedSyn S ↔ S ∈ hornModels synTheory := by
  rw [Suff, observes_iff, preservesSyn_iff]
  constructor
  · rintro ⟨declared, unfold, first, second⟩ clause member premisesIn
    rcases member with rfl | rfl | rfl | rfl
    · exact declared
    · exact unfold
    · obtain ⟨u, d⟩ := pair_subset_iff.mp premisesIn
      exact first u d
    · obtain ⟨u, d⟩ := pair_subset_iff.mp premisesIn
      exact second u d
  · intro closed
    have declared := closed ⟨∅, decl top⟩ (Or.inl rfl) (empty_subset S)
    have unfold := closed ⟨∅, unfoldTop⟩ (Or.inr (Or.inl rfl)) (empty_subset S)
    refine ⟨declared, unfold, fun u d => ?_, fun u d => ?_⟩
    · exact closed ⟨{unfoldTop, decl top}, decl mid⟩ (Or.inr (Or.inr (Or.inl rfl)))
        (pair_subset_iff.mpr ⟨u, d⟩)
    · exact closed ⟨{unfoldMid, decl mid}, decl low⟩ (Or.inr (Or.inr (Or.inr rfl)))
        (pair_subset_iff.mpr ⟨u, d⟩)

/-- The repair: the Horn closure of the empty seed. -/
def repair : Set Gen := {decl top, unfoldTop, decl mid}

/-- **Syntax-directed typing: the repair is the least sufficient bubble.** -/
theorem syntactic_isLeast : IsLeast {S | Suff TypedSyn S} repair := by
  constructor
  · refine ⟨Or.inl rfl, (observes_iff _).mpr (Or.inr (Or.inl rfl)),
      (preservesSyn_iff _).mpr ⟨fun _ _ => Or.inr (Or.inr rfl), fun absurd _ => ?_⟩⟩
    rcases absurd with absurd | absurd | absurd <;> cases absurd
  · rintro S ⟨declared, observed, preserves⟩ g member
    have unfold := (observes_iff S).mp observed
    have reduct := ((preservesSyn_iff S).mp preserves).1 unfold declared
    rcases member with rfl | rfl | rfl
    · exact declared
    · exact unfold
    · exact reduct

/-- **The repair is the Horn closure of the empty seed.** -/
theorem repair_eq_hornClosure : repair = hornClosure synTheory ∅ := by
  have same : {S | Suff TypedSyn S} = {S | S ∈ hornModels synTheory ∧ ∅ ⊆ S} := by
    ext S
    exact (syntactic_suff_iff_mem_hornModels S).trans ⟨fun h => ⟨h, empty_subset S⟩, fun h => h.1⟩
  have least := syntactic_isLeast
  rw [same] at least
  exact least.unique (isLeast_hornClosure synTheory ∅)

/-- Least bubbles exist above every seed for the syntax-directed request. -/
theorem syntactic_leastAbove : LeastAboveEverySeed {S | Suff TypedSyn S} := by
  rw [leastAbove_iff_hornDefinable]
  exact ⟨synTheory, by ext S; exact (syntactic_suff_iff_mem_hornModels S).symm⟩

/-- Replay and preservation without the observation. -/
def SuffNoObservation (S : Set Gen) : Prop :=
  decl top ∈ S ∧ Preserves TypedSyn S

/-- **Sufficiency is not convex**: a bubble, a larger one, and a larger one
still, which are sufficient, insufficient and sufficient. -/
theorem syntactic_not_convex :
    SuffNoObservation {decl top} ∧
      ¬ SuffNoObservation {decl top, unfoldTop} ∧
      SuffNoObservation {decl top, unfoldTop, decl mid} := by
  refine ⟨⟨rfl, (preservesSyn_iff _).mpr ⟨fun absurd _ => ?_, fun absurd _ => ?_⟩⟩, ?_,
    ⟨Or.inl rfl, (preservesSyn_iff _).mpr ⟨fun _ _ => Or.inr (Or.inr rfl), fun absurd _ => ?_⟩⟩⟩
  · cases absurd
  · cases absurd
  · rintro ⟨_, preserves⟩
    have reduct := ((preservesSyn_iff _).mp preserves).1 (Or.inr rfl) (Or.inl rfl)
    rcases reduct with absurd | absurd <;> cases absurd
  · rcases absurd with absurd | absurd | absurd <;> cases absurd

/-! ## Typing by evaluation -/

/-- A term is typed when retained computation takes it to a declared constant. -/
def TypedEv (S : Set Gen) (c : Const) : Prop :=
  ∃ d, Relation.ReflTransGen (PkgStep S) c d ∧ decl d ∈ S

theorem typedEv_iff_step (S : Set Gen) (c : Const) :
    TypedEv S c ↔ decl c ∈ S ∨ ∃ d, PkgStep S c d ∧ TypedEv S d := by
  constructor
  · rintro ⟨d, path, declared⟩
    rcases Relation.ReflTransGen.cases_head_iff.mp path with same | ⟨next, step, rest⟩
    · exact Or.inl (same ▸ declared)
    · exact Or.inr ⟨next, step, d, rest, declared⟩
  · rintro (declared | ⟨next, step, d, rest, declared⟩)
    · exact ⟨c, .refl, declared⟩
    · exact ⟨d, Relation.ReflTransGen.head step rest, declared⟩

theorem typedEv_low (S : Set Gen) : TypedEv S low ↔ decl low ∈ S := by
  rw [typedEv_iff_step]
  constructor
  · rintro (declared | ⟨d, step, _⟩)
    · exact declared
    · rcases (pkgStep_iff S low d).mp step with ⟨absurd, _⟩ | ⟨absurd, _⟩ <;> cases absurd
  · exact Or.inl

theorem typedEv_mid (S : Set Gen) :
    TypedEv S mid ↔ decl mid ∈ S ∨ (unfoldMid ∈ S ∧ decl low ∈ S) := by
  rw [typedEv_iff_step]
  constructor
  · rintro (declared | ⟨d, step, typed⟩)
    · exact Or.inl declared
    · rcases (pkgStep_iff S mid d).mp step with ⟨absurd, _⟩ | ⟨_, rfl, unfold⟩
      · cases absurd
      · exact Or.inr ⟨unfold, (typedEv_low S).mp typed⟩
  · rintro (declared | ⟨unfold, declared⟩)
    · exact Or.inl declared
    · exact Or.inr ⟨low, ⟨_, unfold, .mid⟩, (typedEv_low S).mpr declared⟩

theorem preservesEv_iff (S : Set Gen) :
    Preserves TypedEv S ↔
      (unfoldTop ∈ S → TypedEv S top → TypedEv S mid) ∧
        (unfoldMid ∈ S → TypedEv S mid → TypedEv S low) := by
  constructor
  · intro preserves
    exact ⟨fun unfold typed => preserves top mid typed ⟨_, unfold, .top⟩,
      fun unfold typed => preserves mid low typed ⟨_, unfold, .mid⟩⟩
  · rintro ⟨first, second⟩ a b typed step
    rcases (pkgStep_iff S a b).mp step with ⟨rfl, rfl, unfold⟩ | ⟨rfl, rfl, unfold⟩
    · exact first unfold typed
    · exact second unfold typed

/-- An evaluation-discipline request forces the reduct `mid` to be typed. -/
theorem suffEv_iff (S : Set Gen) :
    Suff TypedEv S ↔ decl top ∈ S ∧ unfoldTop ∈ S ∧
      (decl mid ∈ S ∨ (unfoldMid ∈ S ∧ decl low ∈ S)) ∧
      (unfoldMid ∈ S → decl mid ∈ S → decl low ∈ S) := by
  rw [Suff, observes_iff, preservesEv_iff, typedEv_mid, typedEv_low]
  constructor
  · rintro ⟨declared, unfold, first, second⟩
    have topTyped : TypedEv S top := ⟨top, .refl, declared⟩
    have midTyped := first unfold topTyped
    exact ⟨declared, unfold, midTyped, fun u d => second u (Or.inl d)⟩
  · rintro ⟨declared, unfold, midTyped, lowNeeded⟩
    refine ⟨declared, unfold, fun _ _ => ?_, fun u typed => ?_⟩
    · exact midTyped
    · rcases typed with d | ⟨_, low⟩
      · exact lowNeeded u d
      · exact low

/-- The repair by declaring the reduct. -/
def declareRepair : Set Gen := {decl top, unfoldTop, decl mid}

/-- The repair by computing the reduct further. -/
def computeRepair : Set Gen := {decl top, unfoldTop, unfoldMid, decl low}

theorem declareRepair_sufficient : Suff TypedEv declareRepair := by
  rw [suffEv_iff]
  refine ⟨Or.inl rfl, Or.inr (Or.inl rfl), Or.inl (Or.inr (Or.inr rfl)), fun absurd _ => ?_⟩
  rcases absurd with absurd | absurd | absurd <;> cases absurd

theorem computeRepair_sufficient : Suff TypedEv computeRepair := by
  rw [suffEv_iff]
  exact ⟨Or.inl rfl, Or.inr (Or.inl rfl), Or.inr ⟨Or.inr (Or.inr (Or.inl rfl)),
    Or.inr (Or.inr (Or.inr rfl))⟩, fun _ _ => Or.inr (Or.inr (Or.inr rfl))⟩

/-- **Both repairs are minimal.** -/
theorem evaluation_repairs_minimal :
    Minimal (Suff TypedEv) declareRepair ∧ Minimal (Suff TypedEv) computeRepair := by
  constructor
  · refine ⟨declareRepair_sufficient, fun S sufficient included => ?_⟩
    obtain ⟨declared, unfold, midTyped, _⟩ := (suffEv_iff S).mp sufficient
    have reduct : decl mid ∈ S := by
      rcases midTyped with d | ⟨u, _⟩
      · exact d
      · rcases included u with absurd | absurd | absurd <;> cases absurd
    rintro g (rfl | rfl | rfl)
    · exact declared
    · exact unfold
    · exact reduct
  · refine ⟨computeRepair_sufficient, fun S sufficient included => ?_⟩
    obtain ⟨declared, unfold, midTyped, _⟩ := (suffEv_iff S).mp sufficient
    have further : unfoldMid ∈ S ∧ decl low ∈ S := by
      rcases midTyped with d | further
      · rcases included d with absurd | absurd | absurd | absurd <;> cases absurd
      · exact further
    rintro g (rfl | rfl | rfl | rfl)
    · exact declared
    · exact unfold
    · exact further.1
    · exact further.2

/-- **The meet of the two repairs replays the proof and exhibits the
observation, yet loses preservation.** -/
theorem evaluation_meet_loses_preservation :
    decl top ∈ declareRepair ∩ computeRepair ∧ observes (declareRepair ∩ computeRepair) ∧
      ¬ Preserves TypedEv (declareRepair ∩ computeRepair) := by
  refine ⟨⟨Or.inl rfl, Or.inl rfl⟩, (observes_iff _).mpr ⟨Or.inr (Or.inl rfl), Or.inr (Or.inl rfl)⟩,
    fun preserves => ?_⟩
  have midTyped := ((preservesEv_iff _).mp preserves).1 ⟨Or.inr (Or.inl rfl), Or.inr (Or.inl rfl)⟩
    ⟨top, .refl, ⟨Or.inl rfl, Or.inl rfl⟩⟩
  rcases (typedEv_mid _).mp midTyped with ⟨_, absurd⟩ | ⟨⟨absurd, _⟩, _⟩
  · rcases absurd with absurd | absurd | absurd | absurd <;> cases absurd
  · rcases absurd with absurd | absurd | absurd <;> cases absurd

/-- **Typing by evaluation: no least sufficient bubble.** -/
theorem evaluation_no_least : ¬ ∃ least, IsLeast {S | Suff TypedEv S} least := by
  rintro ⟨least, sufficient, smallest⟩
  have inDeclare : least ⊆ declareRepair := smallest declareRepair_sufficient
  have inCompute : least ⊆ computeRepair := smallest computeRepair_sufficient
  obtain ⟨_, _, midTyped, _⟩ := (suffEv_iff least).mp sufficient
  rcases midTyped with d | ⟨u, _⟩
  · rcases inCompute d with absurd | absurd | absurd | absurd <;> cases absurd
  · rcases inDeclare u with absurd | absurd | absurd <;> cases absurd

/-- The evaluation-discipline family is not intersection-closed, hence not
Horn-definable. -/
theorem evaluation_not_hornDefinable :
    ¬ ∃ theory : Set (HornClause Gen), hornModels theory = {S | Suff TypedEv S} := by
  intro definable
  have leastAbove := (leastAbove_iff_hornDefinable {S | Suff TypedEv S}).mpr definable
  obtain ⟨least, ⟨sufficient, _⟩, smallest⟩ := leastAbove ∅
  exact evaluation_no_least ⟨least, sufficient,
    fun S member => smallest ⟨member, empty_subset S⟩⟩

/-- Adding a computation rule to a sufficient bubble can lose preservation
under either discipline. -/
theorem evaluation_join_not_monotone :
    Suff TypedEv declareRepair ∧ ¬ Suff TypedEv (insert unfoldMid declareRepair) := by
  refine ⟨declareRepair_sufficient, fun sufficient => ?_⟩
  obtain ⟨_, _, _, lowNeeded⟩ := (suffEv_iff _).mp sufficient
  rcases lowNeeded (Or.inl rfl) (Or.inr (Or.inr (Or.inr rfl))) with
    absurd | absurd | absurd | absurd <;> cases absurd

/-! ## The source satisfies both requests -/

theorem source_sufficient : Suff TypedSyn univ ∧ Suff TypedEv univ := by
  refine ⟨⟨mem_univ _, (observes_iff _).mpr (mem_univ _),
    (preservesSyn_iff _).mpr ⟨fun _ _ => mem_univ _, fun _ _ => mem_univ _⟩⟩, ?_⟩
  rw [suffEv_iff]
  exact ⟨mem_univ _, mem_univ _, Or.inl (mem_univ _), fun _ _ => mem_univ _⟩

#print axioms observes_iff
#print axioms observes_mono
#print axioms syntactic_suff_iff_mem_hornModels
#print axioms syntactic_isLeast
#print axioms repair_eq_hornClosure
#print axioms syntactic_leastAbove
#print axioms syntactic_not_convex
#print axioms evaluation_repairs_minimal
#print axioms evaluation_meet_loses_preservation
#print axioms evaluation_no_least
#print axioms evaluation_not_hornDefinable
#print axioms evaluation_join_not_monotone
#print axioms source_sufficient

end Mettapedia.GSLT.OpenEnded.ComputationBubbles
