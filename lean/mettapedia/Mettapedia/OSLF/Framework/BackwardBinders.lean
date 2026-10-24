import Mettapedia.OSLF.Framework.HerbrandBridge
import Mettapedia.OSLF.Framework.PredFiniteSufficient
import Mettapedia.OSLF.Framework.FiniteModels

/-!
# Predecessors with binders: second-order matching of right sides

A rule whose right side substitutes into a binder's body, such as β (`App (Lam (λ. body)) arg ~>
body[arg]`) or name passing (`Out x y | In x (λ. P) ~> P[y]`), runs backward by matching its right
side against a state: which body and which argument give the state after substitution. This is
second-order matching, and it has finitely many solutions: the argument occurs in the state, or the
body does not use its variable.

- `abstractAt`: every pattern whose bound variable, replaced by a given pattern, gives the target;
  exactly the preimages of instantiation (`mem_abstractAt`).
- `matchBack`: partial assignments of a right side's metavariables that give the target, with
  collections read in order and a rest variable taking the remaining elements. Every assignment that
  agrees with one gives the target (`matchBack_sound`), and every assignment that gives the target, with
  its rest variables bound to collections, agrees with one (`matchBack_complete`). An argument that the
  body does not use is left open.
- `predecessors`: for each rule, its left side with the values `matchBack` fixes. A symbolic predecessor
  stands for the states that match the left side with bindings agreeing with the fixed values
  (`Family.Matches`); each of them steps to the target (`predecessors_sound`), and every object state
  that steps to the target is one of them (`predecessors_complete`). Bags in the left side are matched
  modulo permutation, as the language does, so rho's communication runs backward too.
- Without collections or binder display names in the left side, the states a predecessor stands for are
  the instances of one pattern (`instance_of_matches`, `matches_of_instance`).
- `pastBox_of_check`: the past box of a native type a finite model selects, at a state. Every object
  state that steps to it in one step has an accepted value, when each symbolic predecessor's left side
  is accepted under its fixed values and every table for the rest.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.BackwardBinders

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars liftBVarsList_eq_map instantiateBVarAt instantiateBVar freeVars)
open Mettapedia.OSLF.MeTTaIL.MatchSpec (MatchRel MatchArgsRel matchPattern_sound matchRel_complete
  mergeBindings_subsumed_left mergeBindings_subsumed_right)
open Mettapedia.OSLF.Framework.PredFiniteSufficient (lookupOrFvar BindingsValued mergeBindings_some_of_valued)
open Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction (rootReducts)
open Mettapedia.OSLF.Framework.HerbrandBridge (mem_rootReducts)
open Mettapedia.OSLF.Framework.FiniteModels (RestsBound restVars restVarsList_eq restsCovered ObjectState
  applyBindings_collection_none applyBindings_collection_some restsBound_of_matchRel scoped_of_matchRel occurrences
  occurrencesList_eq mem_of_mergeBindings)

/-! ## Preimages of instantiation -/

mutual
/-- Whether the bound variable at a depth occurs. -/
def hasHole : ℕ → Pattern → Bool
  | depth, .bvar index => index == depth
  | _, .fvar _ => false
  | depth, .apply _ arguments => hasHoleList depth arguments
  | depth, .lambda _ body => hasHole (depth + 1) body
  | depth, .multiLambda arity _ body => hasHole (depth + arity) body
  | depth, .subst body replacement => hasHole (depth + 1) body || hasHole depth replacement
  | depth, .collection _ elements _ => hasHoleList depth elements

def hasHoleList : ℕ → List Pattern → Bool
  | _, [] => false
  | depth, pattern :: patterns => hasHole depth pattern || hasHoleList depth patterns
end

theorem hasHoleList_eq (depth : ℕ) :
    ∀ patterns : List Pattern, hasHoleList depth patterns = patterns.any (hasHole depth)
  | [] => rfl
  | pattern :: patterns => by simp only [hasHoleList, List.any_cons, hasHoleList_eq depth patterns]

/-- The bound variable at a depth, as a hole to fill: itself when the target is the lifted
replacement. -/
def holeAt (replacement : Pattern) (depth : ℕ) (target : Pattern) : List Pattern :=
  if target = liftBVars 0 depth replacement then [.bvar depth] else []

mutual
/-- **The preimages of instantiation**: the patterns whose bound variable at the depth, replaced by
the replacement, give the target. At every node the target may be the filled hole, or have the same
head; a bound variable above the depth was one higher before. -/
def abstractAt (replacement : Pattern) : ℕ → Pattern → List Pattern
  | depth, .bvar index =>
      holeAt replacement depth (.bvar index) ++ [.bvar (if index < depth then index else index + 1)]
  | depth, .fvar name => holeAt replacement depth (.fvar name) ++ [.fvar name]
  | depth, .apply label arguments =>
      holeAt replacement depth (.apply label arguments) ++
        (abstractList replacement depth arguments).map (.apply label)
  | depth, .lambda name body =>
      holeAt replacement depth (.lambda name body) ++ (abstractAt replacement (depth + 1) body).map (.lambda name)
  | depth, .multiLambda arity names body =>
      holeAt replacement depth (.multiLambda arity names body) ++
        (abstractAt replacement (depth + arity) body).map (.multiLambda arity names)
  | depth, .subst body nested =>
      holeAt replacement depth (.subst body nested) ++
        (abstractAt replacement (depth + 1) body).flatMap fun body' =>
          (abstractAt replacement depth nested).map (.subst body')
  | depth, .collection kind elements rest =>
      holeAt replacement depth (.collection kind elements rest) ++
        (abstractList replacement depth elements).map (.collection kind · rest)

def abstractList (replacement : Pattern) : ℕ → List Pattern → List (List Pattern)
  | _, [] => [[]]
  | depth, pattern :: patterns =>
      (abstractAt replacement depth pattern).flatMap fun first =>
        (abstractList replacement depth patterns).map (first :: ·)
end

theorem mem_abstractList_iff {replacement : Pattern} {depth : ℕ} :
    ∀ {targets : List Pattern},
      (∀ target ∈ targets, ∀ preimage,
        preimage ∈ abstractAt replacement depth target ↔ instantiateBVarAt depth replacement preimage = target) →
      ∀ preimages, preimages ∈ abstractList replacement depth targets ↔
        preimages.map (instantiateBVarAt depth replacement) = targets
  | [], _, preimages => by cases preimages <;> simp [abstractList]
  | target :: targets, agree, preimages => by
    have rest := mem_abstractList_iff (targets := targets) fun other member => agree other (List.mem_cons_of_mem _ member)
    cases preimages with
    | nil => simp [abstractList]
    | cons first others =>
      simp only [abstractList, List.mem_flatMap, List.mem_map, List.map_cons, List.cons.injEq]
      constructor
      · rintro ⟨head, headMember, tail, tailMember, same⟩
        obtain ⟨rfl, rfl⟩ := same
        exact ⟨(agree target List.mem_cons_self head).mp headMember, (rest tail).mp tailMember⟩
      · rintro ⟨headSame, tailSame⟩
        exact ⟨first, (agree target List.mem_cons_self first).mpr headSame, others, (rest others).mpr tailSame, rfl, rfl⟩

theorem mem_holeAt {replacement : Pattern} {depth : ℕ} {target preimage : Pattern} :
    preimage ∈ holeAt replacement depth target ↔ preimage = .bvar depth ∧ target = liftBVars 0 depth replacement := by
  unfold holeAt
  split <;> simp_all

theorem instantiate_hole (replacement : Pattern) (depth : ℕ) :
    instantiateBVarAt depth replacement (.bvar depth) = liftBVars 0 depth replacement := by
  simp [instantiateBVarAt]

/-- A bound variable other than the hole instantiates to a bound variable. -/
theorem instantiate_bvar_ne {replacement : Pattern} {depth index : ℕ} (other : index ≠ depth) :
    instantiateBVarAt depth replacement (.bvar index) = .bvar (if index < depth then index else index - 1) := by
  rw [instantiateBVarAt]
  by_cases below : index < depth
  · simp [below]
  · simp [below, other]

/-- **`abstractAt` is exactly the preimage of instantiation.** -/
theorem mem_abstractAt (replacement : Pattern) (target : Pattern) :
    ∀ (depth : ℕ) (preimage : Pattern),
      preimage ∈ abstractAt replacement depth target ↔ instantiateBVarAt depth replacement preimage = target := by
  induction target using Pattern.inductionOn with
  | hbvar index =>
    intro depth preimage
    simp only [abstractAt, List.mem_append, mem_holeAt, List.mem_singleton]
    constructor
    · rintro (⟨rfl, same⟩ | rfl)
      · rw [instantiate_hole, same]
      · split
        · rw [instantiate_bvar_ne (by omega)]; simp [*]
        · rw [instantiate_bvar_ne (by omega)]; simp; omega
    · intro inst
      by_cases hole : preimage = .bvar depth
      · exact Or.inl ⟨hole, by rw [← inst, hole, instantiate_hole]⟩
      · right
        cases preimage with
        | bvar other =>
          have different : other ≠ depth := fun same => hole (by rw [same])
          rw [instantiate_bvar_ne different] at inst
          simp only [Pattern.bvar.injEq] at inst
          split at inst <;> split <;> simp <;> omega
        | _ => simp [instantiateBVarAt] at inst
  | hfvar name =>
    intro depth preimage
    simp only [abstractAt, List.mem_append, mem_holeAt, List.mem_singleton]
    constructor
    · rintro (⟨rfl, same⟩ | rfl)
      · rw [instantiate_hole, same]
      · simp [instantiateBVarAt]
    · intro inst
      by_cases hole : preimage = .bvar depth
      · exact Or.inl ⟨hole, by rw [← inst, hole, instantiate_hole]⟩
      · right
        cases preimage with
        | bvar other =>
          rw [instantiate_bvar_ne fun same => hole (by rw [same])] at inst
          simp at inst
        | fvar other => simpa [instantiateBVarAt] using inst
        | _ => simp [instantiateBVarAt] at inst
  | happly label arguments ih =>
    intro depth preimage
    have lists := mem_abstractList_iff (replacement := replacement) (depth := depth) (targets := arguments)
      fun target member => ih target member depth
    simp only [abstractAt, List.mem_append, mem_holeAt, List.mem_map]
    constructor
    · rintro (⟨rfl, same⟩ | ⟨preimages, member, rfl⟩)
      · rw [instantiate_hole, same]
      · rw [instantiateBVarAt]
        simp only [(lists preimages).mp member]
    · intro inst
      by_cases hole : preimage = .bvar depth
      · exact Or.inl ⟨hole, by rw [← inst, hole, instantiate_hole]⟩
      · right
        cases preimage with
        | bvar other =>
          rw [instantiate_bvar_ne fun same => hole (by rw [same])] at inst
          simp at inst
        | apply otherLabel preimages =>
          rw [instantiateBVarAt] at inst
          simp only [Pattern.apply.injEq] at inst
          obtain ⟨rfl, mapped⟩ := inst
          exact ⟨preimages, (lists preimages).mpr mapped, rfl⟩
        | _ => simp [instantiateBVarAt] at inst
  | hlambda name body ih =>
    intro depth preimage
    simp only [abstractAt, List.mem_append, mem_holeAt, List.mem_map]
    constructor
    · rintro (⟨rfl, same⟩ | ⟨inner, member, rfl⟩)
      · rw [instantiate_hole, same]
      · rw [instantiateBVarAt, (ih (depth + 1) inner).mp member]
    · intro inst
      by_cases hole : preimage = .bvar depth
      · exact Or.inl ⟨hole, by rw [← inst, hole, instantiate_hole]⟩
      · right
        cases preimage with
        | bvar other =>
          rw [instantiate_bvar_ne fun same => hole (by rw [same])] at inst
          simp at inst
        | lambda otherName inner =>
          rw [instantiateBVarAt] at inst
          simp only [Pattern.lambda.injEq] at inst
          obtain ⟨rfl, inside⟩ := inst
          exact ⟨inner, (ih (depth + 1) inner).mpr inside, rfl⟩
        | _ => simp [instantiateBVarAt] at inst
  | hmultiLambda arity names body ih =>
    intro depth preimage
    simp only [abstractAt, List.mem_append, mem_holeAt, List.mem_map]
    constructor
    · rintro (⟨rfl, same⟩ | ⟨inner, member, rfl⟩)
      · rw [instantiate_hole, same]
      · rw [instantiateBVarAt, (ih (depth + arity) inner).mp member]
    · intro inst
      by_cases hole : preimage = .bvar depth
      · exact Or.inl ⟨hole, by rw [← inst, hole, instantiate_hole]⟩
      · right
        cases preimage with
        | bvar other =>
          rw [instantiate_bvar_ne fun same => hole (by rw [same])] at inst
          simp at inst
        | multiLambda otherArity otherNames inner =>
          rw [instantiateBVarAt] at inst
          simp only [Pattern.multiLambda.injEq] at inst
          obtain ⟨rfl, rfl, inside⟩ := inst
          exact ⟨inner, (ih (depth + otherArity) inner).mpr inside, rfl⟩
        | _ => simp [instantiateBVarAt] at inst
  | hsubst body nested bodyIh nestedIh =>
    intro depth preimage
    simp only [abstractAt, List.mem_append, mem_holeAt, List.mem_flatMap, List.mem_map]
    constructor
    · rintro (⟨rfl, same⟩ | ⟨inner, member, other, otherMember, rfl⟩)
      · rw [instantiate_hole, same]
      · rw [instantiateBVarAt, (bodyIh (depth + 1) inner).mp member, (nestedIh depth other).mp otherMember]
    · intro inst
      by_cases hole : preimage = .bvar depth
      · exact Or.inl ⟨hole, by rw [← inst, hole, instantiate_hole]⟩
      · right
        cases preimage with
        | bvar other =>
          rw [instantiate_bvar_ne fun same => hole (by rw [same])] at inst
          simp at inst
        | subst inner other =>
          rw [instantiateBVarAt] at inst
          simp only [Pattern.subst.injEq] at inst
          obtain ⟨inside, outside⟩ := inst
          exact ⟨inner, (bodyIh (depth + 1) inner).mpr inside, other, (nestedIh depth other).mpr outside, rfl⟩
        | _ => simp [instantiateBVarAt] at inst
  | hcollection kind elements rest ih =>
    intro depth preimage
    have lists := mem_abstractList_iff (replacement := replacement) (depth := depth) (targets := elements)
      fun target member => ih target member depth
    simp only [abstractAt, List.mem_append, mem_holeAt, List.mem_map]
    constructor
    · rintro (⟨rfl, same⟩ | ⟨preimages, member, rfl⟩)
      · rw [instantiate_hole, same]
      · rw [instantiateBVarAt]
        simp only [(lists preimages).mp member]
    · intro inst
      by_cases hole : preimage = .bvar depth
      · exact Or.inl ⟨hole, by rw [← inst, hole, instantiate_hole]⟩
      · right
        cases preimage with
        | bvar other =>
          rw [instantiate_bvar_ne fun same => hole (by rw [same])] at inst
          simp at inst
        | collection otherKind preimages otherRest =>
          rw [instantiateBVarAt] at inst
          simp only [Pattern.collection.injEq] at inst
          obtain ⟨rfl, mapped, rfl⟩ := inst
          exact ⟨preimages, (lists preimages).mpr mapped, rfl⟩
        | _ => simp [instantiateBVarAt] at inst

/-- **A body without the hole instantiates the same way whatever fills it.** -/
theorem instantiate_of_no_hole (replacement other : Pattern) (body : Pattern) :
    ∀ depth, hasHole depth body = false →
      instantiateBVarAt depth replacement body = instantiateBVarAt depth other body := by
  induction body using Pattern.inductionOn with
  | hbvar index =>
    intro depth absent
    simp only [hasHole, beq_eq_false_iff_ne] at absent
    rw [instantiate_bvar_ne absent, instantiate_bvar_ne absent]
  | hfvar name => intro _ _; simp [instantiateBVarAt]
  | happly label arguments ih =>
    intro depth absent
    simp only [hasHole, hasHoleList_eq, List.any_eq_false, Bool.not_eq_true] at absent
    rw [instantiateBVarAt, instantiateBVarAt]
    simp only [Pattern.apply.injEq, true_and]
    exact List.map_congr_left fun argument member => ih argument member depth (absent argument member)
  | hlambda name body ih =>
    intro depth absent
    rw [instantiateBVarAt, instantiateBVarAt, ih (depth + 1) absent]
  | hmultiLambda arity names body ih =>
    intro depth absent
    rw [instantiateBVarAt, instantiateBVarAt, ih (depth + arity) absent]
  | hsubst body nested bodyIh nestedIh =>
    intro depth absent
    simp only [hasHole, Bool.or_eq_false_iff] at absent
    rw [instantiateBVarAt, instantiateBVarAt, bodyIh (depth + 1) absent.1, nestedIh depth absent.2]
  | hcollection kind elements rest ih =>
    intro depth absent
    simp only [hasHole, hasHoleList_eq, List.any_eq_false, Bool.not_eq_true] at absent
    rw [instantiateBVarAt, instantiateBVarAt]
    simp only [Pattern.collection.injEq, true_and, and_true]
    exact List.map_congr_left fun element member => ih element member depth (absent element member)

mutual
/-- Every subterm with the number of binders above it, from a starting depth. -/
def subtermsAt : ℕ → Pattern → List (ℕ × Pattern)
  | depth, .bvar index => [(depth, .bvar index)]
  | depth, .fvar name => [(depth, .fvar name)]
  | depth, .apply label arguments => (depth, .apply label arguments) :: subtermsList depth arguments
  | depth, .lambda name body => (depth, .lambda name body) :: subtermsAt (depth + 1) body
  | depth, .multiLambda arity names body =>
      (depth, .multiLambda arity names body) :: subtermsAt (depth + arity) body
  | depth, .subst body nested => (depth, .subst body nested) :: (subtermsAt (depth + 1) body ++ subtermsAt depth nested)
  | depth, .collection kind elements rest => (depth, .collection kind elements rest) :: subtermsList depth elements

def subtermsList : ℕ → List Pattern → List (ℕ × Pattern)
  | _, [] => []
  | depth, pattern :: patterns => subtermsAt depth pattern ++ subtermsList depth patterns
end

theorem subtermsList_eq (depth : ℕ) :
    ∀ patterns : List Pattern, subtermsList depth patterns = patterns.flatMap (subtermsAt depth)
  | [] => rfl
  | pattern :: patterns => by simp only [subtermsList, List.flatMap_cons, subtermsList_eq depth patterns]

theorem root_mem_subtermsAt (depth : ℕ) (pattern : Pattern) : (depth, pattern) ∈ subtermsAt depth pattern := by
  cases pattern <;> simp [subtermsAt]

mutual
/-- Lower the bound variables from a cutoff by a shift; none when one of them falls in between. -/
def lowerBVars? (cutoff shift : ℕ) : Pattern → Option Pattern
  | .bvar index =>
      if index < cutoff then some (.bvar index)
      else if index < cutoff + shift then none
      else some (.bvar (index - shift))
  | .fvar name => some (.fvar name)
  | .apply label arguments => (lowerList? cutoff shift arguments).map (.apply label)
  | .lambda name body => (lowerBVars? (cutoff + 1) shift body).map (.lambda name)
  | .multiLambda arity names body => (lowerBVars? (cutoff + arity) shift body).map (.multiLambda arity names)
  | .subst body nested =>
      (lowerBVars? (cutoff + 1) shift body).bind fun body' => (lowerBVars? cutoff shift nested).map (.subst body')
  | .collection kind elements rest => (lowerList? cutoff shift elements).map (.collection kind · rest)

def lowerList? (cutoff shift : ℕ) : List Pattern → Option (List Pattern)
  | [] => some []
  | pattern :: patterns =>
      (lowerBVars? cutoff shift pattern).bind fun first => (lowerList? cutoff shift patterns).map (first :: ·)
end

theorem lowerList?_map (cutoff shift : ℕ) :
    ∀ patterns : List Pattern, (∀ pattern ∈ patterns, lowerBVars? cutoff shift (liftBVars cutoff shift pattern) = some pattern) →
      lowerList? cutoff shift (patterns.map (liftBVars cutoff shift)) = some patterns
  | [], _ => rfl
  | pattern :: patterns, lowered => by
    simp only [List.map_cons, lowerList?, lowered pattern List.mem_cons_self, Option.bind_some,
      lowerList?_map cutoff shift patterns fun other member => lowered other (List.mem_cons_of_mem _ member),
      Option.map_some]

/-- **Lowering undoes lifting.** -/
theorem lower_lift (pattern : Pattern) :
    ∀ cutoff shift, lowerBVars? cutoff shift (liftBVars cutoff shift pattern) = some pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
    intro cutoff shift
    simp only [liftBVars]
    by_cases above : index ≥ cutoff
    · simp only [above, ↓reduceIte, lowerBVars?]
      rw [if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel]
    · simp only [above, ↓reduceIte, lowerBVars?]
      rw [if_pos (by omega)]
  | hfvar name => intro _ _; rfl
  | happly label arguments ih =>
    intro cutoff shift
    simp only [liftBVars, liftBVarsList_eq_map, lowerBVars?,
      lowerList?_map cutoff shift arguments fun argument member => ih argument member cutoff shift, Option.map_some]
  | hlambda name body ih =>
    intro cutoff shift
    simp only [liftBVars, lowerBVars?, ih (cutoff + 1) shift, Option.map_some]
  | hmultiLambda arity names body ih =>
    intro cutoff shift
    simp only [liftBVars, lowerBVars?, ih (cutoff + arity) shift, Option.map_some]
  | hsubst body nested bodyIh nestedIh =>
    intro cutoff shift
    simp only [liftBVars, lowerBVars?, bodyIh (cutoff + 1) shift, nestedIh cutoff shift, Option.bind_some,
      Option.map_some]
  | hcollection kind elements rest ih =>
    intro cutoff shift
    simp only [liftBVars, liftBVarsList_eq_map, lowerBVars?,
      lowerList?_map cutoff shift elements fun element member => ih element member cutoff shift, Option.map_some]

/-- **Where the hole was filled, the lifted replacement occurs.** -/
theorem occurs_of_hole (replacement : Pattern) (body : Pattern) :
    ∀ depth, hasHole depth body = true →
      ∃ inner, (inner, liftBVars 0 inner replacement) ∈ subtermsAt depth (instantiateBVarAt depth replacement body) := by
  induction body using Pattern.inductionOn with
  | hbvar index =>
    intro depth present
    simp only [hasHole, beq_iff_eq] at present
    subst present
    rw [instantiate_hole]
    exact ⟨index, root_mem_subtermsAt _ _⟩
  | hfvar name => intro _ present; simp [hasHole] at present
  | happly label arguments ih =>
    intro depth present
    simp only [hasHole, hasHoleList_eq, List.any_eq_true] at present
    obtain ⟨argument, member, inside⟩ := present
    obtain ⟨inner, found⟩ := ih argument member depth inside
    refine ⟨inner, ?_⟩
    rw [instantiateBVarAt]
    simp only [subtermsAt, subtermsList_eq, List.mem_cons, List.mem_flatMap, List.mem_map]
    exact Or.inr ⟨_, ⟨argument, member, rfl⟩, found⟩
  | hlambda name body ih =>
    intro depth present
    obtain ⟨inner, found⟩ := ih (depth + 1) present
    exact ⟨inner, by rw [instantiateBVarAt]; exact List.mem_cons_of_mem _ found⟩
  | hmultiLambda arity names body ih =>
    intro depth present
    obtain ⟨inner, found⟩ := ih (depth + arity) present
    exact ⟨inner, by rw [instantiateBVarAt]; exact List.mem_cons_of_mem _ found⟩
  | hsubst body nested bodyIh nestedIh =>
    intro depth present
    simp only [hasHole, Bool.or_eq_true] at present
    rw [instantiateBVarAt]
    rcases present with inBody | inNested
    · obtain ⟨inner, found⟩ := bodyIh (depth + 1) inBody
      exact ⟨inner, List.mem_cons_of_mem _ (List.mem_append_left _ found)⟩
    · obtain ⟨inner, found⟩ := nestedIh depth inNested
      exact ⟨inner, List.mem_cons_of_mem _ (List.mem_append_right _ found)⟩
  | hcollection kind elements rest ih =>
    intro depth present
    simp only [hasHole, hasHoleList_eq, List.any_eq_true] at present
    obtain ⟨element, member, inside⟩ := present
    obtain ⟨inner, found⟩ := ih element member depth inside
    refine ⟨inner, ?_⟩
    rw [instantiateBVarAt]
    simp only [subtermsAt, subtermsList_eq, List.mem_cons, List.mem_flatMap, List.mem_map]
    exact Or.inr ⟨_, ⟨element, member, rfl⟩, found⟩

/-- The patterns a substituted argument may have been: every subterm of the target, lowered by the
binders above it. -/
def candidates (target : Pattern) : List Pattern :=
  (subtermsAt 0 target).filterMap fun entry => lowerBVars? 0 entry.1 entry.2

theorem mem_candidates {replacement body : Pattern} (present : hasHole 0 body = true) :
    replacement ∈ candidates (instantiateBVarAt 0 replacement body) := by
  obtain ⟨inner, found⟩ := occurs_of_hole replacement body 0 present
  exact List.mem_filterMap.mpr ⟨_, found, lower_lift replacement 0 inner⟩

/-! ## Matching right sides backward -/

mutual
/-- **Match a right side backward**: partial assignments of its metavariables under which it gives the
target. For an explicit substitution, the argument is a candidate from the target, matched in turn,
and the body is the target abstracted over some of the argument's occurrences; or the body does not
use its variable, and the argument stays open. -/
def matchBack : Pattern → Pattern → List Bindings
  | .fvar name, target => [[(name, target)]]
  | .bvar index, target => if target = .bvar index then [[]] else []
  | .apply label arguments, target =>
      match target with
      | .apply label' targets => if label = label' then matchBackList arguments targets else []
      | _ => []
  | .lambda name body, target =>
      match target with
      | .lambda name' inner => if name = name' then matchBack body inner else []
      | _ => []
  | .multiLambda arity names body, target =>
      match target with
      | .multiLambda arity' names' inner => if arity = arity' ∧ names = names' then matchBack body inner else []
      | _ => []
  | .subst body argument, target =>
      ((candidates target).dedup.flatMap fun value =>
        (matchBack argument value).flatMap fun first =>
          ((abstractAt value 0 target).filter (hasHole 0)).flatMap fun abstracted =>
            (matchBack body abstracted).filterMap (mergeBindings first)) ++
      ((abstractAt (.bvar 0) 0 target).filter (fun abstracted => !hasHole 0 abstracted)).flatMap (matchBack body)
  | .collection kind elements rest, target =>
      match target with
      | .collection kind' targets none =>
          if kind = kind' then
            match rest with
            | none => matchBackList elements targets
            | some name =>
                if elements.length ≤ targets.length then
                  (matchBackList elements (targets.take elements.length)).filterMap fun fixed =>
                    mergeBindings fixed [(name, .collection kind (targets.drop elements.length) none)]
                else []
          else []
      | _ => []

def matchBackList : List Pattern → List Pattern → List Bindings
  | [], [] => [[]]
  | pattern :: patterns, target :: targets =>
      (matchBack pattern target).flatMap fun first => (matchBackList patterns targets).filterMap (mergeBindings first)
  | _, _ => []
end

/-- Bindings agree with fixed values: each fixed metavariable reads its value. -/
def Agrees (fixed bindings : Bindings) : Prop :=
  ∀ name value, fixed.find? (·.1 == name) = some (name, value) → lookupOrFvar bindings name = value

theorem agrees_left {first second merged bindings : Bindings} (merge : mergeBindings first second = some merged)
    (agrees : Agrees merged bindings) : Agrees first bindings :=
  fun name value found => agrees name value (mergeBindings_subsumed_left merge found)

theorem agrees_right {first second merged bindings : Bindings} (merge : mergeBindings first second = some merged)
    (agrees : Agrees merged bindings) : Agrees second bindings :=
  fun name value found => agrees name value (mergeBindings_subsumed_right merge found)

theorem agrees_of_valued {fixed bindings : Bindings} (valued : BindingsValued fixed (lookupOrFvar bindings)) :
    Agrees fixed bindings := fun name value found => by
  have member := List.mem_of_find?_eq_some found
  exact (valued name value member).symm

/-- A metavariable that reads a collection is bound to it. -/
theorem find_of_lookup {bindings : Bindings} {name : String} {kind : CollType} {elements : List Pattern}
    {rest : Option String} (read : lookupOrFvar bindings name = .collection kind elements rest) :
    bindings.find? (·.1 == name) = some (name, .collection kind elements rest) := by
  simp only [lookupOrFvar, applyBindings] at read
  cases found : bindings.find? (·.1 == name) with
  | none => simp [found] at read
  | some entry =>
    obtain ⟨key, value⟩ := entry
    have same : key = name := by simpa using List.find?_some found
    subst same
    simp only [found] at read
    rw [read]

theorem applyBindings_subst (bindings : Bindings) (body argument : Pattern) :
    applyBindings bindings (.subst body argument) =
      instantiateBVar (applyBindings bindings argument) (applyBindings bindings body) := by
  rw [applyBindings]

mutual
/-- **Every assignment agreeing with a backward match gives the target.** -/
theorem matchBack_sound : ∀ (pattern target : Pattern) (fixed : Bindings), fixed ∈ matchBack pattern target →
    ∀ bindings, Agrees fixed bindings → applyBindings bindings pattern = target
  | .fvar name, target, fixed, member, bindings, agrees => by
    simp only [matchBack, List.mem_singleton] at member
    subst member
    exact agrees name target (by simp)
  | .bvar index, target, fixed, member, bindings, _ => by
    simp only [matchBack] at member
    split at member
    · rw [applyBindings]; simp_all
    · simp at member
  | .apply label arguments, target, fixed, member, bindings, agrees => by
    cases target with
    | apply label' targets =>
      simp only [matchBack] at member
      split at member
      · rename_i same
        subst same
        rw [applyBindings]
        rw [matchBackList_sound arguments targets fixed member bindings agrees]
      · simp at member
    | _ => simp [matchBack] at member
  | .lambda name body, target, fixed, member, bindings, agrees => by
    cases target with
    | lambda name' inner =>
      simp only [matchBack] at member
      split at member
      · rename_i same
        subst same
        rw [applyBindings, matchBack_sound body inner fixed member bindings agrees]
      · simp at member
    | _ => simp [matchBack] at member
  | .multiLambda arity names body, target, fixed, member, bindings, agrees => by
    cases target with
    | multiLambda arity' names' inner =>
      simp only [matchBack] at member
      split at member
      · rename_i same
        obtain ⟨rfl, rfl⟩ := same
        rw [applyBindings, matchBack_sound body inner fixed member bindings agrees]
      · simp at member
    | _ => simp [matchBack] at member
  | .subst body argument, target, fixed, member, bindings, agrees => by
    rw [applyBindings_subst]
    simp only [matchBack, List.mem_append, List.mem_flatMap, List.mem_filter, List.mem_filterMap] at member
    rcases member with ⟨value, _, first, firstMember, abstracted, ⟨abstractedMember, _⟩, second, secondMember, merge⟩ |
        ⟨abstracted, ⟨abstractedMember, absent⟩, fixedMember⟩
    · rw [matchBack_sound argument value first firstMember bindings (agrees_left merge agrees),
        matchBack_sound body abstracted second secondMember bindings (agrees_right merge agrees)]
      exact (mem_abstractAt value target 0 abstracted).mp abstractedMember
    · rw [matchBack_sound body abstracted fixed fixedMember bindings agrees, instantiateBVar,
        instantiate_of_no_hole _ (.bvar 0) abstracted 0 (by simpa using absent)]
      exact (mem_abstractAt (.bvar 0) target 0 abstracted).mp abstractedMember
  | .collection kind elements rest, target, fixed, member, bindings, agrees => by
    cases target with
    | collection kind' targets targetRest =>
      cases targetRest with
      | some _ => simp [matchBack] at member
      | none =>
        simp only [matchBack] at member
        split at member
        · rename_i same
          subst same
          cases rest with
          | none =>
            rw [applyBindings_collection_none, matchBackList_sound elements targets fixed member bindings agrees]
          | some name =>
            simp only at member
            split at member
            · obtain ⟨prefixFixed, prefixMember, merge⟩ := List.mem_filterMap.mp member
              have found := find_of_lookup (agrees_right merge agrees name (.collection kind (targets.drop elements.length) none)
                (by simp))
              rw [applyBindings_collection_some found, matchBackList_sound elements _ prefixFixed prefixMember bindings
                (agrees_left merge agrees), List.take_append_drop]
            · simp at member
        · simp at member
    | _ => simp [matchBack] at member

theorem matchBackList_sound : ∀ (patterns targets : List Pattern) (fixed : Bindings),
    fixed ∈ matchBackList patterns targets →
    ∀ bindings, Agrees fixed bindings → patterns.map (applyBindings bindings) = targets
  | [], [], _, _, _, _ => rfl
  | pattern :: patterns, target :: targets, fixed, member, bindings, agrees => by
    simp only [matchBackList, List.mem_flatMap, List.mem_filterMap] at member
    obtain ⟨first, firstMember, rest, restMember, merge⟩ := member
    simp only [List.map_cons, matchBack_sound pattern target first firstMember bindings (agrees_left merge agrees),
      matchBackList_sound patterns targets rest restMember bindings (agrees_right merge agrees)]
  | [], _ :: _, _, member, _, _ => by simp [matchBackList] at member
  | _ :: _, [], _, member, _, _ => by simp [matchBackList] at member
end

theorem valued_singleton (bindings : Bindings) (name : String) :
    BindingsValued [(name, lookupOrFvar bindings name)] (lookupOrFvar bindings) := by
  intro other value member
  simp only [List.mem_singleton, Prod.mk.injEq] at member
  obtain ⟨rfl, rfl⟩ := member
  rfl

theorem restsBound_of_subset {bindings : Bindings} {pattern : Pattern} (bound : RestsBound bindings pattern)
    {other : Pattern} (within : ∀ entry ∈ restVars other, entry ∈ restVars pattern) : RestsBound bindings other :=
  fun entry inside => bound entry (within entry inside)

mutual
/-- **Every assignment giving the target agrees with a backward match**, when the right side's rest
variables are bound to collections of their kinds. -/
theorem matchBack_complete : ∀ (pattern : Pattern) (bindings : Bindings), RestsBound bindings pattern →
    ∃ fixed ∈ matchBack pattern (applyBindings bindings pattern), BindingsValued fixed (lookupOrFvar bindings)
  | .fvar name, bindings, _ => ⟨[(name, lookupOrFvar bindings name)], by simp [matchBack, lookupOrFvar],
      valued_singleton bindings name⟩
  | .bvar index, bindings, _ => ⟨[], by rw [applyBindings]; simp [matchBack], fun _ _ member => by simp at member⟩
  | .apply label arguments, bindings, bound => by
    obtain ⟨fixed, member, valued⟩ := matchBackList_complete arguments bindings fun argument inside =>
      restsBound_of_subset bound fun entry within => by
        simp only [restVars, restVarsList_eq, List.mem_flatMap]
        exact ⟨argument, inside, within⟩
    refine ⟨fixed, ?_, valued⟩
    rw [applyBindings]
    simpa [matchBack] using member
  | .lambda name body, bindings, bound => by
    obtain ⟨fixed, member, valued⟩ := matchBack_complete body bindings (restsBound_of_subset bound fun entry within => by
      simpa [restVars] using within)
    refine ⟨fixed, ?_, valued⟩
    rw [applyBindings]
    simpa [matchBack] using member
  | .multiLambda arity names body, bindings, bound => by
    obtain ⟨fixed, member, valued⟩ := matchBack_complete body bindings (restsBound_of_subset bound fun entry within => by
      simpa [restVars] using within)
    refine ⟨fixed, ?_, valued⟩
    rw [applyBindings]
    simpa [matchBack] using member
  | .subst body argument, bindings, bound => by
    obtain ⟨second, secondMember, secondValued⟩ := matchBack_complete body bindings
      (restsBound_of_subset bound fun entry within => by simp [restVars, within])
    rw [applyBindings_subst, instantiateBVar]
    simp only [matchBack, List.mem_append, List.mem_flatMap, List.mem_filter, List.mem_filterMap]
    by_cases present : hasHole 0 (applyBindings bindings body) = true
    · obtain ⟨first, firstMember, firstValued⟩ := matchBack_complete argument bindings
        (restsBound_of_subset bound fun entry within => by simp [restVars, within])
      obtain ⟨merged, merge, mergedValued⟩ := mergeBindings_some_of_valued first second _ firstValued secondValued
      exact ⟨merged, Or.inl ⟨_, List.mem_dedup.mpr (mem_candidates present), first, firstMember, _,
        ⟨(mem_abstractAt _ _ 0 _).mpr rfl, present⟩, second, secondMember, merge⟩, mergedValued⟩
    · have absent : hasHole 0 (applyBindings bindings body) = false := by simpa using present
      refine ⟨second, Or.inr ⟨_, ⟨(mem_abstractAt _ _ 0 _).mpr ?_, by simp [absent]⟩, secondMember⟩, secondValued⟩
      exact instantiate_of_no_hole _ _ _ 0 absent
  | .collection kind elements rest, bindings, bound => by
    have elementsBound : ∀ element ∈ elements, RestsBound bindings element := fun element inside =>
      restsBound_of_subset bound fun entry within => by
        simp only [restVars, restVarsList_eq, List.mem_append, List.mem_flatMap]
        exact Or.inl ⟨element, inside, within⟩
    obtain ⟨fixed, member, valued⟩ := matchBackList_complete elements bindings elementsBound
    cases rest with
    | none =>
      refine ⟨fixed, ?_, valued⟩
      rw [applyBindings_collection_none]
      simpa [matchBack] using member
    | some name =>
      obtain ⟨restElements, found⟩ := bound (name, kind) (by simp [restVars])
      have read : lookupOrFvar bindings name = .collection kind restElements none := by
        simp [lookupOrFvar, applyBindings, found]
      obtain ⟨merged, merge, mergedValued⟩ := mergeBindings_some_of_valued fixed
        [(name, .collection kind restElements none)] _ valued (by rw [← read]; exact valued_singleton bindings name)
      refine ⟨merged, ?_, mergedValued⟩
      rw [applyBindings_collection_some found]
      simp only [matchBack, ↓reduceIte, List.length_append, List.length_map, Nat.le_add_right,
        List.mem_filterMap]
      refine ⟨fixed, ?_, ?_⟩
      · simpa [List.take_left'] using member
      · simpa [List.drop_left'] using merge

theorem matchBackList_complete : ∀ (patterns : List Pattern) (bindings : Bindings),
    (∀ pattern ∈ patterns, RestsBound bindings pattern) →
    ∃ fixed ∈ matchBackList patterns (patterns.map (applyBindings bindings)), BindingsValued fixed (lookupOrFvar bindings)
  | [], _, _ => ⟨[], by simp [matchBackList], fun _ _ member => by simp at member⟩
  | pattern :: patterns, bindings, bound => by
    obtain ⟨first, firstMember, firstValued⟩ := matchBack_complete pattern bindings (bound pattern List.mem_cons_self)
    obtain ⟨rest, restMember, restValued⟩ := matchBackList_complete patterns bindings fun other inside =>
      bound other (List.mem_cons_of_mem _ inside)
    obtain ⟨merged, merge, mergedValued⟩ := mergeBindings_some_of_valued first rest _ firstValued restValued
    exact ⟨merged, by
      simp only [List.map_cons, matchBackList, List.mem_flatMap, List.mem_filterMap]
      exact ⟨first, firstMember, rest, restMember, merge⟩, mergedValued⟩
end

/-! ## Matching instances of left sides -/

mutual
/-- Whether a pattern uses no explicit substitution and no collection: the left sides `matchPattern`
reconstructs. -/
def leftShape : Pattern → Bool
  | .bvar _ => true
  | .fvar _ => true
  | .apply _ arguments => leftShapeList arguments
  | .lambda _ body => leftShape body
  | .multiLambda _ _ body => leftShape body
  | .subst _ _ => false
  | .collection _ _ _ => false

def leftShapeList : List Pattern → Bool
  | [] => true
  | pattern :: patterns => leftShape pattern && leftShapeList patterns
end

theorem leftShapeList_eq : ∀ patterns : List Pattern, leftShapeList patterns = patterns.all leftShape
  | [] => rfl
  | pattern :: patterns => by simp only [leftShapeList, List.all_cons, leftShapeList_eq patterns]

mutual
/-- Whether no binder carries a display name, as in the core. -/
def nameless : Pattern → Bool
  | .bvar _ => true
  | .fvar _ => true
  | .apply _ arguments => namelessList arguments
  | .lambda name body => name.isNone && nameless body
  | .multiLambda _ names body => names.isEmpty && nameless body
  | .subst body argument => nameless body && nameless argument
  | .collection _ elements _ => namelessList elements

def namelessList : List Pattern → Bool
  | [] => true
  | pattern :: patterns => nameless pattern && namelessList patterns
end

theorem freeVars_apply (label : String) (arguments : List Pattern) :
    freeVars (.apply label arguments) = arguments.flatMap freeVars := by
  rw [freeVars]

theorem bound_of_find {bindings : Bindings} {name : String} {value : Pattern}
    (found : bindings.find? (·.1 == name) = some (name, value)) : lookupOrFvar bindings name = value := by
  simp [lookupOrFvar, applyBindings, found]

mutual
/-- **Matching an instance of a left side succeeds**, with bindings that read the instance's values
on every metavariable of the left side. -/
theorem exists_matchRel : ∀ (pattern : Pattern), leftShape pattern = true → ∀ bindings : Bindings,
    ∃ matched, MatchRel pattern (applyBindings bindings pattern) matched ∧
      BindingsValued matched (lookupOrFvar bindings) ∧
      ∀ name ∈ freeVars pattern, ∃ value, matched.find? (·.1 == name) = some (name, value)
  | .fvar name, _, bindings => by
    refine ⟨[(name, lookupOrFvar bindings name)], .fvar, valued_singleton bindings name, ?_⟩
    intro other member
    rw [freeVars] at member
    simp only [List.mem_singleton] at member
    subst member
    exact ⟨lookupOrFvar bindings other, by simp⟩
  | .bvar index, _, bindings => by
    refine ⟨[], by rw [applyBindings]; exact .bvar, fun _ _ member => by simp at member, ?_⟩
    intro name member
    rw [freeVars] at member
    simp at member
  | .apply label arguments, shape, bindings => by
    simp only [leftShape] at shape
    obtain ⟨matched, relation, valued, covers⟩ := exists_matchArgsRel arguments shape bindings
    refine ⟨matched, ?_, valued, fun name member => covers name (by rwa [freeVars_apply] at member)⟩
    rw [applyBindings]
    exact .apply relation (by simp)
  | .lambda name body, shape, bindings => by
    simp only [leftShape] at shape
    obtain ⟨matched, relation, valued, covers⟩ := exists_matchRel body shape bindings
    refine ⟨matched, ?_, valued, fun other member => covers other (by rwa [freeVars] at member)⟩
    rw [applyBindings]
    exact .lambda relation
  | .multiLambda arity names body, shape, bindings => by
    simp only [leftShape] at shape
    obtain ⟨matched, relation, valued, covers⟩ := exists_matchRel body shape bindings
    refine ⟨matched, ?_, valued, fun other member => covers other (by rwa [freeVars] at member)⟩
    rw [applyBindings]
    exact .multiLambda relation
  | .subst _ _, shape, _ => by simp [leftShape] at shape
  | .collection _ _ _, shape, _ => by simp [leftShape] at shape

theorem exists_matchArgsRel : ∀ (patterns : List Pattern), leftShapeList patterns = true → ∀ bindings : Bindings,
    ∃ matched, MatchArgsRel patterns (patterns.map (applyBindings bindings)) matched ∧
      BindingsValued matched (lookupOrFvar bindings) ∧
      ∀ name ∈ patterns.flatMap freeVars, ∃ value, matched.find? (·.1 == name) = some (name, value)
  | [], _, _ => ⟨[], .nil, fun _ _ member => by simp at member, fun _ member => by simp at member⟩
  | pattern :: patterns, shape, bindings => by
    simp only [leftShapeList, Bool.and_eq_true] at shape
    obtain ⟨first, firstRelation, firstValued, firstCovers⟩ := exists_matchRel pattern shape.1 bindings
    obtain ⟨rest, restRelation, restValued, restCovers⟩ := exists_matchArgsRel patterns shape.2 bindings
    obtain ⟨merged, merge, mergedValued⟩ := mergeBindings_some_of_valued first rest _ firstValued restValued
    refine ⟨merged, .cons firstRelation restRelation merge, mergedValued, ?_⟩
    intro name member
    simp only [List.flatMap_cons, List.mem_append] at member
    rcases member with inFirst | inRest
    · obtain ⟨value, found⟩ := firstCovers name inFirst
      exact ⟨value, mergeBindings_subsumed_left merge found⟩
    · obtain ⟨value, found⟩ := restCovers name inRest
      exact ⟨value, mergeBindings_subsumed_right merge found⟩
end

mutual
/-- **A match reconstructs the matched state**, for left sides without explicit substitutions or
collections, when neither side carries binder display names. -/
theorem applyBindings_of_matchRel : ∀ (pattern state : Pattern) (matched : Bindings),
    MatchRel pattern state matched → leftShape pattern = true → nameless pattern = true → nameless state = true →
    ∀ larger : Bindings, (∀ name value, matched.find? (·.1 == name) = some (name, value) →
      larger.find? (·.1 == name) = some (name, value)) → applyBindings larger pattern = state
  | .fvar name, state, _, .fvar, _, _, _, larger, extends_ => by
    have found := extends_ name state (by simp)
    simp [applyBindings, found]
  | .bvar index, _, _, .bvar, _, _, _, _, _ => by rw [applyBindings]
  | .apply label arguments, _, matched, .apply relation _, shape, patternNameless, stateNameless, larger,
      extends_ => by
    simp only [leftShape] at shape
    simp only [nameless] at patternNameless stateNameless
    rw [applyBindings, applyBindingsList_of_matchArgsRel arguments _ matched relation shape patternNameless
      stateNameless larger extends_]
  | .lambda name body, .lambda name' inner, matched, .lambda relation, shape, patternNameless, stateNameless,
      larger, extends_ => by
    simp only [leftShape] at shape
    simp only [nameless, Bool.and_eq_true, Option.isNone_iff_eq_none] at patternNameless stateNameless
    rw [applyBindings, applyBindings_of_matchRel body inner matched relation shape patternNameless.2
      stateNameless.2 larger extends_, patternNameless.1, stateNameless.1]
  | .multiLambda arity names body, .multiLambda _ names' inner, matched, .multiLambda relation, shape,
      patternNameless, stateNameless, larger, extends_ => by
    simp only [leftShape] at shape
    simp only [nameless, Bool.and_eq_true, List.isEmpty_iff] at patternNameless stateNameless
    rw [applyBindings, applyBindings_of_matchRel body inner matched relation shape patternNameless.2
      stateNameless.2 larger extends_, patternNameless.1, stateNameless.1]
  | .subst _ _, _, _, _, shape, _, _, _, _ => by simp [leftShape] at shape
  | .collection _ _ _, _, _, _, shape, _, _, _, _ => by simp [leftShape] at shape

theorem applyBindingsList_of_matchArgsRel : ∀ (patterns states : List Pattern) (matched : Bindings),
    MatchArgsRel patterns states matched → leftShapeList patterns = true → namelessList patterns = true →
    namelessList states = true →
    ∀ larger : Bindings, (∀ name value, matched.find? (·.1 == name) = some (name, value) →
      larger.find? (·.1 == name) = some (name, value)) → patterns.map (applyBindings larger) = states
  | [], [], _, .nil, _, _, _, _, _ => rfl
  | pattern :: patterns, state :: states, matched, .cons relation rest merge, shape, patternNameless,
      stateNameless, larger, extends_ => by
    simp only [leftShapeList, namelessList, Bool.and_eq_true] at shape patternNameless stateNameless
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨applyBindings_of_matchRel pattern state _ relation shape.1 patternNameless.1 stateNameless.1 larger
        fun name value found => extends_ name value (mergeBindings_subsumed_left merge found),
      applyBindingsList_of_matchArgsRel patterns states _ rest shape.2 patternNameless.2 stateNameless.2 larger
        fun name value found => extends_ name value (mergeBindings_subsumed_right merge found)⟩
end

/-! ## Predecessors -/

mutual
/-- Whether a pattern uses no explicit substitution. -/
def substFree : Pattern → Bool
  | .bvar _ => true
  | .fvar _ => true
  | .apply _ arguments => substFreeList arguments
  | .lambda _ body => substFree body
  | .multiLambda _ _ body => substFree body
  | .subst _ _ => false
  | .collection _ elements _ => substFreeList elements

def substFreeList : List Pattern → Bool
  | [] => true
  | pattern :: patterns => substFree pattern && substFreeList patterns
end

theorem substFreeList_eq : ∀ patterns : List Pattern, substFreeList patterns = patterns.all substFree
  | [] => rfl
  | pattern :: patterns => by simp only [substFreeList, List.all_cons, substFreeList_eq patterns]

/-- A rule runs backward: its left side is in scope and uses no explicit substitution, and its right
side uses only rest variables its left side binds. -/
def ruleBackward (rule : RewriteRule) : Bool :=
  rule.left.isWellScopedAt 0 && substFree rule.left && restsCovered rule

/-- **A symbolic predecessor**: a rule's left side, with values fixed for some of its metavariables. -/
structure Family where
  rule : RewriteRule
  fixed : Bindings
  deriving Repr

/-- A symbolic predecessor as a pattern: the left side with its fixed values in place. -/
def Family.pattern (family : Family) : Pattern := applyBindings family.fixed family.rule.left

/-- **The states a symbolic predecessor stands for**: those matching the rule's left side with bindings
that agree with the fixed values. -/
def Family.Matches (family : Family) (state : Pattern) : Prop :=
  ∃ bindings ∈ matchPattern family.rule.left state, Agrees family.fixed bindings

/-- The symbolic predecessors of a state: for each rule that runs backward, its left side with the
values of each backward match of its right side, kept when its bound variables are in scope. -/
def predecessors (language : LanguageDef) (target : Pattern) : List Family :=
  (language.rewrites.flatMap fun rule =>
    if ruleBackward rule then (matchBack rule.right target).map (Family.mk rule) else []).filter
      fun family => family.pattern.isWellScopedAt 0

theorem mem_predecessors {language : LanguageDef} {target : Pattern} {family : Family} :
    family ∈ predecessors language target ↔
      family.rule ∈ language.rewrites ∧ ruleBackward family.rule = true ∧
        family.fixed ∈ matchBack family.rule.right target ∧ family.pattern.isWellScopedAt 0 = true := by
  obtain ⟨rule, fixed⟩ := family
  simp only [predecessors, List.mem_filter, List.mem_flatMap]
  constructor
  · rintro ⟨⟨other, member, inRule⟩, inScope⟩
    split at inRule
    · obtain ⟨_, fixedMember, same⟩ := List.mem_map.mp inRule
      cases same
      exact ⟨member, by assumption, fixedMember, inScope⟩
    · simp at inRule
  · rintro ⟨member, backward, fixedMember, inScope⟩
    exact ⟨⟨rule, member, by simp [backward, fixedMember]⟩, inScope⟩

/-- **Every state a symbolic predecessor stands for steps to the target.** -/
theorem predecessors_sound {language : LanguageDef} {target : Pattern} {family : Family}
    (member : family ∈ predecessors language target) {state : Pattern} (matches_ : family.Matches state) :
    target ∈ rootReducts language state := by
  obtain ⟨ruleMember, _, fixedMember, _⟩ := mem_predecessors.mp member
  obtain ⟨bindings, matched, agrees⟩ := matches_
  exact mem_rootReducts.mpr ⟨family.rule, ruleMember, bindings, matched,
    matchBack_sound _ _ _ fixedMember bindings agrees⟩

/-- **Fixed values in scope keep a left side in scope.** -/
theorem scoped_applyBindings (fixed : Bindings) (pattern : Pattern) (free : substFree pattern = true) :
    ∀ depth, pattern.isWellScopedAt depth = true →
      (∀ entry ∈ occurrences depth pattern, ∀ value, fixed.find? (·.1 == entry.1) = some (entry.1, value) →
        value.isWellScopedAt entry.2 = true) →
      (applyBindings fixed pattern).isWellScopedAt depth = true := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro depth inScope _; rwa [applyBindings]
  | hfvar name =>
    intro depth _ values
    cases found : fixed.find? (·.1 == name) with
    | none => simp [applyBindings, found, Pattern.isWellScopedAt]
    | some entry =>
      obtain ⟨key, value⟩ := entry
      have same : key = name := by simpa using List.find?_some found
      subst same
      simp only [applyBindings, found]
      exact values (key, depth) (by simp [occurrences]) value found
  | happly label arguments ih =>
    intro depth inScope values
    simp only [substFree, substFreeList_eq, List.all_eq_true] at free
    rw [applyBindings]
    simp only [Pattern.isWellScopedAt, Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff,
      List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at inScope ⊢
    exact fun argument member => ih argument member (free argument member) depth (inScope argument member)
      fun entry inside => values entry (by
        simp only [occurrences, occurrencesList_eq, List.mem_flatMap]
        exact ⟨argument, member, inside⟩)
  | hlambda name body ih =>
    intro depth inScope values
    rw [applyBindings]
    exact ih (by simpa [substFree] using free) (depth + 1) inScope fun entry inside =>
      values entry (by simpa [occurrences] using inside)
  | hmultiLambda arity names body ih =>
    intro depth inScope values
    rw [applyBindings]
    exact ih (by simpa [substFree] using free) (depth + arity) inScope fun entry inside =>
      values entry (by simpa [occurrences] using inside)
  | hsubst _ _ _ _ => simp [substFree] at free
  | hcollection kind elements rest ih =>
    intro depth inScope values
    simp only [substFree, substFreeList_eq, List.all_eq_true] at free
    simp only [Pattern.isWellScopedAt, Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff] at inScope
    have mapped : ∀ element ∈ elements.map (applyBindings fixed), element.isWellScopedAt depth = true := by
      simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      exact fun element member => ih element member (free element member) depth (inScope element member)
        fun entry inside => values entry (by
          simp only [occurrences, occurrencesList_eq, List.mem_append, List.mem_flatMap]
          exact Or.inl ⟨element, member, inside⟩)
    cases rest with
    | none =>
      rw [applyBindings_collection_none]
      simpa [Pattern.isWellScopedAt, Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff] using mapped
    | some name =>
      rw [applyBindings]
      cases found : fixed.find? (·.1 == name) with
      | none =>
        simpa [found, Pattern.isWellScopedAt, Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff]
          using mapped
      | some entry =>
        obtain ⟨key, value⟩ := entry
        have same : key = name := by simpa using List.find?_some found
        subst same
        have valueScoped := values (key, depth) (by simp [occurrences]) value found
        cases value with
        | collection boundKind bound boundRest =>
          cases boundRest with
          | none =>
            by_cases sameKind : boundKind = kind
            · subst sameKind
              simp only [beq_self_eq_true, ↓reduceIte, Pattern.isWellScopedAt,
                Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff, List.mem_append] at valueScoped ⊢
              rintro element (inside | inside)
              · exact mapped element inside
              · exact valueScoped element inside
            · simpa [found, sameKind, Pattern.isWellScopedAt,
                Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff] using mapped
          | some _ =>
            simpa [found, Pattern.isWellScopedAt, Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff]
              using mapped
        | _ =>
          simpa [found, Pattern.isWellScopedAt, Mettapedia.OSLF.MeTTaIL.ScopedPattern.isWellScopedListAt_eq_true_iff]
            using mapped

/-- **Every object state that steps to the target is one a symbolic predecessor stands for**, when every
rule runs backward. -/
theorem predecessors_complete {language : LanguageDef}
    (backward : ∀ rule ∈ language.rewrites, ruleBackward rule = true) {state target : Pattern}
    (object : ObjectState state) (step : target ∈ rootReducts language state) :
    ∃ family ∈ predecessors language target, family.Matches state := by
  obtain ⟨rule, ruleMember, matched, matchedMember, rfl⟩ := mem_rootReducts.mp step
  have checked := backward rule ruleMember
  simp only [ruleBackward, Bool.and_eq_true] at checked
  obtain ⟨⟨leftScoped, leftFree⟩, covered⟩ := checked
  have relation := matchPattern_sound matchedMember
  have leftBound : RestsBound matched rule.left := restsBound_of_matchRel relation matched fun _ _ found => found
  have rightBound : RestsBound matched rule.right := fun entry inside => leftBound entry (by
    simp only [restsCovered, List.all_eq_true, decide_eq_true_eq] at covered
    exact covered entry inside)
  obtain ⟨fixed, fixedMember, valued⟩ := matchBack_complete rule.right matched rightBound
  refine ⟨⟨rule, fixed⟩, mem_predecessors.mpr ⟨ruleMember, backward rule ruleMember, fixedMember, ?_⟩,
    matched, matchedMember, agrees_of_valued valued⟩
  refine scoped_applyBindings fixed rule.left leftFree 0 leftScoped fun entry inside value found => ?_
  obtain ⟨bound, boundFound, boundScoped⟩ :=
    scoped_of_matchRel relation matched (fun _ _ found => found) 0 object.1 entry inside
  have read := agrees_of_valued valued entry.1 value found
  rw [bound_of_find boundFound] at read
  rw [← read]
  exact boundScoped

/-! ## Symbolic predecessors as patterns -/

mutual
/-- **A backward match fixes only metavariables of the right side.** -/
theorem keys_of_matchBack : ∀ (pattern target : Pattern) (fixed : Bindings), fixed ∈ matchBack pattern target →
    ∀ entry ∈ fixed, entry.1 ∈ freeVars pattern ∨ entry.1 ∈ (restVars pattern).map Prod.fst
  | .fvar name, target, fixed, member, entry, inside => by
    simp only [matchBack, List.mem_singleton] at member
    subst member
    simp only [List.mem_singleton] at inside
    subst inside
    left
    rw [freeVars]
    simp
  | .bvar index, target, fixed, member, entry, inside => by
    simp only [matchBack] at member
    split at member <;> simp_all
  | .apply label arguments, target, fixed, member, entry, inside => by
    cases target with
    | apply label' targets =>
      simp only [matchBack] at member
      split at member
      · rcases keysList_of_matchBackList arguments targets fixed member entry inside with free | rest
        · left
          rw [freeVars_apply]
          exact free
        · right
          simpa [restVars, restVarsList_eq] using rest
      · simp at member
    | _ => simp [matchBack] at member
  | .lambda name body, target, fixed, member, entry, inside => by
    cases target with
    | lambda name' inner =>
      simp only [matchBack] at member
      split at member
      · rcases keys_of_matchBack body inner fixed member entry inside with free | rest
        · left; rw [freeVars]; exact free
        · right; simpa [restVars] using rest
      · simp at member
    | _ => simp [matchBack] at member
  | .multiLambda arity names body, target, fixed, member, entry, inside => by
    cases target with
    | multiLambda arity' names' inner =>
      simp only [matchBack] at member
      split at member
      · rcases keys_of_matchBack body inner fixed member entry inside with free | rest
        · left; rw [freeVars]; exact free
        · right; simpa [restVars] using rest
      · simp at member
    | _ => simp [matchBack] at member
  | .subst body argument, target, fixed, member, entry, inside => by
    simp only [matchBack, List.mem_append, List.mem_flatMap, List.mem_filter, List.mem_filterMap] at member
    rcases member with ⟨value, _, first, firstMember, abstracted, _, second, secondMember, merge⟩ |
        ⟨abstracted, _, fixedMember⟩
    · rcases mem_of_mergeBindings merge entry inside with inFirst | inSecond
      · rcases keys_of_matchBack argument value first firstMember entry inFirst with free | rest
        · left; rw [freeVars]; exact List.mem_append_right _ free
        · right; simp only [restVars, List.map_append, List.mem_append]; exact Or.inr rest
      · rcases keys_of_matchBack body abstracted second secondMember entry inSecond with free | rest
        · left; rw [freeVars]; exact List.mem_append_left _ free
        · right; simp only [restVars, List.map_append, List.mem_append]; exact Or.inl rest
    · rcases keys_of_matchBack body abstracted fixed fixedMember entry inside with free | rest
      · left; rw [freeVars]; exact List.mem_append_left _ free
      · right; simp only [restVars, List.map_append, List.mem_append]; exact Or.inl rest
  | .collection kind elements rest, target, fixed, member, entry, inside => by
    cases target with
    | collection kind' targets targetRest =>
      cases targetRest with
      | some _ => simp [matchBack] at member
      | none =>
        simp only [matchBack] at member
        split at member
        · cases rest with
          | none =>
            rcases keysList_of_matchBackList elements targets fixed member entry inside with free | restKey
            · left; rw [freeVars]; exact free
            · right; simpa [restVars, restVarsList_eq] using restKey
          | some name =>
            simp only at member
            split at member
            · obtain ⟨prefixFixed, prefixMember, merge⟩ := List.mem_filterMap.mp member
              rcases mem_of_mergeBindings merge entry inside with inPrefix | isRest
              · rcases keysList_of_matchBackList elements _ prefixFixed prefixMember entry inPrefix with free | restKey
                · left; rw [freeVars]; exact free
                · right; simp only [restVars, restVarsList_eq, List.map_append, List.mem_append]; exact Or.inl restKey
              · simp only [List.mem_singleton] at isRest
                subst isRest
                right
                simp [restVars]
            · simp at member
        · simp at member
    | _ => simp [matchBack] at member

theorem keysList_of_matchBackList : ∀ (patterns targets : List Pattern) (fixed : Bindings),
    fixed ∈ matchBackList patterns targets →
    ∀ entry ∈ fixed, entry.1 ∈ patterns.flatMap freeVars ∨ entry.1 ∈ (patterns.flatMap restVars).map Prod.fst
  | [], [], fixed, member, entry, inside => by simp_all [matchBackList]
  | pattern :: patterns, target :: targets, fixed, member, entry, inside => by
    simp only [matchBackList, List.mem_flatMap, List.mem_filterMap] at member
    obtain ⟨first, firstMember, rest, restMember, merge⟩ := member
    rcases mem_of_mergeBindings merge entry inside with inFirst | inRest
    · rcases keys_of_matchBack pattern target first firstMember entry inFirst with free | restKey
      · left; simp only [List.flatMap_cons, List.mem_append]; exact Or.inl free
      · right; simp only [List.flatMap_cons, List.map_append, List.mem_append]; exact Or.inl restKey
    · rcases keysList_of_matchBackList patterns targets rest restMember entry inRest with free | restKey
      · left; simp only [List.flatMap_cons, List.mem_append]; exact Or.inr free
      · right; simp only [List.flatMap_cons, List.map_append, List.mem_append]; exact Or.inr restKey
  | [], _ :: _, _, member, _, _ => by simp [matchBackList] at member
  | _ :: _, [], _, member, _, _ => by simp [matchBackList] at member
end

/-- A rule whose predecessors are exactly the instances of patterns: its left side uses no explicit
substitution, collection or binder display name, and its right side only the left side's
metavariables. -/
def literalRule (rule : RewriteRule) : Bool :=
  leftShape rule.left && nameless rule.left && (freeVars rule.right).all (· ∈ freeVars rule.left)

/-- The instances of a symbolic predecessor: the left side under bindings that agree with the fixed
values. -/
def Family.Instance (family : Family) (state : Pattern) : Prop :=
  ∃ bindings, Agrees family.fixed bindings ∧ applyBindings bindings family.rule.left = state

theorem restVars_of_leftShape (pattern : Pattern) (shape : leftShape pattern = true) : restVars pattern = [] := by
  induction pattern using Pattern.inductionOn with
  | hbvar _ => rfl
  | hfvar _ => rfl
  | happly label arguments ih =>
    simp only [leftShape, leftShapeList_eq, List.all_eq_true] at shape
    simp only [restVars, restVarsList_eq, List.flatMap_eq_nil_iff]
    exact fun argument member => ih argument member (shape argument member)
  | hlambda _ body ih => exact ih (by simpa [leftShape] using shape)
  | hmultiLambda _ _ body ih => exact ih (by simpa [leftShape] using shape)
  | hsubst _ _ _ _ => simp [leftShape] at shape
  | hcollection _ _ _ _ => simp [leftShape] at shape

/-- **A nameless state a literal family stands for is an instance of its pattern.** -/
theorem instance_of_matches {family : Family} (literal : literalRule family.rule = true) {state : Pattern}
    (stateNameless : nameless state = true) (matches_ : family.Matches state) : family.Instance state := by
  simp only [literalRule, Bool.and_eq_true] at literal
  obtain ⟨⟨shape, ruleNameless⟩, _⟩ := literal
  obtain ⟨bindings, matched, agrees⟩ := matches_
  exact ⟨bindings, agrees, applyBindings_of_matchRel _ _ _ (matchPattern_sound matched) shape ruleNameless
    stateNameless bindings fun _ _ found => found⟩

/-- **Every instance of a literal symbolic predecessor is a state it stands for.** -/
theorem matches_of_instance {language : LanguageDef} {target : Pattern} {family : Family}
    (member : family ∈ predecessors language target) (literal : literalRule family.rule = true) {state : Pattern}
    (instance_ : family.Instance state) : family.Matches state := by
  obtain ⟨_, backward, fixedMember, _⟩ := mem_predecessors.mp member
  simp only [literalRule, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at literal
  obtain ⟨⟨shape, _⟩, covered⟩ := literal
  have noRests : restVars family.rule.right = [] := by
    simp only [ruleBackward, restsCovered, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at backward
    rw [restVars_of_leftShape _ shape] at backward
    exact List.eq_nil_iff_forall_not_mem.mpr fun entry inside => by simpa using backward.2 entry inside
  obtain ⟨bindings, agrees, rfl⟩ := instance_
  obtain ⟨matched, relation, valued, covers⟩ := exists_matchRel family.rule.left shape bindings
  refine ⟨matched, matchRel_complete relation, fun name value found => ?_⟩
  have key := keys_of_matchBack _ _ _ fixedMember (name, value) (List.mem_of_find?_eq_some found)
  rw [noRests] at key
  have free : name ∈ freeVars family.rule.left := covered name (by simpa using key)
  obtain ⟨matchedValue, matchedFound⟩ := covers name free
  rw [bound_of_find matchedFound, valued name matchedValue (List.mem_of_find?_eq_some matchedFound)]
  exact agrees name value found

/-! ## The past box of a model's native type -/

section PastBox

open Mettapedia.OSLF.Framework.FiniteModels (FiniteModel Valuation Table eval stateValuation tableValuation tables
  firstDepths value bindingValuation exists_table firstDepths_keys eval_congr eval_of_matchPattern LeftCommutes)

variable {A : Type} [DecidableEq A] (model : FiniteModel A) (elements : List A)

/-- The valuation of a family's instances: a fixed metavariable reads the value of its fixed pattern,
any other reads a table. -/
def familyValuation (family : Family) (table : Table A) : Valuation A := fun name env =>
  match family.fixed.find? (·.1 == name) with
  | some (_, fixedValue) => eval model (stateValuation model) env fixedValue
  | none => tableValuation model elements table name env

/-- Every state a family stands for is accepted: its left side, under every table for the
metavariables that are not fixed. -/
def familyCheck (accept : A → Bool) (family : Family) : Bool :=
  (occurrences 0 family.rule.left).all (· ∈ firstDepths (occurrences 0 family.rule.left)) &&
    (tables elements (firstDepths (occurrences 0 family.rule.left))).all fun table =>
      accept (eval model (familyValuation model elements family table) [] family.rule.left)

/-- The join of every unordered collection kind is left-commutative on the elements. -/
def joinCommutes : Bool :=
  [CollType.hashBag, CollType.hashSet].all fun kind =>
    elements.all fun first => elements.all fun second => elements.all fun rest =>
      model.collectionJoin kind first (model.collectionJoin kind second rest) ==
        model.collectionJoin kind second (model.collectionJoin kind first rest)

/-- **The past box at a state**: every unordered collection join commutes, and every symbolic predecessor
is accepted. -/
def pastBoxCheck (language : LanguageDef) (accept : A → Bool) (target : Pattern) : Bool :=
  joinCommutes model elements && (predecessors language target).all (familyCheck model elements accept)

variable {model elements}

theorem leftCommutes_of_check (complete : ∀ entry : A, entry ∈ elements) (checked : joinCommutes model elements = true) :
    LeftCommutes model := fun kind notVec first second rest => by
  simp only [joinCommutes, List.all_eq_true, beq_iff_eq] at checked
  have unordered : kind ∈ [CollType.hashBag, CollType.hashSet] := by cases kind <;> simp_all
  exact checked kind unordered first (complete first) second (complete second) rest (complete rest)

/-- **Every object state a checked family stands for is accepted.** -/
theorem familyCheck_sound (complete : ∀ entry : A, entry ∈ elements) (comm : LeftCommutes model) {accept : A → Bool}
    {family : Family} (checked : familyCheck model elements accept family = true) {state : Pattern}
    (object : Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPattern state = true) (matches_ : family.Matches state) :
    accept (value model state) = true := by
  simp only [familyCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at checked
  obtain ⟨sameDepths, tablesChecked⟩ := checked
  obtain ⟨bindings, matched, agrees⟩ := matches_
  have bound := restsBound_of_matchRel (matchPattern_sound matched) bindings fun _ _ found => found
  obtain ⟨table, tableMember, realizes⟩ := exists_table model elements complete (bindingValuation model bindings) _
    (firstDepths_keys _)
  unfold value
  rw [← eval_of_matchPattern model comm matched object bound [],
    eval_congr model (second := familyValuation model elements family table) _ [] fun entry inside inner length => ?_]
  · exact tablesChecked table tableMember
  · simp only [familyValuation]
    cases fixedFound : family.fixed.find? (·.1 == entry.1) with
    | some pair =>
      obtain ⟨key, fixedValue⟩ := pair
      have same : key = entry.1 := by simpa using List.find?_some fixedFound
      subst same
      have read := agrees entry.1 fixedValue fixedFound
      simp only [bindingValuation]
      cases boundFound : bindings.find? (·.1 == entry.1) with
      | some boundPair =>
        obtain ⟨_, boundValue⟩ := boundPair
        simp only [lookupOrFvar, applyBindings, boundFound] at read
        rw [read]
      | none =>
        simp only [lookupOrFvar, applyBindings, boundFound] at read
        rw [← read]
        rfl
    | none =>
      simp only
      rw [realizes entry (sameDepths entry inside) inner (by omega), List.take_of_length_le (by omega)]

/-- **The past box of a model's native type at a state**: when the check passes, every object state
stepping to the target in one step has an accepted value. -/
theorem pastBox_of_check (complete : ∀ entry : A, entry ∈ elements) {language : LanguageDef} {accept : A → Bool}
    {target : Pattern} (backward : ∀ rule ∈ language.rewrites, ruleBackward rule = true)
    (checked : pastBoxCheck model elements language accept target = true) {state : Pattern}
    (object : ObjectState state) (step : target ∈ rootReducts language state) : accept (value model state) = true := by
  simp only [pastBoxCheck, Bool.and_eq_true] at checked
  obtain ⟨family, member, matches_⟩ := predecessors_complete backward object step
  exact familyCheck_sound complete (leftCommutes_of_check complete checked.1)
    (List.all_eq_true.mp checked.2 family member) object.2 matches_

end PastBox

end Mettapedia.OSLF.Framework.BackwardBinders
