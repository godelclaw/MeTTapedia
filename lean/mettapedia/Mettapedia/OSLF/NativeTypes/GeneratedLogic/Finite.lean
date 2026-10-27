import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Invariance
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Generated

/-!
# Deciding generated formulas on a finite structure

A finite structure lists its carrier and decides each of its relations (`FiniteStructure`). Every
generated formula is then decided by evaluation (`FiniteStructure.eval`):
- the modal, singleton, body and quantifier formers enumerate the listed carrier;
- the constructor formers enumerate the argument lists of the right length (`Listed.lists`);
- a least fixed point iterates from the empty predicate, a greatest one from the full predicate
  (`Listed.up`, `Listed.down`).

A monotone operator on the predicates over a listed carrier stabilizes within as many rounds as the
carrier has entries, since each round that changes the predicate changes how many entries it holds at
(`Listed.up_stable`, `Listed.down_stable`). So the iterations reach the least and greatest fixed points.

**Exactness** (`FiniteStructure.eval_iff`, `FiniteStructure.check_iff`): evaluation is satisfaction in
the structure. Evaluation is structural recursion over finite lists, so the kernel decides the verdicts
of a concrete finite structure.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Formula

universe u

/-! ## Predicates over a listed carrier -/

namespace Listed

variable {Carrier : Type u} (elements : List Carrier)

/-- All lists of a length over the listed carrier. -/
def lists : ℕ → List (List Carrier)
  | 0 => [[]]
  | length + 1 => elements.flatMap fun first => (lists length).map (first :: ·)

theorem mem_lists (complete : ∀ element, element ∈ elements) :
    ∀ {length : ℕ} {list : List Carrier}, list ∈ lists elements length ↔ list.length = length
  | 0, list => by cases list <;> simp [lists]
  | _ + 1, [] => by simp [lists]
  | length + 1, first :: rest => by
    simp [lists, mem_lists complete (length := length), complete first]

/-- One predicate holds wherever another does. -/
def Le (smaller larger : Carrier → Bool) : Prop := ∀ element, smaller element = true → larger element = true

/-- How many listed entries a predicate holds at. -/
def count (predicate : Carrier → Bool) : ℕ := elements.countP predicate

theorem count_le (predicate : Carrier → Bool) : count elements predicate ≤ elements.length :=
  List.countP_le_length

theorem count_lt {smaller larger : Carrier → Bool} (le : Le smaller larger) {element : Carrier}
    (member : element ∈ elements) (outside : smaller element = false) (inside : larger element = true) :
    count elements smaller < count elements larger := by
  unfold count
  induction elements with
  | nil => cases member
  | cons first rest previous =>
    have mono : rest.countP smaller ≤ rest.countP larger :=
      List.countP_mono_left fun entry _ holds => le entry holds
    rw [List.countP_cons, List.countP_cons]
    rcases List.mem_cons.mp member with rfl | member
    · rw [if_neg (by simp [outside]), if_pos inside]
      omega
    · have below := previous member
      by_cases smallerHolds : smaller first = true
      · rw [if_pos smallerHolds, if_pos (le first smallerHolds)]
        omega
      · rw [if_neg smallerHolds]
        split <;> omega

variable {elements}

/-- Iterate an operator from the empty predicate. -/
def up (operator : (Carrier → Bool) → Carrier → Bool) : ℕ → Carrier → Bool
  | 0 => fun _ => false
  | rounds + 1 => operator (up operator rounds)

/-- Iterate an operator from the full predicate. -/
def down (operator : (Carrier → Bool) → Carrier → Bool) : ℕ → Carrier → Bool
  | 0 => fun _ => true
  | rounds + 1 => operator (down operator rounds)

section Monotone

variable {operator : (Carrier → Bool) → Carrier → Bool}
  (mono : ∀ smaller larger, Le smaller larger → Le (operator smaller) (operator larger))
include mono

theorem up_le_succ : ∀ rounds, Le (up operator rounds) (up operator (rounds + 1))
  | 0 => fun _ holds => by simp [up] at holds
  | rounds + 1 => mono _ _ (up_le_succ rounds)

theorem down_succ_le : ∀ rounds, Le (down operator (rounds + 1)) (down operator rounds)
  | 0 => fun _ _ => rfl
  | rounds + 1 => mono _ _ (down_succ_le rounds)

theorem up_stable_or_grows (complete : ∀ element, element ∈ elements) : ∀ rounds,
    up operator (rounds + 1) = up operator rounds ∨ rounds + 1 ≤ count elements (up operator (rounds + 1)) := by
  intro rounds
  induction rounds with
  | zero =>
    by_cases same : up operator 1 = up operator 0
    · exact Or.inl same
    · obtain ⟨element, differs⟩ := Function.ne_iff.mp same
      have values : up operator 0 element = false ∧ up operator 1 element = true := by
        have le := up_le_succ mono 0 element
        cases first : up operator 0 element <;> cases second : up operator 1 element <;> simp_all
      have grows := count_lt elements (up_le_succ mono 0) (complete element) values.1 values.2
      right
      omega
  | succ rounds previous =>
    by_cases same : up operator (rounds + 2) = up operator (rounds + 1)
    · exact Or.inl same
    · rcases previous with stable | grown
      · exact absurd (by simp only [up] at stable ⊢; rw [stable]; exact stable) same
      · obtain ⟨element, differs⟩ := Function.ne_iff.mp same
        have values : up operator (rounds + 1) element = false ∧ up operator (rounds + 2) element = true := by
          have le := up_le_succ mono (rounds + 1) element
          cases first : up operator (rounds + 1) element <;> cases second : up operator (rounds + 2) element <;>
            simp_all
        have grows := count_lt elements (up_le_succ mono (rounds + 1)) (complete element) values.1 values.2
        right
        omega

theorem down_stable_or_shrinks (complete : ∀ element, element ∈ elements) : ∀ rounds,
    down operator (rounds + 1) = down operator rounds ∨
      count elements (down operator (rounds + 1)) + (rounds + 1) ≤ elements.length := by
  intro rounds
  induction rounds with
  | zero =>
    by_cases same : down operator 1 = down operator 0
    · exact Or.inl same
    · obtain ⟨element, differs⟩ := Function.ne_iff.mp same
      have values : down operator 1 element = false ∧ down operator 0 element = true := by
        have le := down_succ_le mono 0 element
        cases first : down operator 0 element <;> cases second : down operator 1 element <;> simp_all
      have shrinks := count_lt elements (down_succ_le mono 0) (complete element) values.1 values.2
      have full := count_le elements (down operator 0)
      right
      omega
  | succ rounds previous =>
    by_cases same : down operator (rounds + 2) = down operator (rounds + 1)
    · exact Or.inl same
    · rcases previous with stable | shrunk
      · exact absurd (by simp only [down] at stable ⊢; rw [stable]; exact stable) same
      · obtain ⟨element, differs⟩ := Function.ne_iff.mp same
        have values : down operator (rounds + 2) element = false ∧ down operator (rounds + 1) element = true := by
          have le := down_succ_le mono (rounds + 1) element
          cases first : down operator (rounds + 1) element <;> cases second : down operator (rounds + 2) element <;>
            simp_all
        have shrinks := count_lt elements (down_succ_le mono (rounds + 1)) (complete element) values.1 values.2
        right
        omega

/-- **The upward iteration stabilizes** within as many rounds as the carrier has entries. -/
theorem up_stable (complete : ∀ element, element ∈ elements) :
    operator (up operator elements.length) = up operator elements.length := by
  rcases up_stable_or_grows mono complete elements.length with stable | grown
  · exact stable
  · have := count_le elements (up operator (elements.length + 1))
    omega

/-- **The downward iteration stabilizes** within as many rounds as the carrier has entries. -/
theorem down_stable (complete : ∀ element, element ∈ elements) :
    operator (down operator elements.length) = down operator elements.length := by
  rcases down_stable_or_shrinks mono complete elements.length with stable | shrunk
  · exact stable
  · rcases elements.length.eq_zero_or_pos with empty | positive
    · obtain ⟨⟩ : elements = [] := List.length_eq_zero_iff.mp empty
      funext element
      exact absurd (complete element) (List.not_mem_nil)
    · omega

end Monotone

/-- The upward iteration stays inside every set the operator keeps inside. -/
theorem up_inside {operator : (Carrier → Bool) → Carrier → Bool} {closed : Set Carrier}
    (keeps : ∀ predicate : Carrier → Bool, (∀ element, predicate element = true → element ∈ closed) →
      ∀ element, operator predicate element = true → element ∈ closed) :
    ∀ rounds element, up operator rounds element = true → element ∈ closed
  | 0, _, holds => by simp [up] at holds
  | rounds + 1, element, holds => keeps _ (up_inside keeps rounds) element holds

/-- The downward iteration contains every set the operator keeps. -/
theorem down_contains {operator : (Carrier → Bool) → Carrier → Bool} {invariant : Set Carrier}
    (keeps : ∀ predicate : Carrier → Bool, (∀ element ∈ invariant, predicate element = true) →
      ∀ element ∈ invariant, operator predicate element = true) :
    ∀ rounds, ∀ element ∈ invariant, down operator rounds element = true
  | 0, _, _ => rfl
  | rounds + 1, element, member => keeps _ (down_contains keeps rounds) element member

end Listed

/-! ## Finite structures -/

/-- **A finite structure**: a listed carrier with every relation decided. -/
structure FiniteStructure (Carrier : Type u) where
  elements : List Carrier
  complete : ∀ element, element ∈ elements
  step : Carrier → StepLabel → Carrier → Bool
  built : Carrier → String → List Carrier → Bool
  split : Carrier → CollType → Carrier → Carrier → Bool
  empty : Carrier → CollType → Bool
  single : Carrier → CollType → Carrier → Bool
  body : Carrier → Carrier → Bool
  multiBody : Carrier → ℕ → Carrier → Bool
  bound : Carrier → ℕ → Bool
  typed : Carrier → TypeExpr → Bool
  named : Carrier → Pattern → Bool
  same : Carrier → Carrier → Bool
  apply : Carrier → Carrier → Carrier
  inRelation : Carrier → String → Bool

namespace FiniteStructure

variable {Carrier : Type u} (F : FiniteStructure Carrier)

/-- The native structure a finite structure decides. -/
def native : NativeStructure Carrier where
  step source label target := F.step source label target = true
  built element constructor parts := F.built element constructor parts = true
  split element kind first second := F.split element kind first second = true
  empty element kind := F.empty element kind = true
  single element kind member := F.single element kind member = true
  body element inner := F.body element inner = true
  multiBody element arity inner := F.multiBody element arity inner = true
  bound element index := F.bound element index = true
  typed element type := F.typed element type = true
  named element term := F.named element term = true
  same first second := F.same first second = true
  apply := F.apply
  inRelation element relation := F.inRelation element relation = true

/-- A decided step in the direction. -/
def stepIn (direction : Direction) (element : Carrier) (label : StepLabel) (other : Carrier) : Bool :=
  match direction with
  | .forward => F.step element label other
  | .backward => F.step other label element

theorem stepIn_iff (direction : Direction) (element : Carrier) (label : StepLabel) (other : Carrier) :
    F.stepIn direction element label other = true ↔ F.native.stepIn direction element label other := by
  cases direction <;> rfl

/-- **At least `count` distinct listed elements satisfy the predicate**, decided by trying every list of
that length. -/
def atLeastCheck (count : ℕ) (holds : Carrier → Bool) : Bool :=
  (Listed.lists F.elements count).any fun witnesses =>
    decide (witnesses.Pairwise fun first second => F.same first second = false) && witnesses.all holds

theorem atLeastCheck_iff (count : ℕ) (holds : Carrier → Bool) :
    F.atLeastCheck count holds = true ↔ F.native.AtLeast count fun element => holds element = true := by
  simp only [atLeastCheck, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Listed.mem_lists F.elements F.complete, NativeStructure.AtLeast, native, Bool.not_eq_true]

mutual
/-- **Evaluate a formula** at an element, in an environment of predicates for its fixed-point
variables. -/
def eval : {n : ℕ} → (Fin n → Carrier → Bool) → Formula n → Carrier → Bool
  | _, _, .top, _ => true
  | _, _, .bot, _ => false
  | _, env, .and left right, element => eval env left element && eval env right element
  | _, env, .or left right, element => eval env left element || eval env right element
  | _, env, .var index, element => env index element
  | _, env, .mu inner, element => Listed.up (fun set => eval (Fin.cons set env) inner) F.elements.length element
  | _, env, .nu inner, element => Listed.down (fun set => eval (Fin.cons set env) inner) F.elements.length element
  | _, env, .possibly label formula, element =>
      F.elements.any fun next => F.step element label next && eval env formula next
  | _, env, .necessarily label formula, element =>
      F.elements.all fun next => !F.step element label next || eval env formula next
  | _, env, .sometimeBefore label formula, element =>
      F.elements.any fun previous => F.step previous label element && eval env formula previous
  | _, env, .alwaysBefore label formula, element =>
      F.elements.all fun previous => !F.step previous label element || eval env formula previous
  | _, env, .atLeast count direction label formula, element =>
      F.atLeastCheck count fun other => F.stepIn direction element label other && eval env formula other
  | _, env, .allButFewer count direction label formula, element =>
      !F.atLeastCheck count fun other => F.stepIn direction element label other && !eval env formula other
  | _, env, .built constructor arguments, element =>
      (Listed.lists F.elements arguments.length).any fun parts =>
        F.built element constructor parts && evalAll env arguments parts
  | _, env, .everyBuilt constructor arguments, element =>
      (Listed.lists F.elements arguments.length).all fun parts =>
        !F.built element constructor parts || evalSome env arguments parts
  | _, env, .split kind left right, element =>
      F.elements.any fun first => F.elements.any fun second =>
        F.split element kind first second && eval env left first && eval env right second
  | _, env, .everySplit kind left right, element =>
      F.elements.all fun first => F.elements.all fun second =>
        !F.split element kind first second || eval env left first || eval env right second
  | _, _, .empty kind, element => F.empty element kind
  | _, _, .nonEmpty kind, element => !F.empty element kind
  | _, env, .single kind formula, element =>
      F.elements.any fun member => F.single element kind member && eval env formula member
  | _, env, .everySingle kind formula, element =>
      F.elements.all fun member => !F.single element kind member || eval env formula member
  | _, env, .body formula, element => F.elements.any fun inner => F.body element inner && eval env formula inner
  | _, env, .everyBody formula, element =>
      F.elements.all fun inner => !F.body element inner || eval env formula inner
  | _, env, .multiBody arity formula, element =>
      F.elements.any fun inner => F.multiBody element arity inner && eval env formula inner
  | _, env, .everyMultiBody arity formula, element =>
      F.elements.all fun inner => !F.multiBody element arity inner || eval env formula inner
  | _, _, .bound index, element => F.bound element index
  | _, _, .notBound index, element => !F.bound element index
  | _, _, .typed type, element => F.typed element type
  | _, _, .untyped type, element => !F.typed element type
  | _, _, .is term, element => F.named element term
  | _, _, .isNot term, element => !F.named element term
  | _, _, .inRelation relation, element => F.inRelation element relation
  | _, _, .notInRelation relation, element => !F.inRelation element relation
  | _, env, .mapsAll argument result, element =>
      F.elements.any fun inner => F.body element inner &&
        F.elements.all fun value => eval env argument value || eval env result (F.apply inner value)
  | _, env, .mapsSome argument result, element =>
      F.elements.all fun inner => !F.body element inner ||
        F.elements.any fun value => eval env argument value && eval env result (F.apply inner value)
  | _, env, .someOf type formula, _ => F.elements.any fun witness => F.typed witness type && eval env formula witness
  | _, env, .everyOf type formula, _ =>
      F.elements.all fun witness => !F.typed witness type || eval env formula witness

/-- Every formula of the list holds at the corresponding part, and the lengths agree. -/
def evalAll : {n : ℕ} → (Fin n → Carrier → Bool) → Formulas n → List Carrier → Bool
  | _, _, .nil, [] => true
  | _, env, .cons formula formulas, part :: parts => eval env formula part && evalAll env formulas parts
  | _, _, _, _ => false

/-- Some formula of the list holds at the corresponding part, or the lengths differ. -/
def evalSome : {n : ℕ} → (Fin n → Carrier → Bool) → Formulas n → List Carrier → Bool
  | _, _, .nil, [] => false
  | _, env, .cons formula formulas, part :: parts => eval env formula part || evalSome env formulas parts
  | _, _, _, _ => true
end

/-- The sets an environment of predicates denotes. -/
def sets {n : ℕ} (env : Fin n → Carrier → Bool) : Env Carrier n := fun index => {element | env index element = true}

theorem sets_cons {n : ℕ} (env : Fin n → Carrier → Bool) (set : Carrier → Bool) :
    sets (Fin.cons set env : Fin (n + 1) → Carrier → Bool) = (sets env).extend {element | set element = true} := by
  funext index
  refine Fin.cases ?_ (fun _ => ?_) index <;> rfl

end FiniteStructure

namespace NativeStructure

variable {Carrier : Type u} (S : NativeStructure Carrier)

theorem satAll_length : ∀ {n : ℕ} {env : Env Carrier n} (formulas : Formulas n) {parts : List Carrier},
    S.satAll env formulas parts → parts.length = formulas.length
  | _, _, .nil, [], _ => rfl
  | _, _, .cons _ formulas, _ :: _, holds => by
    simp only [List.length_cons, Formulas.length, satAll_length formulas holds.2]
  | _, _, .nil, _ :: _, holds => holds.elim
  | _, _, .cons _ _, [], holds => holds.elim

theorem satSome_of_length_ne : ∀ {n : ℕ} {env : Env Carrier n} (formulas : Formulas n) {parts : List Carrier},
    parts.length ≠ formulas.length → S.satSome env formulas parts
  | _, _, .nil, [], differs => absurd rfl differs
  | _, _, .cons _ formulas, _ :: _, differs => by
    refine Or.inr (satSome_of_length_ne formulas ?_)
    simpa [Formulas.length] using differs
  | _, _, .nil, _ :: _, _ => trivial
  | _, _, .cons _ _, [], _ => trivial

end NativeStructure

namespace FiniteStructure

variable {Carrier : Type u} (F : FiniteStructure Carrier)

mutual
/-- **Evaluation is satisfaction.** -/
theorem eval_iff : ∀ {n : ℕ} (formula : Formula n) (env : Fin n → Carrier → Bool) (element : Carrier),
    F.eval env formula element = true ↔ F.native.sat (sets env) formula element
  | _, .top, _, _ => by simp [eval, NativeStructure.sat]
  | _, .bot, _, _ => by simp [eval, NativeStructure.sat]
  | _, .and left right, env, element => by
    simp only [eval, Bool.and_eq_true, NativeStructure.sat, eval_iff left env element, eval_iff right env element]
  | _, .or left right, env, element => by
    simp only [eval, Bool.or_eq_true, NativeStructure.sat, eval_iff left env element, eval_iff right env element]
  | _, .var index, env, element => by simp [eval, NativeStructure.sat, sets]
  | _, .mu inner, env, element => by
    have unfold : ∀ (set : Carrier → Bool) (other : Carrier),
        F.eval (Fin.cons set env) inner other = true ↔
          F.native.sat ((sets env).extend {member | set member = true}) inner other := by
      intro set other
      rw [eval_iff inner, sets_cons]
    have mono : ∀ smaller larger, Listed.Le smaller larger →
        Listed.Le (fun other => F.eval (Fin.cons smaller env) inner other)
          (fun other => F.eval (Fin.cons larger env) inner other) := by
      intro smaller larger le other holds
      rw [unfold] at holds ⊢
      exact F.native.sat_mono inner ((sets env).extend_sub fun member inside => le member inside) other holds
    simp only [eval, NativeStructure.sat]
    constructor
    · intro holds closed isClosed
      refine Listed.up_inside (fun predicate inside other otherHolds => isClosed other ?_) _ element holds
      have := (unfold predicate other).mp otherHolds
      exact F.native.sat_mono inner ((sets env).extend_sub fun member member' => inside member member') other
        this
    · intro least
      apply least {member | Listed.up (fun set => F.eval (Fin.cons set env) inner) F.elements.length member = true}
      intro other otherHolds
      have stable := congrFun (Listed.up_stable mono F.complete) other
      exact stable.symm.trans ((unfold _ other).mpr otherHolds)
  | _, .nu inner, env, element => by
    have unfold : ∀ (set : Carrier → Bool) (other : Carrier),
        F.eval (Fin.cons set env) inner other = true ↔
          F.native.sat ((sets env).extend {member | set member = true}) inner other := by
      intro set other
      rw [eval_iff inner, sets_cons]
    have mono : ∀ smaller larger, Listed.Le smaller larger →
        Listed.Le (fun other => F.eval (Fin.cons smaller env) inner other)
          (fun other => F.eval (Fin.cons larger env) inner other) := by
      intro smaller larger le other holds
      rw [unfold] at holds ⊢
      exact F.native.sat_mono inner ((sets env).extend_sub fun member inside => le member inside) other holds
    simp only [eval, NativeStructure.sat]
    constructor
    · intro holds
      refine ⟨{member | Listed.down (fun set => F.eval (Fin.cons set env) inner) F.elements.length member = true},
        holds, fun other otherMember => ?_⟩
      have stable := congrFun (Listed.down_stable mono F.complete) other
      exact (unfold _ other).mp (stable.trans otherMember)
    · rintro ⟨invariant, member, preserved⟩
      refine Listed.down_contains (fun predicate inside other otherMember => ?_) _ element member
      apply (unfold predicate other).mpr
      exact F.native.sat_mono inner ((sets env).extend_sub fun entry entryMember => inside entry entryMember)
        other (preserved other otherMember)
  | _, .possibly _ formula, env, element => by
    simp only [eval, List.any_eq_true, Bool.and_eq_true, NativeStructure.sat, native, eval_iff formula]
    exact ⟨fun ⟨next, _, step, holds⟩ => ⟨next, step, holds⟩,
      fun ⟨next, step, holds⟩ => ⟨next, F.complete next, step, holds⟩⟩
  | _, .necessarily label formula, env, element => by
    simp only [eval, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', NativeStructure.sat, native,
      eval_iff formula]
    constructor
    · intro every next step
      exact (every next (F.complete next)).resolve_left (by rw [step]; decide)
    · intro every next _
      by_cases step : F.step element label next = true
      · exact Or.inr (every next step)
      · exact Or.inl (by simpa using step)
  | _, .sometimeBefore _ formula, env, element => by
    simp only [eval, List.any_eq_true, Bool.and_eq_true, NativeStructure.sat, native, eval_iff formula]
    exact ⟨fun ⟨previous, _, step, holds⟩ => ⟨previous, step, holds⟩,
      fun ⟨previous, step, holds⟩ => ⟨previous, F.complete previous, step, holds⟩⟩
  | _, .alwaysBefore label formula, env, element => by
    simp only [eval, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', NativeStructure.sat, native,
      eval_iff formula]
    constructor
    · intro every previous step
      exact (every previous (F.complete previous)).resolve_left (by rw [step]; decide)
    · intro every previous _
      by_cases step : F.step previous label element = true
      · exact Or.inr (every previous step)
      · exact Or.inl (by simpa using step)
  | _, .atLeast count direction label formula, env, element => by
    simp only [eval, NativeStructure.sat]
    rw [atLeastCheck_iff]
    exact NativeStructure.AtLeast.congr fun other => by
      rw [Bool.and_eq_true, stepIn_iff, eval_iff formula]
  | _, .allButFewer count direction label formula, env, element => by
    simp only [eval, NativeStructure.sat, Bool.not_eq_true']
    rw [← Bool.not_eq_true, atLeastCheck_iff]
    exact not_congr (NativeStructure.AtLeast.congr fun other => by
      rw [Bool.and_eq_true, stepIn_iff, Bool.not_eq_true', ← Bool.not_eq_true, eval_iff formula])
  | _, .built _ arguments, env, element => by
    simp only [eval, List.any_eq_true, Bool.and_eq_true, NativeStructure.sat, native, evalAll_iff arguments,
      Listed.mem_lists F.elements F.complete]
    exact ⟨fun ⟨parts, _, isBuilt, all⟩ => ⟨parts, isBuilt, all⟩,
      fun ⟨parts, isBuilt, all⟩ => ⟨parts, F.native.satAll_length arguments all, isBuilt, all⟩⟩
  | _, .everyBuilt constructor arguments, env, element => by
    simp only [eval, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', NativeStructure.sat, native,
      evalSome_iff arguments, Listed.mem_lists F.elements F.complete]
    constructor
    · intro every parts isBuilt
      by_cases length : parts.length = arguments.length
      · exact (every parts length).resolve_left (by rw [isBuilt]; decide)
      · exact F.native.satSome_of_length_ne arguments length
    · intro every parts _
      by_cases isBuilt : F.built element constructor parts = true
      · exact Or.inr (every parts isBuilt)
      · exact Or.inl (by simpa using isBuilt)
  | _, .split _ left right, env, element => by
    simp only [eval, List.any_eq_true, Bool.and_eq_true, NativeStructure.sat, native, eval_iff left,
      eval_iff right]
    exact ⟨fun ⟨first, _, second, _, ⟨isSplit, leftHolds⟩, rightHolds⟩ => ⟨first, second, isSplit, leftHolds, rightHolds⟩,
      fun ⟨first, second, isSplit, leftHolds, rightHolds⟩ =>
        ⟨first, F.complete first, second, F.complete second, ⟨isSplit, leftHolds⟩, rightHolds⟩⟩
  | _, .everySplit kind left right, env, element => by
    simp only [eval, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', NativeStructure.sat, native,
      eval_iff left, eval_iff right]
    constructor
    · intro every first second isSplit
      rcases every first (F.complete first) second (F.complete second) with (notSplit | leftHolds) | rightHolds
      · rw [isSplit] at notSplit
        cases notSplit
      · exact Or.inl leftHolds
      · exact Or.inr rightHolds
    · intro every first _ second _
      by_cases isSplit : F.split element kind first second = true
      · rcases every first second isSplit with leftHolds | rightHolds
        · exact Or.inl (Or.inr leftHolds)
        · exact Or.inr rightHolds
      · exact Or.inl (Or.inl (by simpa using isSplit))
  | _, .empty _, env, element => by simp [eval, NativeStructure.sat, native]
  | _, .nonEmpty _, env, element => by simp [eval, NativeStructure.sat, native]
  | _, .single _ formula, env, element => by
    simp only [eval, List.any_eq_true, Bool.and_eq_true, NativeStructure.sat, native, eval_iff formula]
    exact ⟨fun ⟨member, _, isSingle, holds⟩ => ⟨member, isSingle, holds⟩,
      fun ⟨member, isSingle, holds⟩ => ⟨member, F.complete member, isSingle, holds⟩⟩
  | _, .everySingle kind formula, env, element => by
    simp only [eval, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', NativeStructure.sat, native,
      eval_iff formula]
    constructor
    · intro every member isSingle
      exact (every member (F.complete member)).resolve_left (by rw [isSingle]; decide)
    · intro every member _
      by_cases isSingle : F.single element kind member = true
      · exact Or.inr (every member isSingle)
      · exact Or.inl (by simpa using isSingle)
  | _, .body formula, env, element => by
    simp only [eval, List.any_eq_true, Bool.and_eq_true, NativeStructure.sat, native, eval_iff formula]
    exact ⟨fun ⟨inner, _, isBody, holds⟩ => ⟨inner, isBody, holds⟩,
      fun ⟨inner, isBody, holds⟩ => ⟨inner, F.complete inner, isBody, holds⟩⟩
  | _, .everyBody formula, env, element => by
    simp only [eval, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', NativeStructure.sat, native,
      eval_iff formula]
    constructor
    · intro every inner isBody
      exact (every inner (F.complete inner)).resolve_left (by rw [isBody]; decide)
    · intro every inner _
      by_cases isBody : F.body element inner = true
      · exact Or.inr (every inner isBody)
      · exact Or.inl (by simpa using isBody)
  | _, .multiBody _ formula, env, element => by
    simp only [eval, List.any_eq_true, Bool.and_eq_true, NativeStructure.sat, native, eval_iff formula]
    exact ⟨fun ⟨inner, _, isBody, holds⟩ => ⟨inner, isBody, holds⟩,
      fun ⟨inner, isBody, holds⟩ => ⟨inner, F.complete inner, isBody, holds⟩⟩
  | _, .everyMultiBody arity formula, env, element => by
    simp only [eval, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', NativeStructure.sat, native,
      eval_iff formula]
    constructor
    · intro every inner isBody
      exact (every inner (F.complete inner)).resolve_left (by rw [isBody]; decide)
    · intro every inner _
      by_cases isBody : F.multiBody element arity inner = true
      · exact Or.inr (every inner isBody)
      · exact Or.inl (by simpa using isBody)
  | _, .bound _, env, element => by simp [eval, NativeStructure.sat, native]
  | _, .notBound _, env, element => by simp [eval, NativeStructure.sat, native]
  | _, .typed _, env, element => by simp [eval, NativeStructure.sat, native]
  | _, .untyped _, env, element => by simp [eval, NativeStructure.sat, native]
  | _, .is _, env, element => by simp [eval, NativeStructure.sat, native]
  | _, .isNot _, env, element => by simp [eval, NativeStructure.sat, native]
  | _, .inRelation _, env, element => by simp [eval, NativeStructure.sat, native]
  | _, .notInRelation _, env, element => by simp [eval, NativeStructure.sat, native]
  | _, .mapsAll argument result, env, element => by
    simp only [eval, List.any_eq_true, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, NativeStructure.sat,
      native, eval_iff argument, eval_iff result]
    exact ⟨fun ⟨inner, _, isBody, every⟩ => ⟨inner, isBody, fun value => every value (F.complete value)⟩,
      fun ⟨inner, isBody, every⟩ => ⟨inner, F.complete inner, isBody, fun value _ => every value⟩⟩
  | _, .mapsSome argument result, env, element => by
    simp only [eval, List.any_eq_true, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      NativeStructure.sat, native, eval_iff argument, eval_iff result]
    constructor
    · intro every inner isBody
      rcases every inner (F.complete inner) with notBody | ⟨value, _, holds⟩
      · rw [isBody] at notBody
        cases notBody
      · exact ⟨value, holds⟩
    · intro every inner _
      by_cases isBody : F.body element inner = true
      · obtain ⟨value, holds⟩ := every inner isBody
        exact Or.inr ⟨value, F.complete value, holds⟩
      · exact Or.inl (by simpa using isBody)
  | _, .someOf _ formula, env, element => by
    simp only [eval, List.any_eq_true, Bool.and_eq_true, NativeStructure.sat, native, eval_iff formula]
    exact ⟨fun ⟨witness, _, isTyped, holds⟩ => ⟨witness, isTyped, holds⟩,
      fun ⟨witness, isTyped, holds⟩ => ⟨witness, F.complete witness, isTyped, holds⟩⟩
  | _, .everyOf type formula, env, element => by
    simp only [eval, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', NativeStructure.sat, native,
      eval_iff formula]
    constructor
    · intro every witness isTyped
      exact (every witness (F.complete witness)).resolve_left (by rw [isTyped]; decide)
    · intro every witness _
      by_cases isTyped : F.typed witness type = true
      · exact Or.inr (every witness isTyped)
      · exact Or.inl (by simpa using isTyped)

theorem evalAll_iff : ∀ {n : ℕ} (formulas : Formulas n) {env : Fin n → Carrier → Bool} {parts : List Carrier},
    F.evalAll env formulas parts = true ↔ F.native.satAll (sets env) formulas parts
  | _, .nil, _, [] => by simp [evalAll, NativeStructure.satAll]
  | _, .nil, _, _ :: _ => by simp [evalAll, NativeStructure.satAll]
  | _, .cons _ _, _, [] => by simp [evalAll, NativeStructure.satAll]
  | _, .cons formula formulas, env, part :: parts => by
    simp only [evalAll, Bool.and_eq_true, NativeStructure.satAll, eval_iff formula env part, evalAll_iff formulas]

theorem evalSome_iff : ∀ {n : ℕ} (formulas : Formulas n) {env : Fin n → Carrier → Bool} {parts : List Carrier},
    F.evalSome env formulas parts = true ↔ F.native.satSome (sets env) formulas parts
  | _, .nil, _, [] => by simp [evalSome, NativeStructure.satSome]
  | _, .nil, _, _ :: _ => by simp [evalSome, NativeStructure.satSome]
  | _, .cons _ _, _, [] => by simp [evalSome, NativeStructure.satSome]
  | _, .cons formula formulas, env, part :: parts => by
    simp only [evalSome, Bool.or_eq_true, NativeStructure.satSome, eval_iff formula env part, evalSome_iff formulas]
end

/-- **Decide a closed formula** at an element. -/
def check (formula : Formula 0) (element : Carrier) : Bool := F.eval (fun index => index.elim0) formula element

/-- **A closed formula's verdict is its satisfaction.** -/
theorem check_iff (formula : Formula 0) (element : Carrier) :
    F.check formula element = true ↔ F.native.sat Env.closed formula element := by
  have same : sets (fun index : Fin 0 => index.elim0 : Fin 0 → Carrier → Bool) = Env.closed :=
    funext fun index => index.elim0
  rw [check, eval_iff, same]

end FiniteStructure

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
