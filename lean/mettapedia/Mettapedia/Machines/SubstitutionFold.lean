import Mettapedia.Machines.ResumableRegion

/-!
# Applying a substitution on an explicit stack

Applying a substitution to a term is a fold over the term.  A variable is
replaced by the image of the value it is bound to, or read as it stands when it
is unbound.  An expression is replaced by the expression of its children's
images.  The runtime memoises variables' images and cuts a binding cycle at a
variable met again on its own binding path.  Here both are carried by an
abstract state `S` and an abstract path `P`, which the variable step reads and
extends.  A term that cannot change (the runtime's has-variables flag) is its
own image.

`Fold` is the recursive specification, as a recursive function computes it.
The runtime runs it on an explicit stack instead (`Step`).  The stack holds
pending variables, whose images are stored once found, and pending expressions,
whose remaining children wait.

* `fold_runs`: from any stack, the machine reaches the image `Fold` gives,
  with that stack unchanged.
* `run_unique`: the machine is deterministic (`step_deterministic`), so from
  the empty stack its only final configuration is that image.

A term nested to any depth, or a binding chain of any length, is therefore
applied with its pending work on the heap: the C stack stays constant.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SubstitutionFold

universe u

/-- Terms: variables, leaves, and expressions of terms. -/
inductive Term (V L : Type u) : Type u where
  | var : V → Term V L
  | leaf : L → Term V L
  | expr : List (Term V L) → Term V L

/-- What the variable step makes of a variable read in scope `c` on path `p`
from state `s`.  Either its image and the state after it (a memoised image, a
variable met again on its own path, an unbound variable's reading).  Or the
value it is bound to, with the key its image is stored under and the scope,
path and state that value is read in.  Or a failure, which the runtime
reports for the whole application. -/
inductive Outcome (V L K C P S : Type u) : Type u where
  | image (r : Term V L) (s : S)
  | bound (k : K) (t : Term V L) (c : C) (p : P) (s : S)
  | failed

/-- A substitution as the fold sees it: the variable step, the memo's store,
and which terms may change (any predicate; the runtime uses its has-variables
flag). -/
structure Subst (V L K C P S : Type u) where
  step : C → P → S → V → Outcome V L K C P S
  store : S → K → Term V L → S
  hasVars : Term V L → Bool

variable {V L K C P S : Type u} (σ : Subst V L K C P S)

mutual
/-- The recursive fold: term `t`, read in scope `c` on path `p` from state `s`,
has image `r` and leaves state `s'`. -/
inductive Fold : C → P → S → Term V L → Term V L → S → Prop
  | fixed {c p s t} : σ.hasVars t = false → Fold c p s t t s
  | leaf {c p s l} : σ.hasVars (.leaf l) = true → Fold c p s (.leaf l) (.leaf l) s
  | image {c p s v r s'} :
      σ.hasVars (.var v) = true → σ.step c p s v = .image r s' →
      Fold c p s (.var v) r s'
  | bound {c p s v k t c' p' s₁ r s₂} :
      σ.hasVars (.var v) = true → σ.step c p s v = .bound k t c' p' s₁ →
      Fold c' p' s₁ t r s₂ → Fold c p s (.var v) r (σ.store s₂ k r)
  | expr {c p s ts rs s'} :
      σ.hasVars (.expr ts) = true → Folds c p s ts rs s' →
      Fold c p s (.expr ts) (.expr rs) s'

/-- The children of an expression, left to right, each read in the
expression's scope and path, the state threaded through. -/
inductive Folds : C → P → S → List (Term V L) → List (Term V L) → S → Prop
  | nil {c p s} : Folds c p s [] [] s
  | cons {c p s t ts r rs s₁ s₂} :
      Fold c p s t r s₁ → Folds c p s₁ ts rs s₂ → Folds c p s (t :: ts) (r :: rs) s₂
end

/-- Pending work: a variable whose image is stored under a key once found, or
an expression with the images of its children so far (latest first) and the
children still to read. -/
inductive Frame (V L K C P : Type u) : Type u where
  | var (k : K)
  | expr (c : C) (p : P) (done : List (Term V L)) (rest : List (Term V L))

/-- The machine: descending into a term, or ascending with an image. -/
inductive Config (V L K C P S : Type u) : Type u where
  | descend (c : C) (p : P) (t : Term V L) (stack : List (Frame V L K C P)) (s : S)
  | ascend (r : Term V L) (stack : List (Frame V L K C P)) (s : S)

/-- One step of the machine. -/
inductive Step : Config V L K C P S → Config V L K C P S → Prop
  | fixed {c p t stack s} :
      σ.hasVars t = false → Step (.descend c p t stack s) (.ascend t stack s)
  | leaf {c p l stack s} :
      σ.hasVars (.leaf l) = true →
      Step (.descend c p (.leaf l) stack s) (.ascend (.leaf l) stack s)
  | image {c p v stack s r s'} :
      σ.hasVars (.var v) = true → σ.step c p s v = .image r s' →
      Step (.descend c p (.var v) stack s) (.ascend r stack s')
  | bound {c p v stack s k t c' p' s₁} :
      σ.hasVars (.var v) = true → σ.step c p s v = .bound k t c' p' s₁ →
      Step (.descend c p (.var v) stack s) (.descend c' p' t (.var k :: stack) s₁)
  | empty {c p stack s} :
      σ.hasVars (.expr []) = true →
      Step (.descend c p (.expr []) stack s) (.ascend (.expr []) stack s)
  | enter {c p u us stack s} :
      σ.hasVars (.expr (u :: us)) = true →
      Step (.descend c p (.expr (u :: us)) stack s)
        (.descend c p u (.expr c p [] us :: stack) s)
  | store {r k stack s} :
      Step (.ascend r (.var k :: stack) s) (.ascend r stack (σ.store s k r))
  | next {r c p done u us stack s} :
      Step (.ascend r (.expr c p done (u :: us) :: stack) s)
        (.descend c p u (.expr c p (r :: done) us :: stack) s)
  | close {r c p done stack s} :
      Step (.ascend r (.expr c p done [] :: stack) s)
        (.ascend (.expr (r :: done).reverse) stack s)

/-- Runs of the machine. -/
inductive Steps : Config V L K C P S → Config V L K C P S → Prop
  | refl {x} : Steps x x
  | head {x y z} : Step σ x y → Steps y z → Steps x z

variable {σ}

theorem Steps.single {x y : Config V L K C P S} (h : Step σ x y) : Steps σ x y :=
  .head h .refl

theorem Steps.trans {x y z : Config V L K C P S} :
    Steps σ x y → Steps σ y z → Steps σ x z := by
  intro hxy hyz
  induction hxy with
  | refl => exact hyz
  | head h _ ih => exact .head h (ih hyz)

/-- Where the machine stands inside a pending expression with images `done`
(latest first) and children `ts` still to read: descending into the next
child, or closing the expression. -/
def resume (c : C) (p : P) (done : List (Term V L)) :
    List (Term V L) → List (Frame V L K C P) → S → Config V L K C P S
  | u :: us, stack, s => .descend c p u (.expr c p done us :: stack) s
  | [], stack, s => .ascend (.expr done.reverse) stack s

/-- Entering an expression resumes it with no image yet. -/
theorem enter_resume {c : C} {p : P} {ts : List (Term V L)}
    {stack : List (Frame V L K C P)} {s : S} (hv : σ.hasVars (.expr ts) = true) :
    Step σ (.descend c p (.expr ts) stack s) (resume c p [] ts stack s) := by
  cases ts with
  | nil => exact .empty hv
  | cons u us => exact .enter hv

/-- A child's image resumes its expression with that image. -/
theorem ascend_resume {r : Term V L} {c : C} {p : P} {done ts : List (Term V L)}
    {stack : List (Frame V L K C P)} {s : S} :
    Step σ (.ascend r (.expr c p done ts :: stack) s) (resume c p (r :: done) ts stack s) := by
  cases ts with
  | nil => exact .close
  | cons u us => exact .next

/-- The machine reaches, from any stack, the image the recursive fold gives.
Inside a pending expression it reads the remaining children and closes the
expression with every image in order. -/
theorem fold_runs {c : C} {p : P} {s s' : S} {t r : Term V L}
    (h : Fold σ c p s t r s') (stack : List (Frame V L K C P)) :
    Steps σ (.descend c p t stack s) (.ascend r stack s') := by
  refine Fold.rec
    (motive_1 := fun c p s t r s' _ => ∀ stack : List (Frame V L K C P),
      Steps σ (.descend c p t stack s) (.ascend r stack s'))
    (motive_2 := fun c p s ts rs s' _ =>
      ∀ (stack : List (Frame V L K C P)) (done : List (Term V L)),
        Steps σ (resume c p done ts stack s)
          (.ascend (.expr (done.reverse ++ rs)) stack s'))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ h stack
  · intro c p s t hv stack
    exact .single (.fixed hv)
  · intro c p s l hv stack
    exact .single (.leaf hv)
  · intro c p s v r s' hv hs stack
    exact .single (.image hv hs)
  · intro c p s v k t c' p' s₁ r s₂ hv hs _ ih stack
    exact .head (.bound hv hs) ((ih _).trans (.single .store))
  · intro c p s ts rs s' hv _ ih stack
    have hrun := ih stack []
    simp only [List.reverse_nil, List.nil_append] at hrun
    exact .head (enter_resume hv) hrun
  · intro c p s stack done
    simp only [List.append_nil]
    exact .refl
  · intro c p s t ts r rs s₁ s₂ _ _ ih₁ ih₂ stack done
    have hrest := ih₂ stack (r :: done)
    rw [List.reverse_cons, List.append_assoc, List.singleton_append] at hrest
    exact (ih₁ _).trans (.head ascend_resume hrest)

/-- The machine has at most one step from any configuration. -/
theorem step_deterministic {x y z : Config V L K C P S}
    (hy : Step σ x y) (hz : Step σ x z) : y = z := by
  cases hy <;> cases hz <;> simp_all

/-- An image with no pending work is final. -/
theorem ascend_nil_final (r : Term V L) (s : S) (y : Config V L K C P S) :
    ¬ Step σ (.ascend r [] s) y := by
  intro h
  cases h

/-- Two final configurations reached from one configuration are equal. -/
theorem steps_final_unique {x a : Config V L K C P S} (ha : Steps σ x a) :
    ∀ {b}, (∀ y, ¬ Step σ a y) → Steps σ x b → (∀ y, ¬ Step σ b y) → a = b := by
  induction ha with
  | refl =>
      intro b ha_final hb _
      cases hb with
      | refl => rfl
      | head h _ => exact absurd h (ha_final _)
  | head hxy _ ih =>
      intro b ha_final hb hb_final
      cases hb with
      | refl => exact absurd hxy (hb_final _)
      | head hxy' hb' =>
          rw [← step_deterministic hxy hxy'] at hb'
          exact ih ha_final hb' hb_final

/-- From the empty stack, the machine's only final configuration is the
recursive fold's image, with the state the fold leaves. -/
theorem run_unique {c : C} {p : P} {s s' : S} {t r : Term V L}
    (h : Fold σ c p s t r s') {z : Config V L K C P S}
    (hz : Steps σ (.descend c p t [] s) z) (hz_final : ∀ y, ¬ Step σ z y) :
    z = .ascend r [] s' :=
  (steps_final_unique (fold_runs h []) (ascend_nil_final r s') hz hz_final).symm

/-! ## Executable retained traversal

The executable body implements the existing relational stack. A failed
variable resolution stops with its exact configuration retained; it is not a
completed image. Scope/path interpretation and the work inside one variable
resolution remain the substitution instance's responsibility.
-/

/-- One structural transition, with the same variable and memo operations as
`Step`. Failure does not fabricate an image or discard the pending stack. -/
def step (σ : Subst V L K C P S) : Config V L K C P S → Option (Config V L K C P S)
  | .descend c p term stack state =>
      if σ.hasVars term then
        match term with
        | .leaf value => some (.ascend (.leaf value) stack state)
        | .var name => match σ.step c p state name with
          | .image value later => some (.ascend value stack later)
          | .bound key value scope path later =>
              some (.descend scope path value (.var key :: stack) later)
          | .failed => none
        | .expr [] => some (.ascend (.expr []) stack state)
        | .expr (first :: rest) =>
            some (.descend c p first (.expr c p [] rest :: stack) state)
      else some (.ascend term stack state)
  | .ascend _ [] _ => none
  | .ascend value (.var key :: stack) state =>
      some (.ascend value stack (σ.store state key value))
  | .ascend value (.expr c p done (first :: rest) :: stack) state =>
      some (.descend c p first (.expr c p (value :: done) rest :: stack) state)
  | .ascend value (.expr _ _ done [] :: stack) state =>
      some (.ascend (.expr (value :: done).reverse) stack state)

theorem step_complete {before after : Config V L K C P S}
    (transition : Step σ before after) : step σ before = some after := by
  cases transition <;> simp_all [step]

theorem step_sound {before after : Config V L K C P S}
    (transition : step σ before = some after) : Step σ before after := by
  cases before with
  | descend c p term stack state =>
      cases changing : σ.hasVars term with
      | false =>
          simp only [step, changing, Bool.false_eq_true, ↓reduceIte,
            Option.some.injEq] at transition
          subst after
          exact .fixed changing
      | true =>
          cases term with
          | leaf value =>
              simp only [step, changing, ↓reduceIte, Option.some.injEq] at transition
              subst after
              exact .leaf changing
          | var name =>
              cases resolved : σ.step c p state name with
              | failed => simp [step, changing, resolved] at transition
              | image value later =>
                  simp only [step, changing, ↓reduceIte, resolved,
                    Option.some.injEq] at transition
                  subst after
                  exact .image changing resolved
              | bound key value scope path later =>
                  simp only [step, changing, ↓reduceIte, resolved,
                    Option.some.injEq] at transition
                  subst after
                  exact .bound changing resolved
          | expr terms =>
              cases terms with
              | nil =>
                  simp only [step, changing, ↓reduceIte, Option.some.injEq] at transition
                  subst after
                  exact .empty changing
              | cons first rest =>
                  simp only [step, changing, ↓reduceIte, Option.some.injEq] at transition
                  subst after
                  exact .enter changing
  | ascend value stack state =>
      cases stack with
      | nil => simp [step] at transition
      | cons frame stack =>
          cases frame with
          | var key =>
              simp only [step, Option.some.injEq] at transition
              subst after
              exact .store
          | expr c p done rest =>
              cases rest with
              | nil =>
                  simp only [step, Option.some.injEq] at transition
                  subst after
                  exact .close
              | cons first rest =>
                  simp only [step, Option.some.injEq] at transition
                  subst after
                  exact .next

theorem step_iff {before after : Config V L K C P S} :
    step σ before = some after ↔ Step σ before after :=
  ⟨step_sound, step_complete⟩

/-- Only an empty returned stack supplies an image. An explicit resolution
failure has its own result; an unfinished traversal has no terminal result. -/
def readout (σ : Subst V L K C P S) :
    Config V L K C P S → Option (Except Unit (Term V L × S))
  | .ascend value [] state => some (.ok (value, state))
  | .descend scope path (.var name) _ state =>
      if σ.hasVars (.var name) then
        match σ.step scope path state name with
        | .failed => some (.error ())
        | _ => none
      else none
  | _ => none

theorem readout_success_iff (configuration : Config V L K C P S)
    (value : Term V L) (state : S) :
    readout σ configuration = some (.ok (value, state)) ↔
      configuration = .ascend value [] state := by
  cases configuration with
  | ascend image stack later =>
      cases stack <;> simp [readout, Prod.ext_iff]
  | descend scope path term stack earlier =>
      cases term with
      | leaf => simp [readout]
      | expr => simp [readout]
      | var name =>
          cases changing : σ.hasVars (.var name) <;>
            cases resolved : σ.step scope path earlier name <;>
              simp [readout, changing, resolved]

theorem readout_final_iff (configuration : Config V L K C P S) :
    (readout σ configuration).isSome = true ↔ step σ configuration = none := by
  cases configuration with
  | ascend value stack state =>
      cases stack with
      | nil => simp [readout, step]
      | cons frame stack =>
          cases frame with
          | var => simp [readout, step]
          | expr scope path done rest => cases rest <;> simp [readout, step]
  | descend scope path term stack state =>
      cases term with
      | leaf value => cases σ.hasVars (.leaf value) <;> simp [readout, step, *]
      | expr terms =>
          cases changing : σ.hasVars (.expr terms) <;> cases terms <;>
            simp [readout, step, changing]
      | var name =>
          cases changing : σ.hasVars (.var name) <;>
            cases resolved : σ.step scope path state name <;>
              simp [readout, step, changing, resolved]

namespace Executable

variable {Name Leaf Key Scope Path Store : Type}
variable (substitution : Subst Name Leaf Key Scope Path Store)

abbrev Input := Scope × Path × Store × Term Name Leaf

/-- The existing machine substrate, loaded with the actual starting scope,
path and private store. The loader does not interpret or force a source. -/
abbrev machineCore : Mettapedia.Machines.MachineCore
    (Input (Name := Name) (Leaf := Leaf) (Scope := Scope) (Path := Path) (Store := Store)) where
  State := Config Name Leaf Key Scope Path Store
  load := fun ⟨scope, path, state, term⟩ => .descend scope path term [] state
  step := step substitution

theorem steps_to_core {before after : Config Name Leaf Key Scope Path Store}
    (run : Steps substitution before after) : (machineCore substitution).Steps before after := by
  induction run with
  | refl => exact .refl
  | head transition _ ih => exact .head (step_complete transition) ih

theorem core_to_steps {before after : Config Name Leaf Key Scope Path Store}
    (run : (machineCore substitution).Steps before after) : Steps substitution before after := by
  induction run using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head transition _ ih => exact .head (step_sound transition) ih

/-- Every derivation of the independent recursive fold is realized by a
finite number of the executable stack's actual transitions. -/
theorem steps_exact_slice {before after : Config Name Leaf Key Scope Path Store}
    (run : Steps substitution before after) :
    ∃ used, Mettapedia.Machines.MachineCore.runSlice (machineCore substitution) used before =
      (after, used) := by
  induction run with
  | refl => exact ⟨0, rfl⟩
  | @head before middle after transition _ ih =>
      obtain ⟨used, exactRun⟩ := ih
      refine ⟨used + 1, ?_⟩
      simp only [Mettapedia.Machines.MachineCore.runSlice,
        step_complete transition]
      rw [exactRun]

theorem fold_exact_slice {scope : Scope} {path : Path} {state later : Store}
    {term value : Term Name Leaf}
    (fold : Fold substitution scope path state term value later) :
    ∃ used, Mettapedia.Machines.MachineCore.runSlice (machineCore substitution) used
      (.descend scope path term [] state) = (.ascend value [] later, used) :=
  steps_exact_slice substitution (fold_runs fold [])

/-- A terminal sliced run agrees with the independently specified recursive
fold, including its complete private store, rather than only its term. -/
theorem completed_slice_eq_fold {scope : Scope} {path : Path} {state later : Store}
    {term value : Term Name Leaf}
    (fold : Fold substitution scope path state term value later) (grant : Nat)
    (finished : (machineCore substitution).step
      (Mettapedia.Machines.MachineCore.runSlice (machineCore substitution) grant
        (.descend scope path term [] state)).1 = none) :
    (Mettapedia.Machines.MachineCore.runSlice (machineCore substitution) grant
      (.descend scope path term [] state)).1 = .ascend value [] later := by
  apply run_unique fold
  · exact core_to_steps substitution
      (Mettapedia.Machines.MachineCore.runSlice_steps (machineCore substitution) grant _)
  · intro next transition
    have executable := step_complete transition
    change (machineCore substitution).step _ = some next at executable
    rw [finished] at executable
    simp at executable

/-- Arbitrary grant words retain the existing paid machine packet. -/
def grantWord (grants : List Nat) (packet : Nat × Config Name Leaf Key Scope Path Store) :
    Nat × Config Name Leaf Key Scope Path Store :=
  grants.foldl (fun held grant =>
    Mettapedia.Machines.MachineCore.paidSlice (machineCore substitution) grant held) packet

theorem grantWord_exact (grants : List Nat)
    (packet : Nat × Config Name Leaf Key Scope Path Store) :
    grantWord substitution grants packet =
      Mettapedia.Machines.MachineCore.paidSlice (machineCore substitution) grants.sum packet := by
  induction grants generalizing packet with
  | nil =>
      exact (Mettapedia.Machines.MachineCore.paidSlice_zero
        (machineCore substitution) packet).symm
  | cons first rest ih =>
      change grantWord substitution rest
          (Mettapedia.Machines.MachineCore.paidSlice (machineCore substitution) first packet) =
        Mettapedia.Machines.MachineCore.paidSlice (machineCore substitution)
          (first + rest.sum) packet
      rw [ih, Mettapedia.Machines.MachineCore.paidSlice_add]

theorem grantWord_debit_bounds (grants : List Nat)
    (packet : Nat × Config Name Leaf Key Scope Path Store) :
    packet.1 ≤ (grantWord substitution grants packet).1 ∧
      (grantWord substitution grants packet).1 ≤ packet.1 + grants.sum := by
  rw [grantWord_exact]
  exact Mettapedia.Machines.MachineCore.paidSlice_debit_bounds
    (machineCore substitution) grants.sum packet

theorem zero_grant_retains (packet : Nat × Config Name Leaf Key Scope Path Store) :
    Mettapedia.Machines.MachineCore.paidSlice (machineCore substitution) 0 packet = packet :=
  Mettapedia.Machines.MachineCore.paidSlice_zero _ _

theorem terminal_grants_inert (configuration : Config Name Leaf Key Scope Path Store)
    (terminal : (readout substitution configuration).isSome = true) (paid : Nat)
    (grants : List Nat) : grantWord substitution grants (paid, configuration) =
      (paid, configuration) := by
  rw [grantWord_exact]
  exact Mettapedia.Machines.MachineCore.paidSlice_of_final _ _
    ((readout_final_iff configuration).mp terminal) _ _

end Executable

namespace Controls

/-- Variables and leaves of the controls. -/
inductive Name | x | y | z
  deriving DecidableEq

inductive Leaf | cons | one | two | nil
  deriving DecidableEq

/-- A two-cell list bound cell by cell: `x ↦ (cons 1 y)`, `y ↦ (cons 2 nil)`;
`z` is unbound. -/
def chain : Subst Name Leaf Name Unit Unit Unit where
  step _ _ _ v :=
    match v with
    | .x => .bound .x (.expr [.leaf .cons, .leaf .one, .var .y]) () () ()
    | .y => .bound .y (.expr [.leaf .cons, .leaf .two, .leaf .nil]) () () ()
    | .z => .image (.var .z) ()
  store s _ _ := s
  hasVars t :=
    match t with
    | .var _ => true
    | .leaf _ => false
    | .expr [_, _, .var _] => true
    | .expr _ => false

/-- The image of `x` is the whole list: the fold follows the chain through `y`. -/
theorem chain_image :
    Fold chain () () () (.var .x)
      (.expr [.leaf .cons, .leaf .one,
        .expr [.leaf .cons, .leaf .two, .leaf .nil]]) () :=
  .bound (k := .x) (t := .expr [.leaf .cons, .leaf .one, .var .y])
    (c' := ()) (p' := ()) (s₁ := ()) rfl rfl
    (.expr rfl (.cons (.fixed rfl) (.cons (.fixed rfl)
      (.cons (.bound (k := .y) (t := .expr [.leaf .cons, .leaf .two, .leaf .nil])
        (c' := ()) (p' := ()) (s₁ := ()) rfl rfl (.fixed rfl)) .nil))))

/-- An unbound variable's image is the step's own reading of it. -/
theorem unbound_image : Fold chain () () () (.var .z) (.var .z) () :=
  .image rfl rfl

/-- The machine does not stop at the bound value `(cons 1 y)`: its only final
configuration from `x` is the whole list. -/
theorem chain_not_shallow
    (hz : Steps chain (.descend () () (.var .x) [] ())
      (.ascend (.expr [.leaf .cons, .leaf .one, .var .y]) [] ())) : False := by
  have := run_unique chain_image hz (ascend_nil_final _ _)
  simp at this

/-! Stateful executable controls. The private memo is used by the second
occurrence; the selected scope changes the first resolution. -/

private def memoized : Subst Nat Nat Nat Bool (List Nat) (List (Nat × Term Nat Nat)) where
  step scope path state name :=
    match state.find? (fun row => row.1 == name) with
    | some row => .image row.2 state
    | none =>
        if name ∈ path then .failed else
          match name with
          | 0 => .bound 0 (.expr [.var 1, .var 1]) scope (0 :: path) state
          | 1 => .bound 1 (.leaf (if scope then 7 else 8)) scope (1 :: path) state
          | 2 => .failed
          | other => .image (.var other) state
  store state key value := (key, value) :: state
  hasVars _ := true

private def memoStart : Config Nat Nat Nat Bool (List Nat) (List (Nat × Term Nat Nat)) :=
  .descend true [] (.var 0) [] []

private def memoValue : Term Nat Nat := .expr [.leaf 7, .leaf 7]

private def memoFinal : Config Nat Nat Nat Bool (List Nat) (List (Nat × Term Nat Nat)) :=
  .ascend memoValue [] [(0, memoValue), (1, .leaf 7)]

theorem paid_memoized_traversal :
    Mettapedia.Machines.MachineCore.paidSlice (Executable.machineCore memoized)
      9 (4, memoStart) = (13, memoFinal) := by
  rfl

theorem arbitrary_slices_keep_scope_path_and_memo :
    Executable.grantWord memoized [1, 0, 2, 1, 5, 8] (4, memoStart) =
      (13, memoFinal) := by
  rfl

theorem pause_keeps_pending_variable_and_expression :
    Mettapedia.Machines.MachineCore.paidSlice (Executable.machineCore memoized)
      3 (4, memoStart) =
        (7, .descend true [1, 0] (.leaf 7)
          [.var 1, .expr true [0] [] [.var 1], .var 0] []) := by
  rfl

theorem another_scope_changes_the_completed_image :
    Mettapedia.Machines.MachineCore.runSlice (Executable.machineCore memoized)
      9 (.descend false [] (.var 0) [] []) =
        (.ascend (.expr [.leaf 8, .leaf 8]) []
          [(0, .expr [.leaf 8, .leaf 8]), (1, .leaf 8)], 9) := by
  rfl

private def refusedStart : Config Nat Nat Nat Bool (List Nat) (List (Nat × Term Nat Nat)) :=
  .descend true [] (.expr [.var 1, .var 2]) [] []

private def refusedFinal : Config Nat Nat Nat Bool (List Nat) (List (Nat × Term Nat Nat)) :=
  .descend true [] (.var 2) [.expr true [] [.leaf 7] []] [(1, .leaf 7)]

theorem refusal_retains_earlier_memo_writes_and_paid_work :
    Mettapedia.Machines.MachineCore.paidSlice (Executable.machineCore memoized)
      30 (4, refusedStart) = (9, refusedFinal) ∧
      readout memoized refusedFinal = some (.error ()) := by
  exact ⟨rfl, rfl⟩

theorem refused_terminal_does_not_repeat_a_transition :
    Executable.grantWord memoized [0, 1, 7] (9, refusedFinal) = (9, refusedFinal) := by
  rfl

private def endless : Subst Nat Nat Nat Unit Unit Nat where
  step _ _ state name := .bound name (.var name) () () (state + 1)
  store state _ _ := state
  hasVars _ := true

theorem grant_exhaustion_has_no_terminal_readout :
    let later := Mettapedia.Machines.MachineCore.paidSlice (Executable.machineCore endless)
      3 (0, .descend () () (.var 0) [] 0)
    later.1 = 3 ∧ later.2 = .descend () () (.var 0) [.var 0, .var 0, .var 0] 3 ∧
      readout endless later.2 = none := by
  exact ⟨rfl, rfl, rfl⟩

end Controls

end Mettapedia.Machines.SubstitutionFold
