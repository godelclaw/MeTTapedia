import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

/-!
# Reaching marked carriers through immutable variable support

Constructor structure is immutable; the store can change between observations.
The independent reachability relation follows both constructor children and
current variable bindings. Direct support factors out constructor traversal.
Cell identities may include a lexical frame or generation.

This models the semantic reduction used by list-carrier admission. It does not
verify native metadata construction, frame lookup, allocation or C execution.
-/

namespace Mettapedia.Machines.ContextualCarrierSupport

inductive Term (Cell : Type) where
  | literal (marked : Bool)
  | var (cell : Cell)
  | pair (left right : Term Cell)

variable {Cell : Type} [DecidableEq Cell]

def support : Term Cell → Finset Cell
  | .literal _ => ∅
  | .var cell => {cell}
  | .pair left right => support left ∪ support right

def marked : Term Cell → Bool
  | .literal flag => flag
  | .var _ => false
  | .pair left right => marked left || marked right

abbrev Store (Cell : Type) := Cell → Option (Term Cell)

/-- Finite witnessing paths through constructors and the current store. -/
inductive Reaches (store : Store Cell) : Term Cell → Prop where
  | literal {flag} : flag = true → Reaches store (.literal flag)
  | binding {cell image} : store cell = some image →
      Reaches store image → Reaches store (.var cell)
  | left {left right} : Reaches store left → Reaches store (.pair left right)
  | right {left right} : Reaches store right → Reaches store (.pair left right)

theorem reaches_decompose {store : Store Cell} {term : Term Cell}
    (reached : Reaches store term) :
    marked term = true ∨
      ∃ cell ∈ support term, ∃ image, store cell = some image ∧ Reaches store image := by
  induction reached with
  | literal found => exact Or.inl found
  | @binding cell image bound child _ =>
      exact Or.inr ⟨cell, by simp [support], image, bound, child⟩
  | @left left right _ ih =>
      rcases ih with found | ⟨cell, member, image, bound, child⟩
      · exact Or.inl (by simp [marked, found])
      · exact Or.inr ⟨cell, Finset.mem_union_left _ member, image, bound, child⟩
  | @right left right _ ih =>
      rcases ih with found | ⟨cell, member, image, bound, child⟩
      · exact Or.inl (by simp [marked, found])
      · exact Or.inr ⟨cell, Finset.mem_union_right _ member, image, bound, child⟩

omit [DecidableEq Cell] in
theorem reaches_of_marked (store : Store Cell) (term : Term Cell)
    (found : marked term = true) : Reaches store term := by
  induction term with
  | literal flag => exact .literal found
  | var cell => simp [marked] at found
  | pair left right ihLeft ihRight =>
      simp only [marked, Bool.or_eq_true] at found
      rcases found with h | h
      · exact .left (ihLeft h)
      · exact .right (ihRight h)

theorem reaches_of_support {store : Store Cell} (term : Term Cell)
    {cell : Cell} (member : cell ∈ support term) {image : Term Cell}
    (bound : store cell = some image) (child : Reaches store image) :
    Reaches store term := by
  induction term with
  | literal flag => simp [support] at member
  | var atCell =>
      have same : cell = atCell := by simpa [support] using member
      subst atCell
      exact .binding bound child
  | pair left right ihLeft ihRight =>
      rcases Finset.mem_union.mp member with h | h
      · exact .left (ihLeft h)
      · exact .right (ihRight h)

theorem reaches_iff_frontier (store : Store Cell) (term : Term Cell) :
    Reaches store term ↔ marked term = true ∨
      ∃ cell ∈ support term, ∃ image, store cell = some image ∧ Reaches store image := by
  constructor
  · exact reaches_decompose
  · rintro (found | ⟨cell, member, image, bound, child⟩)
    · exact reaches_of_marked store term found
    · exact reaches_of_support term member bound child

/-- No constructor is marked, and one variable accounts for every dynamic edge. -/
theorem singleton_refinement (store : Store Cell) (term : Term Cell) (cell : Cell)
    (clear : marked term = false) (single : support term = {cell}) :
    Reaches store term ↔ ∃ image, store cell = some image ∧ Reaches store image := by
  rw [reaches_iff_frontier]
  simp [clear, single]

theorem singleton_unbound (store : Store Cell) (term : Term Cell) (cell : Cell)
    (clear : marked term = false) (single : support term = {cell})
    (unbound : store cell = none) : ¬ Reaches store term := by
  rw [singleton_refinement store term cell clear single]
  simp [unbound]

/-- Immutable syntax alone cannot decide a live carrier query. In particular,
a cached verdict must not survive arbitrary binding changes or rollback. -/
theorem no_store_independent_verdict (term : Term Cell) (cell : Cell)
    (clear : marked term = false) (single : support term = {cell}) :
    ¬ ∃ answer : Bool, ∀ store : Store Cell,
      answer = true ↔ Reaches store term := by
  rintro ⟨answer, correct⟩
  let empty : Store Cell := fun _ => none
  let bound : Store Cell := fun other =>
    if other = cell then some (.literal true) else none
  have absent : ¬ Reaches empty term :=
    singleton_unbound empty term cell clear single rfl
  have present : Reaches bound term := by
    apply (singleton_refinement bound term cell clear single).mpr
    exact ⟨.literal true, by simp [bound], .literal rfl⟩
  exact absent ((correct empty).mp ((correct bound).mpr present))

/-- The single image is unbound or already carries a complete ground answer. -/
def AtomicAt (store : Store Cell) (cell : Cell) : Prop :=
  store cell = none ∨ ∃ flag, store cell = some (.literal flag)

/-- Fixed-footprint lower bound on an inhabited region: even when the only
image is unbound or ground, an exact observer must read its live coordinate.
Preparation of immutable support is outside this bound. -/
theorem required_live_read (term : Term Cell) (cell : Cell)
    (clear : marked term = false) (single : support term = {cell})
    (reads : Finset Cell) (observer : Store Cell → Bool)
    (depends : ∀ first second : Store Cell,
      (∀ other ∈ reads, first other = second other) →
        observer first = observer second)
    (correct : ∀ store, AtomicAt store cell →
      (observer store = true ↔ Reaches store term)) :
    cell ∈ reads := by
  by_contra missing
  let empty : Store Cell := fun _ => none
  let bound : Store Cell := fun other =>
    if other = cell then some (.literal true) else none
  have agree : ∀ other ∈ reads, empty other = bound other := by
    intro other member
    have different : other ≠ cell := by
      intro same
      subst other
      exact missing member
    simp [empty, bound, different]
  have same := depends empty bound agree
  have absent : ¬ Reaches empty term :=
    singleton_unbound empty term cell clear single rfl
  have present : Reaches bound term := by
    apply (singleton_refinement bound term cell clear single).mpr
    exact ⟨.literal true, by simp [bound], .literal rfl⟩
  have emptyAtomic : AtomicAt empty cell := Or.inl rfl
  have boundAtomic : AtomicAt bound cell := Or.inr ⟨true, by simp [bound]⟩
  exact absent ((correct empty emptyAtomic).mp
    (same.trans ((correct bound boundAtomic).mpr present)))

/-- An actual one-lookup observer for the admitted ground-image region. -/
def readCarrier (cell : Cell) (store : Store Cell) : Bool :=
  match store cell with
  | some (.literal flag) => flag
  | _ => false

omit [DecidableEq Cell] in
theorem reaches_literal_iff (store : Store Cell) (flag : Bool) :
    Reaches store (.literal flag) ↔ flag = true := by
  constructor
  · intro reached
    cases reached with
    | literal found => exact found
  · exact Reaches.literal

theorem readCarrier_correct (store : Store Cell) (term : Term Cell) (cell : Cell)
    (clear : marked term = false) (single : support term = {cell})
    (atomic : AtomicAt store cell) :
    readCarrier cell store = true ↔ Reaches store term := by
  rw [singleton_refinement store term cell clear single]
  rcases atomic with unbound | ⟨flag, bound⟩
  · simp [readCarrier, unbound]
  · simp [readCarrier, bound, reaches_literal_iff]

omit [DecidableEq Cell] in
theorem readCarrier_footprint (cell : Cell) (first second : Store Cell)
    (agree : ∀ other ∈ ({cell} : Finset Cell), first other = second other) :
    readCarrier cell first = readCarrier cell second := by
  unfold readCarrier
  rw [agree cell (by simp)]

/-- The lower bound is attained by a concrete observer on this region. -/
theorem singleton_attains_live_bound (term : Term Cell) (cell : Cell)
    (clear : marked term = false) (single : support term = {cell}) :
    ∃ (reads : Finset Cell) (observer : Store Cell → Bool),
      reads.card = 1 ∧
      (∀ first second, (∀ other ∈ reads, first other = second other) →
        observer first = observer second) ∧
      (∀ store, AtomicAt store cell →
        (observer store = true ↔ Reaches store term)) := by
  exact ⟨{cell}, readCarrier cell, by simp,
    readCarrier_footprint cell,
    fun store atomic => readCarrier_correct store term cell clear single atomic⟩

def repeated (cell : Cell) : Nat → Term Cell
  | 0 => .var cell
  | n + 1 => .pair (repeated cell n) (repeated cell n)

theorem repeated_support (cell : Cell) (depth : Nat) :
    support (repeated cell depth) = {cell} := by
  induction depth with
  | zero => rfl
  | succ n ih => simp [repeated, support, ih]

omit [DecidableEq Cell] in
theorem repeated_clear (cell : Cell) (depth : Nat) :
    marked (repeated cell depth) = false := by
  induction depth with
  | zero => rfl
  | succ n ih => simp [repeated, marked, ih]

theorem repeated_refinement (store : Store Cell) (cell : Cell) (depth : Nat) :
    Reaches store (repeated cell depth) ↔
      ∃ image, store cell = some image ∧ Reaches store image :=
  singleton_refinement store _ cell (repeated_clear cell depth) (repeated_support cell depth)

example : Reaches (fun _ : Nat => some (.literal true)) (repeated 7 32) := by
  rw [repeated_refinement]
  exact ⟨.literal true, rfl, .literal rfl⟩

example : ¬ Reaches (fun _ : Nat => none) (repeated 7 32) :=
  singleton_unbound _ _ _ (repeated_clear 7 32) (repeated_support 7 32) rfl

example : ¬ Reaches
    (fun coordinate : Nat × Nat => if coordinate = (1, 7) then some (.literal true) else none)
    (repeated (2, 7) 32) := by
  apply singleton_unbound _ _ _ (repeated_clear _ _) (repeated_support _ _)
  decide

#print axioms reaches_iff_frontier
#print axioms singleton_refinement
#print axioms repeated_refinement
#print axioms no_store_independent_verdict
#print axioms required_live_read
#print axioms singleton_attains_live_bound

/-- Independent finite substitution derivations. Bound images are recursively
read; cycles have no finite derivation unless another rule discharges them. -/
inductive Substitutes (store : Store Cell) : Term Cell → Term Cell → Prop where
  | literal (flag) : Substitutes store (.literal flag) (.literal flag)
  | unbound {cell} : store cell = none → Substitutes store (.var cell) (.var cell)
  | binding {cell image result} : store cell = some image →
      Substitutes store image result → Substitutes store (.var cell) result
  | pair {left right leftImage rightImage} :
      Substitutes store left leftImage → Substitutes store right rightImage →
      Substitutes store (.pair left right) (.pair leftImage rightImage)

/-- If no supported coordinate is bound, the original term is the unique
substitution image. No acyclicity assumption about unrelated bindings is used. -/
theorem substitutes_iff_of_support_unbound (store : Store Cell) (term : Term Cell)
    (unbound : ∀ cell ∈ support term, store cell = none) (image : Term Cell) :
    Substitutes store term image ↔ image = term := by
  induction term generalizing image with
  | literal flag =>
      constructor
      · intro observed
        cases observed
        rfl
      · rintro rfl
        exact .literal flag
  | var cell =>
      have absent := unbound cell (by simp [support])
      constructor
      · intro observed
        cases observed with
        | unbound _ => rfl
        | binding bound _ => simp [absent] at bound
      · rintro rfl
        exact .unbound absent
  | pair left right ihLeft ihRight =>
      have clearLeft : ∀ cell ∈ support left, store cell = none :=
        fun cell member => unbound cell (Finset.mem_union_left _ member)
      have clearRight : ∀ cell ∈ support right, store cell = none :=
        fun cell member => unbound cell (Finset.mem_union_right _ member)
      constructor
      · intro observed
        cases observed with
        | pair leftRun rightRun =>
            rw [(ihLeft clearLeft _).mp leftRun, (ihRight clearRight _).mp rightRun]
      · rintro rfl
        exact .pair ((ihLeft clearLeft _).mpr rfl) ((ihRight clearRight _).mpr rfl)

/-- Exact specialization to immutable singleton support and one live lookup.
This concerns materialized syntax, without a variable-renaming hook. -/
theorem singleton_unbound_substitution (store : Store Cell) (term : Term Cell)
    (cell : Cell) (single : support term = {cell}) (absent : store cell = none)
    (image : Term Cell) : Substitutes store term image ↔ image = term := by
  apply substitutes_iff_of_support_unbound
  intro other member
  have same : other = cell := by simpa [single] using member
  simpa [same] using absent

omit [DecidableEq Cell] in
theorem reaches_pair_iff (store : Store Cell) (left right : Term Cell) :
    Reaches store (.pair left right) ↔ Reaches store left ∨ Reaches store right := by
  constructor
  · intro observed
    cases observed with
    | left child => exact Or.inl child
    | right child => exact Or.inr child
  · rintro (child | child)
    · exact .left child
    · exact .right child

/-- Full finite substitution exposes exactly the marked constructor paths. -/
theorem substitution_reaches_iff {store : Store Cell} {term image : Term Cell}
    (observed : Substitutes store term image) :
    Reaches store term ↔ marked image = true := by
  induction observed with
  | literal flag => exact reaches_literal_iff store flag
  | @unbound cell absent =>
      rw [reaches_iff_frontier store (.var cell)]
      simp [marked, support, absent]
  | @binding cell source result bound _ ih =>
      rw [reaches_iff_frontier store (.var cell)]
      simpa [marked, support, bound] using ih
  | pair _ _ ihLeft ihRight =>
      rw [reaches_pair_iff, ihLeft, ihRight]
      simp [marked, Bool.or_eq_true]

/-- A sound gate admitting an unbound store must inspect the supported
coordinate. The bound concerns store probes after support preparation. -/
theorem singleton_gate_requires_live_read (term : Term Cell) (cell : Cell)
    (clear : marked term = false) (single : support term = {cell})
    (reads : Finset Cell) (gate : Store Cell → Bool)
    (depends : ∀ first second : Store Cell,
      (∀ other ∈ reads, first other = second other) → gate first = gate second)
    (sound : ∀ store, gate store = true → Substitutes store term term)
    (admits : gate (fun _ => none) = true) : cell ∈ reads := by
  by_contra missing
  let empty : Store Cell := fun _ => none
  let bound : Store Cell := fun other =>
    if other = cell then some (.literal true) else none
  have agree : ∀ other ∈ reads, empty other = bound other := by
    intro other member
    have different : other ≠ cell := by
      intro same
      subst other
      exact missing member
    simp [empty, bound, different]
  have allowed : gate bound = true := (depends empty bound agree).symm.trans admits
  have present : Reaches bound term :=
    (singleton_refinement bound term cell clear single).mpr
      ⟨.literal true, by simp [bound], .literal rfl⟩
  have markedImage := (substitution_reaches_iff (sound bound allowed)).mp present
  simp [clear] at markedImage

def admitsUnbound (cell : Cell) (store : Store Cell) : Bool :=
  (store cell).isNone

theorem admitsUnbound_sound (store : Store Cell) (term : Term Cell) (cell : Cell)
    (single : support term = {cell}) (allowed : admitsUnbound cell store = true) :
    Substitutes store term term := by
  have absent : store cell = none := by
    cases found : store cell with
    | none => rfl
    | some image => simp [admitsUnbound, found] at allowed
  exact (singleton_unbound_substitution store term cell single absent term).mpr rfl

/-- The concrete admission gate attains the one-probe lower bound. -/
theorem singleton_gate_attains_bound (term : Term Cell) (cell : Cell)
    (single : support term = {cell}) :
    ∃ (reads : Finset Cell) (gate : Store Cell → Bool), reads.card = 1 ∧
      (∀ first second, (∀ other ∈ reads, first other = second other) →
        gate first = gate second) ∧
      (∀ store, gate store = true → Substitutes store term term) ∧
      gate (fun _ => none) = true := by
  refine ⟨{cell}, admitsUnbound cell, by simp, ?_, ?_, rfl⟩
  · intro first second agree
    unfold admitsUnbound
    rw [agree cell (by simp)]
  · intro store allowed
    exact admitsUnbound_sound store term cell single allowed

example : Substitutes (fun _ : Nat => none) (repeated 7 32) (repeated 7 32) :=
  (singleton_unbound_substitution _ _ 7 (repeated_support 7 32) rfl _).mpr rfl

/-- A later binding invalidates an earlier unbound verdict. -/
example : ¬ Substitutes (fun _ : Nat => some (.literal true))
    (.var 7) (.var 7) := by
  intro observed
  cases observed with
  | unbound absent => simp at absent
  | binding bound image =>
      cases bound
      cases image

#print axioms substitutes_iff_of_support_unbound
#print axioms singleton_unbound_substitution
#print axioms substitution_reaches_iff
#print axioms singleton_gate_requires_live_read
#print axioms singleton_gate_attains_bound

end Mettapedia.Machines.ContextualCarrierSupport
