import Mettapedia.Languages.MeTTa.Experimental.NoValueZoo
import Mettapedia.PLN.RuleFamilies.QuantaleSemantics.DoubleNegationCorners

/-!
# Two designs for no-values that carry other no-values

A no-value can say why it is there, and the reason can carry other no-values.  Two
designs keep the kinds of `NoValueZoo` apart while doing so.

**Reasons** (`Reason`): a no-value of a zoo kind with its payload, or an absence inside
a larger computation caused by a list of other reasons, as an exception's cause chain.
Two absences combine by appending their reasons.

**Design Z: parameterized nulls inside computational types.**  A null of kind `k`
(`Null k`) carries a payload and the reasons it carries.  A computational type is lifted
with nulls (`Lifted T`), so code is written in direct style: application is strict and a
null argument propagates with its kind and payload (`kindOf_map`, `kindOf_bind_null`).
* **By kind or uniformly.**  A handler for one kind handles exactly that kind
  (`handle_same_kind`, `handle_other_kind`).  "Some null, whichever" is the forgetful
  view to `Option` (`Lifted.toOption`); it is a lawful projection, a monad morphism
  (`toOption_value`, `toOption_bind`, `toOption_map`), it identifies exactly the nulls
  (`toOption_eq_iff`), and a catch-all handler that ignores the null factors through it
  (`handleAny_const`).
* **Coherence.**  Equality is reflexive, nulls of different kinds or payloads differ, and
  no null equals a value (`null_ne_value`, `null_injective`).  An IEEE-style comparison,
  false whenever a null is involved, is not reflexive (`nanEq_not_reflexive`); an
  IEEE-style maximum absorbs a null into a value (`maxNum_absorbs_null`).
* **Try, catch and case.**  `tryCatch` gives a null to the first clause that catches it
  and raises an uncaught null again with its kind and reason intact (`tryCatch_reraise`,
  `tryCatch_reraise_kind`, `catchKind_other`); a nested case whose default raises again
  does the same (`caseNull_reraise`).  A catch-all that ignores which null it caught
  commutes with the forgetful view (`catchAll_const_toOption`,
  `catchAll_const_respects_view`); one that examines the kind does not
  (`catchAll_by_kind_not_view`).
* **Zero answers are not a null.**  The explicit observer of a computation's answers fires
  its empty branch on zero answers and never on an answer that is a null
  (`caseAnswers_zero`, `caseAnswers_null`), and keeps zero answers apart from the datum
  `Empty` (`caseAnswers_keeps_empty_datum_apart`), where a case that first turns zero
  answers into that datum identifies them (`caseViaEmptyDatum_collapses`).
* **Propositions stay null-free.**  A null at every proposition proves `False`
  (`null_at_every_proposition_inconsistent`), as does a null inhabiting every equation
  between numbers (`null_at_every_equation_inconsistent`).  Nulls at every lifted type are
  built without any assumption (`nullAt`, `lifted_nonempty`), and `Lifted` applies to
  types, not to propositions: the lifting is the marker of which types admit nulls.

**Design M: absence beside the type.**  `Typed T` is a value of `T` or the reasons it is
absent: the exception monad over lists of reasons.
* **Short-circuit**: the first absence wins (`bothShort`); it is Kleisli composition, and
  every function of the values lifts (`bind_ok`, `bind_assoc`).
* **Accumulation**: every absent argument's reasons are kept (`both`, `liftA2`, `seqA`); it
  is a lawful applicative (`seqA_identity`, `seqA_homomorphism`, `seqA_interchange`,
  `seqA_composition`).
* **They differ** (`short_circuit_ne_accumulation`), and no bind under which an absence is
  a left zero induces the accumulating application (`no_bind_accumulates`).
* **Non-collapse**: the reasons are observable, unlike a junk value (`junk_division_collapses`
  against `safeDiv_keeps_apart`) or a single dummy for every undefined result
  (`dummy_collapses` against `safeDiv_payloads_differ`, `safeDiv_ne_safeHead`).

**Evidence.**  Reading an absence's reasons as negative evidence that a value is present
(`presenceEvidence`), accumulating two absences is evidence revision
(`accumulation_is_revision`), and on the four corners it is the knowledge join
(`accumulation_corners`).  Short-circuit loses the second reasons
(`shortCircuit_not_revision`), and a present argument's support is not evidence for the
combined value (`present_absent_not_revision`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Experimental.NullDesigns

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.RuleFamilies.QuantaleSemantics.DoubleNegationCorners
open Mettapedia.Languages.MeTTa.Experimental.NoValueZoo (Kind sym)

universe u

/-! ## Reasons -/

/-- Why a value is absent. -/
inductive Reason where
  /-- A no-value of kind `k` with its payload. -/
  | null (k : Kind) (payload : Pattern)
  /-- An absence in `context`, caused by the reasons `inner`. -/
  | cause (inner : List Reason) (context : Pattern)

/-! ## Design Z: parameterized nulls inside computational types -/

/-- A null of kind `k`: its payload and the reasons it carries. -/
structure Null (k : Kind) where
  payload : Pattern
  carries : List Reason

/-- Some null, with its kind. -/
abbrev AnyNull := Σ k : Kind, Null k

/-- A null seen as some null; its kind is kept in the pair. -/
def Null.forget {k : Kind} (n : Null k) : AnyNull :=
  ⟨k, n⟩

/-- A computational type lifted with parameterized nulls. -/
inductive Lifted (T : Type u) : Type u where
  | value (v : T)
  | null (n : AnyNull)

namespace Lifted

variable {T A B C : Type u}

/-- Strict application: a null argument propagates. -/
def map (f : A → B) : Lifted A → Lifted B
  | .value a => .value (f a)
  | .null n => .null n

/-- Strict sequencing. -/
def bind (x : Lifted A) (f : A → Lifted B) : Lifted B :=
  match x with
  | .value a => f a
  | .null n => .null n

/-- The kind of a null, if it is one. -/
def kindOf? : Lifted T → Option Kind
  | .value _ => none
  | .null n => some n.1

/-- **"Some null, I don't care which"**: the forgetful view. -/
def toOption : Lifted T → Option T
  | .value v => some v
  | .null _ => none

/-- A null. -/
def IsNull : Lifted T → Prop
  | .value _ => False
  | .null _ => True

theorem kindOf_map (f : A → B) (x : Lifted A) : (x.map f).kindOf? = x.kindOf? := by
  cases x <;> rfl

/-- **The kind is preserved** through strict sequencing. -/
theorem kindOf_bind_null (n : AnyNull) (f : A → Lifted B) :
    ((Lifted.null n : Lifted A).bind f).kindOf? = some n.1 :=
  rfl

theorem null_forget_kind {k : Kind} (n : Null k) : (Lifted.null n.forget : Lifted T).kindOf? = some k :=
  rfl

/-! ### The forgetful view is a lawful projection -/

theorem toOption_value (v : T) : (Lifted.value v).toOption = some v :=
  rfl

theorem toOption_map (f : A → B) (x : Lifted A) : (x.map f).toOption = x.toOption.map f := by
  cases x <;> rfl

/-- **The forgetful view is a monad morphism to `Option`.** -/
theorem toOption_bind (x : Lifted A) (f : A → Lifted B) :
    (x.bind f).toOption = x.toOption.bind fun a => (f a).toOption := by
  cases x <;> rfl

/-- **It identifies exactly the nulls.** -/
theorem toOption_eq_iff (x y : Lifted T) :
    x.toOption = y.toOption ↔ x = y ∨ (x.IsNull ∧ y.IsNull) := by
  cases x with
  | value a =>
      cases y with
      | value b => simp [toOption, IsNull]
      | null m => simp [toOption, IsNull]
  | null n =>
      cases y with
      | value b => simp [toOption, IsNull]
      | null m => simp [toOption, IsNull]

/-! ### Handling by kind, and uniformly -/

/-- Handle the nulls of kind `k`, leaving the others. -/
def handle (k : Kind) (h : Null k → T) : Lifted T → Lifted T
  | .value v => .value v
  | .null ⟨k', n⟩ => if equal : k' = k then .value (h (equal ▸ n)) else .null ⟨k', n⟩

/-- Handle every null the same way: the catch-all pattern. -/
def handleAny (h : AnyNull → T) : Lifted T → T
  | .value v => v
  | .null n => h n

theorem handle_same_kind (k : Kind) (h : Null k → T) (n : Null k) :
    (Lifted.null n.forget).handle k h = .value (h n) := by
  simp [handle, Null.forget]

theorem handle_other_kind {k k' : Kind} (h : Null k → T) (n : Null k') (different : k' ≠ k) :
    (Lifted.null n.forget).handle k h = .null n.forget := by
  simp [handle, Null.forget, different]

/-- A catch-all that ignores which null it caught factors through the forgetful view. -/
theorem handleAny_const (d : T) (x : Lifted T) : x.handleAny (fun _ => d) = x.toOption.getD d := by
  cases x <;> rfl

/-! ### Coherence -/

theorem null_ne_value (n : AnyNull) (v : T) : (Lifted.null n : Lifted T) ≠ .value v :=
  fun equal => by cases equal

theorem null_injective {n m : AnyNull} (equal : (Lifted.null n : Lifted T) = .null m) : n = m := by
  cases equal
  rfl

/-- An IEEE-style comparison: false whenever a null is involved. -/
def nanEq : Lifted ℕ → Lifted ℕ → Bool
  | .value a, .value b => a == b
  | _, _ => false

/-- **Such a comparison is not reflexive.** -/
theorem nanEq_not_reflexive (n : AnyNull) : nanEq (.null n) (.null n) = false :=
  rfl

/-- An IEEE-style maximum, which returns the other operand when one is a null. -/
def maxNum : Lifted ℕ → Lifted ℕ → Lifted ℕ
  | .null _, y => y
  | x, .null _ => x
  | .value a, .value b => .value (max a b)

/-- **It absorbs a null into a value**: the absence disappears. -/
theorem maxNum_absorbs_null (n : AnyNull) : maxNum (.null n) (.value 1) = .value 1 :=
  rfl

end Lifted

/-! ### Try, catch and case on nulls -/

/-- A catch clause: which nulls it catches, and what it does with them. -/
structure Clause (T : Type u) where
  catches : AnyNull → Bool
  handler : AnyNull → Lifted T

/-- The clause catching every null. -/
def Clause.catchAll {T : Type u} (handler : AnyNull → Lifted T) : Clause T :=
  ⟨fun _ => true, handler⟩

/-- The clause catching the nulls of kind `k`. -/
def Clause.catchKind {T : Type u} (k : Kind) (handler : AnyNull → Lifted T) : Clause T :=
  ⟨fun n => decide (n.1 = k), handler⟩

/-- `try`: the first clause that catches the null handles it; a null no clause catches is
raised again unchanged. -/
def tryCatch {T : Type u} (x : Lifted T) (clauses : List (Clause T)) : Lifted T :=
  match x with
  | .value v => .value v
  | .null n =>
      match clauses.find? (fun clause => clause.catches n) with
      | some clause => clause.handler n
      | none => .null n

/-- A nested case: a value, or some null whose kind the handler can examine. -/
def caseNull {T : Type u} {R : Type u} (x : Lifted T) (onValue : T → R) (onNull : AnyNull → R) : R :=
  match x with
  | .value v => onValue v
  | .null n => onNull n

namespace TryLaws

variable {T : Type u}

theorem tryCatch_value (v : T) (clauses : List (Clause T)) :
    tryCatch (.value v) clauses = .value v :=
  rfl

/-- **Raising again preserves kind and reason.** -/
theorem tryCatch_reraise (n : AnyNull) (clauses : List (Clause T))
    (uncaught : ∀ clause ∈ clauses, clause.catches n = false) :
    tryCatch (.null n) clauses = .null n := by
  simp only [tryCatch]
  rw [List.find?_eq_none.mpr (by simpa using uncaught)]

theorem tryCatch_reraise_kind (n : AnyNull) (clauses : List (Clause T))
    (uncaught : ∀ clause ∈ clauses, clause.catches n = false) :
    (tryCatch (.null n) clauses).kindOf? = some n.1 := by
  rw [tryCatch_reraise n clauses uncaught]
  rfl

/-- A clause for one kind does not catch another kind, which is raised again intact. -/
theorem catchKind_other (k : Kind) (handler : AnyNull → Lifted T) (n : AnyNull)
    (different : n.1 ≠ k) : tryCatch (.null n) [Clause.catchKind k handler] = .null n :=
  tryCatch_reraise n _ (by simp [Clause.catchKind, different])

/-- **A catch-all handler that ignores which null it caught commutes with the forgetful
view**: the result's view is the view of the input, defaulted. -/
theorem catchAll_const_toOption (d : T) (x : Lifted T) :
    (tryCatch x [Clause.catchAll fun _ => .value d]).toOption = some (x.toOption.getD d) := by
  cases x <;> rfl

/-- Hence it gives the same result on any two inputs with the same view. -/
theorem catchAll_const_respects_view (d : T) {x y : Lifted T} (same : x.toOption = y.toOption) :
    tryCatch x [Clause.catchAll fun _ => .value d] = tryCatch y [Clause.catchAll fun _ => .value d] := by
  cases x <;> cases y <;> simp_all [tryCatch, Lifted.toOption, Clause.catchAll]

/-- Negative control: a catch-all that examines the kind does not factor through the
forgetful view: two nulls with the same view are handled differently. -/
theorem catchAll_by_kind_not_view :
    ∃ x y : Lifted Bool, x.toOption = y.toOption ∧
      tryCatch x [Clause.catchAll fun n => .value (decide (n.1 = .errorValue))] ≠
        tryCatch y [Clause.catchAll fun n => .value (decide (n.1 = .errorValue))] := by
  refine ⟨.null ⟨.errorValue, ⟨sym "a", []⟩⟩, .null ⟨.inertCall, ⟨sym "a", []⟩⟩, rfl, ?_⟩
  simp [tryCatch, Clause.catchAll]

/-- **A nested case whose default raises again preserves kind and reason.** -/
theorem caseNull_reraise (n : AnyNull) (handled : Kind → Bool) (handler : AnyNull → Lifted T)
    (unhandled : handled n.1 = false) :
    caseNull (.null n : Lifted T) Lifted.value
      (fun m => if handled m.1 then handler m else .null m) = .null n := by
  simp [caseNull, unhandled]

end TryLaws

/-! ### Zero answers are not a null -/

/-- The explicit observer of zero answers: a computation's answers, each a value or a
null, or none at all. -/
def caseAnswers {T : Type u} {R : Type u} (answers : Multiset (Lifted T)) (onNone : R)
    (onAnswer : Lifted T → R) : Multiset R :=
  if Multiset.card answers = 0 then {onNone} else answers.map onAnswer

/-- **Zero answers fire the observer's empty branch; an answer that is a null does not.** -/
theorem caseAnswers_zero {T R : Type u} (onNone : R) (onAnswer : Lifted T → R) :
    caseAnswers (0 : Multiset (Lifted T)) onNone onAnswer = {onNone} :=
  rfl

theorem caseAnswers_null {T R : Type u} (n : AnyNull) (onNone : R) (onAnswer : Lifted T → R) :
    caseAnswers ({.null n} : Multiset (Lifted T)) onNone onAnswer = {onAnswer (.null n)} := by
  simp [caseAnswers]

/-- The datum `Empty` as an answer. -/
def isEmptyDatum : Lifted Pattern → Bool
  | .value answer => answer == NoValueZoo.emptyAtom
  | .null _ => false

/-- A case that turns zero answers into the datum `Empty` before matching, as HE's does. -/
def caseViaEmptyDatum {R : Type u} (answers : Multiset (Lifted Pattern))
    (onEmpty : R) (onAnswer : Lifted Pattern → R) : Multiset R :=
  (if Multiset.card answers = 0 then {Lifted.value NoValueZoo.emptyAtom} else answers).map
    fun answer => if isEmptyDatum answer then onEmpty else onAnswer answer

/-- **That case identifies zero answers with the datum `Empty`.** -/
theorem caseViaEmptyDatum_collapses {R : Type u} (onEmpty : R) (onAnswer : Lifted Pattern → R) :
    caseViaEmptyDatum 0 onEmpty onAnswer = caseViaEmptyDatum {.value NoValueZoo.emptyAtom} onEmpty onAnswer := by
  simp [caseViaEmptyDatum, isEmptyDatum]

/-- **The explicit observer keeps them apart**: zero answers and the datum `Empty` as an
answer fire different branches. -/
theorem caseAnswers_keeps_empty_datum_apart :
    caseAnswers (0 : Multiset (Lifted Pattern)) "zero answers" (fun _ => "an answer") ≠
      caseAnswers {.value NoValueZoo.emptyAtom} "zero answers" (fun _ => "an answer") := by
  simp [caseAnswers]


/-! ### Propositions stay null-free -/

/-- **Negative control**: a null at every proposition proves `False`. -/
theorem null_at_every_proposition_inconsistent (nullAt : ∀ P : Prop, P) : False :=
  nullAt False

/-- **Negative control**: a null inhabiting every equation between numbers refutes
`0 ≠ 1`. -/
theorem null_at_every_equation_inconsistent (nullAt : ∀ a b : ℕ, a = b) : False :=
  absurd (nullAt 0 1) (by decide)

/-- A null of kind `zeroAnswers` with no payload. -/
def someNull : AnyNull :=
  ⟨.zeroAnswers, ⟨sym "none", []⟩⟩

/-- **Nulls at every lifted type**, built without any assumption.  `Lifted` applies to
types, not to propositions, so no proposition gains an inhabitant. -/
def nullAt (T : Type u) : Lifted T :=
  .null someNull

theorem lifted_nonempty (T : Type u) : Nonempty (Lifted T) :=
  ⟨nullAt T⟩

/-! ## Design M: absence beside the type -/

/-- A value of `T`, or the reasons it is absent. -/
abbrev Typed (T : Type u) := Except (List Reason) T

namespace Typed

variable {A B C D : Type u}

/-- Short-circuit combination: the first absence wins. -/
def bothShort (x : Typed A) (y : Typed B) : Typed (A × B) :=
  x.bind fun a => y.bind fun b => .ok (a, b)

/-- Accumulating combination: both values, or every absent argument's reasons. -/
def both : Typed A → Typed B → Typed (A × B)
  | .ok a, .ok b => .ok (a, b)
  | .error r, .ok _ => .error r
  | .ok _, .error r => .error r
  | .error r, .error r' => .error (r ++ r')

/-- Accumulating application of a two-argument function. -/
def liftA2 (f : A → B → C) (x : Typed A) (y : Typed B) : Typed C :=
  (both x y).map fun pair => f pair.1 pair.2

/-- Accumulating application of a possibly absent function. -/
def seqA (fs : Typed (A → B)) (xs : Typed A) : Typed B :=
  (both fs xs).map fun pair => pair.1 pair.2

/-! ### Short-circuit: Kleisli composition -/

theorem bind_ok (a : A) (k : A → Typed B) : (Except.ok a : Typed A).bind k = k a :=
  rfl

theorem bind_error (r : List Reason) (k : A → Typed B) :
    (Except.error r : Typed A).bind k = .error r :=
  rfl

theorem bind_assoc (x : Typed A) (k : A → Typed B) (k' : B → Typed C) :
    (x.bind k).bind k' = x.bind fun a => (k a).bind k' := by
  cases x <;> rfl

/-- Short-circuit never looks at the second argument after an absence. -/
theorem bothShort_error (r : List Reason) (y : Typed B) :
    bothShort (.error r : Typed A) y = .error r :=
  rfl

/-! ### Accumulation: a lawful applicative -/

theorem liftA2_ok (f : A → B → C) (a : A) (b : B) : liftA2 f (.ok a) (.ok b) = .ok (f a b) :=
  rfl

theorem seqA_identity (x : Typed A) : seqA (.ok id) x = x := by
  cases x <;> rfl

theorem seqA_homomorphism (f : A → B) (a : A) : seqA (.ok f) (.ok a) = .ok (f a) :=
  rfl

theorem seqA_interchange (fs : Typed (A → B)) (a : A) :
    seqA fs (.ok a) = seqA (.ok fun f => f a) fs := by
  cases fs <;> rfl

theorem seqA_composition (fs : Typed (B → C)) (gs : Typed (A → B)) (xs : Typed A) :
    seqA (seqA (seqA (.ok fun (f : B → C) (g : A → B) => f ∘ g) fs) gs) xs =
      seqA fs (seqA gs xs) := by
  cases fs <;> cases gs <;> cases xs <;> simp [seqA, both, Except.map, List.append_assoc]

/-! ### The two laws differ -/

/-- **Short-circuit and accumulation differ** when both arguments are absent. -/
theorem short_circuit_ne_accumulation (r r' : Reason) :
    bothShort (.error [r] : Typed A) (.error [r'] : Typed B) = .error [r] ∧
      both (.error [r] : Typed A) (.error [r'] : Typed B) = .error [r, r'] :=
  ⟨rfl, rfl⟩

/-- **No bind induces accumulation**: under a bind for which an absence is a left zero,
the application it induces keeps only the first absence. -/
theorem no_bind_accumulates
    (bind' : ∀ {X Y : Type}, Typed X → (X → Typed Y) → Typed Y)
    (leftZero : ∀ {X Y : Type} (r : List Reason) (k : X → Typed Y), bind' (.error r) k = .error r)
    {r r' : List Reason} (nonempty : r' ≠ []) :
    (bind' (.error r : Typed (Unit → Unit)) fun f =>
        bind' (.error r' : Typed Unit) fun x => .ok (f x)) ≠
      seqA (.error r : Typed (Unit → Unit)) (.error r' : Typed Unit) := by
  rw [leftZero]
  have accumulated : seqA (.error r : Typed (Unit → Unit)) (.error r' : Typed Unit) =
      .error (r ++ r') := rfl
  rw [accumulated]
  intro equal
  have lengths := congrArg (fun outcome : Typed Unit => match outcome with
    | .error reasons => reasons.length
    | .ok _ => 0) equal
  simp only [List.length_append] at lengths
  exact nonempty (List.eq_nil_of_length_eq_zero (by omega))

/-! ### Non-collapse against junk values and a single dummy -/

/-- Division that says why it has no value. -/
def safeDiv (a b : ℕ) : Typed ℕ :=
  if b = 0 then .error [.null .errorValue (.apply "division-by-zero" (List.replicate a (sym "S")))]
  else .ok (a / b)

/-- The head of a list, or why there is none. -/
def safeHead : List ℕ → Typed ℕ
  | [] => .error [.null .inertCall (.apply "head-of" [sym "Nil"])]
  | a :: _ => .ok a

/-- **A junk value collapses absence into a value**: in Lean's own arithmetic `1 / 0`
equals `0 / 1`. -/
theorem junk_division_collapses : (1 : ℕ) / 0 = (0 : ℕ) / 1 := by
  simp

/-- **The typed design keeps them apart.** -/
theorem safeDiv_keeps_apart : safeDiv 1 0 ≠ safeDiv 0 1 := by
  simp [safeDiv]

/-- A single dummy for every undefined result. -/
def dummyDiv (dummy a b : ℕ) : ℕ :=
  if b = 0 then dummy else a / b

def dummyHead (dummy : ℕ) : List ℕ → ℕ
  | [] => dummy
  | a :: _ => a

/-- **A single dummy collapses every undefinedness into one value**, whatever the cause
or the operand. -/
theorem dummy_collapses (dummy : ℕ) :
    dummyDiv dummy 1 0 = dummyDiv dummy 2 0 ∧ dummyDiv dummy 1 0 = dummyHead dummy [] := by
  simp [dummyDiv, dummyHead]

/-- The typed design keeps the payloads ... -/
theorem safeDiv_payloads_differ : safeDiv 1 0 ≠ safeDiv 2 0 := by
  simp [safeDiv, sym]

/-- ... and the kinds. -/
theorem safeDiv_ne_safeHead : safeDiv 1 0 ≠ safeHead [] := by
  simp [safeDiv, safeHead]

end Typed

/-! ## Reasons as evidence -/

/-- The evidence an outcome gives that a value is present: a value supports it once, an
absence refutes it once per reason. -/
noncomputable def presenceEvidence {T : Type u} : Typed T → BinaryEvidence
  | .ok _ => ⟨1, 0⟩
  | .error reasons => ⟨0, reasons.length⟩

variable {A B : Type u}

/-- **Accumulating two absences is evidence revision.** -/
theorem accumulation_is_revision (r r' : List Reason) :
    presenceEvidence (Typed.both (.error r : Typed A) (.error r' : Typed B)) =
      presenceEvidence (.error r : Typed A) + presenceEvidence (.error r' : Typed B) := by
  simp only [Typed.both, presenceEvidence, BinaryEvidence.hplus_def, List.length_append,
    Nat.cast_add, add_zero]

/-- **On the four corners it is the knowledge join.** -/
theorem accumulation_corners (r r' : List Reason) :
    (presenceEvidence (Typed.both (.error r : Typed A) (.error r' : Typed B)))ᶜᶜ =
      (presenceEvidence (.error r : Typed A))ᶜᶜ ⊔ (presenceEvidence (.error r' : Typed B))ᶜᶜ := by
  rw [accumulation_is_revision, compl_compl_add]

/-- Short-circuit is not revision: it drops the second absence's reasons. -/
theorem shortCircuit_not_revision (r : List Reason) {r' : List Reason} (nonempty : r' ≠ []) :
    presenceEvidence (Typed.bothShort (.error r : Typed A) (.error r' : Typed B)) ≠
      presenceEvidence (.error r : Typed A) + presenceEvidence (.error r' : Typed B) := by
  intro equal
  have negative := congrArg BinaryEvidence.neg equal
  simp only [Typed.bothShort, Except.bind, presenceEvidence, BinaryEvidence.hplus_def] at negative
  rw [← Nat.cast_add, Nat.cast_inj] at negative
  exact nonempty (List.eq_nil_of_length_eq_zero (by omega))

/-- A present argument's support is not evidence for the combined value. -/
theorem present_absent_not_revision (a : A) (r : List Reason) :
    presenceEvidence (Typed.both (.ok a : Typed A) (.error r : Typed B)) ≠
      presenceEvidence (.ok a : Typed A) + presenceEvidence (.error r : Typed B) := by
  intro equal
  have positive := congrArg BinaryEvidence.pos equal
  simp [Typed.both, presenceEvidence, BinaryEvidence.hplus_def] at positive

end Mettapedia.Languages.MeTTa.Experimental.NullDesigns
