import Mathlib.Computability.TuringDegree
import Mathlib.Computability.Halting

/-!
# Computability relative to a set of oracles

Mathlib defines `RecursiveIn O f` (a partial function recursive in the oracles
`O`) with the same constructors as `Nat.Partrec`, plus one constructor for
each oracle. Its library stops at monotonicity and substitution. This file
adds the closure properties that the reverse-mathematics files need:
composition, pairing, primitive recursion, unbounded search, and oracle
queries for sets of numbers.

Each proof below follows the corresponding unrelativized proof in Mathlib's
`Mathlib/Computability/Partrec.lean` (`Nat.Partrec.prec'`, `Partrec.bind`,
`Partrec.map`, `Partrec.nat_rec`, `Partrec.comp`, `Computable.pair`,
`Computable.nat_rec`, `Partrec.rfind`): the constructors of
`Nat.RecursiveIn` are the constructors of `Nat.Partrec`, so the encodings and
the `of_eq` arguments carry over unchanged.

* `RelComp.comp`, `RelComp.pair`, `RelComp.comp₂`: composition and pairing.
* `RelComp.ofPrimrec₂`: a primitive recursive function of oracle-computable
  arguments is oracle-computable.
* `RelComp.nat_rec`: primitive recursion over the naturals.
* `RelComp.rfind`: unbounded search.
* `RelComp.mem`: the membership test of a set is computable in its
  characteristic function.

## References

* P. Odifreddi, *Classical Recursion Theory*, North-Holland, 1989 (relative
  computability, Chapter III).
* Mathlib, `Mathlib/Computability/RecursiveIn.lean` and
  `Mathlib/Computability/Partrec.lean`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ReverseMathematics

open Encodable Part

/-- The characteristic function of a set of naturals, as a total partial
function with values `1` (member) and `0` (non-member). -/
noncomputable def charFn (A : Set ℕ) : ℕ →. ℕ := by
  classical
  exact fun n => Part.some (if n ∈ A then 1 else 0)

theorem charFn_apply (A : Set ℕ) (n : ℕ) [Decidable (n ∈ A)] :
    charFn A n = Part.some (if n ∈ A then 1 else 0) := by
  unfold charFn
  congr 1
  split_ifs <;> rfl

namespace RelComp

variable {α β γ δ σ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]
  [Primcodable δ] [Primcodable σ]
variable {O : Set (ℕ →. ℕ)}

/-- Extensionally equal total functions are computable in the same oracles. -/
theorem of_eq {f g : α → σ} (hf : ComputableIn O f) (H : ∀ a, f a = g a) : ComputableIn O g :=
  (funext H : f = g) ▸ hf

/-- Relativized `Nat.Partrec.prec'`. -/
theorem nat_prec' {f g h : ℕ →. ℕ} (hf : Nat.RecursiveIn O f) (hg : Nat.RecursiveIn O g)
    (hh : Nat.RecursiveIn O h) :
    Nat.RecursiveIn O fun a => (f a).bind fun n => n.rec (g a)
      fun y IH => do {let i ← IH; h (Nat.pair a (Nat.pair y i))} :=
  ((Nat.RecursiveIn.prec hg hh).comp
      (Nat.RecursiveIn.pair (Nat.Partrec.some.recursiveIn) hf)).of_eq fun a =>
    ext fun s => by simp [Seq.seq]

set_option backward.isDefEq.respectTransparency false in
/-- Relativized `Partrec.bind`. -/
theorem bind {f : α →. β} {g : α → β →. σ} (hf : RecursiveIn O f) (hg : RecursiveIn₂ O g) :
    RecursiveIn O fun a => (f a).bind (g a) :=
  (Nat.RecursiveIn.comp hg (Nat.RecursiveIn.pair Nat.Partrec.some.recursiveIn hf)).of_eq
    fun n => by
      rcases e : decode (α := α) n <;> simp [Seq.seq, e, encodek]

/-- Relativized `Partrec.map`. -/
theorem map {f : α →. β} {g : α → β → σ} (hf : RecursiveIn O f) (hg : ComputableIn₂ O g) :
    RecursiveIn O fun a => (f a).map (g a) := by
  simpa [bind_some_eq_map] using bind (g := fun a x => Part.some (g a x)) hf hg

/-- Relativized `Partrec.comp`. -/
theorem comp {f : β →. σ} {g : α → β} (hf : RecursiveIn O f) (hg : ComputableIn O g) :
    RecursiveIn O fun a => f (g a) :=
  (Nat.RecursiveIn.comp hf hg).of_eq fun n => by
    simp only [map_some, bind_eq_bind]
    rcases decode (α := α) n with - | a <;> simp [encodek]

/-- Composition of oracle-computable total functions. -/
theorem comp' {f : β → σ} {g : α → β} (hf : ComputableIn O f) (hg : ComputableIn O g) :
    ComputableIn O fun a => f (g a) :=
  comp (f := fun b => Part.some (f b)) (g := g) hf hg

set_option backward.isDefEq.respectTransparency false in
/-- Relativized `Computable.pair`. -/
theorem pair {f : α → β} {g : α → γ} (hf : ComputableIn O f) (hg : ComputableIn O g) :
    ComputableIn O fun a => (f a, g a) :=
  (Nat.RecursiveIn.pair hf hg).of_eq fun n => by
    cases decode (α := α) n <;> simp [Seq.seq]

/-- A binary oracle-computable function of two oracle-computable arguments. -/
theorem comp₂ {f : β → γ → σ} {g : α → β} {h : α → γ} (hf : ComputableIn₂ O f)
    (hg : ComputableIn O g) (hh : ComputableIn O h) :
    ComputableIn O fun a => f (g a) (h a) :=
  comp' (f := fun p : β × γ => f p.1 p.2) hf (pair hg hh)

/-- A computable function of an oracle-computable argument. -/
theorem ofComputable {f : β → σ} {g : α → β} (hf : Computable f) (hg : ComputableIn O g) :
    ComputableIn O fun a => f (g a) :=
  comp' hf.computableIn hg

/-- A primitive recursive binary function of two oracle-computable arguments. -/
theorem ofPrimrec₂ {f : β → γ → σ} {g : α → β} {h : α → γ} (hf : Primrec₂ f)
    (hg : ComputableIn O g) (hh : ComputableIn O h) :
    ComputableIn O fun a => f (g a) (h a) :=
  comp₂ hf.computableIn₂ hg hh

/-- A primitive recursive function of an oracle-computable argument. -/
theorem ofPrimrec {f : β → σ} {g : α → β} (hf : Primrec f) (hg : ComputableIn O g) :
    ComputableIn O fun a => f (g a) :=
  comp' hf.computableIn hg

theorem const (s : σ) : ComputableIn O fun _ : α => s :=
  ComputableIn.const s

theorem id' : ComputableIn O fun a : α => a :=
  ComputableIn.id

theorem fst : ComputableIn O (@Prod.fst α β) :=
  ComputableIn.fst

theorem snd : ComputableIn O (@Prod.snd α β) :=
  ComputableIn.snd

/-- Relativized `Partrec.nat_rec`. -/
theorem part_nat_rec {f : α → ℕ} {g : α →. σ} {h : α → ℕ × σ →. σ} (hf : ComputableIn O f)
    (hg : RecursiveIn O g) (hh : RecursiveIn₂ O h) :
    RecursiveIn O fun a => (f a).rec (g a) fun y IH => IH.bind fun i => h a (y, i) :=
  (nat_prec' hf hg hh).of_eq fun n => by
    rcases e : decode (α := α) n with - | a
    · simp
    · simp only [coe_some, bind_some]
      induction f a <;> simp_all

/-- Relativized `Computable.nat_rec`: primitive recursion. -/
theorem nat_rec {f : α → ℕ} {g : α → σ} {h : α → ℕ × σ → σ} (hf : ComputableIn O f)
    (hg : ComputableIn O g) (hh : ComputableIn₂ O h) :
    ComputableIn O fun a => Nat.rec (motive := fun _ => σ) (g a) (fun y IH => h a (y, IH)) (f a) :=
  (part_nat_rec (g := fun a => Part.some (g a)) (h := fun a p => Part.some (h a p)) hf hg hh).of_eq
    fun a => by simp; induction f a <;> simp [*]

set_option backward.isDefEq.respectTransparency false in
/-- Relativized `Partrec.rfind`: unbounded search. -/
theorem rfind {p : α → ℕ →. Bool} (hp : RecursiveIn₂ O p) :
    RecursiveIn O fun a => Nat.rfind (p a) :=
  (Nat.RecursiveIn.rfind <|
        map hp ((Primrec.dom_bool fun b => cond b 0 1).comp Primrec.snd).to₂.computableIn₂).of_eq
    fun n => by
    rcases e : decode (α := α) n <;> simp [e, Nat.rfind_zero_none, map_map, map_id']

/-- Unbounded search for a total oracle-computable Boolean predicate. -/
theorem rfind' {p : α → ℕ → Bool} (hp : ComputableIn₂ O p) :
    RecursiveIn O fun a => Nat.rfind fun n => Part.some (p a n) :=
  rfind hp

/-- **An oracle answers membership in its set.** -/
theorem mem {A : Set ℕ} [DecidablePred (· ∈ A)] (h : charFn A ∈ O) :
    ComputableIn O fun n : ℕ => decide (n ∈ A) := by
  have oracle : Nat.RecursiveIn O (charFn A) := Nat.RecursiveIn.oracle _ h
  unfold ComputableIn RecursiveIn
  refine oracle.of_eq fun n => ?_
  rw [charFn_apply]
  by_cases member : n ∈ A <;> simp [member]

/-- Membership in an oracle set at an oracle-computable position. -/
theorem mem_comp {A : Set ℕ} [DecidablePred (· ∈ A)] (h : charFn A ∈ O) {f : α → ℕ}
    (hf : ComputableIn O f) : ComputableIn O fun a => decide (f a ∈ A) :=
  comp' (mem h) hf

/-- A characteristic function computed by a total Boolean decision procedure. -/
theorem charFn_of_decide {A : Set ℕ} [DecidablePred (· ∈ A)]
    (h : ComputableIn O fun n : ℕ => decide (n ∈ A)) : Nat.RecursiveIn O (charFn A) := by
  unfold ComputableIn RecursiveIn at h
  refine h.of_eq fun n => ?_
  rw [charFn_apply]
  by_cases member : n ∈ A <;> simp [member]

/-- Conversely, the decision procedure of a set is computable in any oracle
set that computes its characteristic function. -/
theorem decide_of_charFn {A : Set ℕ} [DecidablePred (· ∈ A)] (h : Nat.RecursiveIn O (charFn A)) :
    ComputableIn O fun n : ℕ => decide (n ∈ A) := by
  unfold ComputableIn RecursiveIn
  refine h.of_eq fun n => ?_
  rw [charFn_apply]
  by_cases member : n ∈ A <;> simp [member]

end RelComp

/-! ## Examples -/

section Examples

open RelComp

/-- Positive: the even numbers are decided relative to no oracle at all. -/
example : ComputableIn (∅ : Set (ℕ →. ℕ)) fun n : ℕ => decide (n % 2 = 0) :=
  ofPrimrec₂ Primrec.eq.decide (ofPrimrec₂ Primrec.nat_mod id' (const 2)) (const 0)

open Classical in
/-- Negative: a function recursive in no oracle is partial recursive, so the
halting problem's decision procedure is not computable in the empty oracle
set. -/
example : ¬ ComputableIn (∅ : Set (ℕ →. ℕ))
    fun c : Nat.Partrec.Code => decide ((Nat.Partrec.Code.eval c 0).Dom) := by
  intro h
  exact ComputablePred.halting_problem 0 ⟨fun _ => Classical.propDecidable _,
    (recursiveIn_empty_iff.mp h : Partrec _)⟩

end Examples

end Mettapedia.Logic.ReverseMathematics
