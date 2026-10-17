import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Fourier–Motzkin elimination for linear real arithmetic

Rational linear inequalities, decided by Fourier–Motzkin elimination. The method
is the one introduced by Joseph Fourier and put in its modern form by Theodore
S. Motzkin, *Beiträge zur Theorie der linearen Ungleichungen* (1936).

An atom in `n` variables is `c · x + d ≤ 0` or `c · x + d < 0` with `c` and `d`
rational. Eliminating the outermost variable replaces each pair of a lower and
an upper bound by one inequality on the remaining variables, and drops a bound
with coefficient zero onto those variables. At zero variables the result is a
comparison of rational constants. The same comparison is true in every ordered
field, and therefore in every ordered real closed field in the sense of
`IsRealClosed` together with its order.

`Formula` is that atom closed under conjunction, negation, and existential
quantification. `Formula.eliminate` puts a quantifier-free matrix into
disjunctive normal form and runs one Fourier–Motzkin pass on every conjunction,
from the inside outward. `linearBubble` decides every closed sentence.
A formula that still has a free variable receives `none`.

`Sentence` remains the existential-conjunction entry. A disjunction or a
universal sentence in that entry returns `none`.

## Open goal

Tarski elimination for polynomial inequalities. Alfred Tarski, *A Decision
Method for Elementary Algebra and Geometry* (1951). The missing statement is:
for a polynomial `p` with rational coefficients in `n + 1` variables, a
quantifier-free formula `φ` of the ordered-field language in `n` variables such
that, in every ordered real closed field, `(∃ x, p(x ∷ e) > 0) ↔ φ(e)`. The
two axioms of `IsRealClosed` that this linear theory does not use are that
every element or its negative is a square, and that every odd-degree polynomial
has a root.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Arithmetic.FourierMotzkin

inductive Coeff : Nat → Type where
  | nil : Coeff 0
  | cons : {n : Nat} → ℚ → Coeff n → Coeff (n + 1)
  deriving DecidableEq

namespace Coeff

def scale {n : Nat} (q : ℚ) : Coeff n → Coeff n
  | nil => nil
  | cons c cs => cons (q * c) (scale q cs)

def add {n : Nat} : Coeff n → Coeff n → Coeff n
  | nil, nil => nil
  | cons a as, cons b bs => cons (a + b) (add as bs)

def dot {R : Type} [Field R] {n : Nat} : Coeff n → (Fin n → R) → R
  | nil, _ => 0
  | cons c cs, env => (c : R) * env 0 + dot cs (fun i => env i.succ)

end Coeff

structure LinTerm (n : Nat) where
  coeff : Coeff n
  const : ℚ
  deriving DecidableEq

namespace LinTerm

def scale {n : Nat} (q : ℚ) (t : LinTerm n) : LinTerm n where
  coeff := t.coeff.scale q
  const := q * t.const

def sub {n : Nat} (t s : LinTerm n) : LinTerm n where
  coeff := t.coeff.add (s.coeff.scale (-1))
  const := t.const - s.const

end LinTerm

inductive Rel where
  | le
  | lt
  deriving DecidableEq

structure Atom (n : Nat) where
  term : LinTerm n
  rel : Rel
  deriving DecidableEq

def envCons {R : Type} {n : Nat} (x : R) (e : Fin n → R) : Fin (n + 1) → R :=
  Fin.cases x e

def envTail {R : Type} {n : Nat} (env : Fin (n + 1) → R) : Fin n → R :=
  fun i => env i.succ

structure Bound (n : Nat) where
  strict : Bool
  term : LinTerm n
  deriving DecidableEq

inductive Piece (n : Nat) where
  | keep (a : Atom n)
  | lower (b : Bound n)
  | upper (b : Bound n)

def classify {n : Nat} (a : Atom (n + 1)) : Piece n :=
  match a.term.coeff with
  | .cons h cs =>
    let tail : LinTerm n := ⟨cs, a.term.const⟩
    if h = 0 then .keep ⟨tail, a.rel⟩
    else if 0 < h then .upper ⟨decide (a.rel = Rel.lt), tail.scale (-h⁻¹)⟩
    else .lower ⟨decide (a.rel = Rel.lt), tail.scale (-h⁻¹)⟩

def cross {n : Nat} (lo hi : Bound n) : Atom n where
  term := lo.term.sub hi.term
  rel := if lo.strict || hi.strict then Rel.lt else Rel.le

def residuals {n : Nat} (atoms : List (Atom (n + 1))) : List (Atom n) :=
  match atoms with
  | [] => []
  | a :: as =>
    match classify a with
    | .keep r => r :: residuals as
    | .lower _ => residuals as
    | .upper _ => residuals as
termination_by structural atoms

def lowers {n : Nat} (atoms : List (Atom (n + 1))) : List (Bound n) :=
  match atoms with
  | [] => []
  | a :: as =>
    match classify a with
    | .lower b => b :: lowers as
    | .keep _ => lowers as
    | .upper _ => lowers as
termination_by structural atoms

def uppers {n : Nat} (atoms : List (Atom (n + 1))) : List (Bound n) :=
  match atoms with
  | [] => []
  | a :: as =>
    match classify a with
    | .upper b => b :: uppers as
    | .keep _ => uppers as
    | .lower _ => uppers as
termination_by structural atoms

def project {n : Nat} (atoms : List (Atom (n + 1))) : List (Atom n) :=
  match atoms with
  | [] => []
  | a :: as =>
    match classify a with
    | .keep r => r :: project as
    | .lower b => project as ++ (uppers as).map (fun hi => cross b hi)
    | .upper b => project as ++ (lowers as).map (fun lo => cross lo b)
termination_by structural atoms

def constHolds (a : Atom 0) : Bool :=
  match a.term.coeff, a.rel with
  | .nil, .le => decide (a.term.const ≤ (0 : ℚ))
  | .nil, .lt => decide (a.term.const < (0 : ℚ))

/-- Primitive recursion on the variable count, so the controls reduce in the kernel.
A well-founded match on an implicit arity does not. -/
def decideSat {n : Nat} (atoms : List (Atom n)) : Bool :=
  Nat.recOn (motive := fun k => List (Atom k) → Bool) n
    (fun atoms => atoms.all constHolds)
    (fun _ ih atoms => ih (project atoms))
    atoms

@[simp] theorem decideSat_zero (atoms : List (Atom 0)) :
    decideSat atoms = atoms.all constHolds := rfl

@[simp] theorem decideSat_succ {n : Nat} (atoms : List (Atom (n + 1))) :
    decideSat atoms = decideSat (project atoms) := rfl

inductive Matrix : Nat → Type where
  | conj {n : Nat} (atoms : List (Atom n)) : Matrix n
  | disj {n : Nat} (φ ψ : Matrix n) : Matrix n

inductive Sentence where
  | exists_ {n : Nat} (φ : Matrix n)
  | forall_ {n : Nat} (φ : Matrix n)

def decideSentence : Sentence → Option Bool
  | .exists_ (.conj atoms) => some (decideSat atoms)
  | .exists_ (.disj _ _) => none
  | .forall_ _ => none

structure Bubble where
  name : String
  decide : Sentence → Option Bool

def realLinearBubble : Bubble where
  name := "Fourier–Motzkin existential linear arithmetic"
  decide := decideSentence

/-! ## The linear language -/

inductive Formula : Nat → Type where
  | bot : {n : Nat} → Formula n
  | atom : {n : Nat} → Atom n → Formula n
  | conj : {n : Nat} → Formula n → Formula n → Formula n
  | neg : {n : Nat} → Formula n → Formula n
  | ex : {n : Nat} → Formula (n + 1) → Formula n

def Formula.quantifierFree : {n : Nat} → (φ : Formula n) → Bool
  | _, .bot => true
  | _, .atom _ => true
  | _, .conj left right =>
      Formula.quantifierFree left && Formula.quantifierFree right
  | _, .neg body => Formula.quantifierFree body
  | _, .ex _ => false
  termination_by structural _ φ => φ

/-- Negation of a non-strict inequality is a strict inequality of the opposite
term, and the other way round. -/
def Atom.negate {n : Nat} (a : Atom n) : Atom n where
  term := a.term.scale (-1)
  rel := match a.rel with
    | .le => .lt
    | .lt => .le

def clauseProd {α : Type} (left right : List (List α)) : List (List α) :=
  left.flatMap fun clause => right.map fun rest => clause ++ rest

theorem forall_append_pred {α : Type} {p : α → Prop} (l r : List α) :
    (∀ a ∈ l ++ r, p a) ↔ (∀ a ∈ l, p a) ∧ (∀ a ∈ r, p a) := by
  constructor
  · intro h
    exact ⟨fun a ha => h a (List.mem_append.mpr (Or.inl ha)),
      fun a ha => h a (List.mem_append.mpr (Or.inr ha))⟩
  · intro h a ha
    rcases List.mem_append.mp ha with hl | hr
    · exact h.1 a hl
    · exact h.2 a hr

theorem clauseProd_iff {α : Type} {p : α → Prop} (left right : List (List α)) :
    (∃ clause ∈ clauseProd left right, ∀ a ∈ clause, p a) ↔
      (∃ clause ∈ left, ∀ a ∈ clause, p a) ∧
        (∃ clause ∈ right, ∀ a ∈ clause, p a) := by
  constructor
  · rintro ⟨clause, hmem, hall⟩
    rw [clauseProd, List.mem_flatMap] at hmem
    rcases hmem with ⟨base, hbase, hclause⟩
    rw [List.mem_map] at hclause
    rcases hclause with ⟨rest, hrest, rfl⟩
    obtain ⟨hL, hR⟩ := (forall_append_pred (p := p) base rest).mp hall
    exact ⟨⟨base, hbase, hL⟩, ⟨rest, hrest, hR⟩⟩
  · rintro ⟨⟨base, hbase, hL⟩, ⟨rest, hrest, hR⟩⟩
    refine ⟨base ++ rest, ?_, (forall_append_pred (p := p) base rest).mpr ⟨hL, hR⟩⟩
    rw [clauseProd, List.mem_flatMap]
    exact ⟨base, hbase, List.mem_map.mpr ⟨rest, hrest, rfl⟩⟩

/-- Disjunctive normal form. `positive = false` builds the negation.
An empty clause list is false. A list containing the empty clause is true.
Negation of an atom is `Atom.negate`, so every clause is a conjunction of atoms. -/
def toDnf {n : Nat} (positive : Bool) : Formula n → List (List (Atom n))
  | .bot =>
      match positive with
      | true => []
      | false => [[]]
  | .atom a =>
      match positive with
      | true => [[a]]
      | false => [[a.negate]]
  | .conj left right =>
      match positive with
      | true => clauseProd (toDnf true left) (toDnf true right)
      | false => toDnf false left ++ toDnf false right
  | .neg body =>
      toDnf (match positive with | true => false | false => true) body
  | .ex _ => []
  termination_by structural φ => φ

def finConj {n : Nat} : List (Formula n) → Formula n
  | [] => .neg .bot
  | f :: fs => .conj f (finConj fs)
  termination_by structural fs => fs

def finDisj {n : Nat} : List (Formula n) → Formula n
  | [] => .bot
  | f :: fs => .neg (.conj (.neg f) (.neg (finDisj fs)))
  termination_by structural fs => fs

theorem finDisj_qf {n : Nat} :
    (fs : List (Formula n)) → (∀ f ∈ fs, f.quantifierFree = true) →
      (finDisj fs).quantifierFree = true
  | [], _ => by simp [finDisj, Formula.quantifierFree]
  | f :: fs, h => by
      have hf := h f List.mem_cons_self
      have hfs := finDisj_qf fs fun g hg => h g (List.mem_cons_of_mem _ hg)
      simp [finDisj, Formula.quantifierFree, hf, hfs]

theorem finConj_qf {n : Nat} :
    (fs : List (Formula n)) → (∀ f ∈ fs, f.quantifierFree = true) →
      (finConj fs).quantifierFree = true
  | [], _ => by simp [finConj, Formula.quantifierFree]
  | f :: fs, h => by
      have hf := h f List.mem_cons_self
      have hfs := finConj_qf fs fun g hg => h g (List.mem_cons_of_mem _ hg)
      simp [finConj, Formula.quantifierFree, hf, hfs]

/-- One existential quantifier over a quantifier-free matrix: disjunctive normal
form, then Fourier–Motzkin on each conjunction. -/
def Formula.cooper {n : Nat} (φ : Formula (n + 1)) : Formula n :=
  finDisj ((toDnf true φ).map fun clause =>
    finConj ((project clause).map Formula.atom))

theorem Formula.cooper_qf {n : Nat} (φ : Formula (n + 1)) :
    (Formula.cooper φ).quantifierFree = true := by
  rw [Formula.cooper]
  refine finDisj_qf _ ?_
  intro form hmem
  obtain ⟨_clause, _, rfl⟩ := List.mem_map.mp hmem
  refine finConj_qf _ ?_
  intro piece hpiece
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hpiece
  simp [Formula.quantifierFree]

def Formula.eliminate : {n : Nat} → (φ : Formula n) → Formula n
  | _, .bot => .bot
  | _, .atom a => .atom a
  | _, .conj a b => .conj (Formula.eliminate a) (Formula.eliminate b)
  | _, .neg a => .neg (Formula.eliminate a)
  | _, .ex body => Formula.cooper (Formula.eliminate body)
  termination_by structural _ φ => φ

theorem Formula.eliminate_qf : {n : Nat} → (φ : Formula n) →
    φ.eliminate.quantifierFree = true
  | _, .bot => by simp [Formula.eliminate, Formula.quantifierFree]
  | _, .atom _ => by simp [Formula.eliminate, Formula.quantifierFree]
  | _, .conj a b => by
      simp [Formula.eliminate, Formula.quantifierFree,
        Formula.eliminate_qf a, Formula.eliminate_qf b]
  | _, .neg a => by
      simp [Formula.eliminate, Formula.quantifierFree, Formula.eliminate_qf a]
  | _, .ex body => by
      simp [Formula.eliminate, Formula.cooper_qf (Formula.eliminate body)]

def Formula.decideQF : Formula 0 → Bool
  | .bot => false
  | .atom a => constHolds a
  | .conj a b => Formula.decideQF a && Formula.decideQF b
  | .neg a => !Formula.decideQF a
  | .ex _ => false

/-- A Boolean for every closed sentence. A free variable receives `none`. -/
def Formula.decideClosed : {n : Nat} → Formula n → Option Bool
  | 0, φ => some φ.eliminate.decideQF
  | _ + 1, _ => none

structure LinearBubble where
  name : String
  decide : Formula 0 → Option Bool

def linearBubble : LinearBubble where
  name := "Fourier–Motzkin linear real arithmetic"
  decide := Formula.decideClosed

section Semantics

set_option linter.unusedSectionVars false

variable {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

@[simp] theorem envCons_zero {n : Nat} (x : R) (e : Fin n → R) :
    envCons x e 0 = x := by
  simp [envCons]

@[simp] theorem envCons_succ {n : Nat} (x : R) (e : Fin n → R) (i : Fin n) :
    envCons x e i.succ = e i := by
  simp [envCons]

theorem env_eq_cons {n : Nat} (env : Fin (n + 1) → R) :
    env = envCons (env 0) (envTail env) := by
  funext i
  cases i using Fin.cases with
  | zero => simp [envCons]
  | succ i => simp [envCons, envTail]

theorem dot_scale {n : Nat} (q : ℚ) (a : Coeff n) (e : Fin n → R) :
    (a.scale q).dot e = (q : R) * a.dot e := by
  induction a with
  | nil => simp [Coeff.scale, Coeff.dot]
  | cons c cs ih =>
    simp only [Coeff.scale, Coeff.dot, ih, Rat.cast_mul]
    ring

theorem dot_add {n : Nat} (a b : Coeff n) (e : Fin n → R) :
    (a.add b).dot e = a.dot e + b.dot e := by
  induction a with
  | nil =>
    cases b
    simp [Coeff.add, Coeff.dot]
  | cons c cs ih =>
    cases b with
    | cons d ds =>
      simp only [Coeff.add, Coeff.dot, ih, Rat.cast_add]
      ring

def LinTerm.eval {n : Nat} (t : LinTerm n) (env : Fin n → R) : R :=
  t.coeff.dot env + (t.const : R)

theorem eval_scale {n : Nat} (q : ℚ) (t : LinTerm n) (e : Fin n → R) :
    (t.scale q).eval e = (q : R) * t.eval e := by
  simp only [LinTerm.scale, LinTerm.eval, dot_scale, Rat.cast_mul]
  ring

theorem eval_sub {n : Nat} (t s : LinTerm n) (e : Fin n → R) :
    (t.sub s).eval e = t.eval e - s.eval e := by
  simp only [LinTerm.sub, LinTerm.eval, dot_add, dot_scale, Rat.cast_sub, Rat.cast_neg,
    Rat.cast_one]
  ring

theorem eval_cons {n : Nat} (h : ℚ) (cs : Coeff n) (k : ℚ) (x : R) (e : Fin n → R) :
    (LinTerm.mk (Coeff.cons h cs) k).eval (envCons x e) =
      (h : R) * x + (LinTerm.mk cs k).eval e := by
  simp only [LinTerm.eval, Coeff.dot, envCons_zero, envCons_succ, add_assoc]

def holds (rel : Rel) (v : R) : Prop :=
  match rel with
  | .le => v ≤ 0
  | .lt => v < 0

def Atom.sat {n : Nat} (a : Atom n) (env : Fin n → R) : Prop :=
  holds a.rel (a.term.eval env)

def allSat {n : Nat} (atoms : List (Atom n)) (env : Fin n → R) : Prop :=
  ∀ a ∈ atoms, a.sat env

theorem allSat_nil {n : Nat} (env : Fin n → R) : allSat ([] : List (Atom n)) env := by
  intro _ h
  cases h

theorem allSat_cons {n : Nat} (a : Atom n) (as : List (Atom n)) (env : Fin n → R) :
    allSat (a :: as) env ↔ a.sat env ∧ allSat as env := by
  constructor
  · intro h
    exact ⟨h a List.mem_cons_self, fun b hb => h b (List.mem_cons_of_mem _ hb)⟩
  · intro h b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact h.1
    · exact h.2 b hb

theorem allSat_append {n : Nat} (xs ys : List (Atom n)) (env : Fin n → R) :
    allSat (xs ++ ys) env ↔ allSat xs env ∧ allSat ys env := by
  constructor
  · intro h
    exact ⟨fun a ha => h a (List.mem_append_left _ ha),
      fun a ha => h a (List.mem_append_right _ ha)⟩
  · intro h a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact h.1 a ha
    · exact h.2 a ha

theorem allSat_map {n m : Nat} (f : Bound n → Atom m) (bs : List (Bound n))
    (env : Fin m → R) :
    allSat (bs.map f) env ↔ ∀ b ∈ bs, (f b).sat env := by
  constructor
  · intro h b hb
    exact h (f b) (List.mem_map.mpr ⟨b, hb, rfl⟩)
  · intro h a ha
    rcases List.mem_map.mp ha with ⟨b, hb, rfl⟩
    exact h b hb

def Bound.below {n : Nat} (b : Bound n) (x : R) (e : Fin n → R) : Prop :=
  if b.strict then b.term.eval e < x else b.term.eval e ≤ x

def Bound.above {n : Nat} (b : Bound n) (x : R) (e : Fin n → R) : Prop :=
  if b.strict then x < b.term.eval e else x ≤ b.term.eval e

theorem le_neg_iff_add_nonpos (a b : R) : a ≤ -b ↔ a + b ≤ 0 := by
  constructor <;> intro h <;> linarith

theorem lt_neg_iff_add_neg (a b : R) : a < -b ↔ a + b < 0 := by
  constructor <;> intro h <;> linarith

theorem scale_neg_inv {n : Nat} (hc : ℚ) (tail : LinTerm n) (e : Fin n → R) :
    (tail.scale (-hc⁻¹)).eval e = -tail.eval e / (hc : R) := by
  rw [eval_scale, div_eq_mul_inv, Rat.cast_neg, Rat.cast_inv]
  ring

theorem pos_le_iff {n : Nat} (hc : ℚ) (hpos : 0 < hc) (tail : LinTerm n)
    (x : R) (e : Fin n → R) :
    (hc : R) * x + tail.eval e ≤ 0 ↔ x ≤ (tail.scale (-hc⁻¹)).eval e := by
  have hcR : (0 : R) < hc := Rat.cast_pos.mpr hpos
  rw [scale_neg_inv, le_div_iff₀ hcR, mul_comm, le_neg_iff_add_nonpos]

theorem pos_lt_iff {n : Nat} (hc : ℚ) (hpos : 0 < hc) (tail : LinTerm n)
    (x : R) (e : Fin n → R) :
    (hc : R) * x + tail.eval e < 0 ↔ x < (tail.scale (-hc⁻¹)).eval e := by
  have hcR : (0 : R) < hc := Rat.cast_pos.mpr hpos
  rw [scale_neg_inv, lt_div_iff₀ hcR, mul_comm, lt_neg_iff_add_neg]

theorem neg_le_iff {n : Nat} (hc : ℚ) (hneg : hc < 0) (tail : LinTerm n)
    (x : R) (e : Fin n → R) :
    (hc : R) * x + tail.eval e ≤ 0 ↔ (tail.scale (-hc⁻¹)).eval e ≤ x := by
  have hcR : (hc : R) < 0 := by
    rw [← Rat.cast_zero]
    exact Rat.cast_lt.mpr hneg
  rw [scale_neg_inv]
  constructor
  · intro h
    have hmul : x * (hc : R) ≤ -tail.eval e := by
      simpa [mul_comm] using
        (le_neg_iff_add_nonpos ((hc : R) * x) (tail.eval e)).mpr h
    exact (div_le_iff_of_neg hcR).mpr hmul
  · intro h
    have hmul : (hc : R) * x ≤ -tail.eval e := by
      simpa [mul_comm] using (div_le_iff_of_neg hcR).mp h
    exact (le_neg_iff_add_nonpos ((hc : R) * x) (tail.eval e)).mp hmul

theorem neg_lt_iff {n : Nat} (hc : ℚ) (hneg : hc < 0) (tail : LinTerm n)
    (x : R) (e : Fin n → R) :
    (hc : R) * x + tail.eval e < 0 ↔ (tail.scale (-hc⁻¹)).eval e < x := by
  have hcR : (hc : R) < 0 := by
    rw [← Rat.cast_zero]
    exact Rat.cast_lt.mpr hneg
  rw [scale_neg_inv]
  constructor
  · intro h
    have hmul : x * (hc : R) < -tail.eval e := by
      simpa [mul_comm] using
        (lt_neg_iff_add_neg ((hc : R) * x) (tail.eval e)).mpr h
    exact (div_lt_iff_of_neg hcR).mpr hmul
  · intro h
    have hmul : (hc : R) * x < -tail.eval e := by
      simpa [mul_comm] using (div_lt_iff_of_neg hcR).mp h
    exact (lt_neg_iff_add_neg ((hc : R) * x) (tail.eval e)).mp hmul

theorem sat_keep {n : Nat} {a : Atom (n + 1)} {r : Atom n} {x : R} {e : Fin n → R}
    (h : classify a = .keep r) : a.sat (envCons x e) ↔ r.sat e := by
  rcases a with ⟨⟨coeff, const⟩, rel⟩
  cases coeff with
  | cons hc cs =>
    simp only [classify] at h
    split at h
    · next hzero =>
      cases h
      cases rel <;>
        simp [Atom.sat, holds, hzero, Rat.cast_zero, zero_mul, LinTerm.eval, Coeff.dot]
    · next =>
      split at h <;> cases h

theorem sat_upper {n : Nat} {a : Atom (n + 1)} {b : Bound n} {x : R} {e : Fin n → R}
    (h : classify a = .upper b) : a.sat (envCons x e) ↔ b.above x e := by
  rcases a with ⟨⟨coeff, const⟩, rel⟩
  cases coeff with
  | cons hc cs =>
    simp only [classify] at h
    split at h
    · next => cases h
    · next hne =>
      split at h
      · next hpos =>
        cases h
        have heval := eval_cons hc cs const x e
        cases rel with
        | le =>
          simpa [Atom.sat, holds, Bound.above, heval] using
            pos_le_iff hc hpos ⟨cs, const⟩ x e
        | lt =>
          simpa [Atom.sat, holds, Bound.above, heval] using
            pos_lt_iff hc hpos ⟨cs, const⟩ x e
      · next => cases h

theorem sat_lower {n : Nat} {a : Atom (n + 1)} {b : Bound n} {x : R} {e : Fin n → R}
    (h : classify a = .lower b) : a.sat (envCons x e) ↔ b.below x e := by
  rcases a with ⟨⟨coeff, const⟩, rel⟩
  cases coeff with
  | cons hc cs =>
    simp only [classify] at h
    split at h
    · next => cases h
    · next hne =>
      split at h
      · next => cases h
      · next hnot =>
        have hneg : hc < 0 := by
          rcases lt_trichotomy hc 0 with hlt | heq | hgt
          · exact hlt
          · exact absurd heq hne
          · exact absurd hgt hnot
        cases h
        have heval := eval_cons hc cs const x e
        cases rel with
        | le =>
          simpa [Atom.sat, holds, Bound.below, heval] using
            neg_le_iff hc hneg ⟨cs, const⟩ x e
        | lt =>
          simpa [Atom.sat, holds, Bound.below, heval] using
            neg_lt_iff hc hneg ⟨cs, const⟩ x e

theorem cross_of_bounds {n : Nat} (lo hi : Bound n) {x : R} {e : Fin n → R}
    (hl : lo.below x e) (hu : hi.above x e) : (cross lo hi).sat e := by
  cases hlo : lo.strict <;> cases hhi : hi.strict
  · simp only [Bound.below, Bound.above, hlo, hhi, cross, Bool.or_false, Atom.sat, holds,
      eval_sub, sub_nonpos] at hl hu ⊢
    exact le_trans hl hu
  · simp only [Bound.below, Bound.above, hlo, hhi, if_true, cross, Bool.false_or, Atom.sat,
      holds, eval_sub, sub_lt_zero] at hl hu ⊢
    exact lt_of_le_of_lt hl hu
  · simp only [Bound.below, Bound.above, hlo, hhi, if_true, cross, Atom.sat, holds, eval_sub,
      sub_lt_zero] at hl hu ⊢
    exact lt_of_lt_of_le hl hu
  · simp only [Bound.below, Bound.above, hlo, hhi, if_true, cross, Bool.or_true, Atom.sat,
      holds, eval_sub, sub_lt_zero] at hl hu ⊢
    exact lt_trans hl hu

theorem project_keep {n : Nat} {a : Atom (n + 1)} {r : Atom n} {as : List (Atom (n + 1))}
    (h : classify a = .keep r) : project (a :: as) = r :: project as := by
  simp [project, h]

theorem project_lower {n : Nat} {a : Atom (n + 1)} {b : Bound n} {as : List (Atom (n + 1))}
    (h : classify a = .lower b) :
    project (a :: as) = project as ++ (uppers as).map (fun hi => cross b hi) := by
  simp [project, h]

theorem project_upper {n : Nat} {a : Atom (n + 1)} {b : Bound n} {as : List (Atom (n + 1))}
    (h : classify a = .upper b) :
    project (a :: as) = project as ++ (lowers as).map (fun lo => cross lo b) := by
  simp [project, h]

theorem residuals_keep {n : Nat} {a : Atom (n + 1)} {r : Atom n}
    {as : List (Atom (n + 1))} (h : classify a = .keep r) :
    residuals (a :: as) = r :: residuals as := by simp [residuals, h]

theorem residuals_lower {n : Nat} {a : Atom (n + 1)} {b : Bound n}
    {as : List (Atom (n + 1))} (h : classify a = .lower b) :
    residuals (a :: as) = residuals as := by simp [residuals, h]

theorem residuals_upper {n : Nat} {a : Atom (n + 1)} {b : Bound n}
    {as : List (Atom (n + 1))} (h : classify a = .upper b) :
    residuals (a :: as) = residuals as := by simp [residuals, h]

theorem lowers_keep {n : Nat} {a : Atom (n + 1)} {r : Atom n}
    {as : List (Atom (n + 1))} (h : classify a = .keep r) :
    lowers (a :: as) = lowers as := by simp [lowers, h]

theorem lowers_lower {n : Nat} {a : Atom (n + 1)} {b : Bound n}
    {as : List (Atom (n + 1))} (h : classify a = .lower b) :
    lowers (a :: as) = b :: lowers as := by simp [lowers, h]

theorem lowers_upper {n : Nat} {a : Atom (n + 1)} {b : Bound n}
    {as : List (Atom (n + 1))} (h : classify a = .upper b) :
    lowers (a :: as) = lowers as := by simp [lowers, h]

theorem uppers_keep {n : Nat} {a : Atom (n + 1)} {r : Atom n}
    {as : List (Atom (n + 1))} (h : classify a = .keep r) :
    uppers (a :: as) = uppers as := by simp [uppers, h]

theorem uppers_lower {n : Nat} {a : Atom (n + 1)} {b : Bound n}
    {as : List (Atom (n + 1))} (h : classify a = .lower b) :
    uppers (a :: as) = uppers as := by simp [uppers, h]

theorem uppers_upper {n : Nat} {a : Atom (n + 1)} {b : Bound n}
    {as : List (Atom (n + 1))} (h : classify a = .upper b) :
    uppers (a :: as) = b :: uppers as := by simp [uppers, h]

theorem project_sat_iff {n : Nat} (atoms : List (Atom (n + 1))) (e : Fin n → R) :
    allSat (project atoms) e ↔
      allSat (residuals atoms) e ∧
        ∀ lo ∈ lowers atoms, ∀ hi ∈ uppers atoms, (cross lo hi).sat e := by
  induction atoms with
  | nil =>
    simp [project, residuals, lowers, uppers, allSat_nil]
  | cons a as ih =>
    cases h : classify a with
    | keep r =>
      rw [project_keep h, residuals_keep h, lowers_keep h, uppers_keep h,
        allSat_cons, allSat_cons, ih]
      constructor
      · intro ⟨hr, htail⟩
        obtain ⟨hres, hcross⟩ := htail
        exact ⟨⟨hr, hres⟩, hcross⟩
      · intro ⟨hhead, hcross⟩
        obtain ⟨hr, hres⟩ := hhead
        exact ⟨hr, hres, hcross⟩
    | lower b =>
      rw [project_lower h, residuals_lower h, lowers_lower h, uppers_lower h,
        allSat_append, allSat_map, ih]
      constructor
      · intro hP
        obtain ⟨⟨hres, hcrossAs⟩, hnew⟩ := hP
        refine ⟨hres, ?_⟩
        intro lo hlo hi hhi
        rcases List.mem_cons.mp hlo with rfl | hlo
        · exact hnew hi hhi
        · exact hcrossAs lo hlo hi hhi
      · intro hP
        obtain ⟨hres, hcross⟩ := hP
        refine ⟨⟨hres, ?_⟩, ?_⟩
        · intro lo hlo hi hhi
          exact hcross lo (List.mem_cons_of_mem _ hlo) hi hhi
        · intro hi hhi
          exact hcross b (List.mem_cons.mpr (Or.inl rfl)) hi hhi
    | upper b =>
      rw [project_upper h, residuals_upper h, lowers_upper h, uppers_upper h,
        allSat_append, allSat_map, ih]
      constructor
      · intro hP
        obtain ⟨⟨hres, hcrossAs⟩, hnew⟩ := hP
        refine ⟨hres, ?_⟩
        intro lo hlo hi hhi
        rcases List.mem_cons.mp hhi with rfl | hhi
        · exact hnew lo hlo
        · exact hcrossAs lo hlo hi hhi
      · intro hP
        obtain ⟨hres, hcross⟩ := hP
        refine ⟨⟨hres, ?_⟩, ?_⟩
        · intro lo hlo hi hhi
          exact hcross lo hlo hi (List.mem_cons_of_mem _ hhi)
        · intro lo hlo
          exact hcross lo hlo b (List.mem_cons.mpr (Or.inl rfl))

def tightLower : List (Bool × R) → Option (Bool × R)
  | [] => none
  | p :: ps =>
    match tightLower ps with
    | none => some p
    | some q =>
      if q.2 < p.2 then some p
      else if p.2 < q.2 then some q
      else some (p.1 || q.1, p.2)

theorem tightLower_eq_none (ps : List (Bool × R)) : tightLower ps = none ↔ ps = [] := by
  induction ps with
  | nil => simp [tightLower]
  | cons p ps ih =>
    cases hps : tightLower ps with
    | none => simp [tightLower, hps]
    | some q =>
      simp only [tightLower, hps]
      split_ifs <;> simp

theorem tightLower_spec (ps : List (Bool × R)) (t : Bool × R)
    (h : tightLower ps = some t) :
    (t.1, t.2) ∈ ps ∧
      (∀ s v, (s, v) ∈ ps → v ≤ t.2) ∧
      (∀ s, (s, t.2) ∈ ps → s = true → t.1 = true) := by
  induction ps generalizing t with
  | nil => simp [tightLower] at h
  | cons p ps ih =>
    cases hq : tightLower ps with
    | none =>
      have hnil : ps = [] := (tightLower_eq_none ps).mp hq
      subst hnil
      simp [tightLower] at h
      cases h
      refine ⟨List.mem_cons.mpr (Or.inl rfl), ?_, ?_⟩
      · intro s v hv
        rcases List.mem_cons.mp hv with hhead | hmem
        · rw [← (Prod.ext rfl rfl : (p.1, p.2) = p)] at hhead
          obtain ⟨_, rfl⟩ := Prod.mk.inj hhead
          exact le_rfl
        · cases hmem
      · intro s hs hst
        rcases List.mem_cons.mp hs with hhead | hmem
        · rw [← (Prod.ext rfl rfl : (p.1, p.2) = p)] at hhead
          obtain ⟨rfl, _⟩ := Prod.mk.inj hhead
          exact hst
        · cases hmem
    | some q =>
      obtain ⟨hqmem, hqle, hqstrict⟩ := ih q hq
      by_cases hlt : q.2 < p.2
      · simp [tightLower, hq, hlt] at h
        cases h
        refine ⟨List.mem_cons.mpr (Or.inl rfl), ?_, ?_⟩
        · intro s v hv
          rcases List.mem_cons.mp hv with hhead | hmem
          · rw [← (Prod.ext rfl rfl : (p.1, p.2) = p)] at hhead
            obtain ⟨_, rfl⟩ := Prod.mk.inj hhead
            exact le_rfl
          · exact le_of_lt (lt_of_le_of_lt (hqle s v hmem) hlt)
        · intro s hs hst
          rcases List.mem_cons.mp hs with hhead | hmem
          · rw [← (Prod.ext rfl rfl : (p.1, p.2) = p)] at hhead
            obtain ⟨rfl, _⟩ := Prod.mk.inj hhead
            exact hst
          · exact absurd (lt_of_le_of_lt (hqle s p.2 hmem) hlt) (lt_irrefl _)
      · by_cases hgt : p.2 < q.2
        · simp [tightLower, hq, hlt, hgt] at h
          cases h
          refine ⟨List.mem_cons_of_mem _ hqmem, ?_, ?_⟩
          · intro s v hv
            rcases List.mem_cons.mp hv with hhead | hmem
            · rw [← (Prod.ext rfl rfl : (p.1, p.2) = p)] at hhead
              obtain ⟨_, rfl⟩ := Prod.mk.inj hhead
              exact le_of_lt hgt
            · exact hqle s v hmem
          · intro s hs hst
            rcases List.mem_cons.mp hs with hhead | hmem
            · rw [← (Prod.ext rfl rfl : (p.1, p.2) = p)] at hhead
              obtain ⟨_, hsnd⟩ := Prod.mk.inj hhead
              rw [hsnd] at hgt
              exact absurd hgt (lt_irrefl _)
            · exact hqstrict s hmem hst
        · have heq : p.2 = q.2 :=
            le_antisymm (le_of_not_gt hlt) (le_of_not_gt hgt)
          simp [tightLower, hq, hlt, hgt] at h
          cases h
          refine ⟨?_, ?_, ?_⟩
          · cases hp1 : p.1
            · cases hq1 : q.1
              · refine List.mem_cons.mpr (Or.inl ?_)
                apply Prod.ext
                · simp [hp1]
                · rfl
              · apply List.mem_cons_of_mem
                convert hqmem
                simp [hq1]
            · refine List.mem_cons.mpr (Or.inl ?_)
              apply Prod.ext
              · simp [hp1, Bool.true_or]
              · rfl
          · intro s v hv
            rcases List.mem_cons.mp hv with hhead | hmem
            · rw [← (Prod.ext rfl rfl : (p.1, p.2) = p)] at hhead
              obtain ⟨_, rfl⟩ := Prod.mk.inj hhead
              exact le_rfl
            · exact le_trans (hqle s v hmem) (le_of_eq heq.symm)
          · intro s hs hst
            rcases List.mem_cons.mp hs with hhead | hmem
            · rw [← (Prod.ext rfl rfl : (p.1, p.2) = p)] at hhead
              obtain ⟨rfl, _⟩ := Prod.mk.inj hhead
              rw [hst]
              rfl
            · have hmem' : (s, q.2) ∈ ps := by
                rw [← heq]
                exact hmem
              have hqtrue : q.1 = true := hqstrict s hmem' hst
              rw [hqtrue]
              exact Bool.or_true _

def tightUpper (ps : List (Bool × R)) : Option (Bool × R) :=
  match tightLower (ps.map fun p => (p.1, -p.2)) with
  | none => none
  | some t => some (t.1, -t.2)

theorem tightUpper_spec (ps : List (Bool × R)) (t : Bool × R)
    (h : tightUpper ps = some t) :
    (t.1, t.2) ∈ ps ∧
      (∀ s v, (s, v) ∈ ps → t.2 ≤ v) ∧
      (∀ s, (s, t.2) ∈ ps → s = true → t.1 = true) := by
  cases hm : tightLower (ps.map fun p => (p.1, -p.2)) with
  | none => simp [tightUpper, hm] at h
  | some s =>
    simp [tightUpper, hm] at h
    cases h
    obtain ⟨hmem, hle, hstrict⟩ := tightLower_spec _ s hm
    rcases List.mem_map.mp hmem with ⟨p, hp, hpq⟩
    have hpq' : (p.1, -p.2) = (s.1, s.2) := by simpa using hpq
    obtain ⟨hfst, hneg⟩ := Prod.mk.inj hpq'
    have hsnd : p.2 = -s.2 := neg_eq_iff_eq_neg.mp hneg
    have hp' : p = (s.1, -s.2) := Prod.ext hfst hsnd
    refine ⟨?_, ?_, ?_⟩
    · simpa [hp'] using hp
    · intro u v hv
      have hmv : (u, -v) ∈ ps.map fun q => (q.1, -q.2) :=
        List.mem_map.mpr ⟨(u, v), hv, rfl⟩
      have hvle : -v ≤ -(-s.2) := by simpa [neg_neg] using hle u (-v) hmv
      exact (neg_le_neg_iff).mp hvle
    · intro u hu hust
      exact hstrict u
        (List.mem_map.mpr ⟨(u, -s.2), hu, by simp [neg_neg]⟩) hust

def chooseX (lows highs : List (Bool × R)) : R :=
  match tightLower lows, tightUpper highs with
  | none, none => 0
  | some L, none => if L.1 then L.2 + 1 else L.2
  | none, some U => if U.1 then U.2 - 1 else U.2
  | some L, some U => if L.1 then (L.2 + U.2) / 2 else L.2

def pairLe (L U : Bool × R) : Prop :=
  if L.1 || U.1 then L.2 < U.2 else L.2 ≤ U.2

def aboveNum (p : Bool × R) (x : R) : Prop :=
  if p.1 then p.2 < x else p.2 ≤ x

def belowNum (p : Bool × R) (x : R) : Prop :=
  if p.1 then x < p.2 else x ≤ p.2

theorem aboveNum_of_lt {p : Bool × R} {x : R} (h : p.2 < x) : aboveNum p x := by
  cases p.1 <;> simp [aboveNum, h, le_of_lt h]

theorem belowNum_of_lt {p : Bool × R} {x : R} (h : x < p.2) : belowNum p x := by
  cases p.1 <;> simp [belowNum, h, le_of_lt h]

theorem choose_above (lows highs : List (Bool × R))
    (hcross : ∀ lo ∈ lows, ∀ hi ∈ highs, pairLe lo hi)
    (lo : Bool × R) (hlo : lo ∈ lows) : aboveNum lo (chooseX lows highs) := by
  cases hL : tightLower lows with
  | none =>
    have : lows = [] := (tightLower_eq_none lows).mp hL
    simp [this] at hlo
  | some L =>
    obtain ⟨hLmem, hLle, hLstrict⟩ := tightLower_spec lows L hL
    cases hU : tightUpper highs with
    | none =>
      have hx : chooseX lows highs = if L.1 then L.2 + 1 else L.2 := by
        simp [chooseX, hL, hU]
      have hloLe : lo.2 ≤ L.2 := hLle lo.1 lo.2 hlo
      cases hflag : L.1
      · have hx' : chooseX lows highs = L.2 := by simp [hx, hflag]
        have hsplit : lo.1 = false ∨ lo.2 < L.2 := by
          by_cases heq : lo.2 = L.2
          · left
            by_contra hs
            have htrue : lo.1 = true := by
              cases hbit : lo.1
              · exact absurd hbit hs
              · rfl
            have hmem : (lo.1, L.2) ∈ lows := by
              have hlo' : lo = (lo.1, L.2) := Prod.ext rfl heq
              rwa [hlo'] at hlo
            have : L.1 = true := hLstrict lo.1 hmem htrue
            exact Bool.false_ne_true (hflag.symm.trans this)
          · right
            exact lt_of_le_of_ne hloLe heq
        cases hsplit with
        | inl hfalse => simp [aboveNum, hx', hfalse, hloLe]
        | inr hlt =>
          cases hlo1 : lo.1
          · simp [aboveNum, hx', hlo1, le_of_lt hlt]
          · simp [aboveNum, hx', hlo1, hlt]
      · have hx' : chooseX lows highs = L.2 + 1 := by simp [hx, hflag]
        apply aboveNum_of_lt
        simp only [hx']
        exact lt_of_le_of_lt hloLe ((lt_add_iff_pos_right L.2).mpr one_pos)
    | some U =>
      obtain ⟨hUmem, hUge, hUstrict⟩ := tightUpper_spec highs U hU
      have hpair : pairLe (L.1, L.2) (U.1, U.2) :=
        hcross (L.1, L.2) hLmem (U.1, U.2) hUmem
      have hloLe : lo.2 ≤ L.2 := hLle lo.1 lo.2 hlo
      cases hflag : L.1
      · have hx : chooseX lows highs = L.2 := by simp [chooseX, hL, hU, hflag]
        have hnot : lo.1 = false ∨ lo.2 < L.2 := by
          by_cases heq : lo.2 = L.2
          · left
            by_contra hs
            have hmem : (lo.1, L.2) ∈ lows := by
              have hlo' : lo = (lo.1, L.2) := Prod.ext rfl heq
              rwa [hlo'] at hlo
            have : L.1 = true := hLstrict lo.1 hmem (by
              cases hbit : lo.1
              · exact absurd hbit hs
              · rfl)
            exact Bool.false_ne_true (hflag.symm.trans this)
          · right
            exact lt_of_le_of_ne hloLe heq
        cases hnot with
        | inl hfalse => simp [aboveNum, hx, hfalse, hloLe]
        | inr hlt =>
          cases lo.1 <;> simp [aboveNum, hx, hlt, le_of_lt hlt]
      · have hx' : chooseX lows highs = (L.2 + U.2) / 2 := by simp [chooseX, hL, hU, hflag]
        have hlt : L.2 < U.2 := by
          simp [pairLe, hflag, Bool.true_or] at hpair
          exact hpair
        have hmid : L.2 < (L.2 + U.2) / 2 := (left_lt_add_div_two).mpr hlt
        apply aboveNum_of_lt
        simp only [hx']
        exact lt_of_le_of_lt hloLe hmid

theorem choose_below (lows highs : List (Bool × R))
    (hcross : ∀ lo ∈ lows, ∀ hi ∈ highs, pairLe lo hi)
    (hi : Bool × R) (hhi : hi ∈ highs) : belowNum hi (chooseX lows highs) := by
  cases hU : tightUpper highs with
  | none =>
    have : highs = [] := by
      cases hm : tightLower (highs.map fun p => (p.1, -p.2)) with
      | none =>
        have hempty : highs.map (fun p => (p.1, -p.2)) = [] := (tightLower_eq_none _).mp hm
        cases highs with
        | nil => rfl
        | cons q qs => simp at hempty
      | some s => simp [tightUpper, hm] at hU
    simp [this] at hhi
  | some U =>
    obtain ⟨hUmem, hUge, hUstrict⟩ := tightUpper_spec highs U hU
    have hhiGe : U.2 ≤ hi.2 := hUge hi.1 hi.2 hhi
    cases hL : tightLower lows with
    | none =>
      have hx : chooseX lows highs = if U.1 then U.2 - 1 else U.2 := by
        simp [chooseX, hL, hU]
      cases hflag : U.1
      · have hnot : hi.1 = false ∨ U.2 < hi.2 := by
          by_cases heq : hi.2 = U.2
          · left
            by_contra hs
            have hmem : (hi.1, U.2) ∈ highs := by
              have hhi' : hi = (hi.1, U.2) := Prod.ext rfl heq
              rwa [hhi'] at hhi
            have : U.1 = true := hUstrict hi.1 hmem (by
              cases hbit : hi.1
              · exact absurd hbit hs
              · rfl)
            exact Bool.false_ne_true (hflag.symm.trans this)
          · right
            exact lt_of_le_of_ne hhiGe (Ne.symm heq)
        cases hnot with
        | inl hfalse => simp [belowNum, hx, hflag, hfalse, hhiGe]
        | inr hlt =>
          cases hi.1 <;> simp [belowNum, hx, hflag, hlt, le_of_lt hlt]
      · apply belowNum_of_lt
        rw [hx, hflag]
        simp
        exact lt_of_lt_of_le (sub_lt_self U.2 one_pos) hhiGe
    | some L =>
      obtain ⟨hLmem, hLle, _hLstrict⟩ := tightLower_spec lows L hL
      have hpair : pairLe (L.1, L.2) (U.1, U.2) :=
        hcross (L.1, L.2) hLmem (U.1, U.2) hUmem
      cases hflag : L.1
      · have hx : chooseX lows highs = L.2 := by simp [chooseX, hL, hU, hflag]
        have hLU : L.2 ≤ U.2 := by
          cases hUf : U.1
          · simp [pairLe, hflag, hUf] at hpair
            exact hpair
          · simp [pairLe, hflag, hUf] at hpair
            exact le_of_lt hpair
        cases hhiF : hi.1
        · simp [belowNum, hx, hhiF]
          exact le_trans hLU hhiGe
        · have hlt : L.2 < hi.2 := by
            by_cases heq : hi.2 = U.2
            · have hmem : (hi.1, U.2) ∈ highs := by
                have hhi' : hi = (hi.1, U.2) := Prod.ext rfl heq
                rwa [hhi'] at hhi
              have hUtrue : U.1 = true := hUstrict hi.1 hmem hhiF
              simp [pairLe, hflag, hUtrue] at hpair
              exact lt_of_lt_of_le hpair (le_of_eq heq.symm)
            · exact lt_of_le_of_lt hLU (lt_of_le_of_ne hhiGe (Ne.symm heq))
          simp [belowNum, hx, hhiF, hlt]
      · have hx : chooseX lows highs = (L.2 + U.2) / 2 := by simp [chooseX, hL, hU, hflag]
        have hlt : L.2 < U.2 := by
          simp [pairLe, hflag, Bool.true_or] at hpair
          exact hpair
        have hmid : (L.2 + U.2) / 2 < U.2 := (add_div_two_lt_right).mpr hlt
        apply belowNum_of_lt
        rw [hx]
        exact lt_of_lt_of_le hmid hhiGe

def ev {n : Nat} (b : Bound n) (e : Fin n → R) : Bool × R :=
  (b.strict, b.term.eval e)

theorem below_ev {n : Nat} (b : Bound n) (x : R) (e : Fin n → R) :
    b.below x e ↔ aboveNum (ev b e) x := by
  cases h : b.strict <;> simp [Bound.below, aboveNum, ev, h]

theorem above_ev {n : Nat} (b : Bound n) (x : R) (e : Fin n → R) :
    b.above x e ↔ belowNum (ev b e) x := by
  cases h : b.strict <;> simp [Bound.above, belowNum, ev, h]

theorem cross_iff_pairLe {n : Nat} (lo hi : Bound n) (e : Fin n → R) :
    (cross lo hi).sat e ↔ pairLe (ev lo e) (ev hi e) := by
  cases hlo : lo.strict <;> cases hhi : hi.strict <;>
    simp [cross, pairLe, ev, Atom.sat, holds, eval_sub, hlo, hhi]

theorem exists_x_of_bounds {n : Nat} (lows highs : List (Bound n)) (e : Fin n → R)
    (hcross : ∀ lo ∈ lows, ∀ hi ∈ highs, (cross lo hi).sat e) :
    ∃ x, (∀ lo ∈ lows, lo.below x e) ∧ (∀ hi ∈ highs, hi.above x e) := by
  let lowsV := lows.map fun b => ev b e
  let highsV := highs.map fun b => ev b e
  have hcrossV : ∀ lo ∈ lowsV, ∀ hi ∈ highsV, pairLe lo hi := by
    intro lo hlo hi hhi
    rcases List.mem_map.mp hlo with ⟨blo, hblo, rfl⟩
    rcases List.mem_map.mp hhi with ⟨bhi, hbhi, rfl⟩
    exact (cross_iff_pairLe blo bhi e).mp (hcross blo hblo bhi hbhi)
  refine ⟨chooseX lowsV highsV, ?_, ?_⟩
  · intro lo hlo
    rw [below_ev]
    exact choose_above lowsV highsV hcrossV (ev lo e) (List.mem_map.mpr ⟨lo, hlo, rfl⟩)
  · intro hi hhi
    rw [above_ev]
    exact choose_below lowsV highsV hcrossV (ev hi e) (List.mem_map.mpr ⟨hi, hhi, rfl⟩)

theorem mem_residuals {n : Nat} {r : Atom n} {atoms : List (Atom (n + 1))} :
    r ∈ residuals atoms ↔ ∃ a ∈ atoms, classify a = .keep r := by
  induction atoms with
  | nil => simp [residuals]
  | cons a as ih =>
    cases h : classify a with
    | keep r' =>
      rw [residuals_keep h]
      constructor
      · intro hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact ⟨a, List.mem_cons_self, h⟩
        · rcases ih.mp hr with ⟨b, hb, hbclass⟩
          exact ⟨b, List.mem_cons_of_mem _ hb, hbclass⟩
      · intro ⟨b, hb, hbclass⟩
        rcases List.mem_cons.mp hb with rfl | hb
        · rw [h] at hbclass
          cases hbclass
          exact List.mem_cons.mpr (Or.inl rfl)
        · exact List.mem_cons_of_mem _ (ih.mpr ⟨b, hb, hbclass⟩)
    | lower b =>
      rw [residuals_lower h, ih]
      constructor
      · intro ⟨c, hc, hclass⟩
        exact ⟨c, List.mem_cons_of_mem _ hc, hclass⟩
      · intro ⟨c, hc, hclass⟩
        rcases List.mem_cons.mp hc with rfl | hc
        · simp [h] at hclass
        · exact ⟨c, hc, hclass⟩
    | upper b =>
      rw [residuals_upper h, ih]
      constructor
      · intro ⟨c, hc, hclass⟩
        exact ⟨c, List.mem_cons_of_mem _ hc, hclass⟩
      · intro ⟨c, hc, hclass⟩
        rcases List.mem_cons.mp hc with rfl | hc
        · simp [h] at hclass
        · exact ⟨c, hc, hclass⟩

theorem mem_lowers {n : Nat} {b : Bound n} {atoms : List (Atom (n + 1))} :
    b ∈ lowers atoms ↔ ∃ a ∈ atoms, classify a = .lower b := by
  induction atoms with
  | nil => simp [lowers]
  | cons a as ih =>
    cases h : classify a with
    | keep r =>
      rw [lowers_keep h, ih]
      constructor
      · intro ⟨c, hc, hclass⟩
        exact ⟨c, List.mem_cons_of_mem _ hc, hclass⟩
      · intro ⟨c, hc, hclass⟩
        rcases List.mem_cons.mp hc with rfl | hc
        · simp [h] at hclass
        · exact ⟨c, hc, hclass⟩
    | lower b' =>
      rw [lowers_lower h]
      constructor
      · intro hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ⟨a, List.mem_cons_self, h⟩
        · rcases ih.mp hb with ⟨c, hc, hclass⟩
          exact ⟨c, List.mem_cons_of_mem _ hc, hclass⟩
      · intro ⟨c, hc, hclass⟩
        rcases List.mem_cons.mp hc with rfl | hc
        · rw [h] at hclass
          cases hclass
          exact List.mem_cons.mpr (Or.inl rfl)
        · exact List.mem_cons_of_mem _ (ih.mpr ⟨c, hc, hclass⟩)
    | upper b' =>
      rw [lowers_upper h, ih]
      constructor
      · intro ⟨c, hc, hclass⟩
        exact ⟨c, List.mem_cons_of_mem _ hc, hclass⟩
      · intro ⟨c, hc, hclass⟩
        rcases List.mem_cons.mp hc with rfl | hc
        · simp [h] at hclass
        · exact ⟨c, hc, hclass⟩

theorem mem_uppers {n : Nat} {b : Bound n} {atoms : List (Atom (n + 1))} :
    b ∈ uppers atoms ↔ ∃ a ∈ atoms, classify a = .upper b := by
  induction atoms with
  | nil => simp [uppers]
  | cons a as ih =>
    cases h : classify a with
    | keep r =>
      rw [uppers_keep h, ih]
      constructor
      · intro ⟨c, hc, hclass⟩
        exact ⟨c, List.mem_cons_of_mem _ hc, hclass⟩
      · intro ⟨c, hc, hclass⟩
        rcases List.mem_cons.mp hc with rfl | hc
        · simp [h] at hclass
        · exact ⟨c, hc, hclass⟩
    | lower b' =>
      rw [uppers_lower h, ih]
      constructor
      · intro ⟨c, hc, hclass⟩
        exact ⟨c, List.mem_cons_of_mem _ hc, hclass⟩
      · intro ⟨c, hc, hclass⟩
        rcases List.mem_cons.mp hc with rfl | hc
        · simp [h] at hclass
        · exact ⟨c, hc, hclass⟩
    | upper b' =>
      rw [uppers_upper h]
      constructor
      · intro hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ⟨a, List.mem_cons_self, h⟩
        · rcases ih.mp hb with ⟨c, hc, hclass⟩
          exact ⟨c, List.mem_cons_of_mem _ hc, hclass⟩
      · intro ⟨c, hc, hclass⟩
        rcases List.mem_cons.mp hc with rfl | hc
        · rw [h] at hclass
          cases hclass
          exact List.mem_cons.mpr (Or.inl rfl)
        · exact List.mem_cons_of_mem _ (ih.mpr ⟨c, hc, hclass⟩)

theorem exists_iff_pieces {n : Nat} (atoms : List (Atom (n + 1))) (e : Fin n → R) :
    (∃ x, allSat atoms (envCons x e)) ↔
      allSat (residuals atoms) e ∧
        ∀ lo ∈ lowers atoms, ∀ hi ∈ uppers atoms, (cross lo hi).sat e := by
  constructor
  · intro ⟨x, hx⟩
    refine ⟨?_, ?_⟩
    · intro r hr
      rcases (mem_residuals).mp hr with ⟨a, ha, hclass⟩
      exact (sat_keep hclass).mp (hx a ha)
    · intro lo hlo hi hhi
      rcases (mem_lowers).mp hlo with ⟨a, ha, hlower⟩
      rcases (mem_uppers).mp hhi with ⟨b, hb, hupper⟩
      exact cross_of_bounds lo hi
        ((sat_lower hlower).mp (hx a ha)) ((sat_upper hupper).mp (hx b hb))
  · intro ⟨hres, hcross⟩
    obtain ⟨x, hlow, hhigh⟩ :=
      exists_x_of_bounds (lowers atoms) (uppers atoms) e hcross
    refine ⟨x, ?_⟩
    intro a ha
    cases hclass : classify a with
    | keep r =>
      exact (sat_keep hclass).mpr (hres r ((mem_residuals).mpr ⟨a, ha, hclass⟩))
    | lower b =>
      exact (sat_lower hclass).mpr (hlow b ((mem_lowers).mpr ⟨a, ha, hclass⟩))
    | upper b =>
      exact (sat_upper hclass).mpr (hhigh b ((mem_uppers).mpr ⟨a, ha, hclass⟩))

/-- Eliminating the outermost variable preserves satisfiability over any ordered field. -/
theorem project_iff {n : Nat} (atoms : List (Atom (n + 1))) (e : Fin n → R) :
    (∃ x, allSat atoms (envCons x e)) ↔ allSat (project atoms) e := by
  rw [exists_iff_pieces, project_sat_iff]

theorem constHolds_iff (a : Atom 0) (e : Fin 0 → R) :
    constHolds a = true ↔ a.sat e := by
  cases a with
  | mk term rel =>
    cases term with
    | mk coeff const =>
      cases coeff with
      | nil =>
        cases rel <;>
          simp [constHolds, Atom.sat, holds, LinTerm.eval, Coeff.dot, decide_eq_true_eq]

theorem unique_env (e : Fin 0 → R) : e = Fin.elim0 := by
  funext i
  exact Fin.elim0 i

theorem decideSat_iff {n : Nat} (atoms : List (Atom n)) :
    decideSat atoms = true ↔ ∃ env : Fin n → R, allSat atoms env := by
  induction n with
  | zero =>
    constructor
    · intro h
      refine ⟨Fin.elim0, ?_⟩
      intro a ha
      have hholds : constHolds a = true := by
        rw [decideSat_zero, List.all_eq_true] at h
        exact h a ha
      exact (constHolds_iff a Fin.elim0).mp hholds
    · intro ⟨env, henv⟩
      rw [unique_env env] at henv
      rw [decideSat_zero, List.all_eq_true]
      intro a ha
      exact (constHolds_iff a Fin.elim0).mpr (henv a ha)
  | succ n ih =>
    rw [decideSat_succ, ih (project atoms)]
    constructor
    · intro ⟨e, he⟩
      rcases (project_iff atoms e).mpr he with ⟨x, hx⟩
      exact ⟨envCons x e, hx⟩
    · intro ⟨env, henv⟩
      refine ⟨envTail env, (project_iff atoms (envTail env)).mp ?_⟩
      rw [env_eq_cons env] at henv
      exact ⟨env 0, henv⟩

/-- Where the procedure returns a bit, that bit is truth in every ordered field. -/
theorem decideSentence_iff {n : Nat} (atoms : List (Atom n)) {b : Bool}
    (h : decideSentence (.exists_ (.conj atoms)) = some b) :
    b = true ↔ ∃ env : Fin n → R, allSat atoms env := by
  simp [decideSentence] at h
  subst h
  exact decideSat_iff atoms

theorem realLinearBubble_decides {n : Nat} (atoms : List (Atom n)) {b : Bool}
    (h : realLinearBubble.decide (.exists_ (.conj atoms)) = some b) :
    b = true ↔ ∃ env : Fin n → R, allSat atoms env :=
  decideSentence_iff atoms h

/-- `IsRealClosed` supplies the order-theoretic squares once an order is present.
Fourier–Motzkin does not use this fact; Tarski elimination does. -/
theorem nonnegative_is_square [IsRealClosed R] {x : R} : 0 ≤ x ↔ IsSquare x :=
  IsRealClosed.nonneg_iff_isSquare

def Formula.sat : {n : Nat} → Formula n → (Fin n → R) → Prop
  | _, .bot, _ => False
  | _, .atom a, env => a.sat env
  | _, .conj left right, env => left.sat env ∧ right.sat env
  | _, .neg body, env => ¬ body.sat env
  | _, .ex body, env => ∃ x, body.sat (envCons x env)

theorem Atom.negate_sat {n : Nat} (a : Atom n) (env : Fin n → R) :
    a.negate.sat env ↔ ¬ a.sat env := by
  cases a with
  | mk term rel =>
    cases rel with
    | le =>
      simp only [Atom.negate, Atom.sat, holds]
      rw [eval_scale, show ((-1 : ℚ) : R) = -1 by simp, neg_one_mul]
      exact neg_lt_zero.trans not_le.symm
    | lt =>
      simp only [Atom.negate, Atom.sat, holds]
      rw [eval_scale, show ((-1 : ℚ) : R) = -1 by simp, neg_one_mul]
      constructor
      · intro hle hlt
        linarith
      · intro hnot
        have hle : (0 : R) ≤ term.eval env := not_lt.mp hnot
        linarith

def clausesSat {n : Nat} (clauses : List (List (Atom n))) (env : Fin n → R) : Prop :=
  ∃ clause ∈ clauses, allSat clause env

theorem clausesSat_append {n : Nat} (left right : List (List (Atom n)))
    (env : Fin n → R) :
    clausesSat (left ++ right) env ↔ clausesSat left env ∨ clausesSat right env := by
  constructor
  · rintro ⟨clause, hmem, hhold⟩
    rcases List.mem_append.mp hmem with hl | hr
    · exact Or.inl ⟨clause, hl, hhold⟩
    · exact Or.inr ⟨clause, hr, hhold⟩
  · rintro (⟨clause, hmem, hhold⟩ | ⟨clause, hmem, hhold⟩)
    · exact ⟨clause, List.mem_append.mpr (Or.inl hmem), hhold⟩
    · exact ⟨clause, List.mem_append.mpr (Or.inr hmem), hhold⟩

theorem clausesSat_clauseProd {n : Nat} (left right : List (List (Atom n)))
    (env : Fin n → R) :
    clausesSat (clauseProd left right) env ↔
      clausesSat left env ∧ clausesSat right env := by
  simp only [clausesSat, allSat]
  exact clauseProd_iff (p := fun (a : Atom n) => a.sat env) left right

theorem toDnf_iff {n : Nat} (positive : Bool) :
    (φ : Formula n) → (hq : φ.quantifierFree = true) → (env : Fin n → R) →
      clausesSat (toDnf positive φ) env ↔
        match positive with
        | true => φ.sat env
        | false => ¬ φ.sat env
  | .bot, _, _ => by
      cases positive with
      | false =>
        simp [toDnf, clausesSat, allSat, Formula.sat]
      | true =>
        simp [toDnf, clausesSat, allSat, Formula.sat]
  | .atom a, _, env => by
      cases positive with
      | false =>
        simp only [toDnf, clausesSat, allSat, List.mem_singleton, exists_eq_left, forall_eq,
          Formula.sat]
        exact Atom.negate_sat a env
      | true =>
        simp [toDnf, clausesSat, allSat, Formula.sat, Atom.sat]
  | .conj left right, hq, env => by
      have hleft : left.quantifierFree = true := by
        simp only [Formula.quantifierFree, Bool.and_eq_true] at hq
        exact hq.1
      have hright : right.quantifierFree = true := by
        simp only [Formula.quantifierFree, Bool.and_eq_true] at hq
        exact hq.2
      cases positive with
      | false =>
        simp only [toDnf, Formula.sat]
        rw [clausesSat_append, toDnf_iff false left hleft env,
          toDnf_iff false right hright env]
        constructor
        · rintro (hnl | hnr) ⟨hl, hr⟩
          · exact hnl hl
          · exact hnr hr
        · intro hboth
          by_cases hl : left.sat env
          · exact Or.inr (fun hr => hboth ⟨hl, hr⟩)
          · exact Or.inl hl
      | true =>
        simp only [toDnf, Formula.sat]
        rw [clausesSat_clauseProd, toDnf_iff true left hleft env,
          toDnf_iff true right hright env]
  | .neg body, hq, env => by
      have hbody : body.quantifierFree = true := by
        simpa [Formula.quantifierFree] using hq
      cases positive with
      | false =>
        simp only [toDnf, Formula.sat]
        rw [toDnf_iff true body hbody env]
        exact Classical.not_not.symm
      | true =>
        simp only [toDnf, Formula.sat]
        exact toDnf_iff false body hbody env
  | .ex _, hq, _ => by
      simp [Formula.quantifierFree] at hq

theorem finConj_iff {n : Nat} (fs : List (Formula n)) (env : Fin n → R) :
    (finConj fs).sat env ↔ ∀ f ∈ fs, f.sat env := by
  induction fs with
  | nil =>
      simp only [finConj, Formula.sat]
      exact ⟨fun _ f hf => (List.not_mem_nil hf).elim, fun _ h => False.elim h⟩
  | cons f fs ih =>
      simp only [finConj, Formula.sat, List.forall_mem_cons, ih]

theorem finDisj_iff {n : Nat} (fs : List (Formula n)) (env : Fin n → R) :
    (finDisj fs).sat env ↔ ∃ f ∈ fs, f.sat env := by
  induction fs with
  | nil =>
      simp only [finDisj, Formula.sat, List.not_mem_nil, false_and, exists_false]
  | cons head tail ih =>
      simp only [finDisj, Formula.sat]
      constructor
      · intro h
        by_cases hh : head.sat env
        · exact ⟨head, List.mem_cons_self, hh⟩
        · have htail : (finDisj tail).sat env :=
            Classical.not_not.mp (fun hn => h ⟨hh, hn⟩)
          obtain ⟨f, hf, hsat⟩ := ih.mp htail
          exact ⟨f, List.mem_cons_of_mem head hf, hsat⟩
      · rintro ⟨f, hfmem, hsat⟩
        intro hboth
        rcases List.mem_cons.mp hfmem with rfl | htail
        · exact hboth.1 hsat
        · exact hboth.2 (ih.mpr ⟨f, htail, hsat⟩)

theorem finConj_atoms_iff {n : Nat} (atoms : List (Atom n)) (env : Fin n → R) :
    (finConj (atoms.map Formula.atom)).sat env ↔ allSat atoms env := by
  rw [finConj_iff]
  constructor
  · intro h a ha
    simpa [Formula.sat] using h (Formula.atom a) (List.mem_map.mpr ⟨a, ha, rfl⟩)
  · intro h form hmem
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hmem
    simpa [Formula.sat] using h a ha

theorem Formula.cooper_iff {n : Nat} (φ : Formula (n + 1))
    (hq : φ.quantifierFree = true) (e : Fin n → R) :
    (Formula.cooper φ).sat e ↔ ∃ x, φ.sat (envCons x e) := by
  rw [Formula.cooper, finDisj_iff]
  constructor
  · rintro ⟨form, hmem, hsat⟩
    obtain ⟨clause, hclause, rfl⟩ := List.mem_map.mp hmem
    have hall : allSat (project clause) e :=
      (finConj_atoms_iff (project clause) e).mp hsat
    obtain ⟨x, hx⟩ := (project_iff clause e).mpr hall
    exact ⟨x, (toDnf_iff true φ hq (envCons x e)).mp ⟨clause, hclause, hx⟩⟩
  · rintro ⟨x, hx⟩
    obtain ⟨clause, hclause, hall⟩ :=
      (toDnf_iff true φ hq (envCons x e)).mpr hx
    refine ⟨finConj ((project clause).map Formula.atom), ?_, ?_⟩
    · exact List.mem_map.mpr ⟨clause, hclause, rfl⟩
    · exact (finConj_atoms_iff (project clause) e).mpr
        ((project_iff clause e).mp ⟨x, hall⟩)

theorem Formula.eliminate_iff : {n : Nat} → (φ : Formula n) → (env : Fin n → R) →
    φ.eliminate.sat env ↔ φ.sat env
  | _, .bot, _ => by simp [Formula.eliminate, Formula.sat]
  | _, .atom _, _ => by simp [Formula.eliminate, Formula.sat]
  | _, .conj a b, env => by
      simp only [Formula.eliminate, Formula.sat]
      exact and_congr (Formula.eliminate_iff a env) (Formula.eliminate_iff b env)
  | _, .neg a, env => by
      simp only [Formula.eliminate, Formula.sat]
      exact not_congr (Formula.eliminate_iff a env)
  | _, .ex body, env => by
      simp only [Formula.eliminate, Formula.sat]
      rw [Formula.cooper_iff (Formula.eliminate body) (Formula.eliminate_qf body) env]
      constructor
      · rintro ⟨x, hx⟩
        exact ⟨x, (Formula.eliminate_iff body (envCons x env)).mp hx⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, (Formula.eliminate_iff body (envCons x env)).mpr hx⟩

theorem Formula.decideQF_iff :
    (φ : Formula 0) → (hq : φ.quantifierFree = true) →
      φ.decideQF = true ↔ φ.sat (Fin.elim0 : Fin 0 → R)
  | .bot, _ => by simp [Formula.decideQF, Formula.sat]
  | .atom a, _ => by
      simpa [Formula.decideQF, Formula.sat] using constHolds_iff a Fin.elim0
  | .conj a b, hq => by
      have hleft : a.quantifierFree = true := by
        simp only [Formula.quantifierFree, Bool.and_eq_true] at hq
        exact hq.1
      have hright : b.quantifierFree = true := by
        simp only [Formula.quantifierFree, Bool.and_eq_true] at hq
        exact hq.2
      simp only [Formula.decideQF, Formula.sat, Bool.and_eq_true]
      exact and_congr (Formula.decideQF_iff a hleft) (Formula.decideQF_iff b hright)
  | .neg body, hq => by
      have hbody : body.quantifierFree = true := by
        simpa [Formula.quantifierFree] using hq
      simp only [Formula.decideQF, Formula.sat]
      rw [Bool.not_eq_true', Bool.eq_false_iff]
      exact (Formula.decideQF_iff body hbody).not
  | .ex _, hq => by simp [Formula.quantifierFree] at hq

theorem Formula.decideClosed_iff (φ : Formula 0) {b : Bool}
    (h : φ.decideClosed = some b) :
    b = true ↔ φ.sat (Fin.elim0 : Fin 0 → R) := by
  simp only [Formula.decideClosed, Option.some.injEq] at h
  subst h
  exact (Formula.decideQF_iff φ.eliminate (Formula.eliminate_qf φ)).trans
    (Formula.eliminate_iff φ (Fin.elim0 : Fin 0 → R))

theorem linearBubble_iff_sat (φ : Formula 0) :
    linearBubble.decide φ = some true ↔ φ.sat (Fin.elim0 : Fin 0 → R) := by
  have hdecide : linearBubble.decide φ = some φ.eliminate.decideQF := by
    simp [linearBubble, Formula.decideClosed]
  rw [hdecide, Option.some.injEq]
  exact (Formula.decideQF_iff φ.eliminate (Formula.eliminate_qf φ)).trans
    (Formula.eliminate_iff φ (Fin.elim0 : Fin 0 → R))

theorem decide_true_of_sat {φ : Formula 0} (h : φ.sat (Fin.elim0 : Fin 0 → R)) :
    linearBubble.decide φ = some true :=
  (linearBubble_iff_sat φ).mpr h

theorem decide_false_of_unsat {φ : Formula 0}
    (h : ¬ φ.sat (Fin.elim0 : Fin 0 → R)) :
    linearBubble.decide φ = some false := by
  have hbit : φ.eliminate.decideQF = false := by
    cases hval : φ.eliminate.decideQF with
    | false => rfl
    | true =>
        exact False.elim (h ((Formula.eliminate_iff φ Fin.elim0).mp
          ((Formula.decideQF_iff _ (Formula.eliminate_qf φ)).mp hval)))
  simp [linearBubble, Formula.decideClosed, hbit]

end Semantics

theorem control_origin :
    decideSat [⟨⟨Coeff.cons (-1) .nil, 0⟩, .le⟩, ⟨⟨Coeff.cons 1 .nil, 0⟩, .le⟩] = true := by
  refine (decideSat_iff (R := ℚ) _).mpr ⟨fun _ => 0, ?_⟩
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · simp only [Atom.sat, holds, LinTerm.eval, Coeff.dot, Rat.cast_neg, Rat.cast_one,
      Rat.cast_zero, neg_one_mul, neg_zero, add_zero]
    exact le_rfl
  · rcases List.mem_cons.mp ha with rfl | ha
    · simp only [Atom.sat, holds, LinTerm.eval, Coeff.dot, Rat.cast_one, Rat.cast_zero,
        one_mul, add_zero]
      exact le_rfl
    · cases ha

theorem control_origin_sat {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    ∃ env : Fin 1 → R,
      allSat [⟨⟨Coeff.cons (-1) .nil, 0⟩, .le⟩, ⟨⟨Coeff.cons 1 .nil, 0⟩, .le⟩] env :=
  (decideSat_iff _).mp control_origin

theorem control_strict_conflict_unsat {R : Type} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] :
    ¬ ∃ env : Fin 1 → R,
      allSat [⟨⟨Coeff.cons 1 .nil, 0⟩, .lt⟩, ⟨⟨Coeff.cons (-1) .nil, 0⟩, .lt⟩] env := by
  intro ⟨env, hsat⟩
  have hpos := hsat _ (List.mem_cons.mpr (Or.inl rfl))
  have hneg := hsat _ (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
  simp only [Atom.sat, holds, LinTerm.eval, Coeff.dot, Rat.cast_neg, Rat.cast_one,
    Rat.cast_zero, neg_one_mul, one_mul, add_zero] at hpos hneg
  linarith

theorem control_strict_conflict :
    decideSat [⟨⟨Coeff.cons 1 .nil, 0⟩, .lt⟩, ⟨⟨Coeff.cons (-1) .nil, 0⟩, .lt⟩] = false := by
  cases hbit : decideSat [⟨⟨Coeff.cons 1 .nil, 0⟩, .lt⟩, ⟨⟨Coeff.cons (-1) .nil, 0⟩, .lt⟩]
  · rfl
  · exact absurd ((decideSat_iff (R := ℚ) _).mp hbit) control_strict_conflict_unsat

theorem control_unbounded :
    decideSat [⟨⟨Coeff.cons (-1) .nil, 0⟩, .lt⟩] = true := by
  refine (decideSat_iff (R := ℚ) _).mpr ⟨fun _ => 1, ?_⟩
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · simp only [Atom.sat, holds, LinTerm.eval, Coeff.dot, Rat.cast_neg, Rat.cast_one,
      Rat.cast_zero, neg_one_mul, add_zero]
    exact neg_one_lt_zero
  · cases ha

theorem control_constant_false_unsat {R : Type} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] :
    ¬ ∃ env : Fin 1 → R, allSat [⟨⟨Coeff.cons 0 .nil, 1⟩, .le⟩] env := by
  intro ⟨env, hsat⟩
  have h := hsat _ (List.mem_cons.mpr (Or.inl rfl))
  simp only [Atom.sat, holds, LinTerm.eval, Coeff.dot, Rat.cast_zero, Rat.cast_one,
    zero_mul, add_zero, zero_add] at h
  linarith

theorem control_constant_false :
    decideSat [⟨⟨Coeff.cons 0 .nil, 1⟩, .le⟩] = false := by
  cases hbit : decideSat [⟨⟨Coeff.cons 0 .nil, 1⟩, .le⟩]
  · exact hbit
  · exact absurd ((decideSat_iff (R := ℚ) _).mp hbit) control_constant_false_unsat

theorem control_parameter_diagonal :
    decideSat [⟨⟨Coeff.cons 1 (Coeff.cons (-1) .nil), 0⟩, .le⟩,
      ⟨⟨Coeff.cons (-1) (Coeff.cons 1 .nil), 0⟩, .le⟩] = true := by
  refine (decideSat_iff (R := ℚ) _).mpr ⟨fun _ => 0, ?_⟩
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · simp only [Atom.sat, holds, LinTerm.eval, Coeff.dot, Rat.cast_neg, Rat.cast_one,
      Rat.cast_zero, one_mul, neg_one_mul, neg_zero, add_zero]
    exact le_rfl
  · rcases List.mem_cons.mp ha with rfl | ha
    · simp only [Atom.sat, holds, LinTerm.eval, Coeff.dot, Rat.cast_neg, Rat.cast_one,
        Rat.cast_zero, one_mul, neg_one_mul, neg_zero, add_zero]
      exact le_rfl
    · cases ha

theorem control_parameter_cycle_unsat {R : Type} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] :
    ¬ ∃ env : Fin 2 → R,
      allSat [⟨⟨Coeff.cons 1 (Coeff.cons (-1) .nil), 0⟩, .lt⟩,
        ⟨⟨Coeff.cons (-1) (Coeff.cons 1 .nil), 0⟩, .lt⟩] env := by
  intro ⟨env, hsat⟩
  have hxy := hsat _ (List.mem_cons.mpr (Or.inl rfl))
  have hyx := hsat _ (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
  simp only [Atom.sat, holds, LinTerm.eval, Coeff.dot, Rat.cast_neg, Rat.cast_one,
    Rat.cast_zero, one_mul, neg_one_mul, add_zero] at hxy hyx
  linarith

theorem control_parameter_cycle :
    decideSat [⟨⟨Coeff.cons 1 (Coeff.cons (-1) .nil), 0⟩, .lt⟩,
      ⟨⟨Coeff.cons (-1) (Coeff.cons 1 .nil), 0⟩, .lt⟩] = false := by
  cases hbit : decideSat [⟨⟨Coeff.cons 1 (Coeff.cons (-1) .nil), 0⟩, .lt⟩,
      ⟨⟨Coeff.cons (-1) (Coeff.cons 1 .nil), 0⟩, .lt⟩]
  · rfl
  · exact absurd ((decideSat_iff (R := ℚ) _).mp hbit) control_parameter_cycle_unsat

theorem control_disjunction_abstain :
    decideSentence
      (.exists_ (.disj (n := 0) (.conj (n := 0) []) (.conj (n := 0) []))) = none := by
  simp [decideSentence]

theorem control_universal_abstain (n : Nat) (atoms : List (Atom n)) :
    decideSentence (.forall_ (.conj atoms)) = none := by
  simp [decideSentence]

def exOrigin : Formula 0 :=
  .ex (.conj
    (.atom ⟨⟨.cons (-1) .nil, 0⟩, .le⟩)
    (.atom ⟨⟨.cons 1 .nil, 0⟩, .le⟩))

def exBothStrict : Formula 0 :=
  .ex (.conj
    (.atom ⟨⟨.cons 1 .nil, 0⟩, .lt⟩)
    (.atom ⟨⟨.cons (-1) .nil, 0⟩, .lt⟩))

def forallZeroLe : Formula 0 :=
  .neg (.ex (.neg (.atom ⟨⟨.cons 0 .nil, 0⟩, .le⟩)))

def forallNonneg : Formula 0 :=
  .neg (.ex (.neg (.atom ⟨⟨.cons (-1) .nil, 0⟩, .le⟩)))

def nestedBot : Formula 0 :=
  .ex (.ex .bot)

def nestedTop : Formula 0 :=
  .ex (.ex (.neg .bot))

def exDiagonal : Formula 0 :=
  .ex (.ex (.conj
    (.atom ⟨⟨.cons (-1) (.cons 1 .nil), 0⟩, .le⟩)
    (.atom ⟨⟨.cons 1 (.cons (-1) .nil), 0⟩, .le⟩)))

def boolTrue : Formula 0 := .atom ⟨⟨.nil, 0⟩, .le⟩

def boolFalse : Formula 0 := .atom ⟨⟨.nil, 1⟩, .le⟩

def boolOrTrue : Formula 0 :=
  .neg (.conj (.neg boolFalse) (.neg boolTrue))

def boolOrFalse : Formula 0 :=
  .neg (.conj (.neg boolFalse) (.neg (.atom ⟨⟨.nil, 1⟩, .lt⟩)))

theorem boolTrue_sat {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    boolTrue.sat (Fin.elim0 : Fin 0 → R) := by
  simp [boolTrue, Formula.sat, Atom.sat, holds, LinTerm.eval, Coeff.dot]

theorem boolFalse_unsat {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    ¬ boolFalse.sat (Fin.elim0 : Fin 0 → R) := by
  intro h
  simp [boolFalse, Formula.sat, Atom.sat, holds, LinTerm.eval, Coeff.dot] at h
  linarith

theorem boolOrTrue_sat {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    boolOrTrue.sat (Fin.elim0 : Fin 0 → R) := by
  intro h
  simp [boolTrue, boolFalse, Formula.sat, Atom.sat, holds, LinTerm.eval, Coeff.dot] at h

theorem boolOrFalse_unsat {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    ¬ boolOrFalse.sat (Fin.elim0 : Fin 0 → R) := by
  intro h
  simp [boolOrFalse, boolFalse, Formula.sat, Atom.sat, holds, LinTerm.eval, Coeff.dot] at h

theorem control_bool_true :
    linearBubble.decide boolTrue = some true :=
  decide_true_of_sat (R := ℚ) boolTrue_sat

theorem control_bool_false :
    linearBubble.decide boolFalse = some false :=
  decide_false_of_unsat (R := ℚ) boolFalse_unsat

theorem control_bool_or_true :
    linearBubble.decide boolOrTrue = some true :=
  decide_true_of_sat (R := ℚ) boolOrTrue_sat

theorem control_bool_or_false :
    linearBubble.decide boolOrFalse = some false :=
  decide_false_of_unsat (R := ℚ) boolOrFalse_unsat

theorem exOrigin_sat {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    exOrigin.sat (Fin.elim0 : Fin 0 → R) := by
  refine ⟨0, ?_⟩
  simp [Formula.sat, Atom.sat, holds, LinTerm.eval, Coeff.dot, envCons]

theorem exBothStrict_unsat {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    ¬ exBothStrict.sat (Fin.elim0 : Fin 0 → R) := by
  intro ⟨_, hx⟩
  simp [Formula.sat, Atom.sat, holds, LinTerm.eval, Coeff.dot, envCons] at hx
  linarith

theorem forallZeroLe_sat {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    forallZeroLe.sat (Fin.elim0 : Fin 0 → R) := by
  intro ⟨_, hx⟩
  simp [Formula.sat, Atom.sat, holds, LinTerm.eval, Coeff.dot, envCons] at hx

theorem forallNonneg_unsat {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    ¬ forallNonneg.sat (Fin.elim0 : Fin 0 → R) := by
  intro h
  apply h
  refine ⟨-1, ?_⟩
  simp [Formula.sat, Atom.sat, holds, LinTerm.eval, Coeff.dot, envCons]

theorem nestedBot_unsat {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    ¬ nestedBot.sat (Fin.elim0 : Fin 0 → R) := by
  intro ⟨_, h⟩
  obtain ⟨_, hbot⟩ := h
  exact hbot

theorem nestedTop_sat {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    nestedTop.sat (Fin.elim0 : Fin 0 → R) := by
  refine ⟨0, 0, ?_⟩
  simp [Formula.sat]

theorem exDiagonal_sat {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    exDiagonal.sat (Fin.elim0 : Fin 0 → R) := by
  refine ⟨0, 0, ?_⟩
  simp [Formula.sat, Atom.sat, holds, LinTerm.eval, Coeff.dot, envCons_zero]
  exact ⟨le_rfl, le_rfl⟩

theorem control_ex_origin :
    linearBubble.decide exOrigin = some true :=
  decide_true_of_sat (R := ℚ) exOrigin_sat

theorem control_ex_both_strict :
    linearBubble.decide exBothStrict = some false :=
  decide_false_of_unsat (R := ℚ) exBothStrict_unsat

theorem control_forall_zero_le :
    linearBubble.decide forallZeroLe = some true :=
  decide_true_of_sat (R := ℚ) forallZeroLe_sat

theorem control_forall_nonneg :
    linearBubble.decide forallNonneg = some false :=
  decide_false_of_unsat (R := ℚ) forallNonneg_unsat

theorem control_nested_bot :
    linearBubble.decide nestedBot = some false :=
  decide_false_of_unsat (R := ℚ) nestedBot_unsat

theorem control_nested_top :
    linearBubble.decide nestedTop = some true :=
  decide_true_of_sat (R := ℚ) nestedTop_sat

theorem control_ex_diagonal :
    linearBubble.decide exDiagonal = some true :=
  decide_true_of_sat (R := ℚ) exDiagonal_sat

#print axioms project_iff
#print axioms decideSat_iff
#print axioms decideSentence_iff
#print axioms realLinearBubble_decides
#print axioms nonnegative_is_square
#print axioms Formula.cooper_iff
#print axioms Formula.eliminate_iff
#print axioms Formula.decideClosed_iff
#print axioms linearBubble_iff_sat

end Mettapedia.Logic.Arithmetic.FourierMotzkin
