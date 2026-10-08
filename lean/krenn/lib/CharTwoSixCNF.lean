import Mathlib.Tactic.Sat.FromLRAT

/-!
# The six-site lemma as a propositional certificate

The six-site base case of the characteristic-two theorem reduces to a finite statement
about which four-site matching sums can be nonzero.  This file builds that statement as a
propositional formula, and checks a solver's refutation of it with Mathlib's `lrat_proof`,
which turns the LRAT trace into an ordinary proof term: no certificate checker remains in
the theorem, and no `native_decide` or `Lean.ofReduceBool` is used.

## The atoms

Variables are numbered from `0`, one below their DIMACS index.  Sites are `0,…,5`; the fifteen pairs are indexed lexicographically.  A four-site set is
indexed by the pair it leaves out.  With `T` a four-site set, `v` a site, `c`, `d` colours,
`f` a pair and `π` one of the six bijections from the three perfect matchings of the
complement of `f` onto the colours:

* `live e` (`e`): some weight on the pair `e` is nonzero;
* `assign f π` (`15 + 6f + π`): `π` is the colouring of the matchings forced at `f`;
* `alive T` (`105 + T`): some colouring of `T` has a nonzero matching sum;
* `const T d` (`120 + 3T + d`): the constant colouring `d` of `T` has a nonzero sum;
* `pin T v c` (`165 + 18T + 3v + c`): every colouring of `T` with a nonzero sum paints `v`
  with `c`;
* `witness p d x` (`435 + 18p + 6d + x`): the edge `px` in colour `d` and the constant
  colouring `d` of the rest both carry nonzero weight.

## The clauses

(a) every site and colour has a witness, and a witness is a live pair whose complement is
alive at the constant colouring; (b) a live pair has an assignment, and its assignment pins
each matching pair of its complement, inside the four-site set it spans with the pair, to
the matching's colour — and makes that set alive; (c) an alive set pins each site to at
most one colour, a constant colouring is alive, and it agrees with every pin.
-/

namespace KrennCharTwo.SixCNF

open Sat

/-- Literal decidable equality, for comparing formulas. -/
def literalDecEq : DecidableEq Sat.Literal
  | .pos a, .pos b =>
      match decEq a b with
      | isTrue h => isTrue (by cases h; rfl)
      | isFalse h => isFalse (fun hab => by cases hab; exact h rfl)
  | .neg a, .neg b =>
      match decEq a b with
      | isTrue h => isTrue (by cases h; rfl)
      | isFalse h => isFalse (fun hab => by cases hab; exact h rfl)
  | .pos _, .neg _ => isFalse (by intro h; cases h)
  | .neg _, .pos _ => isFalse (by intro h; cases h)

def clauseDecEq : DecidableEq Sat.Clause := by
  letI : DecidableEq Sat.Literal := literalDecEq
  unfold Sat.Clause
  infer_instance

def pos (n : Nat) : Sat.Literal := .pos n
def neg (n : Nat) : Sat.Literal := .neg n

/-- A clause from its literals. -/
def cl (ls : List Sat.Literal) : Sat.Clause := ls

/-- Index of the pair `{a, b}` of sites `0,…,5` in lexicographic order. -/
def pairIdx (a b : Nat) : Nat :=
  let i := min a b; let j := max a b; i * (11 - i) / 2 + (j - i - 1)

/-- The two sites of the pair with index `e`. -/
def pairOf : Nat → Nat × Nat
  | 0 => (0, 1) | 1 => (0, 2) | 2 => (0, 3) | 3 => (0, 4) | 4 => (0, 5)
  | 5 => (1, 2) | 6 => (1, 3) | 7 => (1, 4) | 8 => (1, 5)
  | 9 => (2, 3) | 10 => (2, 4) | 11 => (2, 5)
  | 12 => (3, 4) | 13 => (3, 5) | _ => (4, 5)

/-- The four sites outside the pair `e`, ascending. -/
def compl (e : Nat) : List Nat :=
  (List.range 6).filter fun v => v != (pairOf e).1 && v != (pairOf e).2

/-- The value of the `π`-th bijection (lexicographic) on the matching index `m`. -/
def permApply (π m : Nat) : Nat :=
  match π, m with
  | 0, 0 => 0 | 0, 1 => 1 | 0, _ => 2
  | 1, 0 => 0 | 1, 1 => 2 | 1, _ => 1
  | 2, 0 => 1 | 2, 1 => 0 | 2, _ => 2
  | 3, 0 => 1 | 3, 1 => 2 | 3, _ => 0
  | 4, 0 => 2 | 4, 1 => 0 | 4, _ => 1
  | _, 0 => 2 | _, 1 => 1 | _, _ => 0

def live (e : Nat) : Nat := e
def assign (f π : Nat) : Nat := 15 + 6 * f + π
def alive (T : Nat) : Nat := 105 + T
def const (T d : Nat) : Nat := 120 + 3 * T + d
def pin (T v c : Nat) : Nat := 165 + 18 * T + 3 * v + c
def witness (p d x : Nat) : Nat := 435 + 18 * p + 6 * d + x

/-- The three perfect matchings of the complement of `f`, as pairs of pairs of sites. -/
def matchings (f : Nat) : List ((Nat × Nat) × (Nat × Nat)) :=
  match compl f with
  | [a, b, c, d] => [((a, b), (c, d)), ((a, c), (b, d)), ((a, d), (b, c))]
  | _ => []

def clausesA : List Sat.Clause :=
  (List.range 6).flatMap fun p => (List.range 3).flatMap fun d =>
    ((List.range 6).filter (· != p)).flatMap (fun x =>
      [cl [neg (witness p d x), pos (live (pairIdx p x))],
       cl [neg (witness p d x), pos (const (pairIdx p x) d)]]) ++
    [cl (((List.range 6).filter (· != p)).map fun x => pos (witness p d x))]

def clausesBOne (f π m : Nat) (e eo : Nat × Nat) : List Sat.Clause :=
  [cl [neg (assign f π), pos (alive (pairIdx eo.1 eo.2))],
   cl [neg (assign f π), pos (pin (pairIdx eo.1 eo.2) e.1 (permApply π m))],
   cl [neg (assign f π), pos (pin (pairIdx eo.1 eo.2) e.2 (permApply π m))]]

def clausesB : List Sat.Clause :=
  (List.range 15).flatMap fun f =>
    ((List.range 6).flatMap fun π =>
      ((matchings f).zipIdx.flatMap fun ⟨⟨e1, e2⟩, m⟩ =>
        clausesBOne f π m e1 e2 ++ clausesBOne f π m e2 e1)) ++
    [cl (neg (live f) :: (List.range 6).map fun π => pos (assign f π))]

def clausesC : List Sat.Clause :=
  (List.range 15).flatMap fun T =>
    ((List.range 3).map fun d => cl [neg (const T d), pos (alive T)]) ++
    (compl T).flatMap fun v =>
      ([((0 : Nat), (1 : Nat)), (0, 2), (1, 2)].map fun ⟨c1, c2⟩ =>
        cl [neg (alive T), neg (pin T v c1), neg (pin T v c2)]) ++
      ((List.range 3).flatMap fun c => ((List.range 3).filter (· != c)).map fun d =>
        cl [neg (const T d), neg (pin T v c)])

/-- The whole formula, clause for clause in the order of the committed DIMACS file. -/
def sixFmla : Sat.Fmla := (clausesA ++ clausesB ++ clausesC : List Sat.Clause)

lrat_proof sixUnsat
  (include_str "Certificates" / "CharTwo" / "six.cnf")
  (include_str "Certificates" / "CharTwo" / "six.lrat")

/-- The formula parsed from the committed DIMACS file. -/
noncomputable abbrev sixCtx : Sat.Fmla := sixUnsat.ctx_67

/-- Its kernel-checked refutation. -/
theorem sixCtx_proof : sixCtx.proof Sat.Clause.nil := sixUnsat.proof_68

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The committed DIMACS file is exactly the formula built above. -/
theorem sixCtx_eq : sixCtx = sixFmla := by
  letI : DecidableEq Sat.Literal := literalDecEq
  letI : DecidableEq Sat.Clause := clauseDecEq
  decide

/-- **The six-site formula is unsatisfiable.**  No valuation satisfies every clause. -/
theorem sixFmla_unsat (v : Sat.Valuation) (h : ∀ c ∈ sixFmla, v.satisfies c) : False :=
  sixCtx_proof v ⟨fun c hc => h c (sixCtx_eq ▸ hc)⟩

end KrennCharTwo.SixCNF
