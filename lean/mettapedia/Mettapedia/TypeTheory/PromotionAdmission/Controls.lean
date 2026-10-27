import Mettapedia.TypeTheory.PromotionAdmission.Admission

/-!
# Controls for the admission criterion

Each control is a concrete rule list over one signature, checked by kernel computation.

**Refused.**
* *The zero swap promoted into addition* (`peano ++ [zeroSwap]`): the equation `x + 0 = 0 + x`
  is true in `ℕ` (`zeroSwap_valid`), and the request fails twice. A critical pair is refuted:
  `x + 0` rewrites to `x` and to `0 + x`, both normal and distinct, so the rules are not locally
  confluent (`zeroSwap_not_locallyConfluent`). And the rule's sides unify, so it loops on
  `0 + 0` and no certificate orients it (`zeroSwap_not_terminating`,
  `zeroSwap_no_certificate`). The admission check refutes the request at every budget, with
  every certificate (`zeroSwap_refuted`). The head `add` is not fresh, so this is a promotion
  (`zeroSwap_not_fresh`).
* *Commutativity* (`[comm]`): true in `ℕ`, locally confluent (all critical pairs join,
  `comm_locallyConfluent`), and even confluent, because each step can be undone
  (`comm_confluent`). It is refused by the termination part alone: its sides unify, so it loops on
  `x + x` (`comm_refuted`).
* *A fork on an existing head* (`[f x ↦ z] ++ [f x ↦ o]`): the critical pair `(z, o)` is refuted
  (`existingHeadFork_not_locallyConfluent`).

**Admitted.**
* *`x + 0 ↦ x` alone* (`unitAlone_admitted`).
* *A left unit promoted into addition* (`peano ++ [0 + x ↦ x]`), on the existing head `add`,
  with the certificate `add ↦ 1 + x + 2y`, `succ ↦ 1 + x`: every critical pair joins
  (`leftUnit_admitted`), and the rule is true in `ℕ`.
* *Monoid normalization* (`[(x · y) · z ↦ x · (y · z), e · x ↦ x, x · e ↦ x]`) with the
  certificate `· ↦ 1 + 2x + y`, `e ↦ 1` (`monoid_admitted`); conversion of monoid words is then
  decided by normal forms (`monoid_decided`).
* *Fresh heads* (`[f x ↦ z]` extended by `[g zero ↦ o, g (succ x) ↦ g x]`): admission meets the
  overlap condition by construction, with no critical-pair evidence (`fresh_admitted`).

**Two promotions against one base.** `f 0 ↦ z` and `f 0 ↦ o` are each admitted against the
empty base (`concurrent_each_admitted`) and are not locally confluent together
(`concurrent_union_not_locallyConfluent`).

**Budget.** The pair `(1 + 1, 2)` in addition is incomplete at budget one and established at
budget two (`incomplete_then_established`): an exhausted budget is not a refutation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PromotionAdmission.Controls

open Term Relation
open Mettapedia.Logic.Relation (Confluent DecidedOn)
open AuthorityTheory

/-- The symbols of the controls. -/
inductive Sym where
  | zero | succ | add | unit | mul | f | g | z | o
  deriving DecidableEq, Repr

/-- Terms of the controls, with variables numbered. -/
abbrev T := Term Sym ℕ

def x : T := .var 0
def y : T := .var 1
def w : T := .var 2
def zeroT : T := .app .zero []
def succT (t : T) : T := .app .succ [t]
def addT (s t : T) : T := .app .add [s, t]
def unitT : T := .app .unit []
def mulT (s t : T) : T := .app .mul [s, t]

/-- The recursion equations of addition on its second argument. -/
def peano : List (Rule Sym ℕ) :=
  [⟨addT x zeroT, x⟩, ⟨addT x (succT y), succT (addT x y)⟩]

/-- The zero swap `x + 0 ↦ 0 + x`. -/
def zeroSwap : Rule Sym ℕ := ⟨addT x zeroT, addT zeroT x⟩

/-- The left unit `0 + x ↦ x`. -/
def leftUnit : Rule Sym ℕ := ⟨addT zeroT x, x⟩

/-- Commutativity `x + y ↦ y + x`. -/
def comm : Rule Sym ℕ := ⟨addT x y, addT y x⟩

/-- The standard model of numbers: `mul` and `unit` read as addition and zero. -/
def numbers : Interpretation Sym ℕ where
  op
    | .zero, [] => 0
    | .succ, [n] => n + 1
    | .add, [m, n] => m + n
    | .unit, [] => 0
    | .mul, [m, n] => m + n
    | _, _ => 0

/-- A certificate for addition: `add ↦ 1 + x + 2y`, `succ ↦ 1 + x`. -/
def additionOrder : LinearInterpretation Sym where
  weight
    | .succ => 1
    | .add => 1
    | .f => 1
    | .g => 1
    | _ => 0
  extra
    | .add, 1 => 1
    | _, _ => 0

/-! ## Refused: the zero swap promoted into addition -/

/-- The zero swap is true in `ℕ`. -/
theorem zeroSwap_valid : numbers.Valid zeroSwap := by
  intro α; simp [zeroSwap, addT, zeroT, x, numbers]

/-- The head `add` is not fresh: the zero swap is a promotion. -/
theorem zeroSwap_not_fresh : freshHeadsCheck peano [zeroSwap] = false := by decide

theorem zeroSwap_format : rulesWellFormed (peano ++ [zeroSwap]) = true := by decide

theorem zeroSwap_computed : (criticalPairsOf 8 (overlaps (peano ++ [zeroSwap])
    (peano ++ [zeroSwap]))).isSome = true := by decide

/-- **A critical pair is refuted**: `x + 0` reaches the distinct normal forms `x` and `0 + x`. -/
theorem zeroSwap_apart : someApart (peano ++ [zeroSwap]) 1
    ((criticalPairsOf 8 (overlaps (peano ++ [zeroSwap]) (peano ++ [zeroSwap]))).get
      zeroSwap_computed) = true := by decide

/-- **Not locally confluent.** -/
theorem zeroSwap_not_locallyConfluent : ¬ LocallyConfluentAt (peano ++ [zeroSwap]) (ℕ ⊕ ℕ) :=
  not_locallyConfluent_of_someApart zeroSwap_format zeroSwap_computed zeroSwap_apart

theorem zeroSwap_loop : loopSearch 4 (peano ++ [zeroSwap]) = .found := by decide

/-- **Not terminating**: the sides of the zero swap unify, at `0 + 0`. -/
theorem zeroSwap_not_terminating : ¬ TerminatingAt (peano ++ [zeroSwap]) ℕ :=
  not_terminating_of_loopSearch zeroSwap_loop

/-- **No linear certificate orients the zero swap.** -/
theorem zeroSwap_no_certificate (I : LinearInterpretation Sym) :
    ¬ ∀ ρ ∈ peano ++ [zeroSwap], I.orients ρ = true := by
  obtain ⟨ρ, mem, θ, same⟩ := loopSearch_found zeroSwap_loop
  exact no_certificate_of_loop mem same I

/-- **The admission check refutes the zero swap at every budget, with every certificate.** -/
theorem zeroSwap_refuted (k : ℕ) (I : LinearInterpretation Sym) :
    ∃ obstruction, admissionRun k ⟨peano, [zeroSwap], I⟩ = .refuted obstruction :=
  admissionRun_refuted_of_loop zeroSwap_format zeroSwap_loop

/-! ## Refused: commutativity -/

/-- Commutativity is true in `ℕ`. -/
theorem comm_valid : numbers.Valid comm := by
  intro α; simp [comm, addT, x, y, numbers, Nat.add_comm]

theorem comm_computed : (criticalPairsOf 8 (overlaps [comm] [comm])).isSome = true := by decide

theorem comm_joined : allJoined [comm] 1
    ((criticalPairsOf 8 (overlaps [comm] [comm])).get comm_computed) = true := by decide

/-- **Commutativity is locally confluent**: its only critical pair is trivial. -/
theorem comm_locallyConfluent (W : Type) : LocallyConfluentAt [comm] W :=
  locallyConfluent_of_allJoined comm_computed comm_joined W

/-- A commutation step can be undone. -/
theorem comm_symmetric {W : Type} {s t : Term Sym W} (step : Step [comm] s t) : Step [comm] t s := by
  induction step with
  | root mem σ =>
      simp only [List.mem_singleton] at mem
      subst mem
      have back := Step.root (R := [comm]) (List.mem_singleton_self comm)
        (fun n => if n = 0 then σ 1 else if n = 1 then σ 0 else σ n)
      simpa [comm, addT, x, y] using back
  | arg head args i h _ ih =>
      have back := Step.arg (R := [comm]) head (args.set i _) i (by simpa using h) (by simpa using ih)
      simpa using back

/-- **Commutativity is confluent**: every reduction can be retraced. -/
theorem comm_confluent (W : Type) : Confluent (Step (W := W) [comm]) := by
  intro s left right toLeft toRight
  have back : ∀ {a b : Term Sym W}, Steps [comm] a b → Steps [comm] b a := by
    intro a b steps
    induction steps with
    | refl => exact .refl
    | tail _ step ih => exact Relation.ReflTransGen.head (comm_symmetric step) ih
  exact ⟨right, (back toLeft).trans toRight, .refl⟩

theorem comm_loop : loopSearch 4 [comm] = .found := by decide

/-- **Refused by the termination part**: the sides unify at `x + x`. -/
theorem comm_format : rulesWellFormed ([] ++ [comm]) = true := by decide

theorem comm_refuted (k : ℕ) (I : LinearInterpretation Sym) :
    ∃ obstruction, admissionRun k ⟨[], [comm], I⟩ = .refuted obstruction :=
  admissionRun_refuted_of_loop comm_format comm_loop

theorem comm_not_terminating : ¬ TerminatingAt [comm] ℕ := not_terminating_of_loopSearch comm_loop

/-! ## Refused: a fork on an existing head -/

def forkBase : List (Rule Sym ℕ) := [⟨.app .f [x], .app .z []⟩]
def forkDelta : List (Rule Sym ℕ) := [⟨.app .f [x], .app .o []⟩]

theorem fork_not_fresh : freshHeadsCheck forkBase forkDelta = false := by decide

theorem fork_computed : (criticalPairsOf 8 (overlaps (forkBase ++ forkDelta)
    (forkBase ++ forkDelta))).isSome = true := by decide

/-- **The critical pair `(z, o)` is refuted.** -/
theorem existingHeadFork_not_locallyConfluent : ¬ LocallyConfluentAt (forkBase ++ forkDelta) (ℕ ⊕ ℕ) :=
  not_locallyConfluent_of_someApart (k := 1) (by decide) fork_computed (by decide)

/-! ## Admitted -/

/-- **`x + 0 ↦ x` alone is admitted.** -/
theorem unitAlone_admitted :
    ∃ evidence, admissionRun 1 ⟨[], [⟨addT x zeroT, x⟩], additionOrder⟩ = .established evidence :=
  admissionRun_established (n := 8) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The left unit is true in `ℕ`. -/
theorem leftUnit_valid : numbers.Valid leftUnit := by
  intro α; simp [leftUnit, addT, zeroT, x, numbers]

/-- The left unit is promoted onto the existing head `add`. -/
theorem leftUnit_not_fresh : freshHeadsCheck peano [leftUnit] = false := by decide

/-- **The left unit promoted into addition is admitted.** -/
theorem leftUnit_admitted :
    ∃ evidence, admissionRun 2 ⟨peano, [leftUnit], additionOrder⟩ = .established evidence :=
  admissionRun_established (n := 8) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The rules of a monoid. -/
def monoid : List (Rule Sym ℕ) :=
  [⟨mulT (mulT x y) w, mulT x (mulT y w)⟩, ⟨mulT unitT x, x⟩, ⟨mulT x unitT, x⟩]

/-- A certificate for monoid normalization: `· ↦ 1 + 2x + y`, `e ↦ 1`. -/
def monoidOrder : LinearInterpretation Sym where
  weight
    | .mul => 1
    | .unit => 1
    | _ => 0
  extra
    | .mul, 0 => 1
    | _, _ => 0

/-- The monoid rules are true in `(ℕ, +, 0)`. -/
theorem monoid_valid : ∀ ρ ∈ monoid, numbers.Valid ρ := by
  intro ρ mem
  simp only [monoid, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl <;> intro α <;>
    simp [mulT, unitT, x, y, w, numbers, Nat.add_assoc]

/-- **Monoid normalization is admitted.** -/
theorem monoid_admitted :
    ∃ evidence, admissionRun 3 ⟨[], monoid, monoidOrder⟩ = .established evidence :=
  admissionRun_established (n := 12) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Conversion of monoid words is decided by normal forms**, and sound for `(ℕ, +, 0)`. -/
theorem monoid_decided (W : Type) :
    (∀ S : Set (Term Sym W), DecidedOn (Step ([] ++ monoid)) S) ∧
      ∀ {s t : Term Sym W}, EqvGen (Step ([] ++ monoid)) s t → ∀ α, numbers.eval α s = numbers.eval α t := by
  obtain ⟨evidence, ran⟩ := monoid_admitted
  exact admitted_of_established ran numbers
    (fun ρ mem => monoid_valid ρ (by simpa [PromotionRequest.rules] using mem)) W

/-! ## Admitted: fresh heads -/

def freshBase : List (Rule Sym ℕ) := [⟨.app .f [x], .app .z []⟩]
def freshDelta : List (Rule Sym ℕ) :=
  [⟨.app .g [zeroT], .app .o []⟩, ⟨.app .g [succT x], .app .g [x]⟩]

theorem fresh_check : freshHeadsCheck freshBase freshDelta = true := by decide

theorem fresh_rows : rowsApartCheck 8 freshDelta = true := by decide

theorem freshBase_computed : (criticalPairsOf 8 (overlaps freshBase freshBase)).isSome = true := by
  decide

/-- **Fresh heads are admitted with no critical-pair evidence**: the overlap condition holds by
construction, and a certificate gives termination. -/
theorem fresh_admitted : ConvergentRules (freshBase ++ freshDelta) :=
  admit_convergent (fun ρ mem => (rulesWellFormed_iff.mp (by decide)) ρ mem)
    (locallyConfluent_of_allJoined freshBase_computed (k := 1) (by decide))
    (freshHeads_of_check fresh_check) (rowsApart_of_check fresh_rows)
    (fun _ => additionOrder.terminating_of_orients (by decide))

/-! ## Two promotions checked against one base -/

/-- `f 0 ↦ z`. -/
def toZ : Rule Sym ℕ := ⟨.app .f [zeroT], .app .z []⟩

/-- `f 0 ↦ o`. -/
def toO : Rule Sym ℕ := ⟨.app .f [zeroT], .app .o []⟩

/-- **Each promotion alone is admitted** against the empty base. -/
theorem concurrent_each_admitted :
    (∃ evidence, admissionRun 1 ⟨[], [toZ], additionOrder⟩ = .established evidence) ∧
      ∃ evidence, admissionRun 1 ⟨[], [toO], additionOrder⟩ = .established evidence :=
  ⟨admissionRun_established (n := 8) (by decide) (by decide) (by decide) (by decide) (by decide),
    admissionRun_established (n := 8) (by decide) (by decide) (by decide) (by decide) (by decide)⟩

theorem concurrent_computed : (criticalPairsOf 8 (overlaps ([] ++ [toZ, toO])
    ([] ++ [toZ, toO]))).isSome = true := by decide

/-- **Both together are not locally confluent**: a promotion's check reads every rule of the
bubble, so two promotions checked against the same base can each pass and fail together. -/
theorem concurrent_union_not_locallyConfluent : ¬ LocallyConfluentAt ([] ++ [toZ, toO]) (ℕ ⊕ ℕ) :=
  not_locallyConfluent_of_someApart (k := 1) (by decide) concurrent_computed (by decide)

/-! ## The budget -/

def one : T := succT zeroT
def two : T := succT (succT zeroT)

/-- **Incomplete at budget one, established at budget two.** -/
theorem incomplete_then_established :
    (joinRun peano 1 (addT one one, two)).publicStatus = .incomplete ∧
      (joinRun peano 2 (addT one one, two)).publicStatus = .established := by
  decide

/-! ## Axiom audit -/

#print axioms zeroSwap_not_locallyConfluent
#print axioms zeroSwap_not_terminating
#print axioms zeroSwap_no_certificate
#print axioms zeroSwap_refuted
#print axioms comm_locallyConfluent
#print axioms comm_confluent
#print axioms comm_refuted
#print axioms existingHeadFork_not_locallyConfluent
#print axioms unitAlone_admitted
#print axioms leftUnit_admitted
#print axioms monoid_admitted
#print axioms monoid_decided
#print axioms fresh_admitted
#print axioms incomplete_then_established
#print axioms concurrent_each_admitted
#print axioms concurrent_union_not_locallyConfluent

/-! ## Positive and negative controls of the admission conditions -/

/-- **Promoted steps, positive and negative**: promoting "add two" into "add one" steps from `0` to
`2`, and still not from `0` to `3`. -/
theorem promoted_by_delta :
    promoted (fun a b : ℕ => b = a + 1) (fun a b => b = a + 2) 0 2 ∧
      ¬ promoted (fun a b : ℕ => b = a + 1) (fun a b => b = a + 2) 0 3 := by
  unfold promoted; decide

/-- **Convergent, positive**: the admitted fresh-head extension is locally confluent and
terminating. (`BubbleControls.zeroSwapJoin_not_convergent` is the negative control.) -/
theorem fresh_convergent : Convergent (Step (W := ℕ) (freshBase ++ freshDelta)) :=
  fresh_admitted.convergent ℕ

/-- **Terminating, positive**: its steps terminate on every term. (`zeroSwap_not_terminating` and
`comm_not_terminating` are negative controls.) -/
theorem fresh_terminating : TerminatingAt (freshBase ++ freshDelta) ℕ := (fresh_admitted ℕ).2

/-- **Rows apart, positive**: the two new rows `g 0` and `g (s x)` have no common instance. -/
theorem fresh_rowsApart : RowsApart freshDelta := rowsApart_of_check fresh_rows

/-- **Rows apart, negative**: `f 0 ↦ z` and `f 0 ↦ o` share their left side. -/
theorem overlapping_rows_not_apart : ¬ RowsApart [toZ, toO] := by
  intro apart
  have different : toZ ≠ toO := fun same => by
    have := congrArg Rule.rhs same
    simp [toZ, toO] at this
  exact apart toZ (by simp) toO (by simp) different ℕ (fun _ => .var 0) (fun _ => .var 0) rfl

/-- **Fresh heads, positive**: the new rows have a root symbol no base rule uses. -/
theorem fresh_freshHeads : FreshHeads freshBase freshDelta := freshHeads_of_check fresh_check

/-- **Fresh heads, negative**: the zero swap's root, `add`, is a symbol of the Peano rules. -/
theorem zeroSwap_not_freshHeads : ¬ FreshHeads peano [zeroSwap] := by
  intro fresh
  exact fresh.rootFresh zeroSwap List.mem_cons_self .add rfl ⟨addT x zeroT, x⟩
    (by unfold peano; exact List.mem_cons_self)
    (by simp [addT, zeroT, x, Term.symbols, Term.symbolsList])

/-- **Convergent rules, negative**: the Peano rules with the zero swap do not terminate.
(`fresh_admitted` is the positive control.) -/
theorem zeroSwap_not_convergentRules : ¬ ConvergentRules (peano ++ [zeroSwap]) := fun convergent =>
  zeroSwap_not_terminating (convergent ℕ).2

end Mettapedia.TypeTheory.PromotionAdmission.Controls
