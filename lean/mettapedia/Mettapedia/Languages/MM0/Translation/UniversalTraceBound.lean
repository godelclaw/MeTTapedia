import Mettapedia.Languages.MM0.Translation.CertificateEquivalence
import Mettapedia.Languages.MM0.Translation.FirstOrderUniversality

/-!
# A proved size gap between explicit and computing certificates of halting

The universal MM0 theory of `FirstOrderUniversality` accepts a proof that a code halts
exactly when it does. Such a proof is explicit: every stage of the computation is a
step of the proof. A computing checker instead receives only a bound on the work and
runs the code itself (`runFuel`, `fuelChecker`). Both checkers are exact for halting
(`fuelChecker_authority`, `FirstOrderUniversality.mm0_checks_halts_iff`).

This module proves that the explicit checker pays for every stage, and that the
computing checker does not.

* **Stages.** In the presentation of partial recursive functions, a tree for stage `k`
  of a primitive recursion has more than `k` nodes, since each stage needs the one
  before (`stage_bound`). The proof inverts trees rule by rule
  (`invert_prec_succ`, `invert_eval_comp`, `invert_eval_prec`, `invert_halts`) and
  pins intermediate values by the presentation's own soundness.
* **Family.** `powCode n` sends `0` to `2 ^ n` by doubling `n` times, each doubling an
  addition by primitive recursion. Its description grows linearly in `n`
  (`haltsTerm_powCode_size`), but its last doubling runs `2 ^ n` stages
  (`halts_tree_bound`).
* **MM0.** Through the read-back of `CertificateEquivalence`, every proof that the MM0
  checker accepts for `powCode (n + 1)` halting on `0` has more than `2 ^ n` nodes
  (`witness_bound`).
* **Fuel.** The computing checker accepts the same claim with the fuel `2 ^ (n + 1)`,
  written in `n + 2` bits (`fuel_accepts_powCode`).
* **Gap.** So the MM0 checker of the universal theory does not size-simulate the fuel
  checker (`no_sizeSimulation`): no translation turns fuel certificates into MM0
  proofs of polynomially bounded size.

The separation is about this theory. A theory with induction can prove the same claims
with short proofs, and lower bounds between proof systems in general are open.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Translation.UniversalTraceBound

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
open Mettapedia.GSLT.LanguageDef.PartialRecursive
open Mettapedia.GSLT.LanguageDef.ProofSystems
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Kernel FirstOrderSyntax FirstOrderTyping FirstOrderRules
open CertificateSimulation CertificateEquivalence FirstOrderUniversality
open Nat.Partrec (Code)
open Polynomial

/-! ## The family -/

/-- The step of addition: from `pair a (pair y i)`, the successor of `i`. -/
def addStep : Code := .comp .succ (.comp .right .right)

/-- Addition: `pair a b ↦ a + b`, by primitive recursion on `b`. -/
def addCode : Code := .prec Code.id addStep

/-- Doubling: `x ↦ x + x`. -/
def doubleCode : Code := .comp addCode (.pair Code.id Code.id)

/-- `powCode n` sends `0` to `2 ^ n`: one, doubled `n` times. -/
def powCode : ℕ → Code
  | 0 => .comp .succ .zero
  | n + 1 => .comp doubleCode (powCode n)

theorem mem_eval_zero (n : ℕ) : 0 ∈ Code.zero.eval n := Part.mem_some 0

theorem mem_eval_succ (n : ℕ) : n + 1 ∈ Code.succ.eval n := Part.mem_some (n + 1)

theorem mem_eval_right (a b : ℕ) : b ∈ Code.right.eval (Nat.pair a b) := by
  show b ∈ Part.some (Nat.pair a b).unpair.2
  rw [Nat.unpair_pair]
  exact Part.mem_some b

theorem mem_eval_comp {f g : Code} {n x y : ℕ} (inner : x ∈ g.eval n) (outer : y ∈ f.eval x) :
    y ∈ (Code.comp f g).eval n :=
  Part.mem_bind_iff.mpr ⟨x, inner, outer⟩

theorem addStep_eval (a y i : ℕ) :
    addStep.eval (Nat.pair a (Nat.pair y i)) = Part.some (i + 1) :=
  Part.eq_some_iff.mpr (mem_eval_comp (mem_eval_comp (mem_eval_right a (Nat.pair y i))
    (mem_eval_right y i)) (mem_eval_succ i))

theorem precValue_add (a : ℕ) : ∀ b, precValue Code.id addStep a b = Part.some (a + b)
  | 0 => by simp [precValue]
  | b + 1 => by
      rw [precValue, precValue_add a b]
      refine Part.eq_some_iff.mpr (Part.mem_bind_iff.mpr ⟨a + b, Part.mem_some _, ?_⟩)
      rw [addStep_eval]
      exact Part.mem_some_iff.mpr (by omega)

theorem addCode_eval (a b : ℕ) : addCode.eval (Nat.pair a b) = Part.some (a + b) := by
  rw [addCode, prec_eval, precValue_add]

theorem pairId_eval (x : ℕ) : (Code.pair Code.id Code.id).eval x = Part.some (Nat.pair x x) := by
  simp [Code.eval, Seq.seq]

theorem doubleCode_eval (x : ℕ) : doubleCode.eval x = Part.some (x + x) := by
  rw [show doubleCode.eval x = (Code.pair Code.id Code.id).eval x >>= addCode.eval from rfl]
  refine Part.eq_some_iff.mpr (Part.mem_bind_iff.mpr ⟨Nat.pair x x, ?_, ?_⟩)
  · rw [pairId_eval]
    exact Part.mem_some _
  · rw [addCode_eval]
    exact Part.mem_some _

theorem powCode_eval : ∀ n, (powCode n).eval 0 = Part.some (2 ^ n)
  | 0 => Part.eq_some_iff.mpr (by
      rw [pow_zero]
      exact mem_eval_comp (mem_eval_zero 0) (mem_eval_succ 0))
  | n + 1 => by
      rw [show (powCode (n + 1)).eval 0 = (powCode n).eval 0 >>= doubleCode.eval from rfl,
        powCode_eval n]
      refine Part.eq_some_iff.mpr (Part.mem_bind_iff.mpr ⟨2 ^ n, Part.mem_some _, ?_⟩)
      rw [doubleCode_eval]
      exact Part.mem_some_iff.mpr (by rw [pow_succ]; omega)

/-! ## Inverting trees of the universal presentation -/

/-- A closed tree of the presentation of partial recursive functions. -/
abbrev ClosedChecks (tree : RawOpenProof) (pattern : Pattern) : Prop :=
  SortedFirstOrderRules.Checks language rules [] [] tree pattern

theorem valid_of_closed {tree : RawOpenProof} {pattern : Pattern}
    (checked : ClosedChecks tree pattern) : Valid pattern :=
  valid_of_derives checked.derives

/-- A tree for a stage of primitive recursion past the first ends with `precSucc`, whose
first premise is the stage before. -/
theorem invert_prec_succ {tree : RawOpenProof} {pattern : Pattern} (checked : ClosedChecks tree pattern)
    {F G A K M : Pattern} (shape : pattern = precP F G A K M) (positive : 0 < natValue K) :
    ∃ invocation child rest K' I, tree = .node invocation (child :: rest) ∧
      ClosedChecks child (precP F G A K' I) ∧ natValue K = natValue K' + 1 := by
  cases checked with
  | premise lookup => simp at lookup
  | @rule invocation chosen children lookup arity _ _ childrenChecked =>
      obtain ⟨ruleId, arguments⟩ := invocation
      dsimp only at lookup arity shape childrenChecked ⊢
      obtain ⟨member, -⟩ := lookupRule?_member lookup
      simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · obtain ⟨x1, rfl⟩ := list_one arity
        rw [addZero_conclusion] at shape
        simp [addP, precP] at shape
      · obtain ⟨x1, x2, x3, rfl⟩ := list_three arity
        rw [addSucc_conclusion] at shape
        simp [addP, precP] at shape
      · obtain ⟨x1, rfl⟩ := list_one arity
        rw [mulZero_conclusion] at shape
        simp [mulP, precP] at shape
      · obtain ⟨x1, x2, x3, x4, rfl⟩ := list_four arity
        rw [mulSucc_conclusion] at shape
        simp [mulP, precP] at shape
      · obtain ⟨x1, rfl⟩ := list_one arity
        rw [ltZero_conclusion] at shape
        simp [ltP, precP] at shape
      · obtain ⟨x1, x2, rfl⟩ := list_two arity
        rw [ltSucc_conclusion] at shape
        simp [ltP, precP] at shape
      · obtain ⟨x1, rfl⟩ := list_one arity
        rw [leZero_conclusion] at shape
        simp [leP, precP] at shape
      · obtain ⟨x1, x2, rfl⟩ := list_two arity
        rw [leSucc_conclusion] at shape
        simp [leP, precP] at shape
      · obtain ⟨x1, x2, x3, x4, rfl⟩ := list_four arity
        rw [pairBelow_conclusion] at shape
        simp [pairP, precP] at shape
      · obtain ⟨x1, x2, x3, x4, x5, rfl⟩ := list_five arity
        rw [pairAbove_conclusion] at shape
        simp [pairP, precP] at shape
      · obtain ⟨x1, rfl⟩ := list_one arity
        rw [evalZero_conclusion] at shape
        simp [evalP, precP] at shape
      · obtain ⟨x1, rfl⟩ := list_one arity
        rw [evalSucc_conclusion] at shape
        simp [evalP, precP] at shape
      · obtain ⟨x1, x2, x3, rfl⟩ := list_three arity
        rw [evalLeft_conclusion] at shape
        simp [evalP, precP] at shape
      · obtain ⟨x1, x2, x3, rfl⟩ := list_three arity
        rw [evalRight_conclusion] at shape
        simp [evalP, precP] at shape
      · obtain ⟨x1, x2, x3, x4, x5, x6, rfl⟩ := list_six arity
        rw [evalPair_conclusion] at shape
        simp [evalP, precP] at shape
      · obtain ⟨x1, x2, x3, x4, x5, rfl⟩ := list_five arity
        rw [evalComp_conclusion] at shape
        simp [evalP, precP] at shape
      · obtain ⟨x1, x2, x3, x4, rfl⟩ := list_four arity
        rw [precZero_conclusion] at shape
        simp only [precP, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at shape
        obtain ⟨-, -, -, rfl, -⟩ := shape
        simp at positive
      · obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8, rfl⟩ := list_eight arity
        rw [precSucc_conclusion] at shape
        simp only [precP, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at shape
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := shape
        rw [precSucc_premises] at childrenChecked
        cases childrenChecked with
        | cons first _ => exact ⟨_, _, _, x4, x5, rfl, first, by simp⟩
      · obtain ⟨x1, x2, x3, x4, x5, x6, rfl⟩ := list_six arity
        rw [evalPrec_conclusion] at shape
        simp [evalP, precP] at shape
      · obtain ⟨x1, x2, x3, rfl⟩ := list_three arity
        rw [searchZero_conclusion] at shape
        simp [searchP, precP] at shape
      · obtain ⟨x1, x2, x3, x4, x5, x6, x7, rfl⟩ := list_seven arity
        rw [searchSucc_conclusion] at shape
        simp [searchP, precP] at shape
      · obtain ⟨x1, x2, x3, x4, x5, x6, x7, rfl⟩ := list_seven arity
        rw [evalSearch_conclusion] at shape
        simp [evalP, precP] at shape
      · obtain ⟨x1, x2, x3, rfl⟩ := list_three arity
        rw [halting_conclusion] at shape
        simp [haltsP, precP] at shape

/-- A tree for the evaluation of a composite ends with `evalComp`. -/
theorem invert_eval_comp {tree : RawOpenProof} {pattern : Pattern} (checked : ClosedChecks tree pattern)
    {X Y N M : Pattern} (shape : pattern = evalP (ccompP X Y) N M) :
    ∃ invocation first second rest K, tree = .node invocation (first :: second :: rest) ∧
      ClosedChecks first (evalP Y N K) ∧ ClosedChecks second (evalP X K M) := by
  cases checked with
  | premise lookup => simp at lookup
  | @rule invocation chosen children lookup arity _ _ childrenChecked =>
      obtain ⟨ruleId, arguments⟩ := invocation
      dsimp only at lookup arity shape childrenChecked ⊢
      obtain ⟨member, -⟩ := lookupRule?_member lookup
      simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · obtain ⟨x1, rfl⟩ := list_one arity
        rw [addZero_conclusion] at shape
        simp [addP, evalP] at shape
      · obtain ⟨x1, x2, x3, rfl⟩ := list_three arity
        rw [addSucc_conclusion] at shape
        simp [addP, evalP] at shape
      · obtain ⟨x1, rfl⟩ := list_one arity
        rw [mulZero_conclusion] at shape
        simp [mulP, evalP] at shape
      · obtain ⟨x1, x2, x3, x4, rfl⟩ := list_four arity
        rw [mulSucc_conclusion] at shape
        simp [mulP, evalP] at shape
      · obtain ⟨x1, rfl⟩ := list_one arity
        rw [ltZero_conclusion] at shape
        simp [ltP, evalP] at shape
      · obtain ⟨x1, x2, rfl⟩ := list_two arity
        rw [ltSucc_conclusion] at shape
        simp [ltP, evalP] at shape
      · obtain ⟨x1, rfl⟩ := list_one arity
        rw [leZero_conclusion] at shape
        simp [leP, evalP] at shape
      · obtain ⟨x1, x2, rfl⟩ := list_two arity
        rw [leSucc_conclusion] at shape
        simp [leP, evalP] at shape
      · obtain ⟨x1, x2, x3, x4, rfl⟩ := list_four arity
        rw [pairBelow_conclusion] at shape
        simp [pairP, evalP] at shape
      · obtain ⟨x1, x2, x3, x4, x5, rfl⟩ := list_five arity
        rw [pairAbove_conclusion] at shape
        simp [pairP, evalP] at shape
      · obtain ⟨x1, rfl⟩ := list_one arity
        rw [evalZero_conclusion] at shape
        simp [evalP, czeroP, ccompP] at shape
      · obtain ⟨x1, rfl⟩ := list_one arity
        rw [evalSucc_conclusion] at shape
        simp [evalP, csuccP, ccompP] at shape
      · obtain ⟨x1, x2, x3, rfl⟩ := list_three arity
        rw [evalLeft_conclusion] at shape
        simp [evalP, cleftP, ccompP] at shape
      · obtain ⟨x1, x2, x3, rfl⟩ := list_three arity
        rw [evalRight_conclusion] at shape
        simp [evalP, crightP, ccompP] at shape
      · obtain ⟨x1, x2, x3, x4, x5, x6, rfl⟩ := list_six arity
        rw [evalPair_conclusion] at shape
        simp [evalP, cpairP, ccompP] at shape
      · obtain ⟨x1, x2, x3, x4, x5, rfl⟩ := list_five arity
        rw [evalComp_conclusion] at shape
        simp only [evalP, ccompP, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at shape
        obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := shape
        rw [evalComp_premises] at childrenChecked
        cases childrenChecked with
        | cons first rest =>
            cases rest with
            | cons second _ => exact ⟨_, _, _, _, x4, rfl, first, second⟩
      · obtain ⟨x1, x2, x3, x4, rfl⟩ := list_four arity
        rw [precZero_conclusion] at shape
        simp [precP, evalP] at shape
      · obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8, rfl⟩ := list_eight arity
        rw [precSucc_conclusion] at shape
        simp [precP, evalP] at shape
      · obtain ⟨x1, x2, x3, x4, x5, x6, rfl⟩ := list_six arity
        rw [evalPrec_conclusion] at shape
        simp [evalP, cprecP, ccompP] at shape
      · obtain ⟨x1, x2, x3, rfl⟩ := list_three arity
        rw [searchZero_conclusion] at shape
        simp [searchP, evalP] at shape
      · obtain ⟨x1, x2, x3, x4, x5, x6, x7, rfl⟩ := list_seven arity
        rw [searchSucc_conclusion] at shape
        simp [searchP, evalP] at shape
      · obtain ⟨x1, x2, x3, x4, x5, x6, x7, rfl⟩ := list_seven arity
        rw [evalSearch_conclusion] at shape
        simp [evalP, crfindP, ccompP] at shape
      · obtain ⟨x1, x2, x3, rfl⟩ := list_three arity
        rw [halting_conclusion] at shape
        simp [haltsP, evalP] at shape

/-- A tree for the evaluation of a primitive recursion ends with `evalPrec`. -/
theorem invert_eval_prec {tree : RawOpenProof} {pattern : Pattern} (checked : ClosedChecks tree pattern)
    {X Y N M : Pattern} (shape : pattern = evalP (cprecP X Y) N M) :
    ∃ invocation first second rest A J, tree = .node invocation (first :: second :: rest) ∧
      ClosedChecks first (pairP A J N) ∧ ClosedChecks second (precP X Y A J M) := by
  cases checked with
  | premise lookup => simp at lookup
  | @rule invocation chosen children lookup arity _ _ childrenChecked =>
      obtain ⟨ruleId, arguments⟩ := invocation
      dsimp only at lookup arity shape childrenChecked ⊢
      obtain ⟨member, -⟩ := lookupRule?_member lookup
      simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · obtain ⟨x1, rfl⟩ := list_one arity
        rw [addZero_conclusion] at shape
        simp [addP, evalP] at shape
      · obtain ⟨x1, x2, x3, rfl⟩ := list_three arity
        rw [addSucc_conclusion] at shape
        simp [addP, evalP] at shape
      · obtain ⟨x1, rfl⟩ := list_one arity
        rw [mulZero_conclusion] at shape
        simp [mulP, evalP] at shape
      · obtain ⟨x1, x2, x3, x4, rfl⟩ := list_four arity
        rw [mulSucc_conclusion] at shape
        simp [mulP, evalP] at shape
      · obtain ⟨x1, rfl⟩ := list_one arity
        rw [ltZero_conclusion] at shape
        simp [ltP, evalP] at shape
      · obtain ⟨x1, x2, rfl⟩ := list_two arity
        rw [ltSucc_conclusion] at shape
        simp [ltP, evalP] at shape
      · obtain ⟨x1, rfl⟩ := list_one arity
        rw [leZero_conclusion] at shape
        simp [leP, evalP] at shape
      · obtain ⟨x1, x2, rfl⟩ := list_two arity
        rw [leSucc_conclusion] at shape
        simp [leP, evalP] at shape
      · obtain ⟨x1, x2, x3, x4, rfl⟩ := list_four arity
        rw [pairBelow_conclusion] at shape
        simp [pairP, evalP] at shape
      · obtain ⟨x1, x2, x3, x4, x5, rfl⟩ := list_five arity
        rw [pairAbove_conclusion] at shape
        simp [pairP, evalP] at shape
      · obtain ⟨x1, rfl⟩ := list_one arity
        rw [evalZero_conclusion] at shape
        simp [evalP, czeroP, cprecP] at shape
      · obtain ⟨x1, rfl⟩ := list_one arity
        rw [evalSucc_conclusion] at shape
        simp [evalP, csuccP, cprecP] at shape
      · obtain ⟨x1, x2, x3, rfl⟩ := list_three arity
        rw [evalLeft_conclusion] at shape
        simp [evalP, cleftP, cprecP] at shape
      · obtain ⟨x1, x2, x3, rfl⟩ := list_three arity
        rw [evalRight_conclusion] at shape
        simp [evalP, crightP, cprecP] at shape
      · obtain ⟨x1, x2, x3, x4, x5, x6, rfl⟩ := list_six arity
        rw [evalPair_conclusion] at shape
        simp [evalP, cpairP, cprecP] at shape
      · obtain ⟨x1, x2, x3, x4, x5, rfl⟩ := list_five arity
        rw [evalComp_conclusion] at shape
        simp [evalP, ccompP, cprecP] at shape
      · obtain ⟨x1, x2, x3, x4, rfl⟩ := list_four arity
        rw [precZero_conclusion] at shape
        simp [precP, evalP] at shape
      · obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8, rfl⟩ := list_eight arity
        rw [precSucc_conclusion] at shape
        simp [precP, evalP] at shape
      · obtain ⟨x1, x2, x3, x4, x5, x6, rfl⟩ := list_six arity
        rw [evalPrec_conclusion] at shape
        simp only [evalP, cprecP, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at shape
        obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := shape
        rw [evalPrec_premises] at childrenChecked
        cases childrenChecked with
        | cons first rest =>
            cases rest with
            | cons second _ => exact ⟨_, _, _, _, x3, x4, rfl, first, second⟩
      · obtain ⟨x1, x2, x3, rfl⟩ := list_three arity
        rw [searchZero_conclusion] at shape
        simp [searchP, evalP] at shape
      · obtain ⟨x1, x2, x3, x4, x5, x6, x7, rfl⟩ := list_seven arity
        rw [searchSucc_conclusion] at shape
        simp [searchP, evalP] at shape
      · obtain ⟨x1, x2, x3, x4, x5, x6, x7, rfl⟩ := list_seven arity
        rw [evalSearch_conclusion] at shape
        simp [evalP, crfindP, cprecP] at shape
      · obtain ⟨x1, x2, x3, rfl⟩ := list_three arity
        rw [halting_conclusion] at shape
        simp [haltsP, evalP] at shape

/-- A tree for a halting judgment ends with `halting`. -/
theorem invert_halts {tree : RawOpenProof} {pattern : Pattern} (checked : ClosedChecks tree pattern)
    {C N : Pattern} (shape : pattern = haltsP C N) :
    ∃ invocation child rest M, tree = .node invocation (child :: rest) ∧
      ClosedChecks child (evalP C N M) := by
  cases checked with
  | premise lookup => simp at lookup
  | @rule invocation chosen children lookup arity _ _ childrenChecked =>
      obtain ⟨ruleId, arguments⟩ := invocation
      dsimp only at lookup arity shape childrenChecked ⊢
      obtain ⟨member, -⟩ := lookupRule?_member lookup
      simp only [rules, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · obtain ⟨x1, rfl⟩ := list_one arity
        rw [addZero_conclusion] at shape
        simp [addP, haltsP] at shape
      · obtain ⟨x1, x2, x3, rfl⟩ := list_three arity
        rw [addSucc_conclusion] at shape
        simp [addP, haltsP] at shape
      · obtain ⟨x1, rfl⟩ := list_one arity
        rw [mulZero_conclusion] at shape
        simp [mulP, haltsP] at shape
      · obtain ⟨x1, x2, x3, x4, rfl⟩ := list_four arity
        rw [mulSucc_conclusion] at shape
        simp [mulP, haltsP] at shape
      · obtain ⟨x1, rfl⟩ := list_one arity
        rw [ltZero_conclusion] at shape
        simp [ltP, haltsP] at shape
      · obtain ⟨x1, x2, rfl⟩ := list_two arity
        rw [ltSucc_conclusion] at shape
        simp [ltP, haltsP] at shape
      · obtain ⟨x1, rfl⟩ := list_one arity
        rw [leZero_conclusion] at shape
        simp [leP, haltsP] at shape
      · obtain ⟨x1, x2, rfl⟩ := list_two arity
        rw [leSucc_conclusion] at shape
        simp [leP, haltsP] at shape
      · obtain ⟨x1, x2, x3, x4, rfl⟩ := list_four arity
        rw [pairBelow_conclusion] at shape
        simp [pairP, haltsP] at shape
      · obtain ⟨x1, x2, x3, x4, x5, rfl⟩ := list_five arity
        rw [pairAbove_conclusion] at shape
        simp [pairP, haltsP] at shape
      · obtain ⟨x1, rfl⟩ := list_one arity
        rw [evalZero_conclusion] at shape
        simp [evalP, haltsP] at shape
      · obtain ⟨x1, rfl⟩ := list_one arity
        rw [evalSucc_conclusion] at shape
        simp [evalP, haltsP] at shape
      · obtain ⟨x1, x2, x3, rfl⟩ := list_three arity
        rw [evalLeft_conclusion] at shape
        simp [evalP, haltsP] at shape
      · obtain ⟨x1, x2, x3, rfl⟩ := list_three arity
        rw [evalRight_conclusion] at shape
        simp [evalP, haltsP] at shape
      · obtain ⟨x1, x2, x3, x4, x5, x6, rfl⟩ := list_six arity
        rw [evalPair_conclusion] at shape
        simp [evalP, haltsP] at shape
      · obtain ⟨x1, x2, x3, x4, x5, rfl⟩ := list_five arity
        rw [evalComp_conclusion] at shape
        simp [evalP, haltsP] at shape
      · obtain ⟨x1, x2, x3, x4, rfl⟩ := list_four arity
        rw [precZero_conclusion] at shape
        simp [precP, haltsP] at shape
      · obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8, rfl⟩ := list_eight arity
        rw [precSucc_conclusion] at shape
        simp [precP, haltsP] at shape
      · obtain ⟨x1, x2, x3, x4, x5, x6, rfl⟩ := list_six arity
        rw [evalPrec_conclusion] at shape
        simp [evalP, haltsP] at shape
      · obtain ⟨x1, x2, x3, rfl⟩ := list_three arity
        rw [searchZero_conclusion] at shape
        simp [searchP, haltsP] at shape
      · obtain ⟨x1, x2, x3, x4, x5, x6, x7, rfl⟩ := list_seven arity
        rw [searchSucc_conclusion] at shape
        simp [searchP, haltsP] at shape
      · obtain ⟨x1, x2, x3, x4, x5, x6, x7, rfl⟩ := list_seven arity
        rw [evalSearch_conclusion] at shape
        simp [evalP, haltsP] at shape
      · obtain ⟨x1, x2, x3, rfl⟩ := list_three arity
        rw [halting_conclusion] at shape
        simp only [haltsP, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at shape
        obtain ⟨rfl, rfl⟩ := shape
        rw [halting_premises] at childrenChecked
        cases childrenChecked with
        | cons first _ => exact ⟨_, _, _, x3, rfl, first⟩

/-! ## Stages -/

theorem rawSize_pos (tree : RawOpenProof) : 1 ≤ rawSize tree := by
  cases tree <;> simp [rawSize]

theorem rawSize_first (invocation : RuleInstance) (child : RawOpenProof)
    (rest : List RawOpenProof) : rawSize child + 1 ≤ rawSize (.node invocation (child :: rest)) := by
  simp only [rawSize, rawSizes]
  omega

theorem rawSize_second (invocation : RuleInstance) (first second : RawOpenProof)
    (rest : List RawOpenProof) :
    rawSize second + 1 ≤ rawSize (.node invocation (first :: second :: rest)) := by
  simp only [rawSize, rawSizes]
  omega

/-- **Stages.** A closed tree for stage `k` of a primitive recursion has more than `k`
nodes: each stage needs the one before. -/
theorem stage_bound (k : ℕ) : ∀ {tree : RawOpenProof} {F G A K M : Pattern},
    ClosedChecks tree (precP F G A K M) → natValue K = k → k + 1 ≤ rawSize tree := by
  induction k with
  | zero => intro tree _ _ _ _ _ _ _; exact rawSize_pos tree
  | succ k ih =>
      intro tree F G A K M checked stage
      obtain ⟨invocation, child, rest, K', I, rfl, childChecked, step⟩ :=
        invert_prec_succ checked rfl (by omega)
      have previous := ih childChecked (by omega)
      have parent := rawSize_first invocation child rest
      omega

/-- Every closed tree for `powCode (n + 1)` halting on `0` has more than `2 ^ n` nodes:
its last doubling adds `2 ^ n` to itself one stage at a time. -/
theorem halts_tree_bound (n : ℕ) {tree : RawOpenProof}
    (checked : ClosedChecks tree (haltsP (codePattern (powCode (n + 1))) (num 0))) :
    2 ^ n + 1 ≤ rawSize tree := by
  obtain ⟨i₁, evaluation, rest₁, M, rfl, evaluated⟩ := invert_halts checked rfl
  obtain ⟨i₂, inner, outer, rest₂, K, evaluationEq, innerChecked, outerChecked⟩ :=
    invert_eval_comp (X := codePattern doubleCode) (Y := codePattern (powCode n)) evaluated rfl
  have innerValue : natValue K = 2 ^ n := by
    have valid := valid_of_closed innerChecked
    rw [valid_eval, codeValue_codePattern, natValue_num, powCode_eval] at valid
    exact Part.mem_some_iff.mp valid
  obtain ⟨i₃, pairing, adding, rest₃, P, outerEq, pairingChecked, addingChecked⟩ :=
    invert_eval_comp (X := codePattern addCode) (Y := codePattern (.pair Code.id Code.id))
      outerChecked rfl
  have pairValue : natValue P = Nat.pair (2 ^ n) (2 ^ n) := by
    have valid := valid_of_closed pairingChecked
    rw [valid_eval, codeValue_codePattern, innerValue, pairId_eval] at valid
    exact Part.mem_some_iff.mp valid
  obtain ⟨i₄, unpairing, recursion, rest₄, A, J, addingEq, unpairingChecked, recursionChecked⟩ :=
    invert_eval_prec (X := codePattern Code.id) (Y := codePattern addStep) addingChecked rfl
  have stage : natValue J = 2 ^ n := by
    have valid := valid_of_closed unpairingChecked
    rw [valid_pair, pairValue] at valid
    exact (Nat.pair_eq_pair.mp valid).2
  have bound := stage_bound (2 ^ n) recursionChecked stage
  have s₁ := rawSize_first i₁ evaluation rest₁
  have s₂ := rawSize_second i₂ inner outer rest₂
  rw [← evaluationEq] at s₂
  have s₃ := rawSize_second i₃ pairing adding rest₃
  rw [← outerEq] at s₃
  have s₄ := rawSize_second i₄ unpairing recursion rest₄
  rw [← addingEq] at s₄
  omega

/-! ## Every accepted MM0 proof is long -/

/-- **Every proof the MM0 checker accepts that `powCode (n + 1)` halts on `0` has more
than `2 ^ n` nodes.** -/
theorem witness_bound (n : ℕ) {witness : ProofWitness}
    (accepted : ProofWitness.check presentation.theory.termSignature
      presentation.theory.definitionSignature presentation.theory.theoremSignature [] [] witness
      (haltsTerm (powCode (n + 1)) 0) = true) :
    2 ^ n + 1 ≤ Cost.proofSize witness := by
  obtain ⟨sameLanguage, -, sameRules⟩ := presentation_retains
  have checked := (ProofWitness.check_iff _ _ _ _ _ _ _).mp accepted
  obtain ⟨tree, decompiled, treeChecked⟩ := decompile_accepted (presentation := presentation)
    (by rw [sameLanguage]; rfl) (bound := []) (context := []) (hypotheses := [])
    (targetHypotheses := []) (pattern := (Judgment.halts (powCode (n + 1)) 0).pattern)
    (by rw [Signature.sorts, sameLanguage]; exact .nil) .nil
    (by rw [Signature.names, sameLanguage]; exact encodes_judgment (.halts (powCode (n + 1)) 0))
    checked
  have size := decompile_size witness decompiled
  rw [sameLanguage, sameRules] at treeChecked
  have bound := halts_tree_bound n treeChecked
  omega

/-! ## The computing checker -/

/-- Iterate a primitive recursion `k` times from a base value. -/
def precLoop (step : ℕ → Option ℕ) (a : ℕ) (base : Option ℕ) : ℕ → Option ℕ
  | 0 => base
  | k + 1 => (precLoop step a base k).bind fun i => step (Nat.pair a (Nat.pair k i))

/-- Search for the first place where a test returns zero, looking at most `remaining`
places from `j` on. -/
def searchLoop (test : ℕ → Option ℕ) (a offset : ℕ) : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | remaining + 1, j =>
      match test (Nat.pair a (j + offset)) with
      | none => none
      | some 0 => some (j + offset)
      | some (_ + 1) => searchLoop test a offset remaining (j + 1)

/-- Run a code with every loop bounded by `fuel`: a primitive recursion may run at most
`fuel` rounds and a search may look at most `fuel + 1` places. -/
def runFuel (fuel : ℕ) : Code → ℕ → Option ℕ
  | .zero, _ => some 0
  | .succ, n => some (n + 1)
  | .left, n => some n.unpair.1
  | .right, n => some n.unpair.2
  | .pair f g, n => (runFuel fuel f n).bind fun a => (runFuel fuel g n).map (Nat.pair a)
  | .comp f g, n => (runFuel fuel g n).bind (runFuel fuel f)
  | .prec f g, n =>
      if n.unpair.2 ≤ fuel then
        precLoop (runFuel fuel g) n.unpair.1 (runFuel fuel f n.unpair.1) n.unpair.2
      else none
  | .rfind' f, n => searchLoop (runFuel fuel f) n.unpair.1 n.unpair.2 (fuel + 1) 0

theorem precLoop_sound {f g : Code} {step : ℕ → Option ℕ} {a : ℕ} {base : Option ℕ}
    (stepSound : ∀ x y, step x = some y → y ∈ g.eval x)
    (baseSound : ∀ y, base = some y → y ∈ f.eval a) :
    ∀ k y, precLoop step a base k = some y → y ∈ precValue f g a k
  | 0, y, ran => baseSound y ran
  | k + 1, y, ran => by
      simp only [precLoop, Option.bind_eq_some_iff] at ran
      obtain ⟨i, earlier, last⟩ := ran
      exact Part.mem_bind_iff.mpr ⟨i, precLoop_sound stepSound baseSound k i earlier,
        stepSound _ _ last⟩

theorem searchLoop_spec {test : ℕ → Option ℕ} {a offset : ℕ} :
    ∀ remaining j y, searchLoop test a offset remaining j = some y →
      ∃ i, j ≤ i ∧ y = i + offset ∧ test (Nat.pair a (i + offset)) = some 0 ∧
        ∀ l, j ≤ l → l < i → ∃ v, test (Nat.pair a (l + offset)) = some (v + 1)
  | 0, _, _, ran => by simp [searchLoop] at ran
  | remaining + 1, j, y, ran => by
      simp only [searchLoop] at ran
      cases tested : test (Nat.pair a (j + offset)) with
      | none => simp [tested] at ran
      | some v =>
          cases v with
          | zero =>
              simp only [tested, Option.some.injEq] at ran
              exact ⟨j, le_rfl, ran.symm, tested, fun l low high => absurd high (by omega)⟩
          | succ v =>
              simp only [tested] at ran
              obtain ⟨i, later, rfl, found, before⟩ :=
                searchLoop_spec remaining (j + 1) y ran
              refine ⟨i, by omega, rfl, found, fun l low high => ?_⟩
              rcases Nat.eq_or_lt_of_le low with same | larger
              · subst same
                exact ⟨v, tested⟩
              · exact before l (by omega) high

/-- **The fuel interpreter is sound.** -/
theorem runFuel_sound (fuel : ℕ) : ∀ (c : Code) (n y : ℕ), runFuel fuel c n = some y → y ∈ c.eval n
  | .zero, n, y, ran => by
      simp only [runFuel, Option.some.injEq] at ran
      subst ran
      exact mem_eval_zero n
  | .succ, n, y, ran => by
      simp only [runFuel, Option.some.injEq] at ran
      subst ran
      exact mem_eval_succ n
  | .left, n, y, ran => by
      simp only [runFuel, Option.some.injEq] at ran
      subst ran
      exact Part.mem_some _
  | .right, n, y, ran => by
      simp only [runFuel, Option.some.injEq] at ran
      subst ran
      exact Part.mem_some _
  | .pair f g, n, y, ran => by
      simp only [runFuel, Option.bind_eq_some_iff, Option.map_eq_some_iff] at ran
      obtain ⟨a, first, b, second, rfl⟩ := ran
      simp only [Code.eval, Seq.seq]
      exact Part.mem_bind_iff.mpr ⟨_, Part.mem_map _ (runFuel_sound fuel f n a first),
        Part.mem_map _ (runFuel_sound fuel g n b second)⟩
  | .comp f g, n, y, ran => by
      simp only [runFuel, Option.bind_eq_some_iff] at ran
      obtain ⟨x, inner, outer⟩ := ran
      exact Part.mem_bind_iff.mpr ⟨x, runFuel_sound fuel g n x inner, runFuel_sound fuel f x y outer⟩
  | .prec f g, n, y, ran => by
      simp only [runFuel] at ran
      split_ifs at ran with bounded
      have looped := precLoop_sound (f := f) (g := g)
        (fun x z ran => runFuel_sound fuel g x z ran)
        (fun z ran => runFuel_sound fuel f _ z ran) _ y ran
      rw [← Nat.pair_unpair n, prec_eval]
      exact looped
  | .rfind' f, n, y, ran => by
      simp only [runFuel] at ran
      obtain ⟨i, -, rfl, found, before⟩ := searchLoop_spec _ 0 y ran
      rw [← Nat.pair_unpair n]
      simp only [Code.eval, Nat.unpaired, Nat.unpair_pair]
      refine Part.mem_map_iff _ |>.mpr ⟨i, Nat.mem_rfind.mpr ⟨?_, fun {l} low => ?_⟩, rfl⟩
      · exact Part.mem_map_iff _ |>.mpr ⟨0, runFuel_sound fuel f _ 0 found, by simp⟩
      · obtain ⟨v, value⟩ := before l (Nat.zero_le l) low
        exact Part.mem_map_iff _ |>.mpr ⟨v + 1, runFuel_sound fuel f _ _ value, by simp⟩

/-- Doubling with enough fuel. -/
theorem runFuel_add {fuel a b : ℕ} (bounded : b ≤ fuel) :
    runFuel fuel addCode (Nat.pair a b) = some (a + b) := by
  have loop : ∀ k, precLoop (runFuel fuel addStep) a (some a) k = some (a + k) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        simp only [precLoop, ih, Option.bind_some]
        simp [runFuel, addStep, Nat.unpair_pair]
        omega
  have identity : runFuel fuel Code.id a = some a := by
    simp [runFuel, Code.id, Nat.pair_unpair]
  simp only [addCode, runFuel, Nat.unpair_pair, if_pos bounded]
  rw [identity, loop]

theorem runFuel_double {fuel x : ℕ} (bounded : x ≤ fuel) :
    runFuel fuel doubleCode x = some (x + x) := by
  have paired : runFuel fuel (Code.pair Code.id Code.id) x = some (Nat.pair x x) := by
    simp [runFuel, Code.id, Nat.pair_unpair]
  rw [show runFuel fuel doubleCode x =
      (runFuel fuel (Code.pair Code.id Code.id) x).bind (runFuel fuel addCode) from rfl,
    paired, Option.bind_some, runFuel_add bounded]

theorem runFuel_pow {fuel : ℕ} : ∀ n, 2 ^ n ≤ fuel → runFuel fuel (powCode n) 0 = some (2 ^ n)
  | 0, _ => by simp [powCode, runFuel]
  | n + 1, bounded => by
      have half : 2 ^ n ≤ fuel := le_trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ n)) bounded
      rw [show runFuel fuel (powCode (n + 1)) 0 =
          (runFuel fuel (powCode n) 0).bind (runFuel fuel doubleCode) from rfl,
        runFuel_pow n half, Option.bind_some, runFuel_double half, pow_succ, Nat.mul_two]

/-- The computing checker of halting: a claim is a code and an input, and a certificate
is the fuel, written in binary. -/
def fuelChecker : SizedChecker (Code × ℕ) ℕ where
  check claim fuel := (runFuel fuel claim.1 claim.2).isSome
  claimSize claim := (haltsTerm claim.1 claim.2).size
  certificateSize := Nat.size

theorem fuelChecker_sound : fuelChecker.Sound (fun claim => (claim.1.eval claim.2).Dom) := by
  intro claim fuel accepted
  change (runFuel fuel claim.1 claim.2).isSome = true at accepted
  obtain ⟨y, ran⟩ := Option.isSome_iff_exists.mp accepted
  exact Part.dom_iff_mem.mpr ⟨y, runFuel_sound fuel claim.1 claim.2 y ran⟩

/-- A search finds the first place where the test returns zero, given every earlier
place a positive value and enough room. -/
theorem searchLoop_complete {test : ℕ → Option ℕ} {a offset i : ℕ}
    (found : test (Nat.pair a (i + offset)) = some 0)
    (before : ∀ l < i, ∃ v, test (Nat.pair a (l + offset)) = some (v + 1)) :
    ∀ remaining j, j ≤ i → i - j < remaining → searchLoop test a offset remaining j = some (i + offset)
  | 0, _, _, room => absurd room (Nat.not_lt_zero _)
  | remaining + 1, j, low, room => by
      simp only [searchLoop]
      rcases Nat.eq_or_lt_of_le low with same | earlier
      · subst same
        rw [found]
      · obtain ⟨v, value⟩ := before j earlier
        rw [value]
        exact searchLoop_complete found before remaining (j + 1) earlier (by omega)

/-- **The fuel interpreter is complete**: every value of a code is reached by every fuel
beyond some threshold. -/
theorem runFuel_complete : ∀ (c : Code) (n y : ℕ), y ∈ c.eval n →
    ∃ threshold, ∀ fuel, threshold ≤ fuel → runFuel fuel c n = some y
  | .zero, n, y, member => ⟨0, fun _ _ => by
      have value : y = 0 := Part.mem_some_iff.mp member
      simp [runFuel, value]⟩
  | .succ, n, y, member => ⟨0, fun _ _ => by
      have value : y = n + 1 := Part.mem_some_iff.mp member
      simp [runFuel, value]⟩
  | .left, n, y, member => ⟨0, fun _ _ => by
      have value : y = n.unpair.1 := Part.mem_some_iff.mp member
      simp [runFuel, value]⟩
  | .right, n, y, member => ⟨0, fun _ _ => by
      have value : y = n.unpair.2 := Part.mem_some_iff.mp member
      simp [runFuel, value]⟩
  | .pair f g, n, y, member => by
      simp only [Code.eval, Seq.seq] at member
      obtain ⟨h, hMember, yMember⟩ := Part.mem_bind_iff.mp member
      obtain ⟨a, first, rfl⟩ := (Part.mem_map_iff _).mp hMember
      obtain ⟨b, second, rfl⟩ := (Part.mem_map_iff _).mp yMember
      obtain ⟨T₁, run₁⟩ := runFuel_complete f n a first
      obtain ⟨T₂, run₂⟩ := runFuel_complete g n b second
      refine ⟨max T₁ T₂, fun fuel enough => ?_⟩
      simp only [runFuel, run₁ fuel (le_of_max_le_left enough), run₂ fuel (le_of_max_le_right enough),
        Option.bind_some, Option.map_some]
  | .comp f g, n, y, member => by
      obtain ⟨x, inner, outer⟩ := Part.mem_bind_iff.mp member
      obtain ⟨T₁, run₁⟩ := runFuel_complete g n x inner
      obtain ⟨T₂, run₂⟩ := runFuel_complete f x y outer
      refine ⟨max T₁ T₂, fun fuel enough => ?_⟩
      simp only [runFuel, run₁ fuel (le_of_max_le_left enough), Option.bind_some]
      exact run₂ fuel (le_of_max_le_right enough)
  | .prec f g, n, y, member => by
      rw [← Nat.pair_unpair n, prec_eval] at member
      have loop : ∀ k z, z ∈ precValue f g n.unpair.1 k → ∃ threshold, ∀ fuel, threshold ≤ fuel →
          precLoop (runFuel fuel g) n.unpair.1 (runFuel fuel f n.unpair.1) k = some z := by
        intro k
        induction k with
        | zero =>
            intro z base
            obtain ⟨T, run⟩ := runFuel_complete f n.unpair.1 z base
            exact ⟨T, fun fuel enough => run fuel enough⟩
        | succ k ih =>
            intro z step
            obtain ⟨i, earlier, last⟩ := Part.mem_bind_iff.mp step
            obtain ⟨T₁, run₁⟩ := ih i earlier
            obtain ⟨T₂, run₂⟩ := runFuel_complete g _ z last
            refine ⟨max T₁ T₂, fun fuel enough => ?_⟩
            simp only [precLoop, run₁ fuel (le_of_max_le_left enough), Option.bind_some]
            exact run₂ fuel (le_of_max_le_right enough)
      obtain ⟨T, run⟩ := loop n.unpair.2 y member
      refine ⟨max T n.unpair.2, fun fuel enough => ?_⟩
      simp only [runFuel, if_pos (le_of_max_le_right enough)]
      exact run fuel (le_of_max_le_left enough)
  | .rfind' f, n, y, member => by
      rw [← Nat.pair_unpair n] at member
      simp only [Code.eval, Nat.unpaired, Nat.unpair_pair, Part.mem_map_iff] at member
      obtain ⟨i, searched, rfl⟩ := member
      obtain ⟨hit, misses⟩ := Nat.mem_rfind.mp searched
      obtain ⟨hitValue, zeroMember, zeroIs⟩ := Part.mem_map_iff _ |>.mp hit
      have zeroEq : hitValue = 0 := by simpa using zeroIs
      subst zeroEq
      have positive : ∀ l < i, ∃ v, v + 1 ∈ f.eval (Nat.pair n.unpair.1 (l + n.unpair.2)) := by
        intro l low
        obtain ⟨value, valueMember, valueIs⟩ := Part.mem_map_iff _ |>.mp (misses low)
        cases value with
        | zero => simp at valueIs
        | succ v => exact ⟨v, valueMember⟩
      have thresholds : ∀ bound ≤ i, ∃ threshold, ∀ fuel, threshold ≤ fuel → ∀ l < bound,
          ∃ v, runFuel fuel f (Nat.pair n.unpair.1 (l + n.unpair.2)) = some (v + 1) := by
        intro bound
        induction bound with
        | zero => exact fun _ => ⟨0, fun _ _ l low => absurd low (Nat.not_lt_zero l)⟩
        | succ bound ih =>
            intro small
            obtain ⟨T₁, run₁⟩ := ih (by omega)
            obtain ⟨v, value⟩ := positive bound (by omega)
            obtain ⟨T₂, run₂⟩ := runFuel_complete f _ (v + 1) value
            refine ⟨max T₁ T₂, fun fuel enough l low => ?_⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp low with earlier | same
            · exact run₁ fuel (le_of_max_le_left enough) l earlier
            · subst same
              exact ⟨v, run₂ fuel (le_of_max_le_right enough)⟩
      obtain ⟨T₁, run₁⟩ := thresholds i le_rfl
      obtain ⟨T₂, run₂⟩ := runFuel_complete f _ 0 zeroMember
      refine ⟨max (max T₁ T₂) i, fun fuel enough => ?_⟩
      simp only [runFuel]
      exact searchLoop_complete (run₂ fuel (by omega))
        (fun l low => run₁ fuel (by omega) l low) (fuel + 1) 0 (Nat.zero_le i) (by omega)

theorem fuelChecker_complete :
    fuelChecker.CertificateComplete (fun claim => (claim.1.eval claim.2).Dom) := by
  intro claim halts
  obtain ⟨y, member⟩ := Part.dom_iff_mem.mp halts
  obtain ⟨threshold, run⟩ := runFuel_complete claim.1 claim.2 y member
  refine ⟨threshold, ?_⟩
  change (runFuel threshold claim.1 claim.2).isSome = true
  rw [run threshold le_rfl]
  rfl

/-- The fuel checker is exact for halting. -/
theorem fuelChecker_authority :
    fuelChecker.Authority (fun claim => (claim.1.eval claim.2).Dom) :=
  ⟨fuelChecker_sound, fuelChecker_complete⟩

/-- The fuel `2 ^ (n + 1)`, written in `n + 2` bits, certifies that `powCode (n + 1)`
halts on `0`. -/
theorem fuel_accepts_powCode (n : ℕ) :
    fuelChecker.check (powCode (n + 1), 0) (2 ^ (n + 1)) = true := by
  change (runFuel (2 ^ (n + 1)) (powCode (n + 1)) 0).isSome = true
  rw [runFuel_pow (n + 1) le_rfl]
  rfl

/-- The MM0 checker of the universal theory, on the same claims. -/
def universalChecker : SizedChecker (Code × ℕ) ProofWitness where
  check claim witness := ProofWitness.check presentation.theory.termSignature
    presentation.theory.definitionSignature presentation.theory.theoremSignature [] [] witness
    (haltsTerm claim.1 claim.2)
  claimSize claim := (haltsTerm claim.1 claim.2).size
  certificateSize := Cost.proofSize

theorem universalChecker_authority :
    universalChecker.Authority (fun claim => (claim.1.eval claim.2).Dom) where
  sound claim witness accepted := (mm0_checks_halts_iff claim.1 claim.2).mp ⟨witness, accepted⟩
  complete claim halts := (mm0_checks_halts_iff claim.1 claim.2).mpr halts

/-! ## Sizes of the family -/

theorem codeTerm_powCode_size : ∀ n,
    (codeTerm (powCode n)).size = (codeTerm (powCode 0)).size + n * ((codeTerm doubleCode).size + 3)
  | 0 => by simp
  | n + 1 => by
      have previous := codeTerm_powCode_size n
      simp only [powCode, codeTerm, Preterm.applyArgs, Preterm.size] at previous ⊢
      rw [previous]
      ring

/-- The claims of the family grow linearly. -/
theorem haltsTerm_powCode_size (n : ℕ) :
    (haltsTerm (powCode n) 0).size =
      (codeTerm (powCode 0)).size + n * ((codeTerm doubleCode).size + 3) + 4 := by
  rw [← codeTerm_powCode_size]
  simp [haltsTerm, judgmentTerm, numTerm, Preterm.applyArgs, Preterm.size]
  omega

/-! ## The gap -/

/-- **The MM0 checker of the universal theory does not size-simulate the fuel
checker.** Its accepted proofs that `powCode (n + 1)` halts have more than `2 ^ n`
nodes, while the fuel certificates have `n + 2` bits. -/
theorem no_sizeSimulation : ¬ Nonempty (SizeSimulation universalChecker fuelChecker) := by
  rintro ⟨simulation⟩
  obtain ⟨p, bounded⟩ := simulation.sizeBound
  obtain ⟨n, small⟩ := exists_eval_lt_two_pow p ((codeTerm doubleCode).size + 4)
    ((codeTerm doubleCode).size + (codeTerm (powCode 0)).size + 9)
  have translated := simulation.preserves (powCode (n + 1), 0) (2 ^ (n + 1))
    (fuel_accepts_powCode n)
  have lower := witness_bound n translated
  have upper : Cost.proofSize (simulation.translate (powCode (n + 1), 0) (2 ^ (n + 1))) ≤
      p.eval (fuelChecker.inputSize ((powCode (n + 1), 0), 2 ^ (n + 1))) :=
    bounded ((powCode (n + 1), 0), 2 ^ (n + 1))
  have inputEq : fuelChecker.inputSize ((powCode (n + 1), 0), 2 ^ (n + 1)) =
      ((codeTerm doubleCode).size + 4) * n +
        ((codeTerm doubleCode).size + (codeTerm (powCode 0)).size + 9) := by
    simp only [SizedChecker.inputSize, fuelChecker, haltsTerm_powCode_size, Nat.size_pow]
    ring
  rw [inputEq] at upper
  omega

/-! ## Controls -/

namespace Controls

/-- With fuel four, `powCode 2` computes `2 ^ 2` from `0`. -/
example : runFuel 4 (powCode 2) 0 = some 4 := by decide +kernel

/-- With fuel one, the last doubling of `powCode 2` cannot finish, so the fuel checker
rejects. -/
example : fuelChecker.check (powCode 2, 0) 1 = false := by decide +kernel

/-- No MM0 proof that `powCode 2` halts has fewer than three nodes. -/
example (witness : ProofWitness) (accepted : universalChecker.check (powCode 2, 0) witness = true) :
    3 ≤ Cost.proofSize witness :=
  witness_bound 1 accepted

end Controls

end Mettapedia.Languages.MM0.Translation.UniversalTraceBound
