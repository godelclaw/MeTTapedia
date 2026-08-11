import Mettapedia.Logic.LP.RuntimeUnificationSoundness
import Mathlib.Tactic.IntervalCases

/-!
# Runtime-unification regressions

The fixtures pin the cases where a tree-only or non-transactional unifier is
wrong: rational-tree binding, variable orientation, left-to-right compound
work, exact rollback after a later mismatch, and termination on two cyclic
compound graphs.
-/

namespace Mettapedia.Logic.LP.RuntimeUnificationRegression

open RuntimeTerm RuntimeUnification RuntimeReadback
open RuntimeUnificationSoundness

inductive UConst where
  | a | b | c
deriving DecidableEq, Repr

inductive UVar where
  | x | y
deriving DecidableEq, Repr

inductive URel where
  | p
deriving DecidableEq, Repr

inductive UFun where
  | pair | loop
deriving DecidableEq, Repr

def uSig : LPSignature where
  constants := UConst
  vars := UVar
  relationSymbols := URel
  relationArity := fun _ => 0
  functionSymbols := UFun
  functionArity
    | .pair => 2
    | .loop => 1

instance : DecidableEq uSig.constants := inferInstanceAs (DecidableEq UConst)
instance : DecidableEq uSig.vars := inferInstanceAs (DecidableEq UVar)
instance : DecidableEq uSig.functionSymbols := inferInstanceAs (DecidableEq UFun)

def rationalBase : Memory uSig := {
  heap := #[.var .x none, .app .loop #[0]]
  trail := #[]
}

def rationalBound : Memory uSig := {
  heap := #[.var .x (some 1), .app .loop #[0]]
  trail := #[{ address := 0, previous := .var .x none }]
}

/-- `occurs_check=false`: binding `X` to `loop(X)` succeeds and retains the
rational graph rather than rejecting it or trying to unfold it. -/
theorem rational_tree_binding_succeeds :
    runSteps 2 (start rationalBase 0 1) =
      .terminal (.success rationalBound) := by
  rfl

def twoVariables : Memory uSig := {
  heap := #[.var .x none, .var .y none]
  trail := #[]
}

def twoVariablesUnified : Memory uSig := {
  heap := #[.var .x none, .var .y (some 0)]
  trail := #[{ address := 1, previous := .var .y none }]
}

/-- Like SWI's simple-pointer case, two variables point downward by address. -/
theorem variables_are_oriented_downward :
    runSteps 2 (start twoVariables 0 1) =
      .terminal (.success twoVariablesUnified) := by
  rfl

def lateMismatchBase : Memory uSig := {
  heap := #[
    .var .x none,
    .const .b,
    .const .a,
    .const .c,
    .app .pair #[0, 2],
    .app .pair #[1, 3]
  ]
  trail := #[]
}

/-- The first pair argument binds `X`; the second then conflicts.  Failure
unwinds the earlier write exactly, rather than leaking a partial binding. -/
theorem later_mismatch_rolls_back_exactly :
    runSteps 5 (start lateMismatchBase 4 5) =
      .terminal (.failure lateMismatchBase) := by
  rfl

/-- A short budget exposes a resumable running state, never false failure. -/
theorem budget_exhaustion_is_not_failure :
    match runSteps 1 (start lateMismatchBase 4 5) with
    | .running _ => True
    | .terminal _ => False := by
  trivial

def twoRationalCycles : Memory uSig := {
  heap := #[
    .var .x (some 1), .app .loop #[0],
    .var .y (some 3), .app .loop #[2]
  ]
  trail := #[]
}

/-- Visited compound pairs make bisimilar rational cycles terminate. -/
theorem equal_rational_cycles_terminate :
    runSteps 3 (start twoRationalCycles 0 2) =
      .terminal (.success twoRationalCycles) := by
  rfl

def finiteCompoundConvergence : Heap uSig := #[
  .var .x (some 3),
  .const .a,
  .const .b,
  .app .pair #[1, 2]
]

/-- The generalized convergence theorem genuinely covers a compound root.
The heap is not function-free, both addresses have finite readbacks, and their
shared dereference root forces those readbacks to agree. -/
theorem finite_compound_converged_readbacks_agree :
    ¬ FunctionFree finiteCompoundConvergence ∧
    (∀ {leftTerm rightTerm : Term uSig},
      Heap.readTerm finiteCompoundConvergence 0 = .ok leftTerm →
      Heap.readTerm finiteCompoundConvergence 3 = .ok rightTerm →
      leftTerm = rightTerm) := by
  constructor
  · intro hfree
    exact hfree 3 .pair #[1, 2] rfl
  · intro leftTerm rightTerm hLeft hRight
    exact ConvergedAt.readTerm_eq_finite
      ⟨2, 3, rfl, rfl⟩ hLeft hRight

def compoundBindingBefore : Heap uSig := #[
  .var .x none,
  .const .a,
  .app .pair #[0, 1]
]

def compoundBindingAfter : Heap uSig := #[
  .var .x (some 1),
  .const .a,
  .app .pair #[0, 1]
]

theorem compoundBinding_extension :
    BindingExtension compoundBindingBefore compoundBindingAfter := by
  constructor
  · rfl
  · intro address cell hcell
    have hlt := lt_of_getElem?_some hcell
    change address < 3 at hlt
    interval_cases address
    · simp [compoundBindingBefore] at hcell
      subst cell
      exact .inr ⟨.x, 1, rfl, rfl⟩
    · exact .inl (by
        simpa [compoundBindingBefore, compoundBindingAfter] using hcell)
    · exact .inl (by
        simpa [compoundBindingBefore, compoundBindingAfter] using hcell)

theorem compoundBinding_identityInjective :
    IdentityInjective compoundBindingAfter := by
  intro a b identity la lb ha hb
  have hla := lt_of_getElem?_some ha
  have hlb := lt_of_getElem?_some hb
  change a < 3 at hla
  change b < 3 at hlb
  interval_cases a <;> interval_cases b <;>
    simp [compoundBindingAfter] at ha hb ⊢

/-- A binding underneath an immutable application node is reflected exactly
by the canonical heap substitution.  This inhabits the application arm of
`readback_naturality_finite`; it is not a function-free specialization. -/
def compoundPairTerm (left right : Term uSig) : Term uSig :=
  .app .pair fun index =>
    [left, right].get (Fin.cast (by rfl) index)

theorem compoundBindingBefore_readback :
    Heap.readTerm compoundBindingBefore 2 =
      .ok (compoundPairTerm (.var .x) (.const .a)) := by
  simp [Heap.readTerm, readTermFuel, readListFuel, compoundBindingBefore,
    compoundPairTerm, uSig]
  simp only [Bind.bind, Except.bind]
  rw [dif_pos (by rfl)]

theorem compoundBindingAfter_readback :
    Heap.readTerm compoundBindingAfter 2 =
      .ok (compoundPairTerm (.const .a) (.const .a)) := by
  simp [Heap.readTerm, readTermFuel, readListFuel, compoundBindingAfter,
    compoundPairTerm, uSig]
  simp only [Bind.bind, Except.bind]
  rw [dif_pos (by rfl)]

theorem finite_compound_readback_is_natural :
    ∃ beforeTerm afterTerm,
      Heap.readTerm compoundBindingBefore 2 = .ok beforeTerm ∧
      Heap.readTerm compoundBindingAfter 2 = .ok afterTerm ∧
      (heapSubst compoundBindingAfter).applyTerm beforeTerm = afterTerm := by
  refine ⟨compoundPairTerm (.var .x) (.const .a),
    compoundPairTerm (.const .a) (.const .a),
    compoundBindingBefore_readback, compoundBindingAfter_readback, ?_⟩
  exact readback_naturality_finite compoundBinding_extension
    compoundBinding_identityInjective compoundBindingBefore_readback
      compoundBindingAfter_readback

def finiteVisitedHeap : Heap uSig := #[
  .const .a,
  .const .a,
  .app .loop #[0],
  .app .loop #[1]
]

def finiteVisited : List (Addr × Addr) := [(2, 3)]

theorem finiteVisited_closed :
    VisitedClosed finiteVisitedHeap finiteVisited := by
  intro pair hPair
  simp [finiteVisited] at hPair
  subst pair
  refine ⟨.loop, #[0], #[1], rfl, rfl, rfl, ?_⟩
  intro k hkLeft hkRight
  change k < 1 at hkLeft
  interval_cases k
  exact .inl (GoodPair.of_const (fuel := 1) rfl rfl rfl rfl)

theorem finiteVisited_related :
    VisitedRelated finiteVisitedHeap finiteVisited 2 3 :=
  .inr ⟨1, 1, 2, 3, rfl, rfl, by simp [finiteVisited, orderedPair]⟩

/-- The graph certificate is inhabited by two distinct application roots, and
its semantic theorem equates their finite unfoldings. -/
theorem finite_visited_applications_agree :
    FiniteEqual finiteVisitedHeap 2 3 :=
  finiteVisited_related.finiteEqual finiteVisited_closed

def finiteVisitedMemory : Memory uSig := {
  heap := finiteVisitedHeap
  trail := #[]
}

/-- End-to-end discriminator: the executable machine really traverses two
distinct compound roots, and its new run certificate proves their finite
answers equal.  This cannot be discharged by the shared-root case alone. -/
theorem finite_compound_machine_success_is_certified :
    runSteps 3 (start finiteVisitedMemory 2 3) =
        .terminal (.success finiteVisitedMemory) ∧
      FiniteEqual finiteVisitedMemory.heap 2 3 := by
  constructor
  · rfl
  · exact startMany_success_finiteEqual 3 finiteVisitedMemory [(2, 3)]
      finiteVisitedMemory rfl (2, 3) (by simp)

/-- Rational success also produces the graph certificate, while the theorem
does not falsely claim a finite tree readback for the cyclic roots. -/
theorem rational_machine_success_has_graph_certificate :
    GraphCertificate twoRationalCycles.heap [(0, 2)] :=
  startMany_success_graph_certificate 3 twoRationalCycles [(0, 2)]
    twoRationalCycles equal_rational_cycles_terminate

def variableOnlyCycle : Memory uSig := {
  heap := #[.var .x (some 1), .var .y (some 0)]
  trail := #[]
}

/-- A corrupt cycle consisting only of variable links is a structured error,
not a rational term and not an infinite dereference loop. -/
theorem variable_only_cycle_is_visible :
    runSteps 2 (start variableOnlyCycle 0 0) =
      .terminal (.runtimeError (.variableReferenceCycle 1) variableOnlyCycle) := by
  rfl

end Mettapedia.Logic.LP.RuntimeUnificationRegression
