import Mettapedia.Logic.Arithmetic.BuchiRecurrence

open Mettapedia.GSLT.LanguageDef.CertificateGSLT

/-!
# Rabin automata on the infinite binary tree

The target for monadic second-order logic of two successors. A node of the
full binary tree is a finite word over the child directions. A labelling
assigns a letter to every node. A run assigns a state to every node, agrees
with the start state at the root, and follows the transition at every node
into the two children. Acceptance is the Rabin condition along every infinite
branch: for some pair of state-sets, the first set occurs only finitely often
and the second occurs infinitely often. The infinite half is the recurrence
`InfinitelyOftenAccepting` already used for memoryless controllers. It is not
a second progress measure.

## Open goals

Emptiness. For every Rabin automaton whose state type and alphabet are
finite, it is decidable whether some labelling is accepted. Michael O. Rabin,
*Decidability of Second-Order Theories and Automata on Infinite Trees* (1969).

The monadic second-order theory of two successors. For every sentence of that
language there is a Rabin automaton that accepts a labelling if and only if
the labelling satisfies the sentence, and every Rabin automaton arises from
such a sentence. The same paper. Neither direction is proved here. No
decision procedure is claimed.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Arithmetic.RabinTree

/-- A node is a finite word of child directions. `false` is the left child. -/
abbrev Node := List Bool

/-- The node reached by the first `n` steps of a branch. -/
def nodeAt (branch : Nat → Bool) : Nat → Node
  | 0 => []
  | n + 1 => nodeAt branch n ++ [branch n]

/-- States of a run along a branch. -/
def along {σ : Type} (run : Node → σ) (branch : Nat → Bool) : Nat → σ :=
  fun n => run (nodeAt branch n)

/-- One Rabin pair: a set seen only finitely often, and a set seen infinitely often. -/
structure Pair (σ : Type) where
  finite : σ → Bool
  infinite : σ → Bool

/-- A nondeterministic Rabin automaton. The transition reads a state and a
letter and chooses a state for each child. -/
structure Rabin (α σ : Type) where
  start : σ
  delta : σ → α → σ → σ → Bool
  pairs : List (Pair σ)

def finitelyOften {σ : Type} (mark : σ → Bool) (path : Nat → σ) : Prop :=
  ∃ lower, ∀ visit, lower ≤ visit → mark (path visit) = false

/-- The infinite half of a Rabin pair is the existing recurrence predicate. -/
theorem infiniteHalf_iff {σ : Type} (mark : σ → Bool) (path : Nat → σ) :
    InfinitelyOftenAccepting
        (⟨fun _ _ _ => true, mark⟩ : LabeledSystem σ Unit) path ↔
      ∀ lower, ∃ visit, lower ≤ visit ∧ mark (path visit) = true :=
  Iff.rfl

def pairMet {σ : Type} (pair : Pair σ) (path : Nat → σ) : Prop :=
  finitelyOften pair.finite path ∧
    InfinitelyOftenAccepting
      (⟨fun _ _ _ => true, pair.infinite⟩ : LabeledSystem σ Unit) path

def Run {α σ : Type} (A : Rabin α σ) (label : Node → α) (run : Node → σ) : Prop :=
  run [] = A.start ∧
    ∀ node,
      A.delta (run node) (label node) (run (node ++ [false])) (run (node ++ [true])) = true

def branchOk {α σ : Type} (A : Rabin α σ) (run : Node → σ) (branch : Nat → Bool) : Prop :=
  ∃ pair ∈ A.pairs, pairMet pair (along run branch)

def Accepts {α σ : Type} (A : Rabin α σ) (label : Node → α) : Prop :=
  ∃ run, Run A label run ∧ ∀ branch, branchOk A run branch

/-- Every transition is allowed, and the only pair asks for the unique state
infinitely often. -/
def alwaysAccept : Rabin Unit Unit where
  start := ()
  delta := fun _ _ _ _ => true
  pairs := [⟨fun _ => false, fun _ => true⟩]

theorem alwaysAccept_accepts (label : Node → Unit) : Accepts alwaysAccept label := by
  refine ⟨fun _ => (), ⟨rfl, fun _ => rfl⟩, ?_⟩
  intro branch
  refine ⟨⟨fun _ => false, fun _ => true⟩, List.mem_cons.mpr (Or.inl rfl), ?_, ?_⟩
  · exact ⟨0, fun _ _ => rfl⟩
  · intro lower
    exact ⟨lower, le_rfl, rfl⟩

/-- Every transition stays at `false`. The only pair asks for `true`
infinitely often, so no labelling is accepted. -/
def stayFalse : Rabin Unit Bool where
  start := false
  delta := fun q _ left right => (q == false) && (left == false) && (right == false)
  pairs := [⟨fun _ => false, fun s => s⟩]

theorem stayFalse_run {label : Node → Unit} {run : Node → Bool}
    (h : Run stayFalse label run) (node : Node) : run node = false := by
  induction node using List.reverseRecOn with
  | nil => exact h.1
  | append_singleton parent dir _ih =>
    have hstep := h.2 parent
    simp only [stayFalse, Bool.and_eq_true, beq_iff_eq] at hstep
    cases dir
    · exact hstep.1.2
    · exact hstep.2

theorem stayFalse_rejects (label : Node → Unit) : ¬ Accepts stayFalse label := by
  intro hacc
  rcases hacc with ⟨run, hrun, hbranch⟩
  rcases hbranch (fun _ => false) with ⟨pair, hmem, _, hinf⟩
  simp only [stayFalse, List.mem_singleton] at hmem
  subst hmem
  obtain ⟨visit, _, hmark⟩ := hinf 0
  have hstate : along run (fun _ => false) visit = false :=
    stayFalse_run hrun (nodeAt (fun _ => false) visit)
  have htrue : along run (fun _ => false) visit = true := by
    simpa [LabeledSystem.accepting] using hmark
  exact Bool.false_ne_true (hstate.symm.trans htrue)

#print axioms infiniteHalf_iff
#print axioms alwaysAccept_accepts
#print axioms stayFalse_rejects

end Mettapedia.Logic.Arithmetic.RabinTree
