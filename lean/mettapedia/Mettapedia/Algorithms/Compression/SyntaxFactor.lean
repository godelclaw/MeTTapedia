import Mettapedia.Algorithms.Compression.Checked

/-!
# Lossless factoring of ordered syntax trees

Fresh references replace repeated subtrees; expansion restores them before the
original language interprets the result. Binding, rule order and multiplicity
are not reinterpreted. This is presentation compression, not authority to execute
a new rewrite rule or to identify merely equivalent syntax.
-/

namespace Mettapedia.Algorithms.Compression.SyntaxFactor

open Checked

inductive Tree (Symbol : Type*) where
  | atom : Symbol → Tree Symbol
  | ref : Nat → Tree Symbol
  | pair : Tree Symbol → Tree Symbol → Tree Symbol
  deriving DecidableEq, Repr

namespace Tree

def size : Tree Symbol → Nat
  | .atom _ => 1
  | .ref name => name + 1
  | .pair left right => 1 + left.size + right.size

def occurs (name : Nat) : Tree Symbol → Bool
  | .atom _ => false
  | .ref other => name == other
  | .pair left right => occurs name left || occurs name right

def abstract [DecidableEq Symbol] (name : Nat) (pattern : Tree Symbol) : Tree Symbol → Tree Symbol
  | .atom value => if Tree.atom value = pattern then .ref name else .atom value
  | .ref other => if Tree.ref other = pattern then .ref name else .ref other
  | .pair left right =>
      if Tree.pair left right = pattern then .ref name
      else .pair (abstract name pattern left) (abstract name pattern right)

def expand (name : Nat) (pattern : Tree Symbol) : Tree Symbol → Tree Symbol
  | .atom value => .atom value
  | .ref other => if name = other then pattern else .ref other
  | .pair left right => .pair (expand name pattern left) (expand name pattern right)

/-- Actual replacement and expansion, with freshness preventing capture of an
existing reference. Pattern equality is structural, not semantic equivalence. -/
theorem expand_abstract [DecidableEq Symbol] (name : Nat) (pattern source : Tree Symbol)
    (fresh : occurs name source = false) :
    expand name pattern (abstract name pattern source) = source := by
  induction source with
  | atom value =>
      by_cases same : Tree.atom value = pattern
      · rw [abstract, if_pos same]
        simpa [expand] using same.symm
      · rw [abstract, if_neg same]
        rfl
  | ref other =>
      have distinct : name ≠ other := by simpa [occurs] using fresh
      by_cases same : Tree.ref other = pattern
      · rw [abstract, if_pos same]
        simpa [expand] using same.symm
      · rw [abstract, if_neg same]
        simp only [expand, if_neg distinct]
  | pair left right ihLeft ihRight =>
      have children : occurs name left = false ∧ occurs name right = false := by
        simpa [occurs, Bool.or_eq_false_iff] using fresh
      by_cases same : Tree.pair left right = pattern
      · rw [abstract, if_pos same]
        simpa [expand] using same.symm
      · rw [abstract, if_neg same]
        change Tree.pair (expand name pattern (abstract name pattern left))
          (expand name pattern (abstract name pattern right)) = Tree.pair left right
        rw [ihLeft children.1, ihRight children.2]

def maxReference : Tree Symbol → Nat
  | .atom _ => 0
  | .ref name => name
  | .pair left right => max left.maxReference right.maxReference

def subtrees (tree : Tree Symbol) : List (Tree Symbol) :=
  tree :: match tree with
  | .pair left right => left.subtrees ++ right.subtrees
  | _ => []

end Tree

structure Feature (Symbol : Type*) where
  name : Nat
  body : Tree Symbol
  deriving DecidableEq, Repr

def model (Symbol : Type*) [DecidableEq Symbol] : Model (Tree Symbol) (Feature Symbol) where
  extract feature source :=
    if Tree.occurs feature.name source then none
    else some (Tree.abstract feature.name feature.body source)
  expand feature residual := some (Tree.expand feature.name feature.body residual)
  featureCost feature := feature.body.size + feature.name + 2
  dataCost := Tree.size

/-- Fresh-name validation is part of the executable extractor, not an unchecked
promise made by the proposal generator. -/
theorem extract_reconstructs [DecidableEq Symbol]
    (feature : Feature Symbol) (source residual : Tree Symbol)
    (extracted : (model Symbol).extract feature source = some residual) :
    (model Symbol).expand feature residual = some source := by
  unfold model at extracted ⊢
  dsimp at extracted ⊢
  split at extracted
  · cases extracted
  · rename_i fresh
    have same := Option.some.inj extracted
    rw [← same, Tree.expand_abstract]
    simpa using fresh

def proposals (source : Tree Symbol) : List (Feature Symbol) :=
  source.subtrees.map fun body => ⟨source.maxReference + 1, body⟩

def encode [DecidableEq Symbol] (fuel : Nat) (source : Tree Symbol) :=
  compress (model Symbol) proposals fuel source

theorem decode_encode [DecidableEq Symbol] (fuel : Nat) (source : Tree Symbol) :
    restore (model Symbol) (encode fuel source).1 (encode fuel source).2 = some source :=
  (compress_correct (model Symbol) proposals fuel source).1

/-- This observer law follows from the nontrivial codec theorem. It does not
claim that a separate direct executor of compact syntax is already correct. -/
theorem observation_after_expansion [DecidableEq Symbol]
    (observe : Tree Symbol → Observation) (fuel : Nat) (source : Tree Symbol) :
    (restore (model Symbol) (encode fuel source).1 (encode fuel source).2).map observe =
      some (observe source) := by
  rw [decode_encode]
  rfl

def branch : Tree Bool := .pair (.atom true) (.pair (.atom false) (.atom true))
def repeated : Tree Bool := .pair (.pair branch branch) (.pair branch branch)

theorem nontrivial_factor :
    cost (model Bool) (encode 4 repeated).1 (encode 4 repeated).2 < repeated.size := by
  decide

theorem capture_is_refused :
    (model Bool).extract ⟨1, branch⟩ (.pair (.ref 1) branch) = none := by decide

theorem unguarded_capture_changes_source :
    Tree.expand 1 branch (Tree.abstract 1 branch (.pair (.ref 1) branch)) ≠
      Tree.pair (.ref 1) branch := by decide

end Mettapedia.Algorithms.Compression.SyntaxFactor
