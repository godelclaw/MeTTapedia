import Mettapedia.Algorithms.Compression.CompactDag

/-! Pure partial-program composition with ordered failure propagation. The
analysis distinguishes constant values, input-dominant terms and terms with
no certified demand property. It does not infer totality of constant-only
operations. Physical TP1 decoding, type admission and index relabelling are
separate interfaces; compact traversal uses the existing unfolding theorem. -/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Compression.StrictProgramComposition

open KolmogorovComplexity FramedTree

universe u v
variable {Value : Type u} {Error : Type v}

inductive Leaf (Value : Type u) (Error : Type v) where
  | input
  | constant (value : Value)
  | fault (error : Error)

inductive Demand where
  | total
  | inputDominant
  | other
  deriving DecidableEq, Repr

def collect : List (Except Error Value) → Except Error (List Value)
  | [] => .ok []
  | .error error :: _ => .error error
  | .ok value :: rest => (collect rest).map (value :: ·)

def leafValue (read : BinString → Leaf Value Error) (input : Except Error Value) (bytes : BinString) :
    Except Error Value :=
  match read bytes with
  | .input => input
  | .constant value => .ok value
  | .fault error => .error error

def nodeValue (apply : BinString → List Value → Except Error Value)
    (tag : BinString) (arguments : List (Except Error Value)) : Except Error Value :=
  (collect arguments).bind (apply tag)

def run (read : BinString → Leaf Value Error) (apply : BinString → List Value → Except Error Value)
    (input : Except Error Value) : Tree → Except Error Value :=
  CompactDag.fold (leafValue read input) (nodeValue apply)

theorem run_node (read : BinString → Leaf Value Error)
    (apply : BinString → List Value → Except Error Value) (input : Except Error Value)
    (tag : BinString) (children : List Tree) :
    run read apply input (.node tag children) = nodeValue apply tag (children.map (run read apply input)) := by
  simp only [run, CompactDag.fold]

def dominance : List Demand → Demand
  | [] => .other
  | .total :: rest => dominance rest
  | .inputDominant :: _ => .inputDominant
  | .other :: _ => .other

def leafDemand (read : BinString → Leaf Value Error) (bytes : BinString) : Demand :=
  match read bytes with
  | .input => .inputDominant
  | .constant _ => .total
  | .fault _ => .other

def demand (read : BinString → Leaf Value Error) : Tree → Demand :=
  CompactDag.fold (leafDemand read) (fun _ children => dominance children)

def Guarantees (error : Error) (property : Demand) (result : Except Error Value) : Prop :=
  (property = .total → ∃ value, result = .ok value) ∧
    (property = .inputDominant → result = .error error)

theorem dominance_ne_total (arguments : List Demand) : dominance arguments ≠ .total := by
  induction arguments with
  | nil => simp [dominance]
  | cons first rest ih => cases first <;> simp [dominance, ih]

theorem collect_dominant (error : Error) (properties : List Demand) (results : List (Except Error Value))
    (aligned : List.Forall₂ (Guarantees error) properties results) :
    dominance properties = .inputDominant → collect results = .error error := by
  induction aligned with
  | nil => simp [dominance]
  | @cons property result properties results certified _ ih =>
      cases property with
      | total =>
          intro dominant
          obtain ⟨value, rfl⟩ := certified.1 rfl
          have tail := ih (by simpa only [dominance] using dominant)
          simp [collect, tail, Except.map]
      | inputDominant =>
          intro _
          rw [certified.2 rfl]
          rfl
      | other => simp [dominance]

theorem demand_sound (read : BinString → Leaf Value Error)
    (apply : BinString → List Value → Except Error Value) (error : Error) (tree : Tree) :
    Guarantees error (demand read tree) (run read apply (.error error) tree) := by
  induction tree using Tree.rec
    (motive_2 := fun children => List.Forall₂ (Guarantees error)
      (children.map (demand read)) (children.map (run read apply (.error error)))) with
  | leaf bytes =>
      cases classified : read bytes <;>
        simp [Guarantees, demand, run, CompactDag.fold, leafDemand, leafValue, classified]
  | node tag children ih =>
      constructor
      · intro total
        exact False.elim (dominance_ne_total (children.map (demand read))
          (by simpa only [demand, CompactDag.fold] using total))
      · intro dominant
        have failed := collect_dominant error (children.map (demand read))
          (children.map (run read apply (.error error))) ih
          (by simpa only [demand, CompactDag.fold] using dominant)
        rw [run_node]
        unfold nodeValue
        rw [failed]
        rfl
  | nil => exact .nil
  | cons first rest firstResult restResult => exact .cons firstResult restResult

def substitute (read : BinString → Leaf Value Error) (replacement : Tree) : Tree → Tree :=
  CompactDag.fold
    (fun bytes => match read bytes with | .input => replacement | _ => .leaf bytes)
    FramedTree.Tree.node

theorem substitute_node (read : BinString → Leaf Value Error) (replacement : Tree)
    (tag : BinString) (children : List Tree) :
    substitute read replacement (.node tag children) =
      .node tag (children.map (substitute read replacement)) := by
  simp only [substitute, CompactDag.fold]

theorem run_substitute (read : BinString → Leaf Value Error)
    (apply : BinString → List Value → Except Error Value) (input : Except Error Value)
    (replacement tree : Tree) :
    run read apply input (substitute read replacement tree) =
      run read apply (run read apply input replacement) tree := by
  induction tree using Tree.rec
    (motive_2 := fun children =>
      children.map (fun child => run read apply input (substitute read replacement child)) =
        children.map (run read apply (run read apply input replacement))) with
  | leaf bytes =>
      cases classified : read bytes <;>
        simp [run, substitute, CompactDag.fold, leafValue, classified]
  | node tag children ih =>
      rw [substitute_node, run_node, run_node]
      simpa only [List.map_map, Function.comp_def] using congrArg (nodeValue apply tag) ih
  | nil => rfl
  | cons first rest firstResult restResult => simp only [List.map_cons, firstResult, restResult]

/-- Substitution realizes strict monadic composition when the later root
propagates a failed input. No associativity of numerical operations is used. -/
theorem strict_composition (read : BinString → Leaf Value Error)
    (apply : BinString → List Value → Except Error Value) (input : Except Error Value)
    (earlier later : Tree) (strict : demand read later = .inputDominant) :
    run read apply input (substitute read earlier later) =
      (run read apply input earlier).bind (fun middle => run read apply (.ok middle) later) := by
  rw [run_substitute]
  cases result : run read apply input earlier with
  | ok value => rfl
  | error error =>
      change run read apply (.error error) later = .error error
      exact (demand_sound read apply error later).2 strict

theorem compact_execution_agrees (read : BinString → Leaf Value Error)
    (apply : BinString → List Value → Except Error Value) (input : Except Error Value)
    (forest : CompactDag.Forest) :
    CompactDag.evaluate (leafValue read input) (nodeValue apply) forest =
      (CompactDag.unfold forest).map (List.map (run read apply input)) :=
  CompactDag.evaluate_unfold _ _ forest

end Mettapedia.Algorithms.Compression.StrictProgramComposition
