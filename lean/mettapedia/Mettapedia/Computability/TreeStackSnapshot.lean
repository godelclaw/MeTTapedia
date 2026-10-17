import Mettapedia.Computability.StackMachineRegisters
import Lean
/-!
# Materialized typed snapshots for physical stacks and finite registers

Actual cached rows are retained as data alongside lookup functions. This
keeps row computation outside lookup closures. Option and sum keys dispatch
on their constructors; nullary finite leaves use the original dependent
snapshot. Every complete dependent function is preserved. Only physical keys
and finite register indices are enumerated.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Computability.TreeStackSnapshot
universe u v w
open Lean Elab Tactic Meta

structure Snapshot (Key : Type u) (Cells : Key → Type v) where
  cells : List (Sigma (fun key => List (Cells key)))
  read : ∀ key, Cells key

@[noinline] def optionCache {Key : Type u} {Cells : Option Key → Type v}
    (child : (∀ key, Cells (some key)) → Snapshot Key (fun key => Cells (some key)))
    (values : ∀ key, Cells key) : Snapshot _ Cells :=
  let absent := values none
  let present := child (fun key => values (some key))
  ⟨⟨none,[absent]⟩ :: present.cells.map (fun ⟨key,values⟩ => ⟨some key,values⟩),fun key => match key with
    | none => absent
    | some point => present.read point⟩

@[noinline] def sumCache {First : Type u} {Second : Type v} {Cells : First ⊕ Second → Type w}
    (left : (∀ key, Cells (.inl key)) → Snapshot First (fun key => Cells (.inl key)))
    (right : (∀ key, Cells (.inr key)) → Snapshot Second (fun key => Cells (.inr key)))
    (values : ∀ key, Cells key) : Snapshot _ Cells :=
  let first := left (fun key => values (.inl key))
  let second := right (fun key => values (.inr key))
  ⟨first.cells.map (fun ⟨key,values⟩ => ⟨.inl key,values⟩) ++ second.cells.map (fun ⟨key,values⟩ => ⟨.inr key,values⟩),fun key => match key with
    | .inl point => first.read point
    | .inr point => second.read point⟩

theorem option_identity {Key : Type u} {Cells : Option Key → Type v}
    (child : (∀ key, Cells (some key)) → Snapshot Key (fun key => Cells (some key)))
    (same : ∀ values, (child values).read=values) (values : ∀ key, Cells key) :
    (optionCache child values).read=values := by
  funext key
  cases key with
  | none => rfl
  | some key => exact congrFun (same (fun key => values (some key))) key

theorem sum_identity {First : Type u} {Second : Type v} {Cells : First ⊕ Second → Type w}
    (left : (∀ key, Cells (.inl key)) → Snapshot First (fun key => Cells (.inl key)))
    (right : (∀ key, Cells (.inr key)) → Snapshot Second (fun key => Cells (.inr key)))
    (sameLeft : ∀ values, (left values).read=values)
    (sameRight : ∀ values, (right values).read=values) (values : ∀ key, Cells key) :
    (sumCache left right values).read=values := by
  funext key
  cases key with
  | inl key => exact congrFun (sameLeft (fun key => values (.inl key))) key
  | inr key => exact congrFun (sameRight (fun key => values (.inr key))) key

@[noinline] def leafCache {Key : Type u} [DecidableEq Key] {Cells : Key → Type v}
    (keys : List Key) (_all : ∀ key, key ∈ keys) (values : ∀ key, List (Cells key)) : Snapshot Key (fun key => List (Cells key)) :=
  let cells := Mettapedia.Computability.StackMachineRegisters.StackSnapshot.snapshot (fun key => List (Cells key)) (fun key => [values key]) keys
  ⟨cells,fun key => (Mettapedia.Computability.StackMachineRegisters.StackSnapshot.lookup (fun key => List (Cells key)) cells key).head?.getD []⟩

theorem leaf_identity {Key : Type u} [DecidableEq Key] {Cells : Key → Type v}
    (keys : List Key) (all : ∀ key, key ∈ keys) (values : ∀ key, List (Cells key)) :
    (leafCache keys all values).read=values := by
  funext key
  have same := Mettapedia.Computability.StackMachineRegisters.StackSnapshot.lookup_snapshot (fun key => List (Cells key)) (fun key => [values key]) keys key (all key)
  change (Mettapedia.Computability.StackMachineRegisters.StackSnapshot.lookup (fun key => List (Cells key)) _ key).head?.getD []=values key
  rw [same]
  rfl

private partial def makeCache (values : Expr) : TermElabM Expr := do
  let type ← withTransparency .reducible (whnf (← inferType values))
  let .forallE _ keyType _ _ := type | throwError "Expected dependent finite-key function"
  let keyType ← withTransparency .all (whnf keyType)
  let cells ← withLocalDeclD `key keyType fun key => do mkLambdaFVars #[key] (← inferType (mkApp values key))
  match keyType.getAppFn.constName?,keyType.getAppArgs.toList with
  | some ``Option,[child] =>
    let branch ← withLocalDeclD `key child fun key => do
      let wrapped ← mkAppOptM ``Option.some #[some child,some key]
      mkLambdaFVars #[key] (mkApp values wrapped)
    let cached ← withLocalDeclD `branch (← inferType branch) fun value => do
      mkLambdaFVars #[value] (← makeCache value)
    mkAppOptM ``optionCache #[some child,some cells,some cached,some values]
  | some ``Sum,[first,second] =>
    let left ← withLocalDeclD `key first fun key => do
      let wrapped ← mkAppOptM ``Sum.inl #[some first,some second,some key]
      mkLambdaFVars #[key] (mkApp values wrapped)
    let right ← withLocalDeclD `key second fun key => do
      let wrapped ← mkAppOptM ``Sum.inr #[some first,some second,some key]
      mkLambdaFVars #[key] (mkApp values wrapped)
    let cachedLeft ← withLocalDeclD `branch (← inferType left) fun value => do
      mkLambdaFVars #[value] (← makeCache value)
    let cachedRight ← withLocalDeclD `branch (← inferType right) fun value => do
      mkLambdaFVars #[value] (← makeCache value)
    mkAppOptM ``sumCache #[some first,some second,some cells,some cachedLeft,some cachedRight,some values]
  | some name,args =>
    let info ← getConstInfoInduct name
    unless info.numIndices == 0 do throwError "Indexed key leaf unsupported: {keyType}"
    let mut literals := #[]
    for constructor in info.ctors do
      let value ← mkAppOptM constructor (args.toArray.map some)
      unless ← isDefEq (← inferType value) keyType do throwError "Key leaf has fields: {keyType}"
      literals := literals.push value
    let keys ← mkListLit keyType literals.toList
    let complete ← withLocalDeclD `key keyType fun key => do
      mkForallFVars #[key] (← mkAppM ``Membership.mem #[keys,key])
    let all ← Term.elabTerm (← `(by intro key; cases key <;> simp)) (some complete)
    mkAppM ``leafCache #[keys,all,values]
  | _,_ => throwError "Unsupported finite-key shape: {keyType}"

elab "typed_tree_cache " expression:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let value ← Term.elabTerm expression none
    goal.assign (← makeCache value)
  replaceMainGoal []

@[noinline] def functionCache {n : Nat} {Cells : Fin n → Type v} (defaults values : ∀ index, Cells index) : Snapshot (Fin n) Cells :=
  let cells := Mettapedia.Computability.StackMachineRegisters.StackSnapshot.snapshot Cells (fun index => [values index]) (List.finRange n)
  ⟨cells,fun index => (Mettapedia.Computability.StackMachineRegisters.StackSnapshot.lookup Cells cells index).head?.getD (defaults index)⟩

theorem function_identity {n : Nat} {Cells : Fin n → Type v} (defaults values : ∀ index, Cells index) :
    (functionCache defaults values).read=values := by
  funext index
  have same := Mettapedia.Computability.StackMachineRegisters.StackSnapshot.lookup_snapshot Cells (fun index => [values index]) (List.finRange n) index (List.mem_finRange index)
  change (Mettapedia.Computability.StackMachineRegisters.StackSnapshot.lookup Cells _ index).head?.getD (defaults index)=values index
  rw [same]
  rfl


end Mettapedia.Computability.TreeStackSnapshot
