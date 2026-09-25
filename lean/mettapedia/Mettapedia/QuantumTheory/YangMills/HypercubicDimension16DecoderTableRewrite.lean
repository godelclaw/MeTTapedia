import Lean.Elab.Tactic.Basic
import Lean.Meta.Tactic.Delta

/-!
# Rewriting payload decoders to proved tables inside a goal

Kernel replays over generated data call payload decoders such as
`decodedPhysicalTraceWitnessChunk` through several layers of definitions. When a
decoder has been proved equal to an explicit table (`decoder = table`), the
tactic `rewrite_decoders_to_tables [h₁, …]` unfolds exactly the definitions of
this library whose bodies lead to one of the decoders, and then rewrites every
occurrence of those decoders with the given equations. The goal is otherwise
unchanged, so the following `decide +kernel` checks the same proposition while
reading the tables instead of re-decoding the payloads.
-/

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16DecoderTableRewrite

open Lean Meta Elab Tactic

/-- A statement over `Fin n` follows from its instances on the consecutive blocks
`k * s + j` (`j < s`, `k < m`), which lets a large kernel replay be split into
several smaller declarations. -/
theorem forall_fin_of_blocks {n : Nat} (s m : Nat) (hn : n ≤ m * s) (P : Fin n → Prop)
    (h : ∀ k : Nat, k < m → ∀ j : Fin s, ∀ hij : k * s + j.1 < n, P ⟨k * s + j.1, hij⟩) :
    ∀ i : Fin n, P i := by
  intro i
  have hs : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · subst h0
      have := i.2
      simp at hn
      omega
    · exact h0
  have hk : i.1 / s < m := by
    rw [Nat.div_lt_iff_lt_mul hs]
    have := i.2
    omega
  have hij : i.1 / s * s + (⟨i.1 % s, Nat.mod_lt _ hs⟩ : Fin s).1 < n := by
    simp only [Nat.div_add_mod']
    exact i.2
  have e : (⟨i.1 / s * s + (⟨i.1 % s, Nat.mod_lt _ hs⟩ : Fin s).1, hij⟩ : Fin n) = i :=
    Fin.ext (Nat.div_add_mod' i.1 s)
  exact e ▸ h (i.1 / s) hk ⟨i.1 % s, Nat.mod_lt _ hs⟩ hij

/-- Whether the definition `c` of this library reaches one of `decoders` through the
bodies of definitions (memoized; theorems, opaque constants and declarations outside
this library are never unfolded). -/
partial def reachesDecoder (env : Environment) (decoders : NameSet) (c : Name) :
    StateM (Std.HashMap Name Bool) Bool := do
  if decoders.contains c then return true
  if !(`Mettapedia).isPrefixOf c then return false
  if let some b := (← get)[c]? then return b
  modify (·.insert c false)
  let r ← match env.find? c with
    | some (.defnInfo d) => d.value.getUsedConstants.anyM (reachesDecoder env decoders)
    | _ => pure false
  modify (·.insert c r)
  return r

/-- Unfolds every definition in the goal that leads to a decoder on the left of the given
equations `decoder = table`, then rewrites with each equation whose decoder occurs. -/
elab "rewrite_decoders_to_tables" " [" eqs:ident,* "]" : tactic => withMainContext do
  let env ← getEnv
  let mut decoders : NameSet := {}
  let mut eqNames : Array Name := #[]
  for stx in eqs.getElems do
    let n ← realizeGlobalConstNoOverloadWithInfo stx
    let some ci := env.find? n | throwError "rewrite_decoders_to_tables: unknown constant {n}"
    let some (_, lhs, _) := ci.type.eq?
      | throwError "rewrite_decoders_to_tables: {n} is not an equation"
    let some c := lhs.constName?
      | throwError "rewrite_decoders_to_tables: the left side of {n} is not a constant"
    decoders := decoders.insert c
    eqNames := eqNames.push n
  -- decide, for every constant reachable from the goal, whether it must be unfolded
  let mut memo : Std.HashMap Name Bool := {}
  let mut todo := (← getMainTarget).getUsedConstants.toList
  let mut unfold : NameSet := {}
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let c := todo.head!
    todo := todo.tail!
    if seen.contains c then continue
    seen := seen.insert c
    let (r, memo') := (reachesDecoder env decoders c).run memo
    memo := memo'
    if r && !decoders.contains c then
      unfold := unfold.insert c
      if let some (.defnInfo d) := env.find? c then
        todo := d.value.getUsedConstants.toList ++ todo
  let g ← (← getMainGoal).deltaTarget (unfold.contains ·)
  replaceMainGoal [g]
  -- rewrite with the equations whose decoder occurs in the unfolded goal
  let present := (← g.getType).getUsedConstantsAsSet
  for n in eqNames do
    let some (.thmInfo t) := env.find? n | continue
    let some (_, lhs, _) := t.type.eq? | continue
    if lhs.constName?.any present.contains then
      evalTactic (← `(tactic| rewrite [$(mkIdent n):ident]))

end HypercubicDimension16DecoderTableRewrite
end YangMills
end QuantumTheory
end Mettapedia
