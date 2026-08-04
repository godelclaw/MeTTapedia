import Mettapedia.Logic.LP.RuntimeQuery

/-!
# Reading runtime heap terms back into finite LP terms

`RuntimeQuery` yields answers as live heap roots.  Grounding those answers in
the declarative `Logic.LP` semantics requires reading a heap address back into
an inductive `Term` — the direction the runtime never otherwise needs.

Readback is fuel-bounded.  In an acyclic reference graph every simple path
visits pairwise-distinct cells, so any finite term reachable in a heap of size
`n` is fully read with depth budget `n + 1`; exhausting the budget therefore
witnesses a cyclic (rational) or corrupt reference chain, reported as
`notFinite` — never silently truncated.
-/

namespace Mettapedia.Logic.LP
namespace RuntimeReadback

open RuntimeTerm

/-- Failures of finite readback.  A rational (cyclic) term is not corrupt —
it is honestly reported as not finitely readable. -/
inductive ReadbackError where
  | invalidAddress (address : Addr)
  | arityMismatch
  | notFinite
deriving DecidableEq, Repr

mutual

/-- Read one address into a finite term with an explicit depth budget. -/
def readTermFuel {σ : LPSignature} (heap : Heap σ) :
    Nat → Addr → Except ReadbackError (Term σ)
  | 0, _ => .error .notFinite
  | fuel + 1, address =>
      match heap[address]? with
      | none => .error (.invalidAddress address)
      | some (.var identity none) => .ok (.var identity)
      | some (.var _ (some target)) => readTermFuel heap fuel target
      | some (.const symbol) => .ok (.const symbol)
      | some (.app symbol args) => do
          let children ← readListFuel heap fuel args.toList
          if h : children.length = σ.functionArity symbol then
            .ok (.app symbol fun index => children.get (Fin.cast h.symm index))
          else
            .error .arityMismatch
termination_by fuel _ => (fuel, 0)

/-- Read a list of argument addresses at one shared depth budget. -/
def readListFuel {σ : LPSignature} (heap : Heap σ) :
    Nat → List Addr → Except ReadbackError (List (Term σ))
  | _, [] => .ok []
  | fuel, address :: rest => do
      let head ← readTermFuel heap fuel address
      let tail ← readListFuel heap fuel rest
      .ok (head :: tail)
termination_by fuel rest => (fuel, rest.length + 1)

end

/-- Read one address into a finite term.  `heap.size + 1` bounds the longest
simple path in an acyclic reference graph, so failure with `notFinite` is a
genuine cycle/corruption witness, not a budget artifact. -/
def Heap.readTerm {σ : LPSignature} (heap : Heap σ) (address : Addr) :
    Except ReadbackError (Term σ) :=
  readTermFuel heap (heap.size + 1) address

/-- Read every recorded source query variable of an answer.  The result maps
each source variable to the finite term its heap root denotes now. -/
def readAnswer {σ : LPSignature} (answer : RuntimeQuery.Answer σ) :
    Except ReadbackError (List (ScopedVar σ.vars × Term σ.scoped)) :=
  answer.queryVarMap.foldrM (init := []) fun (variable_, address) acc => do
    let term ← Heap.readTerm answer.memory.heap address
    .ok ((variable_, term) :: acc)

/-! ## Small definitional laws -/

@[simp] theorem readTermFuel_const {σ : LPSignature} (heap : Heap σ)
    (fuel address : Nat) (symbol : σ.constants)
    (h : heap[address]? = some (.const symbol)) :
    readTermFuel heap (fuel + 1) address = .ok (.const symbol) := by
  simp [readTermFuel, h]

@[simp] theorem readTermFuel_unbound {σ : LPSignature} (heap : Heap σ)
    (fuel address : Nat) (identity : σ.vars)
    (h : heap[address]? = some (.var identity none)) :
    readTermFuel heap (fuel + 1) address = .ok (.var identity) := by
  simp [readTermFuel, h]

/-- A bound variable reads exactly as its link target at one less depth. -/
theorem readTermFuel_link {σ : LPSignature} (heap : Heap σ)
    (fuel address target : Nat) (identity : σ.vars)
    (h : heap[address]? = some (.var identity (some target))) :
    readTermFuel heap (fuel + 1) address = readTermFuel heap fuel target := by
  simp [readTermFuel, h]

end RuntimeReadback
end Mettapedia.Logic.LP
