import Mettapedia.Languages.MeTTa.HE.SmallStep
import Mettapedia.Languages.MeTTa.HE.BindingComposition
import Mettapedia.Languages.MeTTa.HE.EvalSpec

/-!
# Context Transport Lemmas for the Master Absorption Theorem

Machinery for Theorem M's congruence case (see the design note
`docs/plans/2026-06-10_correspondence_master_theorem_design.txt` in the
CeTTa repository): transporting official derivations across the
replacement of a single element.

The hypothesis shape is exactly M's induction hypothesis: a
*result-preserving substitution* — every official evaluation of the
new element is an official evaluation of the old one, with the same
result pair.  The transport retains the exact result pair, including the wrapper of a
successful singleton tuple and the shape of nested expression elements.

* `interpretTuple_swap` — tuple-path transport at any element position
  (including the head: in the tuple path the head is evaluated at
  `%Undefined%` like every other element).
* `interpretArgs_swap` — typed argument-list transport at any position
  (the hypothesis is type-generic, matching `InterpretArgs`' per-position
  expected types).

The remaining (genuinely hard) part of M's congruence case is the
*function-path head swap*, where path selection itself depends on the
head's declared types — analyzed but not provable by transport alone;
see the design note.  We state only what we prove.
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-- Tuple-path transport: if every official evaluation of `x'` (under
`%Undefined%`) is an official evaluation of `x` with the same result, then
any official tuple derivation of `(pre ++ x' :: post)` transports to
`(pre ++ x :: post)` with the identical result. -/
theorem interpretTuple_swap {space : Space} {d : GroundedDispatch}
    {x x' : Atom}
    (same : atomVariables x' = atomVariables x)
    (h_sub : ∀ (b' : Bindings) (r' : ResultPair) {scope : List Atom},
      EvalAtom space d x' Atom.undefinedType b' r' scope →
      EvalAtom space d x Atom.undefinedType b' r' scope) :
    ∀ (pre : List Atom) {post : List Atom} {b : Bindings} {r : ResultPair}
      {l : List Atom} {live : List Atom}, l = pre ++ x' :: post →
      InterpretTuple space d (.expression l) b r live →
      InterpretTuple space d (.expression (pre ++ x :: post)) b r live
  | [], post, b, r, l, live, h_eq, h => by
      cases h with
      | nil => simp at h_eq
      | singleton a _ result h_eval h_ok =>
          injection h_eq.symm with h1 h2
          cases h1; cases h2
          exact InterpretTuple.singleton x b result (h_sub b result h_eval) h_ok
      | singleton_error a _ result h_eval h_error =>
          injection h_eq.symm with h1 h2
          cases h1; cases h2
          exact InterpretTuple.singleton_error x b r (h_sub b r h_eval) h_error
      | @head_error _ hd tl _ _ h_ne h_ev h_isErr =>
          injection h_eq.symm with h1 h2
          cases h1; cases h2
          exact InterpretTuple.head_error x post b r h_ne
            (h_sub b r h_ev) h_isErr
      | @tail_error _ hd tl _ hr _ h_ne h_ev h_hok h_tail h_terr =>
          injection h_eq.symm with h1 h2
          cases h1; cases h2
          exact InterpretTuple.tail_error x post b hr r h_ne
            (h_sub b hr h_ev) h_hok h_tail h_terr
      | @success _ hd tl _ hr tr h_ne h_ev h_hok h_tl h_tok =>
          injection h_eq.symm with h1 h2
          cases h1; cases h2
          exact InterpretTuple.success x post b hr tr h_ne
            (h_sub b hr h_ev) h_hok h_tl h_tok
  | p :: ps, post, b, r, l, live, h_eq, h => by
      cases h with
      | nil => simp at h_eq
      | singleton a _ _ _ _ | singleton_error a _ _ _ _ =>
          exfalso
          injection h_eq.symm with h1 h2
          exact absurd h2.symm (by simp)
      | @head_error _ hd tl _ _ h_ne h_ev h_isErr =>
          injection h_eq.symm with h1 h2
          cases h1; cases h2
          exact InterpretTuple.head_error p (ps ++ x :: post) b r
            (by simp) (h_ev.scope_congr (by simp [atomVariables, atomListVariables_append, atomListVariables, same])) h_isErr
      | @tail_error _ hd tl _ hr _ h_ne h_ev h_hok h_tail h_terr =>
          injection h_eq.symm with h1 h2
          cases h1; cases h2
          exact InterpretTuple.tail_error p (ps ++ x :: post) b hr r
            (by simp) (h_ev.scope_congr (by simp [atomVariables, atomListVariables_append, atomListVariables, same])) h_hok
            (interpretTuple_swap same h_sub ps rfl h_tail) h_terr
      | @success _ hd tl _ hr tr h_ne h_ev h_hok h_tl h_tok =>
          injection h_eq.symm with h1 h2
          cases h1; cases h2
          exact InterpretTuple.success p (ps ++ x :: post) b hr tr
            (by simp) (h_ev.scope_congr (by simp [atomVariables, atomListVariables_append, atomListVariables, same])) h_hok
            (interpretTuple_swap same h_sub ps rfl h_tl) h_tok

/-- Typed argument-list transport: with a type-generic result-preserving
substitution for one argument position, any official `InterpretArgs`
derivation transports across the replacement with the identical result.
The expected-type lists are arbitrary and untouched: each position keeps
its own expected type, exactly as `InterpretArgs` threads them.

Side conditions: both atoms must be non-Empty/Error-shaped — without
them transport genuinely fails (an unchanged-error argument officially
*continues* to the tail, while the same result against a different
argument would *stop* as a changed error; discovered designing this
lemma — recorded as trap T8). -/
theorem interpretArgs_swap {space : Space} {d : GroundedDispatch}
    {x x' : Atom}
    (same : atomVariables x' = atomVariables x)
    (h_x : isEmptyOrError x = false)
    (h_x' : isEmptyOrError x' = false)
    (h_sub : ∀ (t : Atom) (b' : Bindings) (r' : ResultPair) {scope : List Atom},
      EvalAtom space d x' t b' r' scope → EvalAtom space d x t b' r' scope) :
    ∀ (pre : List Atom) {post : List Atom} {types : List Atom}
      {b : Bindings} {r : ResultPair} {live : List Atom},
      InterpretArgs space d (pre ++ x' :: post) types b r live →
      InterpretArgs space d (pre ++ x :: post) types b r live
  | [], post, types, b, r, live, h => by
      cases h with
      | head_changed_error _ _ t ts _ _ h_head h_err h_changed =>
          refine InterpretArgs.head_changed_error x post t ts b _
            (h_sub t b _ h_head) h_err ?_
          -- result is Empty/Error-shaped; x is not, so they differ
          intro hcontra
          rw [hcontra] at h_err
          rw [h_err] at h_x
          cases h_x
      | cons_tail_error _ _ t ts _ _ _ h_head h_head_ok h_tail h_terr =>
          refine InterpretArgs.cons_tail_error x post t ts b _ _
            (h_sub t b _ h_head) (Or.inl ?_) h_tail h_terr
          rcases h_head_ok with h | h
          · exact h
          · rw [h]; exact h_x'
      | cons_ok _ _ t ts _ _ _ h_head h_head_ok h_tail h_tok =>
          refine InterpretArgs.cons_ok x post t ts b _ _
            (h_sub t b _ h_head) (Or.inl ?_) h_tail h_tok
          rcases h_head_ok with h | h
          · exact h
          · rw [h]; exact h_x'
  | p :: ps, post, types, b, r, live, h => by
      cases h with
      | head_changed_error _ _ t ts _ _ h_head h_err h_changed =>
          exact InterpretArgs.head_changed_error p (ps ++ x :: post) t ts b _
            (h_head.scope_congr (by simp [atomListVariables_append, atomListVariables, same])) h_err h_changed
      | cons_tail_error _ _ t ts _ _ _ h_head h_head_ok h_tail h_terr =>
          exact InterpretArgs.cons_tail_error p (ps ++ x :: post) t ts b _ _
            (h_head.scope_congr (by simp [atomListVariables_append, atomListVariables, same])) h_head_ok (interpretArgs_swap same h_x h_x' h_sub ps h_tail) h_terr
      | cons_ok _ _ t ts _ _ _ h_head h_head_ok h_tail h_tok =>
          exact InterpretArgs.cons_ok p (ps ++ x :: post) t ts b _ _
            (h_head.scope_congr (by simp [atomListVariables_append, atomListVariables, same])) h_head_ok (interpretArgs_swap same h_x h_x' h_sub ps h_tail) h_tok

/-- Tuple-path `InterpretExpression` transport at non-head positions: with
the head untouched, the tuple-path side conditions (the head's non-function
type witness) transfer verbatim, the tuple derivation transports by
`interpretTuple_swap`, and the final `MettaCall` is reused as-is (it runs
on the evaluated tuple result, which transport keeps identical). -/
theorem interpretExpression_swap_tuple_path
    {space : Space} {d : GroundedDispatch} {x x' : Atom}
    (same : atomVariables x' = atomVariables x)
    (h_sub : ∀ (b' : Bindings) (r' : ResultPair) {scope : List Atom},
      EvalAtom space d x' Atom.undefinedType b' r' scope →
      EvalAtom space d x Atom.undefinedType b' r' scope)
    (p : Atom) (ps : List Atom) {post : List Atom}
    {type_ : Atom} {live : List Atom} {b : Bindings} {tupleResult callResult : ResultPair}
    (h_has : ∃ t ∈ getAtomTypes space p,
      isFunctionType t = false ∨ t = Atom.undefinedType)
    (h_tuple : InterpretTuple space d
      (.expression (p :: ps ++ x' :: post)) b tupleResult (type_ :: live))
    (h_call : MettaCall space d tupleResult.1 type_ tupleResult.2 callResult live) :
    InterpretExpression space d (.expression (p :: ps ++ x :: post))
      type_ b callResult live :=
  InterpretExpression.tuple_path _ _ _ tupleResult callResult
    (by simpa using h_has)
    (interpretTuple_swap same h_sub (p :: ps) rfl h_tuple)
    h_call (by simp [Atom.unit])

/-- `EvalAtom` transport for tuple-path `interpret_success` derivations at
non-head positions.  All `interpret_success` side conditions about the
source transfer from the successor's (same head, same expected type, both
proper expressions); the interpretation transports; the success-filter
condition is about the (identical) result. -/
theorem evalAtom_swap_tuple_path
    {space : Space} {d : GroundedDispatch} {x x' : Atom}
    (same : atomVariables x' = atomVariables x)
    (h_sub : ∀ (b' : Bindings) (r' : ResultPair) {scope : List Atom},
      EvalAtom space d x' Atom.undefinedType b' r' scope →
      EvalAtom space d x Atom.undefinedType b' r' scope)
    (p : Atom) (ps : List Atom) {post : List Atom}
    {type_ : Atom} {live : List Atom} {b : Bindings} {tupleResult r : ResultPair}
    (h_not_err : isEmptyOrError (.expression (p :: ps ++ x :: post)) = false)
    (h_not_pass : ¬(type_ = Atom.atomType
      ∨ type_ = getMetaType (Atom.expression (p :: ps ++ x :: post))
      ∨ getMetaType (Atom.expression (p :: ps ++ x :: post))
          = Atom.variableType))
    (h_has : ∃ t ∈ getAtomTypes space p,
      isFunctionType t = false ∨ t = Atom.undefinedType)
    (h_tuple : InterpretTuple space d
      (.expression (p :: ps ++ x' :: post)) b tupleResult (type_ :: live))
    (h_call : MettaCall space d tupleResult.1 type_ tupleResult.2 r live)
    (h_not_error : isErrorAtom r.1 = false) :
    EvalAtom space d (.expression (p :: ps ++ x :: post)) type_ b r live :=
  EvalAtom.interpret_success _ _ _ _
    h_not_err
    h_not_pass
    rfl
    (by intro h_unit; simp [Atom.unit] at h_unit)
    (interpretExpression_swap_tuple_path same h_sub p ps h_has h_tuple h_call)
    h_not_error

end Mettapedia.Languages.MeTTa.HE
