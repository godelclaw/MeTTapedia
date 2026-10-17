import Mettapedia.Languages.MeTTa.HE.SmallStep

/-!
# Sharing in the reflected one-step relation of HE

All statements in this module are about the HE language.

The coarse one-step relation `HESmallStep` gives equation matching priority over
argument congruence. On `same (pick)`, with `(= (same $x) (pair $x $x))`,
`(= (pick) a)` and `(= (pick) b)`, the equation for `same` fires on the
unevaluated argument `(pick)` and copies it; the two copies then step
independently. The relation reaches the normal form `(pair a b)`
(`reflected_reaches_mixed_pair`), a pair whose components were chosen twice.
The HE evaluator chooses an argument once and substitutes the chosen value
(`ArgTraversal.Controls.chosen_once_reused_twice`): it answers only the
diagonal pairs.

`ArgFirstStep` is the repaired successor relation, stated as a specification for
the application fragment (equations and argument congruence; special forms,
grounded dispatch and effects keep their `HESmallStep` rules and are outside this
specification). An argument position is evaluated unless the head declares it
raw (`raw`; for HE, a parameter typed `Atom` or `Expression`). The leftmost
evaluated argument that can step steps first, and an equation fires only when
every evaluated argument is quiescent. So a pattern variable that is used twice
is bound to a quiescent argument, and a choice is copied only after it has been
made.

* `argFirst_quiet_reflected`: once the evaluated arguments are quiescent, every
  step of the repaired relation is an equation step of `HESmallStep`; the repair
  reorders, it adds no successor.
* `argFirst_reachable`: from `same (pick)` the repaired relation reaches exactly
  `same (pick)`, `same a`, `same b`, `pair a a` and `pair b b`; the two pairs
  are its normal forms, and `pair a b` is not reachable.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.ReflectedStepSharing

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-! ## The example -/

def a : Atom := .symbol "a"
def b : Atom := .symbol "b"
def pickCall : Atom := .expression [.symbol "pick"]
def sameOf (x : Atom) : Atom := .expression [.symbol "same", x]
def pairOf (x y : Atom) : Atom := .expression [.symbol "pair", x, y]
def equation (l r : Atom) : Atom := .expression [.symbol "=", l, r]

def space : Space := Space.ofList
  [equation (sameOf (.var "x")) (pairOf (.var "x") (.var "x")),
   equation pickCall a, equation pickCall b]

def fuel : Nat := 30

abbrev d : GroundedDispatch := GroundedDispatch.none

def xFresh : Atom := .var "x#0"

/-- Root instances use the same visible-name discipline as the reflected relation. -/
private abbrev rootEquationQuery (space : Space) (atom : Atom) (fuel : Nat) :=
  queryEquationsAvoiding (equationScope [] atom Atom.undefinedType Bindings.empty) space atom fuel

theorem query_same (x : Atom) (hx : x = pickCall ∨ x = a ∨ x = b) :
    rootEquationQuery space (sameOf x) fuel =
      [(pairOf xFresh xFresh, ⟨[("x#0", x)], []⟩)] := by
  rcases hx with rfl | rfl | rfl <;> decide +kernel

theorem query_pick :
    rootEquationQuery space pickCall fuel = [(a, ⟨[], []⟩), (b, ⟨[], []⟩)] := by
  decide +kernel

theorem query_pair (x y : Atom) (hx : x = pickCall ∨ x = a ∨ x = b)
    (hy : y = pickCall ∨ y = a ∨ y = b) : rootEquationQuery space (pairOf x y) fuel = [] := by
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> decide +kernel

theorem apply_pair (x : Atom) (hx : x = pickCall ∨ x = a ∨ x = b) :
    (⟨[("x#0", x)], []⟩ : Bindings).applyFull (pairOf xFresh xFresh) fuel = pairOf x x := by
  rcases hx with rfl | rfl | rfl <;> decide +kernel

theorem apply_empty (x : Atom) (hx : x = a ∨ x = b) :
    (⟨[], []⟩ : Bindings).applyFull x fuel = x := by
  rcases hx with rfl | rfl <;> decide +kernel

theorem noLoop (x : Atom) (hx : x = pickCall ∨ x = a ∨ x = b) :
    (⟨[("x#0", x)], []⟩ : Bindings).hasLoop = false := by
  rcases hx with rfl | rfl | rfl <;> decide +kernel

/-! ## The reflected relation copies the unevaluated argument -/

theorem symbol_cannot_step (s : String) {live : List Atom} : ¬ HECanSmallStep space d fuel (.symbol s) live := by
  intro h
  cases h with
  | grounded _ hr =>
      obtain ⟨op, args, rs, r, bs, heq, _, _, _⟩ := hr
      cases heq
  | equation hr =>
      obtain ⟨⟨es, heq⟩, _⟩ := hr
      cases heq

theorem not_special (s : String) (hs : s = "same" ∨ s = "pair" ∨ s = "pick")
    (rest : List Atom) : ¬ SpecialFormHead (.expression (.symbol s :: rest)) := by
  rcases hs with rfl | rfl | rfl <;> simp [SpecialFormHead]

theorem head_not_executable (op : Atom) (hop : op = .symbol "same" ∨ op = .symbol "pair" ∨
    op = .symbol "pick") (rest : List Atom) : HeadNotExecutable d (.expression (op :: rest)) := by
  rcases hop with rfl | rfl | rfl <;> simp [HeadNotExecutable, d, GroundedDispatch.none]

theorem not_grounded (es : List Atom) : ¬ GroundedRedex d (.expression es) := by
  rintro ⟨op, args, rs, r, bs, _, hexec, _, _⟩
  simp [d, GroundedDispatch.none] at hexec

theorem pair_not_equationRedex (x y : Atom) (hx : x = pickCall ∨ x = a ∨ x = b)
    (hy : y = pickCall ∨ y = a ∨ y = b) : ¬ EquationRedex space d fuel (pairOf x y) := by
  rintro ⟨_, _, _, p, hp, _⟩
  change p ∈ rootEquationQuery space (pairOf x y) fuel at hp
  rw [query_pair x y hx hy] at hp
  simp at hp

theorem pick_step (x : Atom) (hx : x = a ∨ x = b) {live : List Atom}
    (h_live : atomListVariables live = []) : HESmallStep space d fuel pickCall x live := by
  have hstep := HESmallStep.equation_match (space := space) (d := d) (fuel := fuel)
    (live := live) (es := [.symbol "pick"]) (rhs := x) (qb := ⟨[], []⟩)
    (not_special "pick" (by simp) []) (head_not_executable _ (by simp) [])
    (by
      simp only [equationScope, h_live, List.nil_append]
      change (x, (⟨[], []⟩ : Bindings)) ∈ rootEquationQuery space pickCall fuel
      rw [query_pick]
      rcases hx with rfl | rfl <;> simp)
    (by decide)
  rwa [apply_empty x hx] at hstep

theorem reflected_copies :
    HESmallStep space d fuel (sameOf pickCall) (pairOf pickCall pickCall) := by
  have hstep := HESmallStep.equation_match (space := space) (d := d) (fuel := fuel)
    (live := []) (es := [.symbol "same", pickCall]) (rhs := pairOf xFresh xFresh)
    (qb := ⟨[("x#0", pickCall)], []⟩)
    (not_special "same" (by simp) _) (head_not_executable _ (by simp) _)
    (by
      show _ ∈ rootEquationQuery space (sameOf pickCall) fuel
      rw [query_same pickCall (by simp)]
      simp)
    (noLoop pickCall (by simp))
  rwa [apply_pair pickCall (by simp)] at hstep

theorem reflected_left :
    HESmallStep space d fuel (pairOf pickCall pickCall) (pairOf a pickCall) := by
  have h := HESmallStep.leftmost_congruence (space := space) (d := d) (fuel := fuel)
    (pre := [.symbol "pair"]) (a := pickCall) (a' := a) (post := [pickCall])
    (not_special "pair" (by simp) _) (not_grounded _)
    (pair_not_equationRedex pickCall pickCall (by simp) (by simp))
    (by
      intro y hy
      simp only [List.mem_singleton] at hy
      subst hy
      exact symbol_cannot_step "pair")
    (pick_step a (by simp) (by decide +kernel))
  exact h

theorem reflected_right :
    HESmallStep space d fuel (pairOf a pickCall) (pairOf a b) := by
  have h := HESmallStep.leftmost_congruence (space := space) (d := d) (fuel := fuel)
    (pre := [.symbol "pair", a]) (a := pickCall) (a' := b) (post := [])
    (not_special "pair" (by simp) _) (not_grounded _)
    (pair_not_equationRedex a pickCall (by simp) (by simp))
    (by
      intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · exact symbol_cannot_step "pair"
      · exact symbol_cannot_step "a")
    (pick_step b (by simp) (by decide +kernel))
  exact h

theorem pair_quiescent (x y : Atom) (hx : x = a ∨ x = b) (hy : y = a ∨ y = b) :
    ¬ HECanSmallStep space d fuel (pairOf x y) := by
  have hxs : ∃ s, x = .symbol s := by rcases hx with rfl | rfl <;> exact ⟨_, rfl⟩
  have hys : ∃ s, y = .symbol s := by rcases hy with rfl | rfl <;> exact ⟨_, rfl⟩
  obtain ⟨sx, rfl⟩ := hxs
  obtain ⟨sy, rfl⟩ := hys
  intro h
  cases h with
  | grounded _ hr => exact not_grounded _ hr
  | equation hr =>
      exact pair_not_equationRedex _ _ (by rcases hx with h | h <;> simp [h])
        (by rcases hy with h | h <;> simp [h]) hr
  | eval_form h_shape => simp at h_shape
  | chain_form h_shape => simp at h_shape
  | function_form h_shape => simp at h_shape
  | letStar_empty_form h_shape => simp at h_shape
  | letStar_unroll_form h_shape => simp at h_shape
  | let_source_form h_shape => simp at h_shape
  | let_subst_form h_shape => simp at h_shape
  | case_scrutinee_form h_shape => simp at h_shape
  | case_match_form h_shape => simp at h_shape
  | switch_scrutinee_form h_shape => simp at h_shape
  | switch_match_form h_shape => simp at h_shape
  | switch_minimal_form h_shape => simp at h_shape
  | element _ h_mem h_e =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h_mem
      rcases h_mem with rfl | rfl | rfl
      · exact symbol_cannot_step _ h_e
      · exact symbol_cannot_step _ h_e
      · exact symbol_cannot_step _ h_e

/-- **The discrepancy.** The reflected relation reaches the normal form
`(pair a b)` from `same (pick)`: the argument is chosen twice. -/
theorem reflected_reaches_mixed_pair :
    Relation.ReflTransGen (HESmallStep space d fuel) (sameOf pickCall) (pairOf a b) ∧
      ¬ HECanSmallStep space d fuel (pairOf a b) :=
  ⟨.tail (.tail (.single reflected_copies) reflected_left) reflected_right,
    pair_quiescent a b (by simp) (by simp)⟩

/-! ## The repaired successor relation -/

/-- Steppability for the argument-first relation. -/
inductive ArgFirstCan (space : Space) (raw : Atom → Nat → Bool) (fuel : Nat) : Atom → Prop where
  | arg {op : Atom} {pre : List Atom} {x : Atom} {post : List Atom}
      (h_raw : raw op pre.length = false) (h : ArgFirstCan space raw fuel x) :
      ArgFirstCan space raw fuel (.expression (op :: pre ++ x :: post))
  | equation {es : List Atom}
      (h : ∃ p ∈ rootEquationQuery space (.expression es) fuel, p.2.hasLoop = false) :
      ArgFirstCan space raw fuel (.expression es)

/-- **The argument-first successor relation.** The leftmost evaluated argument
that can step steps first; an equation fires only when every evaluated argument
is quiescent. -/
inductive ArgFirstStep (space : Space) (raw : Atom → Nat → Bool) (fuel : Nat) :
    Atom → Atom → Prop where
  | arg {op : Atom} {pre : List Atom} {x x' : Atom} {post : List Atom}
      (h_raw : raw op pre.length = false)
      (h_pre : ∀ (i : Nat) (y : Atom), pre[i]? = some y → raw op i = false →
        ¬ ArgFirstCan space raw fuel y)
      (h_step : ArgFirstStep space raw fuel x x') :
      ArgFirstStep space raw fuel (.expression (op :: pre ++ x :: post))
        (.expression (op :: pre ++ x' :: post))
  | equation {op : Atom} {args : List Atom} {rhs : Atom} {qb : Bindings}
      (h_quiet : ∀ (i : Nat) (y : Atom), args[i]? = some y → raw op i = false →
        ¬ ArgFirstCan space raw fuel y)
      (h_query : (rhs, qb) ∈ rootEquationQuery space (.expression (op :: args)) fuel)
      (h_no_loop : qb.hasLoop = false) :
      ArgFirstStep space raw fuel (.expression (op :: args)) (qb.applyFull rhs fuel)

theorem ArgFirstStep.can {space : Space} {raw : Atom → Nat → Bool} {fuel : Nat} {x x' : Atom}
    (h : ArgFirstStep space raw fuel x x') : ArgFirstCan space raw fuel x := by
  induction h with
  | arg h_raw _ _ ih => exact .arg h_raw ih
  | equation _ h_query h_no_loop => exact .equation ⟨_, h_query, h_no_loop⟩

/-- **The repair adds no successor.** At a head that is neither a special form
nor executable, once every evaluated argument is quiescent, every step of the
argument-first relation is an equation step of `HESmallStep`. -/
theorem argFirst_quiet_reflected {space : Space} {raw : Atom → Nat → Bool} {fuel : Nat}
    {d : GroundedDispatch} {op : Atom} {args : List Atom} {t : Atom}
    (h_not_special : ¬ SpecialFormHead (.expression (op :: args)))
    (h_not_grounded : HeadNotExecutable d (.expression (op :: args)))
    (h_quiet : ∀ (i : Nat) (y : Atom), args[i]? = some y → raw op i = false →
      ¬ ArgFirstCan space raw fuel y)
    (h : ArgFirstStep space raw fuel (.expression (op :: args)) t) :
    HESmallStep space d fuel (.expression (op :: args)) t := by
  cases h with
  | @arg _ pre x x' post h_raw _ h_step =>
      exact absurd h_step.can (h_quiet pre.length x (by simp) h_raw)
  | equation _ h_query h_no_loop => exact .equation_match h_not_special h_not_grounded h_query h_no_loop

/-- No argument position is raw: `same`, `pick` and `pair` evaluate their
arguments. -/
def noRaw : Atom → Nat → Bool := fun _ _ => false

theorem argFirst_symbol_cannot (s : String) : ¬ ArgFirstCan space noRaw fuel (.symbol s) := by
  intro h
  cases h

theorem argFirst_pick_can : ArgFirstCan space noRaw fuel pickCall :=
  .equation ⟨(a, ⟨[], []⟩), by
    show (a, (⟨[], []⟩ : Bindings)) ∈ rootEquationQuery space pickCall fuel
    rw [query_pick]; simp, rfl⟩

theorem expr_cons_inj {op op' : Atom} {xs ys : List Atom}
    (h : Atom.expression (op :: xs) = Atom.expression (op' :: ys)) : op = op' ∧ xs = ys := by
  cases h
  exact ⟨rfl, rfl⟩

theorem argFirst_pick_step (x : Atom) (hx : x = a ∨ x = b) :
    ArgFirstStep space noRaw fuel pickCall x := by
  have h := ArgFirstStep.equation (space := space) (raw := noRaw) (fuel := fuel)
    (op := .symbol "pick") (args := []) (rhs := x) (qb := ⟨[], []⟩)
    (by intro i y hy; simp at hy)
    (by
      show (x, (⟨[], []⟩ : Bindings)) ∈ rootEquationQuery space pickCall fuel
      rw [query_pick]
      rcases hx with rfl | rfl <;> simp)
    (by decide)
  rwa [apply_empty x hx] at h

/-- The argument steps first. -/
theorem argFirst_same_pick (x : Atom) (hx : x = a ∨ x = b) :
    ArgFirstStep space noRaw fuel (sameOf pickCall) (sameOf x) :=
  ArgFirstStep.arg (op := .symbol "same") (pre := []) (post := []) rfl
    (by intro i y hy; simp at hy) (argFirst_pick_step x hx)

/-- The equation copies the chosen value. -/
theorem argFirst_same_value (x : Atom) (hx : x = a ∨ x = b) :
    ArgFirstStep space noRaw fuel (sameOf x) (pairOf x x) := by
  have hxs : ∃ s, x = .symbol s := by rcases hx with rfl | rfl <;> exact ⟨_, rfl⟩
  have h := ArgFirstStep.equation (space := space) (raw := noRaw) (fuel := fuel)
    (op := .symbol "same") (args := [x]) (rhs := pairOf xFresh xFresh)
    (qb := ⟨[("x#0", x)], []⟩)
    (by
      intro i y hy _
      obtain ⟨s, rfl⟩ := hxs
      cases i with
      | zero => simp at hy; subst hy; exact argFirst_symbol_cannot s
      | succ i => simp at hy)
    (by
      show _ ∈ rootEquationQuery space (sameOf x) fuel
      rw [query_same x (by rcases hx with h | h <;> simp [h])]
      simp)
    (noLoop x (by rcases hx with h | h <;> simp [h]))
  rwa [apply_pair x (by rcases hx with h | h <;> simp [h])] at h

/-! ### Inversion -/

theorem argFirst_inv_pick : ∀ e t, ArgFirstStep space noRaw fuel e t → e = pickCall →
    t = a ∨ t = b := by
  intro e t h
  cases h with
  | @arg op pre x x' post _ _ _ =>
      intro heq
      obtain ⟨-, h2⟩ := expr_cons_inj (ys := []) heq
      replace h2 : pre ++ x :: post = [] := h2
      simp at h2
  | @equation op args rhs qb _ h_query _ =>
      intro heq
      rw [heq, query_pick] at h_query
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h_query
      rcases h_query with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · left; exact apply_empty a (by simp)
      · right; exact apply_empty b (by simp)

theorem argFirst_inv_same_pick : ∀ e t, ArgFirstStep space noRaw fuel e t →
    e = sameOf pickCall → t = sameOf a ∨ t = sameOf b := by
  intro e t h
  cases h with
  | @arg op pre x x' post _ _ hstep =>
      intro heq
      obtain ⟨rfl, h2⟩ := expr_cons_inj (ys := [pickCall]) heq
      replace h2 : pre ++ x :: post = [pickCall] := h2
      cases pre with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at h2
          obtain ⟨rfl, rfl⟩ := h2
          rcases argFirst_inv_pick _ _ hstep rfl with rfl | rfl
          · left; rfl
          · right; rfl
      | cons y ys => simp at h2
  | @equation op args rhs qb h_quiet _ _ =>
      intro heq
      obtain ⟨rfl, rfl⟩ := expr_cons_inj (ys := [pickCall]) heq
      exact absurd argFirst_pick_can (h_quiet 0 pickCall rfl rfl)

theorem argFirst_inv_same_value (x : Atom) (hx : x = a ∨ x = b) :
    ∀ e t, ArgFirstStep space noRaw fuel e t → e = sameOf x → t = pairOf x x := by
  have hxs : ∃ s, x = .symbol s := by rcases hx with rfl | rfl <;> exact ⟨_, rfl⟩
  obtain ⟨s, hs⟩ := hxs
  intro e t h
  cases h with
  | @arg op pre y y' post _ _ hstep =>
      intro heq
      obtain ⟨rfl, h2⟩ := expr_cons_inj (ys := [x]) heq
      replace h2 : pre ++ y :: post = [x] := h2
      cases pre with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at h2
          obtain ⟨rfl, rfl⟩ := h2
          subst hs
          cases hstep
      | cons z zs => simp at h2
  | @equation op args rhs qb _ h_query _ =>
      intro heq
      rw [heq, query_same x (by rcases hx with h | h <;> simp [h])] at h_query
      simp only [List.mem_singleton, Prod.mk.injEq] at h_query
      obtain ⟨rfl, rfl⟩ := h_query
      exact apply_pair x (by rcases hx with h | h <;> simp [h])

theorem argFirst_pair_quiescent (x : Atom) (hx : x = a ∨ x = b) :
    ∀ e t, ArgFirstStep space noRaw fuel e t → e ≠ pairOf x x := by
  have hxs : ∃ s, x = .symbol s := by rcases hx with rfl | rfl <;> exact ⟨_, rfl⟩
  obtain ⟨s, hs⟩ := hxs
  intro e t h
  cases h with
  | @arg op pre y y' post _ _ hstep =>
      intro heq
      obtain ⟨rfl, h2⟩ := expr_cons_inj (ys := [x, x]) heq
      replace h2 : pre ++ y :: post = [x, x] := h2
      cases pre with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at h2
          obtain ⟨rfl, -⟩ := h2
          subst hs
          cases hstep
      | cons z zs =>
          cases zs with
          | nil =>
              simp only [List.cons_append, List.nil_append, List.cons.injEq] at h2
              obtain ⟨-, rfl, -⟩ := h2
              subst hs
              cases hstep
          | cons w ws => simp at h2
  | @equation op args rhs qb _ h_query _ =>
      intro heq
      rw [heq, query_pair x x (by rcases hx with h | h <;> simp [h])
        (by rcases hx with h | h <;> simp [h])] at h_query
      simp at h_query

/-- The terms reachable from `same (pick)` under the argument-first relation. -/
def ArgFirstReach (t : Atom) : Prop :=
  t = sameOf pickCall ∨ t = sameOf a ∨ t = sameOf b ∨ t = pairOf a a ∨ t = pairOf b b

/-- **The repaired relation chooses once.** From `same (pick)` it reaches exactly
five terms; `pair a a` and `pair b b` are reached and are its normal forms, and
`pair a b` is never reached. -/
theorem argFirst_reachable :
    (∀ t, Relation.ReflTransGen (ArgFirstStep space noRaw fuel) (sameOf pickCall) t →
      ArgFirstReach t) ∧
    Relation.ReflTransGen (ArgFirstStep space noRaw fuel) (sameOf pickCall) (pairOf a a) ∧
    Relation.ReflTransGen (ArgFirstStep space noRaw fuel) (sameOf pickCall) (pairOf b b) ∧
    (∀ t, ¬ ArgFirstStep space noRaw fuel (pairOf a a) t) ∧
    (∀ t, ¬ ArgFirstStep space noRaw fuel (pairOf b b) t) ∧
    ¬ Relation.ReflTransGen (ArgFirstStep space noRaw fuel) (sameOf pickCall) (pairOf a b) := by
  have closed : ∀ t, Relation.ReflTransGen (ArgFirstStep space noRaw fuel) (sameOf pickCall) t →
      ArgFirstReach t := by
    intro t h
    induction h with
    | refl => exact Or.inl rfl
    | tail _ hstep ih =>
        rcases ih with rfl | rfl | rfl | rfl | rfl
        · rcases argFirst_inv_same_pick _ _ hstep rfl with rfl | rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl rfl))
        · rw [argFirst_inv_same_value a (by simp) _ _ hstep rfl]
          exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        · rw [argFirst_inv_same_value b (by simp) _ _ hstep rfl]
          exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
        · exact absurd rfl (argFirst_pair_quiescent a (by simp) _ _ hstep)
        · exact absurd rfl (argFirst_pair_quiescent b (by simp) _ _ hstep)
  refine ⟨closed, ?_, ?_, fun t h => argFirst_pair_quiescent a (by simp) _ _ h rfl,
    fun t h => argFirst_pair_quiescent b (by simp) _ _ h rfl, ?_⟩
  · exact .tail (.single (argFirst_same_pick a (by simp))) (argFirst_same_value a (by simp))
  · exact .tail (.single (argFirst_same_pick b (by simp))) (argFirst_same_value b (by simp))
  · intro h
    rcases closed _ h with h | h | h | h | h <;> simp [sameOf, pairOf, pickCall, a, b] at h

end Mettapedia.Languages.MeTTa.HE.ReflectedStepSharing
