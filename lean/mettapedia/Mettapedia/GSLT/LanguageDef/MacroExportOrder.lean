import Mettapedia.GSLT.LanguageDef.MacroExportStateful

/-!
# Where the export's evaluation order is unobservable

The interpreter evaluates the operands of `+`, `==`, `>`, `[]`, `=`, `+=` and
of calls left to right. C leaves their order unspecified (C11 6.5p3), so a
compiler may pick another. `disciplined` checks an exported block: every
operand of such a construct is a simple read (a name, a constant, the address
of a name, a load or subscript through simple reads, or a type's size), except
that a plain assignment to a named local may have any right operand, because
the left operand then only names a location. A compound assignment also reads
that location and requires simple reads on both sides. `simple_preserves` shows that a simple
read changes no state, and `values_simple` that each operand of a call made of
simple reads has, evaluated alone from the initial state, the value the
left-to-right evaluation gives it. So every order a compiler may choose
computes the same values with the same effects.
-/

namespace Mettapedia.GSLT.LanguageDef.MacroExportOrder

open Mettapedia.GSLT.LanguageDef.MacroExportPlan
open Mettapedia.GSLT.LanguageDef.MacroExportStateful

set_option autoImplicit false

/-- A read whose evaluation changes no state. -/
def simpleOperand : Marked → Bool
  | .symbol _ => true
  | .name _ => true
  | .list [.symbol "&", .name _] => true
  | .list [.symbol "*", x] => simpleOperand x
  | .list [.symbol "[]", a, b] => simpleOperand a && simpleOperand b
  | .list [.symbol "sizeof", .symbol "type", _] => true
  | _ => false

def isName : Marked → Bool
  | .name _ => true
  | _ => false

mutual
  /-- Every unsequenced operand is a simple read, except the right operand of
  an assignment to a named local. Compile-time items are not evaluated. -/
  def disciplined : Marked → Bool
    | .list (.symbol "_Static_assert" :: _) => true
    | .list (.symbol "typedef" :: _) => true
    | .list (.symbol "call" :: callee :: args) =>
        simpleOperand callee && simpleMany args && disciplinedMany args
    | .list [.symbol op, l, r] =>
        (if op == "=" then isName l || (simpleOperand l && simpleOperand r)
         else if op == "+=" || op == "+" || op == "==" || op == ">" || op == "[]" then simpleOperand l && simpleOperand r
         else true) && disciplined l && disciplined r
    | .list items => disciplinedMany items
    | _ => true
  def disciplinedMany : List Marked → Bool
    | [] => true
    | m :: rest => disciplined m && disciplinedMany rest
  def simpleMany : List Marked → Bool
    | [] => true
    | m :: rest => simpleOperand m && simpleMany rest
end

/-- The simple reads, as a derivation. -/
inductive Simple : Marked → Prop where
  | constant (s : String) : Simple (.symbol s)
  | name (n : String) : Simple (.name n)
  | address (n : String) : Simple (.list [.symbol "&", .name n])
  | load {x : Marked} : Simple x → Simple (.list [.symbol "*", x])
  | index {a b : Marked} : Simple a → Simple b → Simple (.list [.symbol "[]", a, b])
  | size (t : Marked) : Simple (.list [.symbol "sizeof", .symbol "type", t])

theorem simple_of_check (t : Marked) (h : simpleOperand t = true) : Simple t := by
  fun_induction simpleOperand t with
  | case1 s => exact .constant s
  | case2 n => exact .name n
  | case3 n => exact .address n
  | case4 x ih => exact .load (ih (by simpa [simpleOperand] using h))
  | case5 a b iha ihb =>
      simp only [Bool.and_eq_true] at h
      exact .index (iha h.1) (ihb h.2)
  | case6 t => exact .size t
  | case7 => simp at h

theorem addAssign_checks (l r : Marked)
    (h : disciplined (.list [.symbol "+=", l, r]) = true) :
    simpleOperand l = true ∧ simpleOperand r = true := by
  change ((simpleOperand l && simpleOperand r) && disciplined l && disciplined r) = true at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1

/-- A checked compound assignment cannot hide effects behind a named left
operand: both value computations satisfy the simple-read judgment. -/
theorem addAssign_operands_simple (l r : Marked)
    (h : disciplined (.list [.symbol "+=", l, r]) = true) : Simple l ∧ Simple r := by
  obtain ⟨hl, hr⟩ := addAssign_checks l r h
  exact ⟨simple_of_check l hl, simple_of_check r hr⟩

/-- A simple read changes no state, as a value and as a place. -/
theorem simple_preserves (ctx : Ctx) (env : Env) {t : Marked} (h : Simple t) :
    (∀ st v st', value ctx env t st = .ok (v, st') → st' = st) ∧
      (∀ st l st', place ctx env t st = .ok (l, st') → st' = st) := by
  induction h with
  | constant s =>
      refine ⟨fun st v st' h => ?_, fun st l st' h => by simp [place] at h⟩
      simp only [value] at h
      split at h
      · cases h; rfl
      · cases h
  | name n =>
      refine ⟨fun st v st' h => ?_, fun st l st' h => ?_⟩
      · simp only [value, lookup, bind, Except.bind] at h
        cases hl : env.lookup n with
        | none => simp [hl] at h
        | some b =>
            cases b with
            | value w => simp [hl, pure, Except.pure] at h; exact h.2.symm
            | object l =>
                simp only [hl] at h
                cases hv : load st l with
                | error e => simp [hv] at h
                | ok w => simp [hv, pure, Except.pure] at h; exact h.2.symm
      · simp only [place, lookup, bind, Except.bind] at h
        cases hl : env.lookup n with
        | none => simp [hl] at h
        | some b =>
            cases b with
            | value w => simp [hl] at h
            | object l' => simp [hl, pure, Except.pure] at h; exact h.2.symm
  | address n =>
      refine ⟨fun st v st' h => ?_, fun st l st' h => by simp [place] at h⟩
      rw [value.eq_7 _ _ _ _ (fun _ e => by cases e)] at h
      simp only [place, lookup, bind, Except.bind] at h
      cases hl : env.lookup n with
      | none => simp [hl] at h
      | some b =>
          cases b with
          | value w => simp [hl] at h
          | object l => simp [hl, pure, Except.pure] at h; exact h.2.symm
  | @load x _ ih =>
      have pl : ∀ st l st', place ctx env (.list [.symbol "*", x]) st = .ok (l, st') → st' = st := by
        intro st l st' h
        simp only [place, bind, Except.bind] at h
        cases hv : value ctx env x st with
        | error e => simp [hv] at h
        | ok r =>
            obtain ⟨p, s⟩ := r
            have := ih.1 st p s hv
            subst this
            simp only [hv] at h
            cases p <;> simp [pure, Except.pure] at h
            exact h.2.symm
      refine ⟨fun st v st' h => ?_, pl⟩
      simp only [value, bind, Except.bind] at h
      cases hp : place ctx env (.list [.symbol "*", x]) st with
      | error e => simp [hp] at h
      | ok r =>
          obtain ⟨l, s⟩ := r
          have := pl st l s hp
          subst this
          simp only [hp] at h
          cases hv : load s l with
          | error e => simp [hv] at h
          | ok w => simp [hv, pure, Except.pure] at h; exact h.2.symm
  | @index a b _ _ iha ihb =>
      have pl : ∀ st l st', place ctx env (.list [.symbol "[]", a, b]) st = .ok (l, st') → st' = st := by
        intro st l st' h
        simp only [place, bind, Except.bind] at h
        cases hv : value ctx env a st with
        | error e => simp [hv] at h
        | ok r =>
            obtain ⟨p, s⟩ := r
            have := iha.1 st p s hv
            subst this
            simp only [hv] at h
            cases hw : value ctx env b s with
            | error e => simp [hw] at h
            | ok r2 =>
                obtain ⟨i, s2⟩ := r2
                have := ihb.1 s i s2 hw
                subst this
                simp only [hw] at h
                cases p <;> cases i <;> simp [pure, Except.pure] at h
                exact h.2.symm
      refine ⟨fun st v st' h => ?_, pl⟩
      simp only [value, bind, Except.bind] at h
      cases hp : place ctx env (.list [.symbol "[]", a, b]) st with
      | error e => simp [hp] at h
      | ok r =>
          obtain ⟨l, s⟩ := r
          have := pl st l s hp
          subst this
          simp only [hp] at h
          cases hv : load s l with
          | error e => simp [hv] at h
          | ok w => simp [hv, pure, Except.pure] at h; exact h.2.symm
  | size t =>
      refine ⟨fun st v st' h => ?_, fun st l st' h => by simp [place] at h⟩
      simp only [value, bind, Except.bind] at h
      cases hty : typeOf ctx t with
      | error e => simp [hty] at h
      | ok ty =>
          simp only [hty] at h
          cases hs : ctx.profile.sizeOf ty <;> simp [hs, pure, Except.pure] at h
          exact h.2.symm

/-- Operands that are simple reads each have, evaluated alone from the initial
state, the value they have in the left-to-right evaluation, which changes no
state: any order computes the same values. -/
theorem values_simple (ctx : Ctx) (env : Env) :
    ∀ (args : List Marked), simpleMany args = true → ∀ st vs st',
      values ctx env args st = .ok (vs, st') →
        st' = st ∧ List.Forall₂ (fun a v => value ctx env a st = .ok (v, st)) args vs
  | [], _, st, vs, st', h => by simp only [values] at h; cases h; exact ⟨rfl, .nil⟩
  | a :: rest, hs, st, vs, st', h => by
      simp only [simpleMany, Bool.and_eq_true] at hs
      simp only [values, bind, Except.bind] at h
      cases hr : value ctx env a st with
      | error e => simp [hr] at h
      | ok r =>
          obtain ⟨v, s⟩ := r
          have hs1 := (simple_preserves ctx env (simple_of_check a hs.1)).1 st v s hr
          subst hs1
          simp only [hr] at h
          cases hr2 : values ctx env rest s with
          | error e => simp [hr2] at h
          | ok r2 =>
              obtain ⟨vs2, s2⟩ := r2
              obtain ⟨hs2, hall⟩ := values_simple ctx env rest hs.2 s vs2 s2 hr2
              subst hs2
              simp only [hr2, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨rfl, .cons hr hall⟩

/-- The input reads of a checked compound assignment are stable: evaluation
does not change the state, and each input has its initial-state value. The
assignment's final store remains a separate operation. -/
theorem addAssign_inputs_stable (ctx : Ctx) (env : Env) (l r : Marked)
    (h : disciplined (.list [.symbol "+=", l, r]) = true) (st : State) (vs : List Val) (st' : State)
    (evaluated : values ctx env [l, r] st = .ok (vs, st')) :
    st' = st ∧ List.Forall₂ (fun a v => value ctx env a st = .ok (v, st)) [l, r] vs := by
  have checked := addAssign_checks l r h
  exact values_simple ctx env [l, r] (by simp [simpleMany, checked]) st vs st' evaluated

/-! ## Examples -/

/-- A call's operands are reads: any order. -/
example : disciplined (.list [.symbol "call", .symbol "__builtin_add_overflow", .name "value_1", .symbol "0",
    .list [.symbol "&", .name "converted_1"]]) = true := by decide

/-- A call's result assigned to a named local: the location needs no evaluation. -/
example : disciplined (.list [.symbol "=", .name "replacement_1",
    .list [.symbol "call", .name "resize_1", .list [.symbol "*", .name "buffer_1"], .name "bytes_1"]]) = true := by
  decide

/-- A call beside a read of memory: a compiler may order them either way. -/
example : disciplined (.list [.symbol "+", .list [.symbol "call", .name "f"], .name "x"]) = false := by decide

/-- A store through a pointer whose right side calls: the pointer's load and the call are unsequenced. -/
example : disciplined (.list [.symbol "=", .list [.symbol "*", .name "p"], .list [.symbol "call", .name "f"]]) =
    false := by decide

/-- Caller code is not a simple read. -/
example : disciplined (.list [.symbol "+", .operand 0, .name "x"]) = false := by decide

/-- Compound assignment reads its destination; an increment on its right is
not an independent input computation. -/
theorem incrementing_addAssign_refused :
    disciplined (.list [.symbol "+=", .name "x", .list [.symbol "++", .name "x"]]) = false := by decide

/-- A read of the same destination is permitted when neither input writes. -/
theorem reading_addAssign_allowed :
    disciplined (.list [.symbol "+=", .name "x", .name "x"]) = true := by decide

end Mettapedia.GSLT.LanguageDef.MacroExportOrder
