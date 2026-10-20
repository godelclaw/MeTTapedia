import Mettapedia.GSLT.LanguageDef.MacroExportStateful
import Mathlib.Data.List.Forall2

/-!
# The readable export corresponds to its source, construct by construct

`Sim params acq p s t` relates a source template term `s`, read with the
captured arguments `params`, to an exported term `t`, read with the acquisition
locals `acq`, at a position `p` (value, place, block item or type).
`sim_agrees` shows that related terms behave the same at their position for
every environment that keeps the acquisition locals visible. `admittedAt`
decides the template fragment the proof covers, and `lower_sim` shows that
lowering an admitted template gives the exported term that corresponds to its
instantiated source. `MacroExportTheorem` assembles these with the acquisition
into `export_correct`.
-/

namespace Mettapedia.GSLT.LanguageDef.MacroExportCorrect

open Mettapedia.GSLT.LanguageDef.MacroExportPlan
open Mettapedia.GSLT.LanguageDef.MacroExportStateful

set_option autoImplicit false

/-! ## Environments and release -/

theorem lookup_append_some (env acq : Env) (n : String) (b : Binding)
    (found : env.lookup n = some b) : (env ++ acq).lookup n = some b := by
  induction env with
  | nil => simp at found
  | cons head rest ih =>
      obtain ⟨k, c⟩ := head
      by_cases h : n = k
      · subst h; simpa [List.lookup] using found
      · simp only [List.cons_append, List.lookup, show (n == k) = false from by simpa using h] at found ⊢
        exact ih found

theorem lookup_append_none (env acq : Env) (n : String)
    (missing : env.lookup n = none) : (env ++ acq).lookup n = acq.lookup n := by
  induction env with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨k, c⟩ := head
      by_cases h : n = k
      · subst h; simp [List.lookup] at missing
      · simp only [List.cons_append, List.lookup, show (n == k) = false from by simpa using h] at missing ⊢
        exact ih missing

theorem release_release (start : Nat) (st : State) : release start (release start st) = release start st := by
  simp only [release]
  congr 1
  funext l
  by_cases h : start ≤ l.object <;> simp [h]

/-! ## What each argument slot stands for -/

/-- Slot `i` of the source and of the export denote the same thing: a syntax
argument is the caller's code in both; a value argument is the captured value,
held by the acquisition name; a place argument is the captured location,
held as a pointer by the acquisition name and dereferenced at each use. -/
inductive SlotAgrees (acq : Env) (i : Nat) : Option Param → Marked → Prop where
  | code : SlotAgrees acq i (some .syntax) (.operand i)
  | value (v : Val) (n : String) (bound : acq.lookup n = some (.value v)) :
      SlotAgrees acq i (some (.value v)) (.name n)
  | place (l : Loc) (n : String) (bound : acq.lookup n = some (.value (.ptr l))) :
      SlotAgrees acq i (some (.place l)) (.list [.symbol "*", .name n])

/-! ## Corresponding source and target terms -/

/-- How the interpreter reads a term: as a value, a place, a block item or a type. -/
inductive Pos where
  | value | place | stmt | type
  deriving DecidableEq, Repr

/-- Heads the interpreter reads as block items rather than expressions. -/
def stmtHead : Marked → Bool
  | .list (.symbol h :: _) => h == "_Static_assert" || h == "typedef" || h == "var" || h == "if" || h == "block"
  | _ => false

def builtinCallee : Marked → Bool
  | .symbol s => s == "__builtin_add_overflow" || s == "__builtin_mul_overflow"
  | _ => false

mutual
  /-- `Sim params acq p s t`: the source term `s`, read at `p` with the captured
  arguments `params`, and the exported term `t`, read at `p` with the
  acquisition locals `acq`, are the same construct with corresponding parts.
  Every constructor is one construct of the interpreter. -/
  inductive Sim (params : Nat → Option Param) (acq : Env) : Pos → Marked → Marked → Prop where
    | constant (s : String) : Sim params acq .value (.symbol s) (.symbol s)
    | localValue (n : String) (fresh : acq.lookup n = none) : Sim params acq .value (.name n) (.name n)
    | slotValue (i : Nat) (x : Marked) (agrees : SlotAgrees acq i (params i) x) :
        Sim params acq .value (.arg i) x
    | addressOfDeref {x y : Marked} : Sim params acq .value x y →
        Sim params acq .value (.list [.symbol "&", .list [.symbol "*", x]]) y
    | addressOfPlace (i : Nat) (l : Loc) (n : String) (captured : params i = some (.place l))
        (bound : acq.lookup n = some (.value (.ptr l))) :
        Sim params acq .value (.list [.symbol "&", .arg i]) (.name n)
    | addressOf {x y : Marked} : Sim params acq .place x y →
        (∀ z, x ≠ .list [.symbol "*", z]) → (∀ z, y ≠ .list [.symbol "*", z]) →
        Sim params acq .value (.list [.symbol "&", x]) (.list [.symbol "&", y])
    | deref {x y : Marked} : Sim params acq .value x y →
        Sim params acq .value (.list [.symbol "*", x]) (.list [.symbol "*", y])
    | index {a b a' b' : Marked} : Sim params acq .value a a' → Sim params acq .value b b' →
        Sim params acq .value (.list [.symbol "[]", a, b]) (.list [.symbol "[]", a', b'])
    | unary (op : String) (known : op = "!" ∨ op = "-") {x y : Marked} : Sim params acq .value x y →
        Sim params acq .value (.list [.symbol op, x]) (.list [.symbol op, y])
    | binary (op : String) (known : op = "+" ∨ op = "==" ∨ op = ">" ∨ op = "&&" ∨ op = "||" ∨ op = ",")
        {a b a' b' : Marked} : Sim params acq .value a a' → Sim params acq .value b b' →
        Sim params acq .value (.list [.symbol op, a, b]) (.list [.symbol op, a', b'])
    | assign (op : String) (known : op = "=" ∨ op = "+=") {l r l' r' : Marked} :
        Sim params acq .place l l' → Sim params acq .value r r' →
        Sim params acq .value (.list [.symbol op, l, r]) (.list [.symbol op, l', r'])
    | increment {l l' : Marked} : Sim params acq .place l l' →
        Sim params acq .value (.list [.symbol "++", l]) (.list [.symbol "++", l'])
    | choice {c a b c' a' b' : Marked} : Sim params acq .value c c' → Sim params acq .value a a' →
        Sim params acq .value b b' →
        Sim params acq .value (.list [.symbol "?:", c, a, b]) (.list [.symbol "?:", c', a', b'])
    | castVoid {x y : Marked} : Sim params acq .value x y →
        Sim params acq .value (.list [.symbol "cast", .symbol "void", x]) (.list [.symbol "cast", .symbol "void", y])
    | sizeofType {t t' : Marked} : Sim params acq .type t t' →
        Sim params acq .value (.list [.symbol "sizeof", .symbol "type", t]) (.list [.symbol "sizeof", .symbol "type", t'])
    | builtin (f : String) (known : f = "__builtin_add_overflow" ∨ f = "__builtin_mul_overflow")
        {args args' : List Marked} : Sims params acq .value args args' →
        Sim params acq .value (.list (.symbol "call" :: .symbol f :: args)) (.list (.symbol "call" :: .symbol f :: args'))
    | call {f f' : Marked} {args args' : List Marked} : Sim params acq .value f f' →
        builtinCallee f = false → builtinCallee f' = false → Sims params acq .value args args' →
        Sim params acq .value (.list (.symbol "call" :: f :: args)) (.list (.symbol "call" :: f' :: args'))
    | block {items items' : List Marked} : Sims params acq .stmt items items' →
        Sim params acq .value (.list (.symbol "block" :: items)) (.list (.symbol "block" :: items'))
    | localPlace (n : String) (fresh : acq.lookup n = none) : Sim params acq .place (.name n) (.name n)
    | slotPlace (i : Nat) (x : Marked) (agrees : SlotAgrees acq i (params i) x) :
        Sim params acq .place (.arg i) x
    | derefPlace {x y : Marked} : Sim params acq .value x y →
        Sim params acq .place (.list [.symbol "*", x]) (.list [.symbol "*", y])
    | indexPlace {a b a' b' : Marked} : Sim params acq .value a a' → Sim params acq .value b b' →
        Sim params acq .place (.list [.symbol "[]", a, b]) (.list [.symbol "[]", a', b'])
    | staticAssert (xs ys : List Marked) :
        Sim params acq .stmt (.list (.symbol "_Static_assert" :: xs)) (.list (.symbol "_Static_assert" :: ys))
    | typedef (xs ys : List Marked) :
        Sim params acq .stmt (.list (.symbol "typedef" :: xs)) (.list (.symbol "typedef" :: ys))
    | declareValue (n : String) (fresh : acq.lookup n = none) {init init' : Marked} :
        Sim params acq .value init init' →
        Sim params acq .stmt (.list [.symbol "var", .symbol "__auto_type", .name n, init])
          (.list [.symbol "var", .symbol "__auto_type", .name n, init'])
    | declare (n : String) (fresh : acq.lookup n = none) {t t' : Marked} : Sim params acq .type t t' →
        Sim params acq .stmt (.list [.symbol "var", t, .name n]) (.list [.symbol "var", t', .name n])
    | declarePointer (n : String) (fresh : acq.lookup n = none) {t t' : Marked} : Sim params acq .type t t' →
        Sim params acq .stmt (.list [.symbol "var", t, .list [.symbol "*", .name n]])
          (.list [.symbol "var", t', .list [.symbol "*", .name n]])
    | declareInit (n : String) (fresh : acq.lookup n = none) {t t' init init' : Marked} :
        Sim params acq .type t t' → t ≠ .symbol "__auto_type" → t' ≠ .symbol "__auto_type" →
        Sim params acq .value init init' →
        Sim params acq .stmt (.list [.symbol "var", t, .name n, init]) (.list [.symbol "var", t', .name n, init'])
    | when {c a c' a' : Marked} : Sim params acq .value c c' → Sim params acq .stmt a a' →
        Sim params acq .stmt (.list [.symbol "if", c, a]) (.list [.symbol "if", c', a'])
    | choose {c a b c' a' b' : Marked} : Sim params acq .value c c' → Sim params acq .stmt a a' →
        Sim params acq .stmt b b' →
        Sim params acq .stmt (.list [.symbol "if", c, a, b]) (.list [.symbol "if", c', a', b'])
    | blockStmt {items items' : List Marked} : Sims params acq .stmt items items' →
        Sim params acq .stmt (.list (.symbol "block" :: items)) (.list (.symbol "block" :: items'))
    | expr {s t : Marked} : Sim params acq .value s t → stmtHead s = false → stmtHead t = false →
        Sim params acq .stmt s t
    | typeSymbol (s : String) : Sim params acq .type (.symbol s) (.symbol s)
    | typeText (s : String) : Sim params acq .type (.text s) (.text s)
    | typeSlot (i : Nat) (unevaluated : params i = some .syntax) : Sim params acq .type (.arg i) (.operand i)
    | typeList {items items' : List Marked} : Sims params acq .type items items' →
        Sim params acq .type (.list items) (.list items')
  inductive Sims (params : Nat → Option Param) (acq : Env) : Pos → List Marked → List Marked → Prop where
    | nil (p : Pos) : Sims params acq p [] []
    | cons {p : Pos} {s t : Marked} {ss ts : List Marked} :
        Sim params acq p s t → Sims params acq p ss ts → Sims params acq p (s :: ss) (t :: ts)
end

/-! ## Corresponding terms behave the same -/

section Agreement

variable (profile : Profile) (written : List Atom) (operands : Nat → Operand)

/-- The interpreter's context with the given captured arguments. -/
abbrev ctxOf (params : Nat → Option Param) : Ctx := { profile, written, operands, params }

/-- The source's local names never hide an acquisition local. -/
def Separate (env acq : Env) : Prop := ∀ n b, acq.lookup n = some b → env.lookup n = none

/-- A source block item's result, seen with the acquisition locals behind it. -/
def extend (acq : Env) : Out (Env × Val × State) → Out (Env × Val × State)
  | .ok (e, v, s) => .ok (e ++ acq, v, s)
  | .error err => .error err

def Agrees (params : Nat → Option Param) (acq : Env) : Pos → Marked → Marked → Prop
  | .value, s, t => ∀ env, Separate env acq → ∀ st,
      value (ctxOf profile written operands fun _ => none) (env ++ acq) t st =
        value (ctxOf profile written operands params) env s st
  | .place, s, t => ∀ env, Separate env acq → ∀ st,
      place (ctxOf profile written operands fun _ => none) (env ++ acq) t st =
        place (ctxOf profile written operands params) env s st
  | .stmt, s, t => ∀ env, Separate env acq → ∀ st,
      statement (ctxOf profile written operands fun _ => none) (env ++ acq) t st =
          extend acq (statement (ctxOf profile written operands params) env s st) ∧
        ∀ e v st', statement (ctxOf profile written operands params) env s st = .ok (e, v, st') →
          Separate e acq
  | .type, s, t => typeAtom (ctxOf profile written operands params) s =
      typeAtom (ctxOf profile written operands fun _ => none) t

theorem lookup_append_fresh (env acq : Env) (n : String) (fresh : acq.lookup n = none) :
    (env ++ acq).lookup n = env.lookup n := by
  cases h : env.lookup n with
  | none => rw [lookup_append_none env acq n h, fresh]
  | some b => exact lookup_append_some env acq n b h

theorem lookup_separate {env acq : Env} (sep : Separate env acq) {n : String} {b : Binding}
    (bound : acq.lookup n = some b) : (env ++ acq).lookup n = some b := by
  rw [lookup_append_none env acq n (sep n b bound), bound]

theorem separate_cons {env acq : Env} (sep : Separate env acq) {n : String}
    (fresh : acq.lookup n = none) (b : Binding) : Separate ((n, b) :: env) acq := by
  intro m c bound
  have : (m == n) = false := by
    rw [beq_eq_false_iff_ne]; rintro rfl; rw [fresh] at bound; cases bound
  simp [List.lookup, this, sep m c bound]

theorem bind_ok {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {b : β} :
    (m >>= f) = .ok b ↔ ∃ a, m = .ok a ∧ f a = .ok b := by
  cases m <;> simp [bind, Except.bind]

/-- An expression in item position is evaluated as an expression. -/
theorem statement_expr (ctx : Ctx) (env : Env) (e : Marked) (st : State) (hs : stmtHead e = false) :
    statement ctx env e st = (do let (v, st) ← value ctx env e st; pure (env, v, st)) := by
  rw [statement.eq_10] <;> intros <;> subst_vars <;> simp [stmtHead] at hs

theorem values_agree {params : Nat → Option Param} {acq : Env} : ∀ {args args' : List Marked},
    List.Forall₂ (Agrees profile written operands params acq .value) args args' →
    ∀ env, Separate env acq → ∀ st,
      values (ctxOf profile written operands fun _ => none) (env ++ acq) args' st =
        values (ctxOf profile written operands params) env args st
  | [], [], .nil, env, _, st => by simp only [values]
  | _ :: _, _ :: _, .cons h hs, env, sep, st => by
      simp only [values]
      simp only [h env sep, values_agree hs env sep]

theorem statements_agree {params : Nat → Option Param} {acq : Env} : ∀ {items items' : List Marked},
    List.Forall₂ (Agrees profile written operands params acq .stmt) items items' →
    ∀ env, Separate env acq → ∀ st,
      statements (ctxOf profile written operands fun _ => none) (env ++ acq) items' st =
        extend acq (statements (ctxOf profile written operands params) env items st)
  | [], [], .nil, env, _, st => by simp only [statements]; rfl
  | [_], [_], .cons h .nil, env, sep, st => by simp only [statements]; exact (h env sep st).1
  | a :: _ :: _, _ :: _ :: _, .cons h (.cons h2 hs), env, sep, st => by
      simp only [statements]
      rw [(h env sep st).1]
      cases hr : statement (ctxOf profile written operands params) env a st with
      | error e => rfl
      | ok r =>
          obtain ⟨e, v, st'⟩ := r
          have rest := statements_agree (.cons h2 hs) e ((h env sep st).2 e v st' hr) st'
          simpa [extend, bind, Except.bind] using rest

theorem typeAtomMany_agree {params : Nat → Option Param} {acq : Env} : ∀ {items items' : List Marked},
    List.Forall₂ (Agrees profile written operands params acq .type) items items' →
      typeAtomMany (ctxOf profile written operands params) items =
        typeAtomMany (ctxOf profile written operands fun _ => none) items'
  | [], [], .nil => by simp only [typeAtomMany]
  | _ :: _, _ :: _, .cons h hs => by
      simp only [typeAtomMany]
      rw [show typeAtom _ _ = _ from h, typeAtomMany_agree hs]

theorem extend_bind {α : Type} (acq : Env) (m : Out α) (f : α → Out (Env × Val × State)) :
    extend acq (m >>= f) = m >>= fun a => extend acq (f a) := by
  cases m <;> rfl

/-- Every successful outcome of `m` returns the environment `env`. -/
def Keeps (env : Env) (m : Out (Env × Val × State)) : Prop :=
  ∀ e v s, m = .ok (e, v, s) → e = env

theorem keeps_pure {env : Env} {v : Val} {s : State} : Keeps env (pure (env, v, s)) := by
  intro e w t h; cases h; rfl

theorem keeps_ok {env : Env} {v : Val} {s : State} : Keeps env (.ok (env, v, s)) := keeps_pure

theorem keeps_bind {α : Type} {env : Env} {m : Out α} {f : α → Out (Env × Val × State)}
    (hf : ∀ a, Keeps env (f a)) : Keeps env (m >>= f) := by
  intro e v s h
  cases m with
  | error => cases h
  | ok a => exact hf a e v s h

theorem typeOf_agree {params : Nat → Option Param} {t t' : Marked}
    (h : typeAtom (ctxOf profile written operands params) t =
      typeAtom (ctxOf profile written operands fun _ => none) t') :
    typeOf (ctxOf profile written operands fun _ => none) t' =
      typeOf (ctxOf profile written operands params) t := by
  unfold typeOf; rw [← h]

theorem builtin_ne {f : Marked} (h : builtinCallee f = false) :
    (f = .symbol "__builtin_add_overflow" → False) ∧ (f = .symbol "__builtin_mul_overflow" → False) :=
  ⟨fun e => by subst e; simp [builtinCallee] at h, fun e => by subst e; simp [builtinCallee] at h⟩

mutual
  /-- Corresponding terms behave the same at their position. -/
  theorem sim_agrees {params : Nat → Option Param} {acq : Env} :
      {p : Pos} → {s t : Marked} → Sim params acq p s t → Agrees profile written operands params acq p s t
    | _, _, _, .constant s => fun env _ st => by simp only [value]
    | _, _, _, .localValue n fresh => fun env _ st => by
        simp only [value, lookup, lookup_append_fresh env acq n fresh]
    | _, _, _, .slotValue i x agrees => fun env sep st => by
        generalize hq : params i = q at agrees
        cases agrees with
        | code => simp only [value, hq, callerValue]
        | value v n bound => simp only [value, hq, lookup, lookup_separate sep bound]; rfl
        | place l n bound => simp only [value, place, hq, lookup, lookup_separate sep bound]; rfl
    | _, _, _, .addressOfDeref h => fun env sep st => by
        simp only [value]; exact sim_agrees h env sep st
    | _, _, _, .addressOfPlace i l n captured bound => fun env sep st => by
        simp only [value, place, captured, lookup, lookup_separate sep bound]; rfl
    | _, _, _, .addressOf h hx hy => fun env sep st => by
        rw [value.eq_7 _ _ _ _ (fun z e => hy z e), value.eq_7 _ _ _ _ (fun z e => hx z e),
          sim_agrees h env sep st]
    | _, _, _, .deref h => fun env sep st => by
        simp only [value, place, sim_agrees h env sep]
    | _, _, _, .index ha hb => fun env sep st => by
        simp only [value, place, sim_agrees ha env sep, sim_agrees hb env sep]
    | _, _, _, .unary op known h => fun env sep st => by
        rcases known with rfl | rfl <;> simp only [value, sim_agrees h env sep]
    | _, _, _, .binary op known ha hb => fun env sep st => by
        rcases known with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [value, sim_agrees ha env sep, sim_agrees hb env sep]
    | _, _, _, .assign op known hl hr => fun env sep st => by
        rcases known with rfl | rfl <;> simp only [value, sim_agrees hl env sep, sim_agrees hr env sep]
    | _, _, _, .increment hl => fun env sep st => by
        simp only [value, sim_agrees hl env sep]
    | _, _, _, .choice hc ha hb => fun env sep st => by
        simp only [value, sim_agrees hc env sep, sim_agrees ha env sep, sim_agrees hb env sep]
    | _, _, _, .castVoid h => fun env sep st => by
        simp only [value, sim_agrees h env sep]
    | _, _, _, .sizeofType h => fun env sep st => by
        have ht : typeAtom _ _ = typeAtom _ _ := sim_agrees h
        simp only [value, typeOf, ← ht]
    | _, _, _, .builtin f known hargs => fun env sep st => by
        rcases known with rfl | rfl <;>
          simp only [value, values_agree profile written operands (sims_agrees hargs) env sep]
    | _, _, _, .call hf hb hb' hargs => fun env sep st => by
        rw [value.eq_26 _ _ _ _ _ (builtin_ne hb').1 (builtin_ne hb').2,
          value.eq_26 _ _ _ _ _ (builtin_ne hb).1 (builtin_ne hb).2]
        simp only [sim_agrees hf env sep, values_agree profile written operands (sims_agrees hargs) env sep]
    | _, _, _, @Sim.block _ _ items _ hitems => fun env sep st => by
        simp only [value, statements_agree profile written operands (sims_agrees hitems) env sep]
        cases statements (ctxOf profile written operands params) env items st <;> rfl
    | _, _, _, .localPlace n fresh => fun env _ st => by
        simp only [place, lookup, lookup_append_fresh env acq n fresh]
    | _, _, _, .slotPlace i x agrees => fun env sep st => by
        generalize hq : params i = q at agrees
        cases agrees with
        | code => simp only [place, hq, callerPlace]
        | value v n bound => simp only [place, hq, lookup, lookup_separate sep bound]; rfl
        | place l n bound => simp only [place, value, hq, lookup, lookup_separate sep bound]; rfl
    | _, _, _, .derefPlace h => fun env sep st => by
        simp only [place, sim_agrees h env sep]
    | _, _, _, .indexPlace ha hb => fun env sep st => by
        simp only [place, sim_agrees ha env sep, sim_agrees hb env sep]
    | _, _, _, .staticAssert xs ys => fun env sep st =>
        ⟨by simp only [statement]; rfl, fun e v s h => by simp only [statement] at h; cases h; exact sep⟩
    | _, _, _, .typedef xs ys => fun env sep st =>
        ⟨by simp only [statement]; rfl, fun e v s h => by simp only [statement] at h; cases h; exact sep⟩
    | _, _, _, @Sim.declareValue _ _ n fresh init _ h => fun env sep st => by
        refine ⟨?_, fun e v s hr => ?_⟩
        · simp only [statement, sim_agrees h env sep]
          cases value (ctxOf profile written operands params) env init st <;> rfl
        · simp only [statement] at hr
          cases hv : value (ctxOf profile written operands params) env init st with
          | error => rw [hv] at hr; cases hr
          | ok r => rw [hv] at hr; cases hr; exact separate_cons sep fresh _
    | _, _, _, @Sim.declare _ _ n fresh t _ h => fun env sep st => by
        refine ⟨?_, fun e v s hr => ?_⟩
        · simp only [statement, typeOf_agree profile written operands (sim_agrees h)]
          cases typeOf (ctxOf profile written operands params) t <;> rfl
        · simp only [statement] at hr
          cases ht : typeOf (ctxOf profile written operands params) t with
          | error => rw [ht] at hr; cases hr
          | ok r => rw [ht] at hr; cases hr; exact separate_cons sep fresh _
    | _, _, _, @Sim.declarePointer _ _ n fresh t _ h => fun env sep st => by
        refine ⟨?_, fun e v s hr => ?_⟩
        · simp only [statement, typeOf_agree profile written operands (sim_agrees h)]
          cases typeOf (ctxOf profile written operands params) t <;> rfl
        · simp only [statement] at hr
          cases ht : typeOf (ctxOf profile written operands params) t with
          | error => rw [ht] at hr; cases hr
          | ok r => rw [ht] at hr; cases hr; exact separate_cons sep fresh _
    | _, _, _, @Sim.declareInit _ _ n fresh t _ init _ h hauto hauto' hinit => fun env sep st => by
        refine ⟨?_, fun e v s hr => ?_⟩
        · rw [statement.eq_6 _ _ _ _ _ _ hauto', statement.eq_6 _ _ _ _ _ _ hauto,
            typeOf_agree profile written operands (sim_agrees h), sim_agrees hinit env sep]
          cases typeOf (ctxOf profile written operands params) t with
          | error => rfl
          | ok ty =>
            cases value (ctxOf profile written operands params) env init st with
            | error => rfl
            | ok r =>
              obtain ⟨w, s1⟩ := r
              dsimp only [bind, Except.bind]
              cases convert profile ty w <;> rfl
        · rw [statement.eq_6 _ _ _ _ _ _ hauto] at hr
          cases ht : typeOf (ctxOf profile written operands params) t with
          | error => rw [ht] at hr; cases hr
          | ok ty =>
            rw [ht] at hr
            cases hv : value (ctxOf profile written operands params) env init st with
            | error => rw [hv] at hr; cases hr
            | ok r =>
              obtain ⟨w, s1⟩ := r
              rw [hv] at hr
              dsimp only [bind, Except.bind] at hr
              cases hc : convert profile ty w with
              | error => rw [hc] at hr; cases hr
              | ok w' => rw [hc] at hr; cases hr; exact separate_cons sep fresh _
    | _, _, _, @Sim.when _ _ c a c' a' hc ha => fun env sep st => by
        have keeps : Keeps env (statement (ctxOf profile written operands params) env
            (.list [.symbol "if", c, a]) st) := by
          rw [statement.eq_7]
          refine keeps_bind fun ⟨x, st1⟩ => keeps_bind fun b => ?_
          split
          · exact keeps_bind fun ⟨_, _, _⟩ => keeps_pure
          · exact keeps_pure
        refine ⟨?_, fun e v s hr => keeps e v s hr ▸ sep⟩
        rw [statement.eq_7, statement.eq_7, sim_agrees hc env sep st]
        cases value (ctxOf profile written operands params) env c st with
        | error => rfl
        | ok r =>
          obtain ⟨x, st1⟩ := r
          cases ht : truth x with
          | error => simp only [bind, Except.bind, ht]; rfl
          | ok b =>
            cases b
            · simp only [bind, Except.bind, ht]; rfl
            · simp only [bind, Except.bind, ht, if_true, (sim_agrees ha env sep st1).1]
              cases statement (ctxOf profile written operands params) env a st1 <;> rfl
    | _, _, _, @Sim.choose _ _ c a b c' a' b' hc ha hb => fun env sep st => by
        have keeps : Keeps env (statement (ctxOf profile written operands params) env
            (.list [.symbol "if", c, a, b]) st) := by
          rw [statement.eq_8]
          refine keeps_bind fun ⟨x, st1⟩ => keeps_bind fun v => ?_
          split
          · exact keeps_bind fun ⟨_, _, _⟩ => keeps_pure
          · exact keeps_bind fun ⟨_, _, _⟩ => keeps_pure
        refine ⟨?_, fun e v s hr => keeps e v s hr ▸ sep⟩
        rw [statement.eq_8, statement.eq_8, sim_agrees hc env sep st]
        cases value (ctxOf profile written operands params) env c st with
        | error => rfl
        | ok r =>
          obtain ⟨x, st1⟩ := r
          cases ht : truth x with
          | error => simp only [bind, Except.bind, ht]; rfl
          | ok v =>
            cases v
            · simp only [bind, Except.bind, ht, (sim_agrees hb env sep st1).1]
              cases statement (ctxOf profile written operands params) env b st1 <;> rfl
            · simp only [bind, Except.bind, ht, if_true, (sim_agrees ha env sep st1).1]
              cases statement (ctxOf profile written operands params) env a st1 <;> rfl
    | _, _, _, @Sim.blockStmt _ _ items _ hitems => fun env sep st => by
        have keeps : Keeps env (statement (ctxOf profile written operands params) env
            (.list (.symbol "block" :: items)) st) := by
          simp only [statement]
          exact keeps_bind fun ⟨_, _, _⟩ => keeps_pure
        refine ⟨?_, fun e v s hr => keeps e v s hr ▸ sep⟩
        simp only [statement, statements_agree profile written operands (sims_agrees hitems) env sep]
        cases statements (ctxOf profile written operands params) env items st <;> rfl
    | _, _, _, @Sim.expr _ _ s _ h hs ht => fun env sep st => by
        have keeps : Keeps env (statement (ctxOf profile written operands params) env s st) := by
          rw [statement_expr _ _ _ _ hs]
          exact keeps_bind fun ⟨_, _⟩ => keeps_pure
        refine ⟨?_, fun e v s hr => keeps e v s hr ▸ sep⟩
        rw [statement_expr _ _ _ _ ht, statement_expr _ _ _ _ hs, sim_agrees h env sep st]
        cases value (ctxOf profile written operands params) env s st <;> rfl
    | _, _, _, .typeSymbol s => rfl
    | _, _, _, .typeText s => rfl
    | _, _, _, .typeSlot i _ => rfl
    | _, _, _, .typeList h => by
        show typeAtom _ _ = typeAtom _ _
        simp only [typeAtom, typeAtomMany_agree profile written operands (sims_agrees h)]
  theorem sims_agrees {params : Nat → Option Param} {acq : Env} :
      {p : Pos} → {ss ts : List Marked} → Sims params acq p ss ts →
        List.Forall₂ (Agrees profile written operands params acq p) ss ts
    | _, _, _, .nil _ => .nil
    | _, _, _, .cons h hs => .cons (sim_agrees h) (sims_agrees hs)
end

end Agreement

/-! ## Admitted templates -/

/-- The operators the interpreter knows, by name. -/
inductive Op where
  | addr | deref | index | not | neg | add | eq | gt | and | or | comma | cond | cast | sizeof
  | assign | addAssign | incr | call | block | staticAssert | typedef | var | when
  deriving DecidableEq, Repr

def Op.spelling : Op → String
  | .addr => "&" | .deref => "*" | .index => "[]" | .not => "!" | .neg => "-" | .add => "+"
  | .eq => "==" | .gt => ">" | .and => "&&" | .or => "||" | .comma => "," | .cond => "?:"
  | .cast => "cast" | .sizeof => "sizeof" | .assign => "=" | .addAssign => "+=" | .incr => "++"
  | .call => "call" | .block => "block" | .staticAssert => "_Static_assert" | .typedef => "typedef"
  | .var => "var" | .when => "if"

def Op.all : List Op :=
  [.addr, .deref, .index, .not, .neg, .add, .eq, .gt, .and, .or, .comma, .cond, .cast, .sizeof,
   .assign, .addAssign, .incr, .call, .block, .staticAssert, .typedef, .var, .when]

def opOf (s : String) : Option Op := Op.all.find? (·.spelling == s)

theorem opOf_spelling {s : String} {o : Op} (h : opOf s = some o) : o.spelling = s := by
  have := List.find?_some h
  simpa using this

def slotIs (args : List Argument) (i : Nat) (c : Category) : Bool :=
  match args[i]? with
  | some a => a.category == c
  | none => false

def isSym (m : Marked) (s : String) : Bool :=
  match m with
  | .symbol t => t == s
  | _ => false

def isSymbol : Marked → Bool
  | .symbol _ => true
  | _ => false

def localOf? : Marked → Option Nat
  | .localRef j => some j
  | _ => none

def pointerLocalOf? : Marked → Option Nat
  | .list [.symbol "*", .localRef j] => some j
  | _ => none

mutual
  /-- The template fragment the proof covers, read at a position: exactly the
  constructs of the interpreter, with arguments only where their category
  makes sense, the `&` operand a place, no `&` inside a type, and declarators
  that are the template's own locals. -/
  def admittedAt (args : List Argument) (nlocals : Nat) : Pos → Marked → Bool
    | .type, .symbol s => s != "&"
    | .type, .text _ => true
    | .type, .arg i => slotIs args i .syntax
    | .type, .typeArg i => slotIs args i .syntax
    | .type, .list items => admittedMany args nlocals .type items
    | .value, .symbol _ => true
    | .value, .localRef j => decide (j < nlocals)
    | .value, .arg i => decide (i < args.length)
    | .place, .arg i => decide (i < args.length) && !slotIs args i .value
    | .place, .localRef j => decide (j < nlocals)
    | p, .list (.symbol s :: rest) =>
        match opOf s with
        | some o => admittedOp args nlocals p o rest
        | none => false
    | _, _ => false
  termination_by structural _ t => t
  def admittedOp (args : List Argument) (nlocals : Nat) : Pos → Op → List Marked → Bool
    | .value, .addr, [.list [.symbol "*", x]] =>
        !stmtHead x && !isSymbol x && admittedAt args nlocals .value x
    | .value, .addr, [x] => admittedAt args nlocals .place x
    | .value, .deref, [x] => admittedAt args nlocals .value x
    | .place, .deref, [x] => admittedAt args nlocals .value x
    | .value, .index, [a, b] => admittedAt args nlocals .value a && admittedAt args nlocals .value b
    | .place, .index, [a, b] => admittedAt args nlocals .value a && admittedAt args nlocals .value b
    | .value, .not, [x] => admittedAt args nlocals .value x
    | .value, .neg, [x] => admittedAt args nlocals .value x
    | .value, .add, [a, b] => admittedAt args nlocals .value a && admittedAt args nlocals .value b
    | .value, .eq, [a, b] => admittedAt args nlocals .value a && admittedAt args nlocals .value b
    | .value, .gt, [a, b] => admittedAt args nlocals .value a && admittedAt args nlocals .value b
    | .value, .and, [a, b] => admittedAt args nlocals .value a && admittedAt args nlocals .value b
    | .value, .or, [a, b] => admittedAt args nlocals .value a && admittedAt args nlocals .value b
    | .value, .comma, [a, b] => admittedAt args nlocals .value a && admittedAt args nlocals .value b
    | .value, .cond, [c, a, b] =>
        admittedAt args nlocals .value c && admittedAt args nlocals .value a && admittedAt args nlocals .value b
    | .value, .cast, [v, x] => isSym v "void" && admittedAt args nlocals .value x
    | .value, .sizeof, [k, t] => isSym k "type" && admittedAt args nlocals .type t
    | .value, .assign, [l, r] => admittedAt args nlocals .place l && admittedAt args nlocals .value r
    | .value, .addAssign, [l, r] => admittedAt args nlocals .place l && admittedAt args nlocals .value r
    | .value, .incr, [l] => admittedAt args nlocals .place l
    | .value, .call, f :: xs =>
        (builtinCallee f || admittedAt args nlocals .value f) && admittedMany args nlocals .value xs
    | .value, .block, [] => true
    | .value, .block, m :: ms =>
        (if stmtHead m then admittedAt args nlocals .stmt m else admittedAt args nlocals .value m) &&
          admittedOp args nlocals .value .block ms
    | .stmt, .staticAssert, _ => true
    | .stmt, .typedef, _ => true
    | .stmt, .var, [t, d] =>
        (match localOf? d, pointerLocalOf? d with
         | some j, _ => decide (j < nlocals)
         | none, some j => decide (j < nlocals)
         | none, none => false) && admittedAt args nlocals .type t
    | .stmt, .var, [t, d, init] =>
        (match localOf? d with
         | some j => decide (j < nlocals)
         | none => false) &&
          (isSym t "__auto_type" || admittedAt args nlocals .type t) && admittedAt args nlocals .value init
    | .stmt, .when, [c, a] =>
        admittedAt args nlocals .value c &&
          (if stmtHead a then admittedAt args nlocals .stmt a else admittedAt args nlocals .value a)
    | .stmt, .when, [c, a, b] =>
        admittedAt args nlocals .value c &&
          (if stmtHead a then admittedAt args nlocals .stmt a else admittedAt args nlocals .value a) &&
          (if stmtHead b then admittedAt args nlocals .stmt b else admittedAt args nlocals .value b)
    | .stmt, .block, [] => true
    | .stmt, .block, m :: ms =>
        (if stmtHead m then admittedAt args nlocals .stmt m else admittedAt args nlocals .value m) &&
          admittedOp args nlocals .stmt .block ms
    | _, _, _ => false
  termination_by structural _ _ rest => rest
  def admittedMany (args : List Argument) (nlocals : Nat) : Pos → List Marked → Bool
    | _, [] => true
    | p, m :: rest => admittedAt args nlocals p m && admittedMany args nlocals p rest
  termination_by structural _ items => items
end

/-- Block items: statements as statements, anything else as an expression. -/
def admittedItems (args : List Argument) (nlocals : Nat) (items : List Marked) : Bool :=
  admittedOp args nlocals .stmt .block items

/-- The rules the theorem covers: an admitted body, in item position for a
statement and in value position for an expression's result, and a nonempty
block when the body is a block. -/
def admittedRule (rule : Rule) : Bool :=
  let args := rule.arguments
  let n := rule.locals.length
  match rule.body with
  | .list (.symbol "block" :: items) =>
      match items.reverse with
      | [] => false
      | last :: earlier =>
          admittedItems args n earlier.reverse &&
            (if rule.expression then admittedAt args n .value last
             else admittedItems args n [last])
  | body =>
      if rule.expression then admittedAt args n .value body
      else admittedItems args n [body]

/-! ## The lowering of an admitted template corresponds to its source -/

/-- The source template with captured arguments in place. -/
abbrev src (L : Nat → String) (t : Marked) : Marked := instantiate (fun i => .arg i) L t

/-- The exported template: acquisition locals in place, `&*` collapsed. -/
abbrev tgt (σT : Nat → Marked) (L : Nat → String) (t : Marked) : Marked :=
  addressOfObject (instantiate σT L t)

def isBlockForm : Marked → Bool
  | .list (.symbol "block" :: _) => true
  | _ => false

/-- The interpreter dispatches the same way on both terms. -/
structure HeadKept (t t' : Marked) : Prop where
  stmt : stmtHead t' = stmtHead t
  block : isBlockForm t' = isBlockForm t
  symbol : ∀ s, t' = .symbol s ↔ t = .symbol s

theorem instantiateMany_eq_map (σ : Nat → Marked) (L : Nat → String) :
    ∀ items : List Marked, instantiateMany σ L items = items.map (instantiate σ L)
  | [] => rfl
  | m :: rest => by simp only [instantiateMany, List.map, instantiateMany_eq_map σ L rest]

theorem addressOfObjectMany_eq_map : ∀ items : List Marked,
    addressOfObjectMany items = items.map addressOfObject
  | [] => rfl
  | m :: rest => by simp only [addressOfObjectMany, List.map, addressOfObjectMany_eq_map rest]

theorem src_list (L : Nat → String) (items : List Marked) :
    src L (.list items) = .list (items.map (src L)) := by
  simp only [src, instantiate, instantiateMany_eq_map]

theorem tgt_list (σT : Nat → Marked) (L : Nat → String) (items : List Marked) :
    tgt σT L (.list items) = addressOfObjectNode (.list (items.map (tgt σT L))) := by
  simp only [tgt, instantiate, addressOfObject, instantiateMany_eq_map, addressOfObjectMany_eq_map,
    List.map_map]
  rfl

theorem tgt_symbol (σT : Nat → Marked) (L : Nat → String) (s : String) :
    tgt σT L (.symbol s) = .symbol s := rfl

theorem tgt_head (σT : Nat → Marked) (L : Nat → String) {s : String} (h : s ≠ "&")
    (rest : List Marked) :
    tgt σT L (.list (.symbol s :: rest)) = .list (.symbol s :: rest.map (tgt σT L)) := by
  rw [tgt_list]
  simp only [List.map, tgt_symbol]
  unfold addressOfObjectNode
  split
  · rename_i heq; simp at heq; exact absurd heq.1 h
  · rfl

theorem headKept_op {s : String} (rest rest' : List Marked) :
    HeadKept (.list (.symbol s :: rest)) (.list (.symbol s :: rest')) :=
  ⟨by simp [stmtHead], by by_cases hs : s = "block" <;> simp [isBlockForm, hs], fun _ => by simp⟩

theorem src_symbol_iff (L : Nat → String) (t : Marked) (s : String) :
    src L t = .symbol s ↔ t = .symbol s := by
  cases t <;> simp [src, instantiate]

theorem stmtHead_src (L : Nat → String) (t : Marked) : stmtHead (src L t) = stmtHead t := by
  cases t with
  | list items =>
      rw [src_list]
      rcases items with _ | ⟨hd, rest⟩
      · rfl
      · cases hd <;> simp [stmtHead, src, instantiate]
  | _ => simp [stmtHead, src, instantiate]

theorem builtinCallee_src (L : Nat → String) (t : Marked) :
    builtinCallee (src L t) = builtinCallee t := by
  cases t <;> simp [builtinCallee, src, instantiate]

theorem isSym_eq {m : Marked} {s : String} (h : isSym m s = true) : m = .symbol s := by
  cases m <;> simp_all [isSym]

theorem isSym_ne {m : Marked} {s : String} (h : isSym m s = false) : m ≠ .symbol s := by
  rintro rfl; simp [isSym] at h

theorem localOf?_eq {m : Marked} {j : Nat} (h : localOf? m = some j) : m = .localRef j := by
  cases m <;> simp_all [localOf?]

theorem pointerLocalOf?_eq {m : Marked} {j : Nat} (h : pointerLocalOf? m = some j) :
    m = .list [.symbol "*", .localRef j] := by
  unfold pointerLocalOf? at h
  split at h
  · cases h; rfl
  · cases h

theorem builtinCallee_eq {f : Marked} (h : builtinCallee f = true) :
    f = .symbol "__builtin_add_overflow" ∨ f = .symbol "__builtin_mul_overflow" := by
  cases f <;> simp_all [builtinCallee]

theorem sizeOf_mem_lt {x hd : Marked} {rest : List Marked} (h : x ∈ rest) :
    sizeOf x < sizeOf (Marked.list (hd :: rest)) := by
  have := List.sizeOf_lt_of_mem h
  simp only [Marked.list.sizeOf_spec, List.cons.sizeOf_spec]
  omega

theorem sizeOf_item_lt {x : Marked} {items : List Marked} (h : x ∈ items) :
    sizeOf x < sizeOf (Marked.list items) := by
  have := List.sizeOf_lt_of_mem h
  simp only [Marked.list.sizeOf_spec]
  omega

theorem src_symbol (L : Nat → String) (s : String) : src L (.symbol s) = .symbol s := rfl

theorem HeadKept.refl (t : Marked) : HeadKept t t := ⟨rfl, rfl, fun _ => Iff.rfl⟩

/-- Neither term is a symbol, a statement or a block. -/
theorem headKept_plain {t t' : Marked} (hs : stmtHead t = false) (hs' : stmtHead t' = false)
    (hb : isBlockForm t = false) (hb' : isBlockForm t' = false)
    (hy : ∀ s, t ≠ .symbol s) (hy' : ∀ s, t' ≠ .symbol s) : HeadKept t t' :=
  ⟨by rw [hs, hs'], by rw [hb, hb'], fun s => ⟨fun h => absurd h (hy' s), fun h => absurd h (hy s)⟩⟩

theorem headKept_cons {a a' : Marked} (rest rest' : List Marked) (ha : HeadKept a a') :
    HeadKept (.list (a :: rest)) (.list (a' :: rest')) := by
  by_cases hs : ∃ s, a = .symbol s
  · obtain ⟨s, rfl⟩ := hs
    rw [(ha.symbol s).mpr rfl]
    exact headKept_op _ _
  · have hs' : ∀ s, a' ≠ .symbol s := fun s h => hs ⟨s, (ha.symbol s).mp h⟩
    have plain : ∀ (b : Marked) (r : List Marked), (∀ s, b ≠ .symbol s) →
        stmtHead (.list (b :: r)) = false ∧ isBlockForm (.list (b :: r)) = false := by
      intro b r hb
      cases b with
      | symbol s => exact absurd rfl (hb s)
      | _ => exact ⟨rfl, rfl⟩
    exact headKept_plain (plain a rest fun s h => hs ⟨s, h⟩).1 (plain a' rest' hs').1
      (plain a rest fun s h => hs ⟨s, h⟩).2 (plain a' rest' hs').2 (fun _ h => by cases h) (fun _ h => by cases h)

theorem slotIs_lt {args : List Argument} {i : Nat} {c : Category} (h : slotIs args i c = true) :
    i < args.length := by
  unfold slotIs at h
  cases hi : args[i]? with
  | none => rw [hi] at h; cases h
  | some a => exact (List.getElem?_eq_some_iff.mp hi).1

theorem tgt_slot {acq : Env} {i : Nat} {q : Option Param} {x : Marked} (h : SlotAgrees acq i q x) :
    addressOfObject x = x := by
  cases h <;> rfl

theorem headKept_slot {acq : Env} {i : Nat} {q : Option Param} {x : Marked} (h : SlotAgrees acq i q x)
    (t : Marked) (ht : stmtHead t = false) (hb : isBlockForm t = false) (hy : ∀ s, t ≠ .symbol s) :
    HeadKept t x := by
  cases h <;> exact headKept_plain ht rfl hb rfl hy (fun _ h => by cases h)

/-- A place that is a list is an indirection or a subscript. -/
theorem place_list_shape {args : List Argument} {nlocals : Nat} {items : List Marked}
    (h : admittedAt args nlocals .place (.list items) = true) :
    (∃ y, items = [.symbol "*", y]) ∨ (∃ a b, items = [.symbol "[]", a, b]) := by
  rcases items with _ | ⟨hd, rest⟩
  · simp [admittedAt] at h
  · cases hd with
    | symbol s =>
        cases hop : opOf s with
        | none => simp [admittedAt, hop] at h
        | some o =>
            have hs := opOf_spelling hop
            subst hs
            rw [admittedAt.eq_11 args nlocals .place _ rest (by simp), hop] at h
            simp only at h
            cases o <;> rcases rest with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp [admittedOp] at h
            · exact .inl ⟨a, rfl⟩
            · exact .inr ⟨a, b, rfl⟩
    | _ => simp [admittedAt] at h

/-- What the lowering's slot map and local names satisfy. -/
structure Lowering (args : List Argument) (nlocals : Nat) (params : Nat → Option Param) (acq : Env)
    (σT : Nat → Marked) (L : Nat → String) : Prop where
  slots : ∀ i, i < args.length → SlotAgrees acq i (params i) (σT i)
  codes : ∀ i, slotIs args i .syntax = true → params i = some .syntax
  fresh : ∀ j, j < nlocals → acq.lookup (L j) = none

section Lowered

variable {args : List Argument} {nlocals : Nat} {params : Nat → Option Param} {acq : Env}
  {σT : Nat → Marked} {L : Nat → String}

theorem sims_of {q : Pos} : ∀ (xs : List Marked),
    (∀ x ∈ xs, admittedAt args nlocals q x = true → Sim params acq q (src L x) (tgt σT L x)) →
      admittedMany args nlocals q xs = true → Sims params acq q (xs.map (src L)) (xs.map (tgt σT L))
  | [], _, _ => .nil q
  | x :: xs, h, hm => by
      simp only [admittedMany, Bool.and_eq_true] at hm
      exact .cons (h x List.mem_cons_self hm.1)
        (sims_of xs (fun y hy => h y (List.mem_cons_of_mem _ hy)) hm.2)

theorem item_sim {x : Marked}
    (h : ∀ p, admittedAt args nlocals p x = true →
      Sim params acq p (src L x) (tgt σT L x) ∧ HeadKept x (tgt σT L x))
    (hx : (if stmtHead x then admittedAt args nlocals .stmt x else admittedAt args nlocals .value x) = true) :
    Sim params acq .stmt (src L x) (tgt σT L x) := by
  by_cases hs : stmtHead x = true
  · rw [if_pos hs] at hx; exact (h .stmt hx).1
  · rw [if_neg hs] at hx
    have hs' : stmtHead x = false := by simpa using hs
    obtain ⟨hsim, hk⟩ := h .value hx
    exact .expr hsim (by rw [stmtHead_src]; exact hs') (by rw [hk.stmt]; exact hs')

theorem items_of {q : Pos} (hq : q = .value ∨ q = .stmt) : ∀ (xs : List Marked),
    (∀ x ∈ xs, ∀ p, admittedAt args nlocals p x = true →
      Sim params acq p (src L x) (tgt σT L x) ∧ HeadKept x (tgt σT L x)) →
      admittedOp args nlocals q .block xs = true →
        Sims params acq .stmt (xs.map (src L)) (xs.map (tgt σT L))
  | [], _, _ => .nil _
  | x :: xs, h, hm => by
      have hm' : (if stmtHead x then admittedAt args nlocals .stmt x else admittedAt args nlocals .value x) = true ∧
          admittedOp args nlocals q .block xs = true := by
        rcases hq with rfl | rfl <;> simpa [admittedOp] using hm
      exact .cons (item_sim (h x List.mem_cons_self) hm'.1)
        (items_of hq xs (fun y hy => h y (List.mem_cons_of_mem _ hy)) hm'.2)

theorem isBlockForm_of_stmtHead {t : Marked} (h : stmtHead t = false) : isBlockForm t = false := by
  unfold isBlockForm; split
  · simp [stmtHead] at h
  · rfl

theorem builtinCallee_tgt {f f' : Marked} (hk : HeadKept f f') : builtinCallee f' = builtinCallee f := by
  by_cases hs : ∃ s, f = .symbol s
  · obtain ⟨s, rfl⟩ := hs
    rw [(hk.symbol s).mpr rfl]
  · have hs' : ∀ s, f' ≠ .symbol s := fun s h => hs ⟨s, (hk.symbol s).mp h⟩
    have plain : ∀ m : Marked, (∀ s, m ≠ .symbol s) → builtinCallee m = false := by
      intro m hm; cases m with
      | symbol s => exact absurd rfl (hm s)
      | _ => rfl
    rw [plain f' hs', plain f fun s h => hs ⟨s, h⟩]

/-- `&` of an argument: the address of a captured place is the pointer the
acquisition local holds; of caller code it is the caller's place. -/
theorem addr_slot {i : Nat} (agrees : SlotAgrees acq i (params i) (σT i)) :
    Sim params acq .value (.list [.symbol "&", .arg i]) (addressOfObjectNode (.list [.symbol "&", σT i])) ∧
      HeadKept (.list [.symbol "&", .arg i]) (addressOfObjectNode (.list [.symbol "&", σT i])) := by
  have h := agrees
  generalize hz : σT i = z at h ⊢
  generalize hq : params i = q at h
  cases h with
  | code =>
      exact ⟨.addressOf (.slotPlace i _ (hz ▸ agrees)) (fun _ h => by cases h) (fun _ h => by cases h),
        headKept_op _ _⟩
  | value v n bound =>
      exact ⟨.addressOf (.slotPlace i _ (hz ▸ agrees)) (fun _ h => by cases h) (fun _ h => by cases h),
        headKept_op _ _⟩
  | place l n bound =>
      exact ⟨.addressOfPlace i l n hq bound,
        headKept_plain rfl rfl rfl rfl (fun _ h => by cases h) (fun _ h => by cases h)⟩

theorem lower_op (low : Lowering args nlocals params acq σT L) (o : Op) (rest : List Marked)
    (ih : ∀ u, sizeOf u < sizeOf (Marked.list (.symbol o.spelling :: rest)) → ∀ p,
      admittedAt args nlocals p u = true → Sim params acq p (src L u) (tgt σT L u) ∧ HeadKept u (tgt σT L u))
    (p : Pos) (hp : admittedOp args nlocals p o rest = true) :
    Sim params acq p (src L (.list (.symbol o.spelling :: rest))) (tgt σT L (.list (.symbol o.spelling :: rest))) ∧
      HeadKept (.list (.symbol o.spelling :: rest)) (tgt σT L (.list (.symbol o.spelling :: rest))) := by
  have mem : ∀ x, x ∈ rest → ∀ q, admittedAt args nlocals q x = true →
      Sim params acq q (src L x) (tgt σT L x) ∧ HeadKept x (tgt σT L x) :=
    fun x hx => ih x (sizeOf_mem_lt hx)
  have keep : o ≠ .addr →
      tgt σT L (.list (.symbol o.spelling :: rest)) = .list (.symbol o.spelling :: rest.map (tgt σT L)) := by
    intro ho; apply tgt_head; cases o <;> simp_all [Op.spelling]
  rw [src_list]
  cases o
  case addr =>
    cases p <;> rcases rest with _ | ⟨x, _ | ⟨b, rest⟩⟩ <;> try simp [admittedOp] at hp
    simp only [Op.spelling, List.map, src_symbol]
    by_cases hx : ∃ y, x = .list [.symbol "*", y]
    · obtain ⟨y, rfl⟩ := hx
      simp only [admittedOp, Bool.and_eq_true, Bool.not_eq_true'] at hp
      obtain ⟨⟨hs, hsym⟩, hy⟩ := hp
      have hlt : sizeOf y < sizeOf (Marked.list [.symbol "&", .list [.symbol "*", y]]) := by
        have h1 := sizeOf_item_lt (x := y) (items := [.symbol "*", y]) (by simp)
        have h2 := sizeOf_item_lt (x := .list [.symbol "*", y])
          (items := [.symbol "&", .list [.symbol "*", y]]) (by simp)
        omega
      obtain ⟨hsim, hk⟩ := ih y hlt .value hy
      have htgt : tgt σT L (.list [.symbol "&", .list [.symbol "*", y]]) = tgt σT L y := by
        rw [tgt_list]; simp only [List.map, tgt_symbol]
        rw [tgt_head _ _ (by decide)]; simp only [List.map]; rfl
      rw [htgt]
      refine ⟨.addressOfDeref hsim, ⟨?_, ?_, fun s => ?_⟩⟩
      · rw [hk.stmt, hs]; rfl
      · rw [hk.block, isBlockForm_of_stmtHead hs]; rfl
      · rw [hk.symbol s]
        constructor
        · rintro rfl; simp [isSymbol] at hsym
        · intro h; cases h
    · have hx' : ∀ y, x ≠ .list [.symbol "*", y] := fun y h => hx ⟨y, h⟩
      have hpl : admittedAt args nlocals .place x = true := by simpa [admittedOp, hx'] using hp
      cases x with
      | arg i =>
          have hi : i < args.length := by simp [admittedAt] at hpl; exact hpl.1
          have agrees := low.slots i hi
          have htgt : tgt σT L (.list [.symbol "&", .arg i]) =
              addressOfObjectNode (.list [.symbol "&", σT i]) := by
            rw [tgt_list]; simp only [List.map, tgt_symbol]
            rw [show tgt σT L (.arg i) = σT i from tgt_slot agrees]
          rw [htgt]
          exact addr_slot agrees
      | localRef j =>
          have hj : j < nlocals := by simpa [admittedAt] using hpl
          exact ⟨.addressOf (.localPlace (L j) (low.fresh j hj)) (fun _ h => by cases h)
            (fun _ h => by cases h), headKept_op _ _⟩
      | list items =>
          rcases place_list_shape hpl with ⟨y, rfl⟩ | ⟨a, b, rfl⟩
          · exact absurd rfl (hx' y)
          · obtain ⟨hsim, -⟩ := mem _ (by simp) .place hpl
            have hx : tgt σT L (.list [.symbol "[]", a, b]) = .list [.symbol "[]", tgt σT L a, tgt σT L b] := by
              rw [tgt_head _ _ (by decide)]; rfl
            have htgt : tgt σT L (.list [.symbol "&", .list [.symbol "[]", a, b]]) =
                .list [.symbol "&", .list [.symbol "[]", tgt σT L a, tgt σT L b]] := by
              rw [tgt_list]; simp only [List.map, tgt_symbol]; rw [hx]; rfl
            rw [htgt]
            rw [hx] at hsim
            exact ⟨.addressOf hsim (fun _ h => by simp [src_list] at h) (fun _ h => by simp at h),
              headKept_op _ _⟩
      | _ => simp [admittedAt] at hpl
  all_goals rw [keep (by decide)]
  all_goals simp only [Op.spelling, List.map, src_symbol]
  case deref =>
    cases p <;> rcases rest with _ | ⟨x, _ | ⟨b, rest⟩⟩ <;> simp [admittedOp] at hp
    · exact ⟨.deref (mem x (by simp) _ hp).1, headKept_op _ _⟩
    · exact ⟨.derefPlace (mem x (by simp) _ hp).1, headKept_op _ _⟩
  case index =>
    cases p <;> rcases rest with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp [admittedOp] at hp
    · exact ⟨.index (mem a (by simp) _ hp.1).1 (mem b (by simp) _ hp.2).1, headKept_op _ _⟩
    · exact ⟨.indexPlace (mem a (by simp) _ hp.1).1 (mem b (by simp) _ hp.2).1, headKept_op _ _⟩
  case not =>
    cases p <;> rcases rest with _ | ⟨x, _ | ⟨b, rest⟩⟩ <;> simp [admittedOp] at hp
    exact ⟨.unary "!" (by simp) (mem x (by simp) _ hp).1, headKept_op _ _⟩
  case neg =>
    cases p <;> rcases rest with _ | ⟨x, _ | ⟨b, rest⟩⟩ <;> simp [admittedOp] at hp
    exact ⟨.unary "-" (by simp) (mem x (by simp) _ hp).1, headKept_op _ _⟩
  case add =>
    cases p <;> rcases rest with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp [admittedOp] at hp
    exact ⟨.binary "+" (by simp) (mem a (by simp) _ hp.1).1 (mem b (by simp) _ hp.2).1, headKept_op _ _⟩
  case eq =>
    cases p <;> rcases rest with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp [admittedOp] at hp
    exact ⟨.binary "==" (by simp) (mem a (by simp) _ hp.1).1 (mem b (by simp) _ hp.2).1, headKept_op _ _⟩
  case gt =>
    cases p <;> rcases rest with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp [admittedOp] at hp
    exact ⟨.binary ">" (by simp) (mem a (by simp) _ hp.1).1 (mem b (by simp) _ hp.2).1, headKept_op _ _⟩
  case and =>
    cases p <;> rcases rest with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp [admittedOp] at hp
    exact ⟨.binary "&&" (by simp) (mem a (by simp) _ hp.1).1 (mem b (by simp) _ hp.2).1, headKept_op _ _⟩
  case or =>
    cases p <;> rcases rest with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp [admittedOp] at hp
    exact ⟨.binary "||" (by simp) (mem a (by simp) _ hp.1).1 (mem b (by simp) _ hp.2).1, headKept_op _ _⟩
  case comma =>
    cases p <;> rcases rest with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp [admittedOp] at hp
    exact ⟨.binary "," (by simp) (mem a (by simp) _ hp.1).1 (mem b (by simp) _ hp.2).1, headKept_op _ _⟩
  case cond =>
    cases p <;> rcases rest with _ | ⟨c, _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩⟩ <;> simp [admittedOp] at hp
    exact ⟨.choice (mem c (by simp) _ hp.1.1).1 (mem a (by simp) _ hp.1.2).1 (mem b (by simp) _ hp.2).1,
      headKept_op _ _⟩
  case cast =>
    cases p <;> rcases rest with _ | ⟨v, _ | ⟨x, _ | ⟨c, rest⟩⟩⟩ <;> simp [admittedOp] at hp
    obtain ⟨hv, hx⟩ := hp
    obtain rfl := isSym_eq hv
    exact ⟨.castVoid (mem x (by simp) _ hx).1, headKept_op _ _⟩
  case sizeof =>
    cases p <;> rcases rest with _ | ⟨k, _ | ⟨x, _ | ⟨c, rest⟩⟩⟩ <;> simp [admittedOp] at hp
    obtain ⟨hk, hx⟩ := hp
    obtain rfl := isSym_eq hk
    exact ⟨.sizeofType (mem x (by simp) _ hx).1, headKept_op _ _⟩
  case assign =>
    cases p <;> rcases rest with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp [admittedOp] at hp
    exact ⟨.assign "=" (by simp) (mem a (by simp) _ hp.1).1 (mem b (by simp) _ hp.2).1, headKept_op _ _⟩
  case addAssign =>
    cases p <;> rcases rest with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp [admittedOp] at hp
    exact ⟨.assign "+=" (by simp) (mem a (by simp) _ hp.1).1 (mem b (by simp) _ hp.2).1, headKept_op _ _⟩
  case incr =>
    cases p <;> rcases rest with _ | ⟨x, _ | ⟨b, rest⟩⟩ <;> simp [admittedOp] at hp
    exact ⟨.increment (mem x (by simp) _ hp).1, headKept_op _ _⟩
  case call =>
    cases p <;> rcases rest with _ | ⟨f, xs⟩ <;> try (simp [admittedOp] at hp; done)
    simp only [admittedOp, Bool.and_eq_true, Bool.or_eq_true] at hp
    obtain ⟨hf, hxs⟩ := hp
    have args' := sims_of xs (fun x hx h => (mem x (by simp [hx]) _ h).1) hxs
    by_cases hb : builtinCallee f = true
    · rcases builtinCallee_eq hb with rfl | rfl
      · exact ⟨.builtin "__builtin_add_overflow" (by simp) args', headKept_op _ _⟩
      · exact ⟨.builtin "__builtin_mul_overflow" (by simp) args', headKept_op _ _⟩
    · have hb' : builtinCallee f = false := by simpa using hb
      have hfa : admittedAt args nlocals .value f = true := by simpa [hb'] using hf
      obtain ⟨hsim, hk⟩ := mem f (by simp) _ hfa
      exact ⟨.call hsim (by rw [builtinCallee_src]; exact hb') (by rw [builtinCallee_tgt hk]; exact hb')
        args', headKept_op _ _⟩
  case block =>
    cases p
    · exact ⟨.block (items_of (.inl rfl) rest mem hp), headKept_op _ _⟩
    · simp [admittedOp] at hp
    · exact ⟨.blockStmt (items_of (.inr rfl) rest mem hp), headKept_op _ _⟩
    · simp [admittedOp] at hp
  case staticAssert =>
    cases p <;> simp [admittedOp] at hp
    exact ⟨.staticAssert _ _, headKept_op _ _⟩
  case typedef =>
    cases p <;> simp [admittedOp] at hp
    exact ⟨.typedef _ _, headKept_op _ _⟩
  case var =>
    cases p <;> rcases rest with _ | ⟨t, _ | ⟨d, _ | ⟨init, _ | ⟨e, rest⟩⟩⟩⟩ <;>
      try (simp [admittedOp] at hp; done)
    · simp only [admittedOp, Bool.and_eq_true] at hp
      obtain ⟨hd, ht⟩ := hp
      obtain ⟨hsim, -⟩ := mem t (by simp) _ ht
      cases hl : localOf? d with
      | some j =>
          rw [hl] at hd
          obtain rfl := localOf?_eq hl
          exact ⟨.declare (L j) (low.fresh j (by simpa using hd)) hsim, headKept_op _ _⟩
      | none =>
          rw [hl] at hd
          cases hpl : pointerLocalOf? d with
          | none => rw [hpl] at hd; cases hd
          | some j =>
              rw [hpl] at hd
              obtain rfl := pointerLocalOf?_eq hpl
              have hdt : tgt σT L (.list [.symbol "*", .localRef j]) = .list [.symbol "*", .name (L j)] := by
                rw [tgt_head _ _ (by decide)]; rfl
              simp only [List.map]
              rw [hdt]
              exact ⟨.declarePointer (L j) (low.fresh j (by simpa using hd)) hsim, headKept_op _ _⟩
    · simp only [admittedOp, Bool.and_eq_true, Bool.or_eq_true] at hp
      obtain ⟨⟨hd, ht⟩, hi⟩ := hp
      obtain ⟨hinit, -⟩ := mem init (by simp) _ hi
      cases hl : localOf? d with
      | none => rw [hl] at hd; cases hd
      | some j =>
          rw [hl] at hd
          obtain rfl := localOf?_eq hl
          have hfresh := low.fresh j (by simpa using hd)
          by_cases ha : isSym t "__auto_type" = true
          · obtain rfl := isSym_eq ha
            exact ⟨.declareValue (L j) hfresh hinit, headKept_op _ _⟩
          · have ha' : isSym t "__auto_type" = false := by simpa using ha
            have htt : admittedAt args nlocals .type t = true := by simpa [ha'] using ht
            obtain ⟨hsim, hk⟩ := mem t (by simp) _ htt
            have hne := isSym_ne ha'
            exact ⟨.declareInit (L j) hfresh hsim (fun h => hne ((src_symbol_iff L t _).mp h))
              (fun h => hne ((hk.symbol _).mp h)) hinit, headKept_op _ _⟩
  case when =>
    cases p <;> rcases rest with _ | ⟨c, _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩⟩ <;>
      try (simp [admittedOp] at hp; done)
    · simp only [admittedOp, Bool.and_eq_true] at hp
      exact ⟨.when (mem c (by simp) _ hp.1).1 (item_sim (mem a (by simp)) hp.2), headKept_op _ _⟩
    · simp only [admittedOp, Bool.and_eq_true] at hp
      exact ⟨.choose (mem c (by simp) _ hp.1.1).1 (item_sim (mem a (by simp)) hp.1.2)
        (item_sim (mem b (by simp)) hp.2), headKept_op _ _⟩

/-- Lowering an admitted template gives the corresponding exported term. -/
theorem lower_sim (low : Lowering args nlocals params acq σT L) :
    ∀ (n : Nat) (t : Marked), sizeOf t < n → ∀ p, admittedAt args nlocals p t = true →
      Sim params acq p (src L t) (tgt σT L t) ∧ HeadKept t (tgt σT L t)
  | 0, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, t, hn, p, hp => by
    have ih : ∀ u, sizeOf u < sizeOf t → ∀ p, admittedAt args nlocals p u = true →
        Sim params acq p (src L u) (tgt σT L u) ∧ HeadKept u (tgt σT L u) :=
      fun u hu => lower_sim low n u (by omega)
    have plainLeaf : ∀ m : Marked, stmtHead m = false → isBlockForm m = false → (∀ s, m ≠ .symbol s) →
        ∀ m', stmtHead m' = false → isBlockForm m' = false → (∀ s, m' ≠ .symbol s) → HeadKept m m' :=
      fun m h1 h2 h3 m' h1' h2' h3' => headKept_plain h1 h1' h2 h2' h3 h3'
    cases t with
    | symbol s =>
        cases p
        case value => exact ⟨.constant s, .refl _⟩
        case type => exact ⟨.typeSymbol s, .refl _⟩
        all_goals simp [admittedAt] at hp
    | text s =>
        cases p
        case type => exact ⟨.typeText s, .refl _⟩
        all_goals simp [admittedAt] at hp
    | arg i =>
        cases p
        case value =>
          have hi : i < args.length := by simpa [admittedAt] using hp
          have agrees := low.slots i hi
          rw [show tgt σT L (.arg i) = σT i from tgt_slot agrees]
          exact ⟨.slotValue i _ agrees, headKept_slot agrees _ rfl rfl (fun _ h => by cases h)⟩
        case place =>
          have hi : i < args.length := by simp [admittedAt] at hp; exact hp.1
          have agrees := low.slots i hi
          rw [show tgt σT L (.arg i) = σT i from tgt_slot agrees]
          exact ⟨.slotPlace i _ agrees, headKept_slot agrees _ rfl rfl (fun _ h => by cases h)⟩
        case type =>
          have hs : slotIs args i .syntax = true := by simpa [admittedAt] using hp
          have hc := low.codes i hs
          have agrees := low.slots i (slotIs_lt hs)
          have hz : σT i = .operand i := by
            have h := agrees
            rw [hc] at h
            generalize hz : σT i = z at h
            cases h; rfl
          rw [show tgt σT L (.arg i) = σT i from tgt_slot agrees, hz]
          exact ⟨.typeSlot i hc, plainLeaf _ rfl rfl (fun _ h => by cases h) _ rfl rfl (fun _ h => by cases h)⟩
        all_goals simp [admittedAt] at hp
    | typeArg i =>
        cases p
        case type =>
          have hs : slotIs args i .syntax = true := by simpa [admittedAt] using hp
          have hc := low.codes i hs
          have agrees := low.slots i (slotIs_lt hs)
          have hz : σT i = .operand i := by
            have h := agrees
            rw [hc] at h
            generalize hz : σT i = z at h
            cases h; rfl
          rw [show tgt σT L (.typeArg i) = σT i from tgt_slot agrees, hz]
          exact ⟨.typeSlot i hc, plainLeaf _ rfl rfl (fun _ h => by cases h) _ rfl rfl (fun _ h => by cases h)⟩
        all_goals simp [admittedAt] at hp
    | localRef j =>
        cases p
        case value =>
          have hj : j < nlocals := by simpa [admittedAt] using hp
          exact ⟨.localValue (L j) (low.fresh j hj),
            plainLeaf _ rfl rfl (fun _ h => by cases h) _ rfl rfl (fun _ h => by cases h)⟩
        case place =>
          have hj : j < nlocals := by simpa [admittedAt] using hp
          exact ⟨.localPlace (L j) (low.fresh j hj),
            plainLeaf _ rfl rfl (fun _ h => by cases h) _ rfl rfl (fun _ h => by cases h)⟩
        all_goals simp [admittedAt] at hp
    | list items =>
        have hall : ∀ x ∈ items, ∀ q, admittedAt args nlocals q x = true →
            Sim params acq q (src L x) (tgt σT L x) ∧ HeadKept x (tgt σT L x) :=
          fun x hx => ih x (sizeOf_item_lt hx)
        have nonType : ∀ q : Pos, q ≠ .type → admittedAt args nlocals q (.list items) = true →
            Sim params acq q (src L (.list items)) (tgt σT L (.list items)) ∧
              HeadKept (.list items) (tgt σT L (.list items)) := by
          intro q hq hq'
          rcases items with _ | ⟨hd, rest⟩
          · cases q <;> simp [admittedAt] at hq'
            exact absurd rfl hq
          · cases hd with
            | symbol s =>
                rw [admittedAt.eq_11 args nlocals q s rest hq] at hq'
                cases hop : opOf s with
                | none => rw [hop] at hq'; cases hq'
                | some o =>
                    rw [hop] at hq'
                    have hs := opOf_spelling hop
                    subst hs
                    exact lower_op low o rest ih q hq'
            | _ =>
                cases q <;> simp [admittedAt] at hq'
                exact absurd rfl hq
        cases p
        case value => exact nonType .value (by simp) hp
        case place => exact nonType .place (by simp) hp
        case stmt => exact nonType .stmt (by simp) hp
        case type =>
          have hm : admittedMany args nlocals .type items = true := by simpa [admittedAt] using hp
          have hsims := sims_of items (fun x hx h => (hall x hx .type h).1) hm
          have hnode : tgt σT L (.list items) = .list (items.map (tgt σT L)) := by
            rw [tgt_list]
            unfold addressOfObjectNode
            split
            · rename_i x heq
              rcases items with _ | ⟨a, _ | ⟨b, _ | ⟨c, _⟩⟩⟩ <;> simp at heq
              have ha : admittedAt args nlocals .type a = true := by
                simp only [admittedMany, Bool.and_eq_true] at hm; exact hm.1
              have := ((hall a (by simp) .type ha).2.symbol "&").mp heq.1
              subst this
              simp [admittedAt] at ha
            · rfl
          rw [src_list, hnode]
          refine ⟨.typeList hsims, ?_⟩
          rcases items with _ | ⟨a, rest⟩
          · exact .refl _
          · have ha : admittedAt args nlocals .type a = true := by
              simp only [admittedMany, Bool.and_eq_true] at hm; exact hm.1
            exact headKept_cons _ _ (hall a (by simp) .type ha).2
    | _ => cases p <;> simp [admittedAt] at hp

end Lowered

end Mettapedia.GSLT.LanguageDef.MacroExportCorrect
