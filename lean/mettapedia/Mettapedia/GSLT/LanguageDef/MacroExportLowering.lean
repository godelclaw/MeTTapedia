import Mathlib.Data.List.Perm.Basic

/-!
# Lowering macro uses to readable C

A typed macro use evaluates each of its arguments once, in declared order, and
then its template with the resulting values. Readable program export writes
that use as a block: one named local per argument, initialized in declared
order, followed by the template with arguments replaced by those locals.

The source contract and the block are evaluated by independent semantics: the
source by call-by-value over the argument list, the block by a generic
statement evaluator that knows nothing about macros. `export_block_eval`
proves they agree on the value and on the trace of observable effects, given
the binding conditions the exporter checks: distinct parameters, distinct
acquisition names that no argument reads, and a template that refers only to
its parameters.

A plain C call is different. C leaves the evaluation order of arguments
unspecified, modelled here as any permutation. `call_trace_any_order` shows
every order yields the source trace when at most one argument has effects;
`call_order_observable` shows two effectful arguments can be observed in the
other order. `prototype_converts` shows that a prototype admits a converted
argument that the exact-type contract refuses. Library headers therefore
state their C contract; program export keeps the ordered, exact form.

The model is integer values, an immutable environment and tagged effects. It
does not model C memory, C types beyond the conversion example, or the native
compiler; native differential tests check the generated C.
-/

namespace Mettapedia.GSLT.LanguageDef.MacroExportLowering

set_option autoImplicit false

/-! ## Expressions with observable effects -/

inductive Exp where
  | lit (value : Int)
  | var (name : String)
  | effect (tag : Nat) (inner : Exp)
  | add (left right : Exp)
  deriving Repr, DecidableEq

abbrev Env := String → Int

/-- The value of an expression and the effects it emits, in order. -/
def eval (env : Env) : Exp → Int × List Nat
  | .lit n => (n, [])
  | .var x => (env x, [])
  | .effect tag e => ((eval env e).1, (eval env e).2 ++ [tag])
  | .add a b => ((eval env a).1 + (eval env b).1, (eval env a).2 ++ (eval env b).2)

def vars : Exp → List String
  | .lit _ => []
  | .var x => [x]
  | .effect _ e => vars e
  | .add a b => vars a ++ vars b

def update (env : Env) (x : String) (v : Int) : Env := fun y => if y = x then v else env y

theorem eval_congr (env env' : Env) (e : Exp) (agree : ∀ x ∈ vars e, env x = env' x) :
    eval env e = eval env' e := by
  induction e with
  | lit n => rfl
  | var x => simp [eval, agree x (by simp [vars])]
  | effect tag e ih => simp [eval, ih (by simpa [vars] using agree)]
  | add a b iha ihb =>
      have ha := iha (fun x hx => agree x (by simp [vars, hx]))
      have hb := ihb (fun x hx => agree x (by simp [vars, hx]))
      simp [eval, ha, hb]

/-- Rename variables. -/
def rename (σ : String → String) : Exp → Exp
  | .lit n => .lit n
  | .var x => .var (σ x)
  | .effect tag e => .effect tag (rename σ e)
  | .add a b => .add (rename σ a) (rename σ b)

theorem eval_rename (σ : String → String) (env env' : Env) (e : Exp)
    (agree : ∀ x ∈ vars e, env (σ x) = env' x) :
    eval env (rename σ e) = eval env' e := by
  induction e with
  | lit n => rfl
  | var x => simp [rename, eval, agree x (by simp [vars])]
  | effect tag e ih => simp [rename, eval, ih (by simpa [vars] using agree)]
  | add a b iha ihb =>
      have ha := iha (fun x hx => agree x (by simp [vars, hx]))
      have hb := ihb (fun x hx => agree x (by simp [vars, hx]))
      simp [rename, eval, ha, hb]

/-! ## The source contract -/

/-- A macro whose template refers only to its parameters. -/
structure Rule where
  params : List String
  body : Exp

/-- Each argument once, left to right. -/
def evalArgs (env : Env) : List Exp → List Int × List Nat
  | [] => ([], [])
  | e :: es => ((eval env e).1 :: (evalArgs env es).1, (eval env e).2 ++ (evalArgs env es).2)

/-- Parameters bound to values over an outer environment. -/
def bindParams (env : Env) : List String → List Int → Env
  | x :: xs, v :: vs => update (bindParams env xs vs) x v
  | _, _ => env

/-- The source use: arguments once in declared order, then the template. -/
def source (env : Env) (rule : Rule) (args : List Exp) : Int × List Nat :=
  ((eval (bindParams env rule.params (evalArgs env args).1) rule.body).1,
   (evalArgs env args).2 ++ (eval (bindParams env rule.params (evalArgs env args).1) rule.body).2)

/-! ## Blocks, evaluated without reference to macros -/

inductive Stmt where
  | declare (name : String) (init : Exp)
  deriving Repr, DecidableEq

def runStmts (env : Env) : List Stmt → Env × List Nat
  | [] => (env, [])
  | .declare x e :: rest =>
      ((runStmts (update env x (eval env e).1) rest).1,
       (eval env e).2 ++ (runStmts (update env x (eval env e).1) rest).2)

/-- Statements in order, then the block's value. -/
def runBlock (env : Env) (stmts : List Stmt) (value : Exp) : Int × List Nat :=
  ((eval (runStmts env stmts).1 value).1, (runStmts env stmts).2 ++ (eval (runStmts env stmts).1 value).2)

/-! ## Readable export of a use -/

/-- One named acquisition per argument. -/
def acquisitions : List String → List Exp → List Stmt
  | x :: xs, e :: es => .declare x e :: acquisitions xs es
  | _, _ => []

/-- The parameter-to-acquisition renaming. -/
def acquire : List String → List String → String → String
  | p :: ps, n :: ns, x => if x = p then n else acquire ps ns x
  | _, _, x => x

/-- The binding conditions the exporter checks. -/
structure Admitted (rule : Rule) (names : List String) (args : List Exp) : Prop where
  params_length : rule.params.length = args.length
  names_length : names.length = args.length
  params_distinct : rule.params.Nodup
  names_distinct : names.Nodup
  unread : ∀ n ∈ names, ∀ e ∈ args, n ∉ vars e
  closed : ∀ x ∈ vars rule.body, x ∈ rule.params

/-! ### Supporting facts -/

theorem runStmts_untouched (env : Env) (names : List String) (args : List Exp) (y : String)
    (absent : y ∉ names) : (runStmts env (acquisitions names args)).1 y = env y := by
  induction names generalizing env args with
  | nil => cases args <;> simp [acquisitions, runStmts]
  | cons n ns ih =>
      cases args with
      | nil => simp [acquisitions, runStmts]
      | cons e es =>
          have hy : y ≠ n := fun h => absent (by simp [h])
          have hys : y ∉ ns := fun h => absent (by simp [h])
          simp only [acquisitions, runStmts]
          rw [ih _ es hys]
          simp [update, hy]

theorem bindParams_bound (base base' : Env) (params : List String) (values : List Int) (x : String)
    (lengths : params.length = values.length) (bound : x ∈ params) :
    bindParams base params values x = bindParams base' params values x := by
  induction params generalizing values with
  | nil => simp at bound
  | cons p ps ih =>
      cases values with
      | nil => simp at lengths
      | cons v vs =>
          simp only [bindParams, update]
          by_cases hx : x = p
          · simp [hx]
          · have : x ∈ ps := by simpa [hx] using bound
            simp [hx, ih vs (by simpa using lengths) this]

theorem evalArgs_length (env : Env) (args : List Exp) : (evalArgs env args).1.length = args.length := by
  induction args with
  | nil => rfl
  | cons e es ih => simp [evalArgs, ih]

theorem evalArgs_unread (env : Env) (n : String) (v : Int) (args : List Exp)
    (unread : ∀ e ∈ args, n ∉ vars e) : evalArgs (update env n v) args = evalArgs env args := by
  induction args with
  | nil => rfl
  | cons e es ih =>
      have he : eval (update env n v) e = eval env e := by
        apply eval_congr
        intro x hx
        have : x ≠ n := fun h => unread e (by simp) (h ▸ hx)
        simp [update, this]
      simp [evalArgs, he, ih (fun f hf => unread f (by simp [hf]))]

/-- The acquisitions emit exactly the arguments' effects in declared order. -/
theorem acquisitions_trace (env : Env) (names : List String) (args : List Exp)
    (lengths : names.length = args.length) (unread : ∀ n ∈ names, ∀ e ∈ args, n ∉ vars e) :
    (runStmts env (acquisitions names args)).2 = (evalArgs env args).2 := by
  induction names generalizing env args with
  | nil => cases args with
    | nil => rfl
    | cons e es => simp at lengths
  | cons n ns ih =>
      cases args with
      | nil => simp at lengths
      | cons e es =>
          have rest := ih (update env n (eval env e).1) es (by simpa using lengths)
            (fun m hm f hf => unread m (by simp [hm]) f (by simp [hf]))
          have same := evalArgs_unread env n (eval env e).1 es
            (fun f hf => unread n (by simp) f (by simp [hf]))
          simp [acquisitions, runStmts, evalArgs, rest, same]

/-- At a parameter's acquisition name the block holds the source binding. -/
theorem acquisitions_bind (env : Env) (params names : List String) (args : List Exp)
    (params_length : params.length = args.length) (names_length : names.length = args.length)
    (params_distinct : params.Nodup) (names_distinct : names.Nodup)
    (unread : ∀ n ∈ names, ∀ e ∈ args, n ∉ vars e) (x : String) (bound : x ∈ params) :
    (runStmts env (acquisitions names args)).1 (acquire params names x) =
      bindParams env params (evalArgs env args).1 x := by
  induction params generalizing env names args with
  | nil => simp at bound
  | cons p ps ih =>
      cases names with
      | nil => cases args with
        | nil => simp at params_length
        | cons e es => simp at names_length
      | cons n ns =>
          cases args with
          | nil => simp at params_length
          | cons e es =>
              have restUnread : ∀ m ∈ ns, ∀ f ∈ es, m ∉ vars f :=
                fun m hm f hf => unread m (by simp [hm]) f (by simp [hf])
              have same := evalArgs_unread env n (eval env e).1 es
                (fun f hf => unread n (by simp) f (by simp [hf]))
              by_cases hx : x = p
              · subst hx
                have absent : n ∉ ns := (List.nodup_cons.mp names_distinct).1
                simp only [acquire, ↓reduceIte, acquisitions, runStmts, evalArgs, bindParams]
                rw [runStmts_untouched _ ns es n absent]
                simp [update]
              · have inRest : x ∈ ps := by simpa [hx] using bound
                have step := ih (update env n (eval env e).1) ns es (by simpa using params_length)
                  (by simpa using names_length) (List.nodup_cons.mp params_distinct).2
                  (List.nodup_cons.mp names_distinct).2 restUnread inRest
                simp only [acquire, if_neg hx, acquisitions, runStmts, evalArgs, bindParams]
                rw [step, same]
                have lengths : ps.length = (evalArgs env es).1.length := by
                  rw [evalArgs_length]; simpa using params_length
                rw [bindParams_bound (update env n (eval env e).1) env ps _ x lengths inRest]
                simp [update, hx]

/-! ### The lowering law -/

/-- Readable export evaluates exactly as the source use: same value, same
effects in the same order. -/
theorem export_block_eval (env : Env) (rule : Rule) (names : List String) (args : List Exp)
    (admitted : Admitted rule names args) :
    runBlock env (acquisitions names args) (rename (acquire rule.params names) rule.body) =
      source env rule args := by
  have body : eval (runStmts env (acquisitions names args)).1 (rename (acquire rule.params names) rule.body) =
      eval (bindParams env rule.params (evalArgs env args).1) rule.body :=
    eval_rename _ _ _ _ (fun x hx => acquisitions_bind env rule.params names args admitted.params_length
      admitted.names_length admitted.params_distinct admitted.names_distinct admitted.unread x
      (admitted.closed x hx))
  have trace := acquisitions_trace env names args admitted.names_length admitted.unread
  simp [runBlock, source, body, trace]

/-! ## A plain C call: unspecified argument order -/

/-- The effects of evaluating arguments in a given order. -/
def callTrace (env : Env) (order : List Exp) : List Nat := (order.map fun e => (eval env e).2).flatten

theorem flatten_perm_of_commute (l l' : List (List Nat)) (perm : l.Perm l')
    (commute : ∀ a ∈ l, ∀ b ∈ l, a ++ b = b ++ a) : l.flatten = l'.flatten := by
  induction perm with
  | nil => rfl
  | cons x _ ih =>
      simp only [List.flatten_cons]
      rw [ih (fun a ha b hb => commute a (by simp [ha]) b (by simp [hb]))]
  | swap x y rest =>
      simp only [List.flatten_cons]
      rw [← List.append_assoc, ← List.append_assoc, commute y (by simp) x (by simp)]
  | trans p _ ih₁ ih₂ =>
      exact (ih₁ commute).trans (ih₂ (fun a ha b hb => commute a (p.symm.subset ha) b (p.symm.subset hb)))

/-- When at most one argument has effects, every evaluation order of a C call
emits the source trace. -/
theorem call_trace_any_order (env : Env) (args order : List Exp) (perm : order.Perm args)
    (quiet : ∀ e ∈ args, ∀ f ∈ args, e ≠ f → (eval env e).2 = [] ∨ (eval env f).2 = []) :
    callTrace env order = (evalArgs env args).2 := by
  have commute : ∀ a ∈ args.map (fun e => (eval env e).2), ∀ b ∈ args.map (fun e => (eval env e).2),
      a ++ b = b ++ a := by
    intro a ha b hb
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hb
    by_cases same : e = f
    · subst same; rfl
    · rcases quiet e he f hf same with h | h <;> simp [h]
  have flat := flatten_perm_of_commute _ _ (perm.map _).symm commute
  have source : (evalArgs env args).2 = (args.map fun e => (eval env e).2).flatten := by
    clear perm quiet commute flat
    induction args with
    | nil => rfl
    | cons e es ih => simp [evalArgs, ih]
  simp [callTrace, source, flat]

/-- Two arguments with effects: a C call may emit them in the other order. -/
theorem call_order_observable :
    callTrace (fun _ => 0) [.effect 2 (.lit 0), .effect 1 (.lit 0)] ≠
      (evalArgs (fun _ => 0) [.effect 1 (.lit 0), .effect 2 (.lit 0)]).2 := by
  decide

/-! ## Exact admission versus prototype conversion -/

inductive Ty where
  | u32 | u64
  deriving DecidableEq, Repr

/-- The exact contract admits an argument only at its declared type. -/
def exactAdmits (declared actual : Ty) : Bool := declared == actual

/-- A prototype converts any integer argument to the parameter type. -/
def prototypeValue : Ty → Int → Int
  | .u32, v => v % 4294967296
  | .u64, v => v % 18446744073709551616

/-- A uint64_t argument to a uint32_t parameter: the exact contract refuses it,
while a prototype accepts it and changes its value. -/
theorem prototype_converts :
    exactAdmits .u32 .u64 = false ∧ prototypeValue .u32 4294967296 ≠ 4294967296 := by
  decide

end Mettapedia.GSLT.LanguageDef.MacroExportLowering
