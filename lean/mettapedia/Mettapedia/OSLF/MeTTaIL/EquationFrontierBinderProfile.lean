import Mettapedia.GSLT.LanguageDef.WellSortedChecker
import Mettapedia.OSLF.MeTTaIL.ScopedEquationControls
import Mathlib.Data.List.FinRange

/-!
# A finite, typed binder-extrusion profile

The carrier is a family indexed by the ambient name context. Its payload can
refer to the local restriction name or any ambient name. The equation moves
an independent closed guard outside that restriction; its guard is an actual
finite relation query. The directed rule is available only in the exposed
presentation. Equation conversion never counts as that directed event.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderProfile

open Syntax Engine
open Mettapedia.GSLT.LanguageDef.WellSorted

inductive Token where
  | permit
  | reserve
  | revoked
  deriving DecidableEq, Repr

def Token.label : Token → String
  | .permit => "Permit"
  | .reserve => "Reserve"
  | .revoked => "Revoked"

def Token.pattern (token : Token) : Pattern := .apply token.label []

def guard (token : Token) : Pattern := .apply "Guard" [token.pattern]

def cell (index : Nat) : Pattern := .apply "Cell" [.bvar index]

def nu (body : Pattern) : Pattern := .apply "Nu" [.lambda none body]

def pair (left right : Pattern) : Pattern := .apply "Pair" [left, right]

def done (body : Pattern) : Pattern := .apply "Done" [body]

def tokenRule (token : Token) : GrammarRule where
  label := token.label
  category := "Name"
  params := []
  syntaxPattern := [.terminal token.label]

def guardRule : GrammarRule where
  label := "Guard"
  category := "Proc"
  params := [.simple "key" .name]
  syntaxPattern := [.terminal "guard", .nonTerminal "key"]

def cellRule : GrammarRule where
  label := "Cell"
  category := "Proc"
  params := [.simple "name" .name]
  syntaxPattern := [.terminal "cell", .nonTerminal "name"]

def pairRule : GrammarRule where
  label := "Pair"
  category := "Proc"
  params := [.simple "left" .proc, .simple "right" .proc]
  syntaxPattern := [.nonTerminal "left", .terminal "|", .nonTerminal "right"]

def nuRule : GrammarRule where
  label := "Nu"
  category := "Proc"
  params := [.abstraction "body" (.arrow .name .proc)]
  syntaxPattern := [.terminal "new", .nonTerminal "body"]

def doneRule : GrammarRule where
  label := "Done"
  category := "Proc"
  params := [.simple "body" .proc]
  syntaxPattern := [.terminal "done", .nonTerminal "body"]

def extrusionEquation : Equation :=
  { ScopedEquationControls.extrusionEquation with
    name := "guarded-binder-extrusion"
    premises := [.relationQuery "allow" [.fvar "Q"]]
    bindings := some {
      dependencies := [("P", [.name]), ("Q", [])]
      occurrences :=
        [{ name := "P", site := .left, path := [0, 0, 0], arguments := [.bvar 0] },
         { name := "Q", site := .left, path := [0, 0, 1], arguments := [] },
         { name := "P", site := .right, path := [0, 0, 0], arguments := [.bvar 0] },
         { name := "Q", site := .right, path := [1], arguments := [] }] } }

def consumeRule : RewriteRule where
  name := "consume-guard"
  typeContext := [("P", .proc), ("Q", .proc)]
  premises := [.relationQuery "allow" [.fvar "Q"]]
  left := pair (nu (.fvar "P")) (.fvar "Q")
  right := nu (done (pair (.fvar "P") (.fvar "Q")))
  bindings := some {
    dependencies := [("P", [.name]), ("Q", [])]
    occurrences :=
      [{ name := "P", site := .left, path := [0, 0, 0], arguments := [.bvar 0] },
       { name := "Q", site := .left, path := [1], arguments := [] },
       { name := "P", site := .right, path := [0, 0, 0, 0], arguments := [.bvar 0] },
       { name := "Q", site := .right, path := [0, 0, 0, 1], arguments := [] }] }

/-- The two declarations intentionally have identical bodies. Their list
positions remain distinct authored event origins. -/
def language : LanguageDef where
  name := "GuardedBinderFrontier"
  types := ["Name", "Proc"]
  terms := [tokenRule .permit, tokenRule .reserve, tokenRule .revoked,
    guardRule, cellRule, pairRule, nuRule, doneRule]
  equations := [extrusionEquation]
  rewrites := [consumeRule, { consumeRule with name := "consume-guard-again" }]

/-- A provider snapshot is a finite list of admitted keys. Repeated keys
remain repeated relation-row occurrences. -/
def provider (allowed : List Token) : RelationEnv where
  tuples := fun relation _ =>
    if relation = "allow" then allowed.map (fun token => [guard token]) else []

inductive Phase where
  | tucked
  | exposed
  | finished
  deriving DecidableEq, Repr

structure State (ambient : Nat) where
  phase : Phase
  name : Fin (ambient + 1)
  key : Token
  deriving DecidableEq, Repr

def State.pattern {ambient : Nat} (state : State ambient) : Pattern :=
  match state.phase with
  | .tucked => nu (pair (cell state.name.val) (guard state.key))
  | .exposed => pair (nu (cell state.name.val)) (guard state.key)
  | .finished => nu (done (pair (cell state.name.val) (guard state.key)))

def ambientContext (ambient : Nat) : List TypeExpr :=
  List.replicate ambient .name

def allTokens : List Token := [.permit, .reserve, .revoked]

def allPhases : List Phase := [.tucked, .exposed, .finished]

def allStates (ambient : Nat) : List (State ambient) :=
  allPhases.flatMap fun phase =>
    (List.finRange (ambient + 1)).flatMap fun name =>
      allTokens.map fun key => ⟨phase, name, key⟩

/-- A finite, executable domain for every ambient context, not just a finite
list of selected ground examples. -/
theorem allStates_complete {ambient : Nat} (state : State ambient) :
    state ∈ allStates ambient := by
  cases state with
  | mk phase name key =>
    apply List.mem_flatMap.mpr
    refine ⟨phase, ?_, List.mem_flatMap.mpr ⟨name, ?_, ?_⟩⟩
    · cases phase <;> simp [allPhases]
    · simp
    · apply List.mem_map.mpr
      refine ⟨key, ?_, rfl⟩
      cases key <;> simp [allTokens]

theorem token_pattern_injective : Function.Injective Token.pattern := by
  intro left right equal
  cases left <;> cases right <;> simp_all [Token.pattern, Token.label]

/-- The source encoding retains the key even after consumption. Distinct
carrier states cannot silently collapse to one raw endpoint. -/
theorem state_pattern_injective {ambient : Nat} :
    Function.Injective (@State.pattern ambient) := by
  intro left right equal
  cases left with
  | mk leftPhase leftName leftKey =>
    cases right with
    | mk rightPhase rightName rightKey =>
      cases leftPhase <;> cases rightPhase <;>
        simp only [State.pattern, nu, pair, cell, done, guard,
          Pattern.apply.injEq, Pattern.lambda.injEq, List.cons.injEq,
          Pattern.bvar.injEq, and_true, true_and] at equal
      all_goals try simp at equal
      all_goals rcases equal with ⟨nameEq, keyEq⟩
      all_goals have names := Fin.ext nameEq
      all_goals have keys := token_pattern_injective keyEq
      all_goals simp [names, keys]

private theorem noBareToken (token : Token) : ¬ UsesBareCollection (tokenRule token) := by
  simp [UsesBareCollection, tokenRule]

theorem token_typed (token : Token) (bound : List TypeExpr) :
    HasType language FreeTypeContext.empty bound token.pattern .name := by
  apply HasType.constructor (rule := tokenRule token)
  · cases token <;> simp [language]
  · exact noBareToken token
  · exact .nil

theorem guard_typed (token : Token) (bound : List TypeExpr) :
    HasType language FreeTypeContext.empty bound (guard token) .proc := by
  apply HasType.constructor (rule := guardRule)
  · simp [language]
  · simp [UsesBareCollection, guardRule, TypeExpr.name, TypeExpr.baseType]
  · exact .cons trivial rfl (token_typed token bound) .nil

theorem cell_typed (ambient : Nat) (index : Fin (ambient + 1)) :
    HasType language FreeTypeContext.empty
      (.name :: ambientContext ambient) (cell index.val) .proc := by
  apply HasType.constructor (rule := cellRule)
  · simp [language]
  · simp [UsesBareCollection, cellRule, TypeExpr.name, TypeExpr.baseType]
  · refine ArgumentsHaveTypes.cons (parameter := .simple "name" .name)
      (argument := .bvar index.val) trivial rfl ?_ .nil
    · apply HasType.bvar
      change (List.replicate (ambient + 1) TypeExpr.name)[index.val]? = some .name
      simp [index.isLt]

theorem pair_typed (bound : List TypeExpr) (left right : Pattern)
    (leftTyped : HasType language FreeTypeContext.empty bound left .proc)
    (rightTyped : HasType language FreeTypeContext.empty bound right .proc) :
    HasType language FreeTypeContext.empty bound (pair left right) .proc := by
  apply HasType.constructor (rule := pairRule)
  · simp [language]
  · simp [UsesBareCollection, pairRule]
  · exact .cons trivial rfl leftTyped (.cons trivial rfl rightTyped .nil)

theorem nu_typed (bound : List TypeExpr) (body : Pattern)
    (bodyTyped : HasType language FreeTypeContext.empty (.name :: bound) body .proc) :
    HasType language FreeTypeContext.empty bound (nu body) .proc := by
  apply HasType.constructor (rule := nuRule)
  · simp [language]
  · simp [UsesBareCollection, nuRule]
  · exact .cons trivial rfl (.lambda bodyTyped) .nil

theorem done_typed (bound : List TypeExpr) (body : Pattern)
    (bodyTyped : HasType language FreeTypeContext.empty bound body .proc) :
    HasType language FreeTypeContext.empty bound (done body) .proc := by
  apply HasType.constructor (rule := doneRule)
  · simp [language]
  · simp [UsesBareCollection, doneRule, TypeExpr.proc, TypeExpr.baseType]
  · exact .cons trivial rfl bodyTyped .nil

/-- Every element of every ambient-indexed carrier is typed by the actual
authored grammar, including the locally bound name. -/
theorem state_typed {ambient : Nat} (state : State ambient) :
    HasType language FreeTypeContext.empty (ambientContext ambient)
      state.pattern .proc := by
  cases state with
  | mk phase name key =>
    cases phase
    · exact nu_typed _ _ (pair_typed _ _ _ (cell_typed ambient name) (guard_typed key _))
    · exact pair_typed _ _ _ (nu_typed _ _ (cell_typed ambient name)) (guard_typed key _)
    · exact nu_typed _ _ (done_typed _ _
        (pair_typed _ _ _ (cell_typed ambient name) (guard_typed key _)))

theorem state_scoped {ambient : Nat} (state : State ambient) :
    state.pattern.isWellScopedAt ambient = true := by
  cases state with
  | mk phase name key =>
    cases phase <;>
      simp [State.pattern, nu, pair, cell, guard, Token.pattern, done,
        Pattern.isWellScopedAt, Pattern.isWellScopedListAt, name.isLt]

theorem state_object {ambient : Nat} (state : State ambient) :
    isObjectPattern state.pattern = true := by
  cases state with
  | mk phase name key =>
    cases phase <;> simp [State.pattern, nu, pair, cell, guard,
      Token.pattern, done, isObjectPattern, isObjectPatternList]

theorem state_checked {ambient : Nat} (state : State ambient) :
    checkHasType language FreeTypeContext.empty (ambientContext ambient)
      state.pattern .proc = true :=
  checkHasType_complete_of_object (state_typed state) (state_object state)

theorem language_valid : language.validate = [] := by
  cbv

theorem bindings_valid : RuleBinding.bindingDeclarationsValid language = true := by
  simp only [RuleBinding.bindingDeclarationsValid, language_valid]
  decide +kernel

/-- Independent authored equation semantics for this admitted carrier. The
provider snapshot guards the conversion; it does not direct a reduction. -/
inductive EquationEdge {ambient : Nat} (allowed : List Token) :
    State ambient → State ambient → Prop where
  | extrusion (name : Fin (ambient + 1)) (key : Token) :
      key ∈ allowed →
      EquationEdge allowed ⟨.tucked, name, key⟩ ⟨.exposed, name, key⟩

structure Origin where
  declaration : Fin 2
  providerRow : Nat
  deriving DecidableEq, Repr

/-- Independent directed-event semantics retains both authored rule and
provider-row positions, even when their targets coincide. -/
inductive Firing {ambient : Nat} (allowed : List Token) :
    State ambient → Origin → State ambient → Prop where
  | consume (name : Fin (ambient + 1)) (key : Token) (declaration : Fin 2)
      (providerRow : Nat) :
      allowed[providerRow]? = some key →
      Firing allowed ⟨.exposed, name, key⟩ ⟨declaration, providerRow⟩
        ⟨.finished, name, key⟩

def opposite {ambient : Nat} (state : State ambient) : State ambient :=
  { state with phase := match state.phase with
      | .tucked => .exposed
      | .exposed => .tucked
      | .finished => .finished }

def neighbors {ambient : Nat} (allowed : List Token) (state : State ambient) :
    List (State ambient) :=
  if state.key ∈ allowed then
    match state.phase with
    | .tucked | .exposed => [opposite state]
    | .finished => []
  else []

theorem neighbors_spec {ambient : Nat} (allowed : List Token)
    (source target : State ambient) :
    target ∈ neighbors allowed source ↔
      EquationEdge allowed source target ∨ EquationEdge allowed target source := by
  constructor
  · intro member
    cases source with
    | mk sourcePhase sourceName sourceKey =>
      cases sourcePhase <;> by_cases admitted : sourceKey ∈ allowed
      all_goals simp [neighbors, admitted, opposite] at member
      · cases member
        exact Or.inl (.extrusion _ _ admitted)
      · cases member
        exact Or.inr (.extrusion _ _ admitted)
  · rintro (edge | edge)
    · cases edge with
      | extrusion name key admitted => simp [neighbors, admitted, opposite]
    · cases edge with
      | extrusion name key admitted => simp [neighbors, admitted, opposite]

end Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderProfile
