import Mettapedia.Logic.HostingStyles.StoredPrograms.Running
import Mettapedia.Logic.HostingStyles.StoredPrograms.TableCheck
import Mettapedia.Logic.HostingStyles.StoredPrograms.NormalForms

/-!
# Replaying a trace in a stored table

`replay` (`Running.lean`) compares, at every step, the instance of the left
side with the term.  For a rule whose left side is an algebraic pattern
without a repeated variable the comparison always succeeds: the match gives
the instance (`bindVariables_inst`).  So in a stored table it is left out
(`contractLinear`, `replayLinear`), which keeps the replay of some hundred
steps in a table of some hundred rules within what the kernel evaluates.

A trace is written with its paths as numbers (`decodePath`): the binary digits
of the number from the least, below its leading one; `1` is the root.

* `replayCoded rules trace term` replays a trace written so.
* **In a stored table a term reduces to what the replay gives**
  (`StoredTable.replayCoded_reduces`), whatever the trace.

Positive: the three steps of unary addition (`addition_replaysCoded`), and the
path of a code (`decodePath_thirteen`).  Negative: the rule of
`(same x x) = x` repeats a variable, and the match without comparison rewrites
the call of `same` on `a` and `b`, which has no step
(`contractLinear_repeated`); so the condition on the table is needed.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.StoredPrograms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.Dedukti
  (Theory RewriteRule Step Reduces inst algebraic patternVars inst_congr_patternVars)
open Mettapedia.GSLT.Dedukti.ConfluenceExamples (step_of_rule)
open Mettapedia.Logic.HostingStyles.AtomsReduce (programTheory)

/-! ## A match of a pattern without a repeated variable gives the instance -/

/-- The keys of the bindings of a match are the variables of the pattern, in
their order. -/
theorem bindVariables_keys : ∀ {pattern term : LF.Term} {bindings : List (Nat × LF.Term)},
    bindVariables pattern term = some bindings → bindings.map Prod.fst = patternVars pattern := by
  intro pattern
  induction pattern with
  | var index =>
      intro term bindings matched
      simp only [bindVariables, Option.some.injEq] at matched
      subst matched
      rfl
  | con name =>
      intro term bindings matched
      cases term with
      | con other =>
          simp only [bindVariables] at matched
          split at matched
          · obtain rfl := Option.some.inj matched
            rfl
          · cases matched
      | _ => simp [bindVariables] at matched
  | app function argument ihFunction ihArgument =>
      intro term bindings matched
      cases term with
      | app otherFunction otherArgument =>
          simp only [bindVariables] at matched
          split at matched
          · next left right foundLeft foundRight =>
            obtain rfl := Option.some.inj matched
            simp [patternVars, ihFunction foundLeft, ihArgument foundRight]
          · cases matched
      | _ => simp [bindVariables] at matched
  | srt sort => intro term bindings matched; cases term <;> simp [bindVariables] at matched
  | pi domain body _ _ =>
      intro term bindings matched; cases term <;> simp [bindVariables] at matched
  | lam domain body _ _ =>
      intro term bindings matched; cases term <;> simp [bindVariables] at matched

/-- A key of the first list is found in the first list. -/
theorem lookup_append_of_mem {left right : List (Nat × LF.Term)} {index : Nat}
    (member : index ∈ left.map Prod.fst) : (left ++ right).lookup index = left.lookup index := by
  induction left with
  | nil => simp at member
  | cons binding rest ih =>
      obtain ⟨key, value⟩ := binding
      by_cases same : index = key
      · subst same
        simp
      · have differs : (index == key) = false := by simpa using same
        have later : index ∈ rest.map Prod.fst := by simpa [same] using member
        simp [List.lookup_cons, differs, ih later]

/-- A key that the first list does not have is looked up in the second. -/
theorem lookup_append_of_not_mem {left right : List (Nat × LF.Term)} {index : Nat}
    (absent : index ∉ left.map Prod.fst) : (left ++ right).lookup index = right.lookup index := by
  induction left with
  | nil => rfl
  | cons binding rest ih =>
      obtain ⟨key, value⟩ := binding
      have differs : (index == key) = false := by
        simpa using fun same : index = key => absent (by simp [same])
      have later : index ∉ rest.map Prod.fst := fun member => absent (by simp [member])
      simp [List.lookup_cons, differs, ih later]

/-- **The match of an algebraic pattern without a repeated variable gives the
instance**: under the bindings of the match the pattern is the term. -/
theorem bindVariables_inst : ∀ {pattern : LF.Term} {headed : Bool},
    algebraic headed pattern = true → (patternVars pattern).Nodup →
    ∀ {term : LF.Term} {bindings : List (Nat × LF.Term)},
      bindVariables pattern term = some bindings → inst (boundTo bindings) pattern = term := by
  intro pattern
  induction pattern with
  | var index =>
      intro headed _ _ term bindings matched
      simp only [bindVariables, Option.some.injEq] at matched
      subst matched
      simp [boundTo]
  | con name =>
      intro headed _ _ term bindings matched
      cases term with
      | con other =>
          simp only [bindVariables] at matched
          split at matched
          · next same =>
            subst same
            simp
          · cases matched
      | _ => simp [bindVariables] at matched
  | app function argument ihFunction ihArgument =>
      intro headed isAlgebraic distinct term bindings matched
      cases term with
      | app otherFunction otherArgument =>
          simp only [bindVariables] at matched
          split at matched
          · next left right foundLeft foundRight =>
            obtain rfl := Option.some.inj matched
            obtain ⟨functionAlgebraic, argumentAlgebraic⟩ := Dedukti.algebraic_app.mp isAlgebraic
            have parts : (patternVars function ++ patternVars argument).Nodup := distinct
            have leftKeys := bindVariables_keys foundLeft
            rw [Dedukti.inst_app]
            congr 1
            · rw [← ihFunction functionAlgebraic (List.Nodup.of_append_left parts) foundLeft]
              refine inst_congr_patternVars functionAlgebraic fun index member => ?_
              unfold boundTo
              rw [lookup_append_of_mem (leftKeys ▸ member)]
            · rw [← ihArgument argumentAlgebraic (List.Nodup.of_append_right parts) foundRight]
              refine inst_congr_patternVars argumentAlgebraic fun index member => ?_
              have absent : index ∉ left.map Prod.fst := by
                rw [leftKeys]
                exact fun inFunction => List.disjoint_of_nodup_append parts inFunction member
              unfold boundTo
              rw [lookup_append_of_not_mem absent]
          · cases matched
      | _ => simp [bindVariables] at matched
  | srt sort =>
      intro headed _ _ term bindings matched; cases term <;> simp [bindVariables] at matched
  | pi domain body _ _ =>
      intro headed _ _ term bindings matched; cases term <;> simp [bindVariables] at matched
  | lam domain body _ _ =>
      intro headed _ _ term bindings matched; cases term <;> simp [bindVariables] at matched

/-! ## Steps without the comparison -/

/-- **One rule at the root, without the comparison**: the instance of the
right side under the bindings of the match. -/
def contractLinear (rule : RewriteRule) (term : LF.Term) : Option LF.Term :=
  match bindVariables rule.lhs term with
  | some bindings => some (inst (boundTo bindings) rule.rhs)
  | none => none

/-- **A rule at a position, without the comparison.** -/
def contractLinearAt (rule : RewriteRule) : List Bool → LF.Term → Option LF.Term
  | [], term => contractLinear rule term
  | false :: path, .app function argument =>
      (contractLinearAt rule path function).map fun next => .app next argument
  | true :: path, .app function argument =>
      (contractLinearAt rule path argument).map fun next => .app function next
  | _ :: _, _ => none

/-- **The replay of a trace, without the comparison.** -/
def replayLinear (rules : List RewriteRule) : List (List Bool × Nat) → LF.Term → Option LF.Term
  | [], term => some term
  | (path, index) :: trace, term =>
      match rules[index]? with
      | some rule =>
          match contractLinearAt rule path term with
          | some next => replayLinear rules trace next
          | none => none
      | none => none

theorem contractLinear_sound {theory : Theory} {rule : RewriteRule} (member : theory.rule rule)
    (isAlgebraic : algebraic true rule.lhs = true) (distinct : (patternVars rule.lhs).Nodup)
    {term next : LF.Term} (contracted : contractLinear rule term = some next) :
    Step theory term next := by
  unfold contractLinear at contracted
  split at contracted
  · next bindings matched =>
    exact step_of_rule member (boundTo bindings) (bindVariables_inst isAlgebraic distinct matched)
      (Option.some.inj contracted)
  · cases contracted

theorem contractLinearAt_sound {theory : Theory} {rule : RewriteRule} (member : theory.rule rule)
    (isAlgebraic : algebraic true rule.lhs = true) (distinct : (patternVars rule.lhs).Nodup)
    (path : List Bool) : ∀ {term next : LF.Term}, contractLinearAt rule path term = some next →
      Step theory term next := by
  induction path with
  | nil =>
      intro term next contracted
      exact contractLinear_sound member isAlgebraic distinct contracted
  | cons side path ih =>
      intro term next contracted
      cases term with
      | app function argument =>
          cases side with
          | false =>
              simp only [contractLinearAt, Option.map_eq_some_iff] at contracted
              obtain ⟨inner, found, rfl⟩ := contracted
              exact (ih found).plug (.appFunction .hole argument)
          | true =>
              simp only [contractLinearAt, Option.map_eq_some_iff] at contracted
              obtain ⟨inner, found, rfl⟩ := contracted
              exact (ih found).plug (.appArgument function .hole)
      | _ => cases side <;> simp [contractLinearAt] at contracted

/-- **A term reduces to what the replay without comparison gives**, when the
left side of every rule is an algebraic pattern without a repeated
variable. -/
theorem replayLinear_reduces {rules : List RewriteRule}
    (linear : ∀ rule ∈ rules, algebraic true rule.lhs = true ∧ (patternVars rule.lhs).Nodup) :
    ∀ (trace : List (List Bool × Nat)) {term result : LF.Term},
      replayLinear rules trace term = some result → Reduces (programTheory rules) term result
  | [], _, _, replayed => by
      obtain rfl := Option.some.inj replayed
      exact .refl
  | (path, index) :: trace, term, result, replayed => by
      simp only [replayLinear] at replayed
      split at replayed
      · next rule found =>
        split at replayed
        · next inner contracted =>
          have member := List.mem_of_getElem? found
          exact Relation.ReflTransGen.head
            (contractLinearAt_sound (theory := programTheory rules) member (linear rule member).1
              (linear rule member).2 path contracted)
            (replayLinear_reduces linear trace replayed)
        · cases replayed
      · cases replayed

/-! ## Paths as numbers -/

/-- The digits of a code, with fuel. -/
def decodePathWith : Nat → Nat → List Bool
  | 0, _ => []
  | fuel + 1, code =>
      if code ≤ 1 then [] else (code % 2 == 1) :: decodePathWith fuel (code / 2)

/-- **The path that a number codes**: its binary digits from the least, below
its leading one.  An odd digit is the argument of an application, an even one
its function. -/
def decodePath (code : Nat) : List Bool := decodePathWith code code

/-- **Positive**: thirteen is the first argument of a call: the argument, its
function, and the argument of that.  One is the root. -/
theorem decodePath_thirteen : decodePath 13 = [true, false, true] ∧ decodePath 1 = [] := by
  decide

/-- **Negative**: nought codes the root as well, so a path has not one code. -/
theorem decodePath_nought : decodePath 0 = decodePath 1 := by decide

/-- **The replay of a trace whose paths are numbers.** -/
def replayCoded (rules : List RewriteRule) (trace : List (Nat × Nat)) (term : LF.Term) :
    Option LF.Term :=
  replayLinear rules (trace.map fun step => (decodePath step.1, step.2)) term

namespace StoredTable

variable {rules : List RewriteRule}

/-- The left sides of a stored table are algebraic patterns without a repeated
variable. -/
theorem linear (stored : StoredTable rules) :
    ∀ rule ∈ rules, algebraic true rule.lhs = true ∧ (patternVars rule.lhs).Nodup :=
  fun rule member =>
    ⟨(storedRuleCheck_spec (stored.each rule member)).2.1,
      (storedRuleCheck_spec (stored.each rule member)).2.2.1⟩

/-- **In a stored table a term reduces to what the replay gives**, whatever
the trace. -/
theorem replayCoded_reduces (stored : StoredTable rules) {trace : List (Nat × Nat)}
    {term result : LF.Term} (replayed : replayCoded rules trace term = some result) :
    Reduces (programTheory rules) term result :=
  replayLinear_reduces stored.linear _ replayed

end StoredTable

/-! ## Examples -/

/-- **Positive**: the three steps of the addition of two and one, with their
paths as numbers. -/
theorem addition_replaysCoded :
    replayCoded (programRules constantSpelling additionProgram []) [(1, 1), (27, 1), (443, 0)]
        (callTerm "add" (data constantSpelling
          [.expr [.sym "S", .expr [.sym "S", .sym "Z"]], .expr [.sym "S", .sym "Z"]])) =
      some (datum constantSpelling
        (.expr [.sym "S", .expr [.sym "S", .expr [.sym "S", .sym "Z"]]])) := by
  decide +kernel

/-- **Negative**: the rule of `(same x x) = x` repeats a variable.  The match
without comparison binds it at its first occurrence, as the engine does, and
rewrites the call of `same` on `a` and `b` to the datum of `a`; that call has
no step in the theory of the rule. -/
theorem contractLinear_repeated :
    (repeatedRules.head?.bind fun rule =>
        contractLinear rule (callTerm "same" (data constantSpelling [.sym "a", .sym "b"]))) =
      some (datum constantSpelling (.sym "a")) ∧
    ∀ target, ¬ Step (programTheory repeatedRules)
      (callTerm "same" (data constantSpelling [.sym "a", .sym "b"])) target := by
  refine ⟨by decide +kernel, fun target step => ?_⟩
  exact repeatedVariable_witness.2.1 target step

#print axioms bindVariables_keys
#print axioms bindVariables_inst
#print axioms contractLinear_sound
#print axioms contractLinearAt_sound
#print axioms replayLinear_reduces
#print axioms StoredTable.replayCoded_reduces
#print axioms decodePath_thirteen
#print axioms addition_replaysCoded
#print axioms contractLinear_repeated

end Mettapedia.Logic.HostingStyles.StoredPrograms
