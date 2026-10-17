import Mettapedia.Languages.ProcessCalculi.RhoCalculus.SemanticSubstitution

/-!
# Explicit computation evidence for rho communication

The evidence follows rho's own name normalization and COMM substitution.
Every recursive call retains its literal result. Replay checks one constructor
case and its submitted child calls; it does not execute the original recursive
normalizer or substitution as a trusted inference step.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.SemanticSubstitutionEvidence

open Mettapedia.OSLF.MeTTaIL.Syntax

inductive Task where
  | normalizeName (name : Pattern)
  | normalizeProc (process : Pattern)
  | normalizeList (processes : List Pattern)
  | substituteName (index : Nat) (replacement name : Pattern)
  | substituteProc (index : Nat) (replacement process : Pattern)
  | substituteList (index : Nat) (replacement : Pattern) (processes : List Pattern)
  | comm (body payload : Pattern)
  deriving DecidableEq, Repr

inductive Result where
  | pattern (value : Pattern)
  | patterns (values : List Pattern)
  | marked (name : Pattern) (matched : Bool)
  deriving DecidableEq, Repr

/-- Source meaning uses the independently defined rho functions. -/
def Task.meaning : Task → Result
  | .normalizeName n => .pattern (semanticNormalizeName n)
  | .normalizeProc p => .pattern (semanticNormalizeProc p)
  | .normalizeList ps => .patterns (semanticNormalizeProcList ps)
  | .substituteName k replacement name =>
      let marked := semanticSubstNameMark k replacement name
      .marked marked.1 marked.2
  | .substituteProc k replacement p => .pattern (semanticSubstProc k replacement p)
  | .substituteList k replacement ps => .patterns (semanticSubstProcList k replacement ps)
  | .comm body payload => .pattern (semanticCommSubst body payload)

/-- A literal call tree, containing no functions or proof fields. -/
inductive Certificate where
  | node (result : Result) (children : List Certificate)
  deriving Repr

def Certificate.result : Certificate → Result
  | .node result _ => result

/-- Recursive calls made by the independent source functions. This is a
specification of their call tree, not an operation used by replay. -/
def Task.calls : Task → List Task
  | .normalizeName (.apply "NQuote" [.apply "PDrop" [n]]) => [.normalizeName n]
  | .normalizeName (.apply "NQuote" [p]) => [.normalizeProc p]
  | .normalizeName _ => []
  | .normalizeProc (.apply "POutput" [n, q]) => [.normalizeName n, .normalizeProc q]
  | .normalizeProc (.apply "PInput" [n, .lambda none body]) => [.normalizeName n, .normalizeProc body]
  | .normalizeProc (.apply "PDrop" [n]) => [.normalizeName n]
  | .normalizeProc (.apply "NQuote" [p]) => [.normalizeProc p]
  | .normalizeProc (.lambda _ body) | .normalizeProc (.multiLambda _ _ body) => [.normalizeProc body]
  | .normalizeProc (.subst body replacement) => [.normalizeProc body, .normalizeProc replacement]
  | .normalizeProc (.collection _ ps _) => [.normalizeList ps]
  | .normalizeProc _ => []
  | .normalizeList [] => []
  | .normalizeList (p :: ps) => [.normalizeProc p, .normalizeList ps]
  | .substituteName _ _ name => [.normalizeName name]
  | .substituteProc _ _ (.bvar _) | .substituteProc _ _ (.fvar _)
  | .substituteProc _ _ (.apply "NQuote" [_]) => []
  | .substituteProc k replacement (.apply "PDrop" [name]) => [.substituteName k replacement name]
  | .substituteProc k replacement (.apply "POutput" [name, process]) =>
      [.substituteName k replacement name, .substituteProc k replacement process]
  | .substituteProc k replacement (.apply "PInput" [name, .lambda none process]) =>
      [.substituteName k replacement name, .substituteProc (k + 1) replacement process]
  | .substituteProc k replacement (.lambda _ body) => [.substituteProc (k + 1) replacement body]
  | .substituteProc k replacement (.multiLambda count _ body) => [.substituteProc (k + count) replacement body]
  | .substituteProc k replacement (.subst body value) =>
      [.substituteProc (k + 1) replacement body, .substituteProc k replacement value]
  | .substituteProc k replacement (.collection _ ps _) => [.substituteList k replacement ps]
  | .substituteProc _ _ _ => []
  | .substituteList _ _ [] => []
  | .substituteList k replacement (p :: ps) => [.substituteProc k replacement p, .substituteList k replacement ps]
  | .comm body payload => [.normalizeProc payload,
      .substituteProc 0 (.apply "NQuote" [semanticNormalizeProc payload]) body]

noncomputable def Task.weight : Task → Nat
  | .normalizeName p | .normalizeProc p => sizeOf p
  | .normalizeList ps => sizeOf ps
  | .substituteName _ _ p | .substituteProc _ _ p => 2 * sizeOf p + 1
  | .substituteList _ _ ps => 2 * sizeOf ps + 1
  | .comm body payload => 2 * sizeOf body + sizeOf payload + 5

theorem Task.calls_weight_lt {task child : Task} (member : child ∈ task.calls) :
    child.weight < task.weight := by
  fun_cases Task.calls task <;>
    simp only [Task.calls, List.mem_cons, List.not_mem_nil, or_false] at member
  all_goals rcases member with rfl | rfl
  all_goals simp only [Task.weight, Pattern.apply.sizeOf_spec, Pattern.lambda.sizeOf_spec,
    Pattern.multiLambda.sizeOf_spec, Pattern.subst.sizeOf_spec, Pattern.collection.sizeOf_spec,
    List.cons.sizeOf_spec]
  all_goals omega

/-- Construct the complete source call tree, including literal intermediate
results. Producers may execute the original functions; replay does not. -/
def derive (task : Task) : Certificate :=
  .node task.meaning (task.calls.attach.map fun child => derive child.1)
termination_by task.weight
decreasing_by exact Task.calls_weight_lt child.2

@[simp] theorem derive_result (task : Task) : (derive task).result = task.meaning := by
  rw [derive]
  rfl

/-- One constructor case. The child results are untrusted until replay checks
the returned tasks against the actual child certificates. -/
def unfoldCall : Task → List Result → Option (List Task × Result)
  | .normalizeName (.apply "NQuote" [.apply "PDrop" [n]]), [.pattern out] =>
      some ([.normalizeName n], .pattern out)
  | .normalizeName (.apply "NQuote" [p]), [.pattern out] =>
      some ([.normalizeProc p], .pattern (.apply "NQuote" [out]))
  | .normalizeName n, [] =>
      match n with
      | .apply "NQuote" [_] => none
      | _ => some ([], .pattern n)
  | .normalizeProc (.apply "POutput" [n, q]), [.pattern name, .pattern process] =>
      some ([.normalizeName n, .normalizeProc q], .pattern (.apply "POutput" [name, process]))
  | .normalizeProc (.apply "PInput" [n, .lambda none body]), [.pattern name, .pattern process] =>
      some ([.normalizeName n, .normalizeProc body], .pattern (.apply "PInput" [name, .lambda none process]))
  | .normalizeProc (.apply "PDrop" [n]), [.pattern name] =>
      some ([.normalizeName n], .pattern (.apply "PDrop" [name]))
  | .normalizeProc (.apply "NQuote" [p]), [.pattern process] =>
      some ([.normalizeProc p], .pattern (.apply "NQuote" [process]))
  | .normalizeProc (.lambda name body), [.pattern process] =>
      some ([.normalizeProc body], .pattern (.lambda name process))
  | .normalizeProc (.multiLambda count names body), [.pattern process] =>
      some ([.normalizeProc body], .pattern (.multiLambda count names process))
  | .normalizeProc (.subst body replacement), [.pattern process, .pattern value] =>
      some ([.normalizeProc body, .normalizeProc replacement], .pattern (.subst process value))
  | .normalizeProc (.collection kind processes rest), [.patterns values] =>
      some ([.normalizeList processes], .pattern (.collection kind values rest))
  | .normalizeProc p, [] =>
      match p with
      | .apply "POutput" [_, _] | .apply "PInput" [_, .lambda none _]
      | .apply "PDrop" [_] | .apply "NQuote" [_]
      | .lambda _ _ | .multiLambda _ _ _ | .subst _ _ | .collection _ _ _ => none
      | _ => some ([], .pattern p)
  | .normalizeList [], [] => some ([], .patterns [])
  | .normalizeList (p :: ps), [.pattern out, .patterns outs] =>
      some ([.normalizeProc p, .normalizeList ps], .patterns (out :: outs))
  | .substituteName k replacement name, [.pattern normalized] =>
      some ([.normalizeName name], match normalized with
        | .bvar n => if n == k then .marked replacement true else .marked (.bvar n) false
        | _ => .marked normalized false)
  | .substituteProc k replacement (.bvar n), [] =>
      some ([], .pattern (if n == k then replacement else .bvar n))
  | .substituteProc _ _ (.fvar name), [] => some ([], .pattern (.fvar name))
  | .substituteProc _ _ (.apply "NQuote" [p]), [] =>
      some ([], .pattern (.apply "NQuote" [p]))
  | .substituteProc k replacement (.apply "PDrop" [name]), [.marked out matched] =>
      some ([.substituteName k replacement name], .pattern (match out, matched with
        | .apply "NQuote" [p], true => p
        | _, _ => .apply "PDrop" [out]))
  | .substituteProc k replacement (.apply "POutput" [name, process]), [.marked out _, .pattern body] =>
      some ([.substituteName k replacement name, .substituteProc k replacement process],
        .pattern (.apply "POutput" [out, body]))
  | .substituteProc k replacement (.apply "PInput" [name, .lambda none process]), [.marked out _, .pattern body] =>
      some ([.substituteName k replacement name, .substituteProc (k + 1) replacement process],
        .pattern (.apply "PInput" [out, .lambda none body]))
  | .substituteProc k replacement (.lambda name body), [.pattern out] =>
      some ([.substituteProc (k + 1) replacement body], .pattern (.lambda name out))
  | .substituteProc k replacement (.multiLambda count names body), [.pattern out] =>
      some ([.substituteProc (k + count) replacement body], .pattern (.multiLambda count names out))
  | .substituteProc k replacement (.subst body value), [.pattern out, .pattern outValue] =>
      some ([.substituteProc (k + 1) replacement body, .substituteProc k replacement value],
        .pattern (.subst out outValue))
  | .substituteProc k replacement (.collection kind ps rest), [.patterns outs] =>
      some ([.substituteList k replacement ps], .pattern (.collection kind outs rest))
  | .substituteProc _ _ p, [] =>
      match p with
      | .bvar _ | .fvar _ | .apply "NQuote" [_] | .apply "PDrop" [_]
      | .apply "POutput" [_, _] | .apply "PInput" [_, .lambda none _]
      | .lambda _ _ | .multiLambda _ _ _ | .subst _ _ | .collection _ _ _ => none
      | _ => some ([], .pattern p)
  | .substituteList _ _ [], [] => some ([], .patterns [])
  | .substituteList k replacement (p :: ps), [.pattern out, .patterns outs] =>
      some ([.substituteProc k replacement p, .substituteList k replacement ps], .patterns (out :: outs))
  | .comm body payload, [.pattern normalized, .pattern out] =>
      some ([.normalizeProc payload, .substituteProc 0 (.apply "NQuote" [normalized]) body], .pattern out)
  | _, _ => none

mutual
  /-- Total replay follows the submitted finite tree, checking every child. -/
  def checkTask (task : Task) : Certificate → Bool
    | .node result children =>
        match unfoldCall task (children.map Certificate.result) with
        | none => false
        | some (requests, expected) => decide (result = expected) && checkChildren requests children

  def checkChildren : List Task → List Certificate → Bool
    | [], [] => true
    | task :: tasks, certificate :: certificates =>
        checkTask task certificate && checkChildren tasks certificates
    | _, _ => false
end

theorem unfoldCall_sound {task : Task} {results : List Result} {requests : List Task} {out : Result}
    (expanded : unfoldCall task results = some (requests, out))
    (children : List.Forall₂ (fun task result => task.meaning = result) requests results) :
    task.meaning = out := by
  fun_cases unfoldCall task results <;>
    simp_all only [unfoldCall, Option.some.injEq, Prod.mk.injEq]
  all_goals rcases expanded with ⟨rfl, rfl⟩
  all_goals
    simp_all [Task.meaning, semanticNormalizeName, semanticNormalizeProc,
      semanticNormalizeProcList, semanticSubstNameMark, semanticSubstName,
      semanticSubstProc, semanticSubstProcList, semanticCommSubst]
  case case4 name excluded =>
    cases name using semanticNormalizeName.fun_cases <;>
      simp_all [semanticNormalizeName.eq_1, semanticNormalizeName.eq_2, semanticNormalizeName.eq_5]
  case case21 process a b c d e f g h =>
    cases process using semanticNormalizeProc.fun_cases <;>
      simp_all [semanticNormalizeProc.eq_1, semanticNormalizeProc.eq_2, semanticNormalizeProc.eq_11]
  case case24 index replacement name normalized =>
    cases normalized <;> simp only []
    split_ifs <;> rfl
  case case28 => rfl

mutual
  theorem checkTask_sound (task : Task) (evidence : Certificate)
      (accepted : checkTask task evidence = true) : task.meaning = evidence.result := by
    cases evidenceEq : evidence with
    | node result children =>
      rw [evidenceEq] at accepted
      cases expanded : unfoldCall task (children.map Certificate.result) with
      | none => simp [checkTask, expanded] at accepted
      | some pair =>
        obtain ⟨requests, expected⟩ := pair
        have checked : result = expected ∧ checkChildren requests children = true := by
          simpa only [checkTask, expanded, Bool.and_eq_true, decide_eq_true_eq] using accepted
        exact (unfoldCall_sound expanded (checkChildren_sound requests children checked.2)).trans
          checked.1.symm
  termination_by sizeOf evidence
  decreasing_by simp_all [Certificate.node.sizeOf_spec]

  theorem checkChildren_sound (tasks : List Task) (evidence : List Certificate)
      (accepted : checkChildren tasks evidence = true) :
      List.Forall₂ (fun task result => task.meaning = result) tasks (evidence.map Certificate.result) := by
    cases tasks with
    | nil => cases evidence <;> simp_all [checkChildren]
    | cons task tasks =>
      cases evidenceEq : evidence with
      | nil => simp [evidenceEq, checkChildren] at accepted
      | cons certificate certificates =>
        rw [evidenceEq] at accepted
        have checked : checkTask task certificate = true ∧ checkChildren tasks certificates = true := by
          simpa only [checkChildren, Bool.and_eq_true] using accepted
        exact .cons (checkTask_sound task certificate checked.1)
          (checkChildren_sound tasks certificates checked.2)
  termination_by sizeOf evidence
  decreasing_by all_goals simp_all [List.cons.sizeOf_spec] <;> omega
end

theorem unfoldCall_source (task : Task) :
    unfoldCall task (task.calls.map Task.meaning) = some (task.calls, task.meaning) := by
  fun_cases Task.calls task <;>
    simp_all [Task.meaning, unfoldCall,
      semanticNormalizeName, semanticNormalizeProc, semanticNormalizeProcList,
      semanticSubstNameMark, semanticSubstName, semanticSubstProc,
      semanticSubstProcList, semanticCommSubst]
  case case3 name excluded =>
    cases name using semanticNormalizeName.fun_cases <;>
      simp_all [semanticNormalizeName.eq_1, semanticNormalizeName.eq_2, semanticNormalizeName.eq_5]
  case case12 process a b c d e f g h =>
    cases process using semanticNormalizeProc.fun_cases <;>
      simp_all [semanticNormalizeProc.eq_1, semanticNormalizeProc.eq_2, semanticNormalizeProc.eq_11]
  case case15 index replacement name =>
    cases normalized : semanticNormalizeName name <;> simp only []
    split_ifs <;> rfl
  case case19 => rfl

theorem unfoldCall_requests {task : Task} {results : List Result} {requests : List Task} {out : Result}
    (expanded : unfoldCall task results = some (requests, out))
    (children : List.Forall₂ (fun task result => task.meaning = result) requests results) :
    requests = task.calls := by
  fun_cases unfoldCall task results <;>
    simp_all only [unfoldCall, Option.some.injEq, Prod.mk.injEq]
  all_goals rcases expanded with ⟨rfl, rfl⟩
  all_goals simp_all [Task.calls, Task.meaning]

/-- A source call tree has the original function's literal result and exactly
its recursive source calls, in their original positions. -/
inductive Certificate.Valid : Task → Certificate → Prop where
  | node {task : Task} {result : Result} {children : List Certificate}
      (result_exact : task.meaning = result)
      (children_valid : List.Forall₂ Certificate.Valid task.calls children) :
      Certificate.Valid task (.node result children)

theorem Certificate.Valid.result_exact {task : Task} {evidence : Certificate}
    (valid : evidence.Valid task) : task.meaning = evidence.result := by
  cases valid with
  | node result_exact _ => exact result_exact

private theorem validChildren_results {tasks : List Task} {evidence : List Certificate}
    (valid : List.Forall₂ Certificate.Valid tasks evidence) :
    evidence.map Certificate.result = tasks.map Task.meaning := by
  induction valid with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, ← head.result_exact, ih]

mutual
  theorem checkTask_valid (task : Task) (evidence : Certificate)
      (accepted : checkTask task evidence = true) : evidence.Valid task := by
    cases evidenceEq : evidence with
    | node result children =>
      rw [evidenceEq] at accepted
      cases expanded : unfoldCall task (children.map Certificate.result) with
      | none => simp [checkTask, expanded] at accepted
      | some pair =>
        obtain ⟨requests, expected⟩ := pair
        have checked : result = expected ∧ checkChildren requests children = true := by
          simpa only [checkTask, expanded, Bool.and_eq_true, decide_eq_true_eq] using accepted
        have sourceChildren := checkChildren_sound requests children checked.2
        have sameCalls := unfoldCall_requests expanded sourceChildren
        exact .node ((unfoldCall_sound expanded sourceChildren).trans checked.1.symm)
          (sameCalls ▸ checkChildren_valid requests children checked.2)
  termination_by sizeOf evidence
  decreasing_by simp_all [Certificate.node.sizeOf_spec]

  theorem checkChildren_valid (tasks : List Task) (evidence : List Certificate)
      (accepted : checkChildren tasks evidence = true) :
      List.Forall₂ Certificate.Valid tasks evidence := by
    cases tasks with
    | nil => cases evidence <;> simp_all [checkChildren]
    | cons task tasks =>
      cases evidenceEq : evidence with
      | nil => simp [evidenceEq, checkChildren] at accepted
      | cons certificate certificates =>
        rw [evidenceEq] at accepted
        have checked : checkTask task certificate = true ∧ checkChildren tasks certificates = true := by
          simpa only [checkChildren, Bool.and_eq_true] using accepted
        exact .cons (checkTask_valid task certificate checked.1)
          (checkChildren_valid tasks certificates checked.2)
  termination_by sizeOf evidence
  decreasing_by all_goals simp_all [List.cons.sizeOf_spec] <;> omega
end

mutual
  theorem Certificate.Valid.checked (task : Task) (evidence : Certificate)
      (valid : evidence.Valid task) : checkTask task evidence = true := by
    cases evidenceEq : evidence with
    | node result children =>
      rw [evidenceEq] at valid
      cases valid with
      | node result_exact children_valid =>
        have results := validChildren_results children_valid
        have checked := validChildren_checked task.calls children children_valid
        simp only [checkTask, results, unfoldCall_source, result_exact, decide_true, Bool.true_and]
        exact checked
  termination_by sizeOf evidence
  decreasing_by simp_all [Certificate.node.sizeOf_spec]

  theorem validChildren_checked (tasks : List Task) (evidence : List Certificate)
      (valid : List.Forall₂ Certificate.Valid tasks evidence) :
      checkChildren tasks evidence = true := by
    cases evidenceEq : evidence with
    | nil =>
      rw [evidenceEq] at valid
      cases valid
      rfl
    | cons certificate certificates =>
      rw [evidenceEq] at valid
      cases valid with
      | cons head tail =>
        simp only [checkChildren, Bool.and_eq_true]
        exact ⟨head.checked _ _, validChildren_checked _ _ tail⟩
  termination_by sizeOf evidence
  decreasing_by all_goals simp_all [List.cons.sizeOf_spec] <;> omega
end

theorem checkTask_exact (task : Task) (evidence : Certificate) :
    checkTask task evidence = true ↔ evidence.Valid task :=
  ⟨checkTask_valid task evidence, Certificate.Valid.checked task evidence⟩

theorem Task.calls_length_le_two (task : Task) : task.calls.length ≤ 2 := by
  fun_cases Task.calls task <;> simp_all

private theorem checkChildren_map (tasks : List Task) (produce : Task → Certificate)
    (accepted : ∀ task ∈ tasks, checkTask task (produce task) = true) :
    checkChildren tasks (tasks.map produce) = true := by
  induction tasks with
  | nil => rfl
  | cons task tasks ih =>
      simp only [List.map_cons, checkChildren]
      rw [accepted task (by simp)]
      simp only [Bool.true_and]
      exact ih (fun child member => accepted child (by simp [member]))

theorem checkTask_derive (task : Task) : checkTask task (derive task) = true := by
  rw [derive]
  simp only [checkTask, List.map_map, Function.comp_def, derive_result, List.attach_map_val,
    unfoldCall_source, decide_true, Bool.true_and]
  apply checkChildren_map
  intro child member
  exact checkTask_derive child
termination_by task.weight
decreasing_by exact Task.calls_weight_lt member

/-- Check explicit evidence of the literal COMM contractum. -/
def check (body payload result : Pattern) (evidence : Certificate) : Bool :=
  checkTask (.comm body payload) evidence && decide (evidence.result = .pattern result)

theorem check_exact (body payload result : Pattern) (evidence : Certificate) :
    check body payload result evidence = true ↔
      evidence.Valid (.comm body payload) ∧ evidence.result = .pattern result := by
  simp only [check, Bool.and_eq_true, checkTask_exact, decide_eq_true_eq]

theorem check_sound (body payload result : Pattern) (evidence : Certificate)
    (accepted : check body payload result evidence = true) :
    semanticCommSubst body payload = result := by
  have checked : checkTask (.comm body payload) evidence = true ∧ evidence.result = .pattern result := by
    simpa only [check, Bool.and_eq_true, decide_eq_true_eq] using accepted
  exact Result.pattern.inj ((checkTask_sound (.comm body payload) evidence checked.1).trans checked.2)

def certificate (body payload : Pattern) : Certificate := derive (.comm body payload)

theorem check_certificate (body payload : Pattern) :
    check body payload (semanticCommSubst body payload) (certificate body payload) = true := by
  simp only [check, certificate, checkTask_derive, derive_result, Task.meaning, decide_true, Bool.true_and]

theorem check_complete (body payload result : Pattern) :
    (∃ evidence, check body payload result evidence = true) ↔ semanticCommSubst body payload = result := by
  constructor
  · rintro ⟨evidence, accepted⟩
    exact check_sound body payload result evidence accepted
  · intro source
    subst result
    exact ⟨certificate body payload, check_certificate body payload⟩

theorem bare_result_refused (body payload result : Pattern) :
    check body payload result (.node (.pattern result) []) = false := by
  simp only [check, checkTask, unfoldCall, List.map_nil, Bool.false_and]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.SemanticSubstitutionEvidence
