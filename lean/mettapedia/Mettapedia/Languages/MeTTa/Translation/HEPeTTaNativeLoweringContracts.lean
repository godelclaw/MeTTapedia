import Mettapedia.Languages.MeTTa.OSLFCore.Atom
import Mettapedia.Languages.MeTTa.HE.BindingComposition
import Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps
import Mettapedia.Languages.MeTTa.HE.Spec.Match.Completeness
import Mettapedia.Languages.MeTTa.HE.EquationScope
import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics
import Mettapedia.Languages.MeTTa.PeTTa.EagerDFS
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory
open Mettapedia.Languages.MeTTa.HE.BindingComposition
open Mettapedia.Languages.MeTTa.HE.MatchSizeTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport

/-!
# HE to PeTTa Native Lowering Contracts

Contracts for the native-first HE to PeTTa lowering boundary. The decidable
predicates identify when lowering may use native PeTTa directly and when it
must keep the compatibility path. The constructor-matching bridge connects
actual PeTTa selection to the HE query matcher and one complete pending-tuple
readout. The complete clause-frontier comparison additionally preserves open
caller constraints, fresh instances, source-copy multiplicity and pending
caller work. Reached-store refinement laws preserve and reflect the next
sibling match, and certified materialization preserves one joint observation
of the entire pending packet after that refinement. Complete clause selection
uses agreement on solutions, so the same law applies after a preceding child
changes the constraint representation. These laws do not assert recursive
whole-program adequacy.
-/

namespace Mettapedia.Languages.MeTTa.Translation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

mutual
  def isLogicVar : Atom → Bool
    | .var _ => true
    | .expression xs => isLogicVarList xs
    | _ => false

  def isLogicVarList : List Atom → Bool
    | [] => false
    | x :: xs => isLogicVar x || isLogicVarList xs
end

def isNativeNumberLiteral : Atom → Bool
  | .grounded (.int _) => true
  | _ => false

def nativeNumericHead (head : String) : Bool :=
  head == "+" || head == "-" || head == "*" || head == "/" ||
    head == "%" || head == "<" || head == ">"

def safeNativeNumericCall : Atom → Bool
  | .expression (.symbol head :: args) =>
      nativeNumericHead head && args.all isNativeNumberLiteral
  | _ => false

def reservedPeTTaDataHead : String → Bool
  | "Predicate" => true
  | _ => false

mutual
  def containsReservedDataHead : Atom → Bool
    | .expression (.symbol head :: args) =>
        reservedPeTTaDataHead head || containsReservedDataHeadList args
    | .expression xs => containsReservedDataHeadList xs
    | _ => false

  def containsReservedDataHeadList : List Atom → Bool
    | [] => false
    | x :: xs => containsReservedDataHead x || containsReservedDataHeadList xs
end

def safeNativeDataEquality : Atom → Bool
  | .expression [.symbol "==", left, right] =>
      !isLogicVar left && !isLogicVar right &&
        !containsReservedDataHead left && !containsReservedDataHead right
  | .expression [.symbol "!=", left, right] =>
      !isLogicVar left && !isLogicVar right &&
        !containsReservedDataHead left && !containsReservedDataHead right
  | _ => false

def renameReservedDataHead : Atom → Atom
  | .expression (.symbol "Predicate" :: args) =>
      .expression (.symbol "Predicate-he" :: args.map renameReservedDataHead)
  | .expression xs => .expression (xs.map renameReservedDataHead)
  | other => other

def headSymbol? : Atom → Option String
  | .expression (.symbol head :: _) => some head
  | _ => none

def sourceHeadNeedsCompat (sourceHeads : List String) (a : Atom) : Bool :=
  match headSymbol? a with
  | some head => sourceHeads.contains head && !safeNativeNumericCall a
  | none => false

def b2DeduceAndKernelRule : Atom :=
  .expression
    [.symbol "=", .expression [.symbol "deduce", .expression [.symbol "And", .var "$a", .var "$b"]],
      .expression [.symbol "And",
        .expression [.symbol "deduce", .var "$a"],
        .expression [.symbol "deduce", .var "$b"]]]

def obsoleteBoolAndRule : Atom :=
  .expression
    [.symbol "=", .expression [.symbol "And", .symbol "T", .symbol "T"], .symbol "T"]

mutual
  def containsAndTerm : Atom → Bool
    | .expression (.symbol "And" :: _ :: _) => true
    | .expression xs => containsAndTermList xs
    | _ => false

  def containsAndTermList : List Atom → Bool
    | [] => false
    | x :: xs => containsAndTerm x || containsAndTermList xs
end

def hasDeduceAndKernelRule (atoms : List Atom) : Bool :=
  atoms.contains b2DeduceAndKernelRule

def hasObsoleteBoolAndRule (atoms : List Atom) : Bool :=
  atoms.contains obsoleteBoolAndRule

def hasLiveValueAndUse : List Atom → Bool
  | [] => false
  | atom :: rest =>
      if atom == b2DeduceAndKernelRule || atom == obsoleteBoolAndRule then
        hasLiveValueAndUse rest
      else
        match atom with
        | .expression [.symbol "=", _, rhs] =>
            containsAndTerm rhs || hasLiveValueAndUse rest
        | .expression (.symbol "!" :: expr :: _) =>
            containsAndTerm expr || hasLiveValueAndUse rest
        | _ => hasLiveValueAndUse rest

def shouldDropDeadBoolAndHelper (atoms : List Atom) : Bool :=
  hasDeduceAndKernelRule atoms &&
    hasObsoleteBoolAndRule atoms &&
    !hasLiveValueAndUse atoms

def d4DirectTruthRule : Atom :=
  .expression
    [.symbol "=", .expression [.symbol "=-he", .var "$type", .symbol "T"],
      .expression
        [.symbol "match", .symbol "&self",
          .expression [.symbol ":", .var "$x", .var "$type"],
          .symbol "T"]]

def d4ImplicationTruthRule : Atom :=
  .expression
    [.symbol "=", .expression [.symbol "=-he", .var "$type", .symbol "T"],
      .expression
        [.symbol "match", .symbol "&self",
          .expression
            [.symbol ":", .var "$impl",
              .expression [.symbol "->", .var "$cause", .var "$type"]],
          .expression
            [.symbol "if",
              .expression [.symbol "==", .var "$cause", .var "$type"],
              .expression [.symbol "empty"],
              .expression [.symbol "=-he", .var "$cause", .symbol "T"]]]]

def d4GuardedImplicationTruthRule : Atom :=
  .expression
    [.symbol "=", .expression [.symbol "=-he", .var "$type", .symbol "T"],
      .expression
        [.symbol "let", .var "$direct",
          .expression
            [.symbol "collapse",
              .expression
                [.symbol "match", .symbol "&self",
                  .expression [.symbol ":", .var "$witness", .var "$type"],
                  .symbol "T"]],
          .expression
            [.symbol "if",
              .expression [.symbol "==", .var "$direct", .expression []],
              .expression
                [.symbol "let", .var "$cause",
                  .expression
                    [.symbol "match", .symbol "&self",
                      .expression
                        [.symbol ":", .var "$impl",
                          .expression [.symbol "->", .var "$cause", .var "$type"]],
                      .var "$cause"],
                  .expression
                    [.symbol "if",
                      .expression [.symbol "==", .var "$cause", .var "$type"],
                      .expression [.symbol "empty"],
                      .expression
                        [.symbol "call-or-inert",
                          .expression
                            [.symbol "quote",
                              .expression [.symbol "=-he", .var "$cause", .symbol "T"]]]]],
              .expression [.symbol "empty"]]]]

def guardedImplicationTruthRuleShape : Atom → Bool
  | .expression
      [.symbol "=", .expression [.symbol "=-he", .var "$type", .symbol "T"],
        .expression
          [.symbol "let", .var "$direct",
            .expression
              [.symbol "collapse",
                .expression
                  [.symbol "match", .symbol "&self",
                    .expression [.symbol ":", .var "$witness", .var "$type"],
                    .symbol "T"]],
            .expression
              [.symbol "if",
                .expression [.symbol "==", .var "$direct", .expression []],
                .expression
                  [.symbol "let", .var "$cause",
                    .expression
                      [.symbol "match", .symbol "&self",
                        .expression
                          [.symbol ":", .var "$impl",
                            .expression [.symbol "->", .var "$cause", .var "$type"]],
                        .var "$cause"],
                    .expression
                      [.symbol "if",
                        .expression [.symbol "==", .var "$cause", .var "$type"],
                        .expression [.symbol "empty"],
                        .expression
                          [.symbol "call-or-inert",
                            .expression
                              [.symbol "quote",
                                .expression [.symbol "=-he", .var "$cause", .symbol "T"]]]]],
                .expression [.symbol "empty"]]]] => true
  | _ => false

def intAtom (n : Int) : Atom := .grounded (.int n)

example :
    safeNativeNumericCall
      (.expression [.symbol "+", intAtom 2, intAtom 1]) = true := by
  decide

example :
    safeNativeNumericCall
      (.expression [.symbol "+", .var "$x", intAtom 1]) = false := by
  decide

example :
    safeNativeDataEquality
      (.expression [.symbol "==", .symbol "A", .symbol "A"]) = true := by
  decide

example :
    safeNativeDataEquality
      (.expression [.symbol "==",
        .expression [.symbol "Predicate", .symbol "P"],
        .expression [.symbol "Predicate", .symbol "P"]]) = false := by
  decide

example :
    renameReservedDataHead
      (.expression [.symbol "Evaluation",
        .expression [.symbol "Predicate", .symbol "P"]]) =
      (.expression [.symbol "Evaluation",
        .expression [.symbol "Predicate-he", .symbol "P"]]) := by
  simp [renameReservedDataHead]

example :
    sourceHeadNeedsCompat ["foo"]
      (.expression [.symbol "foo", .symbol "B"]) = true := by
  decide

example :
    sourceHeadNeedsCompat ["foo"]
      (.expression [.symbol "+", intAtom 2, intAtom 1]) = false := by
  decide

def b2RuleDataAnd : Atom :=
  .expression
    [.symbol "Implication",
      .expression [.symbol "And",
        .expression [.symbol "Evaluation", .expression [.symbol "philosopher", .var "$x"]],
        .expression [.symbol "Evaluation", .expression [.symbol "likes-to-wrestle", .var "$x"]]],
      .expression [.symbol "Evaluation", .expression [.symbol "human", .var "$x"]]]

example :
    shouldDropDeadBoolAndHelper
      [b2RuleDataAnd, b2DeduceAndKernelRule, obsoleteBoolAndRule] = true := by
  decide

example :
    shouldDropDeadBoolAndHelper
      [b2RuleDataAnd, b2DeduceAndKernelRule, obsoleteBoolAndRule,
        .expression [.symbol "=", .expression [.symbol "pair"],
          .expression [.symbol "And", .symbol "A", .symbol "B"]]] = false := by
  decide

example :
    guardedImplicationTruthRuleShape d4GuardedImplicationTruthRule = true := by
  decide

example :
    guardedImplicationTruthRuleShape d4ImplicationTruthRule = false := by
  decide

example :
    guardedImplicationTruthRuleShape d4DirectTruthRule = false := by
  decide

end Mettapedia.Languages.MeTTa.Translation

namespace Mettapedia.Languages.MeTTa.Translation.ConstructorMatch

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi
open private lookup_ground hasAssignedVar_false_of_ground mergeGround?
  mergeBindings_ground_eq_mergeGround matchAtoms_mono_add matchAtoms_ground_canon
  from Mettapedia.Languages.MeTTa.HE.BindingComposition

open PeTTa.EagerDFS.Destination

/-- A PeTTa source clause instance is also a legal HE source instance whenever
the retained PeTTa scope contains the HE caller's visible names. The two
languages retain their existing, independent freshness contracts. -/
theorem petta_fresh_instance_he_alpha
    {control : Control} {equation : PeTTa.SpaceSemantics.Equation}
    {left body query : Atom} {live : List Atom} {incoming : HE.Bindings}
    (freshened : ClauseChoice.FreshInstance control equation left body)
    (covered : ∀ name,
      HE.Spec.Eval.Steps.QueryVisibleName live query incoming name → name ∈ control.support) :
    HE.Spec.Eval.Steps.AlphaVariantRel live query incoming
      (ClauseChoice.pattern equation) equation.body left body := by
  obtain ⟨renamer,injective,fresh,rfl,rfl⟩ := freshened
  apply HE.Spec.Eval.Steps.AlphaVariantRel.of_injOn renamer
  · simpa only [ClauseChoice.names,ClauseChoice.clauseAtoms,List.flatMap_cons,
      List.flatMap_nil,List.append_nil] using injective
  · intro name occurs visible
    have member : name ∈ ClauseChoice.names (ClauseChoice.clauseAtoms equation) := by
      simp only [ClauseChoice.names,ClauseChoice.clauseAtoms,List.flatMap_cons,
        List.flatMap_nil,List.append_nil,List.mem_append]
      exact occurs.elim (fun occurrence => Or.inl (HE.Spec.Eval.Steps.atomOccurs_mem_typeVars occurrence))
        (fun occurrence => Or.inr (HE.Spec.Eval.Steps.atomOccurs_mem_typeVars occurrence))
    exact fresh name member (covered _ visible)

/-- The actual retained clause allocator supplies that shared source instance
at every equation position. Protecting the finite HE caller support leaves
the PeTTa equations, bindings, goals and committed-choice boundary intact. -/
theorem protected_petta_clause_he_alpha
    (control : Control) (position : Nat) (equation : PeTTa.SpaceSemantics.Equation)
    (live : List Atom) (query : Atom) (incoming : HE.Bindings) :
    let guarded := protectControl control (HE.EquationScope.visibleNames live query incoming).toFinset
    HE.Spec.Eval.Steps.AlphaVariantRel live query incoming
      (ClauseChoice.pattern equation) equation.body
      (ClauseChoice.freshPattern guarded position equation)
      (ClauseChoice.freshBody guarded position equation) := by
  apply petta_fresh_instance_he_alpha (ClauseChoice.fresh_clause_instance _ _ _)
  intro name visible
  rw [protectControl_support]
  exact Finset.mem_union_right _ (List.mem_toFinset.mpr
    ((HE.EquationScope.mem_visibleNames_iff live query incoming name).mpr visible))

/-- One HE source candidate and the corresponding PeTTa reached equations
have identical solution theories. This includes all incoming aliases and all
future observations of the resulting store, not just one selected value. -/
theorem he_candidate_petta_solutions
    {query pattern : Atom} {incoming output : HE.Bindings}
    (candidate : HE.Spec.Eval.Steps.UnifyCandidateRel query pattern incoming output)
    (environment : Environment) :
    HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied
        (fun name => decode (environment name)) output ↔
      Solves environment (HE.Spec.Type.Presentation.BindingTheory.bindingAtomEquations incoming ++
        [(query,pattern)]) := by
  rw [candidate.solutions,solves_append_equation,solves_binding_equations]
  simp only [read_eq_applyTypeValuation]
  exact and_comm

/-- Accepted matching agrees at the independent source constraint boundary,
including open queries and alias-bearing callers. The HE derivation is
constructed from the PeTTa model; no evaluator or search-result oracle is a
premise. Conversely the HE conjunction supplies an actual PeTTa model. -/
theorem petta_accepted_iff_he_candidate (incoming : HE.Bindings) (query pattern : Atom) :
    (∃ after, Refinement
      (HE.Spec.Type.Presentation.BindingTheory.bindingAtomEquations incoming)
      query pattern (some after)) ↔
    ∃ output, HE.Spec.Eval.Steps.UnifyCandidateRel query pattern incoming output := by
  constructor
  · rintro ⟨after,accepted⟩
    cases accepted with
    | accepted environment old new =>
        let valuation : String → Atom := fun name => decode (environment name)
        have equation : HE.Spec.Type.RuntimeRefinement.applyTypeValuation valuation query =
            HE.Spec.Type.RuntimeRefinement.applyTypeValuation valuation pattern := by
          simpa only [read_eq_applyTypeValuation] using new
        have encoded : HE.Spec.Match.SolutionTheory.HEAtomEquationSatisfied
            (fun name => HE.Spec.Match.SolutionTheory.encodeModelAtom (valuation name)) query pattern := by
          unfold HE.Spec.Match.SolutionTheory.HEAtomEquationSatisfied
          rw [← HE.Spec.Bindings.ScopeObservation.ModelTransport.encodeModelAtom_applyTypeValuation,
            ← HE.Spec.Bindings.ScopeObservation.ModelTransport.encodeModelAtom_applyTypeValuation,equation]
        obtain ⟨matched,matching,model⟩ :=
          HE.Spec.Match.Completeness.exists_specMatch_of_solution encoded
        let output : HE.Bindings :=
          ⟨matched.assignments ++ incoming.assignments,matched.equalities ++ incoming.equalities⟩
        refine ⟨output,matched,matching,?_⟩
        exact HE.Spec.Bindings.ScopeObservation.LogicalMergeRel.append_of_common_model
          ⟨valuation,(HE.Spec.Bindings.ScopeObservation.ModelTransport.specTypeBindingSatisfied_iff_heBindingSatisfied_translated
            valuation matched).mpr model,
            (solves_binding_equations environment incoming).mp old⟩
  · rintro ⟨output,candidate⟩
    have model : ∃ valuation, HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation output := by
      obtain ⟨_matched,_matching,merged⟩ := candidate
      exact merged.2
    obtain ⟨valuation,satisfied⟩ := model
    let environment : Environment := fun name => encode (valuation name)
    have actual : HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied
        (fun name => decode (environment name)) output := by
      simpa only [environment,decode_encode] using satisfied
    have solved := (he_candidate_petta_solutions candidate environment).mp actual
    obtain ⟨old,new⟩ := (solves_append_equation _ _ _ _).mp solved
    exact ⟨_,.accepted environment old new⟩

/-- A refused PeTTa attempt is precisely absence of any satisfiable HE source
candidate at that same fresh instance. Budget exhaustion is not involved. -/
theorem petta_refused_iff_no_he_candidate (incoming : HE.Bindings) (query pattern : Atom) :
    Refinement (HE.Spec.Type.Presentation.BindingTheory.bindingAtomEquations incoming)
        query pattern none ↔
      ¬∃ output, HE.Spec.Eval.Steps.UnifyCandidateRel query pattern incoming output := by
  rw [← petta_accepted_iff_he_candidate]
  constructor
  · intro refused ⟨after,accepted⟩
    cases refused with
    | refused absent =>
        cases accepted with
        | accepted environment old new => exact absent ⟨environment,old,new⟩
  · intro absent
    apply Refinement.refused
    rintro ⟨environment,old,new⟩
    exact absent ⟨_,.accepted environment old new⟩

/-- A continuation starts in the theory reached by its head. The PeTTa
equations need not be the literal encoding of the HE record: all aliases
and earlier destination equations are carried by their common solutions. -/
theorem he_candidate_petta_reached_solutions
    {query pattern : Atom} {incoming output : HE.Bindings} {before : Equations}
    (related : ∀ environment, HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied
      (fun name => decode (environment name)) incoming ↔ Solves environment before)
    (candidate : HE.Spec.Eval.Steps.UnifyCandidateRel query pattern incoming output)
    (environment : Environment) :
    HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied
        (fun name => decode (environment name)) output ↔
      Solves environment (before ++ [(query,pattern)]) := by
  rw [candidate.solutions,solves_append_equation,← related environment]
  simp only [read_eq_applyTypeValuation]
  exact and_comm

/-- Matching the next operand preserves and reflects acceptance from any
related reached stores. In particular it cannot restart from the caller's
earlier, weaker constraints. -/
theorem petta_reached_accepted_iff_he_candidate
    {incoming : HE.Bindings} {before : Equations}
    (related : ∀ environment, HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied
      (fun name => decode (environment name)) incoming ↔ Solves environment before)
    (query pattern : Atom) :
    (∃ after, Refinement before query pattern (some after)) ↔
      ∃ output, HE.Spec.Eval.Steps.UnifyCandidateRel query pattern incoming output := by
  rw [← petta_accepted_iff_he_candidate]
  constructor
  · rintro ⟨_,accepted⟩
    cases accepted with
    | accepted environment old new =>
        exact ⟨_,.accepted environment
          ((solves_binding_equations environment incoming).mpr ((related environment).mpr old)) new⟩
  · rintro ⟨_,accepted⟩
    cases accepted with
    | accepted environment old new =>
        exact ⟨_,.accepted environment
          ((related environment).mp ((solves_binding_equations environment incoming).mp old)) new⟩

/-- A successful source refinement constructs the next HE candidate and
the full reached-store relation required by the following continuation.
This is a local operation law, with no evaluator-correctness premise. -/
theorem petta_reached_refinement
    {incoming : HE.Bindings} {before after : Equations} {query pattern : Atom}
    (related : ∀ environment, HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied
      (fun name => decode (environment name)) incoming ↔ Solves environment before)
    (accepted : Refinement before query pattern (some after)) :
    ∃ output, HE.Spec.Eval.Steps.UnifyCandidateRel query pattern incoming output ∧
      ∀ environment, HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied
        (fun name => decode (environment name)) output ↔ Solves environment after := by
  obtain ⟨output,candidate⟩ :=
    (petta_reached_accepted_iff_he_candidate related query pattern).mp ⟨after,accepted⟩
  cases accepted
  exact ⟨output,candidate,he_candidate_petta_reached_solutions related candidate⟩

/-- A refused sibling has no candidate under the reached head constraints.
This rules out a completed answer; it is not a statement about an unfinished
search prefix. -/
theorem petta_reached_refused_iff_no_he_candidate
    {incoming : HE.Bindings} {before : Equations}
    (related : ∀ environment, HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied
      (fun name => decode (environment name)) incoming ↔ Solves environment before)
    (query pattern : Atom) :
    Refinement before query pattern none ↔
      ¬∃ output, HE.Spec.Eval.Steps.UnifyCandidateRel query pattern incoming output := by
  rw [← petta_reached_accepted_iff_he_candidate related]
  constructor
  · intro refused ⟨_,accepted⟩
    cases refused with
    | refused absent =>
        cases accepted with
        | accepted environment old new => exact absent ⟨environment,old,new⟩
  · intro absent
    apply Refinement.refused
    rintro ⟨environment,old,new⟩
    exact absent ⟨_,.accepted environment old new⟩

/-- The whole pending packet is read in one model. It may include caller
variables, already returned values and unevaluated siblings, with repeated
variables in any positions. Equal marginals would not suffice here. -/
theorem reached_pending_observations
    {bindings : HE.Bindings} {source : Equations}
    (related : ∀ environment, HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied
      (fun name => decode (environment name)) bindings ↔ Solves environment source)
    (pending : List Atom) :
    HE.Spec.Bindings.ScopeObservation.observedTuples bindings pending =
      solutionTuples source pending := by
  ext values
  constructor
  · rintro ⟨valuation,model,returned⟩
    let environment : Environment := fun name => encode (valuation name)
    have same : (fun name => decode (environment name)) = valuation := by
      funext name
      exact decode_encode (valuation name)
    refine ⟨environment,(related environment).mp (by simpa only [same] using model),?_⟩
    rw [show read environment = _ from funext (read_eq_applyTypeValuation environment),same]
    exact returned
  · rintro ⟨environment,model,returned⟩
    exact ⟨fun name => decode (environment name),(related environment).mpr model,
      by simpa only [show read environment = _ from
        funext (read_eq_applyTypeValuation environment)] using returned⟩

/-- Assembling an evaluated prefix preserves its correlations with the
remaining packet. The two prefixes may use different private names, but
must occupy the same number of joint coordinates. -/
theorem joint_packet_assemble_prefix
    {incoming : HE.Bindings} {before : Equations}
    {prefixValues pending sourcePrefix sourcePending : List Atom}
    (lengths : prefixValues.length = sourcePrefix.length)
    (related : HE.Spec.Bindings.ScopeObservation.observedTuples incoming (prefixValues ++ pending) =
      solutionTuples before (sourcePrefix ++ sourcePending)) :
    HE.Spec.Bindings.ScopeObservation.observedTuples incoming (.expression prefixValues :: pending) =
      solutionTuples before (.expression sourcePrefix :: sourcePending) := by
  have expressionRead (environment : Environment) (atoms : List Atom) :
      read environment (.expression atoms) = .expression (atoms.map (read environment)) := by
    simp only [read_eq_applyTypeValuation,HE.Spec.Type.RuntimeRefinement.applyTypeValuation]
    exact congrArg Atom.expression (List.map_congr_left fun atom _ =>
      (read_eq_applyTypeValuation environment atom).symm)
  ext values
  constructor
  · rintro ⟨valuation,model,returned⟩
    have packet : (prefixValues ++ pending).map
        (HE.Spec.Type.RuntimeRefinement.applyTypeValuation valuation) ∈
        solutionTuples before (sourcePrefix ++ sourcePending) := by
      rw [← related]
      exact ⟨valuation,model,rfl⟩
    obtain ⟨environment,solved,same⟩ := packet
    simp only [List.map_append] at same
    obtain ⟨first,last⟩ := List.append_inj same (by simpa only [List.length_map] using lengths.symm)
    refine ⟨environment,solved,?_⟩
    simpa only [List.map_cons,expressionRead,
      HE.Spec.Type.RuntimeRefinement.applyTypeValuation,first,last] using returned
  · rintro ⟨environment,model,returned⟩
    have packet : (sourcePrefix ++ sourcePending).map (read environment) ∈
        HE.Spec.Bindings.ScopeObservation.observedTuples incoming (prefixValues ++ pending) := by
      rw [related]
      exact ⟨environment,model,rfl⟩
    obtain ⟨valuation,solved,same⟩ := packet
    simp only [List.map_append] at same
    obtain ⟨first,last⟩ := List.append_inj same (by simpa only [List.length_map] using lengths)
    refine ⟨valuation,solved,?_⟩
    simpa only [List.map_cons,expressionRead,
      HE.Spec.Type.RuntimeRefinement.applyTypeValuation,first,last] using returned

/-- A fresh destination may replace any coordinate after an evaluated prefix.
The complete prefix, value and pending caller share one model throughout. -/
theorem private_destination_joint_prefix
    {incoming : HE.Bindings} {before : Equations}
    {value sourceValue : Atom} {prefixValues sourcePrefix pending sourcePending : List Atom}
    (related : HE.Spec.Bindings.ScopeObservation.observedTuples incoming (prefixValues ++ value :: pending) =
      solutionTuples before (sourcePrefix ++ sourceValue :: sourcePending))
    (name : String)
    (storeFresh : ∀ pair ∈ before,
      name ∉ HE.Spec.Type.Presentation.TypeSubst.typeVars pair.1 ∧
        name ∉ HE.Spec.Type.Presentation.TypeSubst.typeVars pair.2)
    (packetFresh : name ∉ HE.Spec.Type.Presentation.TypeSubst.typeVarsList
      (sourcePrefix ++ sourceValue :: sourcePending)) :
    HE.Spec.Bindings.ScopeObservation.observedTuples incoming (prefixValues ++ value :: pending) =
      solutionTuples (before ++ [(sourceValue,.var name)]) (sourcePrefix ++ .var name :: sourcePending) := by
  rw [related]
  ext values
  constructor
  · rintro ⟨environment,model,returned⟩
    let extended : Environment := Function.update environment name (encode (read environment sourceValue))
    have keeps (atom : Atom) (absent : name ∉ HE.Spec.Type.Presentation.TypeSubst.typeVars atom) :
        read extended atom = read environment atom := by
      rw [read_eq_applyTypeValuation extended atom,read_eq_applyTypeValuation environment atom]
      apply HE.Spec.Bindings.ScopeObservation.applyTypeValuation_congr_of_typeVars
      intro key present
      have different : key ≠ name := by
        intro same
        exact absent (same ▸ present)
      exact congrArg decode (Function.update_of_ne different
        (encode (read environment sourceValue)) environment)
    have samePacket : (sourcePrefix ++ sourceValue :: sourcePending).map (read extended) =
        (sourcePrefix ++ sourceValue :: sourcePending).map (read environment) := by
      simp only [show read extended = _ from funext (read_eq_applyTypeValuation extended),
        show read environment = _ from funext (read_eq_applyTypeValuation environment)]
      apply HE.Spec.Bindings.ScopeObservation.applyTypeValuationList_congr_of_typeVars
      intro key present
      have different : key ≠ name := by
        intro same
        exact packetFresh (same ▸ present)
      exact congrArg decode (Function.update_of_ne different
        (encode (read environment sourceValue)) environment)
    have destination : read extended (.var name) = read environment sourceValue := by
      rw [read_eq_applyTypeValuation extended (.var name)]
      simp only [HE.Spec.Type.RuntimeRefinement.applyTypeValuation]
      change decode (Function.update environment name
        (encode (read environment sourceValue)) name) = read environment sourceValue
      exact (congrArg decode (Function.update_self name
        (encode (read environment sourceValue)) environment)).trans (decode_encode _)
    have valueFresh : name ∉ HE.Spec.Type.Presentation.TypeSubst.typeVars sourceValue := by
      intro used
      exact packetFresh (HE.Spec.Type.Presentation.Freshness.typeVars_mem_typeVarsList_of_mem
        (List.mem_append_right sourcePrefix List.mem_cons_self) name used)
    have equation : read extended sourceValue = read extended (.var name) :=
      (keeps sourceValue valueFresh).trans destination.symm
    refine ⟨extended,(solves_append_equation _ _ _ _).mpr ⟨?_,equation⟩,?_⟩
    · intro pair member
      rw [keeps pair.1 (storeFresh pair member).1,keeps pair.2 (storeFresh pair member).2]
      exact model pair member
    · have swapped : (sourcePrefix ++ .var name :: sourcePending).map (read extended) =
          (sourcePrefix ++ sourceValue :: sourcePending).map (read extended) := by
        simp only [List.map_append,List.map_cons,equation]
      exact swapped.trans (samePacket.trans returned)
  · rintro ⟨environment,model,returned⟩
    obtain ⟨previous,equation⟩ := (solves_append_equation _ _ _ _).mp model
    refine ⟨environment,previous,?_⟩
    simpa only [List.map_append,List.map_cons,equation] using returned

/-- Introducing a fresh destination preserves the joint returned-value and
caller packet. Incoming stores may differ outside that packet. -/
theorem private_destination_pending_observations
    {incoming : HE.Bindings} {before : Equations}
    {value sourceValue : Atom} {pending sourcePending : List Atom}
    (related : HE.Spec.Bindings.ScopeObservation.observedTuples incoming (value :: pending) =
      solutionTuples before (sourceValue :: sourcePending))
    (name : String)
    (storeFresh : ∀ pair ∈ before,
      name ∉ HE.Spec.Type.Presentation.TypeSubst.typeVars pair.1 ∧ name ∉ HE.Spec.Type.Presentation.TypeSubst.typeVars pair.2)
    (packetFresh : name ∉ HE.Spec.Type.Presentation.TypeSubst.typeVarsList (sourceValue :: sourcePending)) :
    HE.Spec.Bindings.ScopeObservation.observedTuples incoming (value :: pending) =
      solutionTuples (before ++ [(sourceValue,.var name)]) (.var name :: sourcePending) :=
  private_destination_joint_prefix (prefixValues := []) (sourcePrefix := []) related name storeFresh packetFresh

/-- A local source refinement needs agreement only on the two operands and
the whole pending continuation packet. Private destination variables and
residual representatives may differ. The matching HE candidate is constructed
from the accepted source model, and its reached joint observation is exact. -/
theorem petta_joint_refinement
    {incoming : HE.Bindings} {before after : Equations}
    {left right sourceLeft sourceRight : Atom} {pending sourcePending : List Atom}
    (related : HE.Spec.Bindings.ScopeObservation.observedTuples incoming
        (left :: right :: pending) =
      solutionTuples before (sourceLeft :: sourceRight :: sourcePending))
    (accepted : Refinement before sourceLeft sourceRight (some after)) :
    ∃ output, HE.Spec.Eval.Steps.UnifyCandidateRel left right incoming output ∧
      HE.Spec.Bindings.ScopeObservation.observedTuples output pending =
        solutionTuples after sourcePending := by
  cases accepted with
  | accepted environment old equation =>
      have sourcePacket :
          (sourceLeft :: sourceRight :: sourcePending).map (read environment) ∈
            HE.Spec.Bindings.ScopeObservation.observedTuples incoming
              (left :: right :: pending) := by
        rw [related]
        exact ⟨environment,old,rfl⟩
      obtain ⟨valuation,model,packet⟩ := sourcePacket
      simp only [List.map_cons,List.cons.injEq] at packet
      have heEquation := packet.1.trans (equation.trans packet.2.1.symm)
      let heEnvironment : Environment := fun name => encode (valuation name)
      have heOld : Solves heEnvironment
          (HE.Spec.Type.Presentation.BindingTheory.bindingAtomEquations incoming) := by
        apply (solves_binding_equations _ _).mpr
        simpa only [heEnvironment,decode_encode] using model
      have heNew : read heEnvironment left = read heEnvironment right := by
        rw [read_eq_applyTypeValuation heEnvironment left,
          read_eq_applyTypeValuation heEnvironment right]
        simpa only [heEnvironment,decode_encode] using heEquation
      obtain ⟨output,candidate⟩ := (petta_accepted_iff_he_candidate incoming left right).mp
        ⟨_,Refinement.accepted heEnvironment heOld heNew⟩
      refine ⟨output,candidate,?_⟩
      ext values
      constructor
      · rintro ⟨reached,reachedModel,returned⟩
        obtain ⟨matched,incomingModel⟩ := (candidate.solutions reached).mp reachedModel
        have observed : (left :: right :: pending).map
            (HE.Spec.Type.RuntimeRefinement.applyTypeValuation reached) ∈
            solutionTuples before (sourceLeft :: sourceRight :: sourcePending) := by
          rw [← related]
          exact ⟨reached,incomingModel,rfl⟩
        obtain ⟨source,sourceModel,sourcePacket⟩ := observed
        simp only [List.map_cons,List.cons.injEq] at sourcePacket
        refine ⟨source,(solves_append_equation _ _ _ _).mpr
          ⟨sourceModel,sourcePacket.1.trans (matched.trans sourcePacket.2.1.symm)⟩,
          sourcePacket.2.2.trans returned⟩
      · rintro ⟨source,sourceModel,returned⟩
        obtain ⟨incomingModel,matched⟩ := (solves_append_equation _ _ _ _).mp sourceModel
        have observed : (sourceLeft :: sourceRight :: sourcePending).map (read source) ∈
            HE.Spec.Bindings.ScopeObservation.observedTuples incoming
              (left :: right :: pending) := by
          rw [related]
          exact ⟨source,incomingModel,rfl⟩
        obtain ⟨reached,reachedModel,reachedPacket⟩ := observed
        simp only [List.map_cons,List.cons.injEq] at reachedPacket
        exact ⟨reached,(candidate.solutions reached).mpr
          ⟨reachedPacket.1.trans (matched.trans reachedPacket.2.1.symm),reachedModel⟩,
          reachedPacket.2.2.trans returned⟩

/-- Joint packet agreement reflects matching success in both directions,
even when the two source operands use different private representatives. -/
theorem petta_joint_accepted_iff_he_candidate
    {incoming : HE.Bindings} {before : Equations}
    {left right sourceLeft sourceRight : Atom} {pending sourcePending : List Atom}
    (related : HE.Spec.Bindings.ScopeObservation.observedTuples incoming
        (left :: right :: pending) =
      solutionTuples before (sourceLeft :: sourceRight :: sourcePending)) :
    (∃ after, Refinement before sourceLeft sourceRight (some after)) ↔
      ∃ output, HE.Spec.Eval.Steps.UnifyCandidateRel left right incoming output := by
  constructor
  · rintro ⟨after,accepted⟩
    obtain ⟨output,candidate,_⟩ := petta_joint_refinement related accepted
    exact ⟨output,candidate⟩
  · rintro ⟨output,candidate⟩
    obtain ⟨matched,matching,merged⟩ := candidate
    obtain ⟨valuation,model⟩ := merged.2
    have reached := (HE.Spec.Eval.Steps.UnifyCandidateRel.solutions
      ⟨matched,matching,merged⟩ valuation).mp model
    have observed : (left :: right :: pending).map
        (HE.Spec.Type.RuntimeRefinement.applyTypeValuation valuation) ∈
        solutionTuples before (sourceLeft :: sourceRight :: sourcePending) := by
      rw [← related]
      exact ⟨valuation,reached.2,rfl⟩
    obtain ⟨environment,old,packet⟩ := observed
    simp only [List.map_cons,List.cons.injEq] at packet
    exact ⟨_,Refinement.accepted environment old
      (packet.1.trans (reached.1.trans packet.2.1.symm))⟩

/-- Refusal is exact absence of a matching model under the same joint
boundary. It cannot be inferred from a merely unfinished execution. -/
theorem petta_joint_refused_iff_no_he_candidate
    {incoming : HE.Bindings} {before : Equations}
    {left right sourceLeft sourceRight : Atom} {pending sourcePending : List Atom}
    (related : HE.Spec.Bindings.ScopeObservation.observedTuples incoming
        (left :: right :: pending) =
      solutionTuples before (sourceLeft :: sourceRight :: sourcePending)) :
    Refinement before sourceLeft sourceRight none ↔
      ¬∃ output, HE.Spec.Eval.Steps.UnifyCandidateRel left right incoming output := by
  rw [← petta_joint_accepted_iff_he_candidate related]
  constructor
  · intro refused ⟨_,accepted⟩
    cases refused with
    | refused absent =>
        cases accepted with
        | accepted environment old new => exact absent ⟨environment,old,new⟩
  · intro absent
    apply Refinement.refused
    rintro ⟨environment,old,new⟩
    exact absent ⟨_,.accepted environment old new⟩

section

open HE.Spec.Type.RuntimeRefinement HE.Spec.Type.Presentation HE.Spec.Bindings.ScopeObservation

/-- Fresh clause syntax extends a joint observation without identifying hidden
store variables. Both model transports are constructed by agreeing with the
old model off the fresh support and with the new clause on that support. -/
theorem joint_pending_prepend_fresh
    {incoming : HE.Bindings} {before : Equations} {pending sourcePending : List Atom}
    (related : observedTuples incoming pending =
      solutionTuples before sourcePending)
    (freshAtoms : List Atom)
    (heFresh : ∀ name ∈ TypeSubst.typeVarsList freshAtoms,
      name ∉ specBindingVars incoming ∧ name ∉ TypeSubst.typeVarsList pending)
    (sourceFresh : ∀ name ∈ TypeSubst.typeVarsList freshAtoms,
      (∀ pair ∈ before, name ∉ TypeSubst.typeVars pair.1 ∧ name ∉ TypeSubst.typeVars pair.2) ∧
        name ∉ TypeSubst.typeVarsList sourcePending) :
    observedTuples incoming (freshAtoms ++ pending) =
      solutionTuples before (freshAtoms ++ sourcePending) := by
  ext values
  constructor
  · rintro ⟨valuation,model,returned⟩
    have packet : pending.map (applyTypeValuation valuation) ∈
        solutionTuples before sourcePending := by
      rw [← related]
      exact ⟨valuation,model,rfl⟩
    obtain ⟨environment,old,pendingSame⟩ := packet
    let extended : Environment := fun key =>
      if key ∈ TypeSubst.typeVarsList freshAtoms then PeTTa.EagerDFS.Destination.encode (valuation key)
      else environment key
    have preserved (atom : Atom)
        (disjoint : ∀ key ∈ TypeSubst.typeVars atom, key ∉ TypeSubst.typeVarsList freshAtoms) :
        read extended atom = read environment atom := by
      rw [PeTTa.EagerDFS.Destination.read_eq_applyTypeValuation extended atom,
        PeTTa.EagerDFS.Destination.read_eq_applyTypeValuation environment atom]
      apply applyTypeValuation_congr_of_typeVars
      intro key member
      dsimp only [extended]
      rw [if_neg (disjoint key member)]
    have kept : Solves extended before := by
      intro pair member
      rw [preserved pair.1 (fun key occurs fresh => (sourceFresh key fresh).1 pair member |>.1 occurs),
        preserved pair.2 (fun key occurs fresh => (sourceFresh key fresh).1 pair member |>.2 occurs)]
      exact old pair member
    have front : freshAtoms.map (read extended) = freshAtoms.map (applyTypeValuation valuation) := by
      simp only [show read extended = _ from funext (PeTTa.EagerDFS.Destination.read_eq_applyTypeValuation extended)]
      apply applyTypeValuationList_congr_of_typeVars
      intro key member
      dsimp only [extended]
      rw [if_pos member,PeTTa.EagerDFS.Destination.decode_encode]
    have tail : sourcePending.map (read extended) = sourcePending.map (read environment) := by
      simp only [show read extended = _ from funext (PeTTa.EagerDFS.Destination.read_eq_applyTypeValuation extended),
        show read environment = _ from funext (PeTTa.EagerDFS.Destination.read_eq_applyTypeValuation environment)]
      apply applyTypeValuationList_congr_of_typeVars
      intro key member
      dsimp only [extended]
      rw [if_neg (fun fresh => (sourceFresh key fresh).2 member)]
    refine ⟨extended,kept,?_⟩
    simp only [List.map_append] at returned ⊢
    rw [front,tail,pendingSame]
    exact returned
  · rintro ⟨environment,model,returned⟩
    have packet : sourcePending.map (read environment) ∈ observedTuples incoming pending := by
      rw [related]
      exact ⟨environment,model,rfl⟩
    obtain ⟨valuation,old,pendingSame⟩ := packet
    let extended : String → Atom := fun key =>
      if key ∈ TypeSubst.typeVarsList freshAtoms then PeTTa.EagerDFS.Destination.decode (environment key)
      else valuation key
    have kept : TypeBindingSatisfied extended incoming := by
      apply (specTypeBindingSatisfied_congr_of_bindingVars (left := valuation) (right := extended) ?_).mp old
      intro key member
      dsimp only [extended]
      rw [if_neg (fun fresh => (heFresh key fresh).1 member)]
    have front : freshAtoms.map (applyTypeValuation extended) = freshAtoms.map (read environment) := by
      simp only [show read environment = _ from funext (PeTTa.EagerDFS.Destination.read_eq_applyTypeValuation environment)]
      apply applyTypeValuationList_congr_of_typeVars
      intro key member
      dsimp only [extended]
      rw [if_pos member]
    have tail : pending.map (applyTypeValuation extended) = pending.map (applyTypeValuation valuation) := by
      apply applyTypeValuationList_congr_of_typeVars
      intro key member
      dsimp only [extended]
      rw [if_neg (fun fresh => (heFresh key fresh).2 member)]
    refine ⟨extended,kept,?_⟩
    simp only [List.map_append] at returned ⊢
    rw [front,tail,pendingSame]
    exact returned

/-- The query, fresh pattern, fresh body and pending caller are one correlated
packet. The same fresh variables interpret the pattern and body; no separate
choice of their models is permitted. -/
theorem joint_query_fresh_clause_observations
    {incoming : HE.Bindings} {before : Equations}
    {query sourceQuery pattern body : Atom} {pending sourcePending : List Atom}
    (related : observedTuples incoming (query :: pending) =
      solutionTuples before (sourceQuery :: sourcePending))
    (heFresh : ∀ name ∈ TypeSubst.typeVarsList [pattern,body],
      name ∉ specBindingVars incoming ∧ name ∉ TypeSubst.typeVarsList (query :: pending))
    (sourceFresh : ∀ name ∈ TypeSubst.typeVarsList [pattern,body],
      (∀ pair ∈ before, name ∉ TypeSubst.typeVars pair.1 ∧ name ∉ TypeSubst.typeVars pair.2) ∧
        name ∉ TypeSubst.typeVarsList (sourceQuery :: sourcePending)) :
    observedTuples incoming (query :: pattern :: body :: pending) =
      solutionTuples before (sourceQuery :: pattern :: body :: sourcePending) := by
  have expanded := joint_pending_prepend_fresh related [pattern,body] heFresh sourceFresh
  ext values
  constructor
  · rintro ⟨valuation,model,rfl⟩
    have packet : ([pattern,body] ++ query :: pending).map (applyTypeValuation valuation) ∈
        observedTuples incoming ([pattern,body] ++ query :: pending) := ⟨valuation,model,rfl⟩
    rw [expanded] at packet
    obtain ⟨environment,other,same⟩ := packet
    simp only [List.cons_append,List.nil_append,List.map_cons,List.cons.injEq] at same
    refine ⟨environment,other,?_⟩
    simp only [List.map_cons,List.cons.injEq]
    exact ⟨same.2.2.1,same.1,same.2.1,same.2.2.2⟩
  · rintro ⟨environment,model,rfl⟩
    have packet : ([pattern,body] ++ sourceQuery :: sourcePending).map (read environment) ∈
        observedTuples incoming ([pattern,body] ++ query :: pending) := by
      rw [expanded]
      exact ⟨environment,model,rfl⟩
    obtain ⟨valuation,other,same⟩ := packet
    simp only [List.cons_append,List.nil_append,List.map_cons,List.cons.injEq] at same
    refine ⟨valuation,other,?_⟩
    simp only [List.map_cons,List.cons.injEq]
    exact ⟨same.2.2.1,same.1,same.2.1,same.2.2.2⟩

/-- An accepted source match of a fresh clause constructs its HE counterpart
under the scoped packet relation. Its body and caller retain their reached
constraints even when earlier private destinations differ between stores. -/
theorem petta_fresh_clause_joint_refinement
    {incoming : HE.Bindings} {before after : Equations}
    {query sourceQuery pattern body : Atom} {pending sourcePending : List Atom}
    (related : observedTuples incoming (query :: pending) =
      solutionTuples before (sourceQuery :: sourcePending))
    (heFresh : ∀ name ∈ TypeSubst.typeVarsList [pattern,body],
      name ∉ specBindingVars incoming ∧ name ∉ TypeSubst.typeVarsList (query :: pending))
    (sourceFresh : ∀ name ∈ TypeSubst.typeVarsList [pattern,body],
      (∀ pair ∈ before, name ∉ TypeSubst.typeVars pair.1 ∧ name ∉ TypeSubst.typeVars pair.2) ∧
        name ∉ TypeSubst.typeVarsList (sourceQuery :: sourcePending))
    (accepted : Refinement before sourceQuery pattern (some after)) :
    ∃ output, HE.Spec.Eval.Steps.UnifyCandidateRel query pattern incoming output ∧
      observedTuples output (body :: pending) =
        solutionTuples after (body :: sourcePending) :=
  petta_joint_refinement (joint_query_fresh_clause_observations related heFresh sourceFresh) accepted

/-- A refused fresh source clause excludes every HE candidate at that shared
instance, using the same joint boundary as the success theorem. -/
theorem petta_fresh_clause_joint_refused_iff
    {incoming : HE.Bindings} {before : Equations}
    {query sourceQuery pattern body : Atom} {pending sourcePending : List Atom}
    (related : observedTuples incoming (query :: pending) =
      solutionTuples before (sourceQuery :: sourcePending))
    (heFresh : ∀ name ∈ TypeSubst.typeVarsList [pattern,body],
      name ∉ specBindingVars incoming ∧ name ∉ TypeSubst.typeVarsList (query :: pending))
    (sourceFresh : ∀ name ∈ TypeSubst.typeVarsList [pattern,body],
      (∀ pair ∈ before, name ∉ TypeSubst.typeVars pair.1 ∧ name ∉ TypeSubst.typeVars pair.2) ∧
        name ∉ TypeSubst.typeVarsList (sourceQuery :: sourcePending)) :
    Refinement before sourceQuery pattern none ↔
      ¬∃ output, HE.Spec.Eval.Steps.UnifyCandidateRel query pattern incoming output :=
  petta_joint_refused_iff_no_he_candidate (joint_query_fresh_clause_observations related heFresh sourceFresh)

/-- An actual source clause selection constructs the matching HE row at the
same physical source position. The reached observer includes the fresh body
and the complete saved caller packet, not independent marginal answers. -/
theorem petta_selected_joint_row
    {program : PeTTa.SpaceSemantics.Program} {control : Control}
    {head : String} {arguments : List Atom} {destination : Atom} {older : List Goal}
    {position : Nat} {pattern body : Atom} {next : Control}
    {incoming : HE.Bindings} {query : Atom} {pending sourcePending live : List Atom}
    (related : observedTuples incoming (query :: pending) =
      solutionTuples control.bindings (.expression (.symbol head :: arguments) :: sourcePending))
    (heFresh : ∀ name ∈ TypeSubst.typeVarsList [pattern,body],
      name ∉ specBindingVars incoming ∧ name ∉ TypeSubst.typeVarsList (query :: pending))
    (sourceFresh : ∀ name ∈ TypeSubst.typeVarsList [pattern,body],
      (∀ pair ∈ control.bindings, name ∉ TypeSubst.typeVars pair.1 ∧ name ∉ TypeSubst.typeVars pair.2) ∧
        name ∉ TypeSubst.typeVarsList (.expression (.symbol head :: arguments) :: sourcePending))
    (covered : ∀ name, HE.Spec.Eval.Steps.QueryVisibleName live query incoming name → name ∈ control.support)
    (selected : ClauseChoice.Selection program control head arguments destination older position pattern body next) :
    ∃ equation output, program.equations[position]? = some equation ∧
      HE.Spec.Eval.Steps.EquationRowResultsRel live query incoming position
        (PeTTa.SpaceSemantics.Equation.toAtom equation)
        [⟨position,ClauseChoice.pattern equation,equation.body,pattern,body,output⟩] ∧
      next.goals = .evaluate body destination :: older ∧
      observedTuples output (body :: pending) =
        solutionTuples next.bindings (body :: sourcePending) := by
  cases selected with
  | selected equation pattern body bindings row sameHead fresh accepted =>
    obtain ⟨output,candidate,observations⟩ := petta_fresh_clause_joint_refinement related heFresh sourceFresh accepted
    obtain ⟨matched,matching,merged⟩ := candidate
    exact ⟨equation,output,row,
      .hit _ _ _ _ _ _ _ (petta_fresh_instance_he_alpha fresh covered) matching merged,
      rfl,observations⟩

/-- The source allocator earns the finite freshness conditions shared by
successful and refused rows. Both caller packets and the binding support are
protected before a clause instance is allocated. -/
private theorem protected_clause_freshness
    (control : Control) (head : String) (arguments : List Atom)
    (position : Nat) (equation : PeTTa.SpaceSemantics.Equation)
    (live : List Atom) (query : Atom) (incoming : HE.Bindings)
    (pending sourcePending : List Atom) :
    let sourceAtoms := control.bindings.flatMap (fun pair => [pair.1,pair.2]) ++
      .expression (.symbol head :: arguments) :: sourcePending
    let forbidden := HE.EquationScope.visibleNames (pending ++ live) query incoming ++
      specBindingVars incoming ++ TypeSubst.typeVarsList (query :: pending) ++ TypeSubst.typeVarsList sourceAtoms
    let guarded := protectControl control forbidden.toFinset
    let pattern := ClauseChoice.freshPattern guarded position equation
    let body := ClauseChoice.freshBody guarded position equation
    (∀ name ∈ TypeSubst.typeVarsList [pattern,body],
      name ∉ specBindingVars incoming ∧ name ∉ TypeSubst.typeVarsList (query :: pending)) ∧
    (∀ name ∈ TypeSubst.typeVarsList [pattern,body],
      (∀ pair ∈ guarded.bindings, name ∉ TypeSubst.typeVars pair.1 ∧ name ∉ TypeSubst.typeVars pair.2) ∧
        name ∉ TypeSubst.typeVarsList (.expression (.symbol head :: arguments) :: sourcePending)) ∧
    (∀ name, HE.Spec.Eval.Steps.QueryVisibleName live query incoming name → name ∈ guarded.support) := by
  intro sourceAtoms forbidden guarded pattern body
  have avoids : ∀ name ∈ TypeSubst.typeVarsList [pattern,body], name ∉ guarded.support := by
    intro name occurs
    obtain ⟨atom,member,inside⟩ := Freshness.exists_mem_of_mem_typeVarsList occurs
    have paired : ClauseChoice.freshen guarded position (ClauseChoice.clauseAtoms equation) = [pattern,body] := rfl
    exact ClauseChoice.freshen_vars_avoid guarded position (ClauseChoice.clauseAtoms equation)
      atom (paired ▸ member) name inside
  have noForbidden : ∀ name ∈ TypeSubst.typeVarsList [pattern,body], name ∉ forbidden := by
    intro name occurs member
    apply avoids name occurs
    rw [show guarded = protectControl control forbidden.toFinset from rfl,protectControl_support]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr member)
  have left : ∀ name ∈ TypeSubst.typeVarsList [pattern,body],
      name ∉ specBindingVars incoming ∧ name ∉ TypeSubst.typeVarsList (query :: pending) := by
    intro name occurs
    constructor
    · intro member
      apply noForbidden name occurs
      simp only [forbidden,List.mem_append]
      tauto
    · intro member
      apply noForbidden name occurs
      simp only [forbidden,List.mem_append]
      tauto
  have right : ∀ name ∈ TypeSubst.typeVarsList [pattern,body],
      (∀ pair ∈ guarded.bindings, name ∉ TypeSubst.typeVars pair.1 ∧ name ∉ TypeSubst.typeVars pair.2) ∧
        name ∉ TypeSubst.typeVarsList (.expression (.symbol head :: arguments) :: sourcePending) := by
    intro name occurs
    have noSource : name ∉ TypeSubst.typeVarsList sourceAtoms := by
      intro member
      apply noForbidden name occurs
      simp only [forbidden,List.mem_append]
      tauto
    constructor
    · intro pair member
      constructor
      · intro inside
        apply noSource
        apply Freshness.typeVars_mem_typeVarsList_of_mem (atom := pair.1) _ name inside
        exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨pair,member,by simp⟩)
      · intro inside
        apply noSource
        apply Freshness.typeVars_mem_typeVarsList_of_mem (atom := pair.2) _ name inside
        exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨pair,member,by simp⟩)
    · intro member
      apply noSource
      exact (TypeSubst.typeVarsList_append _ _ ▸ List.mem_append_right _ member)
  have covered : ∀ name, HE.Spec.Eval.Steps.QueryVisibleName live query incoming name → name ∈ guarded.support := by
    intro name visible
    rw [show guarded = protectControl control forbidden.toFinset from rfl,protectControl_support]
    apply Finset.mem_union_right
    apply List.mem_toFinset.mpr
    have included : name ∈ HE.EquationScope.visibleNames (pending ++ live) query incoming := by
      apply (HE.EquationScope.mem_visibleNames_iff _ _ _ _).mpr
      exact (HE.EquationScope.queryVisible_support_iff _ _ _ _).mpr
       (by
        rcases (HE.EquationScope.queryVisible_support_iff _ _ _ _).mp visible with current | kept | bound
        · exact Or.inl current
        · obtain ⟨atom,member,occurs⟩ := kept
          exact Or.inr (Or.inl ⟨atom,List.mem_append_right _ member,occurs⟩)
        · exact Or.inr (Or.inr bound))
    simp only [forbidden,List.mem_append]
    tauto
  exact ⟨left,right,covered⟩

/-- Protecting the two source packets and the incoming binding support earns
all fresh-variable premises from the existing source allocator. A selected
clause then constructs the HE row and its exact reached joint observer. No
complete-store equivalence or additional allocator correctness is assumed. -/
theorem protected_petta_selected_joint_row
    (program : PeTTa.SpaceSemantics.Program) (control : Control)
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
    (position : Nat) (equation : PeTTa.SpaceSemantics.Equation)
    (live : List Atom) (query : Atom) (incoming : HE.Bindings)
    (pending sourcePending : List Atom)
    (related : observedTuples incoming (query :: pending) =
      solutionTuples control.bindings (.expression (.symbol head :: arguments) :: sourcePending))
    (stored : program.equations[position]? = some equation) :
    let sourceAtoms := control.bindings.flatMap (fun pair => [pair.1,pair.2]) ++
      .expression (.symbol head :: arguments) :: sourcePending
    let forbidden := HE.EquationScope.visibleNames (pending ++ live) query incoming ++
      specBindingVars incoming ++ TypeSubst.typeVarsList (query :: pending) ++ TypeSubst.typeVarsList sourceAtoms
    let guarded := protectControl control forbidden.toFinset
    let pattern := ClauseChoice.freshPattern guarded position equation
    let body := ClauseChoice.freshBody guarded position equation
    ∀ next, ClauseChoice.Selection program guarded head arguments destination older position pattern body next →
      ∃ output, HE.Spec.Eval.Steps.EquationRowResultsRel live query incoming position
        (PeTTa.SpaceSemantics.Equation.toAtom equation)
        [⟨position,ClauseChoice.pattern equation,equation.body,pattern,body,output⟩] ∧
        next.goals = .evaluate body destination :: older ∧
        observedTuples output (body :: pending) =
          solutionTuples next.bindings (body :: sourcePending) := by
  intro sourceAtoms forbidden guarded pattern body next selected
  obtain ⟨left,right,covered⟩ := protected_clause_freshness
    control head arguments position equation live query incoming pending sourcePending
  obtain ⟨actual,output,row,derived,goals,observations⟩ := petta_selected_joint_row (control := guarded) related left right covered selected
  have same : actual = equation := Option.some.inj (row.symm.trans stored)
  subst actual
  exact ⟨output,derived,goals,observations⟩

end

/-- The scoped matching law is realized by the actual destination-equation
source step. The reached world, caller goals and context are retained exactly;
the HE side observes the entire correlated continuation packet. -/
theorem source_equate_joint_pending {Context : Type}
    (policy : Policy) (program : PeTTa.SpaceSemantics.Program) (cursor : Cursor Context)
    {incoming : HE.Bindings} {left right value destination : Atom}
    {pending sourcePending : List Atom} {older : List Goal} {after : Equations}
    (related : HE.Spec.Bindings.ScopeObservation.observedTuples incoming
        (left :: right :: pending) =
      solutionTuples cursor.control.bindings (value :: destination :: sourcePending))
    (atGoal : cursor.control.goals = .equate value destination :: older)
    (accepted : Refinement cursor.control.bindings value destination (some after)) :
    ∃ output,
      Source.Step policy program cursor
        (.silent {cursor with control := {cursor.control with bindings := after,goals := older}}) ∧
      HE.Spec.Eval.Steps.UnifyCandidateRel left right incoming output ∧
      HE.Spec.Bindings.ScopeObservation.observedTuples output pending =
        solutionTuples after sourcePending := by
  obtain ⟨output,candidate,observations⟩ := petta_joint_refinement related accepted
  exact ⟨output,.accepted value destination older after atGoal accepted,candidate,observations⟩

/-- The end of an eager data spine constrains its assembled destination in
the reached source store. Prefix assembly and this actual equation step
preserve one joint model for all caller observations. -/
theorem source_assembled_prefix_joint_pending {Context : Type}
    (policy : Policy) (program : PeTTa.SpaceSemantics.Program) (cursor : Cursor Context)
    {incoming : HE.Bindings} {prefixValues sourcePrefix pending sourcePending : List Atom}
    {target destination : Atom} {older : List Goal} {after : Equations}
    (lengths : prefixValues.length = sourcePrefix.length)
    (related : HE.Spec.Bindings.ScopeObservation.observedTuples incoming
        (prefixValues ++ target :: pending) =
      solutionTuples cursor.control.bindings (sourcePrefix ++ destination :: sourcePending))
    (atGoal : cursor.control.goals = .equate (.expression sourcePrefix) destination :: older)
    (accepted : Refinement cursor.control.bindings (.expression sourcePrefix) destination (some after)) :
    ∃ output,
      Source.Step policy program cursor
        (.silent {cursor with control := {cursor.control with bindings := after,goals := older}}) ∧
      HE.Spec.Eval.Steps.UnifyCandidateRel (.expression prefixValues) target incoming output ∧
      HE.Spec.Bindings.ScopeObservation.observedTuples output pending =
        solutionTuples after sourcePending :=
  source_equate_joint_pending policy program cursor
    (joint_packet_assemble_prefix lengths related) atGoal accepted

/-- The same assembled-prefix boundary reflects genuine refusal, rather than
mistaking an unfinished child or an exhausted budget for an empty result. -/
theorem source_assembled_prefix_refused_iff
    {incoming : HE.Bindings} {before : Equations}
    {prefixValues sourcePrefix pending sourcePending : List Atom} {target destination : Atom}
    (lengths : prefixValues.length = sourcePrefix.length)
    (related : HE.Spec.Bindings.ScopeObservation.observedTuples incoming
        (prefixValues ++ target :: pending) =
      solutionTuples before (sourcePrefix ++ destination :: sourcePending)) :
    Refinement before (.expression sourcePrefix) destination none ↔
      ¬∃ output, HE.Spec.Eval.Steps.UnifyCandidateRel (.expression prefixValues) target incoming output :=
  petta_joint_refused_iff_no_he_candidate (joint_packet_assemble_prefix lengths related)

/-- A completed source head publishes the solved presentation of its reached
destination. The whole caller packet still has the same meaning in every
model, including open aliases shared with unevaluated siblings. -/
theorem source_returned_joint_pending {Context : Type}
    {policy : Policy} {program : PeTTa.SpaceSemantics.Program}
    {cursor reached : Cursor Context} {value : Atom} {bindings : Equations}
    {incoming : HE.Bindings} {head : Atom} {pending sourcePending : List Atom}
    (source : Source.Step policy program cursor (.finish (.value value bindings,reached)))
    (related : HE.Spec.Bindings.ScopeObservation.observedTuples incoming (head :: pending) =
      solutionTuples cursor.control.bindings (cursor.control.destination :: sourcePending)) :
    reached = cursor ∧ bindings = cursor.control.bindings ∧
      HE.Spec.Bindings.ScopeObservation.observedTuples incoming (head :: pending) =
        solutionTuples bindings (value :: sourcePending) := by
  obtain ⟨rfl,rfl,_ended,environment,resolved,rfl⟩ :=
    (Source.Step.returned_iff _ _ _ _ _ _).mp source
  refine ⟨rfl,rfl,related.trans ?_⟩
  symm
  apply solutionTuples_congr_models
  intro candidate solved
  simp only [List.map_cons,resolve_read_preserves resolved candidate solved]

/-- A completed head may occupy any coordinate after the accumulated
prefix. Its materialization preserves the entire prefix/tail joint packet. -/
theorem source_returned_joint_prefix {Context : Type}
    {policy : Policy} {program : PeTTa.SpaceSemantics.Program}
    {cursor reached : Cursor Context} {value : Atom} {bindings : Equations}
    {incoming : HE.Bindings} {prefixValues sourcePrefix pending sourcePending : List Atom}
    {head : Atom}
    (source : Source.Step policy program cursor (.finish (.value value bindings,reached)))
    (related : HE.Spec.Bindings.ScopeObservation.observedTuples incoming
        (prefixValues ++ head :: pending) =
      solutionTuples cursor.control.bindings
        (sourcePrefix ++ cursor.control.destination :: sourcePending)) :
    HE.Spec.Bindings.ScopeObservation.observedTuples incoming
        ((prefixValues ++ [head]) ++ pending) =
      solutionTuples bindings ((sourcePrefix ++ [value]) ++ sourcePending) := by
  obtain ⟨rfl,rfl,_ended,environment,resolved,rfl⟩ :=
    (Source.Step.returned_iff _ _ _ _ _ _).mp source
  simp only [List.append_assoc,List.singleton_append]
  refine related.trans ?_
  symm
  apply solutionTuples_congr_models
  intro candidate solved
  simp only [List.map_append,List.map_cons,resolve_read_preserves resolved candidate solved]

/-- The next actual sibling equation uses the completed head's reached
constraints and materialized value. Acceptance constructs the corresponding
HE refinement and exact joint caller packet; no future evaluator result is
an assumption. -/
theorem source_returned_then_refined_joint_pending {Context : Type}
    {policy : Policy} {program : PeTTa.SpaceSemantics.Program}
    {cursor reached : Cursor Context} {value : Atom} {bindings after : Equations}
    {incoming : HE.Bindings} {head pattern sourcePattern : Atom}
    {pending sourcePending : List Atom} (older : List Goal)
    (source : Source.Step policy program cursor (.finish (.value value bindings,reached)))
    (related : HE.Spec.Bindings.ScopeObservation.observedTuples incoming
        (head :: pattern :: pending) =
      solutionTuples cursor.control.bindings (cursor.control.destination :: sourcePattern :: sourcePending))
    (accepted : Refinement bindings value sourcePattern (some after)) :
    ∃ output,
      HE.Spec.Eval.Steps.UnifyCandidateRel head pattern incoming output ∧
      Source.Step policy program
        {reached with control := {reached.control with
          goals := .equate value sourcePattern :: older}}
        (.silent {reached with control := {reached.control with bindings := after,goals := older}}) ∧
      HE.Spec.Bindings.ScopeObservation.observedTuples output pending =
        solutionTuples after sourcePending := by
  obtain ⟨rfl,rfl,returned⟩ := source_returned_joint_pending source related
  obtain ⟨output,candidate,observations⟩ := petta_joint_refinement returned accepted
  exact ⟨output,candidate,.accepted value sourcePattern older after rfl accepted,observations⟩

/-- Completed-head materialization also reflects refusal. A stale caller
store cannot replace the reached equations when deciding the next sibling. -/
theorem source_returned_then_refused_iff {Context : Type}
    {policy : Policy} {program : PeTTa.SpaceSemantics.Program}
    {cursor reached : Cursor Context} {value : Atom} {bindings : Equations}
    {incoming : HE.Bindings} {head pattern sourcePattern : Atom}
    {pending sourcePending : List Atom}
    (source : Source.Step policy program cursor (.finish (.value value bindings,reached)))
    (related : HE.Spec.Bindings.ScopeObservation.observedTuples incoming
        (head :: pattern :: pending) =
      solutionTuples cursor.control.bindings (cursor.control.destination :: sourcePattern :: sourcePending)) :
    Refinement bindings value sourcePattern none ↔
      ¬∃ output, HE.Spec.Eval.Steps.UnifyCandidateRel head pattern incoming output := by
  exact petta_joint_refused_iff_no_he_candidate
    (source_returned_joint_pending source related).2.2

/-- Two actual source equation steps introduce a private result destination
and use it in the following match. The HE counterpart matches the returned
value directly. No complete-store equivalence is demanded after introduction
of the private name; the common boundary is the joint continuation packet. -/
theorem source_private_destination_pending {Context : Type}
    (policy : Policy) (program : PeTTa.SpaceSemantics.Program) (cursor : Cursor Context)
    {incoming : HE.Bindings} (name : String) (value pattern sourceValue sourcePattern : Atom)
    (pending sourcePending : List Atom) {older : List Goal} {after : Equations}
    (related : HE.Spec.Bindings.ScopeObservation.observedTuples incoming (value :: pattern :: pending) =
      solutionTuples cursor.control.bindings (sourceValue :: sourcePattern :: sourcePending))
    (storeFresh : ∀ pair ∈ cursor.control.bindings,
      name ∉ HE.Spec.Type.Presentation.TypeSubst.typeVars pair.1 ∧
        name ∉ HE.Spec.Type.Presentation.TypeSubst.typeVars pair.2)
    (packetFresh : name ∉ HE.Spec.Type.Presentation.TypeSubst.typeVarsList
      (sourceValue :: sourcePattern :: sourcePending))
    (atGoals : cursor.control.goals =
      .equate sourceValue (.var name) :: .equate (.var name) sourcePattern :: older)
    (accepted : Refinement (cursor.control.bindings ++ [(sourceValue,.var name)])
      (.var name) sourcePattern (some after)) :
    let middle : Cursor Context := {cursor with control := {cursor.control with
      bindings := cursor.control.bindings ++ [(sourceValue,.var name)]
      goals := .equate (.var name) sourcePattern :: older}}
    ∃ output,
      Source.Step policy program cursor (.silent middle) ∧
      Source.Step policy program middle
        (.silent {cursor with control := {cursor.control with bindings := after,goals := older}}) ∧
      HE.Spec.Eval.Steps.UnifyCandidateRel value pattern incoming output ∧
      HE.Spec.Bindings.ScopeObservation.observedTuples output pending =
        solutionTuples after sourcePending := by
  intro middle
  obtain ⟨output,candidate,observations⟩ := petta_joint_refinement
    (private_destination_pending_observations related name storeFresh packetFresh) accepted
  have introduced : Refinement cursor.control.bindings sourceValue (.var name)
      (some (cursor.control.bindings ++ [(sourceValue,.var name)])) := by
    cases accepted with
    | accepted environment old _ =>
        obtain ⟨previous,equation⟩ := (solves_append_equation _ _ _ _).mp old
        exact .accepted environment previous equation
  exact ⟨output,
    .accepted sourceValue (.var name) (.equate (.var name) sourcePattern :: older) _ atGoals introduced,
    .accepted (.var name) sourcePattern older after rfl accepted,candidate,observations⟩

/-- A head's certified materialization remains valid after the sibling
adds constraints. Both dialects observe the same joint packet in the reached
store, even if their residual variable representatives differ. -/
theorem petta_reached_refinement_pending
    {incoming : HE.Bindings} {table : HE.Spec.Type.Presentation.TypeSubst}
    {before after : Equations} {query pattern : Atom}
    (related : ∀ environment, HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied
      (fun name => decode (environment name)) incoming ↔ Solves environment before)
    (certified : HE.Spec.Type.Presentation.BindingTheory.ReadoutCertificate incoming table)
    (accepted : Refinement before query pattern (some after)) (pending : List Atom) :
    ∃ output, HE.Spec.Eval.Steps.UnifyCandidateRel query pattern incoming output ∧
      HE.Spec.Bindings.ScopeObservation.observedTuples output (pending.map table.apply) =
        solutionTuples after pending := by
  have packet : HE.Spec.Bindings.ScopeObservation.observedTuples incoming
        (query :: pattern :: pending.map table.apply) =
      solutionTuples before (query :: pattern :: pending) := by
    calc
      HE.Spec.Bindings.ScopeObservation.observedTuples incoming
          (query :: pattern :: pending.map table.apply) =
          HE.Spec.Bindings.ScopeObservation.observedTuples incoming (query :: pattern :: pending) := by
        apply HE.Spec.Bindings.ScopeObservation.observedTuples_congr_models
        intro valuation model
        have same : (pending.map table.apply).map
            (HE.Spec.Type.RuntimeRefinement.applyTypeValuation valuation) =
            pending.map (HE.Spec.Type.RuntimeRefinement.applyTypeValuation valuation) := by
          rw [List.map_map]
          exact List.map_congr_left fun atom _ => certified.preserves_model valuation model atom
        exact congrArg (fun values =>
          HE.Spec.Type.RuntimeRefinement.applyTypeValuation valuation query ::
            HE.Spec.Type.RuntimeRefinement.applyTypeValuation valuation pattern :: values) same
      _ = _ := reached_pending_observations related _
  exact petta_joint_refinement packet accepted

/-- The joint continuation law commutes with the actual PeTTa destination
equation step. The retained older goals, world, context and destination are unchanged;
only the new equation is added before those goals run. The HE candidate and
pending observer are constructed from that same source refinement. -/
theorem source_equate_he_pending {Context : Type}
    (policy : Policy) (program : PeTTa.SpaceSemantics.Program) (cursor : Cursor Context)
    {incoming : HE.Bindings} {table : HE.Spec.Type.Presentation.TypeSubst}
    {value destination : Atom} {older : List Goal} {after : Equations}
    (related : ∀ environment, HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied
      (fun name => decode (environment name)) incoming ↔ Solves environment cursor.control.bindings)
    (certified : HE.Spec.Type.Presentation.BindingTheory.ReadoutCertificate incoming table)
    (atGoal : cursor.control.goals = .equate value destination :: older)
    (accepted : Refinement cursor.control.bindings value destination (some after))
    (pending : List Atom) :
    ∃ output,
      Source.Step policy program cursor
        (.silent {cursor with control := {cursor.control with bindings := after,goals := older}}) ∧
      HE.Spec.Eval.Steps.UnifyCandidateRel value destination incoming output ∧
      HE.Spec.Bindings.ScopeObservation.observedTuples output (pending.map table.apply) =
        solutionTuples after pending := by
  obtain ⟨output,candidate,observations⟩ :=
    petta_reached_refinement_pending related certified accepted pending
  exact ⟨output,.accepted value destination older after atGoal accepted,candidate,observations⟩

/-- One retained PeTTa alternative and its HE source work item agree on the
source occurrence, pending body, caller boundary and complete solution theory.
The relation imposes no equality of binding representatives or storage. -/
def ClauseAgreement (caller : Control) (destination : Atom) (older : List Goal)
    (selected : Nat × Control) (work : HE.Spec.Eval.Steps.EquationWork) : Prop :=
  work.position = selected.1 ∧
    selected.2.goals = .evaluate work.body destination :: older ∧
    selected.2.destination = caller.destination ∧
    selected.2.reserved = caller.reserved ∧
    selected.2.cutBoundary = caller.cutBoundary ∧
    ∀ environment, HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied
      (fun name => decode (environment name)) work.bindings ↔
        Solves environment selected.2.bindings

/-- The scoped clause boundary retains the exact selected source extension,
caller frame, physical occurrence and joint body/caller observation. Private
destinations need not have corresponding variables in the two stores. -/
structure ClausePendingAgreement (caller : Control) (sourceQuery destination : Atom)
    (older : List Goal) (pending sourcePending : List Atom)
    (selected : Nat × Control) (work : HE.Spec.Eval.Steps.EquationWork) : Prop where
  occurrence : work.position = selected.1
  bindings : selected.2.bindings = caller.bindings ++ [(sourceQuery,work.pattern)]
  goals : selected.2.goals = .evaluate work.body destination :: older
  destination : selected.2.destination = caller.destination
  reserved : selected.2.reserved = caller.reserved
  cutBoundary : selected.2.cutBoundary = caller.cutBoundary
  observations :
    HE.Spec.Bindings.ScopeObservation.observedTuples work.bindings (work.body :: pending) =
      solutionTuples selected.2.bindings (work.body :: sourcePending)

/-- Forgetting the body component retains the whole correlated caller
packet. This projection uses the same model; it does not compare marginals. -/
theorem ClausePendingAgreement.pending_observations
    {caller : Control} {sourceQuery destination : Atom} {older : List Goal}
    {pending sourcePending : List Atom}
    {selected : Nat × Control} {work : HE.Spec.Eval.Steps.EquationWork}
    (related : ClausePendingAgreement caller sourceQuery destination older pending sourcePending
      selected work) :
    HE.Spec.Bindings.ScopeObservation.observedTuples work.bindings pending =
      solutionTuples selected.2.bindings sourcePending := by
  ext values
  constructor
  · rintro ⟨valuation,model,returned⟩
    have packet : (work.body :: pending).map
        (HE.Spec.Type.RuntimeRefinement.applyTypeValuation valuation) ∈
        solutionTuples selected.2.bindings (work.body :: sourcePending) := by
      rw [← related.observations]
      exact ⟨valuation,model,rfl⟩
    obtain ⟨environment,solved,same⟩ := packet
    exact ⟨environment,solved,(List.cons.inj same).2.trans returned⟩
  · rintro ⟨environment,model,returned⟩
    have packet : (work.body :: sourcePending).map (read environment) ∈
        HE.Spec.Bindings.ScopeObservation.observedTuples work.bindings (work.body :: pending) := by
      rw [related.observations]
      exact ⟨environment,model,rfl⟩
    obtain ⟨valuation,solved,same⟩ := packet
    exact ⟨valuation,solved,(List.cons.inj same).2.trans returned⟩

/-- Physical occurrences and reached caller observations survive the scoped
frontier comparison with multiplicity. Traversal order is forgotten only by
the declared multiset observer. -/
theorem ClausePendingAgreement.pending_occurrences
    {caller : Control} {sourceQuery destination : Atom} {older : List Goal}
    {pending sourcePending : List Atom}
    {choices : List (Nat × Control)} {works : List HE.Spec.Eval.Steps.EquationWork}
    (related : List.Forall₂
      (ClausePendingAgreement caller sourceQuery destination older pending sourcePending)
      choices works) :
    (works.map (fun work => (work.position,
      HE.Spec.Bindings.ScopeObservation.observedTuples work.bindings pending)) : Multiset (Nat × Set (List Atom))) =
      (choices.map (fun selected => (selected.1,
        solutionTuples selected.2.bindings sourcePending)) : Multiset (Nat × Set (List Atom))) := by
  have packets : works.map (fun work => (work.position,
        HE.Spec.Bindings.ScopeObservation.observedTuples work.bindings pending)) =
      choices.map (fun selected => (selected.1,
        solutionTuples selected.2.bindings sourcePending)) := by
    induction related with
    | nil => rfl
    | cons one _rest ih =>
      simp only [List.map_cons,one.occurrence,one.pending_observations,ih]
  exact congrArg (fun packets : List (Nat × Set (List Atom)) =>
    (packets : Multiset (Nat × Set (List Atom)))) packets

/-- Selecting a physical clause retains one common environment for every
pending observation, including the caller and that clause's residual body. -/
theorem ClauseAgreement.pending_observations
    {caller : Control} {destination : Atom} {older : List Goal}
    {selected : Nat × Control} {work : HE.Spec.Eval.Steps.EquationWork}
    (related : ClauseAgreement caller destination older selected work) (pending : List Atom) :
    HE.Spec.Bindings.ScopeObservation.observedTuples work.bindings pending =
      solutionTuples selected.2.bindings pending :=
  reached_pending_observations related.2.2.2.2.2 pending

/-- The sibling's actual matching operation consumes the equations reached
by this selected occurrence, including its caller aliases and fresh instance.
The resulting solution relation can be used by another sibling. -/
theorem ClauseAgreement.continue_refinement
    {caller : Control} {destination : Atom} {older : List Goal}
    {selected : Nat × Control} {work : HE.Spec.Eval.Steps.EquationWork}
    (related : ClauseAgreement caller destination older selected work)
    {after : Equations} {query pattern : Atom}
    (accepted : Refinement selected.2.bindings query pattern (some after)) :
    ∃ output, HE.Spec.Eval.Steps.UnifyCandidateRel query pattern work.bindings output ∧
      ∀ environment, HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied
        (fun name => decode (environment name)) output ↔ Solves environment after :=
  petta_reached_refinement related.2.2.2.2.2 accepted

/-- Complete frontiers preserve the bag of joint pending observations with
their source positions. Equal stored clauses still contribute separately;
no public traversal order or answer deduplication is imposed. -/
theorem ClauseAgreement.pending_occurrences
    {caller : Control} {destination : Atom} {older : List Goal}
    {choices : List (Nat × Control)} {works : List HE.Spec.Eval.Steps.EquationWork}
    (related : List.Forall₂ (ClauseAgreement caller destination older) choices works)
    (pending : List Atom) :
    (works.map (fun work => (work.position,
      HE.Spec.Bindings.ScopeObservation.observedTuples work.bindings pending)) :
        Multiset (Nat × Set (List Atom))) =
      (choices.map (fun selected => (selected.1,
        solutionTuples selected.2.bindings pending)) : Multiset (Nat × Set (List Atom))) := by
  have packets : works.map (fun work => (work.position,
        HE.Spec.Bindings.ScopeObservation.observedTuples work.bindings pending)) =
      choices.map (fun selected => (selected.1,
        solutionTuples selected.2.bindings pending)) := by
    induction related with
    | nil => rfl
    | cons one _rest ih =>
        simp only [List.map_cons,one.1,one.pending_observations pending,ih]
  exact congrArg (fun packets : List (Nat × Set (List Atom)) =>
    (packets : Multiset (Nat × Set (List Atom)))) packets

/-- Refusal of one legal fresh instance rules out every other legal spelling.
The resulting HE source row is completed, not merely unexplored. -/
theorem petta_refused_he_row
    {live : List Atom} {query left right pattern body : Atom} {incoming : HE.Bindings}
    {before : Equations}
    (position : Nat)
    (variant : HE.Spec.Eval.Steps.AlphaVariantRel live query incoming left right pattern body)
    (relatedStores : ∀ environment, HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied
      (fun name => decode (environment name)) incoming ↔ Solves environment before)
    (refused : Refinement before query pattern none) :
    HE.Spec.Eval.Steps.EquationRowResultsRel live query incoming position
      (.expression [.symbol "=",left,right]) [] := by
  apply HE.Spec.Eval.Steps.EquationRowResultsRel.miss position left right pattern body variant
  intro otherPattern otherBody otherVariant matched output compatible
  apply (petta_reached_refused_iff_no_he_candidate relatedStores query pattern).mp refused
  exact (HE.EquationFreshening.alphaVariants_candidate_exists_iff otherVariant variant).mp
    ⟨output,matched,compatible⟩

/-- A different literal head cannot be reconciled by a first-order variable
valuation, even when the caller has open or aliased constraints. -/
theorem different_head_refused (before : Equations) (control : Control)
    (position : Nat) (equation : PeTTa.SpaceSemantics.Equation)
    (head : String) (arguments : List Atom) (different : equation.head ≠ head) :
    Refinement before
      (.expression (.symbol head :: arguments))
      (ClauseChoice.freshPattern control position equation) none := by
  apply Refinement.refused
  rintro ⟨environment,_old,same⟩
  simp only [read_eq_applyTypeValuation,ClauseChoice.freshPattern,ClauseChoice.pattern,
    HE.Spec.Type.RuntimeRefinement.renameTypeVars,List.map_cons,
    HE.Spec.Type.RuntimeRefinement.applyTypeValuation,Atom.expression.injEq,
    List.cons.injEq,Atom.symbol.injEq] at same
  exact different same.1.symm

/-- Every independent PeTTa row decision constructs the corresponding
completed HE source row. Selected rows retain the same fresh body and caller;
refused rows exclude all legal HE alpha-instances. The incoming stores agree
on solutions; their constraint records may differ. -/
theorem petta_decision_he_row
    {program : PeTTa.SpaceSemantics.Program} {control : Control}
    {head : String} {arguments : List Atom} {destination : Atom} {older : List Goal}
    {position : Nat} {result : Option Control} {live : List Atom} {incoming : HE.Bindings}
    (relatedStores : ∀ environment, HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied
      (fun name => decode (environment name)) incoming ↔ Solves environment control.bindings)
    (covered : ∀ name, HE.Spec.Eval.Steps.QueryVisibleName live
      (.expression (.symbol head :: arguments)) incoming name → name ∈ control.support)
    (decision : ClauseChoice.Decision program control head arguments destination older position result) :
    ∃ equation works, program.equations[position]? = some equation ∧
      HE.Spec.Eval.Steps.EquationRowResultsRel live
        (.expression (.symbol head :: arguments)) incoming position (PeTTa.SpaceSemantics.Equation.toAtom equation) works ∧
      List.Forall₂ (fun next work => ClauseAgreement control destination older (position,next) work)
        result.toList works := by
  cases decision with
  | other equation row different =>
      refine ⟨equation,[],row,?_,.nil⟩
      exact petta_refused_he_row position
        (petta_fresh_instance_he_alpha (ClauseChoice.fresh_clause_instance _ _ _) covered)
        relatedStores
        (different_head_refused control.bindings control position equation head arguments different)
  | refused equation row _same incompatible =>
      refine ⟨equation,[],row,?_,.nil⟩
      exact petta_refused_he_row position
        (petta_fresh_instance_he_alpha (ClauseChoice.fresh_clause_instance _ _ _) covered)
        relatedStores incompatible
  | selected equation bindings row _same compatible =>
      obtain ⟨output,candidate,reached⟩ := petta_reached_refinement relatedStores compatible
      obtain ⟨matched,matching,merged⟩ := candidate
      refine ⟨equation,[⟨position,ClauseChoice.pattern equation,equation.body,
        ClauseChoice.freshPattern control position equation,
        ClauseChoice.freshBody control position equation,output⟩],row,?_,?_⟩
      · exact .hit _ _ _ _ _ _ _
          (petta_fresh_instance_he_alpha (ClauseChoice.fresh_clause_instance _ _ _) covered)
          matching merged
      · apply List.Forall₂.cons _ .nil
        refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
        exact reached

/-- Every outcome of the actual protected row selector constructs its HE
source row under the scoped observation relation. A refused row is exhausted;
a selected row retains its physical occurrence and reached caller packet. -/
theorem protected_petta_joint_decision_he_row
    (program : PeTTa.SpaceSemantics.Program) (control : Control)
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
    (live : List Atom) (query : Atom) (incoming : HE.Bindings)
    (pending sourcePending : List Atom)
    (related : HE.Spec.Bindings.ScopeObservation.observedTuples incoming (query :: pending) =
      solutionTuples control.bindings (.expression (.symbol head :: arguments) :: sourcePending)) :
    let sourceAtoms := control.bindings.flatMap (fun pair => [pair.1,pair.2]) ++
      .expression (.symbol head :: arguments) :: sourcePending
    let forbidden := HE.EquationScope.visibleNames (pending ++ live) query incoming ++
      HE.Spec.Bindings.ScopeObservation.specBindingVars incoming ++
      HE.Spec.Type.Presentation.TypeSubst.typeVarsList (query :: pending) ++
      HE.Spec.Type.Presentation.TypeSubst.typeVarsList sourceAtoms
    let guarded := protectControl control forbidden.toFinset
    ∀ {position : Nat} {result : Option Control},
      ClauseChoice.Decision program guarded head arguments destination older position result →
      ∃ equation works, program.equations[position]? = some equation ∧
        HE.Spec.Eval.Steps.EquationRowResultsRel live query incoming position
          (PeTTa.SpaceSemantics.Equation.toAtom equation) works ∧
        List.Forall₂ (fun next work => ClausePendingAgreement guarded
          (.expression (.symbol head :: arguments)) destination older pending sourcePending
          (position,next) work) result.toList works := by
  intro sourceAtoms forbidden guarded position result decision
  have miss (equation : PeTTa.SpaceSemantics.Equation)
      (refused : Refinement guarded.bindings (.expression (.symbol head :: arguments))
        (ClauseChoice.freshPattern guarded position equation) none) :
      HE.Spec.Eval.Steps.EquationRowResultsRel live query incoming position
        (PeTTa.SpaceSemantics.Equation.toAtom equation) [] := by
    obtain ⟨left,right,covered⟩ := protected_clause_freshness
      control head arguments position equation live query incoming pending sourcePending
    have variant := petta_fresh_instance_he_alpha (ClauseChoice.fresh_clause_instance guarded position equation) covered
    apply HE.Spec.Eval.Steps.EquationRowResultsRel.miss position _ _ _ _ variant
    intro otherPattern otherBody otherVariant matched output compatible
    apply (petta_fresh_clause_joint_refused_iff related left right).mp refused
    exact (HE.EquationFreshening.alphaVariants_candidate_exists_iff otherVariant variant).mp
      ⟨output,matched,compatible⟩
  cases decision with
  | other equation row different =>
      exact ⟨equation,[],row,miss equation
        (different_head_refused guarded.bindings guarded position equation head arguments different),.nil⟩
  | refused equation row _same incompatible =>
      exact ⟨equation,[],row,miss equation incompatible,.nil⟩
  | selected equation bindings row _same compatible =>
      obtain ⟨left,right,covered⟩ := protected_clause_freshness
        control head arguments position equation live query incoming pending sourcePending
      have bindingsEq : bindings = guarded.bindings ++
          [(.expression (.symbol head :: arguments),ClauseChoice.freshPattern guarded position equation)] := by
        cases compatible
        rfl
      obtain ⟨output,candidate,observations⟩ := petta_fresh_clause_joint_refinement related left right compatible
      obtain ⟨matched,matching,merged⟩ := candidate
      refine ⟨equation,[⟨position,ClauseChoice.pattern equation,equation.body,
        ClauseChoice.freshPattern guarded position equation,ClauseChoice.freshBody guarded position equation,output⟩],
        row,?_,?_⟩
      · exact .hit _ _ _ _ _ _ _
          (petta_fresh_instance_he_alpha (ClauseChoice.fresh_clause_instance guarded position equation) covered)
          matching merged
      · exact .cons ⟨rfl,bindingsEq,rfl,rfl,rfl,rfl,observations⟩ .nil

private theorem petta_frontier_he_rows
    {program : PeTTa.SpaceSemantics.Program} {control : Control}
    {head : String} {arguments : List Atom} {destination : Atom} {older : List Goal}
    {positions : List Nat} {answers : List (Nat × Control)}
    {live : List Atom} {query : Atom} {incoming : HE.Bindings}
    (agreement : (Nat × Control) → HE.Spec.Eval.Steps.EquationWork → Prop)
    (rowLaw : ∀ {position : Nat} {result : Option Control},
      ClauseChoice.Decision program control head arguments destination older position result →
      ∃ equation works, program.equations[position]? = some equation ∧
        HE.Spec.Eval.Steps.EquationRowResultsRel live query incoming position
          (PeTTa.SpaceSemantics.Equation.toAtom equation) works ∧
        List.Forall₂ (fun next work => agreement (position,next) work) result.toList works)
    (source : ClauseChoice.Frontier program control head arguments destination older positions answers)
    (rows : List (Atom × Nat))
    (aligned : List.Forall₂ (fun position row => row.2 = position ∧
      ∃ equation, row.1 = PeTTa.SpaceSemantics.Equation.toAtom equation ∧ program.equations[position]? = some equation)
      positions rows) :
    ∃ blocks, List.Forall₂ (fun row block =>
        HE.Spec.Eval.Steps.EquationRowResultsRel live query incoming row.2 row.1 block) rows blocks ∧
      List.Forall₂ agreement answers blocks.flatten := by
  have rowAt {position : Nat} {result : Option Control}
      (decision : ClauseChoice.Decision program control head arguments destination older position result)
      {row : Atom × Nat} (aligned : row.2 = position ∧
        ∃ equation, row.1 = PeTTa.SpaceSemantics.Equation.toAtom equation ∧ program.equations[position]? = some equation) :
      ∃ works, HE.Spec.Eval.Steps.EquationRowResultsRel live
          query incoming row.2 row.1 works ∧
        List.Forall₂ (fun next work => agreement (position,next) work)
          result.toList works := by
    obtain ⟨samePosition,equation,shape,stored⟩ := aligned
    obtain ⟨actual,works,actualRow,completed,related⟩ :=
      rowLaw decision
    obtain rfl : actual = equation := Option.some.inj (actualRow.symm.trans stored)
    exact ⟨works,by simpa only [samePosition,shape] using completed,related⟩
  induction source generalizing rows with
  | nil =>
      cases aligned
      exact ⟨[],.nil,.nil⟩
  | skip decision _rest ih =>
      cases aligned with
      | cons one tail =>
          obtain ⟨works,completed,related⟩ := rowAt decision one
          cases related
          obtain ⟨blocks,completedRest,relatedRest⟩ := ih _ tail
          exact ⟨[] :: blocks,.cons completed completedRest,relatedRest⟩
  | keep decision _rest ih =>
      cases aligned with
      | cons one tail =>
          obtain ⟨works,completed,related⟩ := rowAt decision one
          cases related with
          | cons agreement empty =>
              cases empty
              obtain ⟨blocks,completedRest,relatedRest⟩ := ih _ tail
              exact ⟨[_] :: blocks,.cons completed completedRest,.cons agreement relatedRest⟩

/-- Lift constructed row counterparts over one complete source enumeration.
The relation on retained work is supplied by each proved local interface;
full-store and scoped-observation clients share this occurrence fold while
retaining physical occurrence multiplicity. -/
theorem petta_frontier_he_frontier_of_decision
    {program : PeTTa.SpaceSemantics.Program} {control : Control}
    {head : String} {arguments : List Atom} {destination : Atom} {older : List Goal}
    {answers : List (Nat × Control)} {live : List Atom} {query : Atom} {incoming : HE.Bindings}
    (agreement : (Nat × Control) → HE.Spec.Eval.Steps.EquationWork → Prop)
    (rowLaw : ∀ {position : Nat} {result : Option Control},
      ClauseChoice.Decision program control head arguments destination older position result →
      ∃ equation works, program.equations[position]? = some equation ∧
        HE.Spec.Eval.Steps.EquationRowResultsRel live query incoming position
          (PeTTa.SpaceSemantics.Equation.toAtom equation) works ∧
        List.Forall₂ (fun next work => agreement (position,next) work) result.toList works)
    (source : ClauseChoice.Frontier program control head arguments destination older
      (List.range program.equations.length) answers) :
    ∃ works, HE.Spec.Eval.Steps.EquationFrontierRel
        (HE.Space.ofList (program.equations.map PeTTa.SpaceSemantics.Equation.toAtom)) live
        query incoming works ∧ List.Forall₂ agreement answers works := by
  have aligned : List.Forall₂ (fun position row => row.2 = position ∧
      ∃ equation, row.1 = PeTTa.SpaceSemantics.Equation.toAtom equation ∧ program.equations[position]? = some equation)
      (List.range program.equations.length) (program.equations.map PeTTa.SpaceSemantics.Equation.toAtom).zipIdx := by
    apply List.forall₂_of_length_eq_of_get (by simp)
    intro index before _after
    have bound : index < program.equations.length := by simpa using before
    refine ⟨?_,program.equations[index],?_,?_⟩
    · simp
    · simp
    · simp
  obtain ⟨blocks,completed,related⟩ := petta_frontier_he_rows agreement rowLaw source _ aligned
  exact ⟨blocks.flatten,.completed completed,related⟩

/-- A complete ordered PeTTa source scan constructs a complete HE source
frontier of the same stored equation table. No rows, duplicate occurrences,
bindings or older caller goals disappear when search order is forgotten. -/
theorem petta_frontier_he_frontier
    {program : PeTTa.SpaceSemantics.Program} {control : Control}
    {head : String} {arguments : List Atom} {destination : Atom} {older : List Goal}
    {answers : List (Nat × Control)} {live : List Atom} {incoming : HE.Bindings}
    (relatedStores : ∀ environment, HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied
      (fun name => decode (environment name)) incoming ↔ Solves environment control.bindings)
    (covered : ∀ name, HE.Spec.Eval.Steps.QueryVisibleName live
      (.expression (.symbol head :: arguments)) incoming name → name ∈ control.support)
    (source : ClauseChoice.Frontier program control head arguments destination older
      (List.range program.equations.length) answers) :
    ∃ works, HE.Spec.Eval.Steps.EquationFrontierRel
        (HE.Space.ofList (program.equations.map PeTTa.SpaceSemantics.Equation.toAtom)) live
        (.expression (.symbol head :: arguments)) incoming works ∧
      List.Forall₂ (ClauseAgreement control destination older) answers works := by
  refine petta_frontier_he_frontier_of_decision (ClauseAgreement control destination older) ?_ source
  intro position result decision
  exact petta_decision_he_row relatedStores covered decision

/-- The actual complete selector constructs a complete HE frontier under
joint caller observations, including stores with earlier private result
variables. Every source row is covered; duplicate rows remain occurrences. -/
theorem protected_petta_joint_choices_he_frontier
    (program : PeTTa.SpaceSemantics.Program) (control : Control)
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
    (live : List Atom) (query : Atom) (incoming : HE.Bindings)
    (pending sourcePending : List Atom)
    (related : HE.Spec.Bindings.ScopeObservation.observedTuples incoming (query :: pending) =
      solutionTuples control.bindings (.expression (.symbol head :: arguments) :: sourcePending)) :
    let sourceAtoms := control.bindings.flatMap (fun pair => [pair.1,pair.2]) ++
      .expression (.symbol head :: arguments) :: sourcePending
    let forbidden := HE.EquationScope.visibleNames (pending ++ live) query incoming ++
      HE.Spec.Bindings.ScopeObservation.specBindingVars incoming ++
      HE.Spec.Type.Presentation.TypeSubst.typeVarsList (query :: pending) ++
      HE.Spec.Type.Presentation.TypeSubst.typeVarsList sourceAtoms
    let guarded := protectControl control forbidden.toFinset
    let choices := ClauseChoice.choices program guarded head arguments destination older
    ∃ works, HE.Spec.Eval.Steps.EquationFrontierRel
        (HE.Space.ofList (program.equations.map PeTTa.SpaceSemantics.Equation.toAtom)) live query incoming works ∧
      List.Forall₂ (ClausePendingAgreement guarded
        (.expression (.symbol head :: arguments)) destination older pending sourcePending)
        choices works ∧
      (works.map (fun work => (work.position,
        HE.Spec.Bindings.ScopeObservation.observedTuples work.bindings pending)) : Multiset (Nat × Set (List Atom))) =
        (choices.map (fun selected => (selected.1,
          solutionTuples selected.2.bindings sourcePending)) : Multiset (Nat × Set (List Atom))) := by
  intro sourceAtoms forbidden guarded choices
  have rowLaw := @protected_petta_joint_decision_he_row program control head arguments destination older
    live query incoming pending sourcePending related
  have completed := (ClauseChoice.choices_iff_frontier program guarded head arguments destination older _).mp rfl
  obtain ⟨works,frontier,paired⟩ := petta_frontier_he_frontier_of_decision
    (ClausePendingAgreement guarded (.expression (.symbol head :: arguments))
      destination older pending sourcePending) rowLaw completed
  exact ⟨works,frontier,paired,ClausePendingAgreement.pending_occurrences paired⟩

/-- The actual PeTTa clause selector therefore earns the complete HE source
frontier, rather than just a possibility or membership witness per answer. -/
theorem petta_choices_he_frontier
    (program : PeTTa.SpaceSemantics.Program) (control : Control)
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
    (live : List Atom) (incoming : HE.Bindings)
    (relatedStores : ∀ environment, HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied
      (fun name => decode (environment name)) incoming ↔ Solves environment control.bindings)
    (covered : ∀ name, HE.Spec.Eval.Steps.QueryVisibleName live
      (.expression (.symbol head :: arguments)) incoming name → name ∈ control.support) :
    ∃ works, HE.Spec.Eval.Steps.EquationFrontierRel
        (HE.Space.ofList (program.equations.map PeTTa.SpaceSemantics.Equation.toAtom)) live
        (.expression (.symbol head :: arguments)) incoming works ∧
      List.Forall₂ (ClauseAgreement control destination older)
        (ClauseChoice.choices program control head arguments destination older) works :=
  petta_frontier_he_frontier relatedStores covered
    ((ClauseChoice.choices_iff_frontier _ _ _ _ _ _ _).mp rfl)

/-- Finite caller protection constructs the freshness coverage needed above;
it does not add an assumed whole-evaluator correspondence. -/
theorem protected_petta_choices_he_frontier
    (program : PeTTa.SpaceSemantics.Program) (control : Control)
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
    (live : List Atom) (incoming : HE.Bindings)
    (relatedStores : ∀ environment, HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied
      (fun name => decode (environment name)) incoming ↔ Solves environment control.bindings) :
    let guarded := protectControl control
      (HE.EquationScope.visibleNames live (.expression (.symbol head :: arguments)) incoming).toFinset
    ∃ works, HE.Spec.Eval.Steps.EquationFrontierRel
        (HE.Space.ofList (program.equations.map PeTTa.SpaceSemantics.Equation.toAtom)) live
        (.expression (.symbol head :: arguments)) incoming works ∧
      List.Forall₂ (ClauseAgreement guarded destination older)
        (ClauseChoice.choices program guarded head arguments destination older) works := by
  apply petta_choices_he_frontier
  · exact relatedStores
  · intro name visible
    rw [protectControl_support]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr
      ((HE.EquationScope.mem_visibleNames_iff _ _ _ _).mpr visible))

/-- The actual complete clause scan preserves joint caller/sibling readouts
as an occurrence bag. The frontier is constructed from the source decisions;
neither its coverage nor its observation equality is an assumed callback.
The pending packet is included in the live scope before clause freshening. -/
theorem protected_petta_choices_he_pending
    (program : PeTTa.SpaceSemantics.Program) (control : Control)
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
    (live : List Atom) (incoming : HE.Bindings) (pending : List Atom)
    (relatedStores : ∀ environment, HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied
      (fun name => decode (environment name)) incoming ↔ Solves environment control.bindings) :
    let guarded := protectControl control
      (HE.EquationScope.visibleNames (pending ++ live) (.expression (.symbol head :: arguments)) incoming).toFinset
    ∃ works, HE.Spec.Eval.Steps.EquationFrontierRel
        (HE.Space.ofList (program.equations.map PeTTa.SpaceSemantics.Equation.toAtom)) (pending ++ live)
        (.expression (.symbol head :: arguments)) incoming works ∧
      (works.map (fun work => (work.position,
        HE.Spec.Bindings.ScopeObservation.observedTuples work.bindings pending)) :
          Multiset (Nat × Set (List Atom))) =
        ((ClauseChoice.choices program guarded head arguments destination older).map
          (fun selected => (selected.1,
            solutionTuples selected.2.bindings pending)) : Multiset (Nat × Set (List Atom))) := by
  obtain ⟨works,completed,related⟩ := protected_petta_choices_he_frontier program control
    head arguments destination older (pending ++ live) incoming relatedStores
  exact ⟨works,completed,ClauseAgreement.pending_occurrences related pending⟩

theorem ClauseAgreement.positions {caller : Control} {destination : Atom} {older : List Goal}
    {choices : List (Nat × Control)} {works : List HE.Spec.Eval.Steps.EquationWork}
    (related : List.Forall₂ (ClauseAgreement caller destination older) choices works) :
    works.map HE.Spec.Eval.Steps.EquationWork.position = choices.map Prod.fst := by
  induction related with
  | nil => rfl
  | cons one _rest ih => exact congrArg₂ List.cons one.1 ih

/-- Every completed HE source frontier has precisely the actual PeTTa source
occurrence bag, including duplicate stored equations. Alternate legal fresh
spellings and binding representatives cannot change this count. -/
theorem petta_choices_he_occurrences
    {program : PeTTa.SpaceSemantics.Program} {control : Control}
    {head : String} {arguments : List Atom} {destination : Atom} {older : List Goal}
    {live : List Atom} {incoming : HE.Bindings} {works : List HE.Spec.Eval.Steps.EquationWork}
    (relatedStores : ∀ environment, HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied
      (fun name => decode (environment name)) incoming ↔ Solves environment control.bindings)
    (covered : ∀ name, HE.Spec.Eval.Steps.QueryVisibleName live
      (.expression (.symbol head :: arguments)) incoming name → name ∈ control.support)
    (completed : HE.Spec.Eval.Steps.EquationFrontierRel
      (HE.Space.ofList (program.equations.map PeTTa.SpaceSemantics.Equation.toAtom)) live
      (.expression (.symbol head :: arguments)) incoming works) :
    (works.map HE.Spec.Eval.Steps.EquationWork.position).Perm
      ((ClauseChoice.choices program control head arguments destination older).map Prod.fst) := by
  obtain ⟨chosen,derived,related⟩ := petta_choices_he_frontier program control head arguments
    destination older live incoming relatedStores covered
  rw [← ClauseAgreement.positions related]
  exact completed.positions_perm derived


namespace FrontierControls

private def incoming : HE.Bindings :=
  ⟨[("root",.symbol "A")],[("root","alias")]⟩

private def localRule : PeTTa.SpaceSemantics.Equation :=
  ⟨"f",[.var "local"],.expression [.symbol "Pair",.var "local",.var "local"]⟩

private def literalRule : PeTTa.SpaceSemantics.Equation := ⟨"f",[.symbol "B"],.symbol "refused"⟩
private def otherRule : PeTTa.SpaceSemantics.Equation := ⟨"g",[.var "local"],.symbol "other"⟩

private def program : PeTTa.SpaceSemantics.Program :=
  { equations := [localRule,localRule,literalRule,otherRule], declarations := [] }

private def older : List Goal :=
  [.evaluate (.expression [.symbol "Saved",.var "alias",.var "saved"]) (.var "out")]

private def caller : Control :=
  { bindings := HE.Spec.Type.Presentation.BindingTheory.bindingAtomEquations incoming
    goals := older
    destination := .var "out" }

private def live : List Atom := [.expression [.symbol "Saved",.var "saved"]]
private def query : Atom := .expression [.symbol "f",.var "alias"]
private def guarded : Control :=
  protectControl caller (HE.EquationScope.visibleNames live query incoming).toFinset

private def selected : List (Nat × Control) :=
  ClauseChoice.choices program guarded "f" [.var "alias"] (.var "answer") older

/-- Two stored copies survive independently despite a bound caller alias and
an older live variable. The incompatible literal and different head do not. -/
private def next (position : Nat) : Control :=
  { guarded with
    bindings := guarded.bindings ++ [(query,ClauseChoice.freshPattern guarded position localRule)]
    goals := .evaluate (ClauseChoice.freshBody guarded position localRule) (.var "answer") :: older }

private def aModel : Environment := fun _ => encode (.symbol "A")

private theorem localAccepted (position : Nat) :
    Refinement guarded.bindings query (ClauseChoice.freshPattern guarded position localRule)
      (some (next position).bindings) := by
  apply Refinement.accepted aModel
  · change Solves _ (HE.Spec.Type.Presentation.BindingTheory.bindingAtomEquations incoming)
    rw [solves_binding_equations]
    simp [HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied,incoming,
      HE.Spec.Type.RuntimeRefinement.applyTypeValuation,aModel,encode,decode]
  · rw [read_eq_applyTypeValuation,read_eq_applyTypeValuation]
    simp [query,ClauseChoice.freshPattern,ClauseChoice.pattern,localRule,
      HE.Spec.Type.RuntimeRefinement.renameTypeVars,
      HE.Spec.Type.RuntimeRefinement.applyTypeValuation,aModel,encode,decode]

private theorem literalRefused (position : Nat) :
    Refinement guarded.bindings query (ClauseChoice.freshPattern guarded position literalRule) none := by
  apply Refinement.refused
  rintro ⟨environment,old,new⟩
  change Solves environment
    (HE.Spec.Type.Presentation.BindingTheory.bindingAtomEquations incoming) at old
  have model := (solves_binding_equations environment incoming).mp old
  have root := model.1 "root" (.symbol "A") (by simp [incoming])
  have aliasEqual := model.2 "root" "alias" (by simp [incoming])
  have rootValue : decode (environment "root") = .symbol "A" := by
    simpa only [HE.Spec.Type.RuntimeRefinement.applyTypeValuation] using root
  have value : decode (environment "alias") = .symbol "A" := aliasEqual.symm.trans rootValue
  rw [read_eq_applyTypeValuation,read_eq_applyTypeValuation] at new
  simp [query,ClauseChoice.freshPattern,ClauseChoice.pattern,
    literalRule,HE.Spec.Type.RuntimeRefinement.renameTypeVars,
    HE.Spec.Type.RuntimeRefinement.applyTypeValuation,value] at new

private theorem choices_exact : selected = [(0,next 0),(1,next 1)] := by
  apply (ClauseChoice.choices_iff_frontier _ _ _ _ _ _ _).mpr
  exact .keep (.selected localRule _ rfl rfl (localAccepted 0))
    (.keep (.selected localRule _ rfl rfl (localAccepted 1))
      (.skip (.refused literalRule rfl rfl (literalRefused 2))
        (.skip (.other otherRule rfl (by decide +kernel)) .nil)))

theorem duplicate_positions : selected.map Prod.fst = [0,1] := by
  rw [choices_exact]
  rfl

private def bodies : List (Option Atom) := selected.map fun next => do
  let environment ← resolve next.2.bindings
  match next.2.goals with
  | .evaluate body _ :: _ => some (PeTTa.EagerDFS.Destination.read environment body)
  | _ => none

#guard bodies == [some (.expression [.symbol "Pair",.symbol "A",.symbol "A"]),
  some (.expression [.symbol "Pair",.symbol "A",.symbol "A"])]
#guard selected.all (fun next => next.2.goals.tail == older)

/-- The complete HE source frontier is earned from those same actual choices,
with the whole caller relation, not a supplied answer-set equality. -/
theorem duplicate_complete_source :
    ∃ works, HE.Spec.Eval.Steps.EquationFrontierRel
      (HE.Space.ofList (program.equations.map PeTTa.SpaceSemantics.Equation.toAtom)) live query incoming works ∧
      works.length = 2 ∧
      List.Forall₂ (ClauseAgreement guarded (.var "answer") older) selected works := by
  obtain ⟨works,completed,related⟩ := protected_petta_choices_he_frontier program caller
    "f" [.var "alias"] (.var "answer") older live incoming
    (fun environment => (solves_binding_equations environment incoming).symm)
  refine ⟨works,completed,?_,related⟩
  have positions := congrArg List.length duplicate_positions
  simp only [List.length_map,List.length_cons,List.length_nil] at positions
  exact related.length_eq.symm.trans positions

/-- Both stored copies retain one joint readout of an aliased caller and its
saved data, observed with any additional packet. Taking the bag never erases
either copy; protection of extra caller names is a separate source condition. -/
theorem duplicate_pending_observations (pending : List Atom) :
    ∃ works, HE.Spec.Eval.Steps.EquationFrontierRel
      (HE.Space.ofList (program.equations.map PeTTa.SpaceSemantics.Equation.toAtom)) live query incoming works ∧
      (works.map (fun work => (work.position,
        HE.Spec.Bindings.ScopeObservation.observedTuples work.bindings
          ([.var "root",.var "alias",.expression [.symbol "Saved",.var "alias"]] ++ pending))) :
            Multiset (Nat × Set (List Atom))) =
        (selected.map (fun chosen => (chosen.1,
          solutionTuples chosen.2.bindings
            ([Atom.var "root",.var "alias",.expression [.symbol "Saved",.var "alias"]] ++ pending))) :
              Multiset (Nat × Set (List Atom))) ∧
      (works.map (fun work => HE.Spec.Bindings.ScopeObservation.observedTuples work.bindings pending) :
        Multiset (Set (List Atom))).card = 2 := by
  obtain ⟨works,completed,count,related⟩ := duplicate_complete_source
  exact ⟨works,completed,ClauseAgreement.pending_occurrences related _,by simpa using count⟩

private def refusalProgram : PeTTa.SpaceSemantics.Program :=
  { equations := [literalRule,otherRule], declarations := [] }

theorem literal_and_other_head_refused :
    ClauseChoice.choices refusalProgram guarded "f" [.var "alias"] (.var "answer") older = [] :=
  by
    apply (ClauseChoice.choices_iff_frontier _ _ _ _ _ _ _).mpr
    exact .skip (.refused literalRule rfl rfl (literalRefused 0))
      (.skip (.other otherRule rfl (by decide +kernel)) .nil)

/-- Rejection at the existing caller constraints completes an empty HE
frontier; it is distinct from an empty unfinished search prefix. -/
theorem refused_complete_source :
    HE.Spec.Eval.Steps.EquationFrontierRel
      (HE.Space.ofList (refusalProgram.equations.map PeTTa.SpaceSemantics.Equation.toAtom)) live query incoming [] := by
  obtain ⟨works,completed,related⟩ := protected_petta_choices_he_frontier refusalProgram caller
    "f" [.var "alias"] (.var "answer") older live incoming
    (fun environment => (solves_binding_equations environment incoming).symm)
  change List.Forall₂ _ (ClauseChoice.choices refusalProgram guarded "f" [.var "alias"]
    (.var "answer") older) works at related
  rw [literal_and_other_head_refused] at related
  cases related
  exact completed

end FrontierControls

namespace ContinuationControls

/-- A caller variable cannot be reused as a supposedly private destination.
The old packet permits the returned value and caller to differ; identifying
them destroys that correlation. -/
theorem nonfresh_destination_changes_observations :
    HE.Spec.Bindings.ScopeObservation.observedTuples HE.Bindings.empty
      [.symbol "A",.var "public"] ≠
      solutionTuples [(.symbol "A",.var "public")] [.var "public",.var "public"] := by
  intro equal
  have witness : [.symbol "A",.symbol "B"] ∈
      HE.Spec.Bindings.ScopeObservation.observedTuples HE.Bindings.empty
        [.symbol "A",.var "public"] := by
    refine ⟨fun _ => .symbol "B",?_,?_⟩
    · constructor <;> simp [HE.Bindings.empty]
    · simp [HE.Spec.Type.RuntimeRefinement.applyTypeValuation]
  rw [equal] at witness
  obtain ⟨environment,_,packet⟩ := witness
  simp only [List.map_cons,List.map_nil,List.cons.injEq,and_true] at packet
  exact (by decide : (Atom.symbol "A") ≠ .symbol "B") (packet.1.symm.trans packet.2)

private def incoming : HE.Bindings := ⟨[],[("x","alias")]⟩
private def before : Equations := HE.Spec.Type.Presentation.BindingTheory.bindingAtomEquations incoming
private def afterHead : Equations := before ++ [(.var "x",.symbol "A")]
private def constant (value : Atom) : Environment := fun _ => encode value

private theorem initial_agreement (environment : Environment) :
    HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied
        (fun name => decode (environment name)) incoming ↔ Solves environment before :=
  (solves_binding_equations environment incoming).symm

/-- An actual completed open head retains both possible alias valuations and
excludes an inconsistent cross-pair. Its output need not be ground, and no
caller binding is reset when the solved presentation is published. -/
theorem completed_open_head_keeps_aliases {Context : Type}
    (policy : Policy) (program : PeTTa.SpaceSemantics.Program)
    (world : PeTTa.EagerDFS.World) (context : Context) :
    let cursor : Cursor Context := ⟨world,
      {bindings := before,goals := [],destination := .var "x"},context⟩
    ∃ value,
      Source.Step policy program cursor (.finish (.value value before,cursor)) ∧
      HE.Spec.Bindings.ScopeObservation.observedTuples incoming [.var "x",.var "alias"] =
        solutionTuples before [value,.var "alias"] ∧
      [Atom.symbol "A",.symbol "A"] ∈ solutionTuples before [value,.var "alias"] ∧
      [Atom.symbol "B",.symbol "B"] ∈ solutionTuples before [value,.var "alias"] ∧
      [Atom.symbol "A",.symbol "B"] ∉ solutionTuples before [value,.var "alias"] := by
  intro cursor
  have model (value : Atom) : Solves (constant value) before := by
    simp [Solves,before,incoming,HE.Spec.Type.Presentation.BindingTheory.bindingAtomEquations,
      read_eq_applyTypeValuation,constant,HE.Spec.Type.RuntimeRefinement.applyTypeValuation]
  obtain ⟨environment,resolved⟩ := resolve_complete ⟨constant (.symbol "A"),model _⟩
  let value := read environment (.var "x")
  have returned : Source.Step policy program cursor (.finish (.value value before,cursor)) :=
    .returned environment rfl resolved
  have packet := (source_returned_joint_pending returned
    (reached_pending_observations initial_agreement [.var "x",.var "alias"])).2.2
  have possible (answer : Atom) : [answer,answer] ∈ solutionTuples before [value,.var "alias"] := by
    refine ⟨constant answer,model answer,?_⟩
    simp only [List.map_cons,List.map_nil,value,
      resolve_read_preserves resolved (constant answer) (model answer)]
    simp [read_eq_applyTypeValuation,constant,HE.Spec.Type.RuntimeRefinement.applyTypeValuation]
  refine ⟨value,returned,packet,possible _,possible _,?_⟩
  rintro ⟨candidate,solved,observed⟩
  have aliases := solved (.var "x",.var "alias") (by
    simp [before,incoming,HE.Spec.Type.Presentation.BindingTheory.bindingAtomEquations])
  have absorbs := resolve_read_preserves resolved candidate solved (.var "x")
  simp only [List.map_cons,List.map_nil,List.cons.injEq,and_true] at observed
  change read candidate (read environment (.var "x")) = .symbol "A" ∧
    read candidate (.var "alias") = .symbol "B" at observed
  have impossible := observed.1.symm.trans (absorbs.trans (aliases.trans observed.2))
  exact (by decide : (Atom.symbol "A") ≠ .symbol "B") impossible

private theorem head_accepts : Refinement before (.var "x") (.symbol "A") (some afterHead) := by
  apply Refinement.accepted (constant (.symbol "A"))
  · simp [Solves,before,incoming,HE.Spec.Type.Presentation.BindingTheory.bindingAtomEquations,
      read_eq_applyTypeValuation,constant,HE.Spec.Type.RuntimeRefinement.applyTypeValuation]
  · simp [read_eq_applyTypeValuation,constant,HE.Spec.Type.RuntimeRefinement.applyTypeValuation]

private theorem reached_sibling_refuses : Refinement afterHead (.var "alias") (.symbol "B") none := by
  apply Refinement.refused
  rintro ⟨environment,solved,new⟩
  obtain ⟨old,head⟩ := (solves_append_equation environment before (.var "x") (.symbol "A")).mp solved
  have aliases : read environment (.var "x") = read environment (.var "alias") :=
    old (.var "x",.var "alias") (by
      simp [before,incoming,HE.Spec.Type.Presentation.BindingTheory.bindingAtomEquations])
  have unequal := head.symm.trans (aliases.trans new)
  simp only [read_eq_applyTypeValuation,HE.Spec.Type.RuntimeRefinement.applyTypeValuation,
    Atom.symbol.injEq] at unequal
  exact (by decide : ("A" : String) ≠ "B") unequal

private theorem stale_sibling_accepts :
    Refinement before (.var "alias") (.symbol "B")
      (some (before ++ [(.var "alias",.symbol "B")])) := by
  apply Refinement.accepted (constant (.symbol "B"))
  · simp [Solves,before,incoming,HE.Spec.Type.Presentation.BindingTheory.bindingAtomEquations,
      read_eq_applyTypeValuation,constant,HE.Spec.Type.RuntimeRefinement.applyTypeValuation]
  · simp [read_eq_applyTypeValuation,constant,HE.Spec.Type.RuntimeRefinement.applyTypeValuation]

/-- An open head binds an alias visible to the next sibling. The real reached
theory refuses the conflicting sibling in both languages. Restarting from
the initial caller would accept it, so a fixed-caller argument loop is not
an adequate replacement for reached-constraint threading. -/
theorem sibling_uses_reached_head_theory :
    ∃ reached, HE.Spec.Eval.Steps.UnifyCandidateRel (.var "x") (.symbol "A") incoming reached ∧
      (¬∃ output, HE.Spec.Eval.Steps.UnifyCandidateRel
        (.var "alias") (.symbol "B") reached output) ∧
      (∃ output, HE.Spec.Eval.Steps.UnifyCandidateRel
        (.var "alias") (.symbol "B") incoming output) ∧
      ∀ pending : List Atom, HE.Spec.Bindings.ScopeObservation.observedTuples reached pending =
        solutionTuples afterHead pending := by
  obtain ⟨reached,head,related⟩ := petta_reached_refinement initial_agreement head_accepts
  exact ⟨reached,head,
    (petta_reached_refused_iff_no_he_candidate related _ _).mp reached_sibling_refuses,
    (petta_reached_accepted_iff_he_candidate initial_agreement _ _).mp ⟨_,stale_sibling_accepts⟩,
    reached_pending_observations related⟩

/-- A real open-alias source refinement supplies the incoming relation for
the next complete clause query. No literal encoding of the reached equation
record is required. The next query and pending caller packet are arbitrary. -/
theorem reached_head_then_frontier {Context : Type}
    (policy : Policy) (program : PeTTa.SpaceSemantics.Program)
    (world : PeTTa.EagerDFS.World) (context : Context)
    (head : String) (arguments : List Atom) (destination output : Atom)
    (older : List Goal) (live pending : List Atom) :
    let caller : Control :=
      { bindings := afterHead
        goals := .invoke head arguments destination :: older
        destination := output }
    let first : Cursor Context := ⟨world,
      { caller with
        bindings := before
        goals := .equate (.var "x") (.symbol "A") :: caller.goals },context⟩
    ∃ reached works,
      Source.Step policy program first (.silent ⟨world,caller,context⟩) ∧
      HE.Spec.Eval.Steps.UnifyCandidateRel (.var "x") (.symbol "A") incoming reached ∧
      HE.Spec.Eval.Steps.EquationFrontierRel
        (HE.Space.ofList (program.equations.map PeTTa.SpaceSemantics.Equation.toAtom))
        (pending ++ live) (.expression (.symbol head :: arguments)) reached works ∧
      let guarded := protectControl caller
        (HE.EquationScope.visibleNames (pending ++ live)
          (.expression (.symbol head :: arguments)) reached).toFinset
      (works.map (fun work => (work.position,
        HE.Spec.Bindings.ScopeObservation.observedTuples work.bindings pending)) :
          Multiset (Nat × Set (List Atom))) =
        ((ClauseChoice.choices program guarded head arguments destination older).map
          (fun selected => (selected.1,
            solutionTuples selected.2.bindings pending)) : Multiset (Nat × Set (List Atom))) := by
  intro caller first
  obtain ⟨reached,candidate,related⟩ := petta_reached_refinement initial_agreement head_accepts
  obtain ⟨works,complete,observed⟩ := protected_petta_choices_he_pending
    program caller head arguments destination older live reached pending related
  exact ⟨reached,works,
    .accepted (.var "x") (.symbol "A") caller.goals afterHead rfl head_accepts,
    candidate,complete,observed⟩

open HE.Spec.Type.RuntimeRefinement HE.Spec.Type.Presentation HE.Spec.Bindings.ScopeObservation in
/-- A past private destination breaks full-store agreement but preserves an
open aliased caller. The real selector keeps both wildcard copies and the
literal row that constrains that caller; the different-head row is refused. -/
theorem private_destination_duplicate_frontier :
    let program := FrontierControls.program
    let query : Atom := .expression [.symbol "f",.var "alias"]
    let pending : List Atom := [.var "x",.var "alias",.var "saved"]
    let caller : Control :=
      { bindings := before ++ [(.var "x",.var "private-result")]
        goals := .invoke "f" [.var "alias"] (.var "answer") :: FrontierControls.older
        destination := .var "out" }
    let sourceAtoms := caller.bindings.flatMap (fun pair => [pair.1,pair.2]) ++ query :: pending
    let forbidden := HE.EquationScope.visibleNames (pending ++ FrontierControls.live) query incoming ++
      specBindingVars incoming ++ TypeSubst.typeVarsList (query :: pending) ++ TypeSubst.typeVarsList sourceAtoms
    let guarded := protectControl caller forbidden.toFinset
    let choices := ClauseChoice.choices program guarded "f" [.var "alias"] (.var "answer") FrontierControls.older
    ∃ works, HE.Spec.Eval.Steps.EquationFrontierRel
        (HE.Space.ofList (program.equations.map PeTTa.SpaceSemantics.Equation.toAtom))
        FrontierControls.live query incoming works ∧
      works.map HE.Spec.Eval.Steps.EquationWork.position = [0,1,2] ∧
      List.Forall₂ (ClausePendingAgreement guarded query (.var "answer")
        FrontierControls.older pending pending) choices works := by
  intro program query pending caller sourceAtoms forbidden guarded choices
  have initial := reached_pending_observations initial_agreement (.var "x" :: query :: pending)
  have hidden := private_destination_pending_observations initial "private-result"
    (by
      simp [before,incoming,HE.Spec.Type.Presentation.BindingTheory.bindingAtomEquations,TypeSubst.typeVars])
    (by simp [query,pending,TypeSubst.typeVarsList,TypeSubst.typeVars])
  have related : observedTuples incoming (query :: pending) =
      solutionTuples caller.bindings (query :: pending) := by
    ext values
    constructor
    · rintro ⟨valuation,model,returned⟩
      have packet : (.var "x" :: query :: pending).map (applyTypeValuation valuation) ∈
          observedTuples incoming (.var "x" :: query :: pending) := ⟨valuation,model,rfl⟩
      rw [hidden] at packet
      obtain ⟨environment,solved,same⟩ := packet
      exact ⟨environment,solved,(List.cons.inj same).2.trans returned⟩
    · rintro ⟨environment,model,returned⟩
      have packet : (.var "private-result" :: query :: pending).map (read environment) ∈
          observedTuples incoming (.var "x" :: query :: pending) := by
        rw [hidden]
        exact ⟨environment,model,rfl⟩
      obtain ⟨valuation,solved,same⟩ := packet
      exact ⟨valuation,solved,(List.cons.inj same).2.trans returned⟩
  obtain ⟨works,frontier,paired,_bag⟩ := protected_petta_joint_choices_he_frontier
    program caller "f" [.var "alias"] (.var "answer") FrontierControls.older
    FrontierControls.live query incoming pending pending related
  let next (position : Nat) (equation : PeTTa.SpaceSemantics.Equation) : Control :=
    { guarded with
      bindings := guarded.bindings ++ [(query,ClauseChoice.freshPattern guarded position equation)]
      goals := .evaluate (ClauseChoice.freshBody guarded position equation) (.var "answer") :: FrontierControls.older }
  have oldSolved (value : Atom) : Solves (constant value) guarded.bindings := by
    simp [Solves,guarded,protectControl,caller,before,incoming,
      HE.Spec.Type.Presentation.BindingTheory.bindingAtomEquations,
      read_eq_applyTypeValuation,constant,applyTypeValuation]
  have localAccepted (position : Nat) :
      Refinement guarded.bindings query (ClauseChoice.freshPattern guarded position FrontierControls.localRule)
        (some (next position FrontierControls.localRule).bindings) := by
    apply Refinement.accepted (constant (.symbol "A")) (oldSolved _)
    simp [query,ClauseChoice.freshPattern,ClauseChoice.pattern,FrontierControls.localRule,
      renameTypeVars,read_eq_applyTypeValuation,applyTypeValuation,constant,encode,decode]
  have literalAccepted :
      Refinement guarded.bindings query (ClauseChoice.freshPattern guarded 2 FrontierControls.literalRule)
        (some (next 2 FrontierControls.literalRule).bindings) := by
    apply Refinement.accepted (constant (.symbol "B")) (oldSolved _)
    simp [query,ClauseChoice.freshPattern,ClauseChoice.pattern,FrontierControls.literalRule,
      renameTypeVars,read_eq_applyTypeValuation,applyTypeValuation,constant,encode,decode]
  have choicesExact : choices =
      [(0,next 0 FrontierControls.localRule),(1,next 1 FrontierControls.localRule),
        (2,next 2 FrontierControls.literalRule)] := by
    apply (ClauseChoice.choices_iff_frontier _ _ _ _ _ _ _).mpr
    exact .keep (.selected FrontierControls.localRule _ rfl rfl (localAccepted 0))
      (.keep (.selected FrontierControls.localRule _ rfl rfl (localAccepted 1))
        (.keep (.selected FrontierControls.literalRule _ rfl rfl literalAccepted)
          (.skip (.other FrontierControls.otherRule rfl (by decide +kernel)) .nil)))
  have mapping {chosen : List (Nat × Control)} {jobs : List HE.Spec.Eval.Steps.EquationWork}
      (paired : List.Forall₂
        (ClausePendingAgreement guarded query (.var "answer")
          FrontierControls.older pending pending) chosen jobs) :
      jobs.map HE.Spec.Eval.Steps.EquationWork.position = chosen.map Prod.fst := by
    induction paired with
    | nil => rfl
    | cons one _rest ih => simp only [List.map_cons,one.occurrence,ih]
  have selected : choices.map Prod.fst = [0,1,2] := by rw [choicesExact]; rfl
  exact ⟨works,frontier,(mapping paired).trans selected,paired⟩

end ContinuationControls

private theorem matched_expression_lengths
    {before after : MORK.Subst} {patterns values : List Atom}
    (matched : MORK.MatchAtomRel before (.expression patterns) (.expression values) after) :
    patterns.length = values.length := by
  cases matched with
  | expr_nil => rfl
  | expr_cons _ tail =>
      exact congrArg Nat.succ (matched_expression_lengths tail)
termination_by patterns.length

/-- A source match can use a differently ordered HE binding record. Every
lookup, including names saved by an older caller, remains the same. The
structural depth bound is independent of successful or failed search paths. -/
theorem source_match_he_seed
    {before after : MORK.Subst} {pattern value : Atom}
    (matched : MORK.MatchAtomRel before pattern value after)
    (seed : HE.Bindings)
    (lookups : ∀ name, seed.lookup name = before.lookup name)
    (depth : Nat) (enough : sizeOf pattern < depth) :
    ∃ result, HE.simpleMatch pattern value seed depth = some result ∧
      ∀ name, result.lookup name = after.lookup name := by
  induction matched generalizing seed depth with
  | @var_fresh before name value absent =>
      cases depth with
      | zero => simp at enough
      | succ depth =>
          have fresh : seed.lookup name = none := (lookups name).trans absent
          refine ⟨seed.assign name value, by simp [HE.simpleMatch, fresh], ?_⟩
          intro other
          by_cases same : other = name
          · subst other
            simp [HE.lookup_assign_of_lookup_none seed name value fresh, MORK.Subst.lookup]
          · rw [HE.assign_lookup_ne seed name value other same fresh]
            simpa [MORK.Subst.lookup, Ne.symm same] using lookups other
  | @var_bound before name value present =>
      cases depth with
      | zero => simp at enough
      | succ depth =>
          exact ⟨seed, by simp [HE.simpleMatch, (lookups name).trans present], lookups⟩
  | symbol =>
      cases depth with
      | zero => simp at enough
      | succ depth => exact ⟨seed, by simp [HE.simpleMatch], lookups⟩
  | grounded =>
      cases depth with
      | zero => simp at enough
      | succ depth => exact ⟨seed, by simp [HE.simpleMatch], lookups⟩
  | expr_nil =>
      cases depth with
      | zero => simp at enough
      | succ depth =>
          exact ⟨seed, by simp [HE.simpleMatch, HE.simpleMatch.simpleMatchList], lookups⟩
  | @expr_cons before middle after first value patterns values head tail ihHead ihTail =>
      cases depth with
      | zero => simp at enough
      | succ depth =>
          have headEnough : sizeOf first < depth := by
            simp only [Atom.expression.sizeOf_spec, List.cons.sizeOf_spec] at enough
            omega
          have tailEnough : sizeOf (Atom.expression patterns) < depth + 1 := by
            simp only [Atom.expression.sizeOf_spec, List.cons.sizeOf_spec] at enough ⊢
            omega
          obtain ⟨next, headMatch, nextLookups⟩ := ihHead seed lookups depth headEnough
          obtain ⟨result, tailMatch, resultLookups⟩ :=
            ihTail next nextLookups (depth + 1) tailEnough
          have length := matched_expression_lengths tail
          refine ⟨result, ?_, resultLookups⟩
          simpa [HE.simpleMatch, HE.simpleMatch.simpleMatchList, length, headMatch] using tailMatch

/-- Successful structural selection on ground data earns an actual HE query
match. This is a binding/matcher bridge, not whole-program adequacy. The same
result record agrees with every source lookup rather than a chosen operand. -/
theorem source_match_he_query
    {pattern value : Atom} {after : MORK.Subst}
    (matched : MORK.MatchAtomRel [] pattern value after)
    (ground : HE.GroundAtom value) :
    ∃ result depth,
      result ∈ HE.matchAtoms value pattern depth ∧
      2 ≤ depth ∧
      ∀ name, result.lookup name = after.lookup name := by
  obtain ⟨result, selected, lookups⟩ := source_match_he_seed matched HE.Bindings.empty
    (by intro name; simp [HE.Bindings.empty, HE.Bindings.lookup, MORK.Subst.lookup])
    (sizeOf pattern + 1) (Nat.lt_succ_self _)
  obtain ⟨depth, member, enough⟩ := HE.simpleMatch_ground_matchAtoms ground selected
  exact ⟨result, depth, member, enough, lookups⟩

/-- PeTTa's ordinary constructor patterns use the shared structural matcher.
The native `cons` list view is excluded at every position; variables and
nonlinear patterns remain admitted. -/
theorem matchValue_eq_structural (pattern : Atom)
    (ordinary : "cons" ∉ PeTTa.SpaceSemantics.patternHeads pattern)
    (bindings : MORK.Subst) (value : Atom) :
    PeTTa.SpaceSemantics.matchValue bindings pattern value =
      MORK.matchAtom bindings pattern value := by
  match pattern with
  | .var _ | .symbol _ | .grounded _ => simp [PeTTa.SpaceSemantics.matchValue]
  | .expression patterns =>
      have notCons : ∀ first rest, patterns ≠ [.symbol "cons", first, rest] := by
        intro first rest same
        apply ordinary
        simp [same, PeTTa.SpaceSemantics.patternHeads]
      have nested : "cons" ∉ PeTTa.SpaceSemantics.patternHeads.nested patterns := by
        cases patterns with
        | nil => simp [PeTTa.SpaceSemantics.patternHeads.nested]
        | cons first rest =>
            cases first <;>
              simp only [PeTTa.SpaceSemantics.patternHeads, List.mem_append, not_or] at ordinary
            all_goals first | exact ordinary | exact ordinary.2
      cases value with
      | expression values =>
          rw [PeTTa.SpaceSemantics.matchValue_expression_of_not_cons bindings patterns values notCons]
          exact lists patterns nested bindings values
      | var _ | symbol _ | grounded _ =>
          simp [PeTTa.SpaceSemantics.matchValue, MORK.matchAtom]
termination_by sizeOf pattern
where
  lists (patterns : List Atom)
      (ordinary : "cons" ∉ PeTTa.SpaceSemantics.patternHeads.nested patterns)
      (bindings : MORK.Subst) (values : List Atom) :
      PeTTa.SpaceSemantics.matchValue.matchValues bindings patterns values =
        MORK.matchAtom.matchAtomList bindings patterns values := by
    cases patterns with
    | nil => cases values <;> simp [PeTTa.SpaceSemantics.matchValue.matchValues,
        MORK.matchAtom.matchAtomList]
    | cons first rest =>
        simp only [PeTTa.SpaceSemantics.patternHeads.nested, List.mem_append, not_or] at ordinary
        cases values with
        | nil => simp [PeTTa.SpaceSemantics.matchValue.matchValues,
            MORK.matchAtom.matchAtomList]
        | cons value values =>
            simp only [PeTTa.SpaceSemantics.matchValue.matchValues,
              MORK.matchAtom.matchAtomList]
            rw [matchValue_eq_structural first ordinary.1 bindings value]
            cases MORK.matchAtom bindings first value with
            | none => rfl
            | some next => exact lists rest ordinary.2 next values
  termination_by sizeOf patterns

/-- Actual PeTTa clause selection on ground constructor data earns a native
HE matcher occurrence and a single readout for all variable names. No result
permutation or whole-evaluator agreement is assumed. -/
theorem petta_match_he_query
    {pattern value : Atom} {after : MORK.Subst}
    (ordinary : "cons" ∉ PeTTa.SpaceSemantics.patternHeads pattern)
    (ground : HE.GroundAtom value)
    (matched : PeTTa.SpaceSemantics.matchValue [] pattern value = some after) :
    ∃ result depth,
      result ∈ HE.matchAtoms value pattern depth ∧
      2 ≤ depth ∧
      ∀ name, result.lookup name = after.lookup name := by
  rw [matchValue_eq_structural pattern ordinary] at matched
  exact source_match_he_query (MORK.matchAtom_sound matched) ground

/-- On ground-valued records, agreement of every lookup determines complete
structural materialization. Pending expressions need not themselves be closed.
The source and HE records may use different physical assignment order. -/
theorem ground_readout (bindings : HE.Bindings) (substitution : MORK.Subst)
    (ground : HE.GroundBindings bindings)
    (lookups : ∀ name, bindings.lookup name = substitution.lookup name)
    (depth : Nat) (value : Atom) (enough : sizeOf value + 2 ≤ depth) :
    bindings.applyFull value depth = MORK.applySubst substitution value := by
  rw [HE.Bindings.applyFull_no_equalities ground.2]
  have independent : HE.BindingComposition.AssignmentValuesIndependent bindings := by
    intro name value found
    exact hasAssignedVar_false_of_ground (lookup_ground ground found) bindings
  induction depth generalizing value with
  | zero => omega
  | succ depth ih =>
      cases depth with
      | zero => omega
      | succ depth =>
          cases value with
          | symbol name => rfl
          | grounded value => rfl
          | var name =>
              simp only [HE.Bindings.apply,
                HE.BindingComposition.resolve_eq_lookup_of_assignmentValuesIndependent independent,
                lookups, MORK.applySubst]
              cases substitution.lookup name <;> rfl
          | expression children =>
              simp only [HE.Bindings.apply, MORK.applySubst]
              have each : ∀ children : List Atom,
                  sizeOf children + 3 ≤ depth + 2 →
                  children.map (fun child => bindings.apply child (depth + 1)) =
                    MORK.applySubst.applySubstList substitution children := by
                intro children
                induction children with
                | nil => intro _; rfl
                | cons child rest ihRest =>
                    intro bound
                    have headBound : sizeOf child + 2 ≤ depth + 1 := by
                      simp only [List.cons.sizeOf_spec] at bound
                      omega
                    have tailBound : sizeOf rest + 3 ≤ depth + 2 := by
                      simp only [List.cons.sizeOf_spec] at bound
                      omega
                    simp only [List.map_cons, MORK.applySubst.applySubstList,
                      ih child headBound, ihRest tailBound]
              exact congrArg Atom.expression (each children (by
                simp only [Atom.expression.sizeOf_spec] at enough
                omega))

/-- One actual clause match yields one HE record serving the whole future-use
tuple. Each operand is materialized with its earned structural depth; repeated
operands and correlations are preserved without per-operand witnesses. -/
theorem petta_match_he_pending
    {pattern value : Atom} {after : MORK.Subst}
    (ordinary : "cons" ∉ PeTTa.SpaceSemantics.patternHeads pattern)
    (ground : HE.GroundAtom value)
    (matched : PeTTa.SpaceSemantics.matchValue [] pattern value = some after) :
    ∃ result depth,
      result ∈ HE.matchAtoms value pattern depth ∧
      2 ≤ depth ∧
      (∀ name, result.lookup name = after.lookup name) ∧
      ∀ pending : List Atom,
        pending.map (fun operand => result.applyFull operand (sizeOf operand + 2)) =
          pending.map (MORK.applySubst after) := by
  obtain ⟨result, depth, member, enough, lookups⟩ := petta_match_he_query ordinary ground matched
  refine ⟨result, depth, member, enough, lookups, ?_⟩
  intro pending
  apply List.map_congr_left
  intro operand _
  exact ground_readout result after (HE.matchAtoms_ground_bindings ground member)
    lookups (sizeOf operand + 2) operand (Nat.le_refl _)

private theorem flatMap_length_le {α β : Type} (items : List α) (next : α → List β)
    (bound : ∀ item ∈ items, (next item).length ≤ 1) :
    (items.flatMap next).length ≤ items.length := by
  induction items with
  | nil => simp
  | cons first rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have tail := ih (fun item member => bound item (List.mem_cons_of_mem _ member))
      have head := bound first (List.mem_cons_self)
      omega

private theorem ground_merge_length (left right : HE.Bindings) (depth : Nat)
    (leftGround : HE.GroundBindings left) (rightGround : HE.GroundBindings right) :
    (HE.mergeBindings left right depth).length ≤ 1 := by
  cases depth with
  | zero => simp [HE.mergeBindings]
  | succ depth =>
      cases depth with
      | succ depth =>
          rw [mergeBindings_ground_eq_mergeGround depth leftGround rightGround]
          cases mergeGround? left right <;> simp
      | zero =>
          have empty (entries : List (String × Atom)) :
              entries.foldl (fun (before : List HE.Bindings) _ =>
                before.flatMap fun _ => []) [] = [] := by
            induction entries with
            | nil => rfl
            | cons first rest ih => simpa [List.foldl_cons, List.flatMap_nil] using ih
          simp only [HE.mergeBindings, rightGround.2, List.foldl_nil]
          cases right.assignments with
          | nil => simp
          | cons first rest => simp [List.foldl_cons, HE.addVarBinding, empty]

private theorem ground_match_lengths (depth : Nat) :
    (∀ value pattern, HE.GroundAtom value →
      (HE.matchAtoms value pattern depth).length ≤ 1) ∧
    (∀ values patterns incoming,
      (∀ value ∈ values, HE.GroundAtom value) →
      (∀ bindings ∈ incoming, HE.GroundBindings bindings) →
      (HE.matchAtomsList values patterns incoming depth).length ≤ incoming.length) := by
  induction depth with
  | zero => exact ⟨by simp [HE.matchAtoms], by simp [HE.matchAtomsList]⟩
  | succ depth ih =>
      obtain ⟨atoms, lists⟩ := ih
      refine ⟨?_, ?_⟩
      · intro value pattern ground
        have singleton (bindings : HE.Bindings) :
            ([bindings].filter (fun binding => !binding.hasLoop)).length ≤ 1 := by
          exact List.length_filter_le _ _
        cases value with
        | var name => exact HE.GroundAtom.not_var ground |>.elim
        | symbol name =>
            cases pattern with
            | var key =>
                simpa [HE.matchAtoms, HE.getMetaType, Atom.symbolType, Atom.variableType] using
                  singleton (HE.Bindings.empty.assign key (.symbol name))
            | symbol other =>
                by_cases same : name = other
                · simpa [HE.matchAtoms, HE.getMetaType, Atom.symbolType, same] using
                    singleton HE.Bindings.empty
                · simp [HE.matchAtoms, HE.getMetaType, Atom.symbolType, same]
            | grounded value => simp [HE.matchAtoms, HE.getMetaType, Atom.symbolType, Atom.groundedType]
            | expression values => simp [HE.matchAtoms, HE.getMetaType, Atom.symbolType, Atom.expressionType]
        | grounded value =>
            cases pattern with
            | var key =>
                simpa [HE.matchAtoms, HE.getMetaType, Atom.groundedType, Atom.variableType] using
                  singleton (HE.Bindings.empty.assign key (.grounded value))
            | grounded other =>
                by_cases same : value = other
                · simpa [HE.matchAtoms, HE.getMetaType, Atom.groundedType, same] using
                    singleton HE.Bindings.empty
                · simp [HE.matchAtoms, HE.getMetaType, Atom.groundedType, same]
            | symbol name => simp [HE.matchAtoms, HE.getMetaType, Atom.symbolType, Atom.groundedType]
            | expression values => simp [HE.matchAtoms, HE.getMetaType, Atom.groundedType, Atom.expressionType]
        | expression values =>
            cases pattern with
            | expression patterns =>
                rw [HE.matchAtoms_ground_expr_filter_free values patterns depth
                  (fun value member => ground.elem member)]
                split
                · exact lists values patterns [HE.Bindings.empty]
                    (fun value member => ground.elem member)
                    (by intro bindings member; obtain rfl := List.mem_singleton.mp member
                        exact HE.GroundBindings.empty)
                · simp
            | var name =>
                simpa [HE.matchAtoms, HE.getMetaType, Atom.expressionType, Atom.variableType]
                  using singleton (HE.Bindings.empty.assign name (.expression values))
            | symbol name | grounded value =>
                simp [HE.matchAtoms, HE.getMetaType, Atom.symbolType, Atom.groundedType,
                  Atom.expressionType]
      · intro values patterns incoming valuesGround incomingGround
        cases values with
        | nil => cases patterns <;> simp [HE.matchAtomsList]
        | cons value values =>
            cases patterns with
            | nil => simp [HE.matchAtomsList]
            | cons pattern patterns =>
                let next := incoming.flatMap fun before =>
                  (HE.matchAtoms value pattern depth).flatMap fun matched =>
                    HE.mergeBindings before matched depth
                have headGround : HE.GroundAtom value := valuesGround value (by simp)
                have nextGround : ∀ bindings ∈ next, HE.GroundBindings bindings := by
                  intro bindings member
                  obtain ⟨before, beforeMember, inside⟩ := List.mem_flatMap.mp member
                  obtain ⟨matched, matchedMember, merged⟩ := List.mem_flatMap.mp inside
                  exact (HE.matcher_ground depth).2.2.1 _ _ _
                    (incomingGround before beforeMember)
                    (HE.matchAtoms_ground_bindings headGround matchedMember) merged
                have nextLength : next.length ≤ incoming.length := by
                  apply flatMap_length_le
                  intro before member
                  exact (flatMap_length_le _ _ (fun matched matchedMember =>
                    ground_merge_length before matched depth (incomingGround before member)
                      (HE.matchAtoms_ground_bindings headGround matchedMember))).trans
                    (atoms value pattern headGround)
                exact (lists values patterns next
                  (fun item member => valuesGround item (by simp [member])) nextGround).trans nextLength

/-- The equality-grounded HE matcher has at most one occurrence per clause
on a ground query. This list bound does not identify equal occurrences from
different stored copies, or apply to an extensible custom matcher. -/
theorem ground_match_length_le_one (value pattern : Atom) (depth : Nat)
    (ground : HE.GroundAtom value) :
    (HE.matchAtoms value pattern depth).length ≤ 1 :=
  (ground_match_lengths depth).1 value pattern ground

/-- A successful native PeTTa constructor match has exactly one HE matcher
occurrence at every greater depth. The same earned record materializes the
whole pending tuple, without quotienting occurrence multiplicity. -/
theorem petta_match_he_pending_exact
    {pattern value : Atom} {after : MORK.Subst}
    (ordinary : "cons" ∉ PeTTa.SpaceSemantics.patternHeads pattern)
    (ground : HE.GroundAtom value)
    (matched : PeTTa.SpaceSemantics.matchValue [] pattern value = some after) :
    ∃ result depth,
      (∀ extra, HE.matchAtoms value pattern (depth + extra) = [result]) ∧
      2 ≤ depth ∧
      (∀ name, result.lookup name = after.lookup name) ∧
      ∀ pending : List Atom,
        pending.map (fun operand => result.applyFull operand (sizeOf operand + 2)) =
          pending.map (MORK.applySubst after) := by
  obtain ⟨result, depth, member, enough, lookups, pending⟩ :=
    petta_match_he_pending ordinary ground matched
  refine ⟨result, depth, ?_, enough, lookups, pending⟩
  intro extra
  have present := matchAtoms_mono_add value pattern depth extra result member
  have bound := ground_match_length_le_one value pattern (depth + extra) ground
  cases found : HE.matchAtoms value pattern (depth + extra) with
  | nil => simp [found] at present
  | cons first rest =>
      have restEmpty : rest = [] := by
        apply List.length_eq_zero_iff.mp
        simp only [found, List.length_cons] at bound
        omega
      have same : result = first := by simpa [found, restEmpty] using present
      simp [restEmpty, same]

private theorem lookup_entries (entries : MORK.Subst) (name : String) :
    HE.Bindings.lookup ⟨entries, []⟩ name = MORK.Subst.lookup entries name := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨key, value⟩ := entry
      by_cases same : key = name
      · subst key
        simp [HE.Bindings.lookup, MORK.Subst.lookup]
      · have different : (name == key) = false :=
          Bool.eq_false_iff.mpr (fun equal => (Ne.symm same) (eq_of_beq equal))
        simpa [HE.Bindings.lookup, List.lookup_cons, MORK.Subst.lookup, same, different]
          using ih

private theorem lookup_member_unique {entries : MORK.Subst}
    (unique : (entries.map Prod.fst).Nodup) {name : String} {value : Atom}
    (member : (name,value) ∈ entries) :
    HE.Bindings.lookup ⟨entries,[]⟩ name = some value := by
  induction entries with
  | nil => simp at member
  | cons entry rest ih =>
      obtain ⟨key,stored⟩ := entry
      simp only [List.map_cons, List.nodup_cons] at unique
      rcases List.mem_cons.mp member with same | tail
      · cases same
        simp [HE.Bindings.lookup]
      · have different : name ≠ key := by
          intro same
          apply unique.1
          exact List.mem_map.mpr ⟨(name,value),tail,same⟩
        have unequal : (name == key) = false :=
          Bool.eq_false_iff.mpr (fun equal => different (eq_of_beq equal))
        simpa [HE.Bindings.lookup, List.lookup_cons, unequal] using ih unique.2 tail

private theorem encoded_read (substitution : MORK.Subst) (atom : Atom) :
    HE.Spec.Match.SolutionTheory.applyClassSolution
        (fun name => HE.Spec.Match.SolutionTheory.encodeModelAtom (MORK.applySubst substitution (.var name)))
        (HE.Spec.Match.SolutionTheory.encodeModelAtom atom) =
      HE.Spec.Match.SolutionTheory.encodeModelAtom (MORK.applySubst substitution atom) := by
  induction atom using Atom.rec (motive_2 := fun atoms =>
      (HE.Spec.Match.SolutionTheory.encodeModelAtoms atoms).map
        (HE.Spec.Match.SolutionTheory.applyClassSolution
          (fun name => HE.Spec.Match.SolutionTheory.encodeModelAtom (MORK.applySubst substitution (.var name)))) =
        HE.Spec.Match.SolutionTheory.encodeModelAtoms (MORK.applySubst.applySubstList substitution atoms)) with
  | symbol _ | var _ | grounded _ =>
      simp only [HE.Spec.Match.SolutionTheory.encodeModelAtom, HE.Spec.Match.SolutionTheory.applyClassSolution, MORK.applySubst]
  | expression atoms ih =>
      simpa only [HE.Spec.Match.SolutionTheory.encodeModelAtom, HE.Spec.Match.SolutionTheory.applyClassSolution,
        MORK.applySubst] using congrArg Metta.Atom.expr ih
  | nil => rfl
  | cons atom atoms head tail => exact congrArg₂ List.cons head tail

/-- Source substitution is the corresponding atom-valued valuation. This
is a structural carrier law; no interpreter or native binding table is used. -/
theorem source_read (substitution : MORK.Subst) (atom : Atom) :
    HE.Spec.Type.RuntimeRefinement.applyTypeValuation
      (fun name => MORK.applySubst substitution (.var name)) atom =
      MORK.applySubst substitution atom := by
  apply HE.Spec.Match.SolutionTheory.encodeModelAtom_injective
  simpa only [HE.Spec.Bindings.ScopeObservation.ModelTransport.encodeModelAtom_applyTypeValuation] using
    encoded_read substitution atom

/-- On a closed query, legal freshening separates rule satisfiability from
the caller's representation. Any satisfiable caller theory is retained; no
choice of its variable representatives determines clause selection. -/
theorem fresh_candidate_iff_raw_solution
    {live : List Atom} {query rawPattern rawBody pattern body : Atom} {incoming : HE.Bindings}
    (variant : HE.Spec.Eval.Steps.AlphaVariantRel live query incoming rawPattern rawBody pattern body)
    (closed : HE.Spec.Type.Presentation.TypeSubst.typeVars query = [])
    (caller : ∃ valuation, HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation incoming) :
    (∃ output, HE.Spec.Eval.Steps.UnifyCandidateRel query pattern incoming output) ↔
      ∃ valuation, HE.Spec.Type.RuntimeRefinement.applyTypeValuation valuation rawPattern = query := by
  have queryFixed (valuation : String → Atom) :=
    HE.Spec.Type.Presentation.applyTypeValuation_of_typeVars_eq_nil valuation query closed
  constructor
  · rintro ⟨output,candidate⟩
    have theory := candidate.solutions
    obtain ⟨_matched,_matching,merged⟩ := candidate
    obtain ⟨valuation,satisfied⟩ := merged.2
    have equation := ((theory valuation).mp satisfied).1
    obtain ⟨rename,_injective,renamed,_body,_fresh⟩ := variant
    refine ⟨valuation ∘ rename,?_⟩
    rw [←HE.Spec.Type.Presentation.ApplicationEquivariance.applyTypeValuation_renameTypeVars,
      ←HE.EquationFreshening.alphaRename_eq renamed]
    exact equation.symm.trans (queryFixed valuation)
  · rintro ⟨rule,instanceImage⟩
    obtain ⟨base,satisfied⟩ := caller
    obtain ⟨combined,retained,patternRead,_agrees⟩ :=
      HE.EquationScope.fresh_pattern_model variant base rule satisfied
    let environment : PeTTa.EagerDFS.Destination.Environment := fun name =>
      PeTTa.EagerDFS.Destination.encode (combined name)
    apply (petta_accepted_iff_he_candidate incoming query pattern).mp
    refine ⟨_,.accepted environment ?_ ?_⟩
    · apply (solves_binding_equations environment incoming).mpr
      simpa only [environment,decode_encode] using retained
    · rw [read_eq_applyTypeValuation,read_eq_applyTypeValuation]
      simpa only [environment,decode_encode] using
        (queryFixed combined).trans (patternRead.trans instanceImage).symm

/-- Successful fresh selection on closed query data preserves the complete
caller observer. New private constraints neither remove caller models nor
change protected query, continuation or binding observations. -/
theorem fresh_candidate_caller_theory
    {live : List Atom} {query rawPattern rawBody pattern body : Atom} {incoming output : HE.Bindings}
    (substitution : MORK.Subst)
    (variant : HE.Spec.Eval.Steps.AlphaVariantRel live query incoming rawPattern rawBody pattern body)
    (instanceImage : MORK.applySubst substitution rawPattern = query)
    (closed : HE.Spec.Type.Presentation.TypeSubst.typeVars query = [])
    (candidate : HE.Spec.Eval.Steps.UnifyCandidateRel query pattern incoming output) :
    HE.Spec.Bindings.ScopeObservation.BindingTheoryEquivAt
      (HE.EquationScope.visibleNames live query incoming) incoming output := by
  constructor
  · intro caller satisfied
    obtain ⟨combined,retained,patternRead,agrees⟩ := HE.EquationScope.fresh_pattern_model variant caller
      (fun name => MORK.applySubst substitution (.var name)) satisfied
    have freshImage := patternRead.trans ((source_read substitution rawPattern).trans instanceImage)
    have queryFixed := HE.Spec.Type.Presentation.applyTypeValuation_of_typeVars_eq_nil combined query closed
    exact ⟨combined,(candidate.solutions combined).mpr ⟨queryFixed.trans freshImage.symm,retained⟩,agrees⟩
  · intro reached satisfied
    exact ⟨reached,((candidate.solutions reached).mp satisfied).2,fun _ _ => rfl⟩

/-- A structural source match constructs the compatible fresh HE candidate
and retains the actual substitution image used later to materialize its body. -/
theorem source_match_fresh_candidate
    {live : List Atom} {query rawPattern rawBody pattern body : Atom} {incoming : HE.Bindings}
    {substitution : MORK.Subst}
    (variant : HE.Spec.Eval.Steps.AlphaVariantRel live query incoming rawPattern rawBody pattern body)
    (closed : HE.Spec.Type.Presentation.TypeSubst.typeVars query = [])
    (ground : MORK.isGroundAtom query = true)
    (caller : ∃ valuation, HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation incoming)
    (matched : MORK.MatchAtomRel [] rawPattern query substitution) :
    MORK.applySubst substitution rawPattern = query ∧
      ∃ output, HE.Spec.Eval.Steps.UnifyCandidateRel query pattern incoming output := by
  have image := matched.applySubst_ground ground
  refine ⟨image,(fresh_candidate_iff_raw_solution variant closed caller).mpr ?_⟩
  exact ⟨_,(source_read substitution rawPattern).trans image⟩

/-- Every model fixing the fresh pattern fixes all covered body positions.
This transports source substitution through one simultaneous rule instance. -/
theorem source_template_model
    {live : List Atom} {query rawPattern rawBody freshPattern freshBody : Atom}
    {incoming : HE.Bindings} (substitution : MORK.Subst)
    (variant : HE.Spec.Eval.Steps.AlphaVariantRel live query incoming
      rawPattern rawBody freshPattern freshBody)
    (instanceImage : MORK.applySubst substitution rawPattern = query)
    (covered : ∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVars rawBody,
      name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVars rawPattern)
    (valuation : String → Atom)
    (patternFixed : HE.Spec.Type.RuntimeRefinement.applyTypeValuation valuation freshPattern = query) :
    HE.Spec.Type.RuntimeRefinement.applyTypeValuation valuation freshBody =
      MORK.applySubst substitution rawBody := by
  obtain ⟨rename,_injective,pattern,body,_fresh⟩ := variant
  have patternShape := HE.EquationFreshening.alphaRename_eq pattern
  have bodyShape := HE.EquationFreshening.alphaRename_eq body
  have patternRead : HE.Spec.Type.RuntimeRefinement.applyTypeValuation (valuation ∘ rename) rawPattern = query := by
    rw [←HE.Spec.Type.Presentation.ApplicationEquivariance.applyTypeValuation_renameTypeVars,←patternShape]
    exact patternFixed
  have same : HE.Spec.Type.RuntimeRefinement.applyTypeValuation (valuation ∘ rename) rawPattern =
      HE.Spec.Type.RuntimeRefinement.applyTypeValuation
        (fun name => MORK.applySubst substitution (.var name)) rawPattern :=
    patternRead.trans ((source_read substitution rawPattern).trans instanceImage).symm
  rw [bodyShape,HE.Spec.Type.Presentation.ApplicationEquivariance.applyTypeValuation_renameTypeVars]
  exact (HE.Spec.Type.Presentation.applyTypeValuation_template_eq_of_pattern_eq _ _ _ _ covered same).trans
    (source_read substitution rawBody)

/-- A fixed fresh pattern determines every covered body in the retained
readout. The source substitution supplies the pattern instance, not a desired
HE table or an assumed evaluation result. -/
theorem source_template_readout
    {live : List Atom} {query rawPattern rawBody freshPattern freshBody : Atom}
    {incoming output : HE.Bindings} {table : HE.Spec.Type.Presentation.TypeSubst}
    (substitution : MORK.Subst)
    (variant : HE.Spec.Eval.Steps.AlphaVariantRel live query incoming
      rawPattern rawBody freshPattern freshBody)
    (instanceImage : MORK.applySubst substitution rawPattern = query)
    (covered : ∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVars rawBody,
      name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVars rawPattern)
    (certified : HE.Spec.Type.Presentation.BindingTheory.ReadoutCertificate output table)
    (patternFixed : ∀ valuation, HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation output →
      HE.Spec.Type.RuntimeRefinement.applyTypeValuation valuation freshPattern = query) :
    table.apply freshBody = MORK.applySubst substitution rawBody := by
  apply certified.forced_read
  intro valuation satisfied
  exact source_template_model substitution variant instanceImage covered valuation
    (patternFixed valuation satisfied)

/-- An actual source query occurrence earns that fixed-pattern premise.
Closed query data, rather than a representation choice, makes the selected
fresh body agree with the source substitution in every certified frame. -/
theorem query_occurrence_template_readout
    {space : HE.Space} {live : List Atom} {query rawPattern rawBody freshPattern freshBody emitted : Atom}
    {incoming matched output : HE.Bindings} {position : Nat}
    {table : HE.Spec.Type.Presentation.TypeSubst} (substitution : MORK.Subst)
    (selected : HE.Spec.Eval.Steps.EquationQueryOccurrenceRel space live query incoming position
      rawPattern rawBody freshPattern freshBody matched emitted output)
    (instanceImage : MORK.applySubst substitution rawPattern = query)
    (covered : ∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVars rawBody,
      name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVars rawPattern)
    (closed : HE.Spec.Type.Presentation.TypeSubst.typeVars query = [])
    (certified : HE.Spec.Type.Presentation.BindingTheory.ReadoutCertificate output table) :
    table.apply freshBody = MORK.applySubst substitution rawBody := by
  apply source_template_readout substitution selected.selected.1 instanceImage covered certified
  intro valuation satisfied
  have candidate : HE.Spec.Eval.Steps.UnifyCandidateRel query freshPattern incoming output :=
    ⟨matched,selected.selected.2,selected.result.1⟩
  have equation := ((candidate.solutions valuation).mp satisfied).1
  have fixed := HE.Spec.Type.Presentation.applyTypeValuation_of_typeVars_eq_nil valuation query closed
  exact equation.symm.trans fixed

private theorem finite_model_lookup (valuation : String → Metta.Atom)
    (names : List String) {name : String} (member : name ∈ names) :
    MORK.Subst.lookup
        (names.map fun key => (key, HE.Spec.Match.SolutionTheory.decodeModelAtom (valuation key)))
        name = some (HE.Spec.Match.SolutionTheory.decodeModelAtom (valuation name)) := by
  induction names with
  | nil => cases member
  | cons first rest ih =>
      by_cases same : first = name
      · subst first
        simp [MORK.Subst.lookup]
      · have later : name ∈ rest := (List.mem_cons.mp member).resolve_left (Ne.symm same)
        simpa [MORK.Subst.lookup, same] using ih later

private theorem decoded_model_read (valuation : String → Metta.Atom) (atom : Atom) :
    ∀ substitution : MORK.Subst,
      (∀ name ∈ MORK.atomFreeVars atom,
        substitution.lookup name = some
          (HE.Spec.Match.SolutionTheory.decodeModelAtom (valuation name))) →
      MORK.applySubst substitution atom = HE.Spec.Match.SolutionTheory.decodeModelAtom
        (HE.Spec.Match.SolutionTheory.applyClassSolution valuation (HE.Spec.Match.SolutionTheory.encodeModelAtom atom)) := by
  induction atom using Atom.rec (motive_2 := fun atoms =>
      ∀ substitution : MORK.Subst,
        (∀ name ∈ MORK.atomFreeVars.atomFreeVarsList atoms,
          substitution.lookup name = some
            (HE.Spec.Match.SolutionTheory.decodeModelAtom (valuation name))) →
        MORK.applySubst.applySubstList substitution atoms =
          HE.Spec.Match.SolutionTheory.decodeModelAtoms
            ((HE.Spec.Match.SolutionTheory.encodeModelAtoms atoms).map
              (HE.Spec.Match.SolutionTheory.applyClassSolution valuation))) with
  | symbol name =>
      intro substitution _
      simp only [MORK.applySubst, HE.Spec.Match.SolutionTheory.encodeModelAtom,
        HE.Spec.Match.SolutionTheory.applyClassSolution, HE.Spec.Match.SolutionTheory.decodeModelAtom]
  | grounded value =>
      intro substitution _
      simp only [MORK.applySubst, HE.Spec.Match.SolutionTheory.encodeModelAtom,
        HE.Spec.Match.SolutionTheory.applyClassSolution, HE.Spec.Match.SolutionTheory.decodeModelAtom,
        HE.Spec.Match.SolutionTheory.decodeModelGround_encodeModelGround]
  | var name =>
      intro substitution reads
      simp only [MORK.applySubst, HE.Spec.Match.SolutionTheory.encodeModelAtom,
        HE.Spec.Match.SolutionTheory.applyClassSolution, reads name (by simp [MORK.atomFreeVars]),
        Option.getD_some]
  | expression atoms ih =>
      intro substitution reads
      simpa only [MORK.applySubst, HE.Spec.Match.SolutionTheory.encodeModelAtom,
        HE.Spec.Match.SolutionTheory.applyClassSolution, HE.Spec.Match.SolutionTheory.decodeModelAtom] using
        congrArg Atom.expression (ih substitution reads)
  | nil =>
      simp only [MORK.applySubst.applySubstList, HE.Spec.Match.SolutionTheory.encodeModelAtoms,
        List.map_nil, HE.Spec.Match.SolutionTheory.decodeModelAtoms]
  | cons atom atoms head tail =>
      rename_i substitution reads
      have first := head substitution (fun name member =>
        reads name (List.mem_append_left _ member))
      have rest := tail substitution (fun name member =>
        reads name (List.mem_append_right _ member))
      simpa only [MORK.applySubst.applySubstList, HE.Spec.Match.SolutionTheory.encodeModelAtoms,
        List.map_cons, HE.Spec.Match.SolutionTheory.decodeModelAtoms] using
        congrArg₂ List.cons first rest

private theorem ground_model_read (valuation : String → Metta.Atom) {value : Atom}
    (ground : HE.GroundAtom value) :
    HE.Spec.Match.SolutionTheory.applyClassSolution valuation (HE.Spec.Match.SolutionTheory.encodeModelAtom value) =
      HE.Spec.Match.SolutionTheory.encodeModelAtom value := by
  induction value using Atom.rec (motive_2 := fun values =>
      (∀ value ∈ values, HE.GroundAtom value) →
        (HE.Spec.Match.SolutionTheory.encodeModelAtoms values).map
            (HE.Spec.Match.SolutionTheory.applyClassSolution valuation) =
          HE.Spec.Match.SolutionTheory.encodeModelAtoms values) with
  | symbol _ | grounded _ =>
      simp only [HE.Spec.Match.SolutionTheory.encodeModelAtom, HE.Spec.Match.SolutionTheory.applyClassSolution]
  | var _ => exact HE.GroundAtom.not_var ground |>.elim
  | expression values ih =>
      simpa only [HE.Spec.Match.SolutionTheory.encodeModelAtom, HE.Spec.Match.SolutionTheory.applyClassSolution] using
        congrArg Metta.Atom.expr (ih (fun value member => ground.elem member))
  | nil => simp only [HE.Spec.Match.SolutionTheory.encodeModelAtoms, List.map_nil]
  | cons value values head tail =>
      rename_i allGround
      simpa only [HE.Spec.Match.SolutionTheory.encodeModelAtoms, List.map_cons] using
        congrArg₂ List.cons (head (allGround value (by simp)))
          (tail (fun item member => allGround item (by simp [member])))

private theorem ground_source_read (substitution : MORK.Subst) {value : Atom}
    (ground : HE.GroundAtom value) : MORK.applySubst substitution value = value := by
  induction value using Atom.rec (motive_2 := fun values =>
      (∀ value ∈ values, HE.GroundAtom value) →
        MORK.applySubst.applySubstList substitution values = values) with
  | symbol _ | grounded _ => rfl
  | var _ => exact HE.GroundAtom.not_var ground |>.elim
  | expression values ih =>
      exact congrArg Atom.expression (ih (fun value member => ground.elem member))
  | nil => rfl
  | cons value values head tail =>
      rename_i allGround
      exact congrArg₂ List.cons (head (allGround value (by simp)))
        (tail (fun item member => allGround item (by simp [member])))

/-- Structural matching can be reconstructed from a whole substitution image.
The seed only fixes already-captured values; it does not supply a desired
matcher answer or an equality between engine binding records. -/
private theorem source_match_of_image (substitution : MORK.Subst) (pattern : Atom) :
    ∀ (seed : MORK.Subst) (value : Atom),
      (∀ name stored, seed.lookup name = some stored →
        MORK.applySubst substitution (.var name) = stored) →
      MORK.applySubst substitution pattern = value →
      ∃ after, MORK.matchAtom seed pattern value = some after ∧
        ∀ name stored, after.lookup name = some stored →
          MORK.applySubst substitution (.var name) = stored := by
  induction pattern using Atom.rec (motive_2 := fun patterns =>
      ∀ (seed : MORK.Subst) (values : List Atom),
        (∀ name stored, seed.lookup name = some stored →
          MORK.applySubst substitution (.var name) = stored) →
        MORK.applySubst.applySubstList substitution patterns = values →
        ∃ after, MORK.matchAtom.matchAtomList seed patterns values = some after ∧
          ∀ name stored, after.lookup name = some stored →
            MORK.applySubst substitution (.var name) = stored) with
  | symbol name =>
      intro seed value compatible image
      cases image
      exact ⟨seed, by simp [MORK.applySubst, MORK.matchAtom], compatible⟩
  | grounded payload =>
      intro seed value compatible image
      cases image
      exact ⟨seed, by simp [MORK.applySubst, MORK.matchAtom], compatible⟩
  | var name =>
      intro seed value compatible image
      cases selected : seed.lookup name with
      | some stored =>
          have same : value = stored := image.symm.trans (compatible name stored selected)
          exact ⟨seed, by simp [MORK.matchAtom, selected, same], compatible⟩
      | none =>
          refine ⟨(name,value)::seed, by simp [MORK.matchAtom, selected], ?_⟩
          intro other stored found
          by_cases same : other = name
          · subst other
            have equal : value = stored := by simpa [MORK.Subst.lookup] using found
            exact image.trans equal
          · apply compatible other stored
            simpa [MORK.Subst.lookup, Ne.symm same] using found
  | expression patterns ih =>
      intro seed value compatible image
      cases image
      obtain ⟨after, selected, preserved⟩ := ih seed _ compatible rfl
      exact ⟨after, selected, preserved⟩
  | nil =>
      rename_i seed values compatible image
      cases image
      exact ⟨seed, rfl, compatible⟩
  | cons pattern patterns head tail =>
      rename_i seed values compatible image
      cases image
      obtain ⟨middle, first, nextCompatible⟩ := head seed _ compatible rfl
      obtain ⟨after, rest, preserved⟩ := tail middle _ nextCompatible rfl
      refine ⟨after, ?_, preserved⟩
      simp only [MORK.applySubst.applySubstList, MORK.matchAtom.matchAtomList, first]
      exact rest

/-- A structural pattern instance determines an actual source match. The
finite substitution is constructed from the model on the pattern's support. -/
theorem source_solution_match (valuation : String → Atom) (pattern query : Atom)
    (image : HE.Spec.Type.RuntimeRefinement.applyTypeValuation valuation pattern = query) :
    ∃ after, MORK.MatchAtomRel [] pattern query after := by
  let encoded : String → Metta.Atom := fun name => HE.Spec.Match.SolutionTheory.encodeModelAtom (valuation name)
  let substitution : MORK.Subst := (MORK.atomFreeVars pattern).map fun name =>
    (name, HE.Spec.Match.SolutionTheory.decodeModelAtom (encoded name))
  have read := decoded_model_read encoded pattern substitution
    (fun _ member => finite_model_lookup encoded _ member)
  have materialized : MORK.applySubst substitution pattern = query := by
    rw [read,←HE.Spec.Bindings.ScopeObservation.ModelTransport.encodeModelAtom_applyTypeValuation]
    simpa only [HE.Spec.Match.SolutionTheory.decodeModelAtom_encodeModelAtom] using image
  obtain ⟨after,matched,_reads⟩ := source_match_of_image substitution pattern [] query
    (by intro name stored found; simp [MORK.Subst.lookup] at found) materialized
  exact ⟨after,MORK.matchAtom_sound matched⟩

/-- Closed ground clause selection agrees independently of fresh spelling or
the representation of satisfiable caller constraints. This is a matching law,
not an assumption that the two evaluators already agree. -/
theorem fresh_candidate_iff_source_match
    {live : List Atom} {query rawPattern rawBody pattern body : Atom} {incoming : HE.Bindings}
    (variant : HE.Spec.Eval.Steps.AlphaVariantRel live query incoming rawPattern rawBody pattern body)
    (closed : HE.Spec.Type.Presentation.TypeSubst.typeVars query = [])
    (ground : MORK.isGroundAtom query = true)
    (caller : ∃ valuation, HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation incoming) :
    (∃ output, HE.Spec.Eval.Steps.UnifyCandidateRel query pattern incoming output) ↔
      ∃ substitution, MORK.MatchAtomRel [] rawPattern query substitution := by
  rw [fresh_candidate_iff_raw_solution variant closed caller]
  constructor
  · rintro ⟨valuation,image⟩
    exact source_solution_match valuation rawPattern query image
  · rintro ⟨substitution,matched⟩
    exact ⟨_,(source_read substitution rawPattern).trans (matched.applySubst_ground ground)⟩

/-- A satisfiable pattern equation over ground constructor data constructs an
actual PeTTa match. The finite table is obtained from the model on the pattern's
own variables, rather than supplied as a desired matcher result. -/
theorem solution_petta_match {pattern value : Atom}
    (ordinary : "cons" ∉ PeTTa.SpaceSemantics.patternHeads pattern)
    (ground : HE.GroundAtom value)
    (model : ∃ valuation, HE.Spec.Match.SolutionTheory.HEAtomEquationSatisfied valuation value pattern) :
    ∃ after, PeTTa.SpaceSemantics.matchValue [] pattern value = some after := by
  obtain ⟨valuation, equation⟩ := model
  let substitution : MORK.Subst := (MORK.atomFreeVars pattern).map fun name =>
    (name, HE.Spec.Match.SolutionTheory.decodeModelAtom (valuation name))
  have image := decoded_model_read valuation pattern substitution
    (fun _ member => finite_model_lookup valuation _ member)
  have decoded : HE.Spec.Match.SolutionTheory.decodeModelAtom
      (HE.Spec.Match.SolutionTheory.applyClassSolution valuation
        (HE.Spec.Match.SolutionTheory.encodeModelAtom pattern)) = value := by
    change HE.Spec.Match.SolutionTheory.applyClassSolution valuation
        (HE.Spec.Match.SolutionTheory.encodeModelAtom value) = _ at equation
    rw [ground_model_read valuation ground] at equation
    simpa only [HE.Spec.Match.SolutionTheory.decodeModelAtom_encodeModelAtom] using
      congrArg HE.Spec.Match.SolutionTheory.decodeModelAtom equation.symm
  obtain ⟨after, selected, _⟩ := source_match_of_image substitution pattern [] value
    (by intro name stored found; simp [MORK.Subst.lookup] at found) (image.trans decoded)
  exact ⟨after, by rw [matchValue_eq_structural pattern ordinary]; exact selected⟩

private theorem ground_match_has_model {pattern value : Atom}
    {result : HE.Bindings} {depth : Nat} (ground : HE.GroundAtom value)
    (matched : result ∈ HE.matchAtoms value pattern depth) :
    ∃ valuation, HE.Spec.Match.SolutionTheory.HEBindingSatisfied valuation result := by
  let substitution : MORK.Subst := result.assignments
  let valuation : String → Metta.Atom := fun name =>
    HE.Spec.Match.SolutionTheory.encodeModelAtom (MORK.applySubst substitution (.var name))
  have canonical := matchAtoms_ground_canon ground matched
  have model : HE.Spec.Match.SolutionTheory.HEBindingSatisfied valuation result := by
    refine ⟨?_, ?_⟩
    · intro name stored member
      have native : result.lookup name = some stored := lookup_member_unique canonical.2 member
      have source : substitution.lookup name = some stored := (lookup_entries _ _).symm.trans native
      have storedGround : HE.GroundAtom stored := canonical.1.1 _ member
      change HE.Spec.Match.SolutionTheory.encodeModelAtom (MORK.applySubst substitution (.var name)) = _
      rw [encoded_read substitution stored, ground_source_read substitution storedGround]
      simp only [MORK.applySubst, source, Option.getD_some]
    · intro left right edge
      simp [canonical.1.2] at edge
  exact ⟨valuation, model⟩

/-- Constructor matching succeeds exactly when the pattern equation has a
model. No executable HE or PeTTa answer appears in the equation theory. -/
theorem petta_match_iff_solution {pattern value : Atom}
    (ordinary : "cons" ∉ PeTTa.SpaceSemantics.patternHeads pattern)
    (ground : HE.GroundAtom value) :
    (∃ after, PeTTa.SpaceSemantics.matchValue [] pattern value = some after) ↔
      ∃ valuation, HE.Spec.Match.SolutionTheory.HEAtomEquationSatisfied valuation value pattern := by
  constructor
  · rintro ⟨after, selected⟩
    obtain ⟨result, depth, matched, _, _⟩ := petta_match_he_query ordinary ground selected
    obtain ⟨valuation, satisfied⟩ := ground_match_has_model ground matched
    exact ⟨valuation, (HE.BindingComposition.matchAtoms_solution_iff matched valuation).mp satisfied⟩
  · exact solution_petta_match ordinary ground

/-- Every satisfiable independent match derivation at the query boundary
constructs a PeTTa constructor match. Query result conjunction supplies the
model; no runtime matcher completeness assumption is used. -/
theorem spec_match_petta {pattern value : Atom} {bindings : HE.Bindings}
    (ordinary : "cons" ∉ PeTTa.SpaceSemantics.patternHeads pattern)
    (ground : HE.GroundAtom value)
    (matched : HE.Spec.Match.Merge.MatchRel HE.Spec.Match.Merge.equalityGroundedSemantic
      value pattern bindings)
    (model : ∃ valuation, HE.Spec.Match.SolutionTheory.HEBindingSatisfied valuation bindings) :
    ∃ after, PeTTa.SpaceSemantics.matchValue [] pattern value = some after := by
  obtain ⟨valuation, satisfied⟩ := model
  exact solution_petta_match ordinary ground
    ⟨valuation, (HE.Spec.Match.SolutionTheory.matchRel_solution_iff matched valuation).mp satisfied⟩

/-- A source match and its satisfiable conjunction earn an exact HE matcher
frontier and the same PeTTa readout for every pending operand. The provided
source binding layout is not identified with either engine's layout. -/
theorem spec_match_he_pending_exact {pattern value : Atom} {bindings : HE.Bindings}
    (ordinary : "cons" ∉ PeTTa.SpaceSemantics.patternHeads pattern)
    (ground : HE.GroundAtom value)
    (matched : HE.Spec.Match.Merge.MatchRel HE.Spec.Match.Merge.equalityGroundedSemantic
      value pattern bindings)
    (model : ∃ valuation, HE.Spec.Match.SolutionTheory.HEBindingSatisfied valuation bindings) :
    ∃ after result depth,
      PeTTa.SpaceSemantics.matchValue [] pattern value = some after ∧
      (∀ extra, HE.matchAtoms value pattern (depth + extra) = [result]) ∧
      2 ≤ depth ∧ (∀ name, result.lookup name = after.lookup name) ∧
      ∀ pending : List Atom,
        pending.map (fun operand => result.applyFull operand (sizeOf operand + 2)) =
          pending.map (MORK.applySubst after) := by
  obtain ⟨after, selected⟩ := spec_match_petta ordinary ground matched model
  obtain ⟨result, depth, complete, enough, lookups, reads⟩ :=
    petta_match_he_pending_exact ordinary ground selected
  exact ⟨after, result, depth, selected, complete, enough, lookups, reads⟩

/-- A physical independent query occurrence supplies its own common model
through the result conjunction. Its chosen fresh pattern therefore earns both
actual matcher frontiers, without an extra model or completeness premise. -/
theorem query_occurrence_he_pending_exact
    {space : HE.Space} {live : List Atom} {query : Atom} {incoming : HE.Bindings}
    {position : Nat} {rawLhs rawRhs freshPattern freshRhs emitted : Atom}
    {matched output : HE.Bindings}
    (ordinary : "cons" ∉ PeTTa.SpaceSemantics.patternHeads freshPattern)
    (ground : HE.GroundAtom query)
    (occurrence : HE.Spec.Eval.Steps.EquationQueryOccurrenceRel space live query incoming
      position rawLhs rawRhs freshPattern freshRhs matched emitted output) :
    ∃ after result depth,
      PeTTa.SpaceSemantics.matchValue [] freshPattern query = some after ∧
      (∀ extra, HE.matchAtoms query freshPattern (depth + extra) = [result]) ∧
      2 ≤ depth ∧ (∀ name, result.lookup name = after.lookup name) ∧
      ∀ pending : List Atom,
        pending.map (fun operand => result.applyFull operand (sizeOf operand + 2)) =
          pending.map (MORK.applySubst after) := by
  obtain ⟨valuation, satisfied⟩ := occurrence.result.1.2
  have common := (HE.Spec.Bindings.ScopeObservation.bindingSatisfied_append_iff
    valuation matched incoming).mp ((occurrence.result.1.1.solutions valuation).mp satisfied)
  exact spec_match_he_pending_exact ordinary ground occurrence.selected.2
    ⟨_, HE.Spec.Bindings.ScopeObservation.ModelTransport.heBindingSatisfied_of_specTypeBindingSatisfied common.1⟩

/-- A rejected ground constructor pattern excludes a source occurrence at
that chosen fresh instance, for every caller conjunction and emitted value.
Physical source rows and alternative alpha-instances remain separate inputs. -/
theorem no_query_occurrence_of_petta_mismatch
    {space : HE.Space} {live : List Atom} {query : Atom} {incoming : HE.Bindings}
    {position : Nat} {rawLhs rawRhs freshPattern freshRhs emitted : Atom}
    {matched output : HE.Bindings}
    (ordinary : "cons" ∉ PeTTa.SpaceSemantics.patternHeads freshPattern)
    (ground : HE.GroundAtom query)
    (refused : PeTTa.SpaceSemantics.matchValue [] freshPattern query = none) :
    ¬HE.Spec.Eval.Steps.EquationQueryOccurrenceRel space live query incoming
      position rawLhs rawRhs freshPattern freshRhs matched emitted output := by
  intro occurrence
  obtain ⟨after, result, depth, selected, _⟩ :=
    query_occurrence_he_pending_exact ordinary ground occurrence
  rw [refused] at selected
  contradiction

/-- Failure on ground constructors means that the independent pattern
equation has no model, rather than merely no answer within one depth bound. -/
theorem petta_mismatch_iff_no_solution {pattern value : Atom}
    (ordinary : "cons" ∉ PeTTa.SpaceSemantics.patternHeads pattern)
    (ground : HE.GroundAtom value) :
    PeTTa.SpaceSemantics.matchValue [] pattern value = none ↔
      ¬∃ valuation, HE.Spec.Match.SolutionTheory.HEAtomEquationSatisfied valuation value pattern := by
  constructor
  · intro refused model
    obtain ⟨after, selected⟩ := solution_petta_match ordinary ground model
    rw [refused] at selected
    contradiction
  · intro unsatisfiable
    cases selected : PeTTa.SpaceSemantics.matchValue [] pattern value with
    | none => rfl
    | some after =>
        exact (unsatisfiable ((petta_match_iff_solution ordinary ground).mp
          ⟨after, selected⟩)).elim

/-- Every actual equality-grounded HE match on a ground query reflects to
PeTTa's constructor matcher. Its own solution theory earns the source image;
no LeaTTa evaluation or cross-engine conformance theorem is imported. -/
theorem he_match_petta
    {pattern value : Atom} {result : HE.Bindings} {depth : Nat}
    (ordinary : "cons" ∉ PeTTa.SpaceSemantics.patternHeads pattern)
    (ground : HE.GroundAtom value)
    (matched : result ∈ HE.matchAtoms value pattern depth) :
    ∃ after, PeTTa.SpaceSemantics.matchValue [] pattern value = some after := by
  obtain ⟨valuation, satisfied⟩ := ground_match_has_model ground matched
  exact solution_petta_match ordinary ground
    ⟨valuation, (HE.BindingComposition.matchAtoms_solution_iff matched valuation).mp satisfied⟩

/-- Reflection retains the actual HE result record. Singleton matching at a
common larger depth identifies the earned source image, so one lookup relation
and one pending-tuple readout work in both directions. -/
theorem he_match_petta_pending
    {pattern value : Atom} {result : HE.Bindings} {depth : Nat}
    (ordinary : "cons" ∉ PeTTa.SpaceSemantics.patternHeads pattern)
    (ground : HE.GroundAtom value)
    (matched : result ∈ HE.matchAtoms value pattern depth) :
    ∃ after, PeTTa.SpaceSemantics.matchValue [] pattern value = some after ∧
      (∀ name, result.lookup name = after.lookup name) ∧
      ∀ pending : List Atom,
        pending.map (fun operand => result.applyFull operand (sizeOf operand + 2)) =
          pending.map (MORK.applySubst after) := by
  obtain ⟨after, selected⟩ := he_match_petta ordinary ground matched
  obtain ⟨earned, needed, complete, _, lookups, reads⟩ :=
    petta_match_he_pending_exact ordinary ground selected
  have later : result ∈ HE.matchAtoms value pattern (needed + depth) := by
    simpa only [Nat.add_comm] using matchAtoms_mono_add value pattern depth needed result matched
  rw [complete depth, List.mem_singleton] at later
  exact ⟨after, selected, later ▸ lookups, later ▸ reads⟩

/-- An independently failed constructor match excludes HE matcher answers at
all depths. An empty prefix at a chosen depth is not used as failure evidence. -/
theorem petta_mismatch_iff_he_empty (pattern value : Atom)
    (ordinary : "cons" ∉ PeTTa.SpaceSemantics.patternHeads pattern)
    (ground : HE.GroundAtom value) :
    PeTTa.SpaceSemantics.matchValue [] pattern value = none ↔
      ∀ depth, HE.matchAtoms value pattern depth = [] := by
  constructor
  · intro refused depth
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro result member
    obtain ⟨after, selected⟩ := he_match_petta ordinary ground member
    rw [refused] at selected
    contradiction
  · intro empty
    cases selected : PeTTa.SpaceSemantics.matchValue [] pattern value with
    | none => rfl
    | some after =>
        obtain ⟨result,depth,member,_,_⟩ := petta_match_he_query ordinary ground selected
        simp [empty depth] at member

namespace Controls

/-- Reusing a rule's raw variable can conflict with a satisfiable caller.
The structural match alone therefore cannot replace legal fresh instantiation. -/
theorem raw_match_does_not_override_caller :
    MORK.MatchAtomRel [] (.var "x") (.symbol "A") [("x",.symbol "A")] ∧
      ¬∃ output, HE.Spec.Eval.Steps.UnifyCandidateRel (.symbol "A") (.var "x")
        (⟨[("x",.symbol "B")],[]⟩ : HE.Bindings) output := by
  refine ⟨.var_fresh rfl,?_⟩
  rintro ⟨output,candidate⟩
  have theory := candidate.solutions
  obtain ⟨_matched,_matching,merged⟩ := candidate
  obtain ⟨valuation,satisfied⟩ := merged.2
  obtain ⟨equation,caller⟩ := (theory valuation).mp satisfied
  have assigned := caller.1 "x" (.symbol "B") (by simp)
  simp only [HE.Spec.Type.RuntimeRefinement.applyTypeValuation] at equation assigned
  have impossible := equation.trans assigned
  simp at impossible

/-- Assigning an open public query variable can change its observer. The
closed-query condition in private-extension preservation is substantive. -/
theorem open_assignment_changes_caller_observer :
    ¬HE.Spec.Bindings.ScopeObservation.BindingTheoryEquivAt ["q"] HE.Bindings.empty
      (⟨[("q",.symbol "A")],[]⟩ : HE.Bindings) := by
  intro equivalent
  obtain ⟨reached,satisfied,agrees⟩ := equivalent.leftToRight (fun _ => .symbol "B")
    (by constructor <;> simp [HE.Bindings.empty])
  have assigned := satisfied.1 "q" (.symbol "A") (by simp)
  have same := agrees "q" List.mem_cons_self
  have impossible := same.trans assigned
  simp [HE.Spec.Type.RuntimeRefinement.applyTypeValuation] at impossible

/-- Repeated occurrences receive one common value in the source model. -/
theorem nonlinear_model_exists :
    ∃ valuation, HE.Spec.Match.SolutionTheory.HEAtomEquationSatisfied valuation
      (.expression [.symbol "Pair", .symbol "A", .symbol "A"])
      (.expression [.symbol "Pair", .var "x", .var "x"]) := by
  refine ⟨fun _ => .sym "A", ?_⟩
  simp [HE.Spec.Match.SolutionTheory.HEAtomEquationSatisfied, HE.Spec.Match.SolutionTheory.encodeModelAtom,
    HE.Spec.Match.SolutionTheory.encodeModelAtoms, HE.Spec.Match.SolutionTheory.applyClassSolution]

/-- A single variable cannot simultaneously denote the two distinct symbols.
This rejection is proved directly in the equation theory. -/
theorem nonlinear_incompatible_has_no_model :
    ¬∃ valuation, HE.Spec.Match.SolutionTheory.HEAtomEquationSatisfied valuation
      (.expression [.symbol "Pair", .symbol "A", .symbol "B"])
      (.expression [.symbol "Pair", .var "x", .var "x"]) := by
  rintro ⟨valuation, equation⟩
  simp only [HE.Spec.Match.SolutionTheory.HEAtomEquationSatisfied, HE.Spec.Match.SolutionTheory.encodeModelAtom,
    HE.Spec.Match.SolutionTheory.encodeModelAtoms, HE.Spec.Match.SolutionTheory.applyClassSolution,
    List.map_cons, List.map_nil, Metta.Atom.expr.injEq, List.cons.injEq,
    and_true, true_and] at equation
  have different : ("A" : String) ≠ "B" := by decide +kernel
  exact different (Metta.Atom.sym.inj (equation.1.trans equation.2.symm))

/-- Freshening preserves a repeated template variable through any actual
certified table containing its source assignment. Other caller constraints
and the table's residual representative choices are unrestricted. -/
theorem fresh_template_repeats_one_value
    (bindings : HE.Bindings) (table : HE.Spec.Type.Presentation.TypeSubst)
    (certified : HE.Spec.Type.Presentation.BindingTheory.ReadoutCertificate bindings table)
    (assigned : ("private",Atom.symbol "A") ∈ bindings.assignments) :
    table.apply (.expression [.symbol "Box",.var "private",.var "private"]) =
      .expression [.symbol "Box",.symbol "A",.symbol "A"] := by
  let names := Equiv.swap "x" "private"
  let template : Atom := .expression [.symbol "Box",.var "x",.var "x"]
  have variant : HE.Spec.Eval.Steps.AlphaVariantRel [] (.symbol "A") HE.Bindings.empty
      (.var "x") template
      (HE.Spec.Type.RuntimeRefinement.renameTypeVars names (.var "x"))
      (HE.Spec.Type.RuntimeRefinement.renameTypeVars names template) := by
    refine ⟨names,names.injective,HE.EquationFreshening.rename_alpha _ _,
      HE.EquationFreshening.rename_alpha _ _,?_⟩
    intro name _occurs visible
    simp [HE.Spec.Eval.Steps.QueryVisibleName,HE.Bindings.empty] at visible
    cases visible
  have covered : ∀ name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVars template,
      name ∈ HE.Spec.Type.Presentation.TypeSubst.typeVars (.var "x") := by
    intro name member
    simpa [template,HE.Spec.Type.Presentation.TypeSubst.typeVars,
      HE.Spec.Type.Presentation.TypeSubst.typeVarsList] using member
  have fixed : ∀ valuation, HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation bindings →
      HE.Spec.Type.RuntimeRefinement.applyTypeValuation valuation
        (HE.Spec.Type.RuntimeRefinement.renameTypeVars names (.var "x")) = .symbol "A" := by
    intro valuation model
    simpa [names,HE.Spec.Type.RuntimeRefinement.renameTypeVars,HE.Spec.Type.RuntimeRefinement.applyTypeValuation] using
      model.1 "private" (.symbol "A") assigned
  have read := source_template_readout [("x",.symbol "A")] variant
    (by simp [MORK.applySubst,MORK.Subst.lookup]) covered certified fixed
  simpa [template,names,HE.Spec.Type.RuntimeRefinement.renameTypeVars,MORK.applySubst,
    MORK.applySubst.applySubstList,MORK.Subst.lookup] using read

/-- Pattern agreement does not determine an escaping RHS variable. This is
the negative control for the covered-template premise, independent of a run. -/
theorem uncovered_template_can_vary :
    ∃ left right : String → Atom,
      HE.Spec.Type.RuntimeRefinement.applyTypeValuation left (.var "x") =
        HE.Spec.Type.RuntimeRefinement.applyTypeValuation right (.var "x") ∧
      HE.Spec.Type.RuntimeRefinement.applyTypeValuation left (.var "y") ≠
        HE.Spec.Type.RuntimeRefinement.applyTypeValuation right (.var "y") := by
  refine ⟨fun _ => .symbol "A",fun name => if name = "y" then .symbol "B" else .symbol "A",?_,?_⟩
  · simp [HE.Spec.Type.RuntimeRefinement.applyTypeValuation]
  · simp [HE.Spec.Type.RuntimeRefinement.applyTypeValuation]

private def pattern : Atom := .expression [.symbol "Pair", .var "x", .var "x"]
private def value : Atom := .expression [.symbol "Pair", .symbol "A", .symbol "A"]
private def selected : MORK.Subst := [("x", .symbol "A")]

theorem nonlinear_source_selection :
    PeTTa.SpaceSemantics.matchValue [] pattern value = some selected := by
  decide +kernel

theorem nonlinear_mismatch_rejected :
    PeTTa.SpaceSemantics.matchValue [] pattern
      (.expression [.symbol "Pair", .symbol "A", .symbol "B"]) = none := by
  decide +kernel

private theorem value_ground : HE.GroundAtom value := by
  apply HE.GroundAtom.expression
  intro child member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> exact .symbol _

theorem nonlinear_match_is_exactly_one :
    ∃ result depth,
      (∀ extra, HE.matchAtoms value pattern (depth + extra) = [result]) ∧
      result.lookup "x" = some (.symbol "A") := by
  have ordinary : "cons" ∉ PeTTa.SpaceSemantics.patternHeads pattern := by decide +kernel
  obtain ⟨result, depth, exactMatches, _, lookups, _⟩ :=
    petta_match_he_pending_exact ordinary value_ground nonlinear_source_selection
  exact ⟨result, depth, exactMatches, by simpa [selected, MORK.Subst.lookup] using lookups "x"⟩

theorem one_clause_cannot_duplicate_a_match (result : HE.Bindings) (depth : Nat) :
    HE.matchAtoms value pattern depth ≠ [result, result] := by
  intro duplicated
  have bound := ground_match_length_le_one value pattern depth value_ground
  rw [duplicated] at bound
  contradiction

/-- The earned HE occurrence has a nonempty binding and materializes repeated
uses together, while an older unbound name stays unbound. -/
theorem nonempty_binding_materializes_saved_tuple :
    ∃ result depth,
      result ∈ HE.matchAtoms value pattern depth ∧
      result.lookup "x" = some (.symbol "A") ∧
      ([.expression [.symbol "Pair", .var "x", .var "x"], .var "x",
        .expression [.symbol "Hold", .var "saved"]] : List Atom).map
        (fun operand => result.applyFull operand (sizeOf operand + 2)) =
          [.expression [.symbol "Pair", .symbol "A", .symbol "A"], .symbol "A",
            .expression [.symbol "Hold", .var "saved"]] := by
  have ordinary : "cons" ∉ PeTTa.SpaceSemantics.patternHeads pattern := by decide +kernel
  obtain ⟨result, depth, member, _, lookups, pending⟩ :=
    petta_match_he_pending ordinary value_ground nonlinear_source_selection
  refine ⟨result, depth, member, ?_, ?_⟩
  · simpa [selected, MORK.Subst.lookup] using lookups "x"
  · simpa [selected, MORK.applySubst, MORK.applySubst.applySubstList, MORK.Subst.lookup]
      using pending [.expression [.symbol "Pair", .var "x", .var "x"], .var "x",
        .expression [.symbol "Hold", .var "saved"]]

/-- The nonlinear mismatch is an independent rejection at every matching
depth, rather than a result of choosing too small an execution allowance. -/
theorem nonlinear_mismatch_is_complete :
    ∀ depth, HE.matchAtoms (.expression [.symbol "Pair", .symbol "A", .symbol "B"])
      pattern depth = [] := by
  apply (petta_mismatch_iff_he_empty pattern _ (by decide +kernel) ?_).mp
    nonlinear_mismatch_rejected
  apply HE.GroundAtom.expression
  intro child member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> exact .symbol _

/-- A truncated matcher is not rejection evidence even when its list is empty. -/
theorem empty_prefix_is_not_a_complete_mismatch :
    HE.matchAtoms value pattern 0 = [] ∧
      PeTTa.SpaceSemantics.matchValue [] pattern value = some selected :=
  ⟨rfl, nonlinear_source_selection⟩

/-- An arbitrary actual HE occurrence earns the same nonlinear source binding
and the whole saved tuple, including names outside the selected clause. -/
theorem actual_he_occurrence_reflects_pending (result : HE.Bindings) (depth : Nat)
    (present : result ∈ HE.matchAtoms value pattern depth) :
    result.lookup "x" = some (.symbol "A") ∧
      ([.expression [.var "x", .var "x"], .var "saved"] : List Atom).map
        (fun operand => result.applyFull operand (sizeOf operand + 2)) =
          [.expression [.symbol "A", .symbol "A"], .var "saved"] := by
  obtain ⟨after, matched, lookups, reads⟩ :=
    he_match_petta_pending (by decide +kernel) value_ground present
  have same : after = selected := Option.some.inj (matched.symm.trans nonlinear_source_selection)
  subst after
  constructor
  · simpa [selected, MORK.Subst.lookup] using lookups "x"
  · simpa [selected, MORK.applySubst, MORK.applySubst.applySubstList, MORK.Subst.lookup]
      using reads [.expression [.var "x", .var "x"], .var "saved"]

theorem list_view_is_not_structural :
    PeTTa.SpaceSemantics.matchValue []
      (.expression [.symbol "cons", .var "first", .var "rest"])
      (.expression [.symbol "A", .symbol "B"]) =
        some [("rest", .expression [.symbol "B"]), ("first", .symbol "A")] ∧
    MORK.matchAtom []
      (.expression [.symbol "cons", .var "first", .var "rest"])
      (.expression [.symbol "A", .symbol "B"]) = none := by
  decide +kernel

theorem open_query_is_outside_ground_fragment : ¬ HE.GroundAtom (.var "query") :=
  HE.GroundAtom.not_var

end Controls

#print axioms source_match_he_seed
#print axioms he_candidate_petta_reached_solutions
#print axioms petta_reached_accepted_iff_he_candidate
#print axioms petta_reached_refinement
#print axioms petta_reached_refused_iff_no_he_candidate
#print axioms reached_pending_observations
#print axioms petta_reached_refinement_pending
#print axioms source_equate_he_pending
#print axioms private_destination_pending_observations
#print axioms petta_joint_refinement
#print axioms petta_joint_accepted_iff_he_candidate
#print axioms petta_joint_refused_iff_no_he_candidate
#print axioms source_equate_joint_pending
#print axioms joint_pending_prepend_fresh
#print axioms joint_query_fresh_clause_observations
#print axioms petta_fresh_clause_joint_refinement
#print axioms petta_fresh_clause_joint_refused_iff
#print axioms petta_selected_joint_row
#print axioms protected_petta_selected_joint_row
#print axioms ClausePendingAgreement.pending_observations
#print axioms ClausePendingAgreement.pending_occurrences
#print axioms protected_petta_joint_decision_he_row
#print axioms protected_petta_joint_choices_he_frontier
#print axioms source_private_destination_pending
#print axioms ClauseAgreement.pending_observations
#print axioms ClauseAgreement.continue_refinement
#print axioms ClauseAgreement.pending_occurrences
#print axioms protected_petta_choices_he_pending
#print axioms FrontierControls.duplicate_pending_observations
#print axioms ContinuationControls.sibling_uses_reached_head_theory
#print axioms ContinuationControls.nonfresh_destination_changes_observations
#print axioms solution_petta_match
#print axioms petta_match_iff_solution
#print axioms spec_match_petta
#print axioms spec_match_he_pending_exact
#print axioms query_occurrence_he_pending_exact
#print axioms no_query_occurrence_of_petta_mismatch
#print axioms petta_mismatch_iff_no_solution
#print axioms Controls.nonlinear_model_exists
#print axioms Controls.nonlinear_incompatible_has_no_model
#print axioms source_match_he_query
#print axioms matchValue_eq_structural
#print axioms petta_match_he_query
#print axioms ground_readout
#print axioms petta_match_he_pending
#print axioms ground_match_length_le_one
#print axioms petta_match_he_pending_exact
#print axioms he_match_petta
#print axioms he_match_petta_pending
#print axioms petta_mismatch_iff_he_empty
#print axioms Controls.nonlinear_mismatch_is_complete
#print axioms Controls.empty_prefix_is_not_a_complete_mismatch
#print axioms Controls.actual_he_occurrence_reflects_pending
#print axioms Controls.nonlinear_source_selection
#print axioms Controls.nonlinear_mismatch_rejected
#print axioms Controls.nonlinear_match_is_exactly_one
#print axioms Controls.one_clause_cannot_duplicate_a_match
#print axioms Controls.nonempty_binding_materializes_saved_tuple
#print axioms Controls.list_view_is_not_structural
#print axioms Controls.open_query_is_outside_ground_fragment
#print axioms petta_refused_he_row
#print axioms different_head_refused
#print axioms petta_decision_he_row
#print axioms petta_frontier_he_frontier
#print axioms petta_choices_he_frontier
#print axioms protected_petta_choices_he_frontier
#print axioms petta_choices_he_occurrences
#print axioms ContinuationControls.reached_head_then_frontier
#print axioms ContinuationControls.private_destination_duplicate_frontier

end Mettapedia.Languages.MeTTa.Translation.ConstructorMatch
