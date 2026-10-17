import Mettapedia.Languages.Megalodon.ProofJudgment
import Mettapedia.Machines.Cursor.ProofChecking

/-!
# Native Megalodon inferences over borrowed proof rows

Each row supplies one local constructor and cites already checked judgments.
The cache retains the full type, term and hypothesis contexts. It contains no
expanded proof trees. Conversion and type synthesis are the existing Mathdata
operations; their work is not claimed to cost one cursor movement.

The equivalence below is uniform in the actual selected environment, so the
cursor does not choose Egal, Mizar, HF, HOAS, or any other foundation. Formation
and authenticated admission remain separate from raw proof inference.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.BorrowedProofCursor

open MathdataKernel ProofJudgment
open Mettapedia.Logic Mettapedia.Logic.DerivationGraph
open Mettapedia.Logic.DerivationGraph.BorrowedCursor

structure Judgment where
  context : Context
  proposition : Tm
  deriving DecidableEq, Repr

inductive Rules (environment : Environment) (fuel : Nat) : List Judgment → Judgment → Prop where
  | hyp {context : Context} {index : Nat} {proposition : Tm} :
      context.hypotheses[index]? = some proposition → Rules environment fuel [] ⟨context, proposition⟩
  | known {context : Context} {name : Name} {source proposition : Tm} :
      environment.lookupKnown? name = some source → normalize environment fuel source = some proposition →
      Rules environment fuel [] ⟨context, proposition⟩
  | termApp {context : Context} {argument body normalized proposition : Tm} {domain : Tp} :
      inferTerm environment context.typeDepth context.terms argument = some domain →
      deltaNormalize environment fuel argument = some normalized →
      normalize environment fuel (Tm.instantiate normalized body) = some proposition →
      Rules environment fuel [⟨context, .all domain body⟩] ⟨context, proposition⟩
  | proofApp {context : Context} {domain codomain : Tm} :
      Rules environment fuel [⟨context, .imp domain codomain⟩, ⟨context, domain⟩] ⟨context, codomain⟩
  | termLam {context : Context} {type : Tp} {body : Tm} :
      type.plainWellFormed context.typeDepth = true →
      Rules environment fuel [⟨context.termBinder type, body⟩] ⟨context, .all type body⟩
  | proofLam {context : Context} {source normalized body : Tm} :
      inferTerm environment context.typeDepth context.terms source = some .prop →
      normalize environment fuel source = some normalized →
      Rules environment fuel [⟨context.proofBinder normalized, body⟩] ⟨context, .imp normalized body⟩
  | typeApp {context : Context} {type : Tp} {body : Tm} :
      Rules environment fuel [⟨context, .typeAll body⟩] ⟨context, Tm.typeInstantiate type body⟩
  | typeLam {context : Context} {body : Tm} :
      context.terms = [] → context.hypotheses = [] →
      Rules environment fuel [⟨context.typeBinder, body⟩] ⟨context, .typeAll body⟩

inductive Witness where
  | hyp (index : Nat)
  | known (name : Name)
  | termApp (argument : Tm) (domain : Tp) (body : Tm)
  | proofApp (domain : Tm)
  | termLam
  | proofLam (source : Tm)
  | typeApp (type : Tp) (body : Tm)
  | typeLam
  deriving DecidableEq, Repr

/-- Local requirements are computed without recursively traversing a proof.
Even equal propositions from different contexts are different premises. -/
def requirements (environment : Environment) (fuel : Nat) (witness : Witness)
    (conclusion : Judgment) : Option (List Judgment) :=
  let context := conclusion.context
  let proposition := conclusion.proposition
  match witness with
  | .hyp index => if context.hypotheses[index]? = some proposition then some [] else none
  | .known name => do
      let source ← environment.lookupKnown? name
      let normalized ← normalize environment fuel source
      if normalized = proposition then some [] else none
  | .termApp argument domain body => do
      if inferTerm environment context.typeDepth context.terms argument ≠ some domain then none else
      let normalized ← deltaNormalize environment fuel argument
      let result ← normalize environment fuel (Tm.instantiate normalized body)
      if result = proposition then some [⟨context, .all domain body⟩] else none
  | .proofApp domain => some [⟨context, .imp domain proposition⟩, ⟨context, domain⟩]
  | .termLam => match proposition with
      | .all type body => if type.plainWellFormed context.typeDepth then
          some [⟨context.termBinder type, body⟩] else none
      | _ => none
  | .proofLam source => match proposition with
      | .imp normalized body =>
          if inferTerm environment context.typeDepth context.terms source = some .prop ∧
              normalize environment fuel source = some normalized then
            some [⟨context.proofBinder normalized, body⟩] else none
      | _ => none
  | .typeApp type body => if Tm.typeInstantiate type body = proposition then
      some [⟨context, .typeAll body⟩] else none
  | .typeLam => match proposition with
      | .typeAll body => if context.terms = [] ∧ context.hypotheses = [] then
          some [⟨context.typeBinder, body⟩] else none
      | _ => none

theorem requirements_sound {environment : Environment} {fuel : Nat} {witness : Witness}
    {conclusion : Judgment} {premises : List Judgment}
    (accepted : requirements environment fuel witness conclusion = some premises) :
    Rules environment fuel premises conclusion := by
  rcases conclusion with ⟨context, proposition⟩
  cases witness with
  | hyp index =>
      simp only [requirements] at accepted
      split at accepted
      · rename_i found; cases Option.some.inj accepted; exact .hyp found
      · contradiction
  | known name =>
      cases found : environment.lookupKnown? name with
      | none => simp [requirements, found] at accepted
      | some source =>
          cases normalized : normalize environment fuel source with
          | none => simp [requirements, found, normalized] at accepted
          | some result =>
              by_cases same : result = proposition
              · subst result
                have empty : premises = [] := by simpa [requirements, found, normalized] using accepted.symm
                subst premises
                exact .known found normalized
              · simp [requirements, found, normalized, same] at accepted
  | termApp argument domain body =>
      by_cases typed : inferTerm environment context.typeDepth context.terms argument = some domain
      · cases unfolded : deltaNormalize environment fuel argument with
        | none => simp [requirements, typed, unfolded] at accepted
        | some normalized =>
            cases result : normalize environment fuel (Tm.instantiate normalized body) with
            | none => simp [requirements, typed, unfolded, result] at accepted
            | some actual =>
                by_cases same : actual = proposition
                · subst actual
                  have parents : premises = [⟨context, .all domain body⟩] := by
                    simpa [requirements, typed, unfolded, result] using accepted.symm
                  subst premises
                  exact .termApp typed unfolded result
                · simp [requirements, typed, unfolded, result, same] at accepted
      · simp [requirements, typed] at accepted
  | proofApp domain =>
      cases Option.some.inj accepted
      exact .proofApp
  | termLam =>
      cases proposition <;> simp only [requirements] at accepted
      all_goals try contradiction
      rename_i type body
      split at accepted
      · rename_i formed; cases Option.some.inj accepted; exact .termLam formed
      · contradiction
  | proofLam source =>
      cases proposition <;> simp only [requirements] at accepted
      all_goals try contradiction
      rename_i domain body
      split at accepted
      · rename_i checked; cases Option.some.inj accepted; exact .proofLam checked.1 checked.2
      · contradiction
  | typeApp type body =>
      simp only [requirements] at accepted
      split at accepted
      · rename_i same
        cases Option.some.inj accepted
        subst proposition
        exact .typeApp
      · contradiction
  | typeLam =>
      cases proposition <;> simp only [requirements] at accepted
      all_goals try contradiction
      rename_i body
      split at accepted
      · rename_i empty; cases Option.some.inj accepted; exact .typeLam empty.1 empty.2
      · contradiction

theorem requirements_complete {environment : Environment} {fuel : Nat}
    {premises : List Judgment} {conclusion : Judgment} (rule : Rules environment fuel premises conclusion) :
    ∃ witness, requirements environment fuel witness conclusion = some premises := by
  cases rule with
  | @hyp context index proposition found => exact ⟨.hyp index, by simp [requirements, found]⟩
  | @known context name source proposition found normalized =>
      exact ⟨.known name, by simp [requirements, found, normalized]⟩
  | @termApp context argument body normalized proposition domain typed unfolded result =>
      exact ⟨.termApp argument domain body, by simp [requirements, typed, unfolded, result]⟩
  | @proofApp context domain codomain => exact ⟨.proofApp domain, rfl⟩
  | termLam formed => exact ⟨.termLam, by simp [requirements, formed]⟩
  | @proofLam context source normalized body typed result =>
      exact ⟨.proofLam source, by simp [requirements, typed, result]⟩
  | @typeApp context type body => exact ⟨.typeApp type body, by simp [requirements]⟩
  | typeLam terms hypotheses => exact ⟨.typeLam, by simp [requirements, terms, hypotheses]⟩

def interface (environment : Environment) (fuel : Nat) : RuleWitness (Rules environment fuel) where
  W := Witness
  isInstance witness premises conclusion := decide (requirements environment fuel witness conclusion = some premises)
  sound _ _ _ accepted := requirements_sound (of_decide_eq_true accepted)
  complete _ _ rule := by
    obtain ⟨witness, checked⟩ := requirements_complete rule
    exact ⟨witness, by simp [checked]⟩

theorem derives_proof {environment : Environment} {fuel : Nat} {judgment : Judgment}
    (derived : Derives (Rules environment fuel) judgment) :
    ∃ proof, Proves environment fuel judgment.context proof judgment.proposition := by
  induction derived with
  | node premises conclusion rule _ ih =>
      cases rule with
      | @hyp context index proposition found => exact ⟨.hyp index, .hyp found⟩
      | @known context name source proposition found normalized => exact ⟨.known name, .known found normalized⟩
      | @termApp context argument body normalized proposition domain typed unfolded result =>
          obtain ⟨proof, proved⟩ := ih ⟨context, .all domain body⟩ (by simp)
          exact ⟨.termApp proof argument, .termApp proved typed unfolded result⟩
      | @proofApp context domain codomain =>
          obtain ⟨function, functionProof⟩ := ih ⟨context, .imp domain codomain⟩ (by simp)
          obtain ⟨argument, argumentProof⟩ := ih ⟨context, domain⟩ (by simp)
          exact ⟨.proofApp function argument, .proofApp functionProof argumentProof⟩
      | @termLam context type body formed =>
          obtain ⟨proof, proved⟩ := ih ⟨context.termBinder type, body⟩ (by simp)
          exact ⟨.termLam type proof, .termLam formed proved⟩
      | @proofLam context source normalized body typed result =>
          obtain ⟨proof, proved⟩ := ih ⟨context.proofBinder normalized, body⟩ (by simp)
          exact ⟨.proofLam source proof, .proofLam typed result proved⟩
      | @typeApp context type body =>
          obtain ⟨proof, proved⟩ := ih ⟨context, .typeAll body⟩ (by simp)
          exact ⟨.typeApp proof type, .typeApp proved⟩
      | @typeLam context body terms hypotheses =>
          obtain ⟨proof, proved⟩ := ih ⟨context.typeBinder, body⟩ (by simp)
          exact ⟨.typeLam proof, .typeLam terms hypotheses proved⟩

private theorem singleton {rule : List Judgment → Judgment → Prop} {judgment : Judgment}
    (derived : Derives rule judgment) : ∀ j ∈ [judgment], Derives rule j := by
  intro j member
  simpa only [List.mem_singleton.mp member] using derived

theorem proof_derives {environment : Environment} {fuel : Nat} {context : Context}
    {proof : Pf} {proposition : Tm} (proved : Proves environment fuel context proof proposition) :
    Derives (Rules environment fuel) ⟨context, proposition⟩ := by
  induction proved with
  | hyp found => exact .node [] _ (.hyp found) (by simp)
  | known found normalized => exact .node [] _ (.known found normalized) (by simp)
  | termApp _ typed unfolded result ih => exact .node _ _ (.termApp typed unfolded result) (singleton ih)
  | @proofApp context function argument domain codomain _ _ ihf iha =>
      refine .node _ _ (.proofApp (domain := domain)) ?_
      intro j member
      rcases List.mem_cons.mp member with rfl | member
      · exact ihf
      · exact singleton iha j member
  | termLam formed _ ih => exact .node _ _ (.termLam formed) (singleton ih)
  | proofLam typed result _ ih => exact .node _ _ (.proofLam typed result) (singleton ih)
  | typeApp _ ih => exact .node _ _ .typeApp (singleton ih)
  | typeLam terms hypotheses _ ih => exact .node _ _ (.typeLam terms hypotheses) (singleton ih)

theorem derives_iff_original (environment : Environment) (fuel : Nat) (judgment : Judgment) :
    Derives (Rules environment fuel) judgment ↔
      ∃ proof, inferProof environment fuel judgment.context.typeDepth judgment.context.terms
        judgment.context.hypotheses proof = some judgment.proposition := by
  constructor
  · intro derived
    obtain ⟨proof, proved⟩ := derives_proof derived
    exact ⟨proof, proved.infer⟩
  · rintro ⟨proof, accepted⟩
    exact proof_derives (proves_of_infer accepted)

abbrev Source := Store Judgment Witness Nat
abbrev SourceNode := StoredNode Judgment Witness Nat
abbrev Cursor (environment : Environment) (fuel : Nat) (source : Source) :=
  CheckedCursor (interface environment fuel) source

def begin (environment : Environment) (fuel : Nat) (source : Source) : Cursor environment fuel source :=
  CheckedCursor.begin (interface environment fuel) source

theorem original_iff_graph (environment : Environment) (fuel : Nat) (judgment : Judgment) :
    (∃ proof, inferProof environment fuel judgment.context.typeDepth judgment.context.terms
      judgment.context.hypotheses proof = some judgment.proposition) ↔
      ∃ (nodes : List (Node Judgment Witness Nat)) (cache : Array Judgment) (root : Nat),
        replay (interface environment fuel) nodes = some cache ∧ cache[root]? = some judgment := by
  rw [← derives_iff_original]
  exact derives_iff_checked_graph (interface environment fuel) (0 : Nat) judgment

theorem checked_root_original (environment : Environment) (fuel : Nat) {source : Source}
    (cursor : Cursor environment fuel source) (address : Nat) (judgment : Judgment)
    (found : (cursor.root address).map CheckedJudgment.judgment = some judgment) :
    ∃ proof, inferProof environment fuel judgment.context.typeDepth judgment.context.terms
      judgment.context.hypotheses proof = some judgment.proposition := by
  obtain ⟨checked, _present, same⟩ := Option.map_eq_some_iff.mp found
  exact same ▸ (derives_iff_original environment fuel checked.judgment).mp checked.valid

/-- A successful whole scheduled check retains a native proof for its root
and has checked every row, including rows not used by that root. -/
theorem worker_root_original (environment : Environment) (conversionFuel : Nat)
    (source : Source) (schedule : List Nat) (steps : Nat)
    (report : Mettapedia.Machines.Cursor.ProofChecking.Report (interface environment conversionFuel) source)
    (completed : Mettapedia.Machines.OutcomeRunner.run
      (Mettapedia.Machines.Cursor.ProofChecking.machine (interface environment conversionFuel) source) steps
      (Mettapedia.Machines.Cursor.ProofChecking.start (begin environment conversionFuel source) schedule) =
        .finished report)
    (accepted : report.accepted = true) (address : Nat) (judgment : Judgment)
    (found : (report.work.cursor.root address).map CheckedJudgment.judgment = some judgment) :
    (∃ proof, inferProof environment conversionFuel judgment.context.typeDepth judgment.context.terms
      judgment.context.hypotheses proof = some judgment.proposition) ∧
        report.work.pending = [] ∧ report.work.accepted = schedule.length := by
  have meaning := Mettapedia.Machines.Cursor.ProofChecking.check_only_report_meaning
    (interface environment conversionFuel) source (begin environment conversionFuel source)
    schedule steps report completed
  have observed : Mettapedia.Machines.Cursor.ProofChecking.verdict report.work = some true := by
    simpa [accepted] using report.valid
  obtain ⟨empty, count, _executed⟩ := Mettapedia.Machines.Cursor.ProofChecking.completed_run
    (interface environment conversionFuel) source (begin environment conversionFuel source)
    schedule report.work meaning observed
  exact ⟨checked_root_original environment conversionFuel report.work.cursor address judgment found,
    empty, count⟩

end Mettapedia.Languages.Megalodon.BorrowedProofCursor
