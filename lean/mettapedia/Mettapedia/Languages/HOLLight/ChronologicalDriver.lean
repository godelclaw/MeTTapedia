import Mettapedia.Languages.HOLLight.InferenceCompiler

/-!
# Chronological controller for the concrete HOL emitter

The resumable source controller invokes the existing AXIOM/SPEC/MP emitter and
chronological HOL replay. Claims and saved roots carry replay-earned evidence;
the occurrence journal retains original child positions and repeated uses.

Its counted unit is a controller task. Original binary-machine realization,
source-admission cost and a joined physical resource bound remain separate
operational obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.ChronologicalDriver

open Mettapedia.Logic
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.FirstOrderRules
open Mettapedia.GSLT.LanguageDef.CertificateGSLT (RawOpenProof)
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.MM0.Translation.CalculusSimulation
open Mettapedia.Logic.HOL.Embedding.InferenceRules
open Mettapedia.Languages.HOLLight.FirstOrder.InferenceTranslation
open Mettapedia.Languages.HOLLight.InferenceHosting
open Mettapedia.Languages.HOLLight.InferenceCompiler

variable (definition : ValidatedCalculusLanguageDef)

/-- All stored primitive receipts have actually passed chronological replay. -/
abbrev Prefix := {state : ProofExecution.State //
  GraphExpansion.BuildChecked (policy (inferenceRules definition.1)) [] state}

def seed : Prefix definition :=
  ⟨initialState definition.1, initialState_checked definition.1⟩

/-- A root in a controller stack or saved environment carries its exact theorem,
including axiom tags. Proof fields erase; lookup and claim checks do not. -/
structure Claim (checkedPrefix : Prefix definition) where
  goal : Pattern
  root : Nat
  out : Theorem
  found : checkedPrefix.val.cache[root]? = some out
  represents : hasClaim goal out = true

/-- Claim construction earns the dependent fields from actual lookup/checking. -/
def claimAt? (checkedPrefix : Prefix definition) (goal : Pattern) (root : Nat) :
    Option (Claim definition checkedPrefix) :=
  match found : checkedPrefix.val.cache[root]? with
  | none => none
  | some out =>
      if represents : hasClaim goal out = true then
        some ⟨goal, root, out, found, represents⟩
      else none

/-- No previously checked root changes when a block is appended. -/
def Claim.keep {before after : Prefix definition}
    (kept : KeepsOld before.val after.val) (claim : Claim definition before) :
    Claim definition after :=
  ⟨claim.goal, claim.root, claim.out, kept _ _ claim.found, claim.represents⟩

@[simp] theorem Claim.keep_root {before after : Prefix definition}
    (kept : KeepsOld before.val after.val) (claim : Claim definition before) :
    (Claim.keep definition kept claim).root = claim.root := rfl

@[simp] theorem Claim.keep_goal {before after : Prefix definition}
    (kept : KeepsOld before.val after.val) (claim : Claim definition before) :
    (Claim.keep definition kept claim).goal = claim.goal := rfl

structure Extension (before : Prefix definition) where
  after : Prefix definition
  root : Nat
  kept : KeepsOld before.val after.val

/-- The smart extension constructor checks and relocates a concrete primitive
block. In particular it does not install the emitter as a new kernel rule. -/
def extend? (before : Prefix definition) (roots : List Nat)
    (block : ProofSystem.Certificate) : Option (Extension definition before) :=
  match emitted : GraphExpansion.emitBlock (policy (inferenceRules definition.1))
      roots block before.val with
  | none => none
  | some (after, root) =>
      let earned := GraphExpansion.emitBlock_preserves_checked before.property emitted
      some ⟨⟨after, earned.1⟩, root, earned.2.2⟩

structure Site where
  origin : ProofExecution.Origin
  path : List Nat
  deriving DecidableEq

inductive Task where
  | visit (goal : Pattern) (proof : RawOpenProof) (site : Site)
  | close (goal : Pattern) (ruleInstance : RuleInstance)
      (premises : List Pattern) (site : Site)
  | save (goal : Pattern) (index : Nat)
  | finish (goal : Pattern)

/-- Work and value stacks have different roles. Values are in return-stack
order; a closing rule reverses precisely its own checkedPrefix to recover premise
order. Saved entries and the occurrence journal remain chronological lists. -/
structure State where
  checkedPrefix : Prefix definition
  todo : List Task
  values : List (Claim definition checkedPrefix)
  saved : List (Claim definition checkedPrefix)
  occurrences : List (Site × Claim definition checkedPrefix)

inductive Error where
  | sourceRefused | noTask | missingSaved | wrongClaim | malformedChildren
  | badRule | insufficientValues | wrongPremiseOrder | emitterRefused
  | replayRefused | missingOutput | badSave | badFinish
  deriving DecidableEq

inductive Status where
  | running (state : State definition)
  | done (state : State definition) (claim : Claim definition state.checkedPrefix)
  | refused (error : Error) (state : State definition)

/-- Sites are original child positions, not hashes of equal subproof values. -/
def children (site : Site) : Nat → List (Pattern × RawOpenProof) → List Task
  | _, [] => []
  | index, (goal, proof) :: rest =>
      .visit goal proof ⟨site.origin, site.path ++ [index]⟩ ::
        children site (index + 1) rest

theorem children_length (site : Site) (index : Nat)
    (jobs : List (Pattern × RawOpenProof)) :
    (children site index jobs).length = jobs.length := by
  induction jobs generalizing index with
  | nil => rfl
  | cons head tail ih => cases head; simp only [children, List.length_cons, ih]

/-- One source occurrence is recorded even when its root was used before. -/
def remember (state : State definition) (site : Site)
    (claim : Claim definition state.checkedPrefix) (rest : List Task) : State definition :=
  { state with
    todo := rest
    values := claim :: state.values
    occurrences := state.occurrences ++ [(site, claim)] }

theorem remember_occurrences (state : State definition) (site : Site)
    (claim : Claim definition state.checkedPrefix) (rest : List Task) :
    (remember definition state site claim rest).occurrences =
      state.occurrences ++ [(site, claim)] := rfl

theorem remember_count (state : State definition) (site : Site)
    (claim : Claim definition state.checkedPrefix) (rest : List Task) :
    (remember definition state site claim rest).occurrences.length =
      state.occurrences.length + 1 := by simp [remember]

/-- One controller step. The counted unit is a task, not a primitive HOL rule
or a machine transition; `close` may emit many primitive requests. -/
def step : Status definition → Status definition
  | .done state claim => .done state claim
  | .refused error state => .refused error state
  | .running state =>
    match state.todo with
    | [] => .refused .noTask state
    | .visit goal (.premise index) site :: rest =>
      match state.saved[index]? with
      | none => .refused .missingSaved state
      | some claim =>
        if claim.goal = goal then
          .running (remember definition state site claim rest)
        else .refused .wrongClaim state
    | .visit goal (.node ruleInstance proofs) site :: rest =>
      match instantiateRule? definition ruleInstance with
      | none => .refused .badRule state
      | some (premises, conclusion) =>
        if conclusion = goal then
          if premises.length = proofs.length then
            .running { state with
              todo := children site 0 (premises.zip proofs) ++
                .close goal ruleInstance premises site :: rest }
          else .refused .malformedChildren state
        else .refused .wrongClaim state
    | .close goal ruleInstance premises site :: rest =>
      if premises.length ≤ state.values.length then
        let selected := (state.values.take premises.length).reverse
        if selected.map (fun claim => claim.goal) = premises then
          match InferenceRuleExpansion.emitRule? definition ruleInstance
              (selected.map (fun claim => claim.out)) site.origin with
          | none => .refused .emitterRefused state
          | some block =>
            match extend? definition state.checkedPrefix
                (selected.map (fun claim => claim.root)) block with
            | none => .refused .replayRefused state
            | some extension =>
              match claimAt? definition extension.after goal extension.root with
              | none => .refused .missingOutput state
              | some claim =>
                let next : State definition :=
                  { checkedPrefix := extension.after
                    todo := rest
                    values := (state.values.drop premises.length).map
                      (Claim.keep definition extension.kept)
                    saved := state.saved.map (Claim.keep definition extension.kept)
                    occurrences := state.occurrences.map fun occurrence =>
                      (occurrence.1, Claim.keep definition extension.kept occurrence.2) }
                .running (remember definition next site claim rest)
        else .refused .wrongPremiseOrder state
      else .refused .insufficientValues state
    | .save goal index :: rest =>
      match state.values with
      | [claim] =>
        if claim.goal = goal ∧ state.saved.length = index then
          .running { state with
            todo := rest
            values := []
            saved := state.saved ++ [claim] }
        else .refused .badSave state
      | _ => .refused .badSave state
    | .finish goal :: rest =>
      match rest, state.values with
      | [], [claim] =>
        if claim.goal = goal then .done state claim
        else .refused .badFinish state
      | _, _ => .refused .badFinish state

/-- Future saved references are refused by the actual controller branch, not
by a supplied assertion that the source checker has already rejected them. -/
theorem future_saved_refused (state : State definition) (goal : Pattern)
    (index : Nat) (site : Site) (rest : List Task)
    (work : state.todo = .visit goal (.premise index) site :: rest)
    (future : state.saved.length ≤ index) :
    step definition (.running state) = .refused .missingSaved state := by
  have missing : state.saved[index]? = none := List.getElem?_eq_none future
  simp only [step, work, missing]

/-- Keeping claims transports their evidence but cannot sort or deduplicate
an ordered premise-root vector. -/
theorem kept_root_vector {before after : Prefix definition}
    (kept : KeepsOld before.val after.val) (claims : List (Claim definition before)) :
    ((claims.map (Claim.keep definition kept)).map (fun claim => claim.root)) =
      claims.map (fun claim => claim.root) := by
  simp only [List.map_map, Function.comp_def, Claim.keep_root]

/-- Two equal-valued saved uses remain two deliveries in the source journal.
This result is independent of primitive proof sharing. -/
theorem remember_twice_count (state : State definition) (first second : Site)
    (claim : Claim definition state.checkedPrefix) (rest : List Task) :
    (remember definition (remember definition state first claim rest)
      second claim rest).occurrences.length = state.occurrences.length + 2 := by
  simp [remember]

/-- Original lemma order; a lemma enters the saved environment only after its
complete traversal. A repeated, equal lemma still has its own index/site. -/
def lemmaTasks : Nat → List (Pattern × RawOpenProof) → List Task
  | _, [] => []
  | index, (goal, proof) :: rest =>
      .visit goal proof ⟨("lemma", index), []⟩ ::
      .save goal index :: lemmaTasks (index + 1) rest

def start (goal : Pattern) (source : LemmaCertificate) : Status definition :=
  let initial : State definition :=
    { checkedPrefix := seed definition
      todo := lemmaTasks 0 source.1 ++
        [.visit goal source.2 ⟨("root", 0), []⟩, .finish goal]
      values := [], saved := [], occurrences := [] }
  if sharedSourceCheck definition goal source then .running initial
  else .refused .sourceRefused initial

def run : Nat → Status definition → Status definition
  | 0, state => state
  | budget + 1, state => run budget (step definition state)

/-- Exact resumption: no saved checkedPrefix is replayed at a budget boundary. -/
theorem run_add (first second : Nat) (state : Status definition) :
    run definition (first + second) state =
      run definition second (run definition first state) := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add, run]
  | succ first ih => simpa only [Nat.succ_add, run] using ih (step definition state)

theorem run_done (budget : Nat) (state : State definition)
    (claim : Claim definition state.checkedPrefix) :
    run definition budget (.done state claim) = .done state claim := by
  induction budget with
  | zero => rfl
  | succ budget ih => simpa only [run, step] using ih

theorem run_refused (budget : Nat) (error : Error) (state : State definition) :
    run definition budget (.refused error state) = .refused error state := by
  induction budget with
  | zero => rfl
  | succ budget ih => simpa only [run, step] using ih

/-- The public boundary rechecks the requested claim and returns the ORIGINAL
HOL graph format. A running/refused checkedPrefix is not published as a completed
certificate, even if it happens to contain a proof of the requested claim. -/
def result (goal : Pattern) : Status definition → Option ProofSystem.Certificate
  | .done state claim =>
      if hasClaim goal claim.out then
        some (GraphExpansion.finish state.checkedPrefix.val claim.root)
      else none
  | _ => none

/-- Any published result is accepted by independent original HOL replay. -/
theorem result_checked (goal : Pattern) (status : Status definition)
    {certificate : ProofSystem.Certificate}
    (published : result definition goal status = some certificate) :
    ∃ out, (ProofSystem.checker (policy (inferenceRules definition.1))).check
      out certificate = true ∧ out.sequent.hyp = ∅ ∧
      out.sequent.concl = compileClaim goal := by
  cases status with
  | running state => simp [result] at published
  | refused error state => simp [result] at published
  | done state claim =>
    cases valid : hasClaim goal claim.out with
    | false => simp [result, valid] at published
    | true =>
      have same : GraphExpansion.finish state.checkedPrefix.val claim.root = certificate := by
        simpa only [result, valid, Bool.true_eq, ↓reduceIte, Option.some.injEq] using published
      subst certificate
      refine ⟨claim.out, ?_, ?_⟩
      · exact (ProofSystem.checker_check_iff _ _ _).mpr
          ⟨state.checkedPrefix.val.cache, state.checkedPrefix.property, claim.found⟩
      · exact of_decide_eq_true valid

/-- Reflection is inherited only for the proven first-order host region.
This theorem must not be reused as a binding-aware hosting theorem. -/
theorem result_reflects (firstOrder : FirstOrderCalculus definition.1)
    (goal : Pattern) (valid : argumentValidAt 0 goal = true)
    (status : Status definition) {certificate : ProofSystem.Certificate}
    (published : result definition goal status = some certificate) :
    ∃ proof, checkRaw definition goal proof = true := by
  obtain ⟨out, checked, hypotheses, conclusion⟩ :=
    result_checked definition goal status published
  exact (graph_checked_iff definition firstOrder valid).mpr
    ⟨out, certificate, checked, hypotheses, conclusion⟩

/-- Malformed source certificates, including unused bad lemmas and future
references, are rejected by the actual source checker before execution. -/
theorem refused_source_no_result (goal : Pattern) (source : LemmaCertificate)
    (rejected : sharedSourceCheck definition goal source = false) (budget : Nat) :
    result definition goal (run definition budget (start definition goal source)) = none := by
  simp only [start, rejected, Bool.false_eq_true, ↓reduceIte]
  rw [run_refused]
  rfl

end Mettapedia.Languages.HOLLight.ChronologicalDriver
