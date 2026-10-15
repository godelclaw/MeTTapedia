import Mettapedia.OSLF.MeTTaIL.GeneralPremiseStaticAdmission
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseQueryTermination

/-!
# Universal resolution of statically admitted finite queries

The invariant follows actual argument tails and matcher answers. Structural
output matches preserve earlier captures; each subsequent input is read at
its authored occurrence. A static signature and projection check therefore
resolve every provider alternative without an input-dependent search gate.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query

open Syntax RuleBinding ScopedRuleMatching

structure InputAdmission (environment : Environment) (request : Request) where
  available : List String
  signature : Signature
  signatureFound : signature? environment.provider request.relation request.arguments.length =
    some signature
  zero : checkZeroDependencies request.context.spec = true
  schemas : Static.checkQueryInputs request.context.rule request.context.spec
    request.context.premiseIndex request.context.quantifierDepth available
    0 request.arguments signature.modes = true
  values : RootValues request.context.bound.length request.initial
  names : BoundNames request.initial available

def ArgumentsReady {environment : Environment} {request : Request}
    (admission : InputAdmission environment request)
    (frame : ArgumentsFrame environment request) : Prop :=
  frame.schemas.length = frame.values.length ∧
    frame.schemas.length = frame.modes.length ∧
    Static.checkQueryInputs request.context.rule request.context.spec
      request.context.premiseIndex request.context.quantifierDepth admission.available
      frame.index frame.schemas frame.modes = true ∧
    RootValues request.context.bound.length frame.assignment ∧
    BoundNames frame.assignment admission.available

def MatcherReady {environment : Environment} {request : Request}
    (admission : InputAdmission environment request)
    (frame : MatcherFrame environment request) : Prop :=
  frame.schemas.length = frame.values.length ∧
    frame.schemas.length = frame.modes.length ∧
    Static.checkQueryInputs request.context.rule request.context.spec
      request.context.premiseIndex request.context.quantifierDepth admission.available
      (frame.argumentIndex + 1) frame.schemas frame.modes = true ∧
    frame.query.rule = request.context.rule ∧
    frame.query.spec = request.context.spec ∧
    frame.query.ambient = request.context.bound.length ∧
    RootValues request.context.bound.length frame.query.initial ∧
    BoundNames frame.query.initial admission.available

def TaskReady {environment : Environment} {request : Request}
    (admission : InputAdmission environment request) : Task environment request → Prop
  | .start | .rows _ => True
  | .arguments frame => ArgumentsReady admission frame
  | .matcher frame => MatcherReady admission frame

theorem input_read {environment : Environment} {request : Request}
    (admission : InputAdmission environment request)
    {frame : ArgumentsFrame environment request} (ready : ArgumentsReady admission frame)
    {schema : Pattern} {schemas values : List Pattern} {value : Pattern}
    {modes : List RelationArgMode}
    (schemaFound : frame.schemas = schema :: schemas)
    (_valueFound : frame.values = value :: values)
    (modeFound : frame.modes = .input :: modes) :
    ∃ actual, instantiateAt? request.context.rule request.context.spec
      request.context.bound.length (request.context.site frame.index) [] 0
      frame.assignment schema = some actual := by
  have checks := ready.2.2.1
  simp only [schemaFound, modeFound, Static.checkQueryInputs, Bool.and_eq_true] at checks
  have bound : BoundNames frame.assignment schema.freeFvarNames := by
    intro name member
    exact ready.2.2.2.2 name (namesAvailable_sound _ _ checks.1.2 name member)
  exact checkRootProjectionSchema_sound (operation := Substitution.instantiateBVar)
    checks.1.1 ready.2.2.2.1 bound

theorem expandArguments_ready {environment : Environment} {request : Request}
    (admission : InputAdmission environment request)
    (frame : ArgumentsFrame environment request) (ready : ArgumentsReady admission frame) :
    (expandArguments environment request frame).unresolved = [] ∧
      ∀ branch ∈ (expandArguments environment request frame).tasks, TaskReady admission branch := by
  unfold expandArguments
  split
  · split <;> exact ⟨rfl, by intro branch member; simp at member⟩
  · rename_i schema schemas value values mode modes schemaFound valueFound modeFound
    have lengths : schemas.length = values.length ∧ schemas.length = modes.length := by
      have left := ready.1
      have right := ready.2.1
      simp only [schemaFound, valueFound, modeFound, List.length_cons] at left right
      exact ⟨by omega, by omega⟩
    have checks := ready.2.2.1
    simp only [schemaFound, modeFound, Static.checkQueryInputs, Bool.and_eq_true] at checks
    cases mode with
    | input =>
      dsimp only
      split
      · rename_i failed
        obtain ⟨actual, read⟩ := input_read admission ready schemaFound valueFound modeFound
        rw [failed] at read
        contradiction
      · split
        · refine ⟨rfl, ?_⟩
          intro branch member
          simp only [List.mem_singleton] at member
          subst branch
          exact ⟨lengths.1, lengths.2, checks.2, ready.2.2.2.1, ready.2.2.2.2⟩
        · exact ⟨rfl, by intro branch member; simp at member⟩
    | output =>
      refine ⟨rfl, ?_⟩
      intro branch member
      simp only [List.mem_singleton] at member
      subst branch
      exact ⟨lengths.1, lengths.2, checks.2, rfl, rfl, rfl,
        ready.2.2.2.1, ready.2.2.2.2⟩
  · rename_i shape
    cases schemaFound : frame.schemas <;> cases valueFound : frame.values <;>
      cases modeFound : frame.modes <;> simp_all [ArgumentsReady]
    exact shape _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl

theorem expandMatcher_ready {environment : Environment} {request : Request}
    (admission : InputAdmission environment request)
    (frame : MatcherFrame environment request) (ready : MatcherReady admission frame) :
    (expandMatcher environment request frame).unresolved = [] ∧
      ∀ branch ∈ (expandMatcher environment request frame).tasks, TaskReady admission branch := by
  unfold expandMatcher
  split
  · rename_i answer found
    have valid := GeneralScopedMatchMachine.answers_sound frame.reachable (List.mem_of_getElem? found)
    have matching := valid.matching
    have values : RootValues request.context.bound.length answer.assignment := by
      rw [ready.2.2.2.1, ready.2.2.2.2.1, ready.2.2.2.2.2.1] at matching
      exact matching_rootValues admission.zero ready.2.2.2.2.2.2.1 matching
    have names := ready.2.2.2.2.2.2.2.extension valid.matching.extends
    refine ⟨rfl, ?_⟩
    intro branch member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same <;> subst branch
    · exact ⟨ready.1, ready.2.1, ready.2.2.1, values, names⟩
    · exact ready
  · split
    · exact ⟨rfl, by intro branch member; simp at member⟩
    · refine ⟨rfl, ?_⟩
      intro branch member
      simp only [List.mem_singleton] at member
      subst branch
      exact ready

theorem expand_ready {environment : Environment} {request : Request}
    (admission : InputAdmission environment request)
    (task : Task environment request) (ready : TaskReady admission task) :
    (expand environment request task).unresolved = [] ∧
      ∀ branch ∈ (expand environment request task).tasks, TaskReady admission branch := by
  cases task with
  | start =>
    rw [expand.eq_1]
    split
    · rename_i missing
      have present := admission.signatureFound
      rw [missing] at present
      contradiction
    · exact ⟨rfl, by intro branch member; simp only [List.mem_singleton] at member; subst branch; trivial⟩
  | rows frame =>
    rw [expand.eq_2]
    split
    · exact ⟨rfl, by intro branch member; simp at member⟩
    · rename_i row found
      split
      · rename_i checked
        have typed := checkRow_sound checked
        have same := Option.some.inj (frame.signatureFound.symm.trans admission.signatureFound)
        have shape := signature?_readout environment.provider request.relation
          request.arguments.length frame.signature frame.signatureFound
        refine ⟨rfl, ?_⟩
        intro branch member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with equality | equality <;> subst branch
        · exact ⟨typed.2.length.trans shape.2.2.1 |>.symm, shape.2.2.2.symm,
            by simpa only [same] using admission.schemas, admission.values, admission.names⟩
        · trivial
      · exact ⟨rfl, by intro branch member; simp only [List.mem_singleton] at member; subst branch; trivial⟩
  | arguments frame => exact expandArguments_ready admission frame ready
  | matcher frame => exact expandMatcher_ready admission frame ready

def StateReady {environment : Environment} {request : Request}
    (admission : InputAdmission environment request) (state : State environment request) : Prop :=
  state.unresolved = [] ∧ ∀ task ∈ state.agenda, TaskReady admission task

theorem start_ready {environment : Environment} {request : Request}
    (admission : InputAdmission environment request) : StateReady admission (start environment request) := by
  refine ⟨rfl, ?_⟩
  intro task member
  simp only [start, List.mem_singleton] at member
  subst task
  trivial

theorem tick_ready {environment : Environment} {request : Request}
    (admission : InputAdmission environment request) {state : State environment request}
    (ready : StateReady admission state) : StateReady admission (tick environment request state) := by
  cases agenda : state.agenda with
  | nil => simpa only [tick, Scheduler.tick, agenda] using ready
  | cons task tasks =>
    obtain ⟨empty, children⟩ := expand_ready admission task (ready.2 task (by rw [agenda]; simp))
    refine ⟨by simp only [tick, Scheduler.tick, agenda, ready.1, empty, List.nil_append], ?_⟩
    intro branch member
    simp only [tick, Scheduler.tick, agenda, List.mem_append] at member
    rcases member with generated | retained
    · exact children branch generated
    · exact ready.2 branch (by rw [agenda]; exact List.mem_cons_of_mem _ retained)

theorem run_ready {environment : Environment} {request : Request}
    (admission : InputAdmission environment request) (fuel : Nat) {state : State environment request}
    (ready : StateReady admission state) : StateReady admission (run environment request fuel state) := by
  induction fuel generalizing state with
  | zero => exact ready
  | succ fuel inductionHypothesis => exact inductionHypothesis (tick_ready admission ready)

theorem run_start_resolved {environment : Environment} {request : Request}
    (admission : InputAdmission environment request) (fuel : Nat) :
    (run environment request fuel (start environment request)).unresolved = [] :=
  (run_ready admission fuel (start_ready admission)).1

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Query
