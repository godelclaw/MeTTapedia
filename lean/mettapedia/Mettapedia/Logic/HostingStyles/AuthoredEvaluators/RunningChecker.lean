import Mettapedia.Logic.HostingStyles.AuthoredEvaluators.EngineSteps
import Mettapedia.Logic.HostingStyles.Guests.MM0Checker

/-!
# The check of a certificate, with running leaves

In the check of the certificates of an authored calculus as it runs
(`Guests.certificateChecker`), a computed leaf is one step: the authored
program that it names runs inside that step, with the fuel that the leaf
carries.  This module gives the same check with the engine's steps in view.

* A **state** is the list of the obligations that remain, together with the
  configuration of the engine when the leaf at the head of the list is being
  run (`Running`).
* A **step** (`RunStep`) checks a rule node as before; or starts the leaf at
  the head, by the configuration of the call of its program on its query; or
  is one step of the engine on that configuration; or finishes the leaf, when
  the configuration holds the answer that the leaf claims and the judgment is
  the judgment of the query and that answer.
* The fuel of a leaf is not read: a run needs none.

## What is proved of it

* A state has at most one step (`RunStep.deterministic`).
* **The check reaches the accepting state exactly when every obligation is
  valid** (`running_reaches_accepting_iff`): each rule node applies with the
  judgment as conclusion, and each computed leaf claims the answer of its
  program for the judgment asked (`Certifies`).
* A certificate that the checker with fuel accepts is valid (`certifies_of_check`),
  and a computed leaf is valid exactly when the checker with fuel accepts it
  with some fuel (`certifies_computed_iff`).  So some certificate of a judgment is
  checked to acceptance exactly when the judgment is derivable from the rules
  and the facts (`exists_running_reaches_iff_derivable`).
* **A computed leaf takes two steps more than the run of its program**
  (`leaf_steps`), three at least (`leaf_steps_ge`), where the checker with
  fuel takes one.  Every step of the checker with fuel is a nonempty run of
  this one (`transGen_of_checkStep`).

## MM0

For the MM0 calculus over a theory, the running check of some certificate of
`context ⊢ expression` reaches the accepting state exactly when the kernel
derives the judgment (`mm0Running_reaches_iff_derives`), and a hosting map
carries this to its images (`mm0Running_reaches_image_iff_derives`).  The
lookups, the instantiations and the conversions of the kernel are now runs of
their equation programs, step by step, inside the check that a candidate is
asked to host.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AuthoredEvaluators

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
  (RuleInstance RawProof RuleApplication checkRaw checkRawChildren)
open Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves (CompactProof check checkChildren)
open Mettapedia.GSLT.LanguageDef.Authored
open Mettapedia.Languages.MM0
open Mettapedia.Languages.MM0.Presentation.Calculus
open Mettapedia.Logic.HostingStyles.Guests
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles (successorTheory)

/-! ## States and steps -/

variable (K : AuthoredCalculus)

/-- A leaf of one member of the family of a calculus: a query, the answer that
it claims, and a fuel. -/
abbrev MemberLeaf (index : K.family.Index) : Type :=
  Mettapedia.GSLT.LanguageDef.Authored.Leaf (K.family.Query index) (K.family.Answer index)

/-- **A state of the check with running leaves**: the obligations that remain,
and the configuration of the engine when the leaf at their head is being
run. -/
structure Running where
  /-- The configuration of the run of the leaf at the head, once started. -/
  machine : Option Configuration
  /-- The obligations that remain, the next one first. -/
  obligations : Checking K

/-- **One step of the check with running leaves.** -/
inductive RunStep : Running K → Running K → Prop where
  /-- A rule node of a certificate, as in the check with fuel. -/
  | node {ruleInstance : RuleInstance} {premises : List Pattern} {goal : Pattern}
      {children : List (Certificate K)} {rest : Checking K}
      (application : RuleApplication K.definition ruleInstance premises goal)
      (arity : premises.length = children.length) :
      RunStep ⟨none, (goal, .node ruleInstance children) :: rest⟩
        ⟨none, premises.zip children ++ rest⟩
  /-- A rule node of a replay tree, as in the check with fuel. -/
  | replay {ruleInstance : RuleInstance} {premises : List Pattern} {goal : Pattern}
      {children : List RawProof} {rest : Checking K}
      (application : RuleApplication K.definition ruleInstance premises goal)
      (arity : premises.length = children.length) :
      RunStep ⟨none, (goal, .replay (.node ruleInstance children)) :: rest⟩
        ⟨none, premises.zip (children.map CompactProof.replay) ++ rest⟩
  /-- A computed leaf starts: the configuration of the call of its program on
  its query. -/
  | start {index : K.family.Index}
      {leaf : MemberLeaf K index} {goal : Pattern}
      {rest : Checking K} :
      RunStep ⟨none, (goal, .computed ⟨index, leaf⟩) :: rest⟩
        ⟨some (callConfiguration (K.family.computation index).head
          ((K.family.computation index).encodeQuery leaf.query)),
          (goal, .computed ⟨index, leaf⟩) :: rest⟩
  /-- One step of the engine on the run of the leaf. -/
  | run {index : K.family.Index}
      {leaf : MemberLeaf K index} {goal : Pattern}
      {rest : Checking K} {configuration next : Configuration}
      (moved : step (K.family.computation index).program (K.family.computation index).host
        configuration = some next) :
      RunStep ⟨some configuration, (goal, .computed ⟨index, leaf⟩) :: rest⟩
        ⟨some next, (goal, .computed ⟨index, leaf⟩) :: rest⟩
  /-- The leaf finishes: the engine holds the answer that the leaf claims, and
  the judgment is that of its query and that answer. -/
  | finish {index : K.family.Index}
      {leaf : MemberLeaf K index} {goal : Pattern}
      {rest : Checking K} {configuration : Configuration}
      (held : configuration =
        valueConfiguration ((K.family.computation index).encodeAnswer (some leaf.answer)))
      (claimed : goal = K.family.judgment index leaf.query leaf.answer) :
      RunStep ⟨some configuration, (goal, .computed ⟨index, leaf⟩) :: rest⟩ ⟨none, rest⟩

/-- **The check of the certificates of an authored calculus, with running
leaves.**  Two states are the same when they are equal; a state is accepting
when no obligation remains and no leaf is being run. -/
def runningChecker : GSLT.{0} where
  Term := Running K
  equations := ⟨Eq, eq_equivalence⟩
  rewrites := RunStep K
  rewrites_resp_left := by
    intro state other next same moved
    cases same
    exact ⟨next, moved, rfl⟩
  rewrites_resp_right := by
    intro state next other moved same
    cases same
    exact moved

/-- The check as a theory presented through its contexts. -/
abbrev runningTheory : ContextTheory.{0} := (runningChecker K).termsAlone

/-- The state that submits obligations, with no leaf being run. -/
def submitted (obligations : Checking K) : Running K := ⟨none, obligations⟩

variable {K}

/-- **A state has at most one step.** -/
theorem RunStep.deterministic {state first second : Running K} (left : RunStep K state first)
    (right : RunStep K state second) : first = second := by
  cases left with
  | node application arity =>
      cases right with
      | node otherApplication otherArity =>
          obtain ⟨rfl, -⟩ := application.outputs_unique otherApplication
          rfl
  | replay application arity =>
      cases right with
      | replay otherApplication otherArity =>
          obtain ⟨rfl, -⟩ := application.outputs_unique otherApplication
          rfl
  | start =>
      cases right with
      | start => rfl
  | run moved =>
      cases right with
      | run otherMoved =>
          obtain rfl := Option.some.inj (moved.symm.trans otherMoved)
          rfl
      | finish held claimed =>
          subst held
          simp [valueConfiguration, step] at moved
  | finish held claimed =>
      cases right with
      | run otherMoved =>
          subst held
          simp [valueConfiguration, step] at otherMoved
      | finish otherHeld otherClaimed => rfl

/-- The accepting state has no step. -/
theorem not_runStep_accepting (next : Running K) : ¬ RunStep K (submitted K []) next :=
  fun moved => by cases moved

/-! ## Valid certificates -/

variable (K)

/-- **A certificate certifies a judgment**: each of its rule nodes applies
with the judgment asked as conclusion and has a valid child for each premise,
and each of its computed leaves claims an answer that its program relates to
its query, for the judgment of that query and answer.  The fuel of a leaf is
not read. -/
inductive Certifies : Pattern → Certificate K → Prop where
  | node {ruleInstance : RuleInstance} {premises : List Pattern} {goal : Pattern}
      {children : List (Certificate K)}
      (application : RuleApplication K.definition ruleInstance premises goal)
      (arity : premises.length = children.length)
      (each : ∀ obligation ∈ premises.zip children, Certifies obligation.1 obligation.2) :
      Certifies goal (.node ruleInstance children)
  | replay {ruleInstance : RuleInstance} {premises : List Pattern} {goal : Pattern}
      {children : List RawProof}
      (application : RuleApplication K.definition ruleInstance premises goal)
      (arity : premises.length = children.length)
      (each : ∀ obligation ∈ premises.zip children, Certifies obligation.1 (.replay obligation.2)) :
      Certifies goal (.replay (.node ruleInstance children))
  | computed {index : K.family.Index}
      {leaf : MemberLeaf K index} {goal : Pattern}
      (related : (K.family.computation index).relation leaf.query leaf.answer)
      (claimed : goal = K.family.judgment index leaf.query leaf.answer) :
      Certifies goal (.computed ⟨index, leaf⟩)

/-- What holds of a state from which the check can still accept. -/
def CanAccept : Running K → Prop
  | ⟨none, obligations⟩ => ∀ obligation ∈ obligations, Certifies K obligation.1 obligation.2
  | ⟨some configuration, (goal, .computed ⟨index, leaf⟩) :: rest⟩ =>
      goal = K.family.judgment index leaf.query leaf.answer ∧
        Reaches (K.family.computation index).program (K.family.computation index).host
          configuration
          (valueConfiguration ((K.family.computation index).encodeAnswer (some leaf.answer))) ∧
        ∀ obligation ∈ rest, Certifies K obligation.1 obligation.2
  | ⟨some _, _⟩ => False

variable {K}

theorem mem_zip_map_replay {premises : List Pattern} {children : List RawProof}
    {obligation : Pattern × RawProof} (member : obligation ∈ premises.zip children) :
    (obligation.1, (CompactProof.replay obligation.2 : Certificate K)) ∈
      premises.zip (children.map CompactProof.replay) := by
  rw [List.zip_map_right]
  exact List.mem_map.mpr ⟨obligation, member, rfl⟩

theorem mem_zip_map_replay_inv {premises : List Pattern} {children : List RawProof}
    {obligation : Pattern × Certificate K}
    (member : obligation ∈ premises.zip (children.map CompactProof.replay)) :
    ∃ inner ∈ premises.zip children, obligation = (inner.1, CompactProof.replay inner.2) := by
  rw [List.zip_map_right] at member
  obtain ⟨inner, inZip, rfl⟩ := List.mem_map.mp member
  exact ⟨inner, inZip, rfl⟩

/-- **A step carries validity back**: a state that steps to a state from which
the check can accept is one. -/
theorem RunStep.canAccept_back {state next : Running K} (moved : RunStep K state next)
    (valid : CanAccept K next) : CanAccept K state := by
  cases moved with
  | @node ruleInstance premises goal children rest application arity =>
      intro obligation member
      rcases List.mem_cons.mp member with rfl | later
      · exact .node application arity fun inner inZip =>
          valid inner (List.mem_append_left _ inZip)
      · exact valid obligation (List.mem_append_right _ later)
  | @replay ruleInstance premises goal children rest application arity =>
      intro obligation member
      rcases List.mem_cons.mp member with rfl | later
      · exact .replay application arity fun inner inZip =>
          valid _ (List.mem_append_left _ (mem_zip_map_replay inZip))
      · exact valid obligation (List.mem_append_right _ later)
  | @start index leaf goal rest =>
      obtain ⟨claimed, reaches, restValid⟩ := valid
      intro obligation member
      rcases List.mem_cons.mp member with rfl | later
      · exact .computed
          (((K.family.computation index).accepts _ _).mp (applies_iff_reaches.mpr reaches)) claimed
      · exact restValid obligation later
  | @run index leaf goal rest configuration next moved =>
      obtain ⟨claimed, reaches, restValid⟩ := valid
      exact ⟨claimed, Relation.ReflTransGen.head moved reaches, restValid⟩
  | @finish index leaf goal rest configuration held claimed =>
      subst held
      exact ⟨claimed, Relation.ReflTransGen.refl, valid⟩

/-- The run of a leaf, step by step, inside the check. -/
theorem runs_of_reaches {index : K.family.Index}
    {leaf : MemberLeaf K index} {goal : Pattern}
    {rest : Checking K} {configuration final : Configuration}
    (reaches : Reaches (K.family.computation index).program (K.family.computation index).host
      configuration final) :
    Relation.ReflTransGen (RunStep K)
      ⟨some configuration, (goal, .computed ⟨index, leaf⟩) :: rest⟩
      ⟨some final, (goal, .computed ⟨index, leaf⟩) :: rest⟩ := by
  induction reaches with
  | refl => exact .refl
  | tail _ moved ih => exact ih.tail (.run moved)

/-- Obligations that are each checked away are checked away one after the
other. -/
theorem reaches_obligations {obligations : Checking K}
    (each : ∀ obligation ∈ obligations, ∀ rest : Checking K,
      Relation.ReflTransGen (RunStep K) ⟨none, obligation :: rest⟩ ⟨none, rest⟩)
    (rest : Checking K) :
    Relation.ReflTransGen (RunStep K) ⟨none, obligations ++ rest⟩ ⟨none, rest⟩ := by
  induction obligations with
  | nil => exact .refl
  | cons obligation obligations ih =>
      exact (each obligation (List.mem_cons_self ..) (obligations ++ rest)).trans
        (ih fun other member => each other (List.mem_cons_of_mem _ member))

/-- **A valid certificate is checked away**, whatever waits behind it. -/
theorem Certifies.reaches {goal : Pattern} {certificate : Certificate K}
    (valid : Certifies K goal certificate) :
    ∀ rest : Checking K,
      Relation.ReflTransGen (RunStep K) ⟨none, (goal, certificate) :: rest⟩ ⟨none, rest⟩ := by
  induction valid with
  | @node ruleInstance premises goal children application arity each ih =>
      intro rest
      exact Relation.ReflTransGen.head (.node application arity)
        (reaches_obligations (fun obligation member => ih obligation member) rest)
  | @replay ruleInstance premises goal children application arity each ih =>
      intro rest
      refine Relation.ReflTransGen.head (.replay application arity)
        (reaches_obligations (fun obligation member waiting => ?_) rest)
      obtain ⟨inner, inZip, rfl⟩ := mem_zip_map_replay_inv member
      exact ih inner inZip waiting
  | @computed index leaf goal related claimed =>
      intro rest
      have reaches := applies_iff_reaches.mp
        (((K.family.computation index).accepts leaf.query leaf.answer).mpr related)
      exact Relation.ReflTransGen.head .start
        ((runs_of_reaches reaches).trans (.single (.finish rfl claimed)))

/-! ## Reaching the accepting state -/

/-- **The check with running leaves reaches the accepting state exactly when
every obligation is valid.** -/
theorem running_reaches_accepting_iff (obligations : Checking K) :
    (runningTheory K).Reaches (interface := PUnit.unit) (submitted K obligations)
        (submitted K []) ↔
      ∀ obligation ∈ obligations, Certifies K obligation.1 obligation.2 := by
  constructor
  · intro reaches
    have back : ∀ state : Running K,
        Relation.ReflTransGen (RunStep K) state (submitted K []) → CanAccept K state := by
      intro state reduction
      induction reduction using Relation.ReflTransGen.head_induction_on with
      | refl => exact fun _ member => absurd member List.not_mem_nil
      | head moved _ ih => exact moved.canAccept_back ih
    exact back _ reaches
  · intro valid
    have reduction := reaches_obligations (K := K)
      (fun obligation member rest => (valid obligation member).reaches rest) []
    rwa [List.append_nil] at reduction

/-- For one certificate. -/
theorem running_reaches_singleton_iff (goal : Pattern) (certificate : Certificate K) :
    (runningTheory K).Reaches (interface := PUnit.unit) (submitted K [(goal, certificate)])
        (submitted K []) ↔ Certifies K goal certificate :=
  (running_reaches_accepting_iff _).trans
    ⟨fun valid => valid (goal, certificate) (List.mem_singleton.mpr rfl),
      fun valid _ member => (List.mem_singleton.mp member) ▸ valid⟩

/-! ## Valid certificates and the checker with fuel -/

variable (K)

theorem certifies_of_checkRaw :
    ∀ (raw : RawProof) (goal : Pattern), checkRaw K.definition goal raw = true →
      Certifies K goal (.replay raw)
  | .node ruleInstance children, goal, accepted => by
      obtain ⟨premises, application, childrenAccepted⟩ := (checkRaw_node_iff _ _ _ _).mp accepted
      obtain ⟨arity, each⟩ := (checkRawChildren_iff_zip _ _ _).mp childrenAccepted
      exact .replay application arity fun obligation member =>
        certifies_of_checkRaw obligation.2 obligation.1 (each obligation member)
termination_by raw => sizeOf raw
decreasing_by
  have smaller := List.sizeOf_lt_of_mem (List.of_mem_zip member).2
  simp only [RawProof.node.sizeOf_spec]
  omega

/-- **A certificate that the checker with fuel accepts is valid.** -/
theorem certifies_of_check :
    ∀ (certificate : Certificate K) (goal : Pattern),
      check K.definition K.family.evaluate goal certificate = true → Certifies K goal certificate
  | .replay raw, goal, accepted => certifies_of_checkRaw K raw goal (by simpa only [check] using accepted)
  | .computed ⟨index, leaf⟩, goal, accepted => by
      have returned : K.family.evaluate ⟨index, leaf⟩ = some goal := by
        simpa only [check, decide_eq_true_eq] using accepted
      obtain ⟨related, claimed⟩ := AuthoredFamily.evaluate_eq_some returned
      exact .computed related claimed
  | .node ruleInstance children, goal, accepted => by
      obtain ⟨premises, application, childrenAccepted⟩ := (check_node_iff _ _ _ _ _).mp accepted
      obtain ⟨arity, each⟩ := (checkChildren_iff_zip _ _ _ _).mp childrenAccepted
      exact .node application arity fun obligation member =>
        certifies_of_check obligation.2 obligation.1 (each obligation member)
termination_by certificate => sizeOf certificate
decreasing_by
  have smaller := List.sizeOf_lt_of_mem (List.of_mem_zip member).2
  simp only [CompactProof.node.sizeOf_spec]
  omega

variable {K}

/-- **A computed leaf is valid exactly when the checker with fuel accepts it
with some fuel.** -/
theorem certifies_computed_iff {index : K.family.Index} (query : K.family.Query index)
    (answer : K.family.Answer index) (fuel : Nat) (goal : Pattern) :
    Certifies K goal (.computed ⟨index, ⟨query, answer, fuel⟩⟩) ↔
      ∃ enough, check K.definition K.family.evaluate goal
        (.computed ⟨index, ⟨query, answer, enough⟩⟩) = true := by
  constructor
  · intro valid
    cases valid with
    | computed related claimed =>
        obtain ⟨enough, runs⟩ := (K.family.computation index).runs_of_relation related
        refine ⟨enough, ?_⟩
        have returned := AuthoredFamily.evaluate_of_runs (F := K.family) (index := index)
          (leaf := ⟨query, answer, enough⟩) (runs enough le_rfl)
        simp only [check, returned, claimed, decide_true]
  · rintro ⟨enough, accepted⟩
    cases certifies_of_check K _ goal accepted with
    | computed related claimed => exact .computed related claimed

theorem exists_mem_zip_of_mem {α β : Type} :
    ∀ {first : List α} {second : List β}, first.length = second.length →
      ∀ {item : α}, item ∈ first → ∃ other, (item, other) ∈ first.zip second
  | [], _, _, _, member => absurd member List.not_mem_nil
  | _ :: _, [], lengths, _, _ => by cases lengths
  | head :: tail, other :: others, lengths, item, member => by
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨other, List.mem_cons_self ..⟩
      · obtain ⟨found, inZip⟩ := exists_mem_zip_of_mem (Nat.succ.inj lengths) later
        exact ⟨found, List.mem_cons_of_mem _ inZip⟩

/-- **A judgment with a valid certificate is derivable** from the rules and
the facts of the calculus. -/
theorem Certifies.derivable {goal : Pattern} {certificate : Certificate K}
    (valid : Certifies K goal certificate) : K.Derivable goal := by
  induction valid with
  | @node ruleInstance premises goal children application arity each ih =>
      refine .byRule ruleInstance application fun premise member => ?_
      obtain ⟨child, inZip⟩ := exists_mem_zip_of_mem arity member
      exact ih (premise, child) inZip
  | @replay ruleInstance premises goal children application arity each ih =>
      refine .byRule ruleInstance application fun premise member => ?_
      obtain ⟨child, inZip⟩ := exists_mem_zip_of_mem arity member
      exact ih (premise, child) inZip
  | @computed index leaf goal related claimed =>
      exact .fact ⟨index, leaf.query, leaf.answer, related, claimed⟩

variable (K)

/-- **Some certificate of a judgment is checked to acceptance, with running
leaves, exactly when the judgment is derivable** from the rules and the facts
of the calculus. -/
theorem exists_running_reaches_iff_derivable (goal : Pattern) :
    (∃ certificate : Certificate K,
      (runningTheory K).Reaches (interface := PUnit.unit) (submitted K [(goal, certificate)])
        (submitted K [])) ↔ K.Derivable goal := by
  constructor
  · rintro ⟨certificate, reaches⟩
    exact ((running_reaches_singleton_iff goal certificate).mp reaches).derivable
  · intro derivable
    obtain ⟨certificate, accepted⟩ := (K.accepts_iff goal).mpr derivable
    exact ⟨certificate,
      (running_reaches_singleton_iff goal certificate).mpr (certifies_of_check K certificate goal accepted)⟩

variable {K}

/-- **Negative**: a leaf that claims an answer that its program does not
relate to its query is never checked to acceptance, whatever fuel it
carries. -/
theorem not_running_reaches_of_unrelated {index : K.family.Index}
    {leaf : MemberLeaf K index} {goal : Pattern}
    (unrelated : ¬ (K.family.computation index).relation leaf.query leaf.answer) :
    ¬ (runningTheory K).Reaches (interface := PUnit.unit)
      (submitted K [(goal, .computed ⟨index, leaf⟩)]) (submitted K []) := fun reaches => by
  cases (running_reaches_singleton_iff goal _).mp reaches with
  | computed related _ => exact unrelated related

/-! ## The steps of a leaf -/

/-- The run of a leaf, with its number of steps. -/
theorem steps_of_stepsIn {index : K.family.Index}
    {leaf : MemberLeaf K index} {goal : Pattern}
    {rest : Checking K} {count : Nat} {configuration final : Configuration}
    (steps : StepsIn (K.family.computation index).program (K.family.computation index).host count
      configuration final) :
    (runningTheory K).Steps (interface := PUnit.unit) count
      (⟨some configuration, (goal, .computed ⟨index, leaf⟩) :: rest⟩ : Running K)
      ⟨some final, (goal, .computed ⟨index, leaf⟩) :: rest⟩ := by
  induction steps with
  | zero => exact .zero _
  | succ moved _ ih => exact .succ (RunStep.run moved) ih

theorem steps_trans {theory : ContextTheory.{0}} {interface : theory.Interface}
    {first second : Nat} {source middle target : theory.Term interface}
    (left : theory.Steps first source middle) (right : theory.Steps second middle target) :
    theory.Steps (first + second) source target := by
  induction left with
  | zero => simpa using right
  | succ moved _ ih =>
      have joined := ContextTheory.Steps.succ moved (ih right)
      rwa [Nat.add_right_comm] at joined

/-- **A computed leaf takes two steps more than the run of its program**: it
starts, the engine runs to the answer, and it finishes. -/
theorem leaf_steps {index : K.family.Index}
    {leaf : MemberLeaf K index} {goal : Pattern}
    (rest : Checking K) {count : Nat}
    (steps : StepsIn (K.family.computation index).program (K.family.computation index).host count
      (callConfiguration (K.family.computation index).head
        ((K.family.computation index).encodeQuery leaf.query))
      (valueConfiguration ((K.family.computation index).encodeAnswer (some leaf.answer))))
    (claimed : goal = K.family.judgment index leaf.query leaf.answer) :
    (runningTheory K).Steps (interface := PUnit.unit) (count + 2)
      (submitted K ((goal, .computed ⟨index, leaf⟩) :: rest)) (submitted K rest) := by
  have started : (runningTheory K).Steps (interface := PUnit.unit) 1
      (submitted K ((goal, .computed ⟨index, leaf⟩) :: rest))
      ⟨some (callConfiguration (K.family.computation index).head
        ((K.family.computation index).encodeQuery leaf.query)),
        (goal, .computed ⟨index, leaf⟩) :: rest⟩ := .succ RunStep.start (.zero _)
  have finished : (runningTheory K).Steps (interface := PUnit.unit) 1
      (⟨some (valueConfiguration ((K.family.computation index).encodeAnswer (some leaf.answer))),
        (goal, .computed ⟨index, leaf⟩) :: rest⟩ : Running K)
      (submitted K rest) := .succ (RunStep.finish rfl claimed) (.zero _)
  have joined := steps_trans (steps_trans started (steps_of_stepsIn steps)) finished
  rwa [show 1 + count + 1 = count + 2 by omega] at joined

/-- The run of a call to a value has a step. -/
theorem stepsIn_call_pos {program : Program} {host : Host} {head : String}
    {arguments : List Term} {result : Term} {count : Nat}
    (steps : StepsIn program host count (callConfiguration head arguments)
      (valueConfiguration result)) : 0 < count := by
  cases steps with
  | succ _ _ => exact Nat.succ_pos _

/-- So a leaf takes three steps at least, where the check with fuel takes
one. -/
theorem leaf_steps_ge {program : Program} {host : Host} {head : String} {arguments : List Term}
    {result : Term} {count : Nat}
    (steps : StepsIn program host count (callConfiguration head arguments)
      (valueConfiguration result)) : 3 ≤ count + 2 := by
  have positive := stepsIn_call_pos steps
  omega

/-- **Every step of the check with fuel is a nonempty run of the check with
running leaves.** -/
theorem transGen_of_checkStep {state next : Checking K} (moved : CheckStep K state next) :
    Relation.TransGen (RunStep K) (submitted K state) (submitted K next) := by
  cases moved with
  | node application arity => exact .single (.node application arity)
  | replay application arity => exact .single (.replay application arity)
  | @computed leaf goal rest returned =>
      obtain ⟨index, leaf⟩ := leaf
      obtain ⟨related, claimed⟩ := AuthoredFamily.evaluate_eq_some returned
      have reaches := applies_iff_reaches.mp
        (((K.family.computation index).accepts leaf.query leaf.answer).mpr related)
      exact Relation.TransGen.head' RunStep.start
        ((runs_of_reaches reaches).trans (.single (.finish rfl claimed)))

/-! ## What a host of the running check has -/

/-- **Under a hosting map, the image of some certificate of a judgment reaches
the image of the accepting state exactly when the judgment is derivable.** -/
theorem exists_running_reaches_image_iff_derivable {candidate : ContextTheory.{0}}
    (map : ContextMap (runningTheory K) candidate) (hosting : map.Hosting) (goal : Pattern) :
    (∃ (certificate : Certificate K) (final : candidate.Term (map.interface PUnit.unit)),
        candidate.Reaches (map.term (origin := PUnit.unit) (submitted K [(goal, certificate)]))
            final ∧
          (candidate.equations (map.interface PUnit.unit)).r final
            (map.term (origin := PUnit.unit) (submitted K []))) ↔
      K.Derivable goal := by
  rw [← exists_running_reaches_iff_derivable K goal]
  refine exists_congr fun certificate => ?_
  refine (hosting.reaches_image_iff (interface := PUnit.unit)
    (submitted K [(goal, certificate)]) (submitted K [])).trans ?_
  constructor
  · rintro ⟨final, reaches, same⟩
    obtain rfl : final = submitted K [] := same
    exact reaches
  · intro reaches
    exact ⟨submitted K [], reaches, rfl⟩

/-! ## MM0 -/

/-- **The checker of an MM0 theory, with running leaves.** -/
abbrev mm0RunningChecker (T : Kernel.Theory) : ContextTheory.{0} := runningTheory (mm0 T)

/-- **The class of the MM0 checkers with running leaves**: one for each
theory. -/
def MM0RunningChecker (source : ContextTheory.{0}) : Prop :=
  ∃ T : Kernel.Theory, source = mm0RunningChecker T

/-- **Positive**: the checker of each theory. -/
theorem mm0RunningChecker_member (T : Kernel.Theory) : MM0RunningChecker (mm0RunningChecker T) :=
  ⟨T, rfl⟩

/-- **Negative**: the successor theory is none of them.  Each of its terms has
a step, and the accepting state of a check has none. -/
theorem successor_not_mm0RunningChecker : ¬ MM0RunningChecker successorTheory.termsAlone := by
  rintro ⟨T, same⟩
  have normal : ∃ (interface : (mm0RunningChecker T).Interface)
      (term : (mm0RunningChecker T).Term interface),
      ∀ next, ¬ (mm0RunningChecker T).rewrites term next :=
    ⟨PUnit.unit, submitted (mm0 T) [], fun next moved => not_runStep_accepting next moved⟩
  rw [← same] at normal
  obtain ⟨interface, term, stuck⟩ := normal
  exact stuck (Nat.succ term) rfl

/-- **The running check of some certificate of `context ⊢ expression` reaches
the accepting state exactly when the MM0 kernel derives the judgment.** -/
theorem mm0Running_reaches_iff_derives (T : Kernel.Theory) (context : Kernel.Context)
    (hypotheses : List Kernel.Preterm) (expression : Kernel.Preterm) :
    (∃ certificate : Certificate (mm0 T),
      (mm0RunningChecker T).Reaches (interface := PUnit.unit)
        (submitted (mm0 T) [(derivesJ context hypotheses expression, certificate)])
        (submitted (mm0 T) [])) ↔
      Kernel.Derives T.termSignature T.definitionSignature T.theoremSignature context hypotheses
        expression :=
  (exists_running_reaches_iff_derivable (mm0 T) _).trans
    (factDerivation_iff context hypotheses expression)

/-- **The transfer**: under a hosting map from the running checker of a
theory, the image of the state that submits some certificate for
`context ⊢ expression` reaches the image of the accepting state exactly when
the MM0 kernel derives the judgment. -/
theorem mm0Running_reaches_image_iff_derives {candidate : ContextTheory.{0}}
    {T : Kernel.Theory} (map : ContextMap (mm0RunningChecker T) candidate)
    (hosting : map.Hosting) (context : Kernel.Context) (hypotheses : List Kernel.Preterm)
    (expression : Kernel.Preterm) :
    (∃ (certificate : Certificate (mm0 T)) (final : candidate.Term (map.interface PUnit.unit)),
        candidate.Reaches
            (map.term (origin := PUnit.unit)
              (submitted (mm0 T) [(derivesJ context hypotheses expression, certificate)]))
            final ∧
          (candidate.equations (map.interface PUnit.unit)).r final
            (map.term (origin := PUnit.unit) (submitted (mm0 T) []))) ↔
      Kernel.Derives T.termSignature T.definitionSignature T.theoremSignature context hypotheses
        expression :=
  (exists_running_reaches_image_iff_derivable map hosting _).trans
    (factDerivation_iff context hypotheses expression)

#print axioms RunStep.deterministic
#print axioms RunStep.canAccept_back
#print axioms Certifies.reaches
#print axioms running_reaches_accepting_iff
#print axioms certifies_of_check
#print axioms certifies_computed_iff
#print axioms Certifies.derivable
#print axioms exists_running_reaches_iff_derivable
#print axioms not_running_reaches_of_unrelated
#print axioms leaf_steps
#print axioms leaf_steps_ge
#print axioms transGen_of_checkStep
#print axioms exists_running_reaches_image_iff_derivable
#print axioms successor_not_mm0RunningChecker
#print axioms mm0Running_reaches_iff_derives
#print axioms mm0Running_reaches_image_iff_derives

end Mettapedia.Logic.HostingStyles.AuthoredEvaluators
