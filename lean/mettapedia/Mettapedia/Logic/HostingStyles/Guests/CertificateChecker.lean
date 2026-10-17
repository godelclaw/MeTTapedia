import Mettapedia.GSLT.LanguageDef.AuthoredComputation
import Mettapedia.Logic.HostingStyles.Guests.HostedRuns

/-!
# The check of a certificate, as it runs

The shared checker decides a certificate of an authored calculus by recursion
on the certificate (`InferenceComputedLeaves.check`).  This module gives the
same check as a theory with states and steps (`certificateChecker K`), read off
that recursion.

* A **state** is the list of the obligations that remain, the next one first;
  an obligation is a judgment with the certificate submitted for it
  (`Checking`).
* A **step** checks the first obligation at its root (`CheckStep`):
  a rule node, in a certificate or in a replay tree, is replaced by the
  premises of its rule instance, each with the certificate beneath it; a
  computed leaf that returns its judgment is removed.  A computed leaf runs
  an authored program of the calculus to its answer in one step.
* The check **accepts** when no obligation remains.

Nothing is assumed of the calculus.

## What is proved of it

* A state has at most one step (`CheckStep.deterministic`).
* Every step checks exactly one node (`CheckStep.pending`), so the check has a
  rank (`certificateCheckerRank`) and terminates.
* **The check reaches the accepting state exactly when the shared checker
  accepts every obligation** (`reaches_accepting_iff`), and then in exactly
  as many steps as the certificates have nodes (`steps_accepting_iff`).  For
  one certificate: `reaches_accepting_singleton_iff`, `steps_singleton_iff`.
* Some certificate of a judgment is checked to acceptance exactly when the
  judgment is derivable from the rules and the facts
  (`exists_reaches_accepting_iff_derivable`).
* Steps are stable under obligations that wait behind
  (`CheckStep.append`).

## What a host of it has

For a map from the check into any theory:

* if the map is hosting, the image of the state that submits a certificate
  reaches the image of the accepting state exactly when the shared checker
  accepts the certificate (`reaches_image_iff_check`), so some certificate's
  image does exactly when the judgment is derivable
  (`exists_reaches_image_iff_derivable`);
* if it preserves transitions, the image of an accepted certificate runs for
  as many steps as the certificate has nodes (`steps_image_of_check`).  So a
  theory whose runs are bounded hosts no check that accepts a larger
  certificate; for the candidate presentation the bound is three
  (`not_hostedBy_presented_of_check`, `not_hostedBy_reading_of_check`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.Guests

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef (ValidatedCalculusLanguageDef)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)
open Mettapedia.GSLT.LanguageDef.InferenceChecker
  (RuleInstance RawProof RuleApplication instantiateRule? checkRaw checkRawChildren
    instantiateRule?_eq_some_iff_application)
open Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves (CompactProof check checkChildren)
open Mettapedia.GSLT.LanguageDef.Authored
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
open Mettapedia.Logic.HostingStyles.ContextReadings

/-! ## The shared checker, one node at a time -/

section Unfolding

variable {Query : Type} (definition : ValidatedCalculusLanguageDef)
  (evaluate : Query → Option Pattern)

/-- **The shared checker accepts a rule node** exactly when its rule instance
applies with the judgment as conclusion and the children are accepted for the
premises. -/
theorem check_node_iff (goal : Pattern) (ruleInstance : RuleInstance)
    (children : List (CompactProof Query)) :
    check definition evaluate goal (.node ruleInstance children) = true ↔
      ∃ premises, RuleApplication definition ruleInstance premises goal ∧
        checkChildren definition evaluate premises children = true := by
  simp only [check]
  cases application : instantiateRule? definition ruleInstance with
  | none =>
      constructor
      · intro impossible
        cases impossible
      · rintro ⟨premises, applies, -⟩
        rw [instantiateRule?_eq_some_iff_application.mpr applies] at application
        cases application
  | some result =>
      obtain ⟨premises, conclusion⟩ := result
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨rfl, accepted⟩
        exact ⟨premises, instantiateRule?_eq_some_iff_application.mp application, accepted⟩
      · rintro ⟨otherPremises, applies, accepted⟩
        rw [instantiateRule?_eq_some_iff_application.mpr applies] at application
        cases application
        exact ⟨rfl, accepted⟩

/-- **The raw checker accepts a rule node** on the same condition. -/
theorem checkRaw_node_iff (goal : Pattern) (ruleInstance : RuleInstance)
    (children : List RawProof) :
    checkRaw definition goal (.node ruleInstance children) = true ↔
      ∃ premises, RuleApplication definition ruleInstance premises goal ∧
        checkRawChildren definition premises children = true := by
  simp only [checkRaw]
  cases application : instantiateRule? definition ruleInstance with
  | none =>
      constructor
      · intro impossible
        cases impossible
      · rintro ⟨premises, applies, -⟩
        rw [instantiateRule?_eq_some_iff_application.mpr applies] at application
        cases application
  | some result =>
      obtain ⟨premises, conclusion⟩ := result
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨rfl, accepted⟩
        exact ⟨premises, instantiateRule?_eq_some_iff_application.mp application, accepted⟩
      · rintro ⟨otherPremises, applies, accepted⟩
        rw [instantiateRule?_eq_some_iff_application.mpr applies] at application
        cases application
        exact ⟨rfl, accepted⟩

/-- **The children of a rule node are accepted** exactly when there is one
for each premise and each is accepted for its premise. -/
theorem checkChildren_iff_zip :
    ∀ (premises : List Pattern) (children : List (CompactProof Query)),
      checkChildren definition evaluate premises children = true ↔
        premises.length = children.length ∧
          ∀ obligation ∈ premises.zip children,
            check definition evaluate obligation.1 obligation.2 = true
  | [], [] => by simp [checkChildren]
  | [], _ :: _ => by simp [checkChildren]
  | _ :: _, [] => by simp [checkChildren]
  | premise :: premises, child :: children => by
      simp only [checkChildren, Bool.and_eq_true, checkChildren_iff_zip premises children,
        List.length_cons, Nat.add_right_cancel_iff, List.zip_cons_cons, List.mem_cons,
        forall_eq_or_imp]
      constructor
      · rintro ⟨head, arity, tail⟩
        exact ⟨arity, head, tail⟩
      · rintro ⟨arity, head, tail⟩
        exact ⟨head, arity, tail⟩

/-- The same for the children of a rule node of a replay tree. -/
theorem checkRawChildren_iff_zip :
    ∀ (premises : List Pattern) (children : List RawProof),
      checkRawChildren definition premises children = true ↔
        premises.length = children.length ∧
          ∀ obligation ∈ premises.zip children,
            checkRaw definition obligation.1 obligation.2 = true
  | [], [] => by simp [checkRawChildren]
  | [], _ :: _ => by simp [checkRawChildren]
  | _ :: _, [] => by simp [checkRawChildren]
  | premise :: premises, child :: children => by
      simp only [checkRawChildren, Bool.and_eq_true, checkRawChildren_iff_zip premises children,
        List.length_cons, Nat.add_right_cancel_iff, List.zip_cons_cons, List.mem_cons,
        forall_eq_or_imp]
      constructor
      · rintro ⟨head, arity, tail⟩
        exact ⟨arity, head, tail⟩
      · rintro ⟨arity, head, tail⟩
        exact ⟨head, arity, tail⟩

end Unfolding

/-! ## The nodes of a certificate -/

mutual

/-- The number of rule nodes of a replay tree. -/
def rawNodes : RawProof → Nat
  | .node _ children => rawNodesList children + 1

/-- The number of rule nodes of a list of replay trees. -/
def rawNodesList : List RawProof → Nat
  | [] => 0
  | head :: tail => rawNodes head + rawNodesList tail

end

mutual

/-- **The number of nodes of a certificate**: its rule nodes, those of its
replay trees, and its computed leaves. -/
def certificateNodes {Query : Type} : CompactProof Query → Nat
  | .replay raw => rawNodes raw
  | .computed _ => 1
  | .node _ children => certificateNodesList children + 1

/-- The number of nodes of a list of certificates. -/
def certificateNodesList {Query : Type} : List (CompactProof Query) → Nat
  | [] => 0
  | head :: tail => certificateNodes head + certificateNodesList tail

end

theorem rawNodesList_eq_sum : ∀ trees : List RawProof,
    rawNodesList trees = (trees.map rawNodes).sum
  | [] => rfl
  | head :: tail => by
      rw [rawNodesList, rawNodesList_eq_sum tail]
      rfl

theorem certificateNodesList_eq_sum {Query : Type} : ∀ certificates : List (CompactProof Query),
    certificateNodesList certificates = (certificates.map certificateNodes).sum
  | [] => rfl
  | head :: tail => by
      rw [certificateNodesList, certificateNodesList_eq_sum tail]
      rfl

/-- A replay tree has a node. -/
theorem rawNodes_pos (raw : RawProof) : 0 < rawNodes raw := by
  cases raw with
  | node ruleInstance children =>
      rw [rawNodes]
      exact Nat.succ_pos _

/-- **A certificate has a node.** -/
theorem certificateNodes_pos {Query : Type} (certificate : CompactProof Query) :
    0 < certificateNodes certificate := by
  cases certificate with
  | replay raw => exact rawNodes_pos raw
  | computed query => exact Nat.one_pos
  | node ruleInstance children =>
      rw [certificateNodes]
      exact Nat.succ_pos _

/-! ## States and steps -/

variable (K : AuthoredCalculus)

/-- A certificate of an authored calculus, as the shared checker is given
it. -/
abbrev Certificate : Type := CompactProof K.family.Leaf

/-- **A state of a check**: the obligations that remain, the next one first.
An obligation is a judgment with the certificate submitted for it. -/
abbrev Checking : Type := List (Pattern × Certificate K)

/-- **One step of the check**: the first obligation is checked at its
root. -/
inductive CheckStep : Checking K → Checking K → Prop where
  /-- A rule node of a certificate: its rule instance applies with the
  judgment as conclusion and has as many premises as the node has children;
  the premises replace the obligation, each with the child beneath it. -/
  | node {ruleInstance : RuleInstance} {premises : List Pattern} {goal : Pattern}
      {children : List (Certificate K)} {rest : Checking K}
      (application : RuleApplication K.definition ruleInstance premises goal)
      (arity : premises.length = children.length) :
      CheckStep ((goal, .node ruleInstance children) :: rest) (premises.zip children ++ rest)
  /-- A rule node of a replay tree, checked in the same way. -/
  | replay {ruleInstance : RuleInstance} {premises : List Pattern} {goal : Pattern}
      {children : List RawProof} {rest : Checking K}
      (application : RuleApplication K.definition ruleInstance premises goal)
      (arity : premises.length = children.length) :
      CheckStep ((goal, .replay (.node ruleInstance children)) :: rest)
        (premises.zip (children.map CompactProof.replay) ++ rest)
  /-- A computed leaf: the authored program returns the judgment; the
  obligation is removed. -/
  | computed {leaf : K.family.Leaf} {goal : Pattern} {rest : Checking K}
      (returned : K.family.evaluate leaf = some goal) :
      CheckStep ((goal, .computed leaf) :: rest) rest

/-- **The check of the certificates of an authored calculus, as it runs.**
Two states are the same when they are equal; a state is accepting when no
obligation remains. -/
def certificateChecker : GSLT.{0} where
  Term := Checking K
  equations := ⟨Eq, eq_equivalence⟩
  rewrites := CheckStep K
  rewrites_resp_left := by
    intro state other next same step
    cases same
    exact ⟨next, step, rfl⟩
  rewrites_resp_right := by
    intro state next other step same
    cases same
    exact step

/-- The check as a theory presented through its contexts: its only contexts
are the hole and the states. -/
abbrev checkerTheory : ContextTheory.{0} := (certificateChecker K).termsAlone

variable {K}

/-- **A state has at most one step**: the check is deterministic. -/
theorem CheckStep.deterministic {state first second : Checking K} (left : CheckStep K state first)
    (right : CheckStep K state second) : first = second := by
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
  | computed returned =>
      cases right with
      | computed otherReturned => rfl

/-- **Steps are stable under obligations that wait behind.** -/
theorem CheckStep.append {state next : Checking K} (step : CheckStep K state next)
    (waiting : Checking K) : CheckStep K (state ++ waiting) (next ++ waiting) := by
  cases step with
  | node application arity =>
      rw [List.cons_append, List.append_assoc]
      exact .node application arity
  | replay application arity =>
      rw [List.cons_append, List.append_assoc]
      exact .replay application arity
  | computed returned => exact .computed returned

/-- The accepting state has no step. -/
theorem not_checkStep_nil (next : Checking K) : ¬ CheckStep K [] next :=
  fun step => by cases step

/-! ## The nodes that remain -/

variable (K)

/-- **The nodes that remain to be checked** in a state. -/
def pending (state : Checking K) : Nat :=
  (state.map fun obligation => certificateNodes obligation.2).sum

variable {K}

@[simp] theorem pending_nil : pending K [] = 0 := rfl

@[simp] theorem pending_cons (goal : Pattern) (certificate : Certificate K) (rest : Checking K) :
    pending K ((goal, certificate) :: rest) = certificateNodes certificate + pending K rest :=
  rfl

@[simp] theorem pending_append (first second : Checking K) :
    pending K (first ++ second) = pending K first + pending K second := by
  simp [pending]

/-- The nodes of the children paired with their premises. -/
theorem pending_zip : ∀ (premises : List Pattern) (children : List (Certificate K)),
    premises.length = children.length →
      pending K (premises.zip children) = certificateNodesList children
  | [], [], _ => rfl
  | [], _ :: _, arity => by cases arity
  | _ :: _, [], arity => by cases arity
  | premise :: premises, child :: children, arity => by
      rw [List.zip_cons_cons, pending_cons, certificateNodesList,
        pending_zip premises children (Nat.succ.inj arity)]

/-- The nodes of the replay trees paired with their premises. -/
theorem pending_zip_replay : ∀ (premises : List Pattern) (children : List RawProof),
    premises.length = children.length →
      pending K (premises.zip (children.map CompactProof.replay)) = rawNodesList children
  | [], [], _ => rfl
  | [], _ :: _, arity => by cases arity
  | _ :: _, [], arity => by cases arity
  | premise :: premises, child :: children, arity => by
      rw [List.map_cons, List.zip_cons_cons, pending_cons, rawNodesList,
        pending_zip_replay premises children (Nat.succ.inj arity)]
      rfl

/-- **Every step checks exactly one node.** -/
theorem CheckStep.pending {state next : Checking K} (step : CheckStep K state next) :
    pending K state = pending K next + 1 := by
  cases step with
  | node application arity =>
      rw [pending_cons, pending_append, pending_zip _ _ arity, certificateNodes]
      omega
  | replay application arity =>
      rw [pending_cons, pending_append, pending_zip_replay _ _ arity, certificateNodes, rawNodes]
      omega
  | computed returned =>
      rw [pending_cons, certificateNodes]
      omega

/-- A state in which no node remains is the accepting state. -/
theorem eq_nil_of_pending_eq_zero {state : Checking K} (none : pending K state = 0) :
    state = [] := by
  cases state with
  | nil => rfl
  | cons obligation rest =>
      obtain ⟨goal, certificate⟩ := obligation
      rw [pending_cons] at none
      have positive := certificateNodes_pos certificate
      omega

variable (K)

/-- **The check has a rank**: the nodes that remain.  It terminates. -/
def certificateCheckerRank : (checkerTheory K).Rank where
  rank := fun state => pending K state
  lowers := fun step => by
    have counted := CheckStep.pending step
    omega

/-! ## Reaching the accepting state -/

/-- **The shared checker accepts every obligation of a state.** -/
def Accepted (state : Checking K) : Prop :=
  ∀ obligation ∈ state, check K.definition K.family.evaluate obligation.1 obligation.2 = true

variable {K}

theorem accepted_nil : Accepted K [] := fun _ member => absurd member List.not_mem_nil

theorem accepted_cons {goal : Pattern} {certificate : Certificate K} {rest : Checking K} :
    Accepted K ((goal, certificate) :: rest) ↔
      check K.definition K.family.evaluate goal certificate = true ∧ Accepted K rest := by
  simp [Accepted]

theorem accepted_append {first second : Checking K} :
    Accepted K (first ++ second) ↔ Accepted K first ∧ Accepted K second := by
  simp only [Accepted, List.mem_append]
  exact ⟨fun all => ⟨fun obligation member => all obligation (.inl member),
      fun obligation member => all obligation (.inr member)⟩,
    fun both obligation member => member.elim (both.1 obligation) (both.2 obligation)⟩

/-- Replay trees paired with their premises are accepted exactly when the raw
checker accepts each. -/
theorem accepted_zip_replay (premises : List Pattern) (children : List RawProof) :
    Accepted K (premises.zip (children.map CompactProof.replay)) ↔
      ∀ obligation ∈ premises.zip children,
        checkRaw K.definition obligation.1 obligation.2 = true := by
  induction premises generalizing children with
  | nil => simp [Accepted]
  | cons premise premises ih =>
      cases children with
      | nil => simp [Accepted]
      | cons child children =>
          rw [List.map_cons, List.zip_cons_cons, List.zip_cons_cons, accepted_cons, ih children]
          simp only [check, List.mem_cons, forall_eq_or_imp]

/-- **A step keeps acceptance, both ways**: the obligations before a step are
accepted exactly when those after it are. -/
theorem CheckStep.accepted_iff {state next : Checking K} (step : CheckStep K state next) :
    Accepted K state ↔ Accepted K next := by
  cases step with
  | @node ruleInstance premises goal children rest application arity =>
      rw [accepted_cons, accepted_append, check_node_iff]
      constructor
      · rintro ⟨⟨otherPremises, otherApplication, accepted⟩, restAccepted⟩
        obtain ⟨rfl, -⟩ := application.outputs_unique otherApplication
        exact ⟨((checkChildren_iff_zip _ _ _ _).mp accepted).2, restAccepted⟩
      · rintro ⟨accepted, restAccepted⟩
        exact ⟨⟨premises, application,
          (checkChildren_iff_zip _ _ _ _).mpr ⟨arity, accepted⟩⟩, restAccepted⟩
  | @replay ruleInstance premises goal children rest application arity =>
      rw [accepted_cons, accepted_append, accepted_zip_replay]
      have unfolded : check K.definition K.family.evaluate goal
            (.replay (.node ruleInstance children)) =
          checkRaw K.definition goal (.node ruleInstance children) := by
        simp only [check]
      rw [unfolded, checkRaw_node_iff]
      constructor
      · rintro ⟨⟨otherPremises, otherApplication, accepted⟩, restAccepted⟩
        obtain ⟨rfl, -⟩ := application.outputs_unique otherApplication
        exact ⟨((checkRawChildren_iff_zip _ _ _).mp accepted).2, restAccepted⟩
      · rintro ⟨accepted, restAccepted⟩
        exact ⟨⟨premises, application,
          (checkRawChildren_iff_zip _ _ _).mpr ⟨arity, accepted⟩⟩, restAccepted⟩
  | @computed leaf goal rest returned =>
      rw [accepted_cons]
      have unfolded : check K.definition K.family.evaluate goal (.computed leaf) = true := by
        simp only [check, returned, decide_true]
      exact ⟨fun both => both.2, fun restAccepted => ⟨unfolded, restAccepted⟩⟩

/-- **An accepted state that is not the accepting state has a step.** -/
theorem exists_step_of_accepted {goal : Pattern} {certificate : Certificate K} {rest : Checking K}
    (accepted : Accepted K ((goal, certificate) :: rest)) :
    ∃ next, CheckStep K ((goal, certificate) :: rest) next := by
  have head := (accepted_cons.mp accepted).1
  cases certificate with
  | node ruleInstance children =>
      obtain ⟨premises, application, childrenAccepted⟩ := (check_node_iff _ _ _ _ _).mp head
      exact ⟨_, .node application ((checkChildren_iff_zip _ _ _ _).mp childrenAccepted).1⟩
  | replay raw =>
      cases raw with
      | node ruleInstance children =>
          have unfolded : checkRaw K.definition goal (.node ruleInstance children) = true := by
            simpa only [check] using head
          obtain ⟨premises, application, childrenAccepted⟩ :=
            (checkRaw_node_iff _ _ _ _).mp unfolded
          exact ⟨_, .replay application
            ((checkRawChildren_iff_zip _ _ _).mp childrenAccepted).1⟩
  | computed leaf =>
      exact ⟨_, .computed (by simpa only [check, decide_eq_true_eq] using head)⟩

/-- An accepted state is checked to the accepting state, in as many steps as
nodes remain. -/
theorem steps_of_accepted : ∀ (count : Nat) (state : Checking K), pending K state = count →
    Accepted K state → (checkerTheory K).Steps (interface := PUnit.unit) count state []
  | 0, state, counted, _ => by
      rw [eq_nil_of_pending_eq_zero counted]
      exact .zero _
  | count + 1, state, counted, accepted => by
      cases state with
      | nil => cases counted
      | cons obligation rest =>
          obtain ⟨goal, certificate⟩ := obligation
          obtain ⟨next, step⟩ := exists_step_of_accepted accepted
          have lowered := CheckStep.pending step
          exact .succ step
            (steps_of_accepted count next (by omega) ((CheckStep.accepted_iff step).mp accepted))

/-- **The check reaches the accepting state in a given number of steps exactly
when the shared checker accepts every obligation and that is the number of
nodes that remain.** -/
theorem steps_accepting_iff (count : Nat) (state : Checking K) :
    (checkerTheory K).Steps (interface := PUnit.unit) count state [] ↔
      Accepted K state ∧ count = pending K state := by
  constructor
  · intro steps
    have counted := ContextTheory.Steps.counted (theory := checkerTheory K)
      (interface := PUnit.unit) (fun state => pending K state)
      (fun step => CheckStep.pending step) steps
    have accepted := ContextTheory.Steps.carry_back (theory := checkerTheory K)
      (interface := PUnit.unit) (fun state => Accepted K state)
      (fun step holds => (CheckStep.accepted_iff step).mpr holds) steps accepted_nil
    have unfolded : pending K state = 0 + count := counted
    exact ⟨accepted, by omega⟩
  · rintro ⟨accepted, rfl⟩
    exact steps_of_accepted _ state rfl accepted

/-- **The check reaches the accepting state exactly when the shared checker
accepts every obligation.** -/
theorem reaches_accepting_iff (state : Checking K) :
    (checkerTheory K).Reaches (interface := PUnit.unit) state [] ↔ Accepted K state :=
  (ContextTheory.reaches_iff_exists_steps (theory := checkerTheory K) (interface := PUnit.unit)
    state []).trans
    ⟨fun ⟨count, steps⟩ => ((steps_accepting_iff count state).mp steps).1,
      fun accepted => ⟨_, (steps_accepting_iff _ state).mpr ⟨accepted, rfl⟩⟩⟩

/-- The state that submits one certificate for one judgment is accepted
exactly when the shared checker accepts the certificate. -/
theorem accepted_singleton_iff (goal : Pattern) (certificate : Certificate K) :
    Accepted K [(goal, certificate)] ↔
      check K.definition K.family.evaluate goal certificate = true := by
  rw [accepted_cons]
  exact ⟨fun both => both.1, fun head => ⟨head, accepted_nil⟩⟩

/-- **A submitted certificate is checked to acceptance exactly when the
shared checker accepts it.** -/
theorem reaches_accepting_singleton_iff (goal : Pattern) (certificate : Certificate K) :
    (checkerTheory K).Reaches (interface := PUnit.unit) [(goal, certificate)] [] ↔
      check K.definition K.family.evaluate goal certificate = true :=
  (reaches_accepting_iff _).trans (accepted_singleton_iff goal certificate)

/-- **And then in exactly as many steps as the certificate has nodes.** -/
theorem steps_singleton_iff (count : Nat) (goal : Pattern) (certificate : Certificate K) :
    (checkerTheory K).Steps (interface := PUnit.unit) count [(goal, certificate)] [] ↔
      check K.definition K.family.evaluate goal certificate = true ∧
        count = certificateNodes certificate := by
  refine (steps_accepting_iff count [(goal, certificate)]).trans ?_
  rw [accepted_singleton_iff, pending_cons, pending_nil, Nat.add_zero]

variable (K)

/-- **Some certificate of a judgment is checked to acceptance exactly when
the judgment is derivable** from the rules and the facts of the calculus. -/
theorem exists_reaches_accepting_iff_derivable (goal : Pattern) :
    (∃ certificate : Certificate K,
      (checkerTheory K).Reaches (interface := PUnit.unit) [(goal, certificate)] []) ↔
      K.Derivable goal := by
  rw [← K.accepts_iff goal]
  exact exists_congr fun certificate => reaches_accepting_singleton_iff goal certificate

variable {K}

/-- **Negative**: a rejected certificate is never checked to acceptance. -/
theorem not_reaches_accepting_of_rejected {goal : Pattern} {certificate : Certificate K}
    (rejected : check K.definition K.family.evaluate goal certificate = false) :
    ¬ (checkerTheory K).Reaches (interface := PUnit.unit) [(goal, certificate)] [] :=
  fun reaches => by
    rw [(reaches_accepting_singleton_iff goal certificate).mp reaches] at rejected
    cases rejected

/-! ## What a host of the check has -/

section Hosts

variable {candidate : ContextTheory.{0}}
  (map : ContextMap (checkerTheory K) candidate)

/-- **Under a hosting map, the image of a submitted certificate reaches the
image of the accepting state exactly when the shared checker accepts the
certificate.**  Reaching is up to the static equivalence of the host. -/
theorem reaches_image_iff_check (hosting : map.Hosting) (goal : Pattern)
    (certificate : Certificate K) :
    (∃ final, candidate.Reaches (map.term (origin := PUnit.unit) [(goal, certificate)]) final ∧
        (candidate.equations (map.interface PUnit.unit)).r final
          (map.term (origin := PUnit.unit) [])) ↔
      check K.definition K.family.evaluate goal certificate = true := by
  refine (hosting.reaches_image_iff (interface := PUnit.unit) [(goal, certificate)] []).trans
    (Iff.trans ?_ (reaches_accepting_singleton_iff goal certificate))
  constructor
  · rintro ⟨final, reaches, same⟩
    obtain rfl : final = [] := same
    exact reaches
  · intro reaches
    exact ⟨[], reaches, rfl⟩

/-- **Soundness needs reflection only**: when the image of a submitted
certificate reaches the image of the accepting state, and the map reflects
steps and the static equivalence, the shared checker accepts the
certificate. -/
theorem check_of_reaches_image (reflects : map.ReflectsTransitions)
    (reflectsEquations : map.ReflectsEquations) {goal : Pattern} {certificate : Certificate K}
    {final : candidate.Term (map.interface PUnit.unit)}
    (reaches : candidate.Reaches (map.term (origin := PUnit.unit) [(goal, certificate)]) final)
    (related : (candidate.equations (map.interface PUnit.unit)).r final
      (map.term (origin := PUnit.unit) [])) :
    check K.definition K.family.evaluate goal certificate = true := by
  obtain ⟨sourceFinal, sourceReaches, same⟩ :=
    map.reaches_of_reaches_image (interface := PUnit.unit) reflects reflectsEquations reaches
      related
  obtain rfl : sourceFinal = [] := same
  exact (reaches_accepting_singleton_iff goal certificate).mp sourceReaches

/-- **Completeness needs preservation only**: the image of an accepted
certificate runs to the image of the accepting state in as many steps as the
certificate has nodes. -/
theorem steps_image_of_check (preserves : map.PreservesTransitions) {goal : Pattern}
    {certificate : Certificate K}
    (accepted : check K.definition K.family.evaluate goal certificate = true) :
    candidate.Steps (certificateNodes certificate)
      (map.term (origin := PUnit.unit) [(goal, certificate)])
      (map.term (origin := PUnit.unit) []) :=
  map.steps_of_preserves preserves
    ((steps_singleton_iff _ goal certificate).mpr ⟨accepted, rfl⟩)

/-- **Under a hosting map, the image of some certificate of a judgment
reaches the image of the accepting state exactly when the judgment is
derivable** from the rules and the facts of the calculus. -/
theorem exists_reaches_image_iff_derivable (hosting : map.Hosting) (goal : Pattern) :
    (∃ (certificate : Certificate K) (final : candidate.Term (map.interface PUnit.unit)),
        candidate.Reaches (map.term (origin := PUnit.unit) [(goal, certificate)]) final ∧
          (candidate.equations (map.interface PUnit.unit)).r final
            (map.term (origin := PUnit.unit) [])) ↔
      K.Derivable goal := by
  rw [← K.accepts_iff goal]
  exact exists_congr fun certificate => reaches_image_iff_check map hosting goal certificate

end Hosts

/-- **The candidate presentation hosts, under the linear reading, no check
that accepts a certificate of more than three nodes**, for any evaluator of
its premises. -/
theorem not_hostedBy_presented_of_check (base : BasePremiseEvaluator) {goal : Pattern}
    {certificate : Certificate K}
    (accepted : check K.definition K.family.evaluate goal certificate = true)
    (large : 3 < certificateNodes certificate) :
    ¬ HostedBy (checkerTheory K) (presentedReading base) :=
  not_hostedBy_presented_of_steps base (interface := PUnit.unit)
    ((steps_singleton_iff _ goal certificate).mpr ⟨accepted, rfl⟩) large

/-- **Nor under any of its readings**, the reading with regions and the
cartesian reading among them. -/
theorem not_hostedBy_reading_of_check (base : BasePremiseEvaluator)
    (declared : LanguageDef.Contexts.Interface → Prop) {goal : Pattern}
    {certificate : Certificate K}
    (accepted : check K.definition K.family.evaluate goal certificate = true)
    (large : 3 < certificateNodes certificate) :
    ¬ HostedBy (checkerTheory K) ((presentedReading base).regionReading declared) :=
  not_hostedBy_reading_of_steps base declared (interface := PUnit.unit)
    ((steps_singleton_iff _ goal certificate).mpr ⟨accepted, rfl⟩) large

#print axioms check_node_iff
#print axioms checkChildren_iff_zip
#print axioms CheckStep.deterministic
#print axioms CheckStep.append
#print axioms CheckStep.pending
#print axioms certificateCheckerRank
#print axioms CheckStep.accepted_iff
#print axioms exists_step_of_accepted
#print axioms steps_accepting_iff
#print axioms reaches_accepting_iff
#print axioms reaches_accepting_singleton_iff
#print axioms steps_singleton_iff
#print axioms exists_reaches_accepting_iff_derivable
#print axioms not_reaches_accepting_of_rejected
#print axioms reaches_image_iff_check
#print axioms check_of_reaches_image
#print axioms steps_image_of_check
#print axioms exists_reaches_image_iff_derivable
#print axioms not_hostedBy_presented_of_check
#print axioms not_hostedBy_reading_of_check

end Mettapedia.Logic.HostingStyles.Guests
