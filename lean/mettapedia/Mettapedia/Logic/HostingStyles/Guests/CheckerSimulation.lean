import Mettapedia.Logic.HostingStyles.Guests.CertificateChecker

/-!
# A host that checks with smaller steps

A hosting map asks for one step of the host for each step of the check.  A
step of the check instantiates a rule or runs a kernel operation, so a host
whose own steps are small will take several.  `RunsCheck candidate K` is the
sentence for such a host: a reading of the states of the check as terms of
the candidate such that

* each step of the check is a nonempty reduction of the candidate
  (`simulates`);
* the image of a state without step has no step (`normal`);
* the terms without step that an image reaches are one, up to the static
  equivalence (`unique`); this holds when the candidate is confluent up to
  its static equivalence (`normalForms_unique_of_confluentUpTo`);
* only the accepting state is read as the image of the accepting state
  (`accepting`).

**What it buys** (`RunsCheck.reaches_iff_check`): the image of the state that
submits a certificate reaches the image of the accepting state exactly when
the shared checker accepts the certificate; hence some certificate's image
does exactly when the judgment is derivable
(`RunsCheck.exists_reaches_iff_derivable`).  The proof uses that the check is
deterministic and terminates: every state reaches exactly one state without
step (`exists_reaches_normal`, `normal_unique`).

The sentence is weaker than hosting: a hosting map from the check gives it
(`RunsCheck.ofHosting`).  The check runs itself (`RunsCheck.self`).  A theory
whose rank is bounded runs no check that has a longer run
(`isEmpty_runsCheck_of_bounded`), since its rank also bounds its nonempty
reductions.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.Guests

open Mettapedia.GSLT
open Mettapedia.Logic.Relation (IsNormal)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves (check)
open Mettapedia.GSLT.LanguageDef.Authored
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles

variable {K : AuthoredCalculus}

/-! ## The check has exactly one result -/

/-- **Every state of the check reaches a state without step**: the check
terminates. -/
theorem exists_reaches_normal (state : Checking K) :
    ∃ final : Checking K, (checkerTheory K).Reaches (interface := PUnit.unit) state final ∧
      IsNormal (CheckStep K) final := by
  generalize size : pending K state = count
  induction count using Nat.strong_induction_on generalizing state with
  | _ count ih =>
      by_cases normal : IsNormal (CheckStep K) state
      · exact ⟨state, Relation.ReflTransGen.refl, normal⟩
      · have moves : ∃ next, CheckStep K state next := by
          by_contra none
          exact normal fun next step => none ⟨next, step⟩
        obtain ⟨next, step⟩ := moves
        have lowered := CheckStep.pending step
        obtain ⟨final, reaches, finalNormal⟩ := ih (pending K next) (by omega) next rfl
        exact ⟨final, Relation.ReflTransGen.head step reaches, finalNormal⟩

/-- The steps of the check are right unique. -/
theorem checkStep_rightUnique : Relator.RightUnique (CheckStep K) :=
  fun _ _ _ left right => left.deterministic right

/-- **A state reaches one state without step at most.** -/
theorem normal_unique {state first second : Checking K}
    (toFirst : (checkerTheory K).Reaches (interface := PUnit.unit) state first)
    (toSecond : (checkerTheory K).Reaches (interface := PUnit.unit) state second)
    (firstNormal : IsNormal (CheckStep K) first) (secondNormal : IsNormal (CheckStep K) second) :
    first = second := by
  rcases Relation.ReflTransGen.total_of_right_unique checkStep_rightUnique toFirst toSecond with
    forward | backward
  · exact (firstNormal.reflTransGen_eq forward).symm
  · exact secondNormal.reflTransGen_eq backward

/-- The accepting state has no step. -/
theorem nil_normal : IsNormal (CheckStep K) [] := not_checkStep_nil

/-! ## The sentence -/

/-- **A theory runs the check of an authored calculus**: a reading of the
states of the check as terms of the theory, with a nonempty reduction for
each step of the check. -/
structure RunsCheck (candidate : ContextTheory.{0}) (K : AuthoredCalculus) where
  /-- The interface at which the states are read. -/
  point : candidate.Interface
  /-- The term that a state is read as. -/
  image : Checking K → candidate.Term point
  /-- Each step of the check is a nonempty reduction of the candidate. -/
  simulates : ∀ {state next : Checking K}, CheckStep K state next →
    Relation.TransGen (candidate.rewrites (interface := point)) (image state) (image next)
  /-- The image of a state without step has no step. -/
  normal : ∀ {state : Checking K}, IsNormal (CheckStep K) state →
    IsNormal (candidate.rewrites (interface := point)) (image state)
  /-- The terms without step that an image reaches are one, up to the static
  equivalence. -/
  unique : ∀ {state : Checking K} {first second : candidate.Term point},
    candidate.Reaches (image state) first → candidate.Reaches (image state) second →
      IsNormal candidate.rewrites first → IsNormal candidate.rewrites second →
        (candidate.equations point).r first second
  /-- Only the accepting state is read as the image of the accepting state. -/
  accepting : ∀ {state : Checking K}, (candidate.equations point).r (image state) (image []) →
    state = []

/-- **A theory that is confluent up to its static equivalence has unique
terms without step among the reducts of a term.** -/
theorem normalForms_unique_of_confluentUpTo {candidate : ContextTheory.{0}}
    (confluent : candidate.ConfluentUpTo) {interface : candidate.Interface}
    {term first second : candidate.Term interface} (toFirst : candidate.Reaches term first)
    (toSecond : candidate.Reaches term second) (firstNormal : IsNormal candidate.rewrites first)
    (secondNormal : IsNormal candidate.rewrites second) :
    (candidate.equations interface).r first second := by
  obtain ⟨firstEnd, secondEnd, firstReaches, secondReaches, joined⟩ :=
    confluent term first second toFirst toSecond
  rw [firstNormal.reflTransGen_eq firstReaches, secondNormal.reflTransGen_eq secondReaches]
    at joined
  exact joined

namespace RunsCheck

variable {candidate : ContextTheory.{0}} (runs : RunsCheck candidate K)

/-- A reduction of the check is a reduction of the candidate between the
images. -/
theorem reaches {state final : Checking K}
    (reaches : (checkerTheory K).Reaches (interface := PUnit.unit) state final) :
    candidate.Reaches (runs.image state) (runs.image final) := by
  induction reaches with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact ih.trans (runs.simulates step).to_reflTransGen

/-- A term equivalent to a term without step has no step. -/
theorem normal_of_equivalent {interface : candidate.Interface}
    {term other : candidate.Term interface}
    (related : (candidate.equations interface).r term other)
    (normal : IsNormal candidate.rewrites other) : IsNormal candidate.rewrites term :=
  fun _ step =>
    let ⟨moved, movedStep, _⟩ := candidate.rewrites_resp_left related step
    normal moved movedStep

/-- **In a theory that runs the check, the image of a submitted certificate
reaches the image of the accepting state exactly when the shared checker
accepts the certificate.**  Reaching is up to the static equivalence. -/
theorem reaches_iff_check (goal : Pattern) (certificate : Certificate K) :
    (∃ final, candidate.Reaches (runs.image [(goal, certificate)]) final ∧
        (candidate.equations runs.point).r final (runs.image [])) ↔
      check K.definition K.family.evaluate goal certificate = true := by
  constructor
  · rintro ⟨final, toFinal, related⟩
    obtain ⟨result, toResult, resultNormal⟩ := exists_reaches_normal [(goal, certificate)]
    have finalNormal : IsNormal candidate.rewrites final :=
      normal_of_equivalent related (runs.normal nil_normal)
    have same := runs.unique toFinal (runs.reaches toResult) finalNormal (runs.normal resultNormal)
    have accepted : result = [] :=
      runs.accepting ((candidate.equations runs.point).iseqv.trans
        ((candidate.equations runs.point).iseqv.symm same) related)
    rw [accepted] at toResult
    exact (reaches_accepting_singleton_iff goal certificate).mp toResult
  · intro accepted
    exact ⟨runs.image [],
      runs.reaches ((reaches_accepting_singleton_iff goal certificate).mpr accepted),
      (candidate.equations runs.point).iseqv.refl _⟩

/-- **The image of some certificate of a judgment reaches the image of the
accepting state exactly when the judgment is derivable** from the rules and
the facts of the calculus. -/
theorem exists_reaches_iff_derivable (goal : Pattern) :
    (∃ (certificate : Certificate K) (final : candidate.Term runs.point),
        candidate.Reaches (runs.image [(goal, certificate)]) final ∧
          (candidate.equations runs.point).r final (runs.image [])) ↔
      K.Derivable goal := by
  rw [← K.accepts_iff goal]
  exact exists_congr fun certificate => runs.reaches_iff_check goal certificate

/-- A run of the check is a run of as many nonempty reductions of the
candidate. -/
theorem steps {count : Nat} {state final : Checking K}
    (steps : (checkerTheory K).Steps (interface := PUnit.unit) count state final) :
    candidate.nonemptyReduction.Steps (interface := runs.point) count (runs.image state)
      (runs.image final) :=
  ContextTheory.Steps.map (theory := checkerTheory K) (target := candidate.nonemptyReduction)
    (interface := PUnit.unit) (point := runs.point) runs.image (fun step => runs.simulates step)
    steps

end RunsCheck

/-- **A hosting map from the check gives the sentence**: one step for each
step. -/
def RunsCheck.ofHosting {candidate : ContextTheory.{0}}
    (map : ContextMap (checkerTheory K) candidate) (hosting : map.Hosting) :
    RunsCheck candidate K where
  point := map.interface PUnit.unit
  image := fun state => map.term (origin := PUnit.unit) state
  simulates := fun step =>
    .single (map.preservesRewrites_of_transitions hosting.preserves (interface := PUnit.unit) step)
  normal := fun {state} stateNormal next step => by
    obtain ⟨sourceNext, sourceStep, -⟩ :=
      map.reflectsRewrites_of_transitions hosting.reflects (interface := PUnit.unit) step
    exact stateNormal sourceNext sourceStep
  unique := fun {state first second} toFirst toSecond firstNormal secondNormal => by
    obtain ⟨firstSource, firstReaches, firstRelated⟩ :=
      map.reaches_reflect (interface := PUnit.unit)
        (map.reflectsRewrites_of_transitions hosting.reflects)
        ((candidate.equations _).iseqv.refl _) toFirst
    obtain ⟨secondSource, secondReaches, secondRelated⟩ :=
      map.reaches_reflect (interface := PUnit.unit)
        (map.reflectsRewrites_of_transitions hosting.reflects)
        ((candidate.equations _).iseqv.refl _) toSecond
    have firstSourceNormal : IsNormal (CheckStep K) firstSource := fun next step =>
      RunsCheck.normal_of_equivalent ((candidate.equations _).iseqv.symm firstRelated)
        firstNormal _
        (map.preservesRewrites_of_transitions hosting.preserves (interface := PUnit.unit) step)
    have secondSourceNormal : IsNormal (CheckStep K) secondSource := fun next step =>
      RunsCheck.normal_of_equivalent ((candidate.equations _).iseqv.symm secondRelated)
        secondNormal _
        (map.preservesRewrites_of_transitions hosting.preserves (interface := PUnit.unit) step)
    obtain rfl := normal_unique firstReaches secondReaches firstSourceNormal secondSourceNormal
    exact (candidate.equations _).iseqv.trans firstRelated
      ((candidate.equations _).iseqv.symm secondRelated)
  accepting := fun related =>
    map.reflectsEquations_of_faithful hosting.faithful (origin := PUnit.unit) related

/-- **Positive**: the check runs itself. -/
def RunsCheck.self (K : AuthoredCalculus) : RunsCheck (checkerTheory K) K :=
  RunsCheck.ofHosting (ContextMap.id (checkerTheory K)) (ContextMap.hosting_id (checkerTheory K))

/-- **Negative**: a theory whose rank is bounded runs no check that has a
longer run.  The rank bounds the nonempty reductions too. -/
theorem isEmpty_runsCheck_of_bounded {candidate : ContextTheory.{0}} (ranked : candidate.Rank)
    (bound : Nat)
    (bounded : ∀ {interface : candidate.Interface} (term : candidate.Term interface),
      ranked.rank term ≤ bound)
    {count : Nat} {state final : Checking K}
    (steps : (checkerTheory K).Steps (interface := PUnit.unit) count state final)
    (long : bound < count) : IsEmpty (RunsCheck candidate K) := by
  refine ⟨fun runs => ?_⟩
  have counted := ranked.nonempty.steps_le (runs.steps steps)
  have unfolded : count + ranked.rank (runs.image final) ≤ ranked.rank (runs.image state) :=
    counted
  have top := bounded (runs.image state)
  omega

#print axioms exists_reaches_normal
#print axioms normal_unique
#print axioms normalForms_unique_of_confluentUpTo
#print axioms RunsCheck.reaches_iff_check
#print axioms RunsCheck.exists_reaches_iff_derivable
#print axioms RunsCheck.steps
#print axioms RunsCheck.ofHosting
#print axioms RunsCheck.self
#print axioms isEmpty_runsCheck_of_bounded

end Mettapedia.Logic.HostingStyles.Guests
