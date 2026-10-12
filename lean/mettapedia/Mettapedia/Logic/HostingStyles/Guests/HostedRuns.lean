import Mettapedia.Logic.HostingStyles.ContextReadings.ProbeReadings

/-!
# Runs under a hosting map, and the length of the runs of the candidate

Two general facts about maps of theories, and their instance at the candidate
presentation.

* **A hosting map preserves and reflects reachability between images**, up to
  the static equivalence (`ContextMap.Hosting.reaches_image_iff`): the image of
  a term reaches the image of another exactly when the term reaches the
  other.  The direction from the host to the source needs the reflection of
  steps and of the static equivalence (`ContextMap.reaches_of_reaches_image`);
  the other direction needs the preservation of steps only.  This is what a
  hosting map buys for a source that decides something by reaching a state.
* A run of `count` steps is a reduction (`ContextTheory.Steps.reaches`), and a
  reduction is a run of some number of steps
  (`ContextTheory.reaches_iff_exists_steps`).  A measure that every step
  lowers by exactly one counts the steps of a run
  (`ContextTheory.Steps.counted`).

**The candidate presentation preserves no run of more than three steps**,
under any evaluator of its premises and under each of its readings
(`presented_not_preserves_of_steps`, `reading_not_preserves_of_steps`): its
rank is at most three, and a reading has the terms and the steps of the
theory.  So a theory with such a run is hosted by none of them
(`not_hostedBy_presented_of_steps`, `not_hostedBy_reading_of_steps`).  Unlike
the argument from a cyclic reduction, this applies to sources that terminate.
Three steps are attained by the candidate (existing `probe_steps_three`), so
the bound of the statement cannot be lowered.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT

universe u

namespace ContextTheory

variable {theory : ContextTheory.{u}}

/-- A run of a number of steps is a reduction. -/
theorem Steps.reaches {interface : theory.Interface} {count : Nat}
    {term final : theory.Term interface} (steps : theory.Steps count term final) :
    theory.Reaches term final := by
  induction steps with
  | zero term => exact .refl
  | succ step _ ih => exact Relation.ReflTransGen.head step ih

/-- **A reduction is a run of some number of steps.** -/
theorem reaches_iff_exists_steps {interface : theory.Interface}
    (term final : theory.Term interface) :
    theory.Reaches term final ↔ ∃ count, theory.Steps count term final := by
  constructor
  · intro reaches
    induction reaches using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨0, .zero _⟩
    | head step _ ih =>
        obtain ⟨count, steps⟩ := ih
        exact ⟨count + 1, .succ step steps⟩
  · rintro ⟨count, steps⟩
    exact steps.reaches

/-- **A measure that every step lowers by exactly one counts the steps of a
run.** -/
theorem Steps.counted {interface : theory.Interface} (measure : theory.Term interface → Nat)
    (lowers : ∀ {term next : theory.Term interface}, theory.rewrites term next →
      measure term = measure next + 1)
    {count : Nat} {term final : theory.Term interface} (steps : theory.Steps count term final) :
    measure term = measure final + count := by
  induction steps with
  | zero term => rfl
  | succ step _ ih =>
      have lowered := lowers step
      omega

/-- **A function on terms that sends each step to a step sends a run to a run
of as many steps.** -/
theorem Steps.map {target : ContextTheory.{u}} {interface : theory.Interface}
    {point : target.Interface} (image : theory.Term interface → target.Term point)
    (preserves : ∀ {term next : theory.Term interface}, theory.rewrites term next →
      target.rewrites (image term) (image next))
    {count : Nat} {term final : theory.Term interface} (steps : theory.Steps count term final) :
    target.Steps count (image term) (image final) := by
  induction steps with
  | zero term => exact .zero _
  | succ step _ ih => exact .succ (preserves step) ih

/-- **A property that every step carries back from its end holds at the start
of every run that ends in it.** -/
theorem Steps.carry_back {interface : theory.Interface} (property : theory.Term interface → Prop)
    (back : ∀ {term next : theory.Term interface}, theory.rewrites term next →
      property next → property term)
    {count : Nat} {term final : theory.Term interface} (steps : theory.Steps count term final)
    (holds : property final) : property term := by
  induction steps with
  | zero term => exact holds
  | succ step _ ih => exact back step (ih holds)

end ContextTheory

namespace ContextMap

variable {source target : ContextTheory.{u}} {map : ContextMap source target}

/-- **What reflection buys**: when the image of a term reaches a term
equivalent to the image of another, the term reaches a term equivalent to the
other.  Reflection of steps and of the static equivalence is all that is
used. -/
theorem reaches_of_reaches_image (reflects : map.ReflectsTransitions)
    (reflectsEquations : map.ReflectsEquations) {interface : source.Interface}
    {start accept : source.Term interface} {final : target.Term (map.interface interface)}
    (reaches : target.Reaches (map.term start) final)
    (related : (target.equations (map.interface interface)).r final (map.term accept)) :
    ∃ sourceFinal, source.Reaches start sourceFinal ∧
      (source.equations interface).r sourceFinal accept := by
  obtain ⟨sourceFinal, sourceReaches, lifted⟩ :=
    map.reaches_reflect (map.reflectsRewrites_of_transitions reflects)
      ((target.equations _).iseqv.refl _) reaches
  exact ⟨sourceFinal, sourceReaches, reflectsEquations
    ((target.equations _).iseqv.trans ((target.equations _).iseqv.symm lifted) related)⟩

/-- **A hosting map preserves and reflects reachability between images**, up
to the static equivalence at the end. -/
theorem Hosting.reaches_image_iff (hosting : map.Hosting) {interface : source.Interface}
    (start accept : source.Term interface) :
    (∃ final, target.Reaches (map.term start) final ∧
        (target.equations (map.interface interface)).r final (map.term accept)) ↔
      ∃ final, source.Reaches start final ∧ (source.equations interface).r final accept := by
  constructor
  · rintro ⟨final, reaches, related⟩
    exact map.reaches_of_reaches_image hosting.reflects
      (map.reflectsEquations_of_faithful hosting.faithful) reaches related
  · rintro ⟨final, reaches, related⟩
    exact ⟨map.term final,
      map.reaches_of_preserves (map.preservesRewrites_of_transitions hosting.preserves) reaches,
      map.term_resp related⟩

end ContextMap

end Mettapedia.GSLT

namespace Mettapedia.Logic.HostingStyles.Guests

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)
open Mettapedia.Logic.HostingStyles.PrimeCandidate
open Mettapedia.Logic.HostingStyles.ContextReadings

/-- **Under the linear reading the candidate preserves no run of more than
three steps**, for any evaluator of its premises. -/
theorem presented_not_preserves_of_steps (base : BasePremiseEvaluator) {source : ContextTheory.{0}}
    (map : ContextMap source (presentedReading base)) {interface : source.Interface} {count : Nat}
    {term final : source.Term interface} (steps : source.Steps count term final)
    (long : 3 < count) : ¬ map.PreservesTransitions :=
  map.not_preserves_of_steps (probeRank base) (fun term => probeRank_le base term) steps long

/-- **Nor under any of its readings**: the reading with regions, for every
class of declared interfaces, and the cartesian reading among them. -/
theorem reading_not_preserves_of_steps (base : BasePremiseEvaluator)
    (declared : Contexts.Interface → Prop) {source : ContextTheory.{0}}
    (map : ContextMap source ((presentedReading base).regionReading declared))
    {interface : source.Interface} {count : Nat} {term final : source.Term interface}
    (steps : source.Steps count term final) (long : 3 < count) : ¬ map.PreservesTransitions :=
  map.not_preserves_of_steps ((probeRank base).regionReading declared)
    (fun term => probeRank_le base term) steps long

/-- **A theory with a run of more than three steps is not hosted by the
candidate under the linear reading.** -/
theorem not_hostedBy_presented_of_steps (base : BasePremiseEvaluator) {source : ContextTheory.{0}}
    {interface : source.Interface} {count : Nat} {term final : source.Term interface}
    (steps : source.Steps count term final) (long : 3 < count) :
    ¬ HostedBy source (presentedReading base) :=
  fun ⟨map, hosting⟩ => presented_not_preserves_of_steps base map steps long hosting.preserves

/-- **Nor under any of its readings.** -/
theorem not_hostedBy_reading_of_steps (base : BasePremiseEvaluator)
    (declared : Contexts.Interface → Prop) {source : ContextTheory.{0}}
    {interface : source.Interface} {count : Nat} {term final : source.Term interface}
    (steps : source.Steps count term final) (long : 3 < count) :
    ¬ HostedBy source ((presentedReading base).regionReading declared) :=
  fun ⟨map, hosting⟩ =>
    reading_not_preserves_of_steps base declared map steps long hosting.preserves

/-- **Negative**, for the bound: a run of three steps is preserved by the
identity of the candidate under the answering evaluator, so three cannot be
lowered. -/
theorem presented_preserves_steps_three :
    ∃ (map : ContextMap (presentedReading answeringEvaluator)
        (presentedReading answeringEvaluator))
      (interface : (presentedReading answeringEvaluator).Interface)
      (term final : (presentedReading answeringEvaluator).Term interface),
      map.PreservesTransitions ∧ (presentedReading answeringEvaluator).Steps 3 term final :=
  ⟨ContextMap.id _, _, _, _, ContextMap.preservesTransitions_id _, probe_steps_three⟩

#print axioms ContextTheory.Steps.reaches
#print axioms ContextTheory.reaches_iff_exists_steps
#print axioms ContextTheory.Steps.counted
#print axioms ContextTheory.Steps.carry_back
#print axioms ContextTheory.Steps.map
#print axioms ContextMap.reaches_of_reaches_image
#print axioms ContextMap.Hosting.reaches_image_iff
#print axioms presented_not_preserves_of_steps
#print axioms reading_not_preserves_of_steps
#print axioms not_hostedBy_presented_of_steps
#print axioms not_hostedBy_reading_of_steps
#print axioms presented_preserves_steps_three

end Mettapedia.Logic.HostingStyles.Guests
