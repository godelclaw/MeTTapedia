import Mettapedia.Logic.HostingStyles.ContextReadings.SeparateSort
import Mettapedia.Logic.HostingStyles.Guests.CertificateChecker

/-!
# The check of a certificate with its contexts

A state of a check is a list of obligations.  The contexts taken here are
the lists of obligations with named places (`OpenChecking`): filling puts a
state at each place, in the order of the list.  A place may occur once,
several times or not at all, as in the other theories of the library that are
given by a syntax with holes.  `checkerWithContexts K` is the check of the
certificates of an authored calculus with these contexts; on terms it is
`checkerTheory K` (`termsInclusion_hosting`).

This is one choice of contexts for a check.  Every statement about the check
on terms is independent of it.

## What a host of it has to have, whatever it computes

The check with its contexts discards (`checkerWithContexts_discards`) and has
the context that puts one state before another (`sequence`).  So the three
obstructions that the readings of a presentation meet apply to it, and none
of them is about how long the host runs.  Let the check have a step.

* **Linear**: into a theory with a linear size there is no map at all
  (`isEmpty_contextMap_checkerWithContexts`).
* **Regions**: a reading whose data does not reduce receives the check as
  data, and no map preserves its steps
  (`regions_not_preserves_checkerWithContexts`).
* **Cartesian**: a presentation that reduces in a sort that no constructor
  takes hosts it under no reading
  (`separateSort_not_hosting_checkerWithContexts`): the image of the sequence
  of two states that are being checked can use one of them at most.  Of the
  contexts of the check this argument uses the sequence alone, which uses each
  of its two places once.

The three hold together of every presentation whose static equivalence is
that of quotation and dropping, whose rewrites are headed by constructors of
processes and none of whose constructors takes a process
(`separateProcess_checkerWithContexts_row`).  Instances: the candidate
presentation (`probe_checkerWithContexts_row`) and the candidate with a run
constructor, **under every evaluator of its premises**
(`run_checkerWithContexts_row`).  On terms the second can run for any number
of steps under a suitable evaluator; with contexts it hosts no check that has
a step, because of where it reduces.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.Guests

open Mettapedia.GSLT
open Mettapedia.GSLT.Dedukti (HoleSyntax)
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)
open Mettapedia.GSLT.LanguageDef.Authored
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
  (language queryFirstCandidatePresentation)
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
open Mettapedia.Logic.HostingStyles.ContextReadings

variable (K : AuthoredCalculus)

/-! ## States with places -/

/-- **A state of a check with named places**: a list whose members are
obligations or places for further states. -/
abbrev OpenChecking (slots : Type) : Type := List (slots ⊕ (Pattern × Certificate K))

variable {K}

/-- Fill each place with a state. -/
def fillPlaces {slots : Type} (filling : slots → Checking K) (context : OpenChecking K slots) :
    Checking K :=
  context.flatMap (Sum.elim filling fun obligation => [obligation])

/-- Put a state with places at each place. -/
def bindPlaces {slots inner : Type} (plugged : slots → OpenChecking K inner)
    (context : OpenChecking K slots) : OpenChecking K inner :=
  context.flatMap (Sum.elim plugged fun obligation => [Sum.inr obligation])

@[simp] theorem fillPlaces_nil {slots : Type} (filling : slots → Checking K) :
    fillPlaces filling ([] : OpenChecking K slots) = [] :=
  rfl

@[simp] theorem fillPlaces_place {slots : Type} (filling : slots → Checking K) (slot : slots)
    (rest : OpenChecking K slots) :
    fillPlaces filling (Sum.inl slot :: rest) = filling slot ++ fillPlaces filling rest := by
  simp [fillPlaces]

@[simp] theorem fillPlaces_obligation {slots : Type} (filling : slots → Checking K)
    (obligation : Pattern × Certificate K) (rest : OpenChecking K slots) :
    fillPlaces filling (Sum.inr obligation :: rest) = obligation :: fillPlaces filling rest := by
  simp [fillPlaces]

theorem fillPlaces_append {slots : Type} (filling : slots → Checking K)
    (first second : OpenChecking K slots) :
    fillPlaces filling (first ++ second) =
      fillPlaces filling first ++ fillPlaces filling second := by
  simp [fillPlaces]

theorem fillPlaces_bindPlaces {slots inner : Type} (filling : inner → Checking K)
    (plugged : slots → OpenChecking K inner) (context : OpenChecking K slots) :
    fillPlaces filling (bindPlaces plugged context) =
      fillPlaces (fun slot => fillPlaces filling (plugged slot)) context := by
  induction context with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | inl slot =>
          rw [fillPlaces_place, ← ih]
          show fillPlaces filling (plugged slot ++ bindPlaces plugged tail) = _
          rw [fillPlaces_append]
      | inr obligation =>
          rw [fillPlaces_obligation, ← ih]
          show fillPlaces filling (Sum.inr obligation :: bindPlaces plugged tail) = _
          rw [fillPlaces_obligation]

theorem fillPlaces_constant {slots : Type} (filling : slots → Checking K) (state : Checking K) :
    fillPlaces filling (state.map Sum.inr) = state := by
  induction state with
  | nil => rfl
  | cons obligation rest ih => rw [List.map_cons, fillPlaces_obligation, ih]

variable (K)

/-- **The states of a check as a syntax with named places.** -/
def obligationSyntax : HoleSyntax (Checking K) where
  Hole := OpenChecking K
  fill := fun filling context => fillPlaces filling context
  bind := fun plugged context => bindPlaces plugged context
  hole := fun slot => [Sum.inl slot]
  constant := fun state => state.map Sum.inr
  fill_bind := fun filling plugged context => fillPlaces_bindPlaces filling plugged context
  fill_hole := fun filling slot => by
    rw [fillPlaces_place, fillPlaces_nil, List.append_nil]
  fill_constant := fun filling state => fillPlaces_constant filling state

/-- **The check of the certificates of an authored calculus, with its
contexts**: the states with named places. -/
def checkerWithContexts : ContextTheory.{0} :=
  (obligationSyntax K).theory ⟨Eq, eq_equivalence⟩ (CheckStep K)
    (fun {_} context {first second} same => by
      have equal : first = second := funext same
      rw [equal])
    (fun {state other next} same step => by
      cases same
      exact ⟨next, step, rfl⟩)
    (fun {state next other} step same => by
      cases same
      exact step)

/-- The context that returns what fills its first place. -/
def firstPlace : (checkerWithContexts K).Context (fun _ : Bool => ()) () :=
  ([Sum.inl false] : OpenChecking K Bool)

/-- **The sequence of two states**: what fills the first place, then what
fills the second. -/
def sequence : (checkerWithContexts K).Context (fun _ : Bool => ()) () :=
  ([Sum.inl false, Sum.inl true] : OpenChecking K Bool)

@[simp] theorem fill_firstPlace (filling : Bool → Checking K) :
    (checkerWithContexts K).fill (firstPlace K) filling = filling false := by
  show fillPlaces filling [Sum.inl false] = filling false
  rw [fillPlaces_place, fillPlaces_nil, List.append_nil]

@[simp] theorem fill_sequence (filling : Bool → Checking K) :
    (checkerWithContexts K).fill (sequence K) filling = filling false ++ filling true := by
  show fillPlaces filling [Sum.inl false, Sum.inl true] = filling false ++ filling true
  rw [fillPlaces_place, fillPlaces_place, fillPlaces_nil, List.append_nil]

/-- **The check with its contexts discards.** -/
theorem checkerWithContexts_discards : (checkerWithContexts K).Discards () :=
  ⟨firstPlace K, fun filling => fill_firstPlace K filling⟩

/-- **Negative**, for the contexts: the check given by its terms alone does
not discard; it has no context of two holes. -/
theorem checkerTheory_not_discards : ¬ (checkerTheory K).Discards PUnit.unit :=
  GSLT.termsAlone_not_discards (certificateChecker K) PUnit.unit

/-- The states of the check, among the states with places: the identity on
terms. -/
def termsInclusion : ContextMap (checkerTheory K) (checkerWithContexts K) :=
  ContextMap.ofTerms (source := certificateChecker K) (target := checkerWithContexts K) ()
    (fun state => state) (fun same => same)

/-- **On terms the check with its contexts is the check**: the inclusion is
hosting.  So a host of the first is a host of the second. -/
theorem termsInclusion_hosting : (termsInclusion K).Hosting :=
  (ContextMap.ofTerms_hosting_iff (source := certificateChecker K)
    (target := checkerWithContexts K) () (fun state => state) (fun same => same)).mpr
    ⟨fun _ _ same => same, fun _ _ step => step, fun _ next step => ⟨next, step, rfl⟩⟩

/-- A host of the check with its contexts hosts the check on terms. -/
theorem hostedBy_checkerTheory_of_withContexts {candidate : ContextTheory.{0}}
    (hosted : HostedBy (checkerWithContexts K) candidate) : HostedBy (checkerTheory K) candidate :=
  HostedBy.trans ⟨termsInclusion K, termsInclusion_hosting K⟩ hosted

/-! ## The three obstructions, for a check that has a step -/

variable {K}

/-- **Linear**: no map of theories goes from the check with its contexts into
a theory whose contexts have a linear size. -/
theorem isEmpty_contextMap_checkerWithContexts {target : ContextTheory.{0}}
    (sized : target.LinearSize) : IsEmpty (ContextMap (checkerWithContexts K) target) :=
  sized.isEmpty_contextMap_of_discards (checkerWithContexts_discards K) ⟨([] : Checking K)⟩

/-- **Regions**: a reading of a presentation whose data does not reduce
receives the check as data; no map preserves a step of the check. -/
theorem regions_not_preserves_checkerWithContexts {base : BasePremiseEvaluator}
    {presentation : ValidatedLanguageDef} (kept : KeptWeight base presentation.language)
    {data active : List String} (headed : rewritesHeadedIn presentation.language active = true)
    (apart : ∀ sort ∈ data, sort ∉ active)
    (map : ContextMap (checkerWithContexts K)
      ((contextTheory base presentation).regionReading (ofSorts data)))
    {state next : Checking K} (step : CheckStep K state next) : ¬ map.PreservesTransitions :=
  kept.regions_not_preserves headed apart map (checkerWithContexts_discards K) (interface := ())
    (term := state) (next := next) step

/-- **Cartesian, and every other reading**: a presentation that reduces in a
sort that no constructor takes hosts the check with its contexts under no
reading, as soon as the check has a step.  The image of the sequence of two
states uses one of its two places at most. -/
theorem separateSort_not_hosting_checkerWithContexts {base : BasePremiseEvaluator}
    {presentation : ValidatedLanguageDef} {active : String}
    (headed : rewritesHeadedIn presentation.language [active] = true)
    (closed : takesNoneOf presentation.language active = true)
    (keeps : ∀ {interface : Contexts.Interface}
      {first second : Contexts.Term presentation.language interface},
      (termSetoid base presentation.language interface).r first second →
        tokens (sortLabels presentation.language active) first.1 =
          tokens (sortLabels presentation.language active) second.1)
    {declared : Contexts.Interface → Prop}
    (map : ContextMap (checkerWithContexts K)
      ((contextTheory base presentation).regionReading declared))
    {state next : Checking K} (step : CheckStep K state next) : ¬ map.Hosting := by
  have nonempty : state ≠ [] := fun empty => not_checkStep_nil next (empty ▸ step)
  refine not_hosting_of_separateSort headed closed keeps map (sequence K) (interface := ())
    (moving := state) (next := next) (still := []) (other := state) step ?_ ?_
  · intro same
    have unfolded : @Eq (Checking K) (state ++ []) (state ++ state) :=
      (fill_sequence K (fun index : Bool => bif index then ([] : Checking K) else state)).symm.trans
        (Eq.trans same (fill_sequence K (fun index : Bool => bif index then state else state)))
    exact nonempty (List.append_cancel_left unfolded).symm
  · intro same
    have unfolded : @Eq (Checking K) ([] ++ state) (state ++ state) :=
      (fill_sequence K (fun index : Bool => bif index then state else ([] : Checking K))).symm.trans
        (Eq.trans same (fill_sequence K (fun index : Bool => bif index then state else state)))
    exact nonempty (List.append_cancel_right unfolded).symm

/-! ## Presentations that reduce in the sort of processes alone -/

/-- **The three cells, for every presentation of this shape**: its static
equivalence is that of quotation and dropping, its rewrites are headed by
constructors of processes, and no constructor takes a process.  For a check
that has a step and every evaluator of the premises: no map at all with the
contexts as they are; no map that preserves steps under the reading in which
atoms and names are data; no hosting map under any reading. -/
theorem separateProcess_checkerWithContexts_row {base : BasePremiseEvaluator}
    {presentation : ValidatedLanguageDef} (only : QuoteDropOnly presentation.language)
    (headed : rewritesHeadedIn presentation.language ["Process"] = true)
    (closed : takesNoneOf presentation.language "Process" = true)
    (quote : sortLabels presentation.language "Process" "prime-quote" = false)
    (drop : sortLabels presentation.language "Process" "prime-drop" = false)
    {state next : Checking K} (step : CheckStep K state next) :
    IsEmpty (ContextMap (checkerWithContexts K) (contextTheory base presentation)) ∧
      (∀ map : ContextMap (checkerWithContexts K)
          ((contextTheory base presentation).regionReading probeData),
        ¬ map.PreservesTransitions) ∧
      ∀ (declared : Contexts.Interface → Prop)
        (map : ContextMap (checkerWithContexts K)
          ((contextTheory base presentation).regionReading declared)), ¬ map.Hosting :=
  ⟨isEmpty_contextMap_checkerWithContexts (QuoteDropOnly.linearSize presentation only base),
    fun map => regions_not_preserves_checkerWithContexts (presentation := presentation)
      (only.keptWeight base) (data := ["Atom", "CandidateName"]) (active := ["Process"]) headed
      (by decide) map step,
    fun _ map => separateSort_not_hosting_checkerWithContexts (presentation := presentation)
      (active := "Process") headed closed (fun related => only.tokens_eq quote drop related) map
      step⟩

/-! ## The candidate presentation, and the candidate with a run constructor -/

/-- Quotation and dropping are not constructors of processes of the candidate
presentation. -/
theorem language_quote_not_process :
    sortLabels language "Process" "prime-quote" = false ∧
      sortLabels language "Process" "prime-drop" = false := by
  decide

/-- **The candidate presentation and the check with its contexts**, for a
check that has a step and every evaluator: no map at all under the linear
reading; no map that preserves steps under the reading with regions; no
hosting map under any reading, the cartesian one among them.  None of the
three reasons is the length of the runs of the candidate. -/
theorem probe_checkerWithContexts_row (base : BasePremiseEvaluator) {state next : Checking K}
    (step : CheckStep K state next) :
    IsEmpty (ContextMap (checkerWithContexts K) (presentedReading base)) ∧
      (∀ map : ContextMap (checkerWithContexts K) (regionProbe base),
        ¬ map.PreservesTransitions) ∧
      ∀ (declared : Contexts.Interface → Prop)
        (map : ContextMap (checkerWithContexts K) ((presentedReading base).regionReading declared)),
        ¬ map.Hosting :=
  separateProcess_checkerWithContexts_row (presentation := queryFirstCandidatePresentation)
    language_quoteDropOnly language_headedIn_process language_takesNoneOf_process
    language_quote_not_process.1 language_quote_not_process.2 step

/-- **The candidate with a run constructor and the check with its contexts**,
under every evaluator of its premises: the same three cells.  On terms this
presentation can run for any number of steps under a suitable evaluator; with
contexts it hosts no check that has a step. -/
theorem run_checkerWithContexts_row (base : BasePremiseEvaluator) {state next : Checking K}
    (step : CheckStep K state next) :
    IsEmpty (ContextMap (checkerWithContexts K) (contextTheory base runPresentation)) ∧
      (∀ map : ContextMap (checkerWithContexts K) (regionRun base),
        ¬ map.PreservesTransitions) ∧
      ∀ (declared : Contexts.Interface → Prop)
        (map : ContextMap (checkerWithContexts K)
          ((contextTheory base runPresentation).regionReading declared)), ¬ map.Hosting :=
  separateProcess_checkerWithContexts_row (presentation := runPresentation)
    probeWithRun_quoteDropOnly probeWithRun_headedIn_process probeWithRun_takesNoneOf_process
    probeWithRun_quote_not_process.1 probeWithRun_quote_not_process.2 step

#print axioms fillPlaces_bindPlaces
#print axioms obligationSyntax
#print axioms checkerWithContexts
#print axioms checkerWithContexts_discards
#print axioms checkerTheory_not_discards
#print axioms termsInclusion_hosting
#print axioms hostedBy_checkerTheory_of_withContexts
#print axioms isEmpty_contextMap_checkerWithContexts
#print axioms regions_not_preserves_checkerWithContexts
#print axioms separateSort_not_hosting_checkerWithContexts
#print axioms separateProcess_checkerWithContexts_row
#print axioms probe_checkerWithContexts_row
#print axioms run_checkerWithContexts_row

end Mettapedia.Logic.HostingStyles.Guests
