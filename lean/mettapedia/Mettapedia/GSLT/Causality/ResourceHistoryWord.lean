import Mettapedia.GSLT.Causality.ResourceRuns
import Mettapedia.Machines.TraceObservationBoundary
import Mettapedia.GSLT.Distinction.CausalGluing
import Mettapedia.Languages.MeTTa.OSLFCore.Atom

/-!
# Complete resource histories are determined by their firing words

For a fixed resource system and initial marking, an ordered word of actual
instances determines every intermediate marking and the complete occurrence
path. No endpoint-only observation has this property in general.

`System.replayWord` checks one supplied word from a supplied marking. The
marking is replay data, not native authority and not a WorldStep realization.
The causal observation of a recovered path is `Trace.mk` on
`System.concurrency.tiles`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction

open OccurrenceHistory
open Mettapedia.GSLT.Causality.EventConcurrency

universe uRes uRule

variable {R : Type uRes} (S : System.{uRes, uRule} R) [DecidableEq R]

def occurrenceEntry {source target : Multiset R}
    (occurrence : Occurrence S.presentation source target) : S.Entry :=
  ⟨occurrence.site, occurrence.evidence.val⟩

theorem occurrenceEntry_determines {source target target' : Multiset R}
    (first : Occurrence S.presentation source target)
    (second : Occurrence S.presentation source target')
    (same : occurrenceEntry S first = occurrenceEntry S second) :
    target = target' ∧ HEq first second := by
  rcases first with ⟨site, ⟨firing, enabled, endpoint⟩⟩
  rcases second with ⟨site', ⟨firing', enabled', endpoint'⟩⟩
  obtain ⟨sites, instances⟩ := Sigma.mk.inj_iff.mp same
  change site = site' at sites
  change HEq firing firing' at instances
  subst site'
  have equal : firing = firing' := eq_of_heq instances
  subst firing'
  have targets : target = target' := endpoint.trans endpoint'.symm
  refine ⟨targets, ?_⟩
  cases targets
  rfl

theorem pathEntries_determines : ∀ {source target target' : Multiset R}
    (first : OccurrencePath S.presentation source target)
    (second : OccurrencePath S.presentation source target'),
    S.pathEntries first = S.pathEntries second → target = target' ∧ HEq first second
  | _, _, _, .refl _, .refl _, _ => ⟨rfl, HEq.rfl⟩
  | _, _, _, .refl _, .cons _ _, same => by cases same
  | _, _, _, .cons _ _, .refl _, same => by cases same
  | _, _, _, .cons occurrence rest, .cons occurrence' rest', same => by
      obtain ⟨head, tail⟩ := List.cons.inj same
      obtain ⟨middle, sameOccurrence⟩ := occurrenceEntry_determines S occurrence occurrence' head
      subst middle
      have equalOccurrence : occurrence = occurrence' := eq_of_heq sameOccurrence
      subst occurrence'
      obtain ⟨last, sameRest⟩ := pathEntries_determines rest rest' tail
      subst last
      have equalRest : rest = rest' := eq_of_heq sameRest
      subst rest'
      exact ⟨rfl, HEq.rfl⟩

theorem pathEntries_injective {source target : Multiset R} :
    Function.Injective (S.pathEntries (M := source) (N := target)) := by
  intro first second same
  exact eq_of_heq (pathEntries_determines S first second same).2

theorem pathEntries_determines_from {source source' target target' : Multiset R}
    (sources : source = source')
    (first : OccurrencePath S.presentation source target)
    (second : OccurrencePath S.presentation source' target')
    (same : S.pathEntries first = S.pathEntries second) : target = target' ∧ HEq first second := by
  cases sources
  exact pathEntries_determines S first second same

namespace System

/-- Sites of a resource path, in firing order, are the sites of its word. -/
theorem sites_eq_entries : ∀ {source target : Multiset R}
    (path : OccurrencePath S.presentation source target),
    OccurrencePath.sites path = (S.pathEntries path).map Sigma.fst
  | _, _, .refl _ => rfl
  | _, _, .cons occurrence rest => by
      exact congrArg (occurrence.site :: ·) (sites_eq_entries rest)

theorem pathEntries_cast {source target target' : Multiset R} (same : target = target')
    (path : OccurrencePath S.presentation source target) :
    S.pathEntries (same ▸ path) = S.pathEntries path := by
  cases same
  rfl

theorem instanceValuation_onPath_cast {A : Type*} [AddCommMonoid A]
    (grade : ∀ {site : S.Site}, S.Instance site → A) {source target target' : Multiset R}
    (same : target = target') (path : OccurrencePath S.presentation source target) :
    (S.instanceValuation grade).onPath (same ▸ path) =
      (S.instanceValuation grade).onPath path := by
  cases same
  rfl

/-- Two firings and a stop: the instance grade is the sum of the two instances. -/
theorem instanceValuation_two {A : Type*} [AddCommMonoid A]
    (grade : ∀ {site : S.Site}, S.Instance site → A) {source middle target : Multiset R}
    (first : Occurrence S.presentation source middle)
    (second : Occurrence S.presentation middle target) :
    (S.instanceValuation grade).onPath
        (.cons first (.cons second (.refl (P := S.presentation) target))) =
      grade first.evidence.val + grade second.evidence.val := by
  calc
    (S.instanceValuation grade).onPath
          (.cons first (.cons second (.refl (P := S.presentation) target)))
        = grade first.evidence.val + (grade second.evidence.val + 0) := rfl
    _ = grade first.evidence.val + grade second.evidence.val := by rw [add_zero]

/-! ## Replaying one firing word

The catalogue explorer enumerates maximal runs and does not tell copies apart.
`ResourceFrontier.follow` is one chain entry. This checker takes one finite
word and one supplied initial marking, checks `Enables` at each step, and
returns that occurrence path or refuses the next consume. An entry is its site
and instance. Action text and a row index are not the word. Duplicate entries
stay duplicate entries. The residual of a tile keeps the instance. -/

def replayWord (word : List S.Entry) (source : Multiset R) :
    Option (Σ target : Multiset R, OccurrencePath S.presentation source target) :=
  match word with
  | [] => some ⟨source, .refl (P := S.presentation) source⟩
  | entry :: rest =>
      match flag : S.enabledB source entry with
      | false => none
      | true =>
          match replayWord rest (S.fire source entry.2) with
          | none => none
          | some continued =>
              some ⟨continued.1,
                .cons ⟨entry.1, ⟨entry.2, (S.enabledB_iff source entry).mp flag, rfl⟩⟩
                  continued.2⟩

theorem replayWord_nil (source : Multiset R) :
    S.replayWord [] source = some ⟨source, .refl (P := S.presentation) source⟩ := rfl

theorem replayWord_cons_disabled (entry : S.Entry) (rest : List S.Entry) (source : Multiset R)
    (disabled : S.enabledB source entry = false) :
    S.replayWord (entry :: rest) source = none := by
  unfold replayWord
  split
  · rfl
  · next flag => exact nomatch (disabled.symm.trans flag)

theorem replayWord_cons_enabled (entry : S.Entry) (rest : List S.Entry) (source : Multiset R)
    (enabled : S.enabledB source entry = true) :
    S.replayWord (entry :: rest) source =
      (S.replayWord rest (S.fire source entry.2)).map fun continued =>
        ⟨continued.1,
          .cons ⟨entry.1, ⟨entry.2, (S.enabledB_iff source entry).mp enabled, rfl⟩⟩
            continued.2⟩ := by
  conv =>
    lhs
    unfold replayWord
  split
  · next flag => exact nomatch (flag.symm.trans enabled)
  · cases S.replayWord rest (S.fire source entry.2) <;> rfl

/-- A successful replay returns the supplied word, duplicates included. -/
theorem replayWord_entries : ∀ (word : List S.Entry) (source : Multiset R)
    (recovered : Σ target : Multiset R, OccurrencePath S.presentation source target),
    S.replayWord word source = some recovered → S.pathEntries recovered.2 = word
  | [], source, recovered, replayed => by
      rw [replayWord_nil] at replayed
      cases replayed
      rfl
  | entry :: rest, source, recovered, replayed => by
      cases flag : S.enabledB source entry with
      | false =>
          rw [S.replayWord_cons_disabled entry rest source flag] at replayed
          cases replayed
      | true =>
          rw [S.replayWord_cons_enabled entry rest source flag] at replayed
          cases continued : S.replayWord rest (S.fire source entry.2) with
          | none =>
              rw [continued] at replayed
              cases replayed
          | some tail =>
              rw [continued] at replayed
              cases replayed
              exact congrArg (entry :: ·)
                (replayWord_entries rest (S.fire source entry.2) tail continued)

/-- A successful replay is a firing from the supplied marking. -/
theorem replayWord_sound (word : List S.Entry) (source : Multiset R)
    (recovered : Σ target : Multiset R, OccurrencePath S.presentation source target)
    (replayed : S.replayWord word source = some recovered) :
    S.Fires word source recovered.1 := by
  have fires := S.fires_pathEntries recovered.2
  rw [S.replayWord_entries word source recovered replayed] at fires
  exact fires

/-- Every firing word is recovered, at the marking where it ends. -/
theorem replayWord_complete : ∀ (word : List S.Entry) {source target : Multiset R},
    S.Fires word source target →
      ∃ path : OccurrencePath S.presentation source target,
        S.replayWord word source = some ⟨target, path⟩ ∧ S.pathEntries path = word
  | [], marking, finished, fires => by
      change finished = marking at fires
      cases fires
      exact ⟨.refl (P := S.presentation) _, rfl, rfl⟩
  | entry :: rest, source, target, ⟨enabled, restFires⟩ => by
      obtain ⟨tail, replayed, entries⟩ := replayWord_complete rest restFires
      have flag : S.enabledB source entry = true := (S.enabledB_iff source entry).mpr enabled
      refine ⟨.cons ⟨entry.1, ⟨entry.2, (S.enabledB_iff source entry).mp flag, rfl⟩⟩ tail, ?_, ?_⟩
      · rw [S.replayWord_cons_enabled entry rest source flag, replayed]
        rfl
      · exact congrArg (entry :: ·) entries

/-- The checker returns the path it was given, not another path with the same word. -/
theorem replayWord_of_path {source target : Multiset R}
    (path : OccurrencePath S.presentation source target) :
    S.replayWord (S.pathEntries path) source = some ⟨target, path⟩ := by
  obtain ⟨recovered, replayed, entries⟩ :=
    S.replayWord_complete (S.pathEntries path) (S.fires_pathEntries path)
  have determined := pathEntries_determines S recovered path entries
  cases determined.1
  have eqPath : recovered = path := eq_of_heq determined.2
  subst eqPath
  exact replayed

/-- Replaying a concatenation is replaying each part and appending the paths. -/
theorem replayWord_append : ∀ (earlier later : List S.Entry) (source : Multiset R),
    S.replayWord (earlier ++ later) source =
      (S.replayWord earlier source).bind fun leftPath =>
        (S.replayWord later leftPath.1).map fun rightPath =>
          ⟨rightPath.1, leftPath.2.append rightPath.2⟩
  | [], later, source => by
      change S.replayWord later source =
        (S.replayWord later source).map (fun p => ⟨p.1, p.2⟩)
      cases S.replayWord later source <;> rfl
  | entry :: rest, later, source => by
      change S.replayWord (entry :: (rest ++ later)) source = _
      cases flag : S.enabledB source entry with
      | false =>
          rw [S.replayWord_cons_disabled entry (rest ++ later) source flag,
              S.replayWord_cons_disabled entry rest source flag]
          rfl
      | true =>
          rw [S.replayWord_cons_enabled entry (rest ++ later) source flag,
              S.replayWord_cons_enabled entry rest source flag,
              replayWord_append rest later (S.fire source entry.2)]
          cases first : S.replayWord rest (S.fire source entry.2) with
          | none => rfl
          | some p =>
              dsimp only [Option.bind, Option.map]
              cases S.replayWord later p.1 <;> rfl

/-- The causal observation of a recovered path. Endpoints stay on the path. -/
def causalReadout {source target : Multiset R}
    (path : OccurrencePath S.presentation source target) :
    EventConcurrency.Trace S.concurrency.tiles source target :=
  EventConcurrency.Trace.mk (T := S.concurrency.tiles) path

/-- An instance grade agrees on the two routes of every residual tile. -/
theorem instanceObservation_descends {A : Type*} [AddCommMonoid A]
    (grade : ∀ {site : S.Site}, S.Instance site → A) :
    Descends S.concurrency.tiles (S.instanceValuation grade) := by
  refine (descends_iff_tiles S.concurrency.tiles (S.instanceValuation grade)).2 ?_
  intro source pair
  change S.concurrency.Pair source at pair
  change (S.instanceValuation grade).onPath (pair.route S.concurrency) =
    (S.instanceValuation grade).onPath (pair.swapped S.concurrency)
  let alternate : OccurrencePath S.presentation source
      (S.concurrency.residual (S.concurrency.symm pair.independent)).target :=
    .cons (EventConcurrency.Concurrency.occ pair.second)
      (.cons (EventConcurrency.Concurrency.occ
        (S.concurrency.residual (S.concurrency.symm pair.independent))) (.refl _))
  have castLaw := S.instanceValuation_onPath_cast grade
    (S.concurrency.close pair.independent).symm alternate
  change (S.instanceValuation grade).onPath (pair.swapped S.concurrency) =
    (S.instanceValuation grade).onPath alternate at castLaw
  refine Eq.trans ?_ castLaw.symm
  change grade pair.first.evidence.val + (grade pair.second.evidence.val + 0) =
    grade pair.second.evidence.val + (grade pair.first.evidence.val + 0)
  simp only [add_zero, add_comm]

/-- Replayed concatenation is the target of the suffix together with the
composite trace. The two sigma targets are compared as one record. -/
theorem causalReadout_append (earlier later : List S.Entry) (source : Multiset R)
    (joined : Σ target : Multiset R, OccurrencePath S.presentation source target)
    (leftPath : Σ middle : Multiset R, OccurrencePath S.presentation source middle)
    (rightPath : Σ target : Multiset R, OccurrencePath S.presentation leftPath.1 target)
    (hjoined : S.replayWord (earlier ++ later) source = some joined)
    (hleft : S.replayWord earlier source = some leftPath)
    (hright : S.replayWord later leftPath.1 = some rightPath) :
    (⟨joined.1, S.causalReadout joined.2⟩ :
        Σ target : Multiset R, EventConcurrency.Trace S.concurrency.tiles source target) =
      ⟨rightPath.1,
        EventConcurrency.Trace.append (S.causalReadout leftPath.2)
          (S.causalReadout rightPath.2)⟩ := by
  have Happ := S.replayWord_append earlier later source
  rw [hjoined, hleft] at Happ
  change some joined =
    (S.replayWord later leftPath.1).map fun step =>
      ⟨step.1, leftPath.2.append step.2⟩ at Happ
  rw [hright] at Happ
  cases Happ
  exact congrArg (fun trace => (⟨rightPath.1, trace⟩ :
      Σ target : Multiset R, EventConcurrency.Trace S.concurrency.tiles source target))
    (EventConcurrency.Trace.append_mk (T := S.concurrency.tiles) leftPath.2 rightPath.2).symm

/-- Replaying either route of one residual tile recovers that route and one trace. -/
theorem causalReadout_tile {source : Multiset R} (pair : S.concurrency.Pair source) :
    S.replayWord (S.pathEntries (pair.route S.concurrency)) source =
        some ⟨(S.concurrency.residual pair.independent).target, pair.route S.concurrency⟩ ∧
      S.replayWord (S.pathEntries (pair.swapped S.concurrency)) source =
        some ⟨(S.concurrency.residual pair.independent).target, pair.swapped S.concurrency⟩ ∧
      S.causalReadout (pair.route S.concurrency) =
        S.causalReadout (pair.swapped S.concurrency) :=
  ⟨S.replayWord_of_path (pair.route S.concurrency),
    S.replayWord_of_path (pair.swapped S.concurrency),
    EventConcurrency.Trace.mk_sound (.tile (T := S.concurrency.tiles) pair)⟩

/-- An arbitrary prefix keeps the two routes of a tile one trace. -/
theorem causalReadout_prefix_tile {source middle : Multiset R}
    (pre : OccurrencePath S.presentation source middle)
    (pair : S.concurrency.Pair middle) :
    S.causalReadout (pre.append (pair.route S.concurrency)) =
      S.causalReadout (pre.append (pair.swapped S.concurrency)) :=
  (EventConcurrency.Trace.append_mk (T := S.concurrency.tiles) pre
      (pair.route S.concurrency)).symm.trans <|
    (congrArg (EventConcurrency.Trace.append (S.causalReadout pre))
      (EventConcurrency.Trace.mk_sound (.tile (T := S.concurrency.tiles) pair))).trans <|
      EventConcurrency.Trace.append_mk (T := S.concurrency.tiles) pre
        (pair.swapped S.concurrency)

/-- An arbitrary suffix keeps the two routes of a tile one trace. -/
theorem causalReadout_suffix_tile {source target : Multiset R}
    (pair : S.concurrency.Pair source)
    (post : OccurrencePath S.presentation
      (S.concurrency.residual pair.independent).target target) :
    S.causalReadout ((pair.route S.concurrency).append post) =
      S.causalReadout ((pair.swapped S.concurrency).append post) :=
  (EventConcurrency.Trace.append_mk (T := S.concurrency.tiles)
      (pair.route S.concurrency) post).symm.trans <|
    (congrArg (fun earlier =>
        EventConcurrency.Trace.append earlier (S.causalReadout post))
      (EventConcurrency.Trace.mk_sound (.tile (T := S.concurrency.tiles) pair))).trans <|
      EventConcurrency.Trace.append_mk (T := S.concurrency.tiles)
        (pair.swapped S.concurrency) post

end System

end Mettapedia.GSLT.Causality.ResourceInteraction

namespace Mettapedia.GSLT.Causality.ResourceInteraction.Controls

open Mettapedia.GSLT.Causality.OccurrenceHistory
open Mettapedia.GSLT.Causality.EventConcurrency

/-!
`persistentReceiver` reads one receiver and consumes two distinct messages.
The ordered words differ. `sharedPair` fires `answerBy 1` twice, so it is the
duplicate-occurrence control rather than this one. The markings supplied here
are replay data. -/

def persistentEntry (value : ℕ) : persistentReceiver.Entry := ⟨(), takeAgain value⟩

def persistentForward : List persistentReceiver.Entry :=
  [persistentEntry 1, persistentEntry 2]

def persistentReverse : List persistentReceiver.Entry :=
  [persistentEntry 2, persistentEntry 1]

def persistentPair : persistentReceiver.concurrency.Pair twoMessages where
  first := persistentReceiver.event twoMessages (takeAgain 1) (by unfold System.Enables; decide)
  second := persistentReceiver.event twoMessages (takeAgain 2) (by unfold System.Enables; decide)
  independent := persistent_receiver_concurrent

theorem persistent_forward_entries :
    persistentReceiver.pathEntries (persistentPair.route persistentReceiver.concurrency) =
      persistentForward := rfl

theorem persistent_reverse_entries :
    persistentReceiver.pathEntries (persistentPair.swapped persistentReceiver.concurrency) =
      persistentReverse :=
  Eq.trans
    (persistentReceiver.pathEntries_cast
      (persistentReceiver.concurrency.close persistentPair.independent).symm
      (.cons (Concurrency.occ persistentPair.second)
        (.cons (Concurrency.occ (persistentReceiver.concurrency.residual
            (persistentReceiver.concurrency.symm persistentPair.independent)))
          (.refl (P := persistentReceiver.presentation) _))))
    rfl

/-- The two message orders are different words, both replay, and one observation. -/
theorem persistent_receiver_orders :
    persistentForward ≠ persistentReverse ∧
      persistentReceiver.replayWord persistentForward twoMessages =
        some ⟨_, persistentPair.route persistentReceiver.concurrency⟩ ∧
      persistentReceiver.replayWord persistentReverse twoMessages =
        some ⟨_, persistentPair.swapped persistentReceiver.concurrency⟩ ∧
      persistentReceiver.causalReadout (persistentPair.route persistentReceiver.concurrency) =
        persistentReceiver.causalReadout
          (persistentPair.swapped persistentReceiver.concurrency) := by
  refine ⟨?_, ?_, ?_,
      EventConcurrency.Trace.mk_sound (.tile (T := persistentReceiver.concurrency.tiles) persistentPair)⟩
  · intro same
    obtain ⟨head, _⟩ := List.cons.inj same
    obtain ⟨_, instances⟩ := Sigma.mk.inj_iff.mp head
    exact absurd (eq_of_heq instances) (by decide : (1 : ℕ) ≠ 2)
  · rw [← persistent_forward_entries]
    exact persistentReceiver.replayWord_of_path _
  · rw [← persistent_reverse_entries]
    exact persistentReceiver.replayWord_of_path _

/-- One linear receiver can take either message, and cannot take the other afterwards. -/
theorem linear_conflict_refuses_second :
    (linearReceiver.replayWord [⟨(), take 1⟩] twoMessages).isSome = true ∧
      (linearReceiver.replayWord [⟨(), take 2⟩] twoMessages).isSome = true ∧
      linearReceiver.replayWord [⟨(), take 1⟩, ⟨(), take 2⟩] twoMessages = none ∧
      linearReceiver.replayWord [⟨(), take 2⟩, ⟨(), take 1⟩] twoMessages = none := by
  have firstFlag : linearReceiver.enabledB twoMessages ⟨(), take 1⟩ = true :=
    (linearReceiver.enabledB_iff twoMessages ⟨(), take 1⟩).mpr linear_receiver_takes_one.1
  have secondFlag : linearReceiver.enabledB twoMessages ⟨(), take 2⟩ = true :=
    (linearReceiver.enabledB_iff twoMessages ⟨(), take 2⟩).mpr (by
      unfold System.Enables
      decide)
  have secondDisabled : linearReceiver.enabledB
      (linearReceiver.fire twoMessages (take 1)) ⟨(), take 2⟩ = false := by
    cases flag : linearReceiver.enabledB (linearReceiver.fire twoMessages (take 1)) ⟨(), take 2⟩ with
    | false => rfl
    | true =>
        exact (linear_receiver_takes_one.2
          ((linearReceiver.enabledB_iff _ _).mp flag)).elim
  have firstDisabled : linearReceiver.enabledB
      (linearReceiver.fire twoMessages (take 2)) ⟨(), take 1⟩ = false := by
    cases flag : linearReceiver.enabledB (linearReceiver.fire twoMessages (take 2)) ⟨(), take 1⟩ with
    | false => rfl
    | true =>
        exact (linearReceiver.disabled_after twoMessages (take 2) (take 1) Res.receiver
          (by decide) (by decide) (by decide) (by decide)
          ((linearReceiver.enabledB_iff _ _).mp flag)).elim
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [linearReceiver.replayWord_cons_enabled _ _ _ firstFlag, linearReceiver.replayWord_nil]
    rfl
  · rw [linearReceiver.replayWord_cons_enabled _ _ _ secondFlag, linearReceiver.replayWord_nil]
    rfl
  · rw [linearReceiver.replayWord_cons_enabled _ _ _ firstFlag,
      linearReceiver.replayWord_cons_disabled _ _ _ secondDisabled]
    rfl
  · rw [linearReceiver.replayWord_cons_enabled _ _ _ secondFlag,
      linearReceiver.replayWord_cons_disabled _ _ _ firstDisabled]
    rfl

/-- Each equation answers the one call. The two-step word is refused. The site
lists agree, and the descended instance grade keeps the answers apart. -/
theorem equation_alternatives_stay_distinct :
    (space.replayWord [ExplorationControls.spaceEntry 1] oneCallTwoEquations).isSome = true ∧
      (space.replayWord [ExplorationControls.spaceEntry 2] oneCallTwoEquations).isSome = true ∧
      space.replayWord [ExplorationControls.spaceEntry 1, ExplorationControls.spaceEntry 2]
        oneCallTwoEquations = none ∧
      space.replayWord [ExplorationControls.spaceEntry 2, ExplorationControls.spaceEntry 1]
        oneCallTwoEquations = none ∧
      ∀ recovered1 recovered2,
        space.replayWord [ExplorationControls.spaceEntry 1] oneCallTwoEquations = some recovered1 →
          space.replayWord [ExplorationControls.spaceEntry 2] oneCallTwoEquations =
              some recovered2 →
            OccurrencePath.sites recovered1.2 = OccurrencePath.sites recovered2.2 ∧
              (space.instanceValuation (fun {_site} (i : space.Instance _site) => (i : ℕ))).onPath
                  recovered1.2 = 1 ∧
                (space.instanceValuation (fun {_site} (i : space.Instance _site) => (i : ℕ))).onPath
                    recovered2.2 = 2 := by
  have enabled1 : space.enabledB oneCallTwoEquations (ExplorationControls.spaceEntry 1) = true :=
    (space.enabledB_iff oneCallTwoEquations (ExplorationControls.spaceEntry 1)).mpr (by
      unfold System.Enables
      decide)
  have enabled2 : space.enabledB oneCallTwoEquations (ExplorationControls.spaceEntry 2) = true :=
    (space.enabledB_iff oneCallTwoEquations (ExplorationControls.spaceEntry 2)).mpr (by
      unfold System.Enables
      decide)
  have secondDisabled : space.enabledB
      (space.fire oneCallTwoEquations (ExplorationControls.spaceEntry 1).2)
      (ExplorationControls.spaceEntry 2) = false := by
    cases flag : space.enabledB
        (space.fire oneCallTwoEquations (ExplorationControls.spaceEntry 1).2)
        (ExplorationControls.spaceEntry 2) with
    | false => rfl
    | true =>
        exact (equations_are_alternatives.2 ((space.enabledB_iff _ _).mp flag)).elim
  have firstDisabled : space.enabledB
      (space.fire oneCallTwoEquations (ExplorationControls.spaceEntry 2).2)
      (ExplorationControls.spaceEntry 1) = false := by
    cases flag : space.enabledB
        (space.fire oneCallTwoEquations (ExplorationControls.spaceEntry 2).2)
        (ExplorationControls.spaceEntry 1) with
    | false => rfl
    | true =>
        exact (space.disabled_after oneCallTwoEquations (answerBy 2) (answerBy 1) SpaceRes.call
          (by decide) (by decide) (by decide) (by decide)
          ((space.enabledB_iff _ _).mp flag)).elim
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [space.replayWord_cons_enabled _ _ _ enabled1, space.replayWord_nil]
    rfl
  · rw [space.replayWord_cons_enabled _ _ _ enabled2, space.replayWord_nil]
    rfl
  · rw [space.replayWord_cons_enabled _ _ _ enabled1,
      space.replayWord_cons_disabled _ _ _ secondDisabled]
    rfl
  · rw [space.replayWord_cons_enabled _ _ _ enabled2,
      space.replayWord_cons_disabled _ _ _ firstDisabled]
    rfl
  · intro recovered1 recovered2 replay1 replay2
    have entries1 := space.replayWord_entries _ _ recovered1 replay1
    have entries2 := space.replayWord_entries _ _ recovered2 replay2
    have sites1 : OccurrencePath.sites recovered1.2 = [()] := by
      rw [space.sites_eq_entries, entries1]
      rfl
    have sites2 : OccurrencePath.sites recovered2.2 = [()] := by
      rw [space.sites_eq_entries, entries2]
      rfl
    have grade1 :
        (space.instanceValuation (fun {_site} (i : space.Instance _site) => (i : ℕ))).onPath
            recovered1.2 = 1 :=
      Eq.trans (space.instanceValuation_onPath _ recovered1.2) (by rw [entries1]; rfl)
    have grade2 :
        (space.instanceValuation (fun {_site} (i : space.Instance _site) => (i : ℕ))).onPath
            recovered2.2 = 2 :=
      Eq.trans (space.instanceValuation_onPath _ recovered2.2) (by rw [entries2]; rfl)
    exact ⟨sites1.trans sites2.symm, grade1, grade2⟩

/-- Two calls fire the same equation twice. The recovered word keeps both occurrences. -/
theorem duplicate_answer_occurrences :
    ∃ recovered : Σ target : Multiset SpaceRes,
        OccurrencePath space.presentation twoCallsOneEquation target,
      space.replayWord [⟨(), answerBy 1⟩, ⟨(), answerBy 1⟩] twoCallsOneEquation =
          some recovered ∧
        space.pathEntries recovered.2 = [⟨(), answerBy 1⟩, ⟨(), answerBy 1⟩] ∧
          (space.pathEntries recovered.2).length = 2 := by
  have enabled : space.Enables twoCallsOneEquation (answerBy 1) := by
    unfold System.Enables
    decide
  have again : space.Enables (space.fire twoCallsOneEquation (answerBy 1)) (answerBy 1) :=
    space.enables_fire calls_share_equation
  have fires : space.Fires [⟨(), answerBy 1⟩, ⟨(), answerBy 1⟩] twoCallsOneEquation
      (space.fire (space.fire twoCallsOneEquation (answerBy 1)) (answerBy 1)) :=
    ⟨enabled, ⟨again, rfl⟩⟩
  obtain ⟨path, replayed, entries⟩ := space.replayWord_complete _ fires
  exact ⟨⟨_, path⟩, replayed, entries, by rw [entries]; rfl⟩

end Mettapedia.GSLT.Causality.ResourceInteraction.Controls

namespace Mettapedia.GSLT.Causality.ResourceInteraction.GroundBag

open Mettapedia.GSLT.Causality.OccurrenceHistory
open Mettapedia.GSLT.Causality.EventConcurrency

/-!
Resource projection for profile `ground-bag-read-take-add-v1`.

The site of a firing is the physical selected-row key, a list of natural
numbers: an initial row index, then an output slot beneath the firing that
created the row. The instance stores taken keys, raw read requests, and an
output count. Produced keys are that site extended by each slot index.
`ground.read` is the deduplicated multiset of those requests, so one physical
row read twice remains one resource. The frontier adapter sends the raw read
list, the selected row and takes, and the output slots to
`CausalReceipt.ResourceFrontier.receipt?`. Action payloads stay outside this
projection.

The supplied bag is replay data. Replaying a word and reading its trace are
observations. They do not schedule work and they do not grant authority.
-/

abbrev Key := List ℕ

/-- Reads, takes, and output slots at one selected row. The row is not among
its own takes or reads, and a taken row is not also read. -/
structure Footprint (site : Key) where
  takes : List Key
  reads : List Key
  outputs : ℕ
  own_once : site ∉ takes
  not_read : site ∉ reads
  takes_apart : ∀ taken ∈ takes, taken ∉ reads

def slots (site : Key) (outputs : ℕ) : List Key :=
  (List.range outputs).map fun slot => site ++ [slot]

def ground : System Key where
  Site := Key
  Instance := Footprint
  consume := fun {site} footprint => {site} + Multiset.ofList footprint.takes
  read := fun footprint => (Multiset.ofList footprint.reads).dedup
  produce := fun {site} footprint => Multiset.ofList (slots site footprint.outputs)

/-- The selected row occurs once in the consumption. -/
theorem selected_consumed_once {site : Key} (footprint : Footprint site) :
    Multiset.count site (ground.consume footprint) = 1 := by
  change Multiset.count site ({site} + Multiset.ofList footprint.takes) = 1
  rw [Multiset.count_add, Multiset.count_singleton_self,
    Multiset.count_eq_zero.mpr fun member =>
      footprint.own_once (Multiset.mem_coe.mp member)]

/-- Repeated raw requests for one row require that row once. -/
theorem read_requirement {site : Key} (footprint : Footprint site) (key : Key) :
    Multiset.count key (ground.read footprint) =
      if key ∈ Multiset.ofList footprint.reads then 1 else 0 := by
  change Multiset.count key ((Multiset.ofList footprint.reads).dedup) =
    if key ∈ Multiset.ofList footprint.reads then 1 else 0
  exact Multiset.count_dedup (Multiset.ofList footprint.reads) key

def step {site : Key} (footprint : Footprint site) : ground.Entry := ⟨site, footprint⟩

def token : Key := [0]
def leftKey : Key := [1]
def rightKey : Key := [2]
def threeRows : Multiset Key := {token, leftKey, rightKey}

def leftRead : Footprint leftKey where
  takes := []
  reads := [token]
  outputs := 1
  own_once := by decide
  not_read := by decide
  takes_apart := by intro _ member; cases member

def rightRead : Footprint rightKey where
  takes := []
  reads := [token]
  outputs := 1
  own_once := by decide
  not_read := by decide
  takes_apart := by intro _ member; cases member

def readForward : List ground.Entry := [step leftRead, step rightRead]
def readReverse : List ground.Entry := [step rightRead, step leftRead]

def readPair : ground.concurrency.Pair threeRows where
  first := ground.event threeRows leftRead (by unfold System.Enables; decide)
  second := ground.event threeRows rightRead (by unfold System.Enables; decide)
  independent := ground.concurrent_of_shared_read threeRows leftRead rightRead {token}
    (by decide) (by decide) (by decide)

theorem read_forward_entries :
    ground.pathEntries (readPair.route ground.concurrency) = readForward := rfl

theorem read_reverse_entries :
    ground.pathEntries (readPair.swapped ground.concurrency) = readReverse :=
  Eq.trans
    (ground.pathEntries_cast (ground.concurrency.close readPair.independent).symm
      (.cons (Concurrency.occ readPair.second)
        (.cons (Concurrency.occ (ground.concurrency.residual
            (ground.concurrency.symm readPair.independent)))
          (.refl (P := ground.presentation) _))))
    rfl

/-- The residual of the right read keeps the right selected-row key. -/
theorem read_residual_keeps_key :
    (ground.concurrency.residual readPair.independent).site = rightKey :=
  ground.concurrency.residual_site readPair.independent

/-- Two reads are different located words and one trace. -/
theorem shared_reads_one_trace :
    OccurrencePath.sites (readPair.route ground.concurrency) = [leftKey, rightKey] ∧
      OccurrencePath.sites (readPair.swapped ground.concurrency) = [rightKey, leftKey] ∧
      readForward ≠ readReverse ∧
      ground.replayWord readForward threeRows =
        some ⟨_, readPair.route ground.concurrency⟩ ∧
      ground.replayWord readReverse threeRows =
        some ⟨_, readPair.swapped ground.concurrency⟩ ∧
      ground.causalReadout (readPair.route ground.concurrency) =
        ground.causalReadout (readPair.swapped ground.concurrency) := by
  refine ⟨?_, ?_, ?_, ?_, ?_,
      EventConcurrency.Trace.mk_sound (.tile (T := ground.concurrency.tiles) readPair)⟩
  · exact (ground.sites_eq_entries _).trans
      ((congrArg (fun entries => entries.map Sigma.fst) read_forward_entries).trans rfl)
  · exact (ground.sites_eq_entries _).trans
      ((congrArg (fun entries => entries.map Sigma.fst) read_reverse_entries).trans rfl)
  · intro same
    obtain ⟨head, _⟩ := List.cons.inj same
    obtain ⟨sites, _⟩ := Sigma.mk.inj_iff.mp head
    change ([1] : List ℕ) = [2] at sites
    exact absurd sites (by decide)
  · rw [← read_forward_entries]
    exact ground.replayWord_of_path _
  · rw [← read_reverse_entries]
    exact ground.replayWord_of_path _

def leftTake : Footprint leftKey where
  takes := [token]
  reads := []
  outputs := 1
  own_once := by decide
  not_read := by decide
  takes_apart := by
    intro taken member
    simp at member
    subst member
    decide

def rightTake : Footprint rightKey where
  takes := [token]
  reads := []
  outputs := 1
  own_once := by decide
  not_read := by decide
  takes_apart := by
    intro taken member
    simp at member
    subst member
    decide

/-- Each take can fire. The shared row is then gone, so the other take is refused. -/
theorem competing_takes_refuse_second :
    (ground.replayWord [step leftTake] threeRows).isSome = true ∧
      (ground.replayWord [step rightTake] threeRows).isSome = true ∧
      ground.replayWord [step leftTake, step rightTake] threeRows = none ∧
      ground.replayWord [step rightTake, step leftTake] threeRows = none := by
  have leftFlag : ground.enabledB threeRows (step leftTake) = true :=
    (ground.enabledB_iff threeRows (step leftTake)).mpr (by unfold System.Enables; decide)
  have rightFlag : ground.enabledB threeRows (step rightTake) = true :=
    (ground.enabledB_iff threeRows (step rightTake)).mpr (by unfold System.Enables; decide)
  have rightDisabled : ground.enabledB
      (ground.fire threeRows (step leftTake).2) (step rightTake) = false := by
    cases flag : ground.enabledB (ground.fire threeRows (step leftTake).2) (step rightTake) with
    | false => rfl
    | true =>
        exact (ground.disabled_after threeRows (step leftTake).2 rightTake token
          (by decide) (by decide) (by decide) (by decide)
          ((ground.enabledB_iff _ _).mp flag)).elim
  have leftDisabled : ground.enabledB
      (ground.fire threeRows (step rightTake).2) (step leftTake) = false := by
    cases flag : ground.enabledB (ground.fire threeRows (step rightTake).2) (step leftTake) with
    | false => rfl
    | true =>
        exact (ground.disabled_after threeRows (step rightTake).2 leftTake token
          (by decide) (by decide) (by decide) (by decide)
          ((ground.enabledB_iff _ _).mp flag)).elim
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ground.replayWord_cons_enabled _ _ _ leftFlag, ground.replayWord_nil]
    rfl
  · rw [ground.replayWord_cons_enabled _ _ _ rightFlag, ground.replayWord_nil]
    rfl
  · rw [ground.replayWord_cons_enabled _ _ _ leftFlag,
      ground.replayWord_cons_disabled _ _ _ rightDisabled]
    rfl
  · rw [ground.replayWord_cons_enabled _ _ _ rightFlag,
      ground.replayWord_cons_disabled _ _ _ leftDisabled]
    rfl

def startKey : Key := [0]
def madeToken : Key := [0, 0]
def madeExec : Key := [0, 1]
def startRows : Multiset Key := {startKey}

def startFiring : Footprint startKey where
  takes := []
  reads := []
  outputs := 2
  own_once := by decide
  not_read := by decide
  takes_apart := by intro _ member; cases member

def nextFiring : Footprint madeExec where
  takes := [madeToken]
  reads := []
  outputs := 1
  own_once := by decide
  not_read := by decide
  takes_apart := by
    intro taken member
    simp at member
    subst member
    decide

/-- The created execution's site is its output-slot key. It is absent from the
initial bag and enabled only on the producer's residual. -/
theorem created_exec_needs_its_producer :
    ground.replayWord [step nextFiring] startRows = none ∧
      ∃ recovered : Σ target : Multiset Key,
          OccurrencePath ground.presentation startRows target,
        ground.replayWord [step startFiring, step nextFiring] startRows = some recovered ∧
          OccurrencePath.sites recovered.2 = [startKey, madeExec] ∧
          nextFiring.takes = [madeToken] := by
  have startEnabled : ground.Enables startRows startFiring := by
    unfold System.Enables
    decide
  have nextDisabled : ground.enabledB startRows (step nextFiring) = false := by
    cases flag : ground.enabledB startRows (step nextFiring) with
    | false => rfl
    | true =>
        exact absurd ((ground.enabledB_iff startRows (step nextFiring)).mp flag) (by
          unfold System.Enables
          decide)
  have nextEnabled : ground.Enables (ground.fire startRows startFiring) nextFiring := by
    unfold System.Enables
    decide
  have fires : ground.Fires [step startFiring, step nextFiring] startRows
      (ground.fire (ground.fire startRows startFiring) nextFiring) :=
    ⟨startEnabled, ⟨nextEnabled, rfl⟩⟩
  obtain ⟨path, replayed, entries⟩ := ground.replayWord_complete _ fires
  refine ⟨ground.replayWord_cons_disabled (step nextFiring) [] startRows nextDisabled,
    ⟨_, path⟩, replayed,
    (ground.sites_eq_entries path).trans
      ((congrArg (fun word => word.map Sigma.fst) entries).trans rfl),
    rfl⟩

def branchToken : Key := [0, 0]
def leftMade : Key := [0, 1]
def rightMade : Key := [0, 2]
def parentRows : Multiset Key := {startKey}

def parentFiring : Footprint startKey where
  takes := []
  reads := []
  outputs := 3
  own_once := by decide
  not_read := by decide
  takes_apart := by intro _ member; cases member

def leftChild : Footprint leftMade where
  takes := []
  reads := [branchToken]
  outputs := 1
  own_once := by decide
  not_read := by decide
  takes_apart := by intro _ member; cases member

def rightChild : Footprint rightMade where
  takes := []
  reads := [branchToken]
  outputs := 1
  own_once := by decide
  not_read := by decide
  takes_apart := by intro _ member; cases member

theorem parent_enabled : ground.Enables parentRows parentFiring := by
  unfold System.Enables
  decide

def parentPath : OccurrencePath ground.presentation parentRows
    (ground.fire parentRows parentFiring) :=
  ground.firing parentRows parentFiring parent_enabled

def childPair : ground.concurrency.Pair (ground.fire parentRows parentFiring) where
  first := ground.event (ground.fire parentRows parentFiring) leftChild
    (by unfold System.Enables; decide)
  second := ground.event (ground.fire parentRows parentFiring) rightChild
    (by unfold System.Enables; decide)
  independent := ground.concurrent_of_shared_read (ground.fire parentRows parentFiring)
    leftChild rightChild {branchToken} (by decide) (by decide) (by decide)

/-- The two created reads keep their selected-row keys, commute, and retain the
producer prefix as one trace. -/
theorem created_reads_keep_the_prefix :
    (ground.concurrency.residual childPair.independent).site = rightMade ∧
      OccurrencePath.sites (parentPath.append (childPair.route ground.concurrency)) =
        [startKey, leftMade, rightMade] ∧
      OccurrencePath.sites (parentPath.append (childPair.swapped ground.concurrency)) =
        [startKey, rightMade, leftMade] ∧
      ground.replayWord [step leftChild, step rightChild] (ground.fire parentRows parentFiring) =
        some ⟨_, childPair.route ground.concurrency⟩ ∧
      ground.replayWord [step rightChild, step leftChild] (ground.fire parentRows parentFiring) =
        some ⟨_, childPair.swapped ground.concurrency⟩ ∧
      ground.causalReadout (parentPath.append (childPair.route ground.concurrency)) =
        ground.causalReadout (parentPath.append (childPair.swapped ground.concurrency)) := by
  refine ⟨ground.concurrency.residual_site childPair.independent, ?_, ?_, ?_, ?_,
      ground.causalReadout_prefix_tile parentPath childPair⟩
  · have parentEntries : ground.pathEntries parentPath = [step parentFiring] := rfl
    have forward : ground.pathEntries (childPair.route ground.concurrency) =
        [step leftChild, step rightChild] := rfl
    have listed :=
      (congrArg (fun earlier => earlier ++ ground.pathEntries (childPair.route ground.concurrency))
          parentEntries).trans
        ((congrArg (fun later => [step parentFiring] ++ later) forward).trans rfl)
    exact (ground.sites_eq_entries _).trans
      ((congrArg (fun word => word.map Sigma.fst)
          ((ground.pathEntries_append parentPath (childPair.route ground.concurrency)).trans
            listed)).trans rfl)
  · have parentEntries : ground.pathEntries parentPath = [step parentFiring] := rfl
    have reverse : ground.pathEntries (childPair.swapped ground.concurrency) =
        [step rightChild, step leftChild] :=
      Eq.trans
        (ground.pathEntries_cast (ground.concurrency.close childPair.independent).symm
          (.cons (Concurrency.occ childPair.second)
            (.cons (Concurrency.occ (ground.concurrency.residual
                (ground.concurrency.symm childPair.independent)))
              (.refl (P := ground.presentation) _))))
        rfl
    have listed :=
      (congrArg (fun earlier => earlier ++ ground.pathEntries (childPair.swapped ground.concurrency))
          parentEntries).trans
        ((congrArg (fun later => [step parentFiring] ++ later) reverse).trans rfl)
    exact (ground.sites_eq_entries _).trans
      ((congrArg (fun word => word.map Sigma.fst)
          ((ground.pathEntries_append parentPath (childPair.swapped ground.concurrency)).trans
            listed)).trans rfl)
  · rw [← show ground.pathEntries (childPair.route ground.concurrency) =
        [step leftChild, step rightChild] from rfl]
    exact ground.replayWord_of_path _
  · have reverse : ground.pathEntries (childPair.swapped ground.concurrency) =
        [step rightChild, step leftChild] :=
      Eq.trans
        (ground.pathEntries_cast (ground.concurrency.close childPair.independent).symm
          (.cons (Concurrency.occ childPair.second)
            (.cons (Concurrency.occ (ground.concurrency.residual
                (ground.concurrency.symm childPair.independent)))
              (.refl (P := ground.presentation) _))))
        rfl
    rw [← reverse]
    exact ground.replayWord_of_path _

/-- One physical token requested twice. The raw requests stay repeated. -/
def doubleRead : Footprint leftKey where
  takes := []
  reads := [token, token]
  outputs := 1
  own_once := by decide
  not_read := by decide
  takes_apart := by intro _ member; cases member

theorem repeated_read_one_resource :
    doubleRead.reads = [token, token] ∧
      Multiset.count token (ground.read doubleRead) = 1 ∧
      ground.Enables {token, leftKey} doubleRead := by
  refine ⟨rfl, ?_, ?_⟩
  · rw [read_requirement]
    decide
  · unfold System.Enables
    decide

/-- Selected-row key. `Sigma.fst`, with the codomain pinned to `Key`. -/
def firingKey : ground.Entry → Key :=
  Sigma.fst

/-- Selected row followed by its takes. The raw read requests stay raw. -/
def firingConsume (entry : ground.Entry) : List Key :=
  entry.1 :: entry.2.takes

def firingReads (entry : ground.Entry) : List Key :=
  entry.2.reads

def firingSlots (entry : ground.Entry) : List Key :=
  slots entry.1 entry.2.outputs

/-- Project a firing word into the existing resource frontier.
Identity is the selected-row key. Consumption is that key followed by its
takes. Reads are the raw requests. Production is the output-slot list. -/
def project (word : List ground.Entry) :
    Option (Mettapedia.Machines.CausalReceipt Key) :=
  Mettapedia.Machines.CausalReceipt.ResourceFrontier.receipt?
    firingKey firingConsume firingReads firingSlots word

theorem project_sound (word : List ground.Entry)
    (result : Mettapedia.Machines.CausalReceipt Key)
    (accepted : project word = some result) :
    Mettapedia.Machines.CausalReceipt.WellFormed [] result ∧
      result.flattenedSupport = word.map Sigma.fst :=
  Mettapedia.Machines.CausalReceipt.ResourceFrontier.receipt?_sound
    firingKey firingConsume firingReads firingSlots word result accepted

/-! ## Physical keys allocated by a legitimate run

Initial roots are distinct row indices. A firing may select only a key that is
still live. Its output slots are the extensions `site ++ [slot]`. Selecting
the row removes it from the live keys and adds those slots. -/

theorem extension_eq {parent parent' : Key} {i j : ℕ} :
    parent ++ [i] = parent' ++ [j] ↔ parent = parent' ∧ i = j := by
  constructor
  · intro eq
    obtain ⟨parents, idxs⟩ := List.append_inj' eq (by simp)
    obtain ⟨idx, _⟩ := List.cons.inj idxs
    exact ⟨parents, idx⟩
  · intro same
    rcases same with ⟨rfl, rfl⟩
    rfl

theorem slot_ne_site (site : Key) (i : ℕ) : site ++ [i] ≠ site := by
  intro eq
  have lengths := congrArg List.length eq
  rw [List.length_append, List.length_singleton] at lengths
  omega

theorem slot_injective (site : Key) : Function.Injective (fun slot : ℕ => site ++ [slot]) := by
  intro i j eq
  exact (extension_eq.mp eq).2

theorem slots_nodup (site : Key) (outputs : ℕ) : (slots site outputs).Nodup := by
  unfold slots
  exact List.Nodup.map (slot_injective site) (List.nodup_range (n := outputs))

def without (live : List Key) (site : Key) : List Key :=
  live.filter fun key => decide (key ≠ site)

theorem mem_without {live : List Key} {site key : Key} :
    key ∈ without live site ↔ key ∈ live ∧ key ≠ site := by
  unfold without
  rw [List.mem_filter, decide_eq_true_iff]

theorem without_nodup {live : List Key} (site : Key) (distinct : live.Nodup) :
    (without live site).Nodup := by
  unfold without
  exact List.Nodup.filter _ distinct

def nextLive (live : List Key) (site : Key) (outputs : ℕ) : List Key :=
  without live site ++ slots site outputs

def nextTaken (taken : List Key) (site : Key) : List Key :=
  site :: taken

/-- Live keys are the initial roots and slots of rows already selected. -/
structure Ledger where
  roots : List Key
  live : List Key
  taken : List Key
  roots_idx : ∀ key ∈ roots, key.length = 1
  live_nodup : live.Nodup
  taken_nodup : taken.Nodup
  apart : ∀ key ∈ live, key ∉ taken
  live_long : ∀ key ∈ live, 1 ≤ key.length
  taken_long : ∀ key ∈ taken, 1 ≤ key.length
  live_origin : ∀ key ∈ live, key ∈ roots ∨ ∃ parent ∈ taken, ∃ slot : ℕ, key = parent ++ [slot]
  taken_origin : ∀ key ∈ taken, key ∈ roots ∨ ∃ parent ∈ taken, ∃ slot : ℕ, key = parent ++ [slot]

def ledger_roots (roots : List Key) (distinct : roots.Nodup)
    (idx : ∀ key ∈ roots, key.length = 1) : Ledger where
  roots := roots
  live := roots
  taken := []
  roots_idx := idx
  live_nodup := distinct
  taken_nodup := List.Pairwise.nil
  apart := by
    intro _ _ member
    cases member
  live_long := by
    intro key member
    have := idx key member
    omega
  taken_long := by
    intro _ member
    cases member
  live_origin := fun _ member => Or.inl member
  taken_origin := by
    intro _ member
    cases member

theorem allocated_extension_fresh (ledger : Ledger) {site : Key}
    (site_live : site ∈ ledger.live) (i : ℕ) :
    site ++ [i] ∉ ledger.live ∧ site ++ [i] ∉ ledger.taken := by
  refine ⟨?_, ?_⟩
  · intro member
    rcases ledger.live_origin _ member with root | ⟨parent, parentTaken, _, eq⟩
    · have short := ledger.roots_idx _ root
      have long := ledger.live_long site site_live
      have lengthEq : (site ++ [i]).length = site.length + 1 := by
        simp [List.length_append]
      omega
    · obtain ⟨rfl, _⟩ := extension_eq.mp eq
      exact ledger.apart site site_live parentTaken
  · intro member
    rcases ledger.taken_origin _ member with root | ⟨parent, parentTaken, _, eq⟩
    · have short := ledger.roots_idx _ root
      have long := ledger.live_long site site_live
      have lengthEq : (site ++ [i]).length = site.length + 1 := by
        simp [List.length_append]
      omega
    · obtain ⟨rfl, _⟩ := extension_eq.mp eq
      exact ledger.apart site site_live parentTaken

def step_ledger (ledger : Ledger) {site : Key} (outputs : ℕ)
    (site_live : site ∈ ledger.live) :
    Ledger where
  roots := ledger.roots
  live := nextLive ledger.live site outputs
  taken := nextTaken ledger.taken site
  roots_idx := ledger.roots_idx
  live_nodup := by
    refine List.Nodup.append (without_nodup site ledger.live_nodup) (slots_nodup site outputs) ?_
    intro key inWithout inSlots
    obtain ⟨inLive, _⟩ := mem_without.mp inWithout
    unfold slots at inSlots
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp inSlots
    exact (allocated_extension_fresh ledger site_live i).1 inLive
  taken_nodup := by
    unfold nextTaken
    rw [List.nodup_cons]
    exact ⟨ledger.apart site site_live, ledger.taken_nodup⟩
  apart := by
    intro key member inTaken
    unfold nextLive at member
    unfold nextTaken at inTaken
    rcases List.mem_append.mp member with inWithout | inSlots
    · obtain ⟨inLive, different⟩ := mem_without.mp inWithout
      rcases List.mem_cons.mp inTaken with same | prior
      · exact different same
      · exact ledger.apart key inLive prior
    · unfold slots at inSlots
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp inSlots
      rcases List.mem_cons.mp inTaken with same | prior
      · exact slot_ne_site site i same
      · exact (allocated_extension_fresh ledger site_live i).2 prior
  live_long := by
    intro key member
    unfold nextLive at member
    rcases List.mem_append.mp member with inWithout | inSlots
    · exact ledger.live_long key (mem_without.mp inWithout).1
    · unfold slots at inSlots
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp inSlots
      have long := ledger.live_long site site_live
      simp [List.length_append]
  taken_long := by
    intro key member
    unfold nextTaken at member
    rcases List.mem_cons.mp member with same | prior
    · rw [same]
      exact ledger.live_long site site_live
    · exact ledger.taken_long key prior
  live_origin := by
    intro key member
    unfold nextLive at member
    rcases List.mem_append.mp member with inWithout | inSlots
    · rcases ledger.live_origin key (mem_without.mp inWithout).1 with
        root | ⟨parent, parentTaken, slot, eq⟩
      · exact Or.inl root
      · exact Or.inr ⟨parent, List.mem_cons_of_mem _ parentTaken, slot, eq⟩
    · unfold slots at inSlots
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp inSlots
      exact Or.inr ⟨site, List.mem_cons_self, i, rfl⟩
  taken_origin := by
    intro key member
    unfold nextTaken at member
    rcases List.mem_cons.mp member with same | prior
    · rw [same]
      rcases ledger.live_origin site site_live with root | ⟨parent, parentTaken, slot, eq⟩
      · exact Or.inl root
      · exact Or.inr ⟨parent, List.mem_cons_of_mem _ parentTaken, slot, eq⟩
    · rcases ledger.taken_origin key prior with root | ⟨parent, parentTaken, slot, eq⟩
      · exact Or.inl root
      · exact Or.inr ⟨parent, List.mem_cons_of_mem _ parentTaken, slot, eq⟩

def Allocated (live : List Key) : List ground.Entry → Prop
  | [] => True
  | entry :: rest =>
      entry.1 ∈ live ∧ Allocated (nextLive live entry.1 entry.2.outputs) rest

theorem allocated_avoids (ledger : Ledger) :
    ∀ (word : List ground.Entry), Allocated ledger.live word →
      ∀ entry ∈ word, entry.1 ∉ ledger.taken
  | [], _, _, member => by cases member
  | entry :: rest, allocated, later, laterMember => by
      rcases allocated with ⟨site_live, tail⟩
      let laterLedger := step_ledger ledger entry.2.outputs site_live
      rcases List.mem_cons.mp laterMember with same | restMember
      · rw [same]
        exact ledger.apart entry.1 site_live
      · have avoided := allocated_avoids laterLedger rest tail later restMember
        intro present
        exact avoided (List.mem_cons_of_mem _ present)

theorem allocated_sites_nodup (ledger : Ledger) :
    ∀ (word : List ground.Entry), Allocated ledger.live word → (word.map firingKey).Nodup
  | [], _ => List.Pairwise.nil
  | entry :: rest, allocated => by
      rcases allocated with ⟨site_live, tail⟩
      let laterLedger := step_ledger ledger entry.2.outputs site_live
      rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, allocated_sites_nodup laterLedger rest tail⟩
      intro member
      obtain ⟨later, laterMember, same⟩ := List.mem_map.mp member
      have avoided := allocated_avoids laterLedger rest tail later laterMember
      apply avoided
      have keySame : later.1 = entry.1 := same
      rw [keySame]
      exact List.mem_cons_self

/-- A run is legitimate when its roots are distinct initial indices and every
selected row is live under child-slot allocation. -/
def Legitimate (roots : List Key) (word : List ground.Entry) : Prop :=
  roots.Nodup ∧ (∀ key ∈ roots, key.length = 1) ∧ Allocated roots word

theorem legitimate_sites_nodup {roots : List Key} {word : List ground.Entry}
    (legitimate : Legitimate roots word) : (word.map firingKey).Nodup := by
  rcases legitimate with ⟨distinct, idx, allocated⟩
  let rootsLedger := ledger_roots roots distinct idx
  exact allocated_sites_nodup rootsLedger word allocated

theorem project_of_legitimate {roots : List Key} {word : List ground.Entry}
    (legitimate : Legitimate roots word) :
    project word =
      some (Mettapedia.Machines.CausalReceipt.ResourceFrontier.receipt
        firingKey firingConsume firingReads firingSlots word) := by
  unfold project
  unfold Mettapedia.Machines.CausalReceipt.ResourceFrontier.receipt?
  exact if_pos (legitimate_sites_nodup legitimate)

/-- Firing subtracts the selected row and its takes, then adds that row's slots. -/
theorem fire_eq {site : Key} (footprint : Footprint site) (bag : Multiset Key) :
    ground.fire bag footprint =
      bag - ({site} + Multiset.ofList footprint.takes) +
        Multiset.ofList (slots site footprint.outputs) := rfl

/-- After a firing, every remaining key is still live and the bag stays duplicate-free.
The live list drops the selected row and retains taken rows, so it contains the
residual bag. Retained takes are the overapproximation; membership of each
residual key is the inclusion `fire` gives. -/
theorem fired_preserves (ledger : Ledger) {site : Key} (footprint : Footprint site)
    (site_live : site ∈ ledger.live) (bag : Multiset Key)
    (covered : ∀ key ∈ bag, key ∈ ledger.live) (distinct : bag.Nodup) :
    (∀ key ∈ ground.fire bag footprint,
        key ∈ nextLive ledger.live site footprint.outputs) ∧
      (ground.fire bag footprint).Nodup := by
  have fireEq := fire_eq footprint bag
  refine ⟨?_, ?_⟩
  · intro key member
    rw [fireEq] at member
    rcases Multiset.mem_add.mp member with remained | produced
    · rcases (Multiset.mem_sub_of_nodup distinct).mp remained with ⟨inBag, notConsumed⟩
      have inLive := covered key inBag
      have different : key ≠ site := by
        intro same
        apply notConsumed
        rw [same]
        exact Multiset.mem_add.mpr (Or.inl <| Multiset.mem_singleton.mpr rfl)
      exact List.mem_append.mpr (Or.inl <| mem_without.mpr ⟨inLive, different⟩)
    · exact List.mem_append.mpr (Or.inr <| Multiset.mem_coe.mp produced)
  · rw [fireEq]
    refine Multiset.nodup_add.mpr ⟨?_, ?_, ?_⟩
    · exact Multiset.nodup_of_le (Multiset.sub_le_self _ _) distinct
    · exact Multiset.coe_nodup.mpr (slots_nodup site footprint.outputs)
    · refine Multiset.disjoint_left.mpr ?_
      intro key remained produced
      rcases (Multiset.mem_sub_of_nodup distinct).mp remained with ⟨inBag, _⟩
      have inSlots : key ∈ slots site footprint.outputs := Multiset.mem_coe.mp produced
      unfold slots at inSlots
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp inSlots
      exact (allocated_extension_fresh ledger site_live i).1 (covered _ inBag)

/-- A successful replay selects only live rows. Each selected row is present in
the bag that enabled it, and that bag stays inside the live allocation. -/
theorem replay_allocated (ledger : Ledger) (bag : Multiset Key)
    (covered : ∀ key ∈ bag, key ∈ ledger.live) (distinct : bag.Nodup) :
    ∀ word : List ground.Entry, (ground.replayWord word bag).isSome →
      Allocated ledger.live word
  | [], _ => trivial
  | entry :: rest, replayed => by
      cases flag : ground.enabledB bag entry with
      | false =>
          rw [ground.replayWord_cons_disabled entry rest bag flag] at replayed
          simp at replayed
      | true =>
          have enabled : ground.Enables bag entry.2 :=
            (ground.enabledB_iff bag entry).mp flag
          have site_live : entry.1 ∈ ledger.live := by
            have enabledK :
                ({entry.1} + Multiset.ofList entry.2.takes) +
                  (Multiset.ofList entry.2.reads).dedup ≤ bag := by
              change ground.consume entry.2 + ground.read entry.2 ≤ bag
              exact enabled
            have consume_le :
                ({entry.1} + Multiset.ofList entry.2.takes) ≤ bag :=
              le_trans (Multiset.le_add_right _ _) enabledK
            exact covered _
              (Multiset.mem_of_le consume_le
                (Multiset.mem_add.mpr (Or.inl <| Multiset.mem_singleton.mpr rfl)))
          rw [ground.replayWord_cons_enabled entry rest bag flag] at replayed
          cases continued : ground.replayWord rest (ground.fire bag entry.2) with
          | none =>
              rw [continued] at replayed
              simp at replayed
          | some _ =>
              let laterLedger := step_ledger ledger entry.2.outputs site_live
              have preserved :=
                fired_preserves ledger entry.2 site_live bag covered distinct
              refine ⟨site_live,
                replay_allocated laterLedger (ground.fire bag entry.2)
                  preserved.1 preserved.2 rest (by rw [continued]; rfl)⟩

/-- Initial root indices plus a successful replay determine the frontier receipt.
The allocation of selected rows is derived from that replay. -/
theorem project_of_replay {roots : List Key} {word : List ground.Entry}
    (distinct : roots.Nodup) (idx : ∀ key ∈ roots, key.length = 1)
    (replayed : (ground.replayWord word (Multiset.ofList roots)).isSome) :
    project word =
      some (Mettapedia.Machines.CausalReceipt.ResourceFrontier.receipt
        firingKey firingConsume firingReads firingSlots word) := by
  let rootsLedger := ledger_roots roots distinct idx
  have covered : ∀ key ∈ Multiset.ofList roots, key ∈ rootsLedger.live := by
    intro key member
    exact Multiset.mem_coe.mp member
  have allocated := replay_allocated rootsLedger (Multiset.ofList roots) covered
    (Multiset.coe_nodup.mpr distinct) word replayed
  exact project_of_legitimate ⟨distinct, idx, allocated⟩

/-! ## Concurrency is not frontier independence

`ground.Concurrent` only says both consumes and both reads fit in the bag.
It does not look at output slots. A reachable allocation supplies the missing
conditions: the bag is duplicate-free, and every key in it is live, so each
selected row's output slots are fresh. -/

/-- One firing produces a key that is already in the bag and read by the other.
The bag is duplicate-free and both firings are concurrent. Their frontier
accesses still meet. -/
def overlapProducer : Footprint [0] where
  takes := []
  reads := []
  outputs := 1
  own_once := by decide
  not_read := by decide
  takes_apart := by intro _ member; cases member

def overlapReader : Footprint [1] where
  takes := []
  reads := [[0, 0]]
  outputs := 0
  own_once := by decide
  not_read := by decide
  takes_apart := by intro _ member; cases member

theorem concurrent_not_frontierIndependent :
    let bag : Multiset Key := Multiset.ofList [[0], [1], [0, 0]]
    bag.Nodup ∧
      ground.Concurrent bag overlapProducer overlapReader ∧
      ¬ Mettapedia.Machines.CausalReceipt.ResourceFrontier.Independent
          ([0] :: overlapProducer.takes) overlapProducer.reads
            (slots [0] overlapProducer.outputs)
          ([1] :: overlapReader.takes) overlapReader.reads
            (slots [1] overlapReader.outputs) := by
  refine ⟨Multiset.coe_nodup.mpr (by decide), ?_, ?_⟩
  · unfold System.Concurrent
    decide
  · intro separate
    exact (List.disjoint_left.mp separate.1)
      (by decide : [0, 0] ∈ [0] :: overlapProducer.takes ++ slots [0] overlapProducer.outputs)
      (by decide : [0, 0] ∈ [1] :: overlapReader.takes ++ overlapReader.reads ++
        slots [1] overlapReader.outputs)

/-- The same selected row occurs twice in the bag. Both copies can fire, and
both frontier records use that one key. -/
def duplicateRow : Footprint [0] where
  takes := []
  reads := []
  outputs := 0
  own_once := by decide
  not_read := by decide
  takes_apart := by intro _ member; cases member

theorem duplicated_site_not_frontierIndependent :
    let bag : Multiset Key := Multiset.ofList [[0], [0]]
    ground.Concurrent bag duplicateRow duplicateRow ∧
      ¬ bag.Nodup ∧
      ¬ Mettapedia.Machines.CausalReceipt.ResourceFrontier.Independent
          ([0] :: duplicateRow.takes) duplicateRow.reads (slots [0] duplicateRow.outputs)
          ([0] :: duplicateRow.takes) duplicateRow.reads (slots [0] duplicateRow.outputs) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold System.Concurrent
    decide
  · intro nodupBag
    exact absurd (Multiset.coe_nodup.mp nodupBag) (by decide)
  · intro separate
    exact (List.disjoint_left.mp separate.1)
      (by decide : [0] ∈ [0] :: duplicateRow.takes ++ slots [0] duplicateRow.outputs)
      (by decide : [0] ∈ [0] :: duplicateRow.takes ++ duplicateRow.reads ++
        slots [0] duplicateRow.outputs)

private theorem count_clash {bag demand other seen : Multiset Key}
    (distinct : bag.Nodup) (fits : demand + other + seen ≤ bag) {key : Key}
    (inDemand : key ∈ demand) (inOther : key ∈ other ∨ key ∈ seen) : False := by
  have atMost : Multiset.count key bag ≤ 1 :=
    (Multiset.nodup_iff_count_le_one.mp distinct) key
  have grew : Multiset.count key (demand + other + seen) ≤ Multiset.count key bag :=
    (Multiset.le_iff_count.mp fits) key
  rw [Multiset.count_add, Multiset.count_add] at grew
  have demandPos : 1 ≤ Multiset.count key demand :=
    Nat.succ_le_of_lt (Multiset.count_pos.mpr inDemand)
  rcases inOther with member | member
  · have otherPos : 1 ≤ Multiset.count key other :=
      Nat.succ_le_of_lt (Multiset.count_pos.mpr member)
    omega
  · have seenPos : 1 ≤ Multiset.count key seen :=
      Nat.succ_le_of_lt (Multiset.count_pos.mpr member)
    omega

private theorem demand_le_bag {bag demand other seen : Multiset Key}
    (fits : demand + other + seen ≤ bag) : demand ≤ bag :=
  le_trans (Multiset.le_add_right demand other)
    (le_trans (Multiset.le_add_right (demand + other) seen) fits)

private theorem later_demand_le_bag {bag demand other seen : Multiset Key}
    (fits : demand + other + seen ≤ bag) : other ≤ bag :=
  le_trans (Multiset.le_add_left other demand)
    (le_trans (Multiset.le_add_right (demand + other) seen) fits)

private theorem seen_le_bag {bag head seen : Multiset Key}
    (fits : head + seen ≤ bag) : seen ≤ bag :=
  le_trans (Multiset.le_add_left seen head) fits

private theorem mem_consume_keys {site : Key} {takes : List Key} {key : Key}
    (member : key ∈ site :: takes) : key ∈ {site} + Multiset.ofList takes := by
  rcases List.mem_cons.mp member with rfl | taken
  · exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton.mpr rfl))
  · exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_coe.mpr taken))

private theorem mem_read_keys {reads : List Key} {key : Key} (member : key ∈ reads) :
    key ∈ (Multiset.ofList reads).dedup :=
  Multiset.mem_dedup.mpr (Multiset.mem_coe.mpr member)

private theorem fresh_slot_outside (ledger : Ledger) {site : Key}
    (site_live : site ∈ ledger.live) {bag : Multiset Key}
    (covered : ∀ key ∈ bag, key ∈ ledger.live) (i : ℕ) : site ++ [i] ∉ bag :=
  fun member => (allocated_extension_fresh ledger site_live i).1 (covered _ member)

private theorem one_sided_apart (ledger : Ledger) {bag : Multiset Key}
    (covered : ∀ key ∈ bag, key ∈ ledger.live) (distinct : bag.Nodup)
    {leftSite rightSite : Key} {leftTakes rightTakes rightReads : List Key}
    {leftOutputs rightOutputs : ℕ}
    (fits : ({leftSite} + Multiset.ofList leftTakes) +
        ({rightSite} + Multiset.ofList rightTakes) +
        (Multiset.ofList rightReads).dedup ≤ bag) :
    List.Disjoint ((leftSite :: leftTakes) ++ slots leftSite leftOutputs)
      ((rightSite :: rightTakes) ++ rightReads ++ slots rightSite rightOutputs) := by
  let demandL := {leftSite} + Multiset.ofList leftTakes
  let demandR := {rightSite} + Multiset.ofList rightTakes
  let readR := (Multiset.ofList rightReads).dedup
  have leftLive : leftSite ∈ ledger.live :=
    covered _ (Multiset.mem_of_le (demand_le_bag fits)
      (Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton.mpr rfl))))
  have rightLive : rightSite ∈ ledger.live :=
    covered _ (Multiset.mem_of_le (later_demand_le_bag fits)
      (Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton.mpr rfl))))
  rw [List.disjoint_left]
  intro key inLeft inRight
  rcases List.mem_append.mp inLeft with inLeftConsume | inLeftProduce
  · rcases List.mem_append.mp inRight with inRightHead | inRightProduce
    · rcases List.mem_append.mp inRightHead with inRightConsume | inRightRead
      · exact count_clash distinct fits (mem_consume_keys inLeftConsume)
          (Or.inl (mem_consume_keys inRightConsume))
      · exact count_clash distinct fits (mem_consume_keys inLeftConsume)
          (Or.inr (mem_read_keys inRightRead))
    · have inSlots : key ∈ slots rightSite rightOutputs := inRightProduce
      unfold slots at inSlots
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp inSlots
      exact fresh_slot_outside ledger rightLive covered i
        (Multiset.mem_of_le (demand_le_bag fits) (mem_consume_keys inLeftConsume))
  · have inSlots : key ∈ slots leftSite leftOutputs := inLeftProduce
    unfold slots at inSlots
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp inSlots
    rcases List.mem_append.mp inRight with inRightHead | inRightProduce
    · rcases List.mem_append.mp inRightHead with inRightConsume | inRightRead
      · exact fresh_slot_outside ledger leftLive covered i
          (Multiset.mem_of_le (later_demand_le_bag fits) (mem_consume_keys inRightConsume))
      · exact fresh_slot_outside ledger leftLive covered i
          (Multiset.mem_of_le (seen_le_bag fits) (mem_read_keys inRightRead))
    · have otherSlots : leftSite ++ [i] ∈ slots rightSite rightOutputs := inRightProduce
      unfold slots at otherSlots
      obtain ⟨j, _, eq⟩ := List.mem_map.mp otherSlots
      obtain ⟨rfl, _⟩ := extension_eq.mp eq.symm
      exact count_clash distinct fits
        (Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton.mpr rfl)))
        (Or.inl (Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton.mpr rfl))))

/-- At a duplicate-free bag covered by the live allocation, an enabled
concurrent pair has frontier-independent accesses. Output slots of each live
row lie outside that bag. -/
theorem frontierIndependent_of_reachable (ledger : Ledger) {bag : Multiset Key}
    (covered : ∀ key ∈ bag, key ∈ ledger.live) (distinct : bag.Nodup)
    (left right : ground.Entry) (tile : ground.Concurrent bag left.2 right.2) :
    Mettapedia.Machines.CausalReceipt.ResourceFrontier.Independent
      (firingConsume left) (firingReads left) (firingSlots left)
      (firingConsume right) (firingReads right) (firingSlots right) := by
  have fitsRight :
      ({firingKey left} + Multiset.ofList left.2.takes) +
        ({firingKey right} + Multiset.ofList right.2.takes) +
        (Multiset.ofList right.2.reads).dedup ≤ bag := by
    change ground.consume left.2 + ground.consume right.2 + ground.read right.2 ≤ bag
    exact tile.2
  have rawLeft :
      ({firingKey left} + Multiset.ofList left.2.takes) +
        ({firingKey right} + Multiset.ofList right.2.takes) +
        (Multiset.ofList left.2.reads).dedup ≤ bag := by
    change ground.consume left.2 + ground.consume right.2 + ground.read left.2 ≤ bag
    exact tile.1
  have fitsLeft :
      ({firingKey right} + Multiset.ofList right.2.takes) +
        ({firingKey left} + Multiset.ofList left.2.takes) +
        (Multiset.ofList left.2.reads).dedup ≤ bag := by
    rw [add_comm ({firingKey left} + Multiset.ofList left.2.takes)
      ({firingKey right} + Multiset.ofList right.2.takes)] at rawLeft
    exact rawLeft
  exact ⟨
    one_sided_apart ledger covered distinct fitsRight,
    one_sided_apart ledger covered distinct fitsLeft⟩

/-- The selected row and footprint of one enabled event. -/
def tileEntry {bag : Multiset Key} (event : ground.presentation.Enabled bag) : ground.Entry :=
  ⟨event.site, ground.inst event⟩

/-- Frontier independence for the two events of one concurrency tile. -/
theorem frontierIndependent_of_tile (ledger : Ledger) {bag : Multiset Key}
    (covered : ∀ key ∈ bag, key ∈ ledger.live) (distinct : bag.Nodup)
    (pair : ground.concurrency.Pair bag) :
    Mettapedia.Machines.CausalReceipt.ResourceFrontier.Independent
      (firingConsume (tileEntry pair.first)) (firingReads (tileEntry pair.first))
      (firingSlots (tileEntry pair.first))
      (firingConsume (tileEntry pair.second)) (firingReads (tileEntry pair.second))
      (firingSlots (tileEntry pair.second)) :=
  frontierIndependent_of_reachable ledger covered distinct
    (tileEntry pair.first) (tileEntry pair.second) pair.independent

/-! ## The ledger after a successful replay

`ledgerAfter` is the allocation reached by selecting each row of a word.
A successful `replayWord` is what makes that walk defined: every selected row
was present in the bag that enabled it, and that bag stayed inside the live
keys. The resulting ledger is not a separate assumption. -/

def ledgerAfter (ledger : Ledger) : List ground.Entry → Option Ledger
  | [] => some ledger
  | entry :: rest =>
      if live : firingKey entry ∈ ledger.live then
        ledgerAfter (step_ledger ledger entry.2.outputs live) rest
      else
        none

/-- A successful replay determines the intermediate ledger.
The bag it reaches stays duplicate-free, and every key in that bag is live. -/
theorem replay_reachable (ledger : Ledger) (bag : Multiset Key)
    (covered : ∀ key ∈ bag, key ∈ ledger.live) (distinct : bag.Nodup) :
    ∀ (word : List ground.Entry)
      (result : Σ target : Multiset Key, OccurrencePath ground.presentation bag target),
      ground.replayWord word bag = some result →
        ∃ later : Ledger, ledgerAfter ledger word = some later ∧
          (∀ key ∈ result.1, key ∈ later.live) ∧ result.1.Nodup
  | [], result, replayed => by
      rw [ground.replayWord_nil] at replayed
      cases replayed
      exact ⟨ledger, rfl, covered, distinct⟩
  | entry :: rest, result, replayed => by
      cases flag : ground.enabledB bag entry with
      | false =>
          rw [ground.replayWord_cons_disabled entry rest bag flag] at replayed
          cases replayed
      | true =>
          have enabled : ground.Enables bag entry.2 :=
            (ground.enabledB_iff bag entry).mp flag
          have site_live : firingKey entry ∈ ledger.live := by
            have enabledK :
                ({firingKey entry} + Multiset.ofList entry.2.takes) +
                  (Multiset.ofList entry.2.reads).dedup ≤ bag := by
              change ground.consume entry.2 + ground.read entry.2 ≤ bag
              exact enabled
            have consume_le :
                ({firingKey entry} + Multiset.ofList entry.2.takes) ≤ bag :=
              le_trans (Multiset.le_add_right _ _) enabledK
            exact covered _
              (Multiset.mem_of_le consume_le
                (Multiset.mem_add.mpr (Or.inl <| Multiset.mem_singleton.mpr rfl)))
          rw [ground.replayWord_cons_enabled entry rest bag flag] at replayed
          cases continued : ground.replayWord rest (ground.fire bag entry.2) with
          | none =>
              rw [continued] at replayed
              cases replayed
          | some tail =>
              rw [continued] at replayed
              cases replayed
              let laterLedger := step_ledger ledger entry.2.outputs site_live
              have preserved :=
                fired_preserves ledger entry.2 site_live bag covered distinct
              obtain ⟨later, after, coveredLater, distinctLater⟩ :=
                replay_reachable laterLedger (ground.fire bag entry.2)
                  preserved.1 preserved.2 rest tail continued
              refine ⟨later, ?_, coveredLater, distinctLater⟩
              have afterStep :
                  ledgerAfter ledger (entry :: rest) =
                    ledgerAfter laterLedger rest := by
                conv =>
                  lhs
                  unfold ledgerAfter
                exact dif_pos site_live
              exact afterStep.trans after

/-- The tile's two routes are the two ordered firing words. -/
theorem tile_ordered_words {bag : Multiset Key} (pair : ground.concurrency.Pair bag) :
    ground.pathEntries (pair.route ground.concurrency) =
      [tileEntry pair.first, tileEntry pair.second] ∧
    ground.pathEntries (pair.swapped ground.concurrency) =
      [tileEntry pair.second, tileEntry pair.first] := by
  refine ⟨rfl, Eq.trans
    (ground.pathEntries_cast (ground.concurrency.close pair.independent).symm
      (.cons (Concurrency.occ pair.second)
        (.cons (Concurrency.occ (ground.concurrency.residual
            (ground.concurrency.symm pair.independent)))
          (.refl (P := ground.presentation) _))))
    rfl⟩

/-- Frontier separation of two firing entries. This is the swap condition
`CausalGluing.resourceFrontier_dependencyView_invariant` reads. -/
abbrev frontierSeparate (left right : ground.Entry) : Prop :=
  Mettapedia.Machines.CausalReceipt.ResourceFrontier.Independent
    (firingConsume left) (firingReads left) (firingSlots left)
    (firingConsume right) (firingReads right) (firingSlots right)

/-- A successful prefix reaches the tile's bag, so the two ordered routes are
one frontier swap inside an arbitrary suffix. The intermediate ledger is the
one `replay_reachable` returns. -/
theorem replay_tile_swap
    {roots : List Key} (distinct : roots.Nodup)
    (idx : ∀ key ∈ roots, key.length = 1)
    (earlier suffix : List ground.Entry) {bag : Multiset Key}
    {prefixPath : OccurrencePath ground.presentation (Multiset.ofList roots) bag}
    (prefixReplay :
      ground.replayWord earlier (Multiset.ofList roots) = some ⟨bag, prefixPath⟩)
    (pair : ground.concurrency.Pair bag) :
    Mettapedia.GSLT.Distinction.CausalGluing.TraceEquiv frontierSeparate
      (earlier ++ ground.pathEntries (pair.route ground.concurrency) ++ suffix)
      (earlier ++ ground.pathEntries (pair.swapped ground.concurrency) ++ suffix) := by
  let rootsLedger := ledger_roots roots distinct idx
  have coveredRoots : ∀ key ∈ Multiset.ofList roots, key ∈ rootsLedger.live := by
    intro key member
    exact Multiset.mem_coe.mp member
  obtain ⟨atBag, _, covered, nodup⟩ :=
    replay_reachable rootsLedger (Multiset.ofList roots) coveredRoots
      (Multiset.coe_nodup.mpr distinct) earlier ⟨bag, prefixPath⟩ prefixReplay
  have words := tile_ordered_words pair
  have separate := frontierIndependent_of_tile atBag covered nodup pair
  have forward :
      earlier ++ ground.pathEntries (pair.route ground.concurrency) ++ suffix =
        earlier ++ tileEntry pair.first :: tileEntry pair.second :: suffix := by
    rw [words.1, List.append_assoc]
    rfl
  have backward :
      earlier ++ ground.pathEntries (pair.swapped ground.concurrency) ++ suffix =
        earlier ++ tileEntry pair.second :: tileEntry pair.first :: suffix := by
    rw [words.2, List.append_assoc]
    rfl
  rw [forward, backward]
  exact Relation.EqvGen.rel _ _
    (Mettapedia.GSLT.Distinction.CausalGluing.Swap.swap earlier suffix separate)

/-- The forward ordered word replays: the prefix, then the tile route, then
the suffix from the route's target. -/
theorem replay_tile_forward
    {roots : List Key}
    (earlier suffix : List ground.Entry) {bag : Multiset Key}
    {prefixPath : OccurrencePath ground.presentation (Multiset.ofList roots) bag}
    (prefixReplay :
      ground.replayWord earlier (Multiset.ofList roots) = some ⟨bag, prefixPath⟩)
    (pair : ground.concurrency.Pair bag)
    {final : Multiset Key}
    {suffixPath :
      OccurrencePath ground.presentation
        (ground.concurrency.residual pair.independent).target final}
    (suffixReplay :
      ground.replayWord suffix
        (ground.concurrency.residual pair.independent).target =
        some ⟨final, suffixPath⟩) :
    (ground.replayWord
      (earlier ++ ground.pathEntries (pair.route ground.concurrency) ++ suffix)
      (Multiset.ofList roots)).isSome := by
  let packed {source target : Multiset Key}
      (path : OccurrencePath ground.presentation source target) :
      Σ finished : Multiset Key, OccurrencePath ground.presentation source finished :=
    ⟨target, path⟩
  have joined :
      ground.replayWord
        (earlier ++ ground.pathEntries (pair.route ground.concurrency))
        (Multiset.ofList roots) =
      some (packed (prefixPath.append (pair.route ground.concurrency))) := by
    rw [ground.replayWord_append, prefixReplay]
    change
      (ground.replayWord (ground.pathEntries (pair.route ground.concurrency)) bag).map
          (fun rightPath => packed (prefixPath.append rightPath.2)) =
        some (packed (prefixPath.append (pair.route ground.concurrency)))
    exact
      (congrArg
          (Option.map fun rightPath => packed (prefixPath.append rightPath.2))
          (ground.replayWord_of_path (pair.route ground.concurrency))).trans
        rfl
  have forwardReplay :
      ground.replayWord
        (earlier ++ ground.pathEntries (pair.route ground.concurrency) ++ suffix)
        (Multiset.ofList roots) =
      some (packed
        ((prefixPath.append (pair.route ground.concurrency)).append suffixPath)) := by
    rw [ground.replayWord_append, joined]
    change
      (ground.replayWord suffix (ground.concurrency.residual pair.independent).target).map
          (fun rightPath =>
            packed
              ((prefixPath.append (pair.route ground.concurrency)).append rightPath.2)) =
        some (packed
          ((prefixPath.append (pair.route ground.concurrency)).append suffixPath))
    exact
      (congrArg
          (Option.map fun rightPath =>
            packed
              ((prefixPath.append (pair.route ground.concurrency)).append rightPath.2))
          suffixReplay).trans
        rfl
  exact forwardReplay ▸ rfl

/-- The two ordered words have one dependency view. Both checked projections
are the frontier receipt of that word. Freshness of the forward word comes
from its replay; freshness of the swapped word comes from the trace
permutation. -/
theorem replay_tile_project
    {roots : List Key} (distinct : roots.Nodup)
    (idx : ∀ key ∈ roots, key.length = 1)
    (earlier suffix : List ground.Entry) {bag : Multiset Key}
    {prefixPath : OccurrencePath ground.presentation (Multiset.ofList roots) bag}
    (prefixReplay :
      ground.replayWord earlier (Multiset.ofList roots) = some ⟨bag, prefixPath⟩)
    (pair : ground.concurrency.Pair bag)
    {final : Multiset Key}
    {suffixPath :
      OccurrencePath ground.presentation
        (ground.concurrency.residual pair.independent).target final}
    (suffixReplay :
      ground.replayWord suffix
        (ground.concurrency.residual pair.independent).target =
        some ⟨final, suffixPath⟩) :
    let forward :=
      earlier ++ ground.pathEntries (pair.route ground.concurrency) ++ suffix
    let backward :=
      earlier ++ ground.pathEntries (pair.swapped ground.concurrency) ++ suffix
    (Mettapedia.Machines.CausalReceipt.ResourceFrontier.receipt
        firingKey firingConsume firingReads firingSlots forward).dependencyView =
      (Mettapedia.Machines.CausalReceipt.ResourceFrontier.receipt
        firingKey firingConsume firingReads firingSlots backward).dependencyView ∧
    (project forward).map Mettapedia.Machines.CausalReceipt.dependencyView =
      (project backward).map Mettapedia.Machines.CausalReceipt.dependencyView ∧
    project forward =
      some (Mettapedia.Machines.CausalReceipt.ResourceFrontier.receipt
        firingKey firingConsume firingReads firingSlots forward) ∧
    project backward =
      some (Mettapedia.Machines.CausalReceipt.ResourceFrontier.receipt
        firingKey firingConsume firingReads firingSlots backward) := by
  intro forward backward
  have swap := replay_tile_swap distinct idx earlier suffix prefixReplay pair
  have replayed :=
    replay_tile_forward earlier suffix prefixReplay pair suffixReplay
  let rootsLedger := ledger_roots roots distinct idx
  have coveredRoots : ∀ key ∈ Multiset.ofList roots, key ∈ rootsLedger.live := by
    intro key member
    exact Multiset.mem_coe.mp member
  have freshForward : (forward.map firingKey).Nodup := by
    have allocated :=
      replay_allocated rootsLedger (Multiset.ofList roots) coveredRoots
        (Multiset.coe_nodup.mpr distinct) forward replayed
    exact legitimate_sites_nodup ⟨distinct, idx, allocated⟩
  have freshBackward : (backward.map firingKey).Nodup :=
    (List.Perm.nodup_iff
      ((Mettapedia.GSLT.Distinction.CausalGluing.TraceEquiv.perm swap).map firingKey)).mp
      freshForward
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Mettapedia.GSLT.Distinction.CausalGluing.resourceFrontier_dependencyView_invariant
      firingKey firingConsume firingReads firingSlots swap
  · exact Mettapedia.GSLT.Distinction.CausalGluing.resourceFrontier_checkedView_invariant
      firingKey firingConsume firingReads firingSlots swap
  · exact project_of_replay distinct idx replayed
  · unfold project
    unfold Mettapedia.Machines.CausalReceipt.ResourceFrontier.receipt?
    exact if_pos freshBackward

/-- Declared work and dependency span agree on those two words. The cost is
read from the shared dependency view. -/
theorem replay_tile_readout
    {roots : List Key} (distinct : roots.Nodup)
    (idx : ∀ key ∈ roots, key.length = 1)
    (earlier suffix : List ground.Entry) {bag : Multiset Key}
    {prefixPath : OccurrencePath ground.presentation (Multiset.ofList roots) bag}
    (prefixReplay :
      ground.replayWord earlier (Multiset.ofList roots) = some ⟨bag, prefixPath⟩)
    (pair : ground.concurrency.Pair bag)
    {final : Multiset Key}
    {suffixPath :
      OccurrencePath ground.presentation
        (ground.concurrency.residual pair.independent).target final}
    (suffixReplay :
      ground.replayWord suffix
        (ground.concurrency.residual pair.independent).target =
        some ⟨final, suffixPath⟩)
    (cost : Key → Mettapedia.Algebra.WorkSpan) :
    (Mettapedia.Machines.CausalReceipt.ResourceFrontier.receipt
        firingKey firingConsume firingReads firingSlots
        (earlier ++ ground.pathEntries (pair.route ground.concurrency) ++ suffix)).dependencyReadout
      cost =
    (Mettapedia.Machines.CausalReceipt.ResourceFrontier.receipt
        firingKey firingConsume firingReads firingSlots
        (earlier ++ ground.pathEntries (pair.swapped ground.concurrency) ++ suffix)).dependencyReadout
      cost := by
  have replayed :=
    replay_tile_forward earlier suffix prefixReplay pair suffixReplay
  let rootsLedger := ledger_roots roots distinct idx
  have coveredRoots : ∀ key ∈ Multiset.ofList roots, key ∈ rootsLedger.live := by
    intro key member
    exact Multiset.mem_coe.mp member
  have fresh :=
    legitimate_sites_nodup ⟨distinct, idx,
      replay_allocated rootsLedger (Multiset.ofList roots) coveredRoots
        (Multiset.coe_nodup.mpr distinct)
        (earlier ++ ground.pathEntries (pair.route ground.concurrency) ++ suffix)
        replayed⟩
  exact Mettapedia.GSLT.Distinction.CausalGluing.resourceFrontier_dependencyReadout_invariant
    firingKey firingConsume firingReads firingSlots cost fresh
    (replay_tile_swap distinct idx earlier suffix prefixReplay pair)

/-! ## Payload admission

The resource word stays a footprint projection. These definitions do not treat
that footprint as the meaning of `exec`. The action decoder reads one
`OSLFCore.Atom` and accepts only the `exec` / `I` / `O` shape, with ordered
`read` or `take` premises and ordered `+` sinks. Physical keys come from the
aligned resource entry. Produced row identities are the entry site extended
by each output slot.

`admitWord` on a shorter aligned word is that prefix's rows. A missing firing
is a payload mismatch only when those rows are not the claimed final rows.
An absent payload section is not a call to this API. -/

open Mettapedia.Languages.MeTTa.OSLFCore

inductive PremiseKind where
  | read
  | take
  deriving DecidableEq, Repr

structure PayloadRow where
  key : Key
  value : Atom
  deriving DecidableEq, Repr

/-- One ordered premise. Its key is the aligned resource entry's key. -/
structure DecodedPremise where
  kind : PremiseKind
  key : Key
  value : Atom
  deriving DecidableEq, Repr

/-- The exec/I/O view of an action atom. This view contains no physical keys. -/
structure ExecIO where
  inputs : List (PremiseKind × Atom)
  outputs : List Atom
  deriving DecidableEq, Repr

/-- One payload claim aligned with one resource entry. -/
structure PayloadClaim where
  action : Atom
  inputs : List DecodedPremise
  produced : List PayloadRow
  deriving DecidableEq, Repr

def premiseAtom? : Atom → Option (PremiseKind × Atom)
  | .expression [.symbol "read", value] => some (.read, value)
  | .expression [.symbol "take", value] => some (.take, value)
  | _ => none

def sinkAtom? : Atom → Option Atom
  | .expression [.symbol "+", value] => some value
  | _ => none

/-- Admit an action atom only when it is `exec`, an `I` premise list, and an
`O` sink list. The head between `exec` and `I` is not interpreted. -/
def decodeExec : Atom → Option ExecIO
  | .expression [.symbol "exec", _, .expression inputs, .expression outputs] =>
    match inputs, outputs with
    | .symbol "I" :: premises, .symbol "O" :: sinks =>
      match premises.mapM premiseAtom?, sinks.mapM sinkAtom? with
      | some decodedInputs, some decodedOutputs =>
        some { inputs := decodedInputs, outputs := decodedOutputs }
      | _, _ => none
    | _, _ => none
  | _ => none

def initialRows (values : List Atom) : List PayloadRow :=
  (List.range values.length).zipWith (fun index value => ⟨[index], value⟩) values

def rowValue (rows : List PayloadRow) (key : Key) : Option Atom :=
  rows.findSome? fun row => if row.key = key then some row.value else none

def derivedProduces (site : Key) (values : List Atom) : List PayloadRow :=
  (slots site values.length).zipWith (fun key value => ⟨key, value⟩) values

def dropConsumed (rows : List PayloadRow) (site : Key) (takes : List Key) :
    List PayloadRow :=
  rows.filter fun row => decide (row.key ≠ site ∧ row.key ∉ takes)

def premiseKeys (kind : PremiseKind) (inputs : List DecodedPremise) : List Key :=
  (inputs.filter fun input => input.kind = kind).map fun input => input.key

def payloadsMatch (rows : List PayloadRow) (inputs : List DecodedPremise) : Bool :=
  inputs.all fun input =>
    match rowValue rows input.key with
    | some found => decide (found = input.value)
    | none => false

/-- Admit one firing. The resource entry supplies the selected key, the take
keys, the read keys, and the output count. The next rows append the derived
slot identities, not an arbitrary key list. -/
def admitFiring (rows : List PayloadRow) (entry : ground.Entry)
    (claim : PayloadClaim) : Option (List PayloadRow) :=
  match rowValue rows (firingKey entry), decodeExec claim.action with
  | some live, some view =>
    let derived := derivedProduces (firingKey entry) view.outputs
    if decide (live = claim.action) &&
        decide (view.inputs =
          claim.inputs.map fun input => (input.kind, input.value)) &&
        decide (view.outputs = claim.produced.map fun row => row.value) &&
        decide (claim.produced = derived) &&
        decide (premiseKeys .take claim.inputs = entry.2.takes) &&
        decide (premiseKeys .read claim.inputs = entry.2.reads) &&
        decide (entry.2.outputs = view.outputs.length) &&
        payloadsMatch rows claim.inputs then
      some (dropConsumed rows (firingKey entry) entry.2.takes ++ derived)
    else
      none
  | _, _ => none

/-- Replay an aligned word. Both lists shorten together on a valid prefix.
Unequal lengths are a broken alignment, not a prefix. -/
def admitWord : List PayloadRow → List ground.Entry → List PayloadClaim →
    Option (List PayloadRow)
  | rows, [], [] => some rows
  | rows, entry :: entries, claim :: claims =>
    match admitFiring rows entry claim with
    | some next => admitWord next entries claims
    | none => none
  | _, _, _ => none

/-- Separate payload verdict. `false` covers a failed step and a reached row
list that is not the claimed final list. -/
def sourcePayloadMatches (reached : Option (List PayloadRow))
    (claimed : List PayloadRow) : Bool :=
  match reached with
  | some rows => decide (rows = claimed)
  | none => false

/-! Payload admission preserves the physical resource interpretation. These
laws do not grant availability or execution authority: successful resource
replay supplies those independent source obligations. -/

theorem mem_dropConsumed_keys (rows : List PayloadRow) (site key : Key) (takes : List Key) :
    key ∈ (dropConsumed rows site takes).map PayloadRow.key ↔
      key ∈ rows.map PayloadRow.key ∧ key ≠ site ∧ key ∉ takes := by
  simp only [dropConsumed, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨row, ⟨member, apart⟩, rfl⟩
    exact ⟨⟨row, member, rfl⟩, apart⟩
  · rintro ⟨⟨row, member, rfl⟩, apart⟩
    exact ⟨row, ⟨member, apart⟩, rfl⟩

theorem dropConsumed_keys_bag (rows : List PayloadRow) (site : Key) (takes : List Key)
    (distinct : (rows.map PayloadRow.key).Nodup) :
    (Multiset.ofList ((dropConsumed rows site takes).map PayloadRow.key)) =
      (Multiset.ofList (rows.map PayloadRow.key)) -
        ({site} + Multiset.ofList takes) := by
  have filtered : ((dropConsumed rows site takes).map PayloadRow.key).Nodup := by
    exact List.Nodup.sublist (List.Sublist.map PayloadRow.key List.filter_sublist) distinct
  apply (Multiset.Nodup.ext (Multiset.coe_nodup.mpr filtered)
    (Multiset.nodup_of_le (Multiset.sub_le_self _ _) (Multiset.coe_nodup.mpr distinct))).mpr
  intro key
  rw [Multiset.mem_sub_of_nodup (Multiset.coe_nodup.mpr distinct)]
  simp only [Multiset.mem_coe, Multiset.mem_add, Multiset.mem_singleton]
  rw [mem_dropConsumed_keys]
  tauto

theorem admitFiring_facts (rows : List PayloadRow) (entry : ground.Entry)
    (claim : PayloadClaim) (next : List PayloadRow)
    (admitted : admitFiring rows entry claim = some next) :
    ∃ view : ExecIO,
      rowValue rows (firingKey entry) = some claim.action ∧
      decodeExec claim.action = some view ∧
      view.inputs = claim.inputs.map (fun input => (input.kind, input.value)) ∧
      claim.produced = derivedProduces (firingKey entry) view.outputs ∧
      premiseKeys .take claim.inputs = entry.2.takes ∧
      premiseKeys .read claim.inputs = entry.2.reads ∧
      entry.2.outputs = view.outputs.length ∧
      payloadsMatch rows claim.inputs = true ∧
      next = dropConsumed rows (firingKey entry) entry.2.takes ++
        derivedProduces (firingKey entry) view.outputs := by
  rcases entry with ⟨site, footprint⟩
  change Key at site
  change Footprint site at footprint
  unfold admitFiring at admitted
  simp only [firingKey] at admitted ⊢
  cases found : rowValue rows site with
  | none => simp only [found] at admitted; contradiction
  | some live =>
    cases decoded : decodeExec claim.action with
    | none => simp only [found, decoded] at admitted; contradiction
    | some view =>
      rw [found, decoded] at admitted
      dsimp only at admitted
      have parts := Option.ite_some_none_eq_some.mp admitted
      have permitted := parts.1
      simp only [Bool.and_eq_true, decide_eq_true_eq] at permitted
      have same : live = claim.action := by tauto
      refine ⟨view, congrArg some same, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · tauto
      · exact of_decide_eq_true (by tauto)
      · tauto
      · tauto
      · tauto
      · tauto
      · exact parts.2.symm

private theorem zipWith_left_projection {A B : Type} (keys : List A) (values : List B)
    (enough : keys.length ≤ values.length) :
    List.zipWith (fun key _ => key) keys values = keys := by
  induction keys generalizing values with
  | nil => rfl
  | cons key keys ih =>
    cases values with
    | nil => simp at enough
    | cons value values =>
      simp only [List.length_cons, Nat.add_le_add_iff_right] at enough
      simpa only [List.zipWith_cons_cons, List.cons.injEq, true_and] using ih values enough

theorem derivedProduces_keys (site : Key)
    (values : List Mettapedia.Languages.MeTTa.OSLFCore.Atom) :
    (derivedProduces site values).map PayloadRow.key = slots site values.length := by
  unfold derivedProduces
  rw [List.map_zipWith]
  exact zipWith_left_projection _ _ (by simp [slots])

theorem admitFiring_keys (rows : List PayloadRow) (entry : ground.Entry)
    (claim : PayloadClaim) (next : List PayloadRow)
    (distinct : (rows.map PayloadRow.key).Nodup)
    (admitted : admitFiring rows entry claim = some next) :
    Multiset.ofList (next.map PayloadRow.key) =
      ground.fire (Multiset.ofList (rows.map PayloadRow.key)) entry.2 := by
  rcases entry with ⟨site, footprint⟩
  change Key at site
  change Footprint site at footprint
  obtain ⟨view, _, _, _, _, _, _, outputs, _, nextEq⟩ :=
    admitFiring_facts rows ⟨site, footprint⟩ claim next admitted
  rw [nextEq, List.map_append, ← Multiset.coe_add, dropConsumed_keys_bag rows _ _ distinct,
    derivedProduces_keys, fire_eq footprint]
  rw [outputs]
  rfl

/-- A lookup reads an actual physical row; it cannot invent its payload. -/
theorem rowValue_present {rows : List PayloadRow} {key : Key} {value : Atom}
    (found : rowValue rows key = some value) :
    ∃ row ∈ rows, row.key = key ∧ row.value = value := by
  obtain ⟨row, member, selected⟩ := List.exists_of_findSome?_eq_some found
  by_cases same : row.key = key
  · simp only [same, if_pos, Option.some.injEq] at selected
    exact ⟨row, member, same, selected⟩
  · simp only [same, if_false] at selected
    contradiction

/-- Ordered premise claims refer to rows with the requested literal payload. -/
theorem payloadsMatch_present {rows : List PayloadRow} {inputs : List DecodedPremise}
    (matched : payloadsMatch rows inputs = true) :
    ∀ input ∈ inputs, ∃ row ∈ rows, row.key = input.key ∧ row.value = input.value := by
  intro input member
  have accepted := (List.all_eq_true.mp matched) input member
  cases found : rowValue rows input.key with
  | none => simp only [found] at accepted; contradiction
  | some value =>
    have same : value = input.value := of_decide_eq_true (by simpa only [found] using accepted)
    exact rowValue_present (same ▸ found)

/-- Ground payload semantics. Resource availability is checked separately by
resource replay of the same aligned entry; this relation grants no authority. -/
inductive PayloadTransition (rows : List PayloadRow) (entry : ground.Entry)
    (claim : PayloadClaim) : List PayloadRow → Prop where
  | fire (view : ExecIO)
      (selected : ∃ row ∈ rows, row.key = firingKey entry ∧ row.value = claim.action)
      (shape : decodeExec claim.action = some view)
      (ordered : view.inputs = claim.inputs.map (fun input => (input.kind, input.value)))
      (premises : ∀ input ∈ claim.inputs,
        ∃ row ∈ rows, row.key = input.key ∧ row.value = input.value)
      (takes : premiseKeys .take claim.inputs = entry.2.takes)
      (reads : premiseKeys .read claim.inputs = entry.2.reads)
      (outputs : entry.2.outputs = view.outputs.length)
      (produced : claim.produced = derivedProduces (firingKey entry) view.outputs) :
      PayloadTransition rows entry claim
        (dropConsumed rows (firingKey entry) entry.2.takes ++ claim.produced)

theorem admitFiring_sound {rows : List PayloadRow} {entry : ground.Entry}
    {claim : PayloadClaim} {next : List PayloadRow}
    (admitted : admitFiring rows entry claim = some next) :
    PayloadTransition rows entry claim next := by
  obtain ⟨view, selected, shape, ordered, produced, takes, reads, outputs, matched, nextEq⟩ :=
    admitFiring_facts rows entry claim next admitted
  rw [nextEq, ← produced]
  exact .fire view (rowValue_present selected) shape ordered
    (payloadsMatch_present matched) takes reads outputs produced

inductive PayloadRun : List PayloadRow → List ground.Entry → List PayloadClaim →
    List PayloadRow → Prop where
  | nil (rows : List PayloadRow) : PayloadRun rows [] [] rows
  | cons {rows next final : List PayloadRow} {entry : ground.Entry}
      {entries : List ground.Entry} {claim : PayloadClaim} {claims : List PayloadClaim}
      (head : PayloadTransition rows entry claim next)
      (tail : PayloadRun next entries claims final) :
      PayloadRun rows (entry :: entries) (claim :: claims) final

theorem admitWord_sound : ∀ (rows : List PayloadRow) (word : List ground.Entry)
    (claims : List PayloadClaim) (final : List PayloadRow),
    admitWord rows word claims = some final → PayloadRun rows word claims final
  | rows, [], [], final, admitted => by
    simp only [admitWord, Option.some.injEq] at admitted
    subst final
    exact .nil rows
  | _, [], _ :: _, _, admitted => by simp only [admitWord] at admitted; contradiction
  | _, _ :: _, [], _, admitted => by simp only [admitWord] at admitted; contradiction
  | rows, entry :: entries, claim :: claims, final, admitted => by
    cases first : admitFiring rows entry claim with
    | none => simp only [admitWord, first] at admitted; contradiction
    | some next =>
      exact .cons (admitFiring_sound first)
        (admitWord_sound next entries claims final (by simpa only [admitWord, first] using admitted))

/-! ## Admitted words and resource replay

`PayloadRun` records the payload atoms. The theorems here record only the
physical keys. A successful `admitWord` from `initialRows` and a successful
`ground.replayWord` from that key bag end on the same key multiset. Coverage
and duplicate-freedom start from the indexed roots and are maintained by
`fired_preserves`. -/

private theorem zipWith_map_left {α β γ : Type} (f : α → γ) :
    ∀ (keys : List α) (values : List β), keys.length ≤ values.length →
      List.zipWith (fun key _ => f key) keys values = keys.map f
  | [], _, _ => rfl
  | _ :: _, [], enough => by
      rw [List.length_cons] at enough
      exact absurd enough (Nat.not_succ_le_zero _)
  | key :: keys, _ :: values, enough => by
      rw [List.length_cons, List.length_cons, Nat.succ_le_succ_iff] at enough
      rw [List.zipWith_cons_cons, List.map_cons, zipWith_map_left f keys values enough]

theorem initialRows_keys (values : List Atom) :
    (initialRows values).map PayloadRow.key =
      (List.range values.length).map (fun index => [index]) := by
  unfold initialRows
  rw [List.map_zipWith]
  exact zipWith_map_left (fun index => [index]) (List.range values.length) values
    (Nat.le_of_eq List.length_range)

theorem initialRows_key_nodup (values : List Atom) :
    ((initialRows values).map PayloadRow.key).Nodup := by
  rw [initialRows_keys]
  exact List.Nodup.map
    (fun i j eq => (List.cons_eq_cons.mp eq).1)
    (List.nodup_range (n := values.length))

theorem initialRows_key_length (values : List Atom) :
    ∀ key ∈ (initialRows values).map PayloadRow.key, key.length = 1 := by
  rw [initialRows_keys]
  intro key member
  rcases List.mem_map.mp member with ⟨_, _, rfl⟩
  rfl

/-- Payload keys follow `ground.fire` for one whole word. The ledger is the
reachable allocation: each bag stays inside `ledger.live`, and
`fired_preserves` supplies the next coverage and duplicate-freedom. -/
theorem admitWord_tracks_replay
    (ledger : Ledger) {bag : Multiset Key}
    (covered : ∀ key ∈ bag, key ∈ ledger.live) (distinct : bag.Nodup)
    {rows : List PayloadRow}
    (aligned : Multiset.ofList (rows.map PayloadRow.key) = bag) :
    ∀ (entries : List ground.Entry) (claims : List PayloadClaim)
      {final : List PayloadRow},
      admitWord rows entries claims = some final →
      ∀ result : Σ target : Multiset Key,
        OccurrencePath ground.presentation bag target,
        ground.replayWord entries bag = some result →
          Multiset.ofList (final.map PayloadRow.key) = result.1
  | [], [], final, admitted, result, replayed => by
      unfold admitWord at admitted
      cases admitted
      rw [ground.replayWord_nil] at replayed
      cases replayed
      exact aligned
  | [], _ :: _, _, admitted, _, _ => by
      unfold admitWord at admitted
      cases admitted
  | _ :: _, [], _, admitted, _, _ => by
      unfold admitWord at admitted
      cases admitted
  | entry :: entries, claim :: claims, final, admitted, result, replayed => by
      unfold admitWord at admitted
      cases first : admitFiring rows entry claim with
      | none =>
          rw [first] at admitted
          dsimp only at admitted
          cases admitted
      | some next =>
          rw [first] at admitted
          dsimp only at admitted
          cases flag : ground.enabledB bag entry with
          | false =>
              rw [ground.replayWord_cons_disabled entry entries bag flag] at replayed
              cases replayed
          | true =>
              have enabled : ground.Enables bag entry.2 :=
                (ground.enabledB_iff bag entry).mp flag
              have site_live : firingKey entry ∈ ledger.live := by
                have enabledK :
                    ({firingKey entry} + Multiset.ofList entry.2.takes) +
                      (Multiset.ofList entry.2.reads).dedup ≤ bag := by
                  change ground.consume entry.2 + ground.read entry.2 ≤ bag
                  exact enabled
                have consume_le :
                    ({firingKey entry} + Multiset.ofList entry.2.takes) ≤ bag :=
                  le_trans (Multiset.le_add_right _ _) enabledK
                exact covered _
                  (Multiset.mem_of_le consume_le
                    (Multiset.mem_add.mpr (Or.inl <| Multiset.mem_singleton.mpr rfl)))
              rw [ground.replayWord_cons_enabled entry entries bag flag] at replayed
              cases continued :
                  ground.replayWord entries (ground.fire bag entry.2) with
              | none =>
                  rw [continued] at replayed
                  cases replayed
              | some tail =>
                  rw [continued] at replayed
                  cases replayed
                  have rowNodup : (rows.map PayloadRow.key).Nodup :=
                    Multiset.coe_nodup.mp (aligned ▸ distinct)
                  have keyEq :=
                    admitFiring_keys rows entry claim next rowNodup first
                  rw [aligned] at keyEq
                  let laterLedger := step_ledger ledger entry.2.outputs site_live
                  have preserved :=
                    fired_preserves ledger entry.2 site_live bag covered distinct
                  exact admitWord_tracks_replay laterLedger preserved.1 preserved.2
                    keyEq entries claims admitted tail continued

/-- Initial singleton rows and a resource replay of the same entries finish
with the same physical key bag. -/
theorem initialRows_replay_keys (values : List Atom)
    (entries : List ground.Entry) (claims : List PayloadClaim)
    {final : List PayloadRow}
    (admitted : admitWord (initialRows values) entries claims = some final)
    {result : Σ target : Multiset Key,
      OccurrencePath ground.presentation
        (Multiset.ofList ((initialRows values).map PayloadRow.key)) target}
    (replayed : ground.replayWord entries
        (Multiset.ofList ((initialRows values).map PayloadRow.key)) = some result) :
    Multiset.ofList (final.map PayloadRow.key) = result.1 := by
  let roots := (initialRows values).map PayloadRow.key
  have distinctRoots : roots.Nodup := initialRows_key_nodup values
  have indexed : ∀ key ∈ roots, key.length = 1 := initialRows_key_length values
  let rootsLedger := ledger_roots roots distinctRoots indexed
  have covered : ∀ key ∈ Multiset.ofList roots, key ∈ rootsLedger.live := by
    intro key member
    exact Multiset.mem_coe.mp member
  exact admitWord_tracks_replay rootsLedger covered
    (Multiset.coe_nodup.mpr distinctRoots) rfl entries claims admitted result replayed

end Mettapedia.GSLT.Causality.ResourceInteraction.GroundBag
