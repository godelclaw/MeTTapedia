import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.EvidenceBorder.WaveTranslation

/-!
# An observation is a trial with its outcome

`countsEachOnce` is `List.Nodup` on Boolean values, so it refuses two trials
that both come out true. A wave counts each observation once when no two
published proposals carry one trial. Under that condition the count of the
wave is the count of the set of its observations, for any number of true
outcomes. Without it the count exceeds the set count by the number of repeated
publications. A policy that keeps one proposal per trial counts each
observation once on every wave, whichever sibling it keeps.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.EvidenceBorder

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.Controls
open Mettapedia.Logic.EvidenceStateInsufficiency

/-- An observation: one trial together with the Boolean outcome it returned. -/
structure Observation where
  trial : Nat
  outcome : Bool
deriving DecidableEq, Repr

/-- Keep `observation` when its trial is not already in `kept`. -/
def absorb (kept : List Observation) (observation : Observation) : List Observation :=
  if kept.any (fun earlier => earlier.trial == observation.trial) then kept
  else kept ++ [observation]

/-- The set of observations: the first publication of each trial, in order. -/
def keepFirstObservation (observations : List Observation) : List Observation :=
  observations.foldl absorb []

/-- No two observations in the list carry one trial. -/
def countsEachTrialOnce (observations : List Observation) : Prop :=
  (observations.map (·.trial)).Nodup

theorem absorb_nodup (kept : List Observation) (observation : Observation)
    (nodup : (kept.map (·.trial)).Nodup) :
    ((absorb kept observation).map (·.trial)).Nodup := by
  unfold absorb
  by_cases duplicate : kept.any (fun earlier => earlier.trial == observation.trial) = true
  · rw [if_pos duplicate]
    exact nodup
  · rw [if_neg duplicate, List.map_append, List.map_singleton]
    refine List.nodup_append.mpr ⟨nodup, List.nodup_singleton _, ?_⟩
    intro a inKept b inNew hab
    have hb : b = observation.trial := List.eq_of_mem_singleton inNew
    subst hb
    subst hab
    obtain ⟨earlier, member, same⟩ := List.mem_map.mp inKept
    have marked :
        kept.any (fun earlier => earlier.trial == observation.trial) = true :=
      List.any_eq_true.mpr ⟨earlier, member, beq_iff_eq.mpr same⟩
    exact duplicate marked

theorem foldl_absorb_nodup (observations kept : List Observation)
    (nodup : (kept.map (·.trial)).Nodup) :
    ((observations.foldl absorb kept).map (·.trial)).Nodup := by
  induction observations generalizing kept with
  | nil => simpa using nodup
  | cons observation rest ih =>
    rw [List.foldl_cons]
    exact ih _ (absorb_nodup kept observation nodup)

/-- **Positive.** The first publication of each trial carries that trial once. -/
theorem keepFirst_trials_nodup (observations : List Observation) :
    countsEachTrialOnce (keepFirstObservation observations) := by
  simpa [countsEachTrialOnce, keepFirstObservation] using
    foldl_absorb_nodup observations [] List.nodup_nil

/-- **Negative.** Dropping the second publication of a trial is not the list
that published it twice. -/
theorem keepFirst_drops_repeat :
    keepFirstObservation [⟨0, true⟩, ⟨0, true⟩] = [⟨0, true⟩] ∧
      keepFirstObservation [⟨0, true⟩, ⟨0, true⟩] ≠ [⟨0, true⟩, ⟨0, true⟩] := by
  decide

theorem foldl_absorb_eq (observations kept : List Observation)
    (nodup : ((kept ++ observations).map (·.trial)).Nodup) :
    observations.foldl absorb kept = kept ++ observations := by
  induction observations generalizing kept with
  | nil => simp
  | cons observation rest ih =>
    have splitNodup := List.nodup_append.mp (by
      simpa [List.map_append, List.map_cons] using nodup)
    have headFresh : observation.trial ∉ kept.map (·.trial) :=
      fun member =>
        splitNodup.2.2 observation.trial member observation.trial List.mem_cons_self rfl
    have notMarked :
        ¬ kept.any (fun earlier => earlier.trial == observation.trial) = true := by
      intro marked
      obtain ⟨earlier, member, same⟩ := List.any_eq_true.mp marked
      exact headFresh (List.mem_map.mpr ⟨earlier, member, beq_iff_eq.mp same⟩)
    rw [List.foldl_cons, absorb, if_neg notMarked]
    have restNodup : (((kept ++ [observation]) ++ rest).map (·.trial)).Nodup := by
      rw [List.append_assoc, List.singleton_append]
      simpa [List.map_append, List.map_cons] using nodup
    rw [ih _ restNodup, List.append_assoc, List.singleton_append]

theorem keep_eq_of_once (observations : List Observation)
    (once : countsEachTrialOnce observations) :
    keepFirstObservation observations = observations := by
  have nodup :
      ((([] : List Observation) ++ observations).map (fun x => x.trial)).Nodup := by
    simpa [countsEachTrialOnce, List.nil_append] using once
  simpa [keepFirstObservation, List.nil_append] using
    foldl_absorb_eq observations [] nodup

/-- Under the corrected condition the count of the wave is the count of the set
of its observations. The list may contain any number of true outcomes. -/
theorem wave_count_eq_set (observations : List Observation)
    (once : countsEachTrialOnce observations) :
    countObservations (observations.map (·.outcome)) =
      countObservations ((keepFirstObservation observations).map (·.outcome)) := by
  rw [keep_eq_of_once observations once]

theorem count_length (observations : List Bool) :
    (countObservations observations).pos + (countObservations observations).neg =
      observations.length := by
  rw [countObservations_pos, countObservations_neg]
  induction observations with
  | nil => rfl
  | cons head tail ih =>
    cases head with
    | true =>
      rw [List.length_cons, List.count_cons, List.count_cons,
        show (true == true) = true from rfl, show (true == false) = false from rfl,
        if_pos rfl, if_neg Bool.false_ne_true]
      omega
    | false =>
      rw [List.length_cons, List.count_cons, List.count_cons,
        show (false == true) = false from rfl, show (false == false) = true from rfl,
        if_neg Bool.false_ne_true, if_pos rfl]
      omega

theorem absorb_length_le (kept : List Observation) (observation : Observation) :
    (absorb kept observation).length ≤ kept.length + 1 := by
  unfold absorb
  by_cases duplicate : kept.any (fun earlier => earlier.trial == observation.trial) = true
  · rw [if_pos duplicate]
    exact Nat.le_add_right _ _
  · rw [if_neg duplicate, List.length_append, List.length_singleton]

theorem foldl_absorb_length_le (observations kept : List Observation) :
    (observations.foldl absorb kept).length ≤ kept.length + observations.length := by
  induction observations generalizing kept with
  | nil => simp
  | cons observation rest ih =>
    rw [List.foldl_cons, List.length_cons]
    refine le_trans (ih (absorb kept observation)) ?_
    calc
      (absorb kept observation).length + rest.length
          ≤ kept.length + 1 + rest.length :=
            Nat.add_le_add_right (absorb_length_le kept observation) rest.length
      _ = kept.length + (rest.length + 1) := by omega

theorem keep_length_le (observations : List Observation) :
    (keepFirstObservation observations).length ≤ observations.length := by
  simpa [keepFirstObservation] using foldl_absorb_length_le observations []

/-- Without the condition, the count of the publications exceeds the count of
the set by the number of repeated publications. -/
theorem repeated_publications_excess (observations : List Observation) :
    let wave := countObservations (observations.map (·.outcome))
    let setCount := countObservations ((keepFirstObservation observations).map (·.outcome))
    wave.pos + wave.neg =
      setCount.pos + setCount.neg +
        (observations.length - (keepFirstObservation observations).length) := by
  simp [count_length, List.length_map,
    Nat.add_sub_of_le (keep_length_le observations)]

/-- **Positive.** Two distinct trials that both come out true count `⟨2, 0⟩`,
and `countsEachOnce` refuses that pair of Boolean values. -/
theorem two_true_trials_count :
    countsEachTrialOnce [⟨0, true⟩, ⟨1, true⟩] ∧
      countObservations [true, true] = ⟨2, 0⟩ ∧
      ¬ countsEachOnce [true, true] := by
  refine ⟨?once, ?count, not_countsEachOnce_repeat⟩
  · unfold countsEachTrialOnce
    decide
  · decide

/-- **Negative.** One trial published twice is not counted once, and the wave
count exceeds the set count by that one repeated publication. -/
theorem one_trial_published_twice :
    ¬ countsEachTrialOnce [⟨0, true⟩, ⟨0, true⟩] ∧
      countObservations [true, true] = ⟨2, 0⟩ ∧
      countObservations ((keepFirstObservation [⟨0, true⟩, ⟨0, true⟩]).map (·.outcome)) =
        ⟨1, 0⟩ ∧
      (countObservations [true, true]).pos =
        (countObservations ((keepFirstObservation [⟨0, true⟩, ⟨0, true⟩]).map (·.outcome))).pos +
          1 := by
  refine ⟨?once, ?wave, ?setCount, ?excess⟩
  · unfold countsEachTrialOnce
    decide
  · decide
  · decide
  · decide

/-- One alternative that publishes one trial and its outcome, and writes nothing. -/
def trialRegion (trial : Nat) (outcome : Bool) : Region Unit Flag Observation :=
  .answer (Readout.const ⟨trial, outcome⟩)

/-- Keep the first proposal of each trial. -/
def onePerTrial : Policy Unit Flag Observation where
  returned outcomes := keepFirstObservation (outcomes.map Prod.fst)
  change _ world := publish ([] : List (Step Unit Flag)) world

/-- Keep the last proposal of each trial. -/
def lastPerTrial : Policy Unit Flag Observation where
  returned outcomes :=
    (keepFirstObservation ((outcomes.map Prod.fst).reverse)).reverse
  change _ world := publish ([] : List (Step Unit Flag)) world

theorem lastPerTrial_nodup (outcomes : List (Observation × Proposal Unit Flag Observation)) :
    countsEachTrialOnce (lastPerTrial.returned outcomes) := by
  unfold lastPerTrial countsEachTrialOnce
  rw [List.map_reverse]
  exact (List.nodup_reverse).mpr (by
    simpa [countsEachTrialOnce] using
      keepFirst_trials_nodup ((outcomes.map Prod.fst).reverse))

/-- On every wave, either choice of sibling counts each trial once. -/
theorem either_sibling_on_every_wave
    (outcomes : List (Observation × Proposal Unit Flag Observation)) :
    countsEachTrialOnce (onePerTrial.returned outcomes) ∧
      countsEachTrialOnce (lastPerTrial.returned outcomes) := by
  refine ⟨?first, lastPerTrial_nodup outcomes⟩
  simpa [onePerTrial, countsEachTrialOnce] using
    keepFirst_trials_nodup (outcomes.map Prod.fst)

/-- Two distinct trials, both true. -/
def twoTrueTrials : Region Unit Flag Observation :=
  Region.alternatives [trialRegion 0 true, trialRegion 1 true]

/-- One trial, published by two siblings. -/
def oneTrialTwice : Region Unit Flag Observation :=
  Region.alternatives [trialRegion 0 true, trialRegion 0 true]

theorem twoTrueTrials_answers :
    ((twoTrueTrials.branchLocal emptyFlag).map Prod.fst) = [⟨0, true⟩, ⟨1, true⟩] := by
  decide

theorem oneTrialTwice_answers :
    ((oneTrialTwice.branchLocal emptyFlag).map Prod.fst) = [⟨0, true⟩, ⟨0, true⟩] := by
  decide

/-- **Positive.** Keeping one proposal per trial returns both distinct true
trials, and their count is `⟨2, 0⟩`. -/
theorem onePerTrial_keeps_two_true :
    (twoTrueTrials.observe onePerTrial emptyFlag).1 = [⟨0, true⟩, ⟨1, true⟩] ∧
      countObservations (((twoTrueTrials.observe onePerTrial emptyFlag).1).map (·.outcome)) =
        ⟨2, 0⟩ := by
  decide

/-- **Negative.** On one trial published twice, keeping either sibling returns
one observation. The unfiltered wave counts two. -/
theorem either_sibling_on_one_trial :
    (oneTrialTwice.observe onePerTrial emptyFlag).1 = [⟨0, true⟩] ∧
      (oneTrialTwice.observe lastPerTrial emptyFlag).1 = [⟨0, true⟩] ∧
      countObservations (((oneTrialTwice.observe onePerTrial emptyFlag).1).map (·.outcome)) =
        ⟨1, 0⟩ ∧
      countObservations (((oneTrialTwice.observe lastPerTrial emptyFlag).1).map (·.outcome)) =
        ⟨1, 0⟩ ∧
      countObservations (((oneTrialTwice.branchLocal emptyFlag).map Prod.fst).map (·.outcome)) =
        ⟨2, 0⟩ := by
  decide
