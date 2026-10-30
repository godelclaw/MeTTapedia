import Mettapedia.Languages.Datalog.Closure

/-! Least positive fact closure and finite one-step explanation support.
The source judgment uses clause matching and premise derivations; its rules
do not invoke the executable producer. Cyclic proof trees are not enumerated
by the finite logical key observation. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.Datalog.Closure

open GroundInstances

theorem authorized_on_premises (policy : Comparisons.Policy) (program : Program)
    (known : List GroundFact) (row : Instance)
    (authorized : ProgramGrounding.SourceAuthorized policy program known row) :
    ProgramGrounding.SourceAuthorized policy program row.key.positivePremises row := by
  obtain ⟨clause, atSource, restricted, ordinal, model, head, body, _, guards, names, values⟩ := authorized
  exact ⟨clause, atSource, restricted, ordinal, model, head, body,
    fun _ member => member, guards, names, values⟩

inductive Derives (policy : Comparisons.Policy) (program : Program) (seeds : List GroundFact) :
    GroundFact → Prop where
  | seed {fact : GroundFact} (member : fact ∈ seeds) : Derives policy program seeds fact
  | fire (row : Instance)
      (authorized : ProgramGrounding.SourceAuthorized policy program row.key.positivePremises row)
      (premises : ∀ fact ∈ row.key.positivePremises, Derives policy program seeds fact) :
      Derives policy program seeds row.conclusion

/-- A key describes one source firing with finitely derivable premises.
The physical validation positions in `row` do not contribute to this identity. -/
def DerivableKey (policy : Comparisons.Policy) (program : Program) (seeds : List GroundFact)
    (key : DerivationKey) : Prop :=
  ∃ row : Instance, row.key = key ∧
    ProgramGrounding.SourceAuthorized policy program row.key.positivePremises row ∧
    ∀ fact ∈ row.key.positivePremises, Derives policy program seeds fact

def Sound (policy : Comparisons.Policy) (program : Program) (seeds : List GroundFact)
    (state : State) : Prop :=
  (∀ fact ∈ state.facts, Derives policy program seeds fact) ∧
    ∀ key ∈ state.keys, DerivableKey policy program seeds key

theorem initial_sound (policy : Comparisons.Policy) (program : Program) (seeds : List GroundFact) :
    Sound policy program seeds (initial seeds) := by
  constructor
  · intro fact member
    exact .seed (List.mem_eraseDups.mp member)
  · intro key member
    cases member

theorem source_firing_premises {policy : Comparisons.Policy} {program : Program}
    {known : List GroundFact} {row : Instance}
    (authorized : ProgramGrounding.SourceAuthorized policy program known row) :
    ∀ fact ∈ row.key.positivePremises, fact ∈ known := by
  obtain ⟨_, _, _, _, _, _, _, available, _, _, _⟩ := authorized
  exact available

theorem step_sound (policy : Comparisons.Policy) (program : Program) (seeds : List GroundFact)
    (state : State) (sound : Sound policy program seeds state) :
    Sound policy program seeds (step policy program state) := by
  constructor
  · intro fact member
    rcases (mem_step_facts _ _ _ _).mp member with old | ⟨key, member⟩
    · exact sound.1 fact old
    · have authorized := (mem_firings_iff policy program state.facts key fact).mp member
      exact .fire ⟨key, fact, []⟩ (authorized_on_premises _ _ _ _ authorized)
        (fun premise inside => sound.1 premise (source_firing_premises authorized premise inside))
  · intro key member
    rcases (mem_step_keys _ _ _ _).mp member with old | ⟨conclusion, member⟩
    · exact sound.2 key old
    · have authorized := (mem_firings_iff policy program state.facts key conclusion).mp member
      exact ⟨⟨key, conclusion, []⟩, rfl, authorized_on_premises _ _ _ _ authorized,
        fun premise inside => sound.1 premise (source_firing_premises authorized premise inside)⟩

theorem run_sound (policy : Comparisons.Policy) (program : Program) (seeds : List GroundFact)
    (ticks : Nat) (state : State) (sound : Sound policy program seeds state) :
    Sound policy program seeds (run policy program ticks state) := by
  induction ticks generalizing state with
  | zero => exact sound
  | succ ticks ih => exact ih (step policy program state) (step_sound _ _ _ _ sound)

theorem run_initial_sound (policy : Comparisons.Policy) (program : Program) (seeds : List GroundFact)
    (ticks : Nat) : Sound policy program seeds (run policy program ticks (initial seeds)) :=
  run_sound _ _ _ _ _ (initial_sound _ _ _)

theorem facts_in_run (policy : Comparisons.Policy) (program : Program) (ticks : Nat) (state : State) :
    ∀ fact ∈ state.facts, fact ∈ (run policy program ticks state).facts := by
  induction ticks generalizing state with
  | zero => exact fun _ member => member
  | succ ticks ih =>
    intro fact member
    exact ih _ fact (facts_in_step policy program state fact member)

theorem seeds_in_run (policy : Comparisons.Policy) (program : Program) (ticks : Nat)
    (seeds : List GroundFact) :
    ∀ fact ∈ seeds, fact ∈ (run policy program ticks (initial seeds)).facts :=
  fun fact member => facts_in_run _ _ _ _ fact (List.mem_eraseDups.mpr member)

/-- Settlement reflects all finite source derivations, not just the firings
encountered in one particular enumeration order. -/
theorem derives_in_closed (policy : Comparisons.Policy) (program : Program) (seeds : List GroundFact)
    (state : State) (seeded : ∀ fact ∈ seeds, fact ∈ state.facts)
    (closed : FactsComplete policy program state) {fact : GroundFact}
    (derived : Derives policy program seeds fact) : fact ∈ state.facts := by
  induction derived with
  | seed member => exact seeded _ member
  | fire row authorized _ ih =>
    have valid := authorized_mono policy program row.key.positivePremises state.facts ih row authorized
    have member : (row.key, row.conclusion) ∈ firings policy program state.facts := by
      apply (mem_firings_iff _ _ _ _ _).mpr
      simpa only [ProgramGrounding.SourceAuthorized, Authorized] using valid
    exact closed row.key row.conclusion member

theorem settled_facts_exact (policy : Comparisons.Policy) (program : Program) (seeds : List GroundFact)
    (ticks : Nat) (closed : FactsComplete policy program (run policy program ticks (initial seeds)))
    (fact : GroundFact) :
    fact ∈ (run policy program ticks (initial seeds)).facts ↔ Derives policy program seeds fact :=
  ⟨(run_initial_sound _ _ _ _).1 fact,
    derives_in_closed policy program seeds _ (seeds_in_run _ _ _ _) closed⟩

theorem settled_keys_exact (policy : Comparisons.Policy) (program : Program) (seeds : List GroundFact)
    (ticks : Nat)
    (factsClosed : FactsComplete policy program (run policy program ticks (initial seeds)))
    (keysClosed : KeysComplete policy program (run policy program ticks (initial seeds)))
    (key : DerivationKey) :
    key ∈ (run policy program ticks (initial seeds)).keys ↔ DerivableKey policy program seeds key := by
  constructor
  · exact (run_initial_sound _ _ _ _).2 key
  · rintro ⟨row, sameKey, authorized, premises⟩
    have available : ∀ fact ∈ row.key.positivePremises,
        fact ∈ (run policy program ticks (initial seeds)).facts :=
      fun fact member => (settled_facts_exact _ _ _ _ factsClosed fact).mpr (premises fact member)
    have valid := authorized_mono policy program row.key.positivePremises _ available row authorized
    have member : (row.key, row.conclusion) ∈ firings policy program
        (run policy program ticks (initial seeds)).facts := by
      apply (mem_firings_iff _ _ _ _ _).mpr
      simpa only [ProgramGrounding.SourceAuthorized, Authorized] using valid
    exact sameKey ▸ keysClosed row.key row.conclusion member

/-- Every closed model containing the input contains the computed prefix.
This independently characterizes the source judgment as the least closure. -/
theorem derives_least (policy : Comparisons.Policy) (program : Program) (seeds : List GroundFact)
    (model : Set GroundFact) (seeded : ∀ fact ∈ seeds, fact ∈ model)
    (closed : ∀ row : Instance,
      ProgramGrounding.SourceAuthorized policy program row.key.positivePremises row →
      (∀ fact ∈ row.key.positivePremises, fact ∈ model) → row.conclusion ∈ model)
    {fact : GroundFact} (derived : Derives policy program seeds fact) : fact ∈ model := by
  induction derived with
  | seed member => exact seeded _ member
  | fire row authorized _ ih => exact closed row authorized ih

#print axioms run_initial_sound
#print axioms settled_facts_exact
#print axioms settled_keys_exact
#print axioms derives_least

end Mettapedia.Languages.Datalog.Closure
