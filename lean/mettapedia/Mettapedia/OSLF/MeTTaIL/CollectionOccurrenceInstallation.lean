import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceBatch

/-!
# Installing newly matched allocations without restarting retained work

New allocations begin with no publications. Installation therefore extends
the retained frame list while preserving the complete chronological account.
It neither advances old continuations nor repeats their existing results.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceBatch

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax

variable {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern}

variable {matcher : GeneralPremise.MatchingExecution}

def State.installWith (profile : SeedProfile matcher plan bound expected source)
    (allocations : List (Allocation plan bound expected source))
    (state : State plan bound expected source matcher) : State plan bound expected source matcher :=
  ⟨state.frames ++ allocations.map (Frame.initialWith profile), state.log⟩

theorem State.installWith_log (profile : SeedProfile matcher plan bound expected source)
    (allocations : List (Allocation plan bound expected source))
    (state : State plan bound expected source matcher) :
    (state.installWith profile allocations).log = state.log := rfl

theorem State.installWith_frames_prefix (profile : SeedProfile matcher plan bound expected source)
    (allocations : List (Allocation plan bound expected source))
    (state : State plan bound expected source matcher) :
    state.frames <+: (state.installWith profile allocations).frames := List.prefix_append _ _

theorem State.installWith_append (profile : SeedProfile matcher plan bound expected source)
    (first extra : List (Allocation plan bound expected source))
    (state : State plan bound expected source matcher) :
    state.installWith profile (first ++ extra) =
      (state.installWith profile first).installWith profile extra := by
  cases state
  simp only [State.installWith, List.map_append, List.append_assoc]

theorem initialWith_publications_empty (profile : SeedProfile matcher plan bound expected source)
    (allocations : List (Allocation plan bound expected source)) :
    (allocations.map (Frame.initialWith profile)).flatMap Frame.publication = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro frame member
  obtain ⟨allocation, _, rfl⟩ := List.mem_map.mp member
  exact Frame.initialWith_publication profile allocation

theorem State.installWith_balanced (profile : SeedProfile matcher plan bound expected source)
    (allocations : List (Allocation plan bound expected source))
    {state : State plan bound expected source matcher} (balanced : state.Balanced) :
    (state.installWith profile allocations).Balanced := by
  simpa only [State.Balanced, State.installWith, List.flatMap_append,
    initialWith_publications_empty profile allocations, List.append_nil] using balanced

def State.install (allocations : List (Allocation plan bound expected source))
    (state : State plan bound expected source) : State plan bound expected source :=
  state.installWith (ordinarySeedProfile plan bound expected source) allocations

theorem State.install_log (allocations : List (Allocation plan bound expected source))
    (state : State plan bound expected source) : (state.install allocations).log = state.log := rfl

theorem State.install_frames_prefix (allocations : List (Allocation plan bound expected source))
    (state : State plan bound expected source) : state.frames <+: (state.install allocations).frames :=
  List.prefix_append _ _

theorem State.install_append (first extra : List (Allocation plan bound expected source))
    (state : State plan bound expected source) :
    state.install (first ++ extra) = (state.install first).install extra := by
  cases state
  simp only [State.install, State.installWith, List.map_append, List.append_assoc]

theorem initial_publications_empty (allocations : List (Allocation plan bound expected source)) :
    (allocations.map Frame.initial).flatMap Frame.publication = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro frame member
  obtain ⟨allocation, _, rfl⟩ := List.mem_map.mp member
  exact Frame.initial_publication allocation

theorem State.install_balanced (allocations : List (Allocation plan bound expected source))
    {state : State plan bound expected source} (balanced : state.Balanced) :
    (state.install allocations).Balanced := by
  exact State.installWith_balanced (ordinarySeedProfile plan bound expected source) allocations balanced

/-- Every frame carries its original source authority, even when frames were
installed at different times. Conservation transfers that authority to the
chronological log without assuming how a scheduler interleaved them. -/
theorem State.balanced_source_sound {state : State plan bound expected source}
    (balanced : state.Balanced) {packet : Publication} (published : packet ∈ state.log)
    {receipt : GeneralRuleJobs.Receipt}
    (finished : packet.finish? plan bound expected = some receipt) :
    (Complete.Presented.gslt plan bound expected).Step source receipt.target := by
  obtain ⟨frame, _, inside⟩ := List.mem_flatMap.mp (balanced.subset published)
  exact Frame.publication_source_sound frame inside finished

theorem State.installWith_ordinary (allocations : List (Allocation plan bound expected source))
    (state : State plan bound expected source) :
    state.installWith (ordinarySeedProfile plan bound expected source) allocations =
      state.install allocations := rfl

#print axioms State.installWith_append
#print axioms State.installWith_balanced
#print axioms State.installWith_ordinary

end Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceBatch
