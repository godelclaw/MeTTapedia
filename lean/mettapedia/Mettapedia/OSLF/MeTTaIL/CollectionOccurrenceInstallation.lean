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

def State.install (allocations : List (Allocation plan bound expected source))
    (state : State plan bound expected source) : State plan bound expected source :=
  ⟨state.frames ++ allocations.map Frame.initial, state.log⟩

theorem State.install_log (allocations : List (Allocation plan bound expected source))
    (state : State plan bound expected source) : (state.install allocations).log = state.log := rfl

theorem State.install_frames_prefix (allocations : List (Allocation plan bound expected source))
    (state : State plan bound expected source) : state.frames <+: (state.install allocations).frames :=
  List.prefix_append _ _

theorem State.install_append (first extra : List (Allocation plan bound expected source))
    (state : State plan bound expected source) :
    state.install (first ++ extra) = (state.install first).install extra := by
  cases state
  simp only [State.install, List.map_append, List.append_assoc]

theorem initial_publications_empty (allocations : List (Allocation plan bound expected source)) :
    (allocations.map Frame.initial).flatMap Frame.publication = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro frame member
  obtain ⟨allocation, _, rfl⟩ := List.mem_map.mp member
  exact Frame.initial_publication allocation

theorem State.install_balanced (allocations : List (Allocation plan bound expected source))
    {state : State plan bound expected source} (balanced : state.Balanced) :
    (state.install allocations).Balanced := by
  simpa only [State.Balanced, State.install, List.flatMap_append,
    initial_publications_empty, List.append_nil] using balanced

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

end Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceBatch
