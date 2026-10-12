import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativePeTTaConfigurations
import Mettapedia.Languages.MeTTa.PeTTa.BoundCallControls

/-!
# Captured-call execution over the native typed configuration representation

This adapter reuses the complete configuration, physical wire, native Data
judgment and constructor-algebra interpretation. Its source relation adds
only the admitted captured authored calls. Effects remain operational edges,
separate from dependent conversion. Guest propositions do not become native
proof inhabitants merely because their configurations have Data formation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativePeTTaBoundCalls

open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open NativePeTTaConfigurations (NativeTerm encode decode decode_encode encode_admitted encode_denotes)

/-- Existing cell-support accounting also covers captured-call entry: that
entry changes control only and leaves the store exactly as it was. -/
theorem transition_support {program : SpaceSemantics.Program} {source target : Eval.Configuration}
    (names : List String) (covers : ∀ name, name ∉ names → source.state.cells name = none)
    (transition : BoundCalls.Transition program source target) :
    ∀ name, name ∉ ConfigurationEncoding.cellSupportAfter source names → target.state.cells name = none := by
  cases transition with
  | captured bindings name head arguments shape resolved authorized =>
      simpa [ConfigurationEncoding.cellSupportAfter, shape] using covers
  | core _ original => exact ConfigurationEncoding.transition_support names covers original

/-- The selected source transition earns its native endpoints. Finite cell
support is updated by the existing source operation, not by a guessed bound. -/
inductive Transition (program : SpaceSemantics.Program) : NativeTerm → NativeTerm → Prop where
  | step {before after : Eval.Configuration} (names : List String)
      (vacant : NamedSpaces.Store.EmptyTail before.state [])
      (covers : ∀ name, name ∉ names → before.state.cells name = none)
      (selected : BoundCalls.Transition program before after) :
      Transition program (encode before names)
        (encode after (ConfigurationEncoding.cellSupportAfter before names))

theorem transition_reflects {program : SpaceSemantics.Program} {source target : NativeTerm}
    (transition : Transition program source target) :
    ∃ before after, decode source = some before ∧ decode target = some after ∧
      BoundCalls.Transition program before after := by
  cases transition with
  | step names vacant covers selected =>
      exact ⟨_, _, decode_encode _ names vacant covers,
        decode_encode _ _ (BoundCalls.transition_empty_tail vacant selected)
          (transition_support names covers selected), selected⟩

theorem transition_admits {program : SpaceSemantics.Program} {source target : NativeTerm}
    (transition : Transition program source target) :
    FormationSensitive.Judgment NativeWireData.rules .nil source NativeWireData.dataType ∧
      FormationSensitive.Judgment NativeWireData.rules .nil target NativeWireData.dataType := by
  cases transition
  exact ⟨encode_admitted _ _, encode_admitted _ _⟩

/-- This is the explicit-state operational graph, separate from the native
dependent conversion graph. Its edges are the transported source steps. -/
def theory (program : SpaceSemantics.Program) : Mettapedia.GSLT.GSLT where
  Term := NativeTerm
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Transition program
  rewrites_resp_left := by
    intro first other second same transition
    subst other
    exact ⟨second, transition, rfl⟩
  rewrites_resp_right := by
    intro first second other transition same
    subst other
    exact transition

/-- Every native explicit-state path reflects a real source execution.
The decoder checks the starting endpoint, including its complete store. -/
theorem path_reflects {program : SpaceSemantics.Program} {source target : NativeTerm}
    (path : (theory program).MultiStep source target) (before : Eval.Configuration)
    (decoded : decode source = some before) :
    ∃ after, decode target = some after ∧ (BoundCalls.theory program).MultiStep before after := by
  refine @Mettapedia.GSLT.GSLT.MultiStep.rec (theory program)
    (fun source target _ => ∀ before : Eval.Configuration, decode source = some before →
      ∃ after, decode target = some after ∧ (BoundCalls.theory program).MultiStep before after)
    (fun _ before decoded => ⟨before, decoded, .refl _⟩)
    (fun {_ _ _} selected _ ih before decoded => ?_) source target path before decoded
  ·
      obtain ⟨original, middle, readSource, readMiddle, step⟩ := transition_reflects selected
      have same : original = before := Option.some.inj (readSource.symm.trans decoded)
      subst original
      obtain ⟨after, readAfter, remaining⟩ := ih middle readMiddle
      exact ⟨after, readAfter, .step step remaining⟩

/-- Source paths construct native state paths, with actual evolving cell
support and no guest evaluator supplied as an assumed soundness interface. -/
theorem path_lifts {program : SpaceSemantics.Program}
    {before after : Eval.Configuration} (path : (BoundCalls.theory program).MultiStep before after)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail before.state [])
    (covers : ∀ name, name ∉ names → before.state.cells name = none) :
    ∃ finalNames,
      (theory program).MultiStep (encode before names) (encode after finalNames) ∧
      NamedSpaces.Store.EmptyTail after.state [] ∧
      (∀ name, name ∉ finalNames → after.state.cells name = none) := by
  refine @Mettapedia.GSLT.GSLT.MultiStep.rec (BoundCalls.theory program)
    (fun before after _ => ∀ names : List String,
      NamedSpaces.Store.EmptyTail before.state [] →
      (∀ name, name ∉ names → before.state.cells name = none) →
      ∃ finalNames, (theory program).MultiStep (encode before names) (encode after finalNames) ∧
        NamedSpaces.Store.EmptyTail after.state [] ∧
        (∀ name, name ∉ finalNames → after.state.cells name = none))
    (fun _ names vacant covers => ⟨names, .refl _, vacant, covers⟩)
    (fun {before _ _} selected _ ih names vacant covers => ?_) before after path names vacant covers
  ·
      have nextVacant := BoundCalls.transition_empty_tail vacant selected
      have nextCovers := transition_support names covers selected
      obtain ⟨finalNames, remaining, finalVacant, finalCovers⟩ :=
        ih (ConfigurationEncoding.cellSupportAfter before names) nextVacant nextCovers
      exact ⟨finalNames, .step (.step names vacant covers selected) remaining,
        finalVacant, finalCovers⟩

/-- The pinned authored call constructs an actual native path. Its endpoints
have the existing formation-sensitive Data judgment and free-algebra meaning. -/
theorem authored_call_native_path (names : List String)
    (vacant : NamedSpaces.Store.EmptyTail Effects.empty [])
    (covers : ∀ name, name ∉ names → Effects.empty.cells name = none) :
    ∃ finalNames,
      (theory BoundCallControls.program).MultiStep
        (encode BoundCallControls.initial names)
        (encode (Eval.finished Effects.empty [BoundCallControls.eight] [] []) finalNames) ∧
      NamedSpaces.Store.EmptyTail Effects.empty [] ∧
      (∀ name, name ∉ finalNames → Effects.empty.cells name = none) :=
  path_lifts BoundCallControls.captured_call_path names vacant covers

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativePeTTaBoundCalls
