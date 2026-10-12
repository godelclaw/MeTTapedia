import Mettapedia.Languages.MeTTa.PeTTa.ConfigurationEncoding
import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeWireDataDenotation

/-!
# Actual PeTTa configurations in the native dependent Data fragment

Three existing codecs compose here: the complete source configuration, the
shared physical Pattern wire, and the native scoped Data representation.
Their round trips retain control, bindings, continuations, pending branches,
spaces, cells and I/O. Each encoded configuration has the existing native
formation-sensitive Data judgment and its actual free-algebra meaning.

The operational graph below transports the existing source transitions onto
those native values. It does not insert effectful transitions into dependent
definitional equality. Data admission does not validate a guest proof or make
it a native inhabitant of its represented proposition. Source-to-C execution
correspondence and that stronger proof interpretation remain separate work.
This is a qualified fragment, not adoption of a complete Prime foundation.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativePeTTaConfigurations

open Presentation
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.GSLT.LanguageDef

abbrev NativeTerm := Tower.Tm 0

def wire (configuration : Eval.Configuration) (names : List String) : CettaWire.Term :=
  InferenceCettaWire.encodePattern (ConfigurationEncoding.encode configuration names)

def encode (configuration : Eval.Configuration) (names : List String) : NativeTerm :=
  NativeWireData.encode (wire configuration names)

def decode (term : NativeTerm) : Option Eval.Configuration := do
  let value ← NativeWireData.decode term
  let pattern ← InferenceCettaWire.decodePattern value
  ConfigurationEncoding.decode pattern

theorem decode_encode (configuration : Eval.Configuration) (names : List String)
    (vacant : NamedSpaces.Store.EmptyTail configuration.state [])
    (covers : ∀ name, name ∉ names → configuration.state.cells name = none) :
    decode (encode configuration names) = some configuration := by
  simpa [decode, encode, wire] using
    ConfigurationEncoding.decode_encode configuration names vacant covers

/-- Actual native formation, using the existing declarations and judgment. -/
theorem encode_admitted (configuration : Eval.Configuration) (names : List String) :
    FormationSensitive.Judgment NativeWireData.rules .nil
      (encode configuration names) NativeWireData.dataType :=
  NativeWireData.encode_judgment .nil _

/-- Meaning is the existing total constructor algebra, independently of the
decoder. The semantic carrier is the actual source store, not a dummy model. -/
theorem encode_denotes (configuration : Eval.Configuration) (names : List String) :
    NativeWireDataDenotation.Denotes .nil
      (fun index (_ : Effects.State) => Fin.elim0 index)
      (encode configuration names)
      (fun _ => NativeWireDataDenotation.ofWire (wire configuration names)) :=
  NativeWireDataDenotation.encode_denotes .nil _ _

/-- Equal native encodings cannot splice different valid source endpoints. -/
theorem equal_encodings_same_configuration
    (first second : Eval.Configuration) (firstNames secondNames : List String)
    (firstVacant : NamedSpaces.Store.EmptyTail first.state [])
    (secondVacant : NamedSpaces.Store.EmptyTail second.state [])
    (firstCovers : ∀ name, name ∉ firstNames → first.state.cells name = none)
    (secondCovers : ∀ name, name ∉ secondNames → second.state.cells name = none)
    (same : encode first firstNames = encode second secondNames) : first = second := by
  have decoded := congrArg decode same
  rw [decode_encode first firstNames firstVacant firstCovers,
    decode_encode second secondNames secondVacant secondCovers] at decoded
  exact Option.some.inj decoded

/-- The selected source transition earns its native endpoints. Finite cell
support is updated by the existing source operation, not by a guessed bound. -/
inductive Transition (program : SpaceSemantics.Program) : NativeTerm → NativeTerm → Prop where
  | step {before after : Eval.Configuration} (names : List String)
      (vacant : NamedSpaces.Store.EmptyTail before.state [])
      (covers : ∀ name, name ∉ names → before.state.cells name = none)
      (selected : DeclarativeSpec.Transition program before after) :
      Transition program (encode before names)
        (encode after (ConfigurationEncoding.cellSupportAfter before names))

theorem transition_reflects {program : SpaceSemantics.Program} {source target : NativeTerm}
    (transition : Transition program source target) :
    ∃ before after, decode source = some before ∧ decode target = some after ∧
      DeclarativeSpec.Transition program before after := by
  cases transition with
  | step names vacant covers selected =>
      exact ⟨_, _, decode_encode _ names vacant covers,
        decode_encode _ _ (DeclarativeSpec.transition_empty_tail vacant selected)
          (ConfigurationEncoding.transition_support names covers selected), selected⟩

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
    ∃ after, decode target = some after ∧ (Eval.theory program).MultiStep before after := by
  refine @Mettapedia.GSLT.GSLT.MultiStep.rec (theory program)
    (fun source target _ => ∀ before : Eval.Configuration, decode source = some before →
      ∃ after, decode target = some after ∧ (Eval.theory program).MultiStep before after)
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
    {before after : Eval.Configuration} (path : (Eval.theory program).MultiStep before after)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail before.state [])
    (covers : ∀ name, name ∉ names → before.state.cells name = none) :
    ∃ finalNames,
      (theory program).MultiStep (encode before names) (encode after finalNames) ∧
      NamedSpaces.Store.EmptyTail after.state [] ∧
      (∀ name, name ∉ finalNames → after.state.cells name = none) := by
  refine @Mettapedia.GSLT.GSLT.MultiStep.rec (Eval.theory program)
    (fun before after _ => ∀ names : List String,
      NamedSpaces.Store.EmptyTail before.state [] →
      (∀ name, name ∉ names → before.state.cells name = none) →
      ∃ finalNames, (theory program).MultiStep (encode before names) (encode after finalNames) ∧
        NamedSpaces.Store.EmptyTail after.state [] ∧
        (∀ name, name ∉ finalNames → after.state.cells name = none))
    (fun _ names vacant covers => ⟨names, .refl _, vacant, covers⟩)
    (fun {before _ _} selected _ ih names vacant covers => ?_) before after path names vacant covers
  ·
      have nextVacant := DeclarativeSpec.transition_empty_tail vacant selected
      have nextCovers := ConfigurationEncoding.transition_support names covers selected
      obtain ⟨finalNames, remaining, finalVacant, finalCovers⟩ :=
        ih (ConfigurationEncoding.cellSupportAfter before names) nextVacant nextCovers
      exact ⟨finalNames, .step (.step names vacant covers selected) remaining,
        finalVacant, finalCovers⟩

/-- Missing a required named cell changes a source configuration; typing the
remaining Data is not permission to invent the missing state. -/
theorem distinct_configurations_distinct_encodings
    (first second : Eval.Configuration) (firstNames secondNames : List String)
    (firstVacant : NamedSpaces.Store.EmptyTail first.state [])
    (secondVacant : NamedSpaces.Store.EmptyTail second.state [])
    (firstCovers : ∀ name, name ∉ firstNames → first.state.cells name = none)
    (secondCovers : ∀ name, name ∉ secondNames → second.state.cells name = none)
    (different : first ≠ second) : encode first firstNames ≠ encode second secondNames :=
  fun same => different (equal_encodings_same_configuration first second firstNames secondNames
    firstVacant secondVacant firstCovers secondCovers same)

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativePeTTaConfigurations
