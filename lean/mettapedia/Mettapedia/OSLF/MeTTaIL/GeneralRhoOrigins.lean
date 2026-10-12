import Mettapedia.OSLF.MeTTaIL.GeneralRhoSites

/-!
# Equal rho endpoints with distinct primitive bag origins

Two identical input components occupy different actual collection positions.
Each COMM derivation stores its selected position in the structural trace,
while retaining the same original body, contextual assignment and reduct.
The equality of endpoints does not identify these physical occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRho

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.Examples.ScopedRhoBinding
open GeneralScopedMatchMachine

def duplicateSource (channel body payload : Pattern) : Pattern :=
  .collection .hashBag [input channel body, input channel body, output channel payload] none

def firstInputTrace : List BagChoice := [{path := [0], selected := 0}, {path := [1], selected := 1}]
def secondInputTrace : List BagChoice := [{path := [0], selected := 1}, {path := [1], selected := 1}]

private theorem duplicate_firing {bound : List TypeExpr} {channel body payload : Pattern}
    (channelTyped : OpenPatternWellSorted language snapshot.free bound (.base "Name") channel)
    (bodyTyped : OpenPatternWellSorted language snapshot.free (.base "Name" :: bound) (.base "Proc") body)
    (sealed : ScopedPattern.binderSafeAt "NQuote" (bound.length + 1) body = true)
    (names : ReflectiveInstantiation.namesAdmitted
      rhoReflectivePresentation.toReflectivePresentationDecl body = true)
    (payloadTyped : OpenPatternWellSorted language snapshot.free bound (.base "Proc") payload)
    {trace : List BagChoice}
    (matched : TracedMatches comm scopedCommBindingSpec bound.length .left [] 0 [] comm.left
      (duplicateSource channel body payload) trace
      (captured bound.length channel body payload [input channel body])) :
    GeneralPremise.RootFiring executionEnvironment bound (.base "Proc")
      (duplicateSource channel body payload) 0 trace
      (captured bound.length channel body payload [input channel body])
      (captured bound.length channel body payload [input channel body]) []
      (.collection .hashBag [reflectiveBody body payload, input channel body] none) := by
  have inputTyped := input_typed channelTyped.1 bodyTyped.1
  have inputRepresented := input_represented ⟨channelTyped.2.1, channelTyped.2.2.1⟩
    ⟨bodyTyped.2.1, bodyTyped.2.2.1⟩
  have base := root_receipt_valid channelTyped bodyTyped sealed names payloadTyped (.cons inputTyped (.nil _ _))
    (by intro pattern member; have same := List.mem_singleton.mp member; subst pattern; exact inputRepresented)
  have readout := GeneralRuleJobs.receipt_root_readout base
  have sourceTyped := parallel_typed (.cons inputTyped (.cons inputTyped
    (.cons (output_typed channelTyped.1 payloadTyped.1) (.nil _ _))))
  have sourceRepresented : Represented (duplicateSource channel body payload) := by
    apply (represented_collection_iff _ _).mpr
    intro pattern member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact inputRepresented
    · exact inputRepresented
    · exact output_represented ⟨channelTyped.2.1, channelTyped.2.2.1⟩
        ⟨payloadTyped.2.1, payloadTyped.2.2.1⟩
  have sourceOpen : OpenPatternWellSorted language snapshot.free bound (.base "Proc")
      (duplicateSource channel body payload) :=
    ⟨sourceTyped, sourceRepresented.1, sourceRepresented.2, sourceTyped.isWellScopedAt⟩
  exact .fire (GeneralRuleJobs.Job.selected_rule base.1)
    (GeneralRuleJobs.Job.selected_specification base.1) readout.1
    ((GeneralPlanEnvironment.typing_iff plan _ _ _).mpr sourceOpen)
    matched readout.2.2.1 .nil readout.2.2.2.1 readout.2.2.2.2

theorem duplicate_root_firings {bound : List TypeExpr} {channel body payload : Pattern}
    (channelTyped : OpenPatternWellSorted language snapshot.free bound (.base "Name") channel)
    (bodyTyped : OpenPatternWellSorted language snapshot.free (.base "Name" :: bound) (.base "Proc") body)
    (sealed : ScopedPattern.binderSafeAt "NQuote" (bound.length + 1) body = true)
    (names : ReflectiveInstantiation.namesAdmitted
      rhoReflectivePresentation.toReflectivePresentationDecl body = true)
    (payloadTyped : OpenPatternWellSorted language snapshot.free bound (.base "Proc") payload) :
    GeneralPremise.RootFiring executionEnvironment bound (.base "Proc")
      (duplicateSource channel body payload) 0 firstInputTrace
      (captured bound.length channel body payload [input channel body])
      (captured bound.length channel body payload [input channel body]) []
      (.collection .hashBag [reflectiveBody body payload, input channel body] none) ∧
    GeneralPremise.RootFiring executionEnvironment bound (.base "Proc")
      (duplicateSource channel body payload) 0 secondInputTrace
      (captured bound.length channel body payload [input channel body])
      (captured bound.length channel body payload [input channel body]) []
      (.collection .hashBag [reflectiveBody body payload, input channel body] none) ∧
    firstInputTrace ≠ secondInputTrace := by
  obtain ⟨first, second, different⟩ := duplicate_input_origins channelTyped.1.isWellScopedAt
    (by simpa using bodyTyped.1.isWellScopedAt) payloadTyped.1.isWellScopedAt
  exact ⟨duplicate_firing channelTyped bodyTyped sealed names payloadTyped first,
    duplicate_firing channelTyped bodyTyped sealed names payloadTyped second, different⟩

#print axioms duplicate_root_firings

end Mettapedia.OSLF.MeTTaIL.GeneralRho
