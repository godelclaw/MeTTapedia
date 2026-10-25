import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceAdmission
import Mettapedia.GSLT.LanguageDef.CollectionNestedConsumerControls
import Mettapedia.OSLF.MeTTaIL.CollectionContextVariantsControls

/-! # Bounded admission controls for nested and guarded collection execution -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CollectionOccurrenceAdmissionControls

open Mettapedia.OSLF.MeTTaIL Syntax
open CollectionOccurrenceAdmission

#guard check (CollectionNestedConsumerControls.plan true)
#guard check (CollectionNestedConsumerControls.plan false)
#guard check CollectionSelection.ContextControls.plan
#guard CollectionSelection.ContextControls.plan.obligations.contains .setDecomposition

def withQuery (arguments : List Pattern) : GeneralExecutionAdmission.Plan :=
  let plan := CollectionNestedConsumerControls.plan true
  { plan with rules := plan.rules.map fun declaration =>
      { declaration with authored := { declaration.authored with premises := [.relationQuery "inspect" arguments] } } }

#guard !check (withQuery [.fvar "rest"])

def withStepPremise : GeneralExecutionAdmission.Plan :=
  let plan := CollectionNestedConsumerControls.plan true
  { plan with rules := plan.rules.map fun declaration =>
      { declaration with authored := { declaration.authored with premises := [.congruence
        (.fvar "rest") (.fvar "rest")] } } }

#guard !check withStepPremise

def withQuantifier : GeneralExecutionAdmission.Plan :=
  let plan := CollectionNestedConsumerControls.plan true
  { plan with rules := plan.rules.map fun declaration =>
      { declaration with authored := { declaration.authored with premises :=
        [.forAll "rest" "item" (.relationQuery "permit" [])] } } }

#guard !check withQuantifier

def dynamic : GeneralExecutionAdmission.Plan :=
  let plan := CollectionNestedConsumerControls.plan true
  { plan with snapshot := { plan.snapshot with provider :=
    { plan.snapshot.provider with dynamicRelations := ["permit"] } } }

#guard !check dynamic

def missingRule : GeneralExecutionAdmission.Plan :=
  let plan := CollectionNestedConsumerControls.plan true
  { plan with obligations := .missingRule 0 :: plan.obligations }

#guard !check missingRule

def invalidLanguage : GeneralExecutionAdmission.Plan :=
  let plan := CollectionNestedConsumerControls.plan true
  { plan with obligations := .invalidLanguage :: plan.obligations }

#guard !check invalidLanguage

def needsChildDepth : GeneralExecutionAdmission.Plan :=
  let plan := CollectionNestedConsumerControls.plan true
  { plan with obligations := .childStratification :: plan.obligations }

#guard check needsChildDepth
#guard !check { withQuery [.fvar "rest"] with obligations := [.setDecomposition, .childStratification] }

end Mettapedia.GSLT.LanguageDef.CollectionOccurrenceAdmissionControls
