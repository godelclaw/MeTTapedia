import Mettapedia.OSLF.MeTTaIL.GeneralRhoExecution

/-!
# Original input and parallel occurrences of typed rho execution

Every licensed inner site lifts through the actual Name-binding input
parameter and the authored bare parallel collection. The wrappers preserve
its complete binder context and typing alternatives. The checked receipt
family executes COMM inside input bodies in arbitrary outer contexts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRho

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence
open GeneralTypedSites

abbrev executionEnvironment := GeneralPlanEnvironment.environment plan

def underInput (channel body : Pattern) (inner : SiteData) : SiteData :=
  (inner.wrapLambda none (.base "Name")).wrapApplication 5 "PInput" [channel, .lambda none body] 1

theorem underInput_licensed {bound : List TypeExpr} {channel body : Pattern} {inner : SiteData}
    (channelTyped : HasType executionEnvironment.language snapshot.free bound channel (.base "Name"))
    (channelObject : isObjectPattern channel = true)
    (licensed : Licensed executionEnvironment.language snapshot.free permissions.sites
      (.base "Name" :: bound) (.base "Proc") body inner) :
    Licensed executionEnvironment.language snapshot.free permissions.sites bound (.base "Proc")
      (input channel body) (underInput channel body inner) := by
  apply Licensed.application (rule := inputRule)
    (parameter := .abstraction "p" (.arrow (.base "Name") (.base "Proc")))
    (parameterType := .arrow (.base "Name") (.base "Proc"))
  · change (inputRule, 5) ∈ language.terms.zipIdx
    decide +kernel
  · simp [UsesBareCollection, inputRule, rhoCalc]
  · exact .cons (by trivial) rfl channelTyped
      (.cons (by trivial) rfl (.lambda licensed.source_typed) .nil)
  · simp only [isObjectPatternList, isObjectPattern, channelObject, licensed.source_object,
      Bool.true_and]
  · rfl
  · rfl
  · rfl
  · exact .inl rfl
  · exact .lambda rfl licensed

theorem underInput_generated {bound : List TypeExpr} {channel body : Pattern} {inner : SiteData}
    (channelTyped : HasType executionEnvironment.language snapshot.free bound channel (.base "Name"))
    (channelObject : isObjectPattern channel = true)
    (generated : inner ∈ generate executionEnvironment.language snapshot.free permissions.sites
      (.base "Name" :: bound) (.base "Proc") body) :
    underInput channel body inner ∈ generate executionEnvironment.language snapshot.free permissions.sites
      bound (.base "Proc") (input channel body) :=
  generate_complete (underInput_licensed channelTyped channelObject (generate_sound _ _ _ _ _ _ _ generated))

def underParallel (elements : List Pattern) (index : Nat) (inner : SiteData) : SiteData :=
  inner.wrapCollection (.authoredCollection 3) .hashBag elements index

theorem underParallel_licensed {bound : List TypeExpr} {elements : List Pattern} {index : Nat}
    {element : Pattern} {inner : SiteData}
    (typed : ElementsHaveType executionEnvironment.language snapshot.free bound elements (.base "Proc"))
    (objects : isObjectPatternList elements = true) (selected : elements[index]? = some element)
    (licensed : Licensed executionEnvironment.language snapshot.free permissions.sites
      bound (.base "Proc") element inner) :
    Licensed executionEnvironment.language snapshot.free permissions.sites bound (.base "Proc")
      (.collection .hashBag elements none) (underParallel elements index inner) := by
  apply Licensed.authoredCollection (rule := parallelRule) (parameterName := "ps")
  · change (parallelRule, 3) ∈ language.terms.zipIdx
    decide +kernel
  · rfl
  · decide +kernel
  · exact typed
  · exact objects
  · exact selected
  · exact licensed

theorem underParallel_generated {bound : List TypeExpr} {elements : List Pattern} {index : Nat}
    {element : Pattern} {inner : SiteData}
    (typed : ElementsHaveType executionEnvironment.language snapshot.free bound elements (.base "Proc"))
    (objects : isObjectPatternList elements = true) (selected : elements[index]? = some element)
    (generated : inner ∈ generate executionEnvironment.language snapshot.free permissions.sites
      bound (.base "Proc") element) :
    underParallel elements index inner ∈ generate executionEnvironment.language snapshot.free permissions.sites
      bound (.base "Proc") (.collection .hashBag elements none) :=
  generate_complete (underParallel_licensed typed objects selected (generate_sound _ _ _ _ _ _ _ generated))

theorem underInput_keeps_binders (channel body : Pattern) (inner : SiteData) :
    (underInput channel body inner).focusBound = inner.focusBound ∧
      (underInput channel body inner).address = 1 :: 0 :: inner.address ∧
      (underInput channel body inner).typingFrames =
        .application 5 1 :: .lambda (.base "Name") :: inner.typingFrames := ⟨rfl, rfl, rfl⟩

def inputReceipt (bound : List TypeExpr) (outerChannel channel body payload : Pattern) (rest : List Pattern) :
    GeneralRuleJobs.Receipt :=
  let root := rootReceipt (.base "Name" :: bound) channel body payload rest
  { root with
    job := {root.job with site := underInput outerChannel (source channel body payload rest) root.job.site}
    target := input outerChannel root.localTarget }

theorem input_receipt_valid {bound : List TypeExpr} {outerChannel channel body payload : Pattern}
    {rest : List Pattern}
    (outerTyped : OpenPatternWellSorted language snapshot.free bound (.base "Name") outerChannel)
    (channelTyped : OpenPatternWellSorted language snapshot.free (.base "Name" :: bound) (.base "Name") channel)
    (bodyTyped : OpenPatternWellSorted language snapshot.free
      (.base "Name" :: .base "Name" :: bound) (.base "Proc") body)
    (sealed : ScopedPattern.binderSafeAt "NQuote" (bound.length + 2) body = true)
    (names : ReflectiveInstantiation.namesAdmitted
      rhoReflectivePresentation.toReflectivePresentationDecl body = true)
    (payloadTyped : OpenPatternWellSorted language snapshot.free (.base "Name" :: bound) (.base "Proc") payload)
    (restTyped : ElementsHaveType language snapshot.free (.base "Name" :: bound) rest (.base "Proc"))
    (restRepresented : ∀ pattern ∈ rest, Represented pattern) :
    (inputReceipt bound outerChannel channel body payload rest).Valid plan bound (.base "Proc")
      (input outerChannel (source channel body payload rest)) := by
  have root := root_receipt_valid channelTyped bodyTyped (by simpa using sealed) names
    payloadTyped restTyped restRepresented
  have licensed := underInput_licensed
    (GeneralLanguageTyping.type_transport (GeneralPlanEnvironment.grammar plan).symm outerTyped.1)
    outerTyped.2.2.1 root.1.2
  have represented : (inputReceipt bound outerChannel channel body payload rest).job.site.acceptsReplacementRepresentation
      executionEnvironment.language (.collection .hashBag (reflectiveBody body payload :: rest) none) = true := rfl
  have targetTyped := licensed.replace_checked _ represented root.2.2.2.2.1
  have targetRepresented := input_represented ⟨outerTyped.2.1, outerTyped.2.2.1⟩
    ⟨root.2.2.2.2.2.1, root.2.2.2.2.2.2.1⟩
  exact ⟨⟨root.1.1, licensed⟩, root.2.1, represented, rfl,
    targetTyped, targetRepresented.1, targetRepresented.2, targetTyped.isWellScopedAt⟩

theorem input_receipt_emitted {bound : List TypeExpr} {outerChannel channel body payload : Pattern}
    {rest : List Pattern}
    (outerTyped : OpenPatternWellSorted language snapshot.free bound (.base "Name") outerChannel)
    (channelTyped : OpenPatternWellSorted language snapshot.free (.base "Name" :: bound) (.base "Name") channel)
    (bodyTyped : OpenPatternWellSorted language snapshot.free
      (.base "Name" :: .base "Name" :: bound) (.base "Proc") body)
    (sealed : ScopedPattern.binderSafeAt "NQuote" (bound.length + 2) body = true)
    (names : ReflectiveInstantiation.namesAdmitted
      rhoReflectivePresentation.toReflectivePresentationDecl body = true)
    (payloadTyped : OpenPatternWellSorted language snapshot.free (.base "Name" :: bound) (.base "Proc") payload)
    (restTyped : ElementsHaveType language snapshot.free (.base "Name" :: bound) rest (.base "Proc"))
    (restRepresented : ∀ pattern ∈ rest, Represented pattern) :
    GeneralRuleJobs.finish? plan bound (.base "Proc")
      (inputReceipt bound outerChannel channel body payload rest).job commTrace
      (captured (bound.length + 1) channel body payload rest)
      (captured (bound.length + 1) channel body payload rest) [] =
      some (inputReceipt bound outerChannel channel body payload rest) := by
  exact GeneralRuleJobs.finish_complete
    (input_receipt_valid outerTyped channelTyped bodyTyped sealed names payloadTyped restTyped restRepresented)

#print axioms underInput_generated
#print axioms underParallel_generated
#print axioms input_receipt_emitted

end Mettapedia.OSLF.MeTTaIL.GeneralRho
