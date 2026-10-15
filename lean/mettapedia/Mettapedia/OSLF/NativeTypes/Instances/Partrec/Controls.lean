import Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated
import Mettapedia.Languages.PartrecMachine.Adequacy

open Mettapedia.OSLF.Framework

/-!
# Original-machine native decision controls

The same generated constructor leaves occur directly and beneath nested
operational modalities. Positive and negative judgments retain the checked
native meaning, and a paused empty search remains inconclusive. The reference
engine comparison below is an executable control, separate from the generic
independent occurrence coverage theorem.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated

def nil : Pattern := .apply "Nil" []
def haltCont : Pattern := .apply "HaltCont" []
def zeroCode : Pattern := .apply "ZeroCode" []
def source : Pattern := .apply "Normal" [zeroCode, haltCont, nil]
def firstTarget : Pattern := .apply "Ret" [haltCont, .apply "Cons" [.apply "Zero" [], nil]]
def finalTarget : Pattern := .apply "Halt" [.apply "Cons" [.apply "Zero" [], nil]]
def stopped : Pattern := .apply "Halt" [nil]

theorem source_admitted : Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.Source [] source :=
  checkOpenPatternWellSorted_sound (by decide +kernel)

theorem stopped_admitted : Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.Source [] stopped :=
  checkOpenPatternWellSorted_sound (by decide +kernel)

def observe (label : String) (make : Formula CfgFormer → Formula CfgFormer)
    (program : Pattern) (budget : Nat) : Option (Option Bool) := do
  let former ← former? label
  return (run [] (make (.atom former)) program budget).answer

def composed (program : Pattern) (budget : Nat) : Option (Option Bool) := do
  let normal ← former? "Normal"
  let halt ← former? "Halt"
  return (run [] (.conj (.atom normal) (.possibility (.possibility (.atom halt)))) program budget).answer

def implication (program : Pattern) (budget : Nat) : Option (Option Bool) := do
  let normal ← former? "Normal"
  let halt ← former? "Halt"
  return (run [] (.imp (.atom normal) (.possibility (.possibility (.atom halt)))) program budget).answer

def universalAfterStep (program : Pattern) (budget : Nat) : Option (Option Bool) := do
  let halt ← former? "Halt"
  return (run [] (.outgoingUniversal (.possibility (.atom halt))) program budget).answer

def frontierTargets (program : Pattern) : List Pattern :=
  let engine := Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.backend []
  (engine.frontier (engine.completionBudget program) program).map (engine.target program)

def declarationOrigins (program : Pattern) : List Nat :=
  let engine := Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.backend []
  (engine.frontier (engine.completionBudget program) program).map fun receipt =>
    receipt.val.firing.job.declaration.declarationIndex

#guard cfgFormers.map (fun former => (Mettapedia.OSLF.NativeTypes.Generation.structuralDeclaration generated former.val).label) ==
  ["Halt", "Ret", "Normal"]
#guard observe "Normal" id source 1 == some (some true)
#guard observe "Ret" id source 1 == some (some false)
#guard observe "Halt" Formula.neg source 2 == some (some true)
#guard observe "Ret" Formula.possibility source 0 == some none
#guard observe "Ret" Formula.possibility source 300 == some (some true)
#guard observe "Halt" Formula.possibility source 300 == some (some false)
#guard observe "Halt" (fun leaf => .possibility (.possibility leaf)) source 300 == some (some true)
#guard observe "Ret" Formula.outgoingUniversal source 300 == some (some true)
#guard observe "Halt" Formula.outgoingUniversal source 300 == some (some false)
#guard composed source 300 == some (some true)
#guard composed finalTarget 300 == some (some false)
#guard implication source 300 == some (some true)
#guard implication finalTarget 300 == some (some true)
#guard universalAfterStep source 300 == some (some true)
#guard (run [] (.possibility .top) stopped 300).answer == some false
#guard (run [] (.outgoingUniversal .bottom) stopped 300).answer == some true
#guard frontierTargets source == [firstTarget]
#guard frontierTargets firstTarget == [finalTarget]
#guard frontierTargets stopped == []
#guard declarationOrigins source == [0]
#guard declarationOrigins firstTarget == [11]
#guard frontierTargets source == NonrecursiveReduction.rootReducts Mettapedia.Languages.PartrecMachine.partrecMachine source
#guard frontierTargets firstTarget == NonrecursiveReduction.rootReducts Mettapedia.Languages.PartrecMachine.partrecMachine firstTarget
#guard frontierTargets stopped == NonrecursiveReduction.rootReducts Mettapedia.Languages.PartrecMachine.partrecMachine stopped

theorem all_nested_generated_questions_complete (formula : Formula CfgFormer) :
    (run [] formula source (decisionBound [] formula source)).Decided :=
  whole_language_formula_complete [] formula source source_admitted

theorem all_nested_generated_questions_complete_at_normal_form (formula : Formula CfgFormer) :
    (run [] formula stopped (decisionBound [] formula stopped)).Decided :=
  whole_language_formula_complete [] formula stopped stopped_admitted

end Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls
