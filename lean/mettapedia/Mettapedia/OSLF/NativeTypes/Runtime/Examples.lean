import Mettapedia.OSLF.NativeTypes.Runtime.Display
import Mettapedia.OSLF.NativeTypes.Runtime.Controls
import Mettapedia.OSLF.NativeTypes.Runtime.GenerationControls
import Mettapedia.OSLF.NativeTypes.Runtime.ModalInstanceControls
import Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverControls

/-!
# Running generated native judgments on original language presentations

Every catalogue and answer below comes from the public generator and its
installed retained formula machine. Formula branches share the supplied work
account. Printed observations are the receipts encountered by this query;
settling a query does not enumerate every possible receipt.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Runtime.Examples

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Executable
open Mettapedia.OSLF.NativeTypes.Runtime (Installed)
open Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax (Query Readout)

abbrev rhoRequest : Request := Mettapedia.OSLF.NativeTypes.Runtime.GenerationControls.rhoRequest
abbrev lambdaRequest : Request := Mettapedia.OSLF.NativeTypes.Runtime.GenerationControls.lambdaRequest
abbrev machineRequest : Request := Mettapedia.OSLF.NativeTypes.Runtime.GenerationControls.machineRequest

structure Example where
  title : String
  query : Query
  source : Pattern
  budget : Nat

def readoutText : Readout → String
  | .unknownConstructor name => "refused: no generated constructor named " ++ name
  | .checked result => Mettapedia.OSLF.NativeTypes.Runtime.Display.readoutText result

def report (installed : Installed) (demo : Example) : String :=
  let session := Mettapedia.OSLF.NativeTypes.Executable.ask installed demo.query demo.source demo.budget
  let observations := session.observations.zipIdx.map fun (observation, ordinal) =>
    "  receipt " ++ toString ordinal ++ "; formula position=" ++ reprStr observation.location ++
      "; " ++ Mettapedia.OSLF.NativeTypes.Semantics.Display.renderPattern
        (installed.native.render observation.source) ++ " -> " ++
      Mettapedia.OSLF.NativeTypes.Semantics.Display.renderPattern
        (installed.native.render (installed.runtime.cursor.target observation.source observation.receipt))
  String.intercalate "\n" <|
    [demo.title ++ ": " ++ Mettapedia.OSLF.NativeTypes.Runtime.Display.queryText demo.query,
     "  source: " ++ Mettapedia.OSLF.NativeTypes.Semantics.Display.renderPattern demo.source,
     "  result: " ++ readoutText session.readout ++
       "; budget=" ++ toString demo.budget ++ "; work=" ++ toString session.spent,
     "  retained receipts=" ++ toString session.observations.length] ++ observations

/-- The view records the actual saved receipt sequence, including each formula
position and both endpoint readouts. Distinct rows are not deduplicated. -/
def saved {installed : Installed} {query : Query} {source : Pattern}
    (session : Mettapedia.OSLF.NativeTypes.Runtime.NamedSession
      installed.native installed.runtime query source) :
    Readout × Nat × List (List Nat × Pattern × Pattern) :=
  (session.readout, session.spent, session.observations.map fun observation =>
    (observation.location, installed.native.render observation.source,
      installed.native.render (installed.runtime.cursor.target observation.source observation.receipt)))

def recorded (request : Request) (query : Query) (source : Pattern) (budget : Nat) :
    Except GenerationIssue (Readout × Nat × List (List Nat × Pattern × Pattern)) :=
  (Mettapedia.OSLF.NativeTypes.Executable.generate request).map fun installed => saved (installed := installed) (Mettapedia.OSLF.NativeTypes.Executable.ask installed query source budget)

def resumed (request : Request) (query : Query) (source : Pattern) (first more : Nat) :
    Except GenerationIssue (Readout × Nat × List (List Nat × Pattern × Pattern)) :=
  (Mettapedia.OSLF.NativeTypes.Executable.generate request).map fun installed =>
    saved (installed := installed) (Mettapedia.OSLF.NativeTypes.Executable.resumeQuery (installed := installed) more (Mettapedia.OSLF.NativeTypes.Executable.ask installed query source first))

def observe (request : Request) (query : Query) (source : Pattern) (budget : Nat) :
    Except GenerationIssue Readout :=
  (Mettapedia.OSLF.NativeTypes.Executable.generate request).map fun installed => (Mettapedia.OSLF.NativeTypes.Executable.ask installed query source budget).readout

def yes : Readout := .checked (.judgment (.decided true))
def no : Readout := .checked (.judgment (.decided false))
def pending : Readout := .checked (.judgment .unknown)

def rhoExamples : List Example :=
  let redex := Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.Controls.redex
  let guarded := Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.Controls.guardedRedex
  let stuck := Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.Controls.stuckOutput
  let equivalentChannel := Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.Controls.equivalentChannelRedex
  [{title := "Parallel structure and a COMM result", query := .conj (.constructor "PPar")
      (.possibility (.constructor "PZero")), source := redex, budget := 100},
   {title := "The COMM result is not an output", query := .outgoingUniversal (.constructor "POutput"),
      source := redex, budget := 100},
   {title := "A protected input does not execute its body", query := .possibility .top,
      source := guarded, budget := 100},
   {title := "Name equations admit the same channel", query := .possibility (.constructor "PZero"),
      source := equivalentChannel, budget := 100},
   {title := "A completed absence judgment", query := .neg (.possibility .top), source := stuck, budget := 100},
   {title := "An unstarted query claims no absence", query := .possibility (.constructor "PZero"),
      source := redex, budget := 0}]

def lambdaExamples : List Example :=
  let beta := Mettapedia.OSLF.NativeTypes.Runtime.Controls.beta
  let identity := Mettapedia.OSLF.NativeTypes.Runtime.Controls.identity
  let guardedBeta := Mettapedia.OSLF.NativeTypes.Runtime.Controls.guardedBeta
  [{title := "Application structure and its beta result", query := .conj (.constructor "App")
      (.possibility (.constructor "Lam")), source := beta, budget := 60},
   {title := "Neither a lambda nor a two-step computation", query := .disj (.constructor "Lam")
      (.possibility (.possibility .top)), source := beta, budget := 60},
   {title := "Beta respects the implication", query := .imp (.constructor "App")
      (.outgoingUniversal (.constructor "Lam")), source := beta, budget := 60},
   {title := "Admitted beta reduction beneath a lambda", query := .conj (.constructor "Lam")
      (.possibility (.constructor "Lam")), source := guardedBeta, budget := 60},
   {title := "A normal form has no successor", query := .possibility .top, source := identity, budget := 60},
   {title := "All successors of a normal form satisfy bottom", query := .outgoingUniversal .bottom,
      source := identity, budget := 60}]

def machineExamples : List Example :=
  let normal := Mettapedia.OSLF.NativeTypes.Runtime.Controls.normal
  let halt := Mettapedia.OSLF.NativeTypes.Runtime.Controls.halt
  [{title := "Configuration structure and its first return", query := .conj (.constructor "Normal")
      (.possibility (.constructor "Ret")), source := normal, budget := 500},
   {title := "One step does not halt", query := .possibility (.constructor "Halt"), source := normal, budget := 500},
   {title := "Two actual steps halt", query := .possibility (.possibility (.constructor "Halt")),
      source := normal, budget := 500},
   {title := "Every first successor is a return", query := .outgoingUniversal (.constructor "Ret"),
      source := normal, budget := 500},
   {title := "A halted machine has no successor", query := .possibility .top, source := halt, budget := 500},
   {title := "Unknown constructor is a refusal", query := .constructor "Missing", source := normal, budget := 500}]

#guard ((Mettapedia.OSLF.NativeTypes.Executable.generate rhoRequest).map fun installed =>
  installed.native.generated.structuralCatalogue.isEmpty || installed.native.generated.modalCatalogue.isEmpty) == .ok false
#guard ((Mettapedia.OSLF.NativeTypes.Executable.generate lambdaRequest).map fun installed =>
  installed.native.generated.structuralCatalogue.isEmpty || installed.native.generated.modalCatalogue.isEmpty) == .ok false
#guard ((Mettapedia.OSLF.NativeTypes.Executable.generate machineRequest).map fun installed =>
  installed.native.generated.structuralCatalogue.isEmpty || installed.native.generated.modalCatalogue.isEmpty) == .ok false

#guard observe rhoRequest (.conj (.constructor "PPar") (.possibility (.constructor "PZero")))
  Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.Controls.redex 100 == .ok yes
#guard observe rhoRequest (.outgoingUniversal (.constructor "POutput"))
  Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.Controls.redex 100 == .ok no
#guard observe lambdaRequest (.conj (.constructor "App") (.possibility (.constructor "Lam")))
  Mettapedia.OSLF.NativeTypes.Runtime.Controls.beta 60 == .ok yes
#guard observe lambdaRequest (.disj (.constructor "Lam") (.possibility (.possibility .top)))
  Mettapedia.OSLF.NativeTypes.Runtime.Controls.beta 60 == .ok no
#guard observe lambdaRequest (.imp (.constructor "App") (.outgoingUniversal (.constructor "Lam")))
  Mettapedia.OSLF.NativeTypes.Runtime.Controls.beta 60 == .ok yes
#guard observe lambdaRequest (.conj (.constructor "Lam") (.possibility (.constructor "Lam")))
  Mettapedia.OSLF.NativeTypes.Runtime.Controls.guardedBeta 60 == .ok yes
#guard observe machineRequest (.conj (.constructor "Normal") (.possibility (.constructor "Ret")))
  Mettapedia.OSLF.NativeTypes.Runtime.Controls.normal 500 == .ok yes
#guard observe machineRequest (.possibility (.constructor "Halt"))
  Mettapedia.OSLF.NativeTypes.Runtime.Controls.normal 500 == .ok no
#guard observe machineRequest (.possibility (.possibility (.constructor "Halt")))
  Mettapedia.OSLF.NativeTypes.Runtime.Controls.normal 500 == .ok yes

#guard (recorded rhoRequest (.possibility (.constructor "PZero"))
  Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.Controls.redex 0).map (fun view =>
    (view.1, view.2.1, view.2.2.isEmpty)) == .ok (pending, 0, true)
#guard (recorded rhoRequest (.possibility (.constructor "PZero"))
  Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.Controls.redex 100).map (fun view =>
    (view.1, decide (view.2.1 ≤ 100), view.2.2.isEmpty)) == .ok (yes, true, false)
#guard (recorded machineRequest (.possibility (.possibility (.constructor "Halt")))
  Mettapedia.OSLF.NativeTypes.Runtime.Controls.normal 500).map (fun view =>
    (view.1, decide (view.2.1 ≤ 500), view.2.2.length)) == .ok (yes, true, 2)
#guard resumed machineRequest (.possibility (.possibility (.constructor "Halt")))
  Mettapedia.OSLF.NativeTypes.Runtime.Controls.normal 7 493 = recorded machineRequest
    (.possibility (.possibility (.constructor "Halt"))) Mettapedia.OSLF.NativeTypes.Runtime.Controls.normal 500
#guard resumed rhoRequest (.conj (.constructor "PPar") (.possibility (.constructor "PZero")))
  Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.Controls.redex 3 97 = recorded rhoRequest
    (.conj (.constructor "PPar") (.possibility (.constructor "PZero")))
      Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.Controls.redex 100

namespace ModalInstanceExample

open Mettapedia.OSLF.NativeTypes.Decision.Reference.ModalControls

def continuationDecision (permit : Bool) : Bool :=
  @decide (((codes permit).inputs.2 supplied).meaning (request permit).target)
    ((decisions permit).continuation supplied (request permit).target)

def report (permit : Bool) (budget : Nat) : String :=
  let assignments := supplied.map fun (name, value) =>
    name ++ "=" ++ Mettapedia.OSLF.NativeTypes.Semantics.Display.renderPattern value.body ++
      "; dependencies=" ++ reprStr value.dependencies ++ "; ambient=" ++ toString value.ambient
  let header :=
    ["Supplied non-root modal instance; schema position=" ++ reprStr schema.position,
     "  rely names=" ++ reprStr schema.relyNames,
     "  assignment: " ++ String.intercalate ", " assignments,
     "  focus: " ++ Mettapedia.OSLF.NativeTypes.Semantics.Display.renderPattern focus,
     "  specified RHS: " ++ Mettapedia.OSLF.NativeTypes.Semantics.Display.renderPattern (request permit).target,
     "  substituted continuation at the specified RHS: " ++ toString (continuationDecision permit)]
  let answer := match Mettapedia.OSLF.NativeTypes.Runtime.ModalInstanceControls.generatedRun permit budget with
    | .error issue => ["  generation refused: " ++ reprStr issue]
    | .ok view =>
        ["  result: " ++ Mettapedia.OSLF.NativeTypes.Runtime.Display.readoutText view.1 ++
           "; budget=" ++ toString budget ++ "; work=" ++ toString view.2.1,
         "  retained receipts=" ++ toString view.2.2.length] ++
        view.2.2.zipIdx.map fun ((source, target), ordinal) =>
          "  receipt " ++ toString ordinal ++ "; " ++
            Mettapedia.OSLF.NativeTypes.Semantics.Display.renderPattern source ++ " -> " ++
            Mettapedia.OSLF.NativeTypes.Semantics.Display.renderPattern target
  String.intercalate "\n" (header ++ answer)

#guard continuationDecision true
#guard !continuationDecision false
#guard (Mettapedia.OSLF.NativeTypes.Runtime.ModalInstanceControls.generatedRun true 1000).map
  (fun view => (view.1, decide (view.2.1 ≤ 1000), view.2.2.length)) ==
    .ok (.judgment (.decided true), true, 1)
#guard (Mettapedia.OSLF.NativeTypes.Runtime.ModalInstanceControls.generatedRun false 1000).map
  (fun view => (view.1, decide (view.2.1 ≤ 1000), view.2.2.length)) ==
    .ok (.judgment (.decided false), true, 1)

end ModalInstanceExample

def runConsumer (title : String) (request : Request) (examples : List Example) : IO Unit := do
  IO.println title
  match Mettapedia.OSLF.NativeTypes.Executable.generate request with
  | .error issue => IO.println ("Generation refused: " ++ reprStr issue)
  | .ok installed =>
    IO.println (Mettapedia.OSLF.NativeTypes.Runtime.Display.catalogue installed.native)
    for demo in examples do
      IO.println (report installed demo)

def main : IO Unit := do
  IO.println "Generated native judgments on original presentations"
  runConsumer "Rho" rhoRequest rhoExamples
  runConsumer "Scoped lambda" lambdaRequest lambdaExamples
  runConsumer "Partial-recursive machine" machineRequest machineExamples
  IO.println (ModalInstanceExample.report true 1000)
  IO.println (ModalInstanceExample.report false 1000)

#eval main

end Mettapedia.OSLF.NativeTypes.Runtime.Examples
