import Mettapedia.OSLF.NativeTypes.Instances.Rho.Driver
import Mettapedia.OSLF.NativeTypes.Executable
import Mettapedia.OSLF.NativeTypes.Instances.Rho.CanonicalControls

open Mettapedia.OSLF.Framework

/-!
# Original rho through the shared generated-query entry point

The same entry point resolves generated constructor names, checks structural
families and executes nested modal questions. Refused syntax and unfinished
work stay distinct from completed negative judgments. The parameterized
structural controls retain both argument order and the binder body.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverControls

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.NativeTypes.Runtime.Description Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax
open Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.Controls

def rho : Driver := Mettapedia.OSLF.NativeTypes.Instances.Rho.Driver.driver {}

def installed : Mettapedia.OSLF.NativeTypes.Runtime.Installed := Mettapedia.OSLF.NativeTypes.Runtime.Profiles.rho {}

def request : Mettapedia.OSLF.NativeTypes.Executable.Request := .canonicalRho
  Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverSource.snapshot Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverSource.fragment {}

theorem generated_original : Mettapedia.OSLF.NativeTypes.Executable.generate request = .ok installed := by
  change (if GeneralOccurrenceFrontier.CoverageClaims.snapshotKey Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverSource.snapshot =
      GeneralOccurrenceFrontier.CoverageClaims.snapshotKey Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverSource.snapshot then
    if Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverSource.fragment = Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverSource.fragment then .ok installed
    else .error (.fragmentMismatch .canonicalRho)
    else .error (.snapshotMismatch .canonicalRho) :
      Except Mettapedia.OSLF.NativeTypes.Executable.GenerationIssue Mettapedia.OSLF.NativeTypes.Runtime.Installed) = .ok installed
  simp

def observe (query : Query) (source : Pattern) (budget : Nat) :=
  (Mettapedia.OSLF.NativeTypes.Executable.generate request).map fun output =>
    (Mettapedia.OSLF.NativeTypes.Executable.ask output query source budget).readout

def yes : Except Mettapedia.OSLF.NativeTypes.Executable.GenerationIssue Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Readout :=
  .ok (.checked (.judgment (.decided true)))
def no : Except Mettapedia.OSLF.NativeTypes.Executable.GenerationIssue Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Readout :=
  .ok (.checked (.judgment (.decided false)))
def pending : Except Mettapedia.OSLF.NativeTypes.Executable.GenerationIssue Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Readout :=
  .ok (.checked (.judgment .unknown))

#guard rho.generated.snapshot.language.rewrites.length == 2
#guard rho.generated.structuralCatalogue.length == rhoCalc.terms.length
#guard rho.profileAdmission == some true
#guard rho.generated.equationAdmission == some false
#guard observe (.constructor "PZero") zero 10 == yes
#guard observe (.constructor "POutput") zero 10 == no
#guard observe (.constructor "PPar") zero 10 == yes
#guard observe (.conj (.constructor "PPar") (.possibility (.constructor "PZero"))) redex 100 == yes
#guard observe (.possibility (.constructor "PZero")) redex 0 == pending
#guard observe (.possibility (.constructor "PZero")) redex 80 == yes
#guard observe (.possibility (.constructor "PZero")) redex 90 == yes
#guard observe (.possibility (.constructor "PZero")) parallelRedex 100 == yes
#guard observe (.possibility (.constructor "PZero")) equivalentChannelRedex 100 == yes
#guard observe (.possibility (.constructor "PZero")) reflectiveRedex 100 == yes
#guard observe (.possibility (.constructor "POutput")) redex 100 == no
#guard observe (.outgoingUniversal (.constructor "PZero")) redex 100 == yes
#guard observe (.outgoingUniversal (.constructor "POutput")) redex 100 == no
#guard observe (.possibility (.possibility .top)) redex 100 == no
#guard observe (.possibility .top) payloadRedex 100 == no
#guard observe (.possibility .top) guardedRedex 100 == no
#guard observe (.possibility .top) quotedRedex 100 == no
#guard observe (.possibility .top) stuckOutput 100 == no
#guard observe (.outgoingUniversal .bottom) payloadRedex 100 == yes
#guard observe (.neg (.possibility .top)) stuckOutput 100 == yes
#guard observe .top (.apply "POutput" [zero, zero]) 100 ==
  .ok (.checked (.sourceRefused .illScopedOrSorted))
#guard observe .top (.apply "PInput" [channel, .lambda none
  (.apply "PDrop" [.apply "NQuote" [.apply "PDrop" [.bvar 0]]])]) 100 ==
  .ok (.checked (.sourceRefused .illScopedOrSorted))

def outputLeaf (first second : Pattern) : Mettapedia.OSLF.NativeTypes.Instances.Rho.Driver.Leaf :=
  {index := ⟨4, by decide⟩
   carrier := rfl
   inputs := Mettapedia.OSLF.NativeTypes.Instances.Rho.OrderedChecking.equalInputs rhoCalc.terms[4]
     (fun position => if position.val = 0 then first else second)}

def inputLeaf (name body : Pattern) : Mettapedia.OSLF.NativeTypes.Instances.Rho.Driver.Leaf :=
  {index := ⟨5, by decide⟩
   carrier := rfl
   inputs := Mettapedia.OSLF.NativeTypes.Instances.Rho.OrderedChecking.equalInputs rhoCalc.terms[5]
     (fun position => if position.val = 0 then name else body)}

def typedRead (leaf : Mettapedia.OSLF.NativeTypes.Instances.Rho.Driver.Leaf) (source : Pattern) :
    Mettapedia.OSLF.NativeTypes.Runtime.Description.Readout :=
  (Mettapedia.OSLF.NativeTypes.Executable.search installed (.atom leaf) source 10).readout

#guard typedRead (outputLeaf channel zero) output == .judgment (.decided true)
#guard typedRead (outputLeaf zero channel) output == .judgment (.decided false)
#guard typedRead (inputLeaf channel (.lambda none zero)) input == .judgment (.decided true)
#guard typedRead (inputLeaf channel (.lambda none (.apply "PDrop" [.bvar 0]))) input ==
  .judgment (.decided false)

def recorded (query : Query) (source : Pattern) (budget : Nat) :=
  (elaborate installed.native query).map fun formula =>
    let result := Mettapedia.OSLF.NativeTypes.Executable.search installed formula source budget
    (result.readout, result.spent, result.settled, result.observations.map fun observation =>
      (observation.receipt.val.declarationIndex, observation.receipt.val.alternativeIndex,
        observation.receipt.val.target, observation.location))

#guard (recorded (.possibility .top) redex 80).toOption ==
  (recorded (.possibility .top) redex 90).toOption
#guard ((recorded (.possibility .top) redex 100).toOption.map fun result =>
  (result.1, result.2.2.1, result.2.2.2)) ==
  some (.judgment (.decided true), true, [(0, 0, zero, [])])
#guard ((recorded (.outgoingUniversal .top) redex 100).toOption.map fun result =>
  (result.1, result.2.2.1, result.2.2.2)) ==
  some (.judgment (.decided true), true, [(0, 0, zero, [])])
#guard ((recorded (.possibility .top) stuckOutput 90).toOption.map fun result =>
  (result.1, result.2.2.1, result.2.2.2)) ==
  some (.judgment (.decided false), true, [])

theorem successful_queries_have_original_meaning (query : Query) (source : Pattern) (budget : Nat)
    (read : observe query source budget = yes) : Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Meaning rho query source := by
  rw [observe, generated_original] at read
  exact Mettapedia.OSLF.NativeTypes.Runtime.named_positive (Mettapedia.OSLF.NativeTypes.Executable.ask installed query source budget)
    (Except.ok.inj read)

theorem negative_queries_refute_original_meaning (query : Query) (source : Pattern) (budget : Nat)
    (read : observe query source budget = no) : ¬ Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.Meaning rho query source := by
  rw [observe, generated_original] at read
  exact Mettapedia.OSLF.NativeTypes.Runtime.named_negative (Mettapedia.OSLF.NativeTypes.Executable.ask installed query source budget)
    (Except.ok.inj read)

end Mettapedia.OSLF.NativeTypes.Instances.Rho.DriverControls
