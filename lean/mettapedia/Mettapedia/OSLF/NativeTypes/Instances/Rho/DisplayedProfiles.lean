import Mettapedia.OSLF.NativeTypes.SortProfiles.DisplayedGraph
import Mettapedia.OSLF.NativeTypes.Instances.Rho.ProfileBoundary

open Mettapedia.OSLF.Framework

/-!
# Original rho's displayed modal interface and corrected profile admission

The raw authored COMM source determines the receive occurrence. Its channel is
an index, its payload and bag remainder are rely inputs, and its continuation
body is ambient.  QuoteDrop remains ordinary conversion and supplies no fresh
typed-occurrence matching in a bare program presentation.  The old universal
fixed-output diagnostic is retained and still rejects every original vertex.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Rho.DisplayedProfiles

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.OSLF.NativeTypes.SortProfiles.DisplayedGraph

def receiveIndex? : Option Nat :=
  (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate rhoCalc).findIdx? fun site =>
    site.declaration == 0 && site.position == [0]

def receiveInterface? : Option (List String × List String) := do
  let index ← receiveIndex?
  let site ← (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.generate rhoCalc)[index]?
  some (indexNames site, site.relyNames)

theorem receive_interface_exact : receiveInterface? = some (["n"], ["q", "rest"]) := by
  decide +kernel

theorem original_carriers_known : carriersKnown rhoCalc = true := by
  cbv

theorem original_allStar_admitted : admit? rhoCalc [] (allStar rhoCalc) = some true :=
  (admission_exact _ _ _).mpr ⟨original_carriers_known, allStar_consistent _ _⟩

def allBox (language : LanguageDef) : Vertex language := (fun _ => .box, fun _ => .box)

theorem original_allBox_admitted : admit? rhoCalc [] (allBox rhoCalc) = some true := by
  apply (admission_exact _ _ _).mpr
  exact ⟨original_carriers_known, fun _ _ _ => rfl⟩

theorem ordinary_quoteDrop_preserved : rhoCalc.equations.length = 1 ∧
    rhoCalc.equations[0].name = "QuoteDrop" := by decide +kernel

def quotientControlRewrite : RewriteRule where
  name := "ChooseMarked"
  typeContext := [("x", .base "Term"), ("y", .base "Term")]
  premises := []
  left := .apply "Choose" [.apply "Mark" [.fvar "x"], .fvar "y", .fvar "x"]
  right := .fvar "y"

def quotientControl : LanguageDef where
  name := "DisplayedTargetVariable"
  types := ["Term"]
  terms := [
    {label := "Mark", category := "Term", params := [.simple "x" (.base "Term")], syntaxPattern := []},
    {label := "Choose", category := "Term", params := [.simple "first" (.base "Term"),
      .simple "second" (.base "Term"), .simple "third" (.base "Term")], syntaxPattern := []}]
  equations := []
  rewrites := [quotientControlRewrite]

def mismatchedTarget : Vertex quotientControl :=
  (fun slot => match slotLabel quotientControl slot with | .target => .box | _ => .star,
    fun _ => .star)

theorem actual_target_variable_rejected : bareCheck quotientControl mismatchedTarget = false := by
  cbv

theorem target_variable_center_proper :
    (center quotientControl []).Nonempty ∧ center quotientControl [] ≠ Finset.univ := by
  refine ⟨⟨allStar quotientControl, (center_exact _ _ _).mpr (allStar_consistent _ _)⟩, ?_⟩
  intro full
  have member : mismatchedTarget ∈ center quotientControl [] := by
    rw [full]
    exact Finset.mem_univ _
  have accepted := (check_exact _ _ _).mpr ((center_exact _ _ _).mp member)
  rw [show check quotientControl [] mismatchedTarget = false from actual_target_variable_rejected] at accepted
  cases accepted

#guard receiveInterface? == some (["n"], ["q", "rest"])
#guard carriersKnown rhoCalc
#guard !(bareCheck quotientControl mismatchedTarget)

#print axioms original_allStar_admitted
#print axioms original_allBox_admitted
#print axioms target_variable_center_proper

end Mettapedia.OSLF.NativeTypes.Instances.Rho.DisplayedProfiles
