import Mettapedia.OSLF.NativeTypes.GeneratedLogic.TokenNetAdequacy
import Mettapedia.Cybernetics.DistinctionCalculus.Basic

/-!
# Saturated bisimilarity as indistinguishability under the native-type observer

In the distinction calculus an observer is a tolerance on a carrier, and an observer that reports data is crisp and
metric (`Tolerance.ofReport`). The native types of a token net are such an observer of its markings: a marking reports
the context-labelled native types it has (`nativeReport`).

- **Two markings are indistinguishable under the native-type observer exactly when they are saturated bisimilar**
  against every environment of tokens (`indistinguishable_iff_saturated`), and apart exactly when some environment
  tells them apart (`apart_iff_not_saturated`). The observer is metric (`nativeObserver_metric`), so its zero distance
  is an equivalence: the behavioural classes of markings.
- **The observer keeps the behavioural distinctions and loses the structural ones**: in the Petri net `{D}` and the
  empty marking are indistinguishable, since no rule consumes `D`, and `{A}` and the empty marking are apart
  (`ContextLabelControls`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.TokenNets

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.GSLT.BagHennessyMilner (SaturatedBisimilarIn)
open Mettapedia.Cybernetics.DistinctionCalculus (Tolerance)

variable {language : LanguageDef} (net : TokenNet language) (relEnv : RelationEnv)

/-- **The native-type report of a marking**: the context-labelled native types over the net's contexts it has. -/
def nativeReport (names : List String) : Set NetFormula :=
  {formula | formula.Within (TokenBag net) ∧
    (referenceStructure relEnv language).sat Env.closed (nativeFormula formula) (marking names)}

open Classical in
/-- **The native-type observer of the net's markings**: the crisp tolerance of the native-type report. -/
noncomputable def nativeObserver : Tolerance (List String) := Tolerance.ofReport (nativeReport net relEnv)

/-- **The native-type observer is metric.** -/
theorem nativeObserver_metric : (nativeObserver net relEnv).Metric := by
  classical
  exact Tolerance.ofReport_metric _

/-- **Indistinguishable under the native-type observer exactly when saturated bisimilar.** -/
theorem indistinguishable_iff_saturated {first second : List String} (firstRegion : Region net first)
    (secondRegion : Region net second) :
    (nativeObserver net relEnv).Indistinguishable first second ↔
      SaturatedBisimilarIn (reactions language) (TokenBag net) (first : Multiset String) (second : Multiset String) := by
  classical
  rw [nativeObserver, Tolerance.ofReport_indistinguishable, saturated_iff_nativeTypes (relEnv := relEnv) net
    firstRegion secondRegion, Set.ext_iff]
  simp only [nativeReport, Set.mem_ofPred_eq]
  exact forall_congr' fun formula => ⟨fun same within => by simpa [within] using same,
    fun same => ⟨fun ⟨within, holds⟩ => ⟨within, (same within).mp holds⟩,
      fun ⟨within, holds⟩ => ⟨within, (same within).mpr holds⟩⟩⟩

/-- **Apart under the native-type observer exactly when some environment tells the markings apart.** -/
theorem apart_iff_not_saturated {first second : List String} (firstRegion : Region net first)
    (secondRegion : Region net second) :
    (nativeObserver net relEnv).Apart first second ↔
      ¬ SaturatedBisimilarIn (reactions language) (TokenBag net) (first : Multiset String) (second : Multiset String) := by
  rw [← indistinguishable_iff_saturated net relEnv firstRegion secondRegion,
    ← Tolerance.not_apart_iff_indistinguishable, not_not]

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.TokenNets
