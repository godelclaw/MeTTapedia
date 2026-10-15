import Mettapedia.OSLF.NativeTypes.Structural.Execution
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceCertificateSound
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFiniteCarrier

open Mettapedia.OSLF.Framework

/-!
# Structural readouts from the certified occurrence executor

The executor earns the object and representative coverage needed by the
structural checker. A partial representative search admits only positive
structural evidence; negative answers require its checked certificate.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Structural

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier

/-- The checker consumes the actual equation representatives retained by the
occurrence executor, with its unchanged grammar and typing contexts. -/
def checkFrontierStructural (request : Request) (state : State request) (former : Former) : Bool :=
  checkStructural request.plan.snapshot.language request.plan.snapshot.free request.bound
    former (representedPatterns request state)

theorem certified_class_objects {request : Request} {state : State request}
    (admitted : Admitted request) (checked : checkCertificate request state = true)
    {term : Pattern}
    (equivalent : Relation.EqvGen
      (Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceSemantics.Equation
        request.plan request.bound request.expected) request.root term) :
    isObjectPattern term = true := by
  have member := (certified_representatives_exact admitted checked term).mpr equivalent
  exact (universe_member_typed request term (represented_within admitted state term member)).2.2.1

theorem checkFrontierStructural_sound {request : Request} {state : State request}
    {former : Former} (checked : checkFrontierStructural request state former = true) :
    StructuralHolds request.plan.snapshot.language request.plan.snapshot.free request.bound
      (Relation.EqvGen (Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceSemantics.Equation
        request.plan request.bound request.expected)) former request.root := by
  apply checkStructural_sound (source := request.root) (representatives := representedPatterns request state)
    (equation := Relation.EqvGen (Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceSemantics.Equation
      request.plan request.bound request.expected)) ?_ checked
  intro term member
  obtain ⟨representative, inside, equal⟩ := List.mem_map.mp member
  rw [← equal]
  exact representative.justified.equivalent

/-- The class-object side condition is derived from the certified finite
carrier; callers do not supply an independent completeness predicate. -/
theorem checkFrontierStructural_iff {request : Request} {state : State request}
    (admitted : Admitted request) (checked : checkCertificate request state = true)
    (former : Former) :
    checkFrontierStructural request state former = true ↔
      StructuralHolds request.plan.snapshot.language request.plan.snapshot.free request.bound
        (Relation.EqvGen (Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceSemantics.Equation
          request.plan request.bound request.expected)) former request.root := by
  apply checkStructural_iff
  · intro term member
    exact (certified_representatives_exact admitted checked term).mp member
  · intro term related
    exact (certified_representatives_exact admitted checked term).mpr related
  · intro term related
    exact certified_class_objects admitted checked related

/-- Without coverage, failed discovery remains unknown. Successful discovery
is already justified by retained representatives. -/
def readFrontierStructural (request : Request) (state : State request) (former : Former) : Option Bool :=
  if checkFrontierStructural request state former then some true
  else if checkCertificate request state then some false else none

theorem readFrontierStructural_true {request : Request} {state : State request} {former : Former}
    (read : readFrontierStructural request state former = some true) :
    StructuralHolds request.plan.snapshot.language request.plan.snapshot.free request.bound
      (Relation.EqvGen (Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceSemantics.Equation
        request.plan request.bound request.expected)) former request.root := by
  unfold readFrontierStructural at read
  split at read
  · exact checkFrontierStructural_sound (by assumption)
  · split at read <;> cases read

theorem readFrontierStructural_false {request : Request} {state : State request} {former : Former}
    (admitted : Admitted request)
    (read : readFrontierStructural request state former = some false) :
    ¬ StructuralHolds request.plan.snapshot.language request.plan.snapshot.free request.bound
      (Relation.EqvGen (Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceSemantics.Equation
        request.plan request.bound request.expected)) former request.root := by
  unfold readFrontierStructural at read
  split at read
  · cases read
  · rename_i failed
    split at read
    · rename_i checked
      intro holds
      exact failed ((checkFrontierStructural_iff admitted checked former).mpr holds)
    · cases read

end Mettapedia.OSLF.NativeTypes.Structural
