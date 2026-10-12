import Mettapedia.OSLF.MeTTaIL.StructuralDescentScheduledReadout
import Mettapedia.OSLF.MeTTaIL.StructuralDescentControls

/-!
# Controls for the generic retained execution machine

The original full lambda profile, partial-recursive machine and sorted
let/case language all run through the same fine-grained scheduler. Receipts
are read only after actual matching, ordered premise work and typed reduct
construction. Initial emptiness leaves pending work and permits no absence
claim.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax GeneralPremise
open StructuralDescent.Controls

private def term : TypeExpr := .base "Term"

def lambdaStart := begin lambdaEnvironment [] term nestedRedex

def lambdaRun := resume lambdaEnvironment [] term nestedRedex 2000 lambdaStart

#guard lambdaStart.answers.isEmpty
#guard !Scheduler.complete lambdaStart
#guard (receipts lambdaRun).map (·.target) == [nestedTarget]
#guard (receipts lambdaRun).map (fun answer =>
  (answer.index, answer.history.flatMap childIndices)) == [(1, [1, 0])]
#guard Scheduler.complete lambdaRun

#guard (resume lambdaEnvironment [] term nestedRedex 2000 lambdaStart).work ==
  (resume lambdaEnvironment [] term nestedRedex 1234
    (resume lambdaEnvironment [] term nestedRedex 766 lambdaStart)).work

#guard (receipts (resume lambdaEnvironment [] term nestedRedex 2000 lambdaStart)).map (·.target) ==
  (receipts (resume lambdaEnvironment [] term nestedRedex 1234
    (resume lambdaEnvironment [] term nestedRedex 766 lambdaStart))).map (·.target)

def partialLambda := resume lambdaEnvironment [] term nestedRedex 1 lambdaStart

#guard (receipts partialLambda).isEmpty
#guard !Scheduler.complete partialLambda
#guard !(resume lambdaEnvironment [] term nestedRedex 1999 partialLambda).answers.isEmpty

def partrecRun := resume partrecEnvironment [] (.base "Cfg") partrecStart 500
  (begin partrecEnvironment [] (.base "Cfg") partrecStart)

#guard (receipts partrecRun).map (·.target) == partrecTargets
#guard Scheduler.complete partrecRun

namespace LetCaseControls
open Mettapedia.OSLF.NativeTypes.Instances.LetCase

private def env := StructuralDescent.Controls.LetCaseControls.environment
private def source := StructuralDescent.Controls.LetCaseControls.nested
private def unit := StructuralDescent.Controls.LetCaseControls.unit
private def snapshot := resume env [] computation source 2000 (begin env [] computation source)

#guard Scheduler.complete snapshot
#guard ((receipts snapshot).map (·.target)).contains
  (caseTerm (pair unit unit) (returnValue unit))
#guard (receipts snapshot).any (fun answer =>
  answer.index == 4 && answer.history.flatMap childIndices == [0])

end LetCaseControls

#print axioms finishSource_occurrences
#print axioms drained_receipts_complete
#print axioms resume_add
#print axioms receipts_preserved

end Mettapedia.OSLF.MeTTaIL.StructuralDescent.Scheduled.Controls
