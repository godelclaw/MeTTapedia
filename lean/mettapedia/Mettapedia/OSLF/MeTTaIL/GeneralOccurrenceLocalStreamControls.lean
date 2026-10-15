import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceLocalStream
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceLocalControls

/-!
# Suspended conditional occurrence controls

The work cursor executes actual finite provider queries at typed sites,
including beneath a binder. A paused empty output remains unfinished;
resumption discovers the same ordered authored and provider origins as
full execution. Receipt transfer has its own work charge.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier.LocalEquationFree.Suspended.Controls

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open GeneralOccurrenceFrontier.LocalEquationFree.Controls
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.NativeTypes.Decision.Scheduling

abbrev experiment (source : Pattern) := stream (request source) whole_profile_equation_free

def delivered (source : Pattern) (budget : Nat) : List (Nat × List Nat × List TypeExpr × List Nat × Pattern) :=
  (Mettapedia.OSLF.NativeTypes.Decision.Scheduling.run (experiment source) budget).outputs.map fun receipt =>
    (receipt.val.firing.job.declaration.declarationIndex, receipt.val.firing.job.site.address,
      receipt.val.firing.job.site.focusBound, queryRows receipt.val.firing.premiseHistory, receipt.val.target)

#guard delivered (successor zero) 0 == []
#guard !(Mettapedia.OSLF.NativeTypes.Decision.Scheduling.run (experiment (successor zero)) 0).closed
#guard delivered (successor zero) 1 == []
#guard !(Mettapedia.OSLF.NativeTypes.Decision.Scheduling.run (experiment (successor zero)) 1).closed

#guard delivered (successor zero) 500 ==
  [(0, [], [], [0], accept zero), (0, [], [], [1], accept zero),
   (1, [], [], [0], accept zero), (1, [], [], [1], accept zero)]
#guard (Mettapedia.OSLF.NativeTypes.Decision.Scheduling.run (experiment (successor zero)) 500).closed

#guard delivered (binder (successor zero)) 1000 ==
  [(0, [0, 0], [term], [0], binder (accept zero)),
   (0, [0, 0], [term], [1], binder (accept zero)),
   (1, [0, 0], [term], [0], binder (accept zero)),
   (1, [0, 0], [term], [1], binder (accept zero))]
#guard (Mettapedia.OSLF.NativeTypes.Decision.Scheduling.run (experiment (binder (successor zero))) 1000).closed

#guard delivered (binder (successor (.bvar 0))) 1000 == []
#guard (Mettapedia.OSLF.NativeTypes.Decision.Scheduling.run (experiment (binder (successor (.bvar 0)))) 1000).closed

#guard (experiment (successor zero)).workBound = workBound (request (successor zero)) + 4

#guard ((resume 499 (Mettapedia.OSLF.NativeTypes.Decision.Scheduling.run (experiment (successor zero)) 1)).outputs.map
  (fun answer => answer.val.firing.job.declaration.declarationIndex)) == [0, 0, 1, 1]

theorem whole_actual_resume (source : Pattern) (first more : Nat) :
    Mettapedia.OSLF.NativeTypes.Decision.Scheduling.run (experiment source) (first + more) =
      resume more (Mettapedia.OSLF.NativeTypes.Decision.Scheduling.run (experiment source) first) :=
  Mettapedia.OSLF.NativeTypes.Decision.Scheduling.run_resume _ first more

theorem whole_archive_readout (source : Pattern) :
    (experiment source).flatten = (finished source).answers :=
  (stream_readouts (request source) whole_profile_equation_free).1

end Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier.LocalEquationFree.Suspended.Controls
