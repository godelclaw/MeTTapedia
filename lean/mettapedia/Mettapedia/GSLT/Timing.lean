import Mettapedia.GSLT.Timing.ClockModels
import Mettapedia.GSLT.Timing.WinnerRuleClocks
import Mettapedia.GSLT.Timing.TimedLeases
import Mettapedia.GSLT.Timing.TimedAwait
import Mettapedia.GSLT.Timing.TimeoutUnknown
import Mettapedia.GSLT.Timing.IdleWaitCost

/-!
# Time: clock models and what each mechanism needs from them

Real time is a global tick count that no process observes; each process reads its own clock, and
messages take time. A timing model is a set of such timings.

* `ClockModels`: the asynchronous model, partial synchrony in its two forms (an unknown bound; a
  known bound after an unknown stabilization time), and the synchronous model with bounded drift,
  with the separations between them; what a deadline passing means in each.
* `WinnerRuleClocks`: the winner rule is live in every model and safe only under a known bound on
  delays, skew and drift; it is unsafe under partial synchrony for every wait.
* `TimedLeases`: fenced leases are safe for every clock and schedule; without fencing, safety needs
  bounded drift and bounded delay; liveness needs eventual synchrony, with durations that grow when
  the bound is unknown, and fails in the asynchronous model for every duration policy.
* `TimedAwait`: a timed `await` is a choice whose second arm takes a deadline occurrence made by a
  clock region; the arms clash, exactly one takes the continuation, and time grants no rights.
* `TimeoutUnknown`: a timeout tells the caller nothing about the effect, even in the synchronous
  model; the durable runner marks it unknown, matches a late completion by identifier, and a retry
  is safe only through the key.
* `IdleWaitCost`: the cost obligations of an idle agent: no work on idle ticks, work bounded by the
  registrations a commit hits, memory bounded by the parked registrations, one event per armed
  deadline; polling, lazy withdrawal and ticks as messages are the controls.
-/
