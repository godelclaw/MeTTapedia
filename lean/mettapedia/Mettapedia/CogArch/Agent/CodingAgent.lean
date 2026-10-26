import Mettapedia.CogArch.Agent.CodingAgent.TurnLoop
import Mettapedia.CogArch.Agent.CodingAgent.PatchApply
import Mettapedia.CogArch.Agent.CodingAgent.Compaction
import Mettapedia.CogArch.Agent.CodingAgent.Truncation
import Mettapedia.CogArch.Agent.CodingAgent.CachePrefix
import Mettapedia.CogArch.Agent.CodingAgent.Retry
import Mettapedia.CogArch.Agent.CodingAgent.ProjectGuidance

/-!
# Tool-using coding agents

Mechanisms that independently built coding agents share, each stated for any
implementation, with the properties that give it a reason to exist:

* `TurnLoop`: a turn ends exactly when the reply calls no tool and no input is
  pending, and steering input is never lost under either delivery policy;
* `PatchApply`: when verification predicts application, when a multi-file
  patch is all or nothing, and which matching rules never misplace an edit;
* `Compaction`: which recovery from an oversized request is live, and what a
  rejection must record for compaction to happen at all;
* `Truncation`: what a middle cut keeps and loses, and why an output is cut
  once;
* `CachePrefix`: what a prefix cache serves, and how request layout decides
  the cost of a step;
* `Retry`: holding rejections, never replaying uncertain effects, and
  surviving outages without an attempt limit;
* `ProjectGuidance`: which project instruction files apply, in what order,
  and how guidance survives resumption and compaction.
-/
