import Mettapedia.UniversalAI.SelfModification.Basic
import Mettapedia.UniversalAI.SelfModification.ValueFunctions
import Mettapedia.UniversalAI.SelfModification.IgnorantAgents
import Mettapedia.UniversalAI.SelfModification.HedonisticAgents
import Mettapedia.UniversalAI.SelfModification.RealisticAgents
import Mettapedia.UniversalAI.SelfModification.OptimalPolicies
import Mettapedia.UniversalAI.SelfModification.CompactnessBridge

/-!
# Finite evaluation and named-policy modification

The common Bellman evaluator specializes to fixed-policy and name-following
predictions. Realistic continuation optimality is a finite-horizon theorem on
supported executions, with branch expressivity and positive discount explicit.
The hedonistic specialization fixes its supplied evaluation utility; its
monotonicity theorem does not model dynamically changing utilities.

The compactness bridge optimizes world actions at a fixed continuation name.
It does not establish an optimal name among all interpreter entries. Infinite
returns, globally optimal named policies, and the infinite-horizon version of
Everitt et al. (2016), Theorem 16, require further results.
-/
