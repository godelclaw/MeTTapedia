import Mettapedia.OSLF.MeTTaIL.CollectionPlanMachine
import Mettapedia.OSLF.MeTTaIL.ScopedCollectionMatchingControls

/-!
# Collection-plan publication controls

The current plan machine recomputes its publication by concatenating every
job's current answers.  It is resumable as a matcher, but that readout is not
an append-only search log: a slower earlier job can insert a result before an
already visible result of a later job.  `Complete.Explore` requires prefix
growth, so its collection integration must retain a chronological log rather
than expose this derived readout directly.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CollectionPlanMachine.Controls

open Syntax
open ScopedCollectionMatching.Controls

def request (kind : CollType) (schemas : List Pattern)
    (rest : Option String) (targets : List Pattern) : ScopedCollectionMachine.Request :=
  { rule := rule kind schemas rest, spec, ambient := 0, site := .left,
    path := [], depth := 0, index := 0, initial := [], schemas, rest, kind, targets }

/-- The first job takes longer to publish than the second. -/
def nonPrefixRequests : List (Nat × ScopedCollectionMachine.Request) :=
  [(0, request .hashSet twoVariables (some "R") [a]),
   (1, request .hashSet repeatedVariable none [a])]

/-- A new result of ordinal 0 is inserted before the previously visible
ordinal-1 result.  Therefore the derived plan publication is not suitable as
the publication field of a lawful generic resumable search. -/
theorem publication_not_prefix :
    ¬ publication (resume 6 (start nonPrefixRequests)) <+:
      publication (resume 7 (start nonPrefixRequests)) := by
  rintro ⟨tail, same⟩
  have heads := congrArg
    (fun firings : List Firing => firings.head?.map (·.ordinal)) same
  cbv at heads
  have impossible : (1 : Nat) = 0 := Option.some.inj heads
  omega

/-- Once no job has yet published, the empty readout is a prefix as expected;
the failure above is specifically late insertion across jobs. -/
example : publication (start nonPrefixRequests) <+:
    publication (resume 1 (start nonPrefixRequests)) := by
  cbv
  exact ⟨[], rfl⟩

#print axioms publication_not_prefix

end Mettapedia.OSLF.MeTTaIL.CollectionPlanMachine.Controls
