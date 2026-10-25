import Mettapedia.GSLT.LanguageDef.CollectionConsumers
import Mettapedia.OSLF.MeTTaIL.CollectionMatcherBackend
import Mettapedia.OSLF.MeTTaIL.CollectionRootSearch
import Mettapedia.OSLF.MeTTaIL.CollectionRootCoverage
import Mettapedia.OSLF.MeTTaIL.CollectionLoggedSearch
import Mettapedia.OSLF.MeTTaIL.CollectionLoggedSearchStable
import Mettapedia.OSLF.MeTTaIL.Complete.Explore

/-! End-to-end source controls for the two authored collection consumers. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls

open Mettapedia.OSLF.MeTTaIL Syntax CanonicalBags ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.ScopedCollectionMachine
open Mettapedia.OSLF.MeTTaIL.CollectionMatcherBackend
open CollectionConsumers

def completed? (request : Option Request) : Option (List Receipt) :=
  request.map fun query => publication (resume query 30 (start query))

def targets? (request : Option Request) : Option (List Pattern) := do
  let query ← request
  let receipts := publication (resume query 30 (start query))
  receipts.mapM fun receipt =>
    canon <$> reduct? query.rule query.spec query.ambient receipt.matching.assignment

def petriAB := petriRequest? 0 [token "A", token "B"]
def petriAAB := petriRequest? 0 [token "A", token "A", token "B"]
def petriMissing := petriRequest? 0 [token "A"]
def graphChain := reachabilityRequest? 0 [edge "A" "B", edge "B" "C"]
def graphLoop := reachabilityRequest? 0 [edge "A" "A"]
def graphMissing := reachabilityRequest? 0 [edge "A" "B", edge "A" "C"]

#guard (completed? petriAB).map List.length == some 1
#guard (completed? petriAAB).map List.length == some 2
#guard (completed? petriMissing).map List.length == some 0

#guard targets? petriAB == some [canon (.collection .hashBag [token "C", token "D"] none)]
#guard targets? petriAAB == some (List.replicate 2
  (canon (.collection .hashBag [token "C", token "D", token "A"] none)))

-- Four retention histories denote one set result; the histories remain
-- distinct receipts even though canonical targets coincide.
#guard (completed? graphChain).map List.length == some 4
#guard targets? graphChain == some (List.replicate 4
  (canon (.collection .hashSet [edge "A" "B", edge "B" "C", edge "A" "C"] none)))

-- Repeated selection is essential: one self-loop satisfies both premises.
#guard (completed? graphLoop).map List.length == some 2
#guard targets? graphLoop == some (List.replicate 2
  (canon (.collection .hashSet [edge "A" "A"] none)))

#guard (completed? graphMissing).map List.length == some 0

def petriSource : Pattern := .collection .hashBag [token "A", token "B"] none
def graphSource : Pattern := .collection .hashSet [edge "A" "B", edge "B" "C"] none

#guard (CollectionExecutionAdmission.requestsForSource
  petriPlan petriCertificate petriSource).map Prod.fst == [0, 1]
#guard (CollectionExecutionAdmission.requestsForSource
  reachabilityPlan reachabilityCertificate graphSource).map Prod.fst == [0]
#guard (CollectionExecutionAdmission.requestsForSource
  petriPlan petriCertificate (.apply "A" [])).isEmpty
#guard (CollectionExecutionAdmission.requestsForSource
  petriPlan petriCertificate graphSource).isEmpty

def petriRequests := CollectionExecutionAdmission.requestsForSource
  petriPlan petriCertificate petriSource

def graphRequests := CollectionExecutionAdmission.requestsForSource
  reachabilityPlan reachabilityCertificate graphSource

def completedPlanFirings (requests : List (Nat × Request)) :
    List CollectionPlanMachine.Firing :=
  CollectionPlanMachine.publication
    (CollectionPlanMachine.resume 30 (CollectionPlanMachine.start requests))

#guard (completedPlanFirings petriRequests).all
  (fun firing => !(adaptations firing).isEmpty)
#guard (completedPlanFirings graphRequests).all
  (fun firing => !(adaptations firing).isEmpty)

def duplicateOriginRequests : List (Nat × Request) :=
  match petriRequests.head? with
  | some (_, request) => [(3, request), (7, request)]
  | none => []

#guard (completedPlanFirings duplicateOriginRequests).map (·.ordinal) == [3, 7]

/-! The Petri consumer enters the generic scheduled continuation after
collection matching. This is the semantic join used by the emitted backend;
typing, premises and reduct construction are no longer collection-specific. -/

def petriFirstFiring : CollectionPlanMachine.Firing :=
  (completedPlanFirings petriRequests)[0]'(by cbv)

theorem petriFirstFiring_member :
    petriFirstFiring ∈ completedPlanFirings petriRequests :=
  List.getElem_mem _

theorem petriFirstFiring_ready : RootReady petriFirstFiring.request :=
  (source_publication_authority petriPlan petriCertificate petriSource 30
    (by simpa only [completedPlanFirings, petriRequests] using petriFirstFiring_member)).ready

theorem petriFirstFiring_valid : petriFirstFiring.Valid :=
  CollectionPlanMachine.publication_sound 30 petriRequests petriFirstFiring_member

def petriEnvironment := GeneralPlanEnvironment.environment petriPlan

theorem petriFirstAuthority : HandoffAuthority petriPlan petriCertificate
    petriSource petriFirstFiring := by
  apply source_publication_authority petriPlan petriCertificate petriSource 30
  simpa only [completedPlanFirings, petriRequests] using petriFirstFiring_member

theorem petriFirstFiring_declared :
    petriEnvironment.language.rewrites[petriFirstFiring.ordinal]? =
      some petriFirstFiring.request.rule := petriFirstAuthority.declared

theorem petriFirstFiring_specified :
    GeneralPremise.specification? petriEnvironment petriFirstFiring.ordinal =
      some petriFirstFiring.request.spec := petriFirstAuthority.specified

theorem petriFirstFiring_admitted :
    RuleBinding.admittedFor petriFirstFiring.request.rule
      petriFirstFiring.request.spec = true := petriFirstAuthority.admitted

theorem petriSource_typed :
    Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      petriEnvironment.language petriEnvironment.free [] (.base "Marking")
      petriSource := by
  apply Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted_sound
  cbv

theorem petriFirstSource_typed :
    Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      petriEnvironment.language petriEnvironment.free [] (.base "Marking")
      (CollectionMatcherCompatibility.ordinaryTarget petriFirstFiring.request
        petriFirstFiring.receipt.source) :=
  petriFirstAuthority.source_typed petriSource_typed

def petriHandoffGoal : StructuralDescent.Scheduled.Goal :=
  .root 1 [] (.base "Marking")
    (CollectionMatcherCompatibility.ordinaryTarget petriFirstFiring.request
      petriFirstFiring.receipt.source) petriFirstFiring.ordinal

def petriHandoff := continueAll petriEnvironment petriHandoffGoal 0 (.base "Marking")
  petriFirstFiring petriFirstFiring_ready petriFirstFiring_declared
  petriFirstFiring_specified petriFirstFiring_admitted petriFirstSource_typed
  (.done petriHandoffGoal) []

#guard !petriHandoff.tasks.isEmpty
#guard petriHandoff.answers.isEmpty
#guard petriHandoff.unresolved.isEmpty

def petriScheduled := startPublished petriPlan petriCertificate petriSource 30 0
  (.base "Marking") petriFirstFiring
  (by simpa only [completedPlanFirings, petriRequests] using petriFirstFiring_member)
  petriFirstSource_typed

#guard !petriScheduled.agenda.isEmpty
#guard petriScheduled.answers.isEmpty
#guard petriScheduled.unresolved.isEmpty

def petriScheduledRun := StructuralDescent.Scheduled.run petriEnvironment
  petriHandoffGoal 20 petriScheduled

#guard petriScheduledRun.agenda.isEmpty
#guard petriScheduledRun.answers.length = 1
#guard petriScheduledRun.unresolved.isEmpty

/-! Graph closure exercises the idempotent set branch through the same generic
continuation. Its four physical retention histories remain separate tasks. -/

def graphFirstFiring : CollectionPlanMachine.Firing :=
  (completedPlanFirings graphRequests)[0]'(by cbv)

theorem graphFirstFiring_member :
    graphFirstFiring ∈ completedPlanFirings graphRequests :=
  List.getElem_mem _

theorem graphFirstFiring_ready : RootReady graphFirstFiring.request :=
  (source_publication_authority reachabilityPlan reachabilityCertificate graphSource 30
    (by simpa only [completedPlanFirings, graphRequests] using graphFirstFiring_member)).ready

theorem graphFirstFiring_valid : graphFirstFiring.Valid :=
  CollectionPlanMachine.publication_sound 30 graphRequests graphFirstFiring_member

def graphEnvironment := GeneralPlanEnvironment.environment reachabilityPlan

theorem graphFirstAuthority : HandoffAuthority reachabilityPlan reachabilityCertificate
    graphSource graphFirstFiring := by
  apply source_publication_authority reachabilityPlan reachabilityCertificate graphSource 30
  simpa only [completedPlanFirings, graphRequests] using graphFirstFiring_member

theorem graphFirstFiring_declared :
    graphEnvironment.language.rewrites[graphFirstFiring.ordinal]? =
      some graphFirstFiring.request.rule := graphFirstAuthority.declared

theorem graphFirstFiring_specified :
    GeneralPremise.specification? graphEnvironment graphFirstFiring.ordinal =
      some graphFirstFiring.request.spec := graphFirstAuthority.specified

theorem graphFirstFiring_admitted :
    RuleBinding.admittedFor graphFirstFiring.request.rule
      graphFirstFiring.request.spec = true := graphFirstAuthority.admitted

theorem graphSource_typed :
    Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      graphEnvironment.language graphEnvironment.free [] (.base "Graph")
      graphSource := by
  apply Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted_sound
  cbv

theorem graphFirstSource_typed :
    Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      graphEnvironment.language graphEnvironment.free [] (.base "Graph")
      (CollectionMatcherCompatibility.ordinaryTarget graphFirstFiring.request
        graphFirstFiring.receipt.source) :=
  graphFirstAuthority.source_typed graphSource_typed

def graphHandoffGoal : StructuralDescent.Scheduled.Goal :=
  .root 1 [] (.base "Graph")
    (CollectionMatcherCompatibility.ordinaryTarget graphFirstFiring.request
      graphFirstFiring.receipt.source) graphFirstFiring.ordinal

def graphHandoff := continueAll graphEnvironment graphHandoffGoal 0 (.base "Graph")
  graphFirstFiring graphFirstFiring_ready graphFirstFiring_declared
  graphFirstFiring_specified graphFirstFiring_admitted graphFirstSource_typed
  (.done graphHandoffGoal) []

#guard !graphHandoff.tasks.isEmpty
#guard graphHandoff.tasks.length = 1
#guard graphHandoff.answers.isEmpty
#guard graphHandoff.unresolved.isEmpty

def graphScheduled := startPublished reachabilityPlan reachabilityCertificate graphSource 30 0
  (.base "Graph") graphFirstFiring
  (by simpa only [completedPlanFirings, graphRequests] using graphFirstFiring_member)
  graphFirstSource_typed

#guard !graphScheduled.agenda.isEmpty
#guard graphScheduled.answers.isEmpty
#guard graphScheduled.unresolved.isEmpty

def graphScheduledRun := StructuralDescent.Scheduled.run graphEnvironment
  graphHandoffGoal 20 graphScheduled

#guard graphScheduledRun.agenda.isEmpty
#guard graphScheduledRun.answers.length = 1
#guard graphScheduledRun.unresolved.isEmpty

/-! Both authored consumers now use the existing generic fair explorer through
the lawful append-only collection search. -/

def petriLoggedExplorer := Complete.Explore.explore
  (CollectionLoggedSearch.search petriPlan petriCertificate) petriSource 20

def graphLoggedExplorer := Complete.Explore.explore
  (CollectionLoggedSearch.search reachabilityPlan reachabilityCertificate) graphSource 20

#guard CanonicalBags.canon (.collection .hashBag [token "C", token "D"] none) ∈
  petriLoggedExplorer.nodes.map (·.state)
#guard CanonicalBags.canon (.collection .hashSet
    [edge "A" "B", edge "B" "C", edge "A" "C"] none) ∈
  graphLoggedExplorer.nodes.map (·.state)

/-! Chronological publication enters the existing shared continuation with
source typing transported once, independently of allocation history. -/

def petriLoggedRun := CollectionLoggedSearch.run petriPlan petriCertificate petriSource 30

def petriLoggedFirstFiring : CollectionPlanMachine.Firing :=
  (petriLoggedRun.state.log)[0]'(by cbv)

theorem petriLoggedFirst_member :
    petriLoggedFirstFiring ∈ petriLoggedRun.state.log := List.getElem_mem _

def petriLoggedGoal : StructuralDescent.Scheduled.Goal :=
  .root 1 [] (.base "Marking")
    (CollectionMatcherCompatibility.ordinaryTarget petriLoggedFirstFiring.request
      petriLoggedFirstFiring.receipt.source) petriLoggedFirstFiring.ordinal

def petriLoggedScheduled := startLoggedPublished petriPlan petriCertificate petriSource 30 0
  (.base "Marking") petriLoggedFirstFiring petriLoggedFirst_member petriSource_typed

def petriLoggedScheduledRun := StructuralDescent.Scheduled.run petriEnvironment
  petriLoggedGoal 20 petriLoggedScheduled

#guard !petriLoggedScheduled.agenda.isEmpty
#guard petriLoggedScheduledRun.agenda.isEmpty
#guard petriLoggedScheduledRun.answers.length = 1
#guard petriLoggedScheduledRun.unresolved.isEmpty

def graphLoggedRun := CollectionLoggedSearch.run reachabilityPlan reachabilityCertificate graphSource 30

def graphLoggedFirstFiring : CollectionPlanMachine.Firing := graphFirstFiring

theorem graphLoggedFirst_member :
    graphLoggedFirstFiring ∈ graphLoggedRun.state.log := by
  have finished : CollectionLoggedSearch.complete
      (CollectionLoggedSearch.resume (29 + 1) (CollectionLoggedSearch.begin graphRequests)) = true := by
    rw [CollectionLoggedSearch.complete_resume_begin_succ]
    cbv
  apply (CollectionLoggedSearch.completed_log_exact graphRequests 30 finished graphLoggedFirstFiring).mpr
  exact ⟨CollectionPlanMachine.publication_origin 30 graphRequests graphFirstFiring_member,
    graphFirstFiring_valid⟩

def graphLoggedGoal : StructuralDescent.Scheduled.Goal :=
  .root 1 [] (.base "Graph")
    (CollectionMatcherCompatibility.ordinaryTarget graphLoggedFirstFiring.request
      graphLoggedFirstFiring.receipt.source) graphLoggedFirstFiring.ordinal

def graphLoggedScheduled := startLoggedPublished reachabilityPlan reachabilityCertificate graphSource 30 0
  (.base "Graph") graphLoggedFirstFiring graphLoggedFirst_member graphSource_typed

def graphLoggedScheduledRun := StructuralDescent.Scheduled.run graphEnvironment
  graphLoggedGoal 20 graphLoggedScheduled

#guard !graphLoggedScheduled.agenda.isEmpty
#guard graphLoggedScheduledRun.agenda.isEmpty
#guard graphLoggedScheduledRun.answers.length = 1
#guard graphLoggedScheduledRun.unresolved.isEmpty

/-- A valid collection match cannot authorize an absent authored rule. -/
def wrongLoggedOrdinal : CollectionPlanMachine.Firing :=
  { petriLoggedFirstFiring with ordinal := 42 }

theorem wrongLoggedOrdinal_not_authorized :
    ¬ HandoffAuthority petriPlan petriCertificate petriSource wrongLoggedOrdinal := by
  intro authority
  have declared := authority.declared
  have absent : petriEnvironment.language.rewrites[42]? = none := by cbv
  change petriEnvironment.language.rewrites[42]? = some _ at declared
  rw [absent] at declared
  cases declared

/-! A completed collection match is provisional: a declared premise can still
reject it. Both provider snapshots are complete, including the empty one. -/

def guardedPetriPlan (permitted : Bool) : GeneralExecutionAdmission.Plan :=
  GeneralExecutionAdmission.compile
    { language := { petri with rewrites := petri.rewrites.map fun rule =>
        { rule with premises := [.relationQuery "permit" []] } }
      freeTypes := []
      provider :=
        { signatures := [{ relation := "permit", argumentTypes := [], modes := [] }]
          rows := if permitted then [{ relation := "permit", values := [] }] else [] } }
    permissions

def guardedPetriCertificate (permitted : Bool) :
    CollectionExecutionAdmission.Certificate (guardedPetriPlan permitted) :=
  ⟨by cases permitted <;> cbv⟩

theorem guardedPetriSource_typed (permitted : Bool) :
    Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      (GeneralPlanEnvironment.environment (guardedPetriPlan permitted)).language
      (GeneralPlanEnvironment.environment (guardedPetriPlan permitted)).free []
      (.base "Marking") petriSource := by
  apply Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted_sound
  cases permitted <;> cbv

def guardedPetriLoggedRun (permitted : Bool) :=
  CollectionLoggedSearch.run (guardedPetriPlan permitted)
    (guardedPetriCertificate permitted) petriSource 30

def guardedPetriLoggedFirst (permitted : Bool) : CollectionPlanMachine.Firing :=
  (guardedPetriLoggedRun permitted).state.log[0]'(by cases permitted <;> cbv)

theorem guardedPetriLoggedFirst_member (permitted : Bool) :
    guardedPetriLoggedFirst permitted ∈ (guardedPetriLoggedRun permitted).state.log :=
  List.getElem_mem _

def guardedPetriGoal (permitted : Bool) : StructuralDescent.Scheduled.Goal :=
  .root 1 [] (.base "Marking")
    (CollectionMatcherCompatibility.ordinaryTarget (guardedPetriLoggedFirst permitted).request
      (guardedPetriLoggedFirst permitted).receipt.source)
    (guardedPetriLoggedFirst permitted).ordinal

def guardedPetriScheduled (permitted : Bool) :=
  startLoggedPublished (guardedPetriPlan permitted) (guardedPetriCertificate permitted)
    petriSource 30 0 (.base "Marking") (guardedPetriLoggedFirst permitted)
    (guardedPetriLoggedFirst_member permitted) (guardedPetriSource_typed permitted)

def guardedPetriScheduledRun (permitted : Bool) :=
  StructuralDescent.Scheduled.run
    (GeneralPlanEnvironment.environment (guardedPetriPlan permitted))
    (guardedPetriGoal permitted) 20 (guardedPetriScheduled permitted)

#guard (guardedPetriLoggedRun true).state.log.length = 1
#guard (guardedPetriLoggedRun false).state.log.length = 1
#guard (guardedPetriScheduledRun true).answers.length = 1
#guard (guardedPetriScheduledRun false).answers.isEmpty
#guard (guardedPetriScheduledRun true).agenda.isEmpty
#guard (guardedPetriScheduledRun false).agenda.isEmpty
#guard (guardedPetriScheduledRun true).unresolved.isEmpty
#guard (guardedPetriScheduledRun false).unresolved.isEmpty

/-- Draining a depth-cut computation is not a negative semantic answer. -/
def petriDepthCutGoal : StructuralDescent.Scheduled.Goal :=
  .root 0 [] (.base "Marking") petriSource 0

def petriDepthCut := StructuralDescent.Scheduled.run petriEnvironment petriDepthCutGoal 1
  (StructuralDescent.Scheduled.start petriEnvironment petriDepthCutGoal)

#guard petriDepthCut.agenda.isEmpty
#guard petriDepthCut.answers.isEmpty
#guard petriDepthCut.unresolved == [.depthExhausted 0]
#guard !GeneralPremise.Scheduler.complete petriDepthCut

/-! Duplicate source occurrences remain separate. Alternative ordinary
proofs for each one must not multiply those occurrences a second time. -/

def petriDuplicateSource : Pattern := marking [token "A", token "A", token "B"]
def petriDuplicateLoggedRun :=
  CollectionLoggedSearch.run petriPlan petriCertificate petriDuplicateSource 30

theorem petriDuplicateSource_typed :
    Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      petriEnvironment.language petriEnvironment.free [] (.base "Marking")
      petriDuplicateSource := by
  apply Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted_sound
  cbv

def petriDuplicateFiring (index : Fin 2) : CollectionPlanMachine.Firing :=
  petriDuplicateLoggedRun.state.log[index.val]'(by
    have length : petriDuplicateLoggedRun.state.log.length = 2 := by cbv
    rw [length]
    exact index.isLt)

theorem petriDuplicateFiring_member (index : Fin 2) :
    petriDuplicateFiring index ∈ petriDuplicateLoggedRun.state.log := List.getElem_mem _

def petriDuplicateGoal (index : Fin 2) : StructuralDescent.Scheduled.Goal :=
  .root 1 [] (.base "Marking")
    (CollectionMatcherCompatibility.ordinaryTarget (petriDuplicateFiring index).request
      (petriDuplicateFiring index).receipt.source) (petriDuplicateFiring index).ordinal

def petriDuplicateScheduled (index : Fin 2) :=
  startLoggedPublished petriPlan petriCertificate petriDuplicateSource 30 0 (.base "Marking")
    (petriDuplicateFiring index) (petriDuplicateFiring_member index) petriDuplicateSource_typed

def petriDuplicateScheduledRun (index : Fin 2) :=
  StructuralDescent.Scheduled.run petriEnvironment (petriDuplicateGoal index) 20
    (petriDuplicateScheduled index)

#guard petriDuplicateLoggedRun.state.log.length = 2
#guard petriDuplicateLoggedRun.state.log.map (fun firing => (adaptations firing).length) == [2, 2]
#guard (petriDuplicateFiring 0).receipt.source.allocation.decisions !=
  (petriDuplicateFiring 1).receipt.source.allocation.decisions
#guard (petriDuplicateScheduledRun 0).answers.length = 1
#guard (petriDuplicateScheduledRun 1).answers.length = 1
#guard (petriDuplicateScheduledRun 0).unresolved.isEmpty
#guard (petriDuplicateScheduledRun 1).unresolved.isEmpty

/-! A premise can supply an RHS value absent from the initial capture. Raw
match receipts must reach the shared continuation before reduct construction. -/

def producedPetriPlan (permitted : Bool) : GeneralExecutionAdmission.Plan :=
  GeneralExecutionAdmission.compile
    { language := { petri with rewrites := petri.rewrites.map fun rule =>
        { rule with
          typeContext := rule.typeContext ++ [("made", .base "Place")]
          premises := [.relationQuery "produce" [.fvar "made"]]
          right := .collection .hashBag [.fvar "made"] (some "rest")
          bindings := none } }
      freeTypes := []
      provider :=
        { signatures := [{ relation := "produce", argumentTypes := [.base "Place"], modes := [.output] }]
          rows := if permitted then [{ relation := "produce", values := [token "C"] }] else [] } }
    permissions

def producedPetriCertificate (permitted : Bool) :
    CollectionExecutionAdmission.Certificate (producedPetriPlan permitted) :=
  ⟨by cases permitted <;> cbv⟩

def producedPetriRequests (permitted : Bool) :=
  CollectionExecutionAdmission.requestsForSource (producedPetriPlan permitted)
    (producedPetriCertificate permitted) petriSource

def producedPetriEntry (permitted : Bool) : Nat × Request :=
  (producedPetriRequests permitted)[0]'(by cases permitted <;> cbv)

def producedPetriReceipt (permitted : Bool) : Receipt :=
  (publication (resume (producedPetriEntry permitted).2 30
    (start (producedPetriEntry permitted).2)))[0]'(by cases permitted <;> cbv)

theorem producedPetriAuthority (permitted : Bool) :
    MatchAuthority (producedPetriPlan permitted) (producedPetriCertificate permitted)
      petriSource (producedPetriEntry permitted).1 (producedPetriEntry permitted).2
      (producedPetriReceipt permitted) :=
  match_authority_of_origin (producedPetriPlan permitted) (producedPetriCertificate permitted)
    petriSource (List.getElem_mem _) (ScopedCollectionMachine.publication_sound _ 30 (List.getElem_mem _))

theorem producedPetriSource_typed (permitted : Bool) :
    Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      (GeneralPlanEnvironment.environment (producedPetriPlan permitted)).language
      (GeneralPlanEnvironment.environment (producedPetriPlan permitted)).free []
      (.base "Marking") petriSource := by
  apply Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted_sound
  cases permitted <;> cbv

def producedPetriGoal (permitted : Bool) : StructuralDescent.Scheduled.Goal :=
  .root 1 [] (.base "Marking")
    (CollectionMatcherCompatibility.ordinaryTarget (producedPetriEntry permitted).2
      (producedPetriReceipt permitted)) (producedPetriEntry permitted).1

def producedPetriScheduled (permitted : Bool) :=
  startMatch (producedPetriPlan permitted) (producedPetriCertificate permitted)
    petriSource 0 (.base "Marking") (producedPetriEntry permitted).1
    (producedPetriEntry permitted).2 (producedPetriReceipt permitted)
    (producedPetriAuthority permitted) (producedPetriSource_typed permitted)

def producedPetriRun (permitted : Bool) :=
  StructuralDescent.Scheduled.run (GeneralPlanEnvironment.environment (producedPetriPlan permitted))
    (producedPetriGoal permitted) 30 (producedPetriScheduled permitted)

def producedPetriTargets (permitted : Bool) : List Pattern :=
  (producedPetriRun permitted).answers.map fun
    | .root _ _ _ _ target _ => target

#guard (ScopedCollectionMachine.firings (producedPetriEntry true).2
  (resume (producedPetriEntry true).2 30 (start (producedPetriEntry true).2))).isEmpty
#guard (producedPetriRun true).answers.length = 1
#guard producedPetriTargets true == [marking [token "C"]]
#guard (producedPetriRun false).answers.isEmpty
#guard (producedPetriRun true).agenda.isEmpty
#guard (producedPetriRun false).agenda.isEmpty
#guard (producedPetriRun true).unresolved.isEmpty
#guard (producedPetriRun false).unresolved.isEmpty

set_option maxHeartbeats 4000000

/-- The provisional-reduct search never publishes this source transition,
regardless of budget. Its completed empty log is stable. -/
theorem producedPetri_raw_log_empty (work : Nat) :
    (CollectionLoggedSearch.run (producedPetriPlan true) (producedPetriCertificate true)
      petriSource work).state.log = [] := by
  let search := CollectionLoggedSearch.search (producedPetriPlan true) (producedPetriCertificate true)
  have lawful := CollectionLoggedSearch.search_lawful (producedPetriPlan true) (producedPetriCertificate true)
  have empty : (search.run petriSource 30).state.log = [] := by cbv
  have complete : search.status (search.run petriSource 30) = .complete := by cbv
  change (search.run petriSource work).state.log = []
  by_cases before : work ≤ 30
  · have grown := lawful.publication_prefix petriSource work (30 - work)
    rw [Nat.add_sub_of_le before] at grown
    change (search.run petriSource work).state.log <+: (search.run petriSource 30).state.log at grown
    rw [empty] at grown
    simpa using grown
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt (Nat.lt_of_not_ge before))
    have stable := (CollectionLoggedSearch.search_stable
      (producedPetriPlan true) (producedPetriCertificate true))
      (search.run petriSource 30) extra complete
    rw [lawful.resume_run] at stable
    exact stable.1.trans empty

/-- Admission accepts the producer plan even though its provisional-reduct
profile stays empty. The producer controls above exercise the missing RHS. -/
theorem producedPetri_raw_admitted_empty :
    (producedPetriPlan true).complete = true ∧
    ∀ work, (CollectionLoggedSearch.run (producedPetriPlan true)
      (producedPetriCertificate true) petriSource work).state.log = [] := by
  exact ⟨by cbv, producedPetri_raw_log_empty⟩

/-- Equal-size nested allocations publish answers in successive stages.
A flattened cursor loses an earlier allocation's new receipt even though
the resulting answer-value multiset can coincide. -/
def outOfOrderRequest : Request :=
  let schemas : List Pattern := [.collection .hashBag [.fvar "X"] (some "Y")]
  let rule : RewriteRule :=
    { name := "nested-publication"
      typeContext := [("X", .base "Item"), ("Y", .base "Items"), ("R", .base "Items")]
      premises := [], left := .collection .hashBag schemas (some "R"), right := .fvar "X" }
  { rule, spec := ⟨[("X", []), ("Y", []), ("R", [])], []⟩,
    ambient := 0, site := .left, path := [], depth := 0, index := 0, initial := [],
    schemas, rest := some "R", kind := .hashBag,
    targets := arrange .hashBag
      [.collection .hashBag [token "A", token "A"] none,
       .collection .hashBag [token "A", token "B"] none] }

def outOfOrderState (work : Nat) : CollectionLoggedSearch.State :=
  CollectionLoggedSearch.resume work (CollectionLoggedSearch.begin [(0, outOfOrderRequest)])

#guard CollectionLoggedSearch.complete (outOfOrderState 100)
#guard ((outOfOrderState 100).log.map (·.receipt.target)).countP (· == token "A") == 3
#guard ((outOfOrderState 100).log.map (·.receipt.target)).countP (· == token "B") == 1
#guard ((outOfOrderState 100).log.map (fun firing => reprStr firing.receipt)).mergeSort (· ≤ ·) ==
  ((firings outOfOrderRequest (resume outOfOrderRequest 100 (start outOfOrderRequest))).map
    reprStr).mergeSort (· ≤ ·)

/-- Every Petri marking has a finite exact collection frontier. This is the
source matching/reduct layer; shared typing and premises remain downstream. -/
theorem petri_source_frontier_exact (items : List Pattern) :
    let requests := CollectionExecutionAdmission.requestsForSource petriPlan petriCertificate (marking items)
    ∃ work, CollectionLoggedSearch.complete
        (CollectionLoggedSearch.resume work (CollectionLoggedSearch.begin requests)) = true ∧
      ((CollectionLoggedSearch.resume work (CollectionLoggedSearch.begin requests)).log.map
        CollectionLoggedSearch.outcome).Perm
        (requests.flatMap fun entry => (CollectionLoggedSearch.Lane.begin entry).sourceTargets) :=
  CollectionLoggedSearch.eventually_source_exact _

/-- The graph frontier has the same exactness for arbitrary finite edge
collections, including repeated selection and overlapping set residuals. -/
theorem graph_source_frontier_exact (items : List Pattern) :
    let requests := CollectionExecutionAdmission.requestsForSource reachabilityPlan
      reachabilityCertificate (graph items)
    ∃ work, CollectionLoggedSearch.complete
        (CollectionLoggedSearch.resume work (CollectionLoggedSearch.begin requests)) = true ∧
      ((CollectionLoggedSearch.resume work (CollectionLoggedSearch.begin requests)).log.map
        CollectionLoggedSearch.outcome).Perm
        (requests.flatMap fun entry => (CollectionLoggedSearch.Lane.begin entry).sourceTargets) :=
  CollectionLoggedSearch.eventually_source_exact _

/-! A premise-produced result has an independent source derivation and a
proved eventual publication; an empty provider has no such source firing. -/
namespace ProducedCoverage

open Mettapedia.OSLF.MeTTaIL Syntax ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.CollectionConsumers
open Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls
open CollectionMatcherBackend

def environment := GeneralPlanEnvironment.environment (producedPetriPlan true)
def request := (producedPetriEntry true).2
def receipt := producedPetriReceipt true
def captured := receipt.matching.assignment
def completed : Assignment := ("made", ⟨[], 0, token "C"⟩) :: captured
def context : GeneralPremise.Context :=
  ⟨(producedPetriEntry true).1, request.rule, request.spec, [], 0, 0⟩
def history : List GeneralPremise.Event := [.query 0 0 0 [(0, [])]]

theorem captured_typed : GeneralPremise.TypedAssignment environment context captured := by
  apply GeneralPremise.checkTypedAssignment_sound
  cbv

theorem completed_typed : GeneralPremise.TypedAssignment environment context completed := by
  apply GeneralPremise.checkTypedAssignment_sound
  cbv

theorem premises : GeneralPremise.PremisesHold environment context request.rule.premises
    captured completed history := by
  have shape : request.rule.premises = [.relationQuery "produce" [.fvar "made"]] := by cbv
  rw [shape]
  change GeneralPremise.PremisesHold environment context [.relationQuery "produce" [.fvar "made"]]
    captured completed [.query 0 0 0 [(0, [])]]
  apply GeneralPremise.PremisesHold.cons (middle := completed)
  · apply GeneralPremise.PremiseHolds.query
    apply GeneralPremise.TracedQuery.row
      (row := ⟨"produce", [token "C"]⟩)
      (signature := ⟨"produce", [.base "Place"], [.output]⟩)
    · cbv
    · cbv
    · apply GeneralPremise.checkRow_sound
      cbv
    · exact .output (.capture (by cbv)) .nil
    · exact completed_typed
  · exact .nil

theorem reduced : reductWith? (ScopedReflectiveExecution.binderOperation
    environment.reflection request.rule) request.rule request.spec 0 completed =
    some (marking [token "C"]) := by
  cbv

theorem target_typed : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
    environment.language environment.free [] (.base "Marking") (marking [token "C"]) := by
  apply Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted_sound
  cbv

theorem source_firing : ∃ trace,
    GeneralPremise.RootFiring environment [] (.base "Marking")
      (CollectionMatcherCompatibility.ordinaryTarget request receipt)
      (producedPetriEntry true).1 trace captured completed history (marking [token "C"]) := by
  let authority := producedPetriAuthority true
  obtain ⟨answer, _, same⟩ := CollectionMatcherCompatibility.ordinaryAnswers_complete
    authority.ready.index authority.unordered authority.valid
  have matching := (ordinaryRootAnswer request receipt authority.ready answer).property
  change GeneralScopedMatchMachine.TracedMatches request.rule request.spec 0 .left [] 0 []
    request.rule.left (CollectionMatcherCompatibility.ordinaryTarget request receipt)
    answer.val.trace answer.val.assignment at matching
  rw [same] at matching
  exact ⟨answer.val.trace, .fire authority.declared authority.specified authority.admitted
    (authority.source_typed (producedPetriSource_typed true)) matching captured_typed
    premises reduced target_typed⟩

theorem eventual_C : ∃ fuel,
    marking [token "C"] ∈
      (StructuralDescent.Scheduled.run environment (producedPetriGoal true) fuel
        (producedPetriScheduled true)).answers.map (fun | .root _ _ _ _ target _ => target) := by
  obtain ⟨trace, held⟩ := source_firing
  let authority := producedPetriAuthority true
  obtain ⟨fuel, chosenTrace, proved, emitted⟩ := startRequest_covers environment 0 (.base "Marking")
    (producedPetriEntry true).1 request receipt authority.ready authority.unordered authority.valid
    authority.declared authority.specified authority.admitted
    (authority.source_typed (producedPetriSource_typed true)) trace completed history
    (marking [token "C"]) held (by cbv)
  refine ⟨fuel, ?_⟩
  have mapped := List.mem_map_of_mem (f := fun
    (result : StructuralDescent.Scheduled.Result environment (producedPetriGoal true)) =>
      match result with | .root _ _ _ _ target _ => target) emitted
  exact mapped

theorem empty_provider_no_firing
    (trace : List GeneralScopedMatchMachine.BagChoice) (initial final : Assignment)
    (events : List GeneralPremise.Event) (target : Pattern) :
    ¬ GeneralPremise.RootFiring (GeneralPlanEnvironment.environment (producedPetriPlan false))
      [] (.base "Marking")
      (CollectionMatcherCompatibility.ordinaryTarget (producedPetriEntry false).2
        (producedPetriReceipt false))
      (producedPetriEntry false).1 trace initial final events target := by
  intro held
  let authority := producedPetriAuthority false
  cases held with
  | @fire _ _ _ _ _ rule spec _ _ _ _ declared specified _ _ _ _ premises _ _ =>
      have ruleEq := Option.some.inj (declared.symm.trans authority.declared)
      subst rule
      have shape : (producedPetriEntry false).2.rule.premises =
          [.relationQuery "produce" [.fvar "made"]] := by cbv
      rw [shape] at premises
      cases premises with
      | cons head tail =>
        cases head with
        | query query =>
          cases query with
          | row selected _ _ _ _ =>
            have empty : (GeneralPlanEnvironment.environment (producedPetriPlan false)).provider.rows = [] := by cbv
            rw [empty] at selected
            simp at selected
          | dynamicRow registered _ _ _ _ _ _ _ =>
            have empty : (GeneralPlanEnvironment.environment (producedPetriPlan false)).provider.dynamicRelations = [] := by cbv
            rw [empty] at registered
            cases registered


end ProducedCoverage

namespace RetainedControls

def producedMatch (permitted : Bool) : Retained.Match :=
  ⟨(producedPetriEntry permitted).1, (producedPetriEntry permitted).2,
    producedPetriReceipt permitted⟩

def producedFrame (permitted : Bool) :=
  Retained.Frame.initial (producedMatch permitted) (producedPetriAuthority permitted)
    (producedPetriSource_typed permitted) 0

def producedBegin (permitted : Bool) := Retained.State.begin [producedFrame permitted]
def producedRun (permitted : Bool) := Retained.State.run 30 (producedBegin permitted)
def producedTargets (permitted : Bool) : List Pattern :=
  (producedRun permitted).log.map (fun publication => publication.outcome.target)

#guard producedTargets true == [marking [token "C"]]
#guard (producedRun false).log.isEmpty
#guard (producedRun true).complete
#guard (producedRun false).complete

def duplicateMatch (index : Fin 2) : Retained.Match :=
  let firing := petriDuplicateFiring index
  ⟨firing.ordinal, firing.request, firing.receipt.source⟩

theorem duplicateAuthority (index : Fin 2) :
    MatchAuthority petriPlan petriCertificate petriDuplicateSource
      (duplicateMatch index).ordinal (duplicateMatch index).request (duplicateMatch index).receipt :=
  let authority := logged_publication_authority petriPlan petriCertificate petriDuplicateSource 30
    (petriDuplicateFiring_member index)
  match_authority_of_origin petriPlan petriCertificate petriDuplicateSource authority.origin authority.valid.1

def duplicateFrame (index : Fin 2) :=
  Retained.Frame.initial (duplicateMatch index) (duplicateAuthority index)
    petriDuplicateSource_typed 0

def duplicateBegin := Retained.State.begin [duplicateFrame 0, duplicateFrame 1]
def duplicateRun := Retained.State.run 30 duplicateBegin

#guard duplicateRun.log.length = 2
#guard duplicateRun.complete
#guard (duplicateRun.log[0]?.map (fun result => result.outcome.target)) ==
  (duplicateRun.log[1]?.map (fun result => result.outcome.target))
#guard (duplicateRun.log[0]?.map (fun result => result.matched.receipt.allocation.decisions)) !=
  (duplicateRun.log[1]?.map (fun result => result.matched.receipt.allocation.decisions))

/-- The independent producer source derivation reaches the one retained
publication log even though the old provisional-reduct search is always empty. -/
theorem producer_eventually_C :
    ∃ work, marking [token "C"] ∈
      (Retained.State.run work (producedBegin true)).log.map (fun result => result.outcome.target) := by
  obtain ⟨trace, held⟩ := ProducedCoverage.source_firing
  obtain ⟨work, chosenTrace, published⟩ := Retained.State.source_coverage
    [producedFrame true] (producedMatch true) (producedPetriAuthority true)
    (producedPetriSource_typed true) 0 List.mem_cons_self trace ProducedCoverage.completed
    ProducedCoverage.history (marking [token "C"]) held (by cbv)
  exact ⟨work, List.mem_map_of_mem published⟩

end RetainedControls

namespace RootControls

def petriProfile : CollectionRootSearch.Profile petriPlan :=
  ⟨petriCertificate, by cbv, by cbv, by cbv, by cbv, by rfl⟩

def graphProfile : CollectionRootSearch.Profile reachabilityPlan :=
  ⟨reachabilityCertificate, by cbv, by cbv, by cbv, by cbv, by rfl⟩

def petriCoverage : CollectionRootSearch.CoverageProfile petriPlan :=
  ⟨petriProfile, fun declaration member => CollectionRootSearch.canonicalRuleCheck_sound
    (List.all_eq_true.mp (show petriPlan.rules.all CollectionRootSearch.canonicalRuleCheck = true by cbv)
      declaration member), by cbv, by cbv⟩

def graphCoverage : CollectionRootSearch.CoverageProfile reachabilityPlan :=
  ⟨graphProfile, fun declaration member => CollectionRootSearch.canonicalRuleCheck_sound
    (List.all_eq_true.mp (show reachabilityPlan.rules.all CollectionRootSearch.canonicalRuleCheck = true by cbv)
      declaration member), by cbv, by cbv⟩

#guard (CollectionRootSearch.coverageProfile? petriPlan).isSome
#guard (CollectionRootSearch.coverageProfile? reachabilityPlan).isSome

example : CollectionRootSearch.checkSpineOrder [.bvar 0, .bvar 2, .bvar 5] = true := by decide
example : CollectionRootSearch.checkSpineOrder [.bvar 2, .bvar 0] = false := by decide
example : CollectionRootSearch.checkSpineOrder [.bvar 1, .bvar 1] = true := by decide

-- Consuming two distinct positions cannot match a canonical singleton set.
-- It can match its duplicate presentation, which has the same set meaning.
#guard (graphLoop.map fun request => (matchAt request.rule request.spec 0 .left [] 0 [] request.rule.left
  (.collection .hashSet [edge "A" "A"] none)).isEmpty) == some true
#guard (graphLoop.map fun request => (matchAt request.rule request.spec 0 .left [] 0 [] request.rule.left
  (.collection .hashSet [edge "A" "A", edge "A" "A"] none)).isEmpty) == some false

private def firstPetriDeclaration : GeneralExecutionAdmission.RulePlan :=
  petriPlan.rules[0]'(by cbv)

example : CollectionRootSearch.canonicalRuleCheck
    { firstPetriDeclaration with authored := { firstPetriDeclaration.authored with
      left := .collection .hashSet [.collection .hashSet [] none] none } } = false := by cbv

example : CollectionRootSearch.canonicalRuleCheck
    { firstPetriDeclaration with authored := { firstPetriDeclaration.authored with
      premises := [.relationQuery "requires-service" []] } } = false := by cbv

theorem petri_presented_iff_published (source target : Pattern) :
    (Complete.Presented.gslt petriPlan [] (.base "Marking")).Step source (canon target) ↔
      ∃ work receipt, receipt ∈ CollectionRootSearch.publication (.base "Marking")
        ((CollectionRootSearch.search (profile := petriCoverage.profile) (.base "Marking")).run
          (canon source) work) ∧ canon receipt.target = canon target :=
  CollectionRootSearch.presented_iff_published petriCoverage.profile (.base "Marking")
    petriCoverage.rules petriCoverage.noLaws petriCoverage.noExtrusions source target

theorem graph_presented_iff_published (source target : Pattern) :
    (Complete.Presented.gslt reachabilityPlan [] (.base "Graph")).Step source (canon target) ↔
      ∃ work receipt, receipt ∈ CollectionRootSearch.publication (.base "Graph")
        ((CollectionRootSearch.search (profile := graphCoverage.profile) (.base "Graph")).run
          (canon source) work) ∧ canon receipt.target = canon target :=
  CollectionRootSearch.presented_iff_published graphCoverage.profile (.base "Graph")
    graphCoverage.rules graphCoverage.noLaws graphCoverage.noExtrusions source target

def producedProfile (permitted : Bool) : CollectionRootSearch.Profile (producedPetriPlan permitted) :=
  ⟨producedPetriCertificate permitted, by cases permitted <;> cbv,
    by cases permitted <;> cbv, by cases permitted <;> cbv,
    by cases permitted <;> cbv, by rfl⟩

def producedRun (permitted : Bool) (work : Nat) :=
  (CollectionRootSearch.search (profile := producedProfile permitted) (.base "Marking")).run petriSource work

theorem produced_source_reaches_C :
    ∃ work receipt,
      receipt ∈ CollectionRootSearch.publication (.base "Marking") (producedRun true work) ∧
      receipt.target = marking [token "C"] := by
  obtain ⟨trace, held⟩ := ProducedCoverage.source_firing
  let receipt : CollectionRootSearch.Receipt :=
    ⟨RetainedControls.producedMatch true, ProducedCoverage.completed,
      ProducedCoverage.history, marking [token "C"]⟩
  obtain ⟨work, published⟩ := CollectionRootSearch.source_coverage (.base "Marking")
    (receipt := receipt) (profile := producedProfile true)
    ⟨producedPetriAuthority true, trace, held⟩
  exact ⟨work, receipt, published, rfl⟩

end RootControls

end Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls
