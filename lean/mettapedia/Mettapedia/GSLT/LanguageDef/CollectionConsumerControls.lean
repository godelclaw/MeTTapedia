import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceSearch
import Mettapedia.OSLF.MeTTaIL.CollectionOccurrencePublication
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

/-! Prefix observations retain their complete committed packets.
These readouts make no enumeration-completion assertion. -/

namespace Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.Observation

open _root_.Mettapedia.OSLF.MeTTaIL
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open CanonicalBags CollectionOccurrenceBatch CollectionCommittedObservation GeneralPremise
open Mettapedia.GSLT.LanguageDef.CollectionConsumers

namespace PetriControls

open Mettapedia.GSLT.LanguageDef.CollectionConsumers

def guardedLanguage : LanguageDef :=
  let first := petri.rewrites[0]' (by cbv)
  { petri with «rewrites» :=
    [{ first with «name» := "route-left", premises := [.relationQuery "permit" []] },
     { first with «name» := "route-right", premises := [.relationQuery "permit" []] }] }

def plan (copies : Nat) : GeneralExecutionAdmission.Plan :=
  GeneralExecutionAdmission.compile
    ⟨guardedLanguage, [],
      { signatures := [⟨"permit", [], []⟩],
        rows := List.replicate copies ⟨"permit", []⟩ }⟩
    { sites := .rootOnly, includeDerivedEquations := false }

def source : Pattern := marking [token "A", token "A", token "B"]
def expected : TypeExpr := .base "Marking"

def finished (copies : Nat) : CollectionOccurrenceMachine.State (plan copies) [] expected source :=
  CollectionOccurrenceMachine.run 0 120 (CollectionOccurrenceMachine.begin (plan copies) [] expected source)

def check : IO Unit := do
  let first := finished 1
  let duplicate := finished 2
  let none := finished 0
  let left := retained (plan 1) [] expected first.batch.log
  let replayed := retained (plan 2) [] expected duplicate.batch.log
  IO.println s!"raw {left.length} / {replayed.length}; keys {(allocationKeys (plan 1) [] expected first.batch.log).card} / {(allocationKeys (plan 2) [] expected duplicate.batch.log).card}; successorStates {(successorStates (plan 2) [] expected duplicate.batch.log).card}; bag {(allocationBag (plan 2) [] expected duplicate.batch.log).card}"
  unless left.length == 4 && replayed.length == 8 do
    throw (IO.userError "actual committed packet count disagrees")
  unless (allocationKeys (plan 2) [] expected duplicate.batch.log).card == 4 do
    throw (IO.userError "validation duplicates changed declared occurrence count")
  unless (successorStates (plan 2) [] expected duplicate.batch.log).card == 1 &&
      (allocationBag (plan 2) [] expected duplicate.batch.log).card == 4 do
    throw (IO.userError "fact and derivation aggregation were conflated")
  unless (retained (plan 0) [] expected none.batch.log).isEmpty do
    throw (IO.userError "missing premise produced a committed derivation")
  unless (allocationKeys (plan 1) [] expected first.batch.log) ==
      allocationKeys (plan 2) [] expected duplicate.batch.log do
    throw (IO.userError "duplicated validation did not preserve declared keys")
  let routes := ((retained (plan 2) [] expected duplicate.batch.log).map (fun entry => (allocationKey entry).authoredRule)).eraseDups
  unless routes.length == 2 do
    throw (IO.userError "independent authored routes were identified")
  let allocations := ((retained (plan 2) [] expected duplicate.batch.log).map (fun entry => (allocationKey entry).allocation.trace)).eraseDups
  unless allocations.length == 2 do
    throw (IO.userError "equal physical token occurrences were identified")
  IO.println "CommittedObservationControls: validation replay, route identity, token identity and absent premise passed"

#eval check

end PetriControls

namespace GraphControls

open Mettapedia.GSLT.LanguageDef.CollectionConsumers

def source : Pattern := graph [edge "A" "B", edge "B" "C"]
def finished := CollectionOccurrenceMachine.run 0 160
  (CollectionOccurrenceMachine.begin reachabilityPlan [] (.base "Graph") source)

def diamond : Pattern :=
  graph [edge "A" "B", edge "B" "C", edge "A" "C", edge "C" "C"]
def finishedDiamond := CollectionOccurrenceMachine.run 0 800
  (CollectionOccurrenceMachine.begin reachabilityPlan [] (.base "Graph") diamond)

def producedEdge? (key : AllocationKey) : Option Pattern := do
  let first ← ScopedRuleMatching.lookup key.completed "x"
  let last ← ScopedRuleMatching.lookup key.completed "z"
  some (.apply "Edge" [first.body, last.body])

def inferredBag (plan : GeneralExecutionAdmission.Plan) (packets : List Publication) : Multiset Pattern :=
  (allocationKeys plan [] (.base "Graph") packets).val.filterMap producedEdge?

def inferredFacts (plan : GeneralExecutionAdmission.Plan) (packets : List Publication) : Finset Pattern :=
  (inferredBag plan packets).toFinset

/-- The root graph observation retains the licensed typed path, but no
source focus or residual/context payload. This projection is scoped to the
root graph policy; allocation observations retain the complete site. -/
structure LogicalSiteShape where
  address : List Nat
  bound : List TypeExpr
  type : TypeExpr
  typingFrames : List GeneralTypedSites.TypingFrame
  deriving DecidableEq

def logicalSiteShape (site : GeneralTypedSites.SiteData) : LogicalSiteShape :=
  ⟨site.address, site.focusBound, site.focusType, site.typingFrames⟩

theorem logicalSiteShape_ignores_payload (site : GeneralTypedSites.SiteData)
    (focus : Pattern) (context : DerivedContexts.OneHoleContext) :
    logicalSiteShape {site with focus := focus, context := context} = logicalSiteShape site := rfl

/-- Root transitivity is identified by its non-rest input binding tuple.
Its rule has no child-step premises; the retained child-history coordinate
keeps explicit child evidence if a separate profile later authorizes it.
Allocation-sensitive publication remains available beside this readout. -/
structure LogicalKey (Choice : Type := GeneralScopedMatchMachine.BagChoice) where
  selectedRule : Nat
  authoredRule : Nat
  siteShape : LogicalSiteShape
  first : Option RuleBinding.ContextualValue
  intermediate : Option RuleBinding.ContextualValue
  last : Option RuleBinding.ContextualValue
  childHistory : List (GeneralPremise.Event Choice)
  deriving DecidableEq

def logicalKey {Choice : Type} (committed : Committed Choice) : LogicalKey Choice :=
  let packet := committed.1
  let receipt := committed.2
  ⟨packet.job.origin.ordinal, packet.job.origin.declaration.declarationIndex, logicalSiteShape packet.job.origin.site,
    (ScopedRuleMatching.lookup receipt.completed "x").map canonValue,
    (ScopedRuleMatching.lookup receipt.completed "y").map canonValue,
    (ScopedRuleMatching.lookup receipt.completed "z").map canonValue,
    validationHistoryReadout receipt.premiseHistory .factValidation⟩

def logicalEdge? {Choice : Type} (key : LogicalKey Choice) : Option Pattern := do
  let first ← key.first
  let last ← key.last
  some (.apply "Edge" [first.body, last.body])

def logicalKeys (plan : GeneralExecutionAdmission.Plan) (packets : List Publication) : Finset LogicalKey :=
  declaredKeys logicalKey plan [] (.base "Graph") packets

def logicalBag (plan : GeneralExecutionAdmission.Plan) (packets : List Publication) : Multiset Pattern :=
  (logicalKeys plan packets).val.filterMap logicalEdge?

def logicalFacts (plan : GeneralExecutionAdmission.Plan) (packets : List Publication) : Finset Pattern :=
  (logicalBag plan packets).toFinset

theorem logicalKey_ignores_allocation {Choice : Type} (packet : Publication Choice) (receipt : GeneralRuleJobs.Receipt Choice)
    (allocation : RecursiveCollectionMachine.Answer) (variant : CollectionSelection.SiteVariant)
    (trace : List Choice) :
    logicalKey (⟨{packet.job with variant := variant}, allocation, packet.prepared, packet.outcome⟩,
        {receipt with matcherTrace := trace}) =
      logicalKey (packet, receipt) := rfl

theorem logicalKey_ignores_source_payload {Choice : Type} (packet : Publication Choice) (receipt : GeneralRuleJobs.Receipt Choice)
    (focus : Pattern) (context : DerivedContexts.OneHoleContext) :
    let site := {packet.job.origin.site with focus := focus, context := context}
    let origin := {packet.job.origin with site := site}
    logicalKey (⟨⟨origin, packet.job.variant⟩, packet.answer, packet.prepared, packet.outcome⟩, receipt) =
      logicalKey (packet, receipt) := rfl

theorem logicalKey_canonical_source_presentation {Choice : Type} (packet : Publication Choice) (receipt : GeneralRuleJobs.Receipt Choice) :
    let site := {packet.job.origin.site with focus := canon packet.job.origin.site.focus}
    let origin := {packet.job.origin with site := site}
    logicalKey (⟨⟨origin, packet.job.variant⟩, packet.answer, packet.prepared, packet.outcome⟩, receipt) =
      logicalKey (packet, receipt) := rfl

theorem logicalKey_ignores_query_validation {Choice : Type} (packet : Publication Choice) (receipt : GeneralRuleJobs.Receipt Choice)
    (p q row : Nat) (origins : List (Nat × List Choice)) :
    logicalKey (packet, {receipt with premiseHistory := [.query p q row origins]}) =
      logicalKey (packet, {receipt with premiseHistory := []}) := rfl

theorem logicalKey_erases_query_in_history {Choice : Type} (packet : Publication Choice)
    (receipt : GeneralRuleJobs.Receipt Choice) (before after : List (GeneralPremise.Event Choice))
    (premise quantifier row : Nat) (origins : List (Nat × List Choice)) :
    logicalKey (packet, {receipt with premiseHistory := before ++ .query premise quantifier row origins :: after}) =
      logicalKey (packet, {receipt with premiseHistory := before ++ after}) := by
  simp only [logicalKey, query_administration_erases]

theorem logicalKey_erases_freshness_in_history {Choice : Type} (packet : Publication Choice)
    (receipt : GeneralRuleJobs.Receipt Choice) (before after : List (GeneralPremise.Event Choice))
    (premise quantifier : Nat) (name : String) (subject : Pattern) :
    logicalKey (packet, {receipt with premiseHistory := before ++ .freshness premise quantifier name subject :: after}) =
      logicalKey (packet, {receipt with premiseHistory := before ++ after}) := by
  simp only [logicalKey, freshness_administration_erases]

theorem logicalBag_ordered_presentation (plan : GeneralExecutionAdmission.Plan) (packets : List Publication) :
    ((orderedCommittedKeys logicalKey (retained plan [] (.base "Graph") packets)).filterMap logicalEdge? :
      Multiset Pattern) = logicalBag plan packets :=
  orderedCommittedKeys_partial_bag logicalKey logicalEdge? _

theorem logicalFacts_ordered_presentation (plan : GeneralExecutionAdmission.Plan) (packets : List Publication) :
    ((orderedCommittedKeys logicalKey (retained plan [] (.base "Graph") packets)).filterMap logicalEdge?).toFinset =
      logicalFacts plan packets :=
  orderedCommittedKeys_partial_facts logicalKey logicalEdge? _

theorem logicalKey_nonrest_ext {Choice : Type} {first second : Committed Choice}
    (rule : first.1.job.origin.ordinal = second.1.job.origin.ordinal)
    (authored : first.1.job.origin.declaration.declarationIndex =
      second.1.job.origin.declaration.declarationIndex)
    (site : logicalSiteShape first.1.job.origin.site = logicalSiteShape second.1.job.origin.site)
    (x : (ScopedRuleMatching.lookup first.2.completed "x").map canonValue =
      (ScopedRuleMatching.lookup second.2.completed "x").map canonValue)
    (y : (ScopedRuleMatching.lookup first.2.completed "y").map canonValue =
      (ScopedRuleMatching.lookup second.2.completed "y").map canonValue)
    (z : (ScopedRuleMatching.lookup first.2.completed "z").map canonValue =
      (ScopedRuleMatching.lookup second.2.completed "z").map canonValue)
    (children : validationHistoryReadout first.2.premiseHistory .factValidation =
      validationHistoryReadout second.2.premiseHistory .factValidation) :
    logicalKey first = logicalKey second := by
  simp only [logicalKey, LogicalKey.mk.injEq]
  exact ⟨rule, authored, site, x, y, z, children⟩

theorem intermediate_distinguishes_route {Choice : Type} {first second : Committed Choice}
    (different : (ScopedRuleMatching.lookup first.2.completed "y").map canonValue ≠
      (ScopedRuleMatching.lookup second.2.completed "y").map canonValue) :
    logicalKey first ≠ logicalKey second := by
  intro same
  exact different (congrArg LogicalKey.intermediate same)

theorem logical_replay_invariant (plan : GeneralExecutionAdmission.Plan)
    (earlier replay : List Publication) (already : logicalKeys plan replay ⊆ logicalKeys plan earlier) :
    logicalBag plan (earlier ++ replay) = logicalBag plan earlier ∧
      logicalFacts plan (earlier ++ replay) = logicalFacts plan earlier := by
  have same : logicalKeys plan (earlier ++ replay) = logicalKeys plan earlier := by
    unfold logicalKeys at already ⊢
    rw [declaredKeys_append, Finset.union_eq_left.mpr already]
  simp only [logicalBag, logicalFacts, same, and_self]

theorem logical_balanced_observations {plan : GeneralExecutionAdmission.Plan} {source : Pattern}
    {state : State plan [] (.base "Graph") source} (balanced : state.Balanced) :
    logicalBag plan state.log = logicalBag plan (state.frames.flatMap Frame.publication) ∧
      logicalFacts plan state.log = logicalFacts plan (state.frames.flatMap Frame.publication) := by
  have same : logicalKeys plan state.log = logicalKeys plan (state.frames.flatMap Frame.publication) :=
    declaredKeys_perm logicalKey plan [] (.base "Graph") balanced
  simp only [logicalBag, logicalFacts, same, and_self]

def twoRouteLanguage : LanguageDef :=
  { reachability with «terms» := reachability.terms ++
    [{ label := "D", category := "Node", params := [], syntaxPattern := [] }] }

def twoRoutePlan : GeneralExecutionAdmission.Plan :=
  GeneralExecutionAdmission.compile (snapshot twoRouteLanguage) permissions

def twoRouteSource : Pattern := graph
  [edge "A" "B", edge "B" "D", edge "A" "C", edge "C" "D"]

def twoRouteFinished := CollectionOccurrenceMachine.run 0 800
  (CollectionOccurrenceMachine.begin twoRoutePlan [] (.base "Graph") twoRouteSource)

def irrelevantExtensionSource : Pattern := graph
  [edge "A" "B", edge "B" "D", edge "A" "C", edge "C" "D", edge "D" "D"]

def irrelevantExtensionFinished := CollectionOccurrenceMachine.run 0 1600
  (CollectionOccurrenceMachine.begin twoRoutePlan [] (.base "Graph") irrelevantExtensionSource)

def reorderedDuplicateSource : Pattern := graph
  [edge "C" "D", edge "A" "B", edge "A" "C", edge "B" "D", edge "A" "B"]

def reorderedDuplicateFinished := CollectionOccurrenceMachine.run 0 800
  (CollectionOccurrenceMachine.begin twoRoutePlan [] (.base "Graph") reorderedDuplicateSource)

def canonicalSourceFinished := CollectionOccurrenceMachine.run 0 800
  (CollectionOccurrenceMachine.begin twoRoutePlan [] (.base "Graph") (canon twoRouteSource))

def aToDKeys (plan : GeneralExecutionAdmission.Plan) (packets : List Publication) : Finset LogicalKey :=
  (logicalKeys plan packets).filter fun key => logicalEdge? key = some (edge "A" "D")

/-- A separating readout that deliberately retains the forbidden source
payload, used to check that the extension control detects that regression. -/
def sourceSensitiveAToDKeys (plan : GeneralExecutionAdmission.Plan) (packets : List Publication) :
    Finset (GeneralTypedSites.SiteData × LogicalKey) :=
  ((retained plan [] (.base "Graph") packets).filter
    (fun committed => logicalEdge? (logicalKey committed) == some (edge "A" "D"))).map
      (fun committed => (committed.1.job.origin.site, logicalKey committed)) |>.toFinset

def guardedTwoRouteLanguage : LanguageDef :=
  {twoRouteLanguage with «rewrites» := twoRouteLanguage.rewrites.map fun rule =>
    {rule with premises := [.relationQuery "permit" []]}}

def guardedTwoRoutePlan (copies : Nat) : GeneralExecutionAdmission.Plan :=
  GeneralExecutionAdmission.compile
    ⟨guardedTwoRouteLanguage, [],
      {signatures := [⟨"permit", [], []⟩],
        rows := List.replicate copies ⟨"permit", []⟩}⟩ permissions

def guardedTwoRouteFinished (copies : Nat) := CollectionOccurrenceMachine.run 0 800
  (CollectionOccurrenceMachine.begin (guardedTwoRoutePlan copies) [] (.base "Graph") twoRouteSource)

def actualRule : RewriteRule := (reachabilityPlan.rules[0]'(by cbv)).rule
def actualSpec : RuleBindingSpec := (reachabilityPlan.rules[0]'(by cbv)).binding.spec

def thirdEdge : Pattern := .apply "Edge" [.fvar "x", .fvar "z"]
def firstEdge : Pattern := .apply "Edge" [.fvar "x", .fvar "y"]
def secondEdge : Pattern := .apply "Edge" [.fvar "y", .fvar "z"]

theorem actual_left : actualRule.left =
    .collection .hashSet [firstEdge, secondEdge] (some "rest") := by cbv

theorem actual_right : actualRule.right =
    .collection .hashSet [firstEdge, secondEdge, thirdEdge] (some "rest") := by cbv

theorem instantiated_collection {operation : Pattern → Pattern → Pattern}
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {assignment : ScopedRuleMatching.Assignment} {kind : CollType} {schemas : List Pattern}
    {rest : String} {target : Pattern}
    (produced : ScopedRuleMatching.instantiateWith? operation rule spec ambient .right [] 0 assignment
      (.collection kind schemas (some rest)) = some target) :
    ∃ explicit residual,
      ScopedRuleMatching.instantiateArgsWith? operation rule spec ambient .right [] 0 assignment 0 schemas =
        some explicit ∧ target = .collection kind (explicit ++ residual) none := by
  simp only [ScopedRuleMatching.instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at produced
  obtain ⟨explicit, built, value, found, arguments, occurrence, projected, interpreted, produced⟩ := produced
  cases projected with
  | collection actual residual rest =>
      cases rest with
      | none =>
          simp only at produced
          split_ifs at produced
          · exact ⟨explicit, residual, built, (Option.some.inj produced).symm⟩
      | some _ => cases produced
  | _ => cases produced

theorem instantiated_three_member {operation : Pattern → Pattern → Pattern}
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {assignment : ScopedRuleMatching.Assignment} {first second third : Pattern} {outputs : List Pattern}
    (produced : ScopedRuleMatching.instantiateArgsWith? operation rule spec ambient .right [] 0 assignment 0
      [first, second, third] = some outputs) :
    ∃ value, ScopedRuleMatching.instantiateWith? operation rule spec ambient .right [2] 0 assignment third =
      some value ∧ value ∈ outputs := by
  simp only [ScopedRuleMatching.instantiateArgsWith?, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.bind_some, Option.some.injEq, List.nil_append] at produced
  obtain ⟨one, oneMade, tail, tailMade, outputEq⟩ := produced
  obtain ⟨two, twoMade, last, lastMade, tailEq⟩ := tailMade
  obtain ⟨three, threeMade, lastEq⟩ := lastMade
  cases outputEq
  cases tailEq
  cases lastEq
  exact ⟨three, threeMade, by simp⟩

theorem third_edge_readout {operation : Pattern → Pattern → Pattern} {ambient : Nat}
    {assignment : ScopedRuleMatching.Assignment} {target : Pattern}
    (produced : ScopedRuleMatching.instantiateWith? operation actualRule actualSpec ambient .right [2] 0
      assignment thirdEdge = some target) :
    ∃ first last,
      ScopedRuleMatching.lookup assignment "x" = some first ∧
      ScopedRuleMatching.lookup assignment "z" = some last ∧
      target = .apply "Edge" [first.body, last.body] := by
  have xArguments : RuleBinding.arguments? actualRule actualSpec "x" .right [2, 0] = some [] := by cbv
  have zArguments : RuleBinding.arguments? actualRule actualSpec "z" .right [2, 1] = some [] := by cbv
  simp only [thirdEdge, ScopedRuleMatching.instantiateWith?, ScopedRuleMatching.instantiateArgsWith?,
    List.cons_append, List.nil_append, xArguments, zArguments,
    Option.bind_eq_bind, Option.bind_eq_some_iff, Option.bind_some, Option.some.injEq] at produced
  obtain ⟨arguments, built, outputEq⟩ := produced
  obtain ⟨firstBody, firstMade, tail, tailMade, argumentsEq⟩ := built
  obtain ⟨first, firstFound, firstRead⟩ := firstMade
  obtain ⟨lastBody, lastMade, tailEq⟩ := tailMade
  obtain ⟨last, lastFound, lastRead⟩ := lastMade
  have firstEq := (ConditionalEquationExecution.instantiate_root_readout first ambient firstBody firstRead).2
  have lastEq := (ConditionalEquationExecution.instantiate_root_readout last ambient lastBody lastRead).2
  cases outputEq
  cases argumentsEq
  cases tailEq
  exact ⟨first, last, firstFound, lastFound, by rw [firstEq, lastEq]⟩

theorem logical_edge_is_authored_output {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} {packet : Publication} {receipt : GeneralRuleJobs.Receipt}
    (valid : receipt.Valid plan bound expected source)
    (selected : receipt.job.declaration.rule = actualRule)
    (specified : receipt.job.declaration.binding.spec = actualSpec)
    {fact : Pattern} (read : logicalEdge? (logicalKey (packet, receipt)) = some fact) :
    ∃ items, receipt.localTarget = .collection .hashSet items none ∧ fact ∈ items.map canon := by
  have reduced := (GeneralRuleJobs.receipt_root_readout valid).2.2.2.1
  rw [selected, specified, ScopedRuleMatching.reductWith?, actual_right] at reduced
  obtain ⟨explicit, residual, instantiated, target⟩ := instantiated_collection reduced
  obtain ⟨third, thirdMade, member⟩ := instantiated_three_member instantiated
  obtain ⟨first, last, firstFound, lastFound, thirdEq⟩ := third_edge_readout thirdMade
  have inferred : fact = canon third := by
    simp only [logicalKey, logicalEdge?, firstFound, lastFound, Option.map_some, Option.bind_some,
      Option.bind_eq_bind, Option.some.injEq, CanonicalBags.canonValue] at read
    rw [← read, thirdEq, canon_apply]
    rfl
  exact ⟨explicit ++ residual, target, by
    rw [inferred]
    exact List.mem_map_of_mem (List.mem_append_left residual member)⟩

theorem logical_key_determines_fact {Choice : Type} {first second : Committed Choice}
    (same : logicalKey first = logicalKey second) :
    logicalEdge? (logicalKey first) = logicalEdge? (logicalKey second) :=
  congrArg logicalEdge? same

theorem two_route_selected {source : Pattern} {receipt : GeneralRuleJobs.Receipt}
    (valid : receipt.Valid twoRoutePlan [] (.base "Graph") source) :
    receipt.job.declaration.rule = actualRule ∧ receipt.job.declaration.binding.spec = actualSpec := by
  have singleton : twoRoutePlan.rules = [reachabilityPlan.rules[0]'(by cbv)] := by cbv
  have member := List.fst_mem_of_mem_zipIdx valid.1.1
  rw [singleton, List.mem_singleton] at member
  change receipt.job.declaration = reachabilityPlan.rules[0]'(by cbv) at member
  rw [member]
  exact ⟨rfl, rfl⟩

/-- Each projected edge comes from the actual source rule match, over a
presentation equivalent to the caller source, and is present in that rule's
actual checked output. The inference map is not an assumed certificate. -/
theorem retained_logical_edge_licensed {source : Pattern}
    {state : State twoRoutePlan [] (.base "Graph") source} (balanced : state.Balanced)
    {committed : Committed} (published : committed ∈ retained twoRoutePlan [] (.base "Graph") state.log)
    {fact : Pattern} (read : logicalEdge? (logicalKey committed) = some fact) :
    Same source (committed.1.job.presentedSource committed.1.prepared) ∧
      GeneralScopedMatch.Matches actualRule actualSpec committed.2.job.site.focusBound.length
        .left [] 0 [] (.collection .hashSet [firstEdge, secondEdge] (some "rest"))
          committed.2.job.site.focus committed.2.captured ∧
      ∃ items, committed.2.localTarget = .collection .hashSet items none ∧ fact ∈ items.map canon := by
  have valid := retained_receipt_valid balanced published
  have selected := two_route_selected valid
  have matched := GeneralRuleJobs.receipt_source_matching valid
  rw [selected.1, selected.2, actual_left] at matched
  exact ⟨retained_source_same balanced published, matched,
    logical_edge_is_authored_output valid selected.1 selected.2 read⟩

def check : IO Unit := do
  let raw := retained reachabilityPlan [] (.base "Graph") finished.batch.log
  unless !raw.isEmpty do throw (IO.userError "authored graph module published no transitive inference")
  unless (successorStates reachabilityPlan [] (.base "Graph") finished.batch.log).card == 1 do
    throw (IO.userError "authored transitive graph observed more than one conclusion state")
  unless (allocationBag reachabilityPlan [] (.base "Graph") finished.batch.log).card > 1 do
    throw (IO.userError "set residual allocation occurrences were accidentally deduplicated")
  for committed in raw do
    unless CanonicalBags.canon committed.2.target ==
        CanonicalBags.canon (graph [edge "A" "B", edge "B" "C", edge "A" "C"]) do
      throw (IO.userError "authored graph transitivity produced a wrong conclusion")
  let cyclic := retained reachabilityPlan [] (.base "Graph") finishedDiamond.batch.log
  unless !cyclic.isEmpty do throw (IO.userError "cyclic graph consumer produced no inference")
  unless (inferredFacts reachabilityPlan finished.batch.log) == {edge "A" "C"} do
    throw (IO.userError "authored graph logical-edge readout produced a wrong fact")
  unless decide (edge "C" "A" ∉ inferredFacts reachabilityPlan finished.batch.log) do
    throw (IO.userError "authored graph inferred a reverse edge")
  let routes := retained twoRoutePlan [] (.base "Graph") twoRouteFinished.batch.log
  unless (inferredFacts twoRoutePlan twoRouteFinished.batch.log) == {edge "A" "D"} do
    throw (IO.userError "two-route graph did not infer exactly A-to-D")
  let intermediates := (routes.filterMap fun entry =>
    (ScopedRuleMatching.lookup entry.2.completed "y").map (·.body)).eraseDups
  unless intermediates.length == 2 do
    throw (IO.userError "two independent graph routes were identified")
  unless (inferredBag twoRoutePlan twoRouteFinished.batch.log).card > 1 do
    throw (IO.userError "inferred fact set replaced the derivation bag")
  unless (logicalKeys twoRoutePlan twoRouteFinished.batch.log).card == 2 &&
      (logicalBag twoRoutePlan twoRouteFinished.batch.log).card == 2 &&
      logicalFacts twoRoutePlan twoRouteFinished.batch.log == {edge "A" "D"} do
    throw (IO.userError "set residual presentations manufactured logical graph derivations")
  let once := (guardedTwoRouteFinished 1).batch.log
  let duplicate := (guardedTwoRouteFinished 2).batch.log
  unless (retained (guardedTwoRoutePlan 1) [] (.base "Graph") once).length == 8 &&
      (retained (guardedTwoRoutePlan 2) [] (.base "Graph") duplicate).length == 16 do
    throw (IO.userError "guarded graph raw validation publications changed")
  unless logicalKeys (guardedTwoRoutePlan 1) once == logicalKeys (guardedTwoRoutePlan 2) duplicate &&
      logicalKeys (guardedTwoRoutePlan 1) once == logicalKeys twoRoutePlan twoRouteFinished.batch.log do
    throw (IO.userError "provider validation manufactured logical graph derivations")
  unless (logicalBag (guardedTwoRoutePlan 2) duplicate).card == 2 &&
      logicalFacts (guardedTwoRoutePlan 2) duplicate == {edge "A" "D"} do
    throw (IO.userError "logical graph routes and fact aggregation were conflated")
  let originalKeys := aToDKeys twoRoutePlan twoRouteFinished.batch.log
  let extendedKeys := aToDKeys twoRoutePlan irrelevantExtensionFinished.batch.log
  unless originalKeys.card == 2 && originalKeys == extendedKeys do
    throw (IO.userError "Unrelated graph facts manufactured a new logical inference key")
  unless aToDKeys twoRoutePlan reorderedDuplicateFinished.batch.log == originalKeys &&
      aToDKeys twoRoutePlan canonicalSourceFinished.batch.log == originalKeys do
    throw (IO.userError "Equivalent set presentations manufactured logical inference keys")
  unless logicalFacts twoRoutePlan reorderedDuplicateFinished.batch.log == {edge "A" "D"} do
    throw (IO.userError "Equivalent graph presentation changed inferred facts")
  unless (sourceSensitiveAToDKeys twoRoutePlan twoRouteFinished.batch.log ∪
      sourceSensitiveAToDKeys twoRoutePlan irrelevantExtensionFinished.batch.log).card == 4 do
    throw (IO.userError "Source-payload identity negative no longer separates the two presentations")
  IO.println "GraphLogicalIdentityControls: same 2 A-to-D keys under unrelated fact extension, reordered duplicates and canonical presentation; distinct intermediate remains distinct"
  IO.println s!"AuthoredGraphObservationControls: {raw.length} committed allocations, {(successorStates reachabilityPlan [] (.base "Graph") finished.batch.log).card} fact-state, {(allocationBag reachabilityPlan [] (.base "Graph") finished.batch.log).card} occurrence derivations; cyclic packets {cyclic.length}"
  IO.println s!"KnowledgeGraphObservationControls: {intermediates.length} independent routes, {routes.length} retained allocations -> {(inferredFacts twoRoutePlan twoRouteFinished.batch.log).card} inferred fact / {(inferredBag twoRoutePlan twoRouteFinished.batch.log).card} occurrence derivations"
  IO.println "LogicalKnowledgeGraphControls: 8/16 allocation/validation packets -> 2 logical routes -> 1 inferred fact; consume/retain and duplicate validation do not multiply routes"

#eval check

#print axioms logicalKey_ignores_allocation
#print axioms logicalKey_ignores_source_payload
#print axioms logicalKey_canonical_source_presentation
#print axioms logicalKey_ignores_query_validation
#print axioms logicalKey_erases_query_in_history
#print axioms logicalKey_erases_freshness_in_history
#print axioms logicalKey_nonrest_ext
#print axioms intermediate_distinguishes_route
#print axioms logical_key_determines_fact
#print axioms logicalBag_ordered_presentation
#print axioms logicalFacts_ordered_presentation
#print axioms retained_logical_edge_licensed

end GraphControls

end Mettapedia.GSLT.LanguageDef.CollectionConsumers.Controls.Observation
