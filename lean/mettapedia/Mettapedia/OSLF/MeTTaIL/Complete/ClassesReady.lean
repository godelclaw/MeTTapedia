import Mettapedia.OSLF.MeTTaIL.Complete.ClassesFootprint

/-!
# Every reached state of the search modulo equations is ready

A lane is ready when its key is licensed at its representative (a rule job of it, or an equation
lane of it or of a predecessor candidate), its deepening search is reachable, and the search stays
within the footprint. A state is ready when its representatives stay within the footprint and
every lane is ready. Rounds keep states ready: lanes stay ready under a unit of work, every
discovered member is within the footprint, and a new member's lanes start ready.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Complete.Footprint

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralPremise GeneralExecutionAdmission ScopedRuleMatching RuleBinding

variable (plan : Plan) (bound : List TypeExpr) (expected : TypeExpr) (footprint : List String)

/-- What a lane of the search modulo equations satisfies. -/
def KeyReady : (key : Classes.Key) → Deep.State (Classes.family plan key) → Prop
  | .rule rep job, state =>
      job.Valid plan bound expected rep.pattern ∧ (∀ name ∈ rep.pattern.freeFvarNames, name ∈ footprint) ∧
        Deep.Good (Step.family plan job) state ∧
        Deep.Covered (Step.family plan job) footprint (FiringWithin footprint job) state
  | .forward rep lane, state =>
      lane ∈ EquationJob.lanes plan bound expected rep.pattern ∧ Deep.Good (EquationJob.family plan lane) state ∧
        Deep.Covered (EquationJob.family plan lane) footprint (OutcomeWithin footprint) state
  | .backward _ candidate lane, state =>
      lane ∈ EquationJob.lanes plan bound expected candidate ∧ Deep.Good (EquationJob.family plan lane) state ∧
        Deep.Covered (EquationJob.family plan lane) footprint (OutcomeWithin footprint) state

/-- A state whose members and lanes stay within the footprint. -/
structure ClassReady (state : Classes.State plan) : Prop where
  reps : ∀ rep ∈ state.reps, ∀ name ∈ rep.pattern.freeFvarNames, name ∈ footprint
  entries : ∀ entry ∈ state.entries, KeyReady plan bound expected footprint entry.1 entry.2
  log : ∀ receipt ∈ state.log, ∀ name ∈ receipt.target.freeFvarNames, name ∈ footprint

variable {plan bound expected footprint}

theorem key_ready_tick (scope : Scope plan footprint) {key : Classes.Key} {state : Deep.State (Classes.family plan key)}
    (ready : KeyReady plan bound expected footprint key state) :
    KeyReady plan bound expected footprint key (Deep.tick (Classes.family plan key) state) := by
  cases key with
  | rule rep job =>
    exact ⟨ready.1, ready.2.1, Deep.tick_good _ ready.2.2.1,
      Deep.tick_covered (job_footprinted scope ready.1 ready.2.1) ready.2.2.2⟩
  | forward rep lane =>
    exact ⟨ready.1, Deep.tick_good _ ready.2.1, Deep.tick_covered (lane_footprinted scope ready.1) ready.2.2⟩
  | backward rep candidate lane =>
    exact ⟨ready.1, Deep.tick_good _ ready.2.1, Deep.tick_covered (lane_footprinted scope ready.1) ready.2.2⟩

theorem key_ready_start (scope : Scope plan footprint) {rep : Classes.Rep}
    (inside : ∀ name ∈ rep.pattern.freeFvarNames, name ∈ footprint) {key : Classes.Key}
    (member : key ∈ Classes.lanesOf plan bound expected rep) :
    KeyReady plan bound expected footprint key (Deep.start (Classes.family plan key)) := by
  simp only [Classes.lanesOf, List.mem_append, List.mem_map, List.mem_flatMap] at member
  rcases member with (⟨job, listed, rfl⟩ | ⟨lane, listed, rfl⟩) | ⟨candidate, _, lane, listed, rfl⟩
  · have licensed := (GeneralRuleJobs.jobs_spec plan bound expected rep.pattern job).mp listed
    exact ⟨licensed, inside, Deep.start_good _, Deep.start_covered (job_footprinted scope licensed inside)⟩
  · exact ⟨listed, Deep.start_good _, Deep.start_covered (lane_footprinted scope listed)⟩
  · exact ⟨listed, Deep.start_good _, Deep.start_covered (lane_footprinted scope listed)⟩

/-- Every member a ready lane discovers is within the footprint. -/
theorem discoveries_within (scope : Scope plan footprint) {key : Classes.Key}
    {state : Deep.State (Classes.family plan key)} (ready : KeyReady plan bound expected footprint key state)
    (payloads : List (Classes.family plan key).Payload) :
    ∀ event ∈ Classes.events plan bound expected key payloads, ∀ pattern conversions,
      event = .discovery pattern conversions → ∀ name ∈ pattern.freeFvarNames, name ∈ footprint := by
  intro event member pattern conversions discovered
  cases key with
  | rule rep job =>
    simp only [Classes.events, List.mem_map] at member
    obtain ⟨_, _, rfl⟩ := member
    cases discovered
  | forward rep lane =>
    simp only [Classes.events, List.mem_map, List.mem_filterMap] at member
    obtain ⟨receipt, ⟨payload, _, lifted⟩, rfl⟩ := member
    cases discovered
    exact lift_target_within scope.declared lifted
  | backward rep candidate lane =>
    simp only [Classes.events, List.mem_map] at member
    obtain ⟨_, _, rfl⟩ := member
    cases discovered
    exact lane_source_within scope.declared ready.1

/-- A lifted rule firing's target is well-sorted, so it is within the footprint. -/
theorem step_lift_within (declared : Declared plan footprint) {job : GeneralRuleJobs.Job}
    {firing : DeepRoot.Firing} {receipt : GeneralRuleJobs.Receipt}
    (lifted : Step.lift plan bound expected job firing = some receipt) :
    ∀ name ∈ receipt.target.freeFvarNames, name ∈ footprint := by
  unfold Step.lift at lifted
  split at lifted
  · rename_i accepted
    cases lifted
    exact sorted_within declared (Bool.and_eq_true_iff.mp accepted).2
  · cases lifted

theorem mem_firings {receipt : GeneralOccurrenceSemantics.Receipt} :
    ∀ events : List Classes.Event, receipt ∈ Classes.firings events → Classes.Event.firing receipt ∈ events
  | [], member => by simp [Classes.firings] at member
  | .firing other :: rest, member => by
    rw [Classes.firings] at member
    rcases List.mem_cons.mp member with rfl | later
    · simp
    · exact List.mem_cons_of_mem _ (mem_firings rest later)
  | .discovery _ _ :: rest, member => by
    rw [Classes.firings] at member
    exact List.mem_cons_of_mem _ (mem_firings rest member)

/-- Every receipt a lane publishes has its target within the footprint. -/
theorem firings_within (declared : Declared plan footprint) (key : Classes.Key)
    (payloads : List (Classes.family plan key).Payload) :
    ∀ receipt ∈ Classes.firings (Classes.events plan bound expected key payloads),
      ∀ name ∈ receipt.target.freeFvarNames, name ∈ footprint := by
  intro receipt member
  have event := mem_firings _ member
  cases key with
  | rule rep job =>
    simp only [Classes.events, List.mem_map, List.mem_filterMap] at event
    obtain ⟨firing, ⟨payload, _, lifted⟩, same⟩ := event
    cases same
    exact step_lift_within declared lifted
  | forward rep lane =>
    simp only [Classes.events, List.mem_map] at event
    obtain ⟨_, _, impossible⟩ := event
    cases impossible
  | backward rep candidate lane =>
    simp only [Classes.events, List.mem_map] at event
    obtain ⟨_, _, impossible⟩ := event
    cases impossible

theorem firings_append (first second : List Classes.Event) :
    Classes.firings (first ++ second) = Classes.firings first ++ Classes.firings second := by
  induction first with
  | nil => rfl
  | cons event rest ih => cases event <;> simp [Classes.firings, ih]

theorem firings_flatMap_within (declared : Declared plan footprint) :
    ∀ (advanced : List (Classes.Entry plan × List Classes.Event)),
      (∀ pair ∈ advanced, ∃ payloads, pair.2 = Classes.events plan bound expected pair.1.1 payloads) →
      ∀ receipt ∈ Classes.firings (advanced.flatMap Prod.snd), ∀ name ∈ receipt.target.freeFvarNames,
        name ∈ footprint
  | [], _ => by simp [Classes.firings]
  | pair :: rest, shaped => by
    intro receipt member
    rw [List.flatMap_cons, firings_append] at member
    rcases List.mem_append.mp member with here | later
    · obtain ⟨payloads, same⟩ := shaped pair (by simp)
      rw [same] at here
      exact firings_within declared _ payloads receipt here
    · exact firings_flatMap_within declared rest (fun other inside => shaped other (by simp [inside])) receipt later

theorem addDiscoveries_within (born : Nat) :
    ∀ (reps : List Classes.Rep) (events : List Classes.Event),
      (∀ rep ∈ reps, ∀ name ∈ rep.pattern.freeFvarNames, name ∈ footprint) →
      (∀ event ∈ events, ∀ pattern conversions, event = .discovery pattern conversions →
        ∀ name ∈ pattern.freeFvarNames, name ∈ footprint) →
      ∀ rep ∈ Classes.addDiscoveries born reps events, ∀ name ∈ rep.pattern.freeFvarNames, name ∈ footprint
  | reps, [], inside, _ => by simpa [Classes.addDiscoveries] using inside
  | reps, .firing receipt :: rest, inside, found => by
    rw [Classes.addDiscoveries]
    exact addDiscoveries_within born reps rest inside (fun event member => found event (by simp [member]))
  | reps, .discovery pattern conversions :: rest, inside, found => by
    rw [Classes.addDiscoveries]
    split
    · exact addDiscoveries_within born reps rest inside (fun event member => found event (by simp [member]))
    · apply addDiscoveries_within born _ rest _ (fun event member => found event (by simp [member]))
      intro rep member
      rcases List.mem_append.mp member with old | new
      · exact inside rep old
      · rcases List.mem_singleton.mp new with rfl
        exact found _ (by simp) pattern conversions rfl

theorem ready_round (scope : Scope plan footprint) {state : Classes.State plan}
    (ready : ClassReady plan bound expected footprint state) :
    ClassReady plan bound expected footprint (Classes.round plan bound expected state) := by
  have advanced : ∀ entry ∈ state.entries,
      KeyReady plan bound expected footprint (Classes.advance plan bound expected entry).1.1
        (Classes.advance plan bound expected entry).1.2 := fun entry member =>
    key_ready_tick scope (ready.entries entry member)
  have found : ∀ event ∈ (state.entries.map (Classes.advance plan bound expected)).flatMap Prod.snd,
      ∀ pattern conversions, event = .discovery pattern conversions →
        ∀ name ∈ pattern.freeFvarNames, name ∈ footprint := by
    intro event member
    obtain ⟨pair, inside, eventMember⟩ := List.mem_flatMap.mp member
    obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp inside
    exact discoveries_within scope (ready.entries entry entryMember) _ event eventMember
  have reps := addDiscoveries_within (state.round + 1) state.reps _ ready.reps found
  refine ⟨reps, ?_, ?_⟩
  rotate_left
  · intro receipt member
    simp only [Classes.round] at member
    rcases List.mem_append.mp member with old | new
    · exact ready.log receipt old
    · refine firings_flatMap_within (bound := bound) (expected := expected) scope.declared _ ?_ receipt new
      intro pair inside
      obtain ⟨entry, _, rfl⟩ := List.mem_map.mp inside
      exact ⟨_, rfl⟩
  intro entry member
  simp only [Classes.round] at member
  rcases List.mem_append.mp member with old | new
  · obtain ⟨pair, inside, rfl⟩ := List.mem_map.mp old
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp inside
    exact advanced original originalMember
  · obtain ⟨key, keyMember, rfl⟩ := List.mem_map.mp new
    obtain ⟨rep, repMember, lanesMember⟩ := List.mem_flatMap.mp keyMember
    exact key_ready_start scope (reps rep (List.mem_of_mem_drop repMember)) lanesMember

theorem ready_rounds (scope : Scope plan footprint) :
    ∀ (work : Nat) {state : Classes.State plan}, ClassReady plan bound expected footprint state →
      ClassReady plan bound expected footprint (Classes.rounds plan bound expected work state)
  | 0, _, ready => ready
  | work + 1, _, ready => ready_rounds scope work (ready_round scope ready)

theorem ready_begin (scope : Scope plan footprint) {source : Pattern}
    (inside : ∀ name ∈ source.freeFvarNames, name ∈ footprint) :
    ClassReady plan bound expected footprint (Classes.begin plan bound expected source) := by
  refine ⟨?_, ?_, ?_⟩
  · intro rep member
    rcases List.mem_singleton.mp member with rfl
    exact inside
  rotate_left
  · intro receipt member
    simp [Classes.begin] at member
  · intro entry member
    obtain ⟨key, keyMember, rfl⟩ := List.mem_map.mp member
    exact key_ready_start scope (rep := ⟨source, [], 0⟩) inside keyMember

variable (plan)

/-- The plan's declared free names, then its provider's undeclared names. -/
def declaredFootprint : List String :=
  plan.snapshot.freeTypes.map Prod.fst ++
    (providerFreeNames plan.snapshot.provider).filter fun name => name ∉ plan.snapshot.freeTypes.map Prod.fst

variable {plan}

theorem free_declared {name : String} {type : TypeExpr} (found : plan.snapshot.free name = some type) :
    name ∈ plan.snapshot.freeTypes.map Prod.fst := by
  simp only [GeneralExecutionAdmission.Snapshot.free, Option.map_eq_some_iff] at found
  obtain ⟨entry, located, _⟩ := found
  have same := List.find?_some located
  simp only [beq_iff_eq] at same
  exact List.mem_map.mpr ⟨entry, List.mem_of_find?_eq_some located, same⟩

theorem declared_footprint : Declared plan (declaredFootprint plan) := fun _ _ found =>
  List.mem_append_left _ (free_declared found)

/-- Every plan with a finite provider and admitted equations is in scope on its declared names. -/
theorem declared_scope (finite : plan.snapshot.provider.dynamicRelations = [])
    (admitted : ∀ equation ∈ plan.equations, admittedFor equation.rule equation.binding.spec = true) :
    Scope plan (declaredFootprint plan) where
  declared := declared_footprint
  finite := finite
  provider name member := by
    by_cases inside : name ∈ plan.snapshot.freeTypes.map Prod.fst
    · exact List.mem_append_left _ inside
    · exact List.mem_append_right _ (List.mem_filter.mpr ⟨member, by simpa using inside⟩)
  admitted := admitted

theorem entriesOn_keys : ∀ entries : List (String × TypeExpr), (entries.map Prod.fst).Nodup →
    (entries.map Prod.fst).filterMap
        (fun name => ((entries.find? fun entry => entry.1 == name).map Prod.snd).map (name, ·)) = entries
  | [], _ => rfl
  | (name, type) :: rest, distinct => by
    rw [List.map_cons, List.nodup_cons] at distinct
    rw [List.map_cons, List.filterMap_cons]
    simp only [List.find?_cons, beq_self_eq_true, Option.map_some]
    congr 1
    refine (List.filterMap_congr ?_).trans (entriesOn_keys rest distinct.2)
    intro other member
    have differ : (name == other) = false := by
      rw [beq_eq_false_iff_ne]
      rintro rfl
      exact distinct.1 member
    simp only [differ]

/-- On its declared footprint, the free table is the plan's own list of free types. -/
theorem entriesOn_declared (distinct : (plan.snapshot.freeTypes.map Prod.fst).Nodup) :
    plan.snapshot.free.entriesOn (declaredFootprint plan) = plan.snapshot.freeTypes := by
  unfold Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.entriesOn declaredFootprint
  rw [List.filterMap_append]
  have undeclared : ((providerFreeNames plan.snapshot.provider).filter fun name =>
      name ∉ plan.snapshot.freeTypes.map Prod.fst).filterMap
        (fun name => (plan.snapshot.free name).map (name, ·)) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro name member
    have outside := (List.mem_filter.mp member).2
    cases found : plan.snapshot.free name with
    | none => rfl
    | some type => exact absurd (free_declared found) (by simpa using outside)
  rw [undeclared, List.append_nil]
  exact entriesOn_keys _ distinct

/-! ## Compiled plans -/

section Compiled

variable {snapshot : Snapshot} {permissions : Permissions}

theorem obligation_stratification
    (pending : (compile snapshot permissions).obligations.filter (· != .childStratification) = [])
    {obligation : Obligation} (member : obligation ∈ (compile snapshot permissions).obligations) :
    obligation = .childStratification := by
  by_contra other
  have kept : obligation ∈ (compile snapshot permissions).obligations.filter (· != .childStratification) :=
    List.mem_filter.mpr ⟨member, by simpa using other⟩
  rw [pending] at kept
  cases kept

/-- A compiled plan whose only obligation may be stratification has distinct free names. -/
theorem compiled_distinct
    (pending : (compile snapshot permissions).obligations.filter (· != .childStratification) = []) :
    ((compile snapshot permissions).snapshot.freeTypes.map Prod.fst).Nodup := by
  have free : checkFreeContext snapshot = true := by
    by_contra failed
    have bad : Obligation.invalidFreeContext ∈ (compile snapshot permissions).obligations := by
      simp [compile, Bool.eq_false_iff.mpr failed]
    cases obligation_stratification pending bad
  simpa [compile, checkFreeContext] using (Bool.and_eq_true_iff.mp free).1

/-- Every equation of such a plan is admitted. -/
theorem compiled_admitted
    (pending : (compile snapshot permissions).obligations.filter (· != .childStratification) = []) :
    ∀ equation ∈ (compile snapshot permissions).equations,
      admittedFor equation.rule equation.binding.spec = true := by
  intro equation member
  obtain ⟨authored, index, direction, pair, enabled, allowed, planned⟩ := compiled_equation_origin member
  have selectedMember : (authored, index, direction) ∈ selectedEquations snapshot permissions :=
    List.mem_flatMap.mpr ⟨(authored, index), List.mem_filter.mpr ⟨pair, enabled⟩,
      List.mem_map.mpr ⟨direction, List.mem_eraseDups.mpr allowed, rfl⟩⟩
  have empty : equationObligations snapshot index authored direction = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro obligation inside
    have total : obligation ∈ (compile snapshot permissions).obligations := by
      have flat : obligation ∈ (selectedEquations snapshot permissions).flatMap
          (fun (equation, index, direction) => equationObligations snapshot index equation direction) :=
        List.mem_flatMap.mpr ⟨(authored, index, direction), selectedMember, inside⟩
      simp only [compile, List.mem_append]
      tauto
    have strata := obligation_stratification pending total
    subst strata
    unfold equationObligations at inside
    dsimp only at inside
    cases found : GeneralRuleBindingInference.compile? snapshot.language
        (ScopedEquationExecution.orientedRule authored direction) with
    | none => simp [found] at inside
    | some binding =>
      simp only [found] at inside
      split at inside
      · split at inside
        · split at inside <;> simp at inside
        · simp at inside
      · simp at inside
  obtain ⟨other, again, ready⟩ := (equationObligations_empty_iff snapshot index authored direction).mp empty
  rw [planned] at again
  cases again
  unfold EquationPlan.rule
  have checked := ready
  unfold equationPlan? at planned
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at planned
  obtain ⟨binding, _, accepted⟩ := planned
  split at accepted
  · cases accepted
    exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp checked).1).1).1
  · cases accepted

/-- A compiled plan the complete machine accepts, with a finite provider, is in scope on its
declared footprint, and its free table there is its own list of free types. -/
theorem compiled_scope
    (pending : (compile snapshot permissions).obligations.filter (· != .childStratification) = [])
    (finite : snapshot.provider.dynamicRelations = []) :
    Scope (compile snapshot permissions) (declaredFootprint (compile snapshot permissions)) ∧
      (compile snapshot permissions).snapshot.free.entriesOn (declaredFootprint (compile snapshot permissions)) =
        (compile snapshot permissions).snapshot.freeTypes :=
  ⟨declared_scope finite (compiled_admitted pending), entriesOn_declared (compiled_distinct pending)⟩

end Compiled

end Mettapedia.OSLF.MeTTaIL.Complete.Footprint