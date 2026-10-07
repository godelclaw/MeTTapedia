import GoalSystem

/-!
# Weighted service for the shared goal queue

Goals retain their existing identity, recurrence, motivation and completion
ledger. Scheduling compares service/share exactly by cross multiplication;
age and base urgency break equal-service ties. Every allocated quantum is
charged, including unsuccessful work. Only the existing receipt checker can
acknowledge a goal cycle.

The mechanism is a discrete weighted virtual-runtime scheduler, related to
stride scheduling (Waldspurger and Weihl, MIT/LCS/TM-528, 1995). It borrows
EEVDF's separation of service owed from work completion, but does not claim
to implement Linux's lag eligibility or latency/deadline policy.

* https://www.waldspurger.org/carl/papers/stride-mit-tm528.pdf
* https://docs.kernel.org/scheduler/sched-eevdf.html

The bounded-service theorem concerns a finite, fixed cohort and positive
shares, counting successful scheduling opportunities. It is independent of
task success. A wall-clock bound additionally needs bounded action duration
and continued admission. Unbounded arrivals, weight changes, interruption
or resource denial are not hidden inside a fairness assumption.

From the repository root, with its pinned Lean dependencies installed:

```
python3 lean/pettaclaw/check_observed_strategy.py --suite fair-goals --output-dir build/fair-goals
```
-/

namespace FairGoalScheduling

open GoalSystem

def runnable (goal : Goal) : Bool := eligible goal && decide (0 < goal.share)

/-- Exact comparison of normalized service; no integer division or floating
point rounding can erase a small positive share. -/
def serviceLE (a b : Goal) : Prop := a.service * b.share ≤ b.service * a.share

instance (a b : Goal) : Decidable (serviceLE a b) := inferInstanceAs
  (Decidable (a.service * b.share ≤ b.service * a.share))

def prefer (a b : Goal) : Prop :=
  a.service * b.share < b.service * a.share ∨
    (a.service * b.share = b.service * a.share ∧ urgency b ≤ urgency a)

instance (a b : Goal) : Decidable (prefer a b) := inferInstanceAs
  (Decidable (a.service * b.share < b.service * a.share ∨
    (a.service * b.share = b.service * a.share ∧ urgency b ≤ urgency a)))

def select : List Goal → Option Goal
  | [] => none
  | goal :: goals =>
      if runnable goal then
        match select goals with
        | none => some goal
        | some later => if prefer goal later then some goal else some later
      else select goals

def chargeGoal (id units : Nat) (goal : Goal) : Goal :=
  if goal.id = id then { goal with service := goal.service + units } else goal

def charge (id units : Nat) (goals : List Goal) : List Goal :=
  goals.map (chargeGoal id units)

/-- Allocation trace with unit quanta. Completion is intentionally absent:
a stuck task consumes its share just as a successful task does. -/
def trace : Nat → List Goal → List Nat
  | 0, _ => []
  | fuel + 1, goals =>
      match select goals with
      | none => []
      | some goal => goal.id :: trace fuel (charge goal.id 1 goals)

/-- Number of unit quanta this competitor could receive before it must
overtake the target's current normalized service. Includes an equal-score
quantum, so the bound is independent of the urgency tie breaker. -/
def capacity (target other : Goal) : Nat :=
  target.service * other.share / target.share + 1 - other.service

def waitBudget (target : Goal) : List Goal → Nat
  | [] => 0
  | goal :: goals => capacity target goal + waitBudget target goals

theorem runnable_contract (goal : Goal) :
    runnable goal = true ↔ eligible goal = true ∧ 0 < goal.share := by
  simp [runnable]

theorem serviceLE_refl (goal : Goal) : serviceLE goal goal := Nat.le_refl _

theorem serviceLE_trans (a b c : Goal) (positive : 0 < b.share)
    (ab : serviceLE a b) (bc : serviceLE b c) : serviceLE a c := by
  have first := Nat.mul_le_mul_right c.share ab
  have second := Nat.mul_le_mul_right a.share bc
  have joined : (a.service * c.share) * b.share ≤
      (c.service * a.share) * b.share := by
    exact le_trans (by simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using first)
      (by simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using second)
  exact Nat.le_of_mul_le_mul_right joined positive

theorem select_none_iff (goals : List Goal) :
    select goals = none ↔ ∀ goal ∈ goals, runnable goal = false := by
  induction goals with
  | nil => simp [select]
  | cons goal goals ih =>
      cases available : runnable goal with
      | false => simpa [select, available] using ih
      | true =>
          cases later : select goals <;> simp [select, available, later]
          split <;> simp

theorem selection_contract (goals : List Goal) (chosen : Goal)
    (selected : select goals = some chosen) :
    chosen ∈ goals ∧ runnable chosen = true ∧
      ∀ goal ∈ goals, runnable goal = true → serviceLE chosen goal := by
  induction goals generalizing chosen with
  | nil => simp [select] at selected
  | cons head tail ih =>
      cases available : runnable head with
      | false =>
          have found : select tail = some chosen := by simpa [select, available] using selected
          obtain ⟨member, valid, minimum⟩ := ih chosen found
          refine ⟨List.mem_cons_of_mem head member, valid, ?_⟩
          intro goal member eligibleGoal
          rcases List.mem_cons.mp member with equal | member
          · subst goal; simp [available] at eligibleGoal
          · exact minimum goal member eligibleGoal
      | true =>
          cases later : select tail with
          | none =>
              have equal : head = chosen := by simpa [select, available, later] using selected
              subst chosen
              refine ⟨List.mem_cons_self, available, ?_⟩
              intro goal member eligibleGoal
              rcases List.mem_cons.mp member with equal | member
              · subst goal; exact serviceLE_refl _
              · have invalid := (select_none_iff tail).mp later goal member
                simp [invalid] at eligibleGoal
          | some best =>
              obtain ⟨member, valid, minimum⟩ := ih best later
              by_cases wins : prefer head best
              · have equal : head = chosen := by
                  simpa [select, available, later, wins] using selected
                subst chosen
                have lower : serviceLE head best := by
                  unfold prefer at wins; unfold serviceLE; omega
                refine ⟨List.mem_cons_self, available, ?_⟩
                intro goal member eligibleGoal
                rcases List.mem_cons.mp member with equal | member
                · subst goal; exact serviceLE_refl _
                · exact serviceLE_trans head best goal
                    ((runnable_contract best).mp valid).2 lower
                    (minimum goal member eligibleGoal)
              · have equal : best = chosen := by
                  simpa [select, available, later, wins] using selected
                subst chosen
                refine ⟨List.mem_cons_of_mem head member, valid, ?_⟩
                intro goal member eligibleGoal
                rcases List.mem_cons.mp member with equal | member
                · subst goal; unfold prefer at wins; unfold serviceLE; omega
                · exact minimum goal member eligibleGoal

theorem charge_preserves_goal_meaning (id units : Nat) (goal : Goal) :
    (chargeGoal id units goal).id = goal.id ∧
    (chargeGoal id units goal).share = goal.share ∧
    (chargeGoal id units goal).finished = goal.finished ∧
    (chargeGoal id units goal).round = goal.round ∧
    (chargeGoal id units goal).age = goal.age ∧
    runnable (chargeGoal id units goal) = runnable goal := by
  unfold chargeGoal
  split <;> simp [runnable, eligible]

theorem charge_keeps_other (target : Goal) (goals : List Goal) (id units : Nat)
    (member : target ∈ goals) (different : target.id ≠ id) :
    target ∈ charge id units goals := by
  have unchanged : chargeGoal id units target = target := by simp [chargeGoal, different]
  rw [← unchanged]
  exact List.mem_map.mpr ⟨target, member, rfl⟩

theorem capacity_charge_le (target other : Goal) (id units : Nat) :
    capacity target (chargeGoal id units other) ≤ capacity target other := by
  unfold chargeGoal
  split <;> simp only [capacity] <;> omega

theorem capacity_charge_lt (target other : Goal) (units : Nat)
    (positive : 0 < target.share) (spent : 0 < units) (owed : serviceLE other target) :
    capacity target (chargeGoal other.id units other) < capacity target other := by
  have under : other.service ≤ target.service * other.share / target.share :=
    (Nat.le_div_iff_mul_le positive).mpr owed
  simp only [chargeGoal, ↓reduceIte, capacity]
  omega

theorem charge_budget_le (target : Goal) (goals : List Goal) (id units : Nat) :
    waitBudget target (charge id units goals) ≤ waitBudget target goals := by
  induction goals with
  | nil => simp [charge, waitBudget]
  | cons goal goals ih =>
      simpa [charge, waitBudget] using
        Nat.add_le_add (capacity_charge_le target goal id units) ih

theorem charge_budget_lt (target chosen : Goal) (goals : List Goal) (units : Nat)
    (member : chosen ∈ goals) (positive : 0 < target.share) (spent : 0 < units)
    (owed : serviceLE chosen target) :
    waitBudget target (charge chosen.id units goals) < waitBudget target goals := by
  induction goals with
  | nil => simp at member
  | cons goal goals ih =>
      rcases List.mem_cons.mp member with equal | member
      · subst goal
        simpa [charge, waitBudget] using
          Nat.add_lt_add_of_lt_of_le (capacity_charge_lt target chosen units positive spent owed)
            (charge_budget_le target goals chosen.id units)
      · simpa [charge, waitBudget] using
          Nat.add_lt_add_of_le_of_lt (capacity_charge_le target goal chosen.id units) (ih member)

/-- A genuinely bounded service theorem, independent of task completion.
No target name, task kind or success predicate occurs in the selector. -/
theorem service_within_budget (fuel : Nat) (goals : List Goal) (target : Goal)
    (member : target ∈ goals) (available : runnable target = true)
    (enough : waitBudget target goals < fuel) :
    target.id ∈ trace fuel goals := by
  induction fuel generalizing goals with
  | zero => omega
  | succ fuel ih =>
      cases selected : select goals with
      | none =>
          have unavailable := (select_none_iff goals).mp selected target member
          simp [available] at unavailable
      | some chosen =>
          obtain ⟨chosenMember, _, minimum⟩ := selection_contract goals chosen selected
          simp only [trace, selected]
          by_cases same : target.id = chosen.id
          · exact List.mem_cons.mpr (Or.inl same)
          · apply List.mem_cons.mpr; right
            apply ih (charge chosen.id 1 goals)
              (charge_keeps_other target goals chosen.id 1 member same)
            have decrease := charge_budget_lt target chosen goals 1 chosenMember
              ((runnable_contract target).mp available).2 (by decide)
              (minimum target member available)
            omega

theorem no_starvation (goals : List Goal) (target : Goal)
    (member : target ∈ goals) (available : runnable target = true) :
    target.id ∈ trace (waitBudget target goals + 1) goals :=
  service_within_budget _ goals target member available (Nat.lt_succ_self _)

theorem time_preserves_accounting (ticks : Nat) (goal : Goal) :
    (advance ticks goal).share = goal.share ∧
    (advance ticks goal).service = goal.service := by
  unfold advance
  split <;> exact ⟨rfl, rfl⟩

theorem runnable_after_time (ticks : Nat) (goal : Goal)
    (available : runnable goal = true) : runnable (advance ticks goal) = true := by
  obtain ⟨eligibleGoal, positive⟩ := (runnable_contract goal).mp available
  have unfinished : goal.finished = false := by
    by_cases finished : goal.finished = true
    · simp [eligible, finished] at eligibleGoal
    · exact Bool.eq_false_iff.mpr finished
  cases recurrence : goal.recurrence <;> simp_all [advance, runnable, eligible]
  omega

theorem waitBudget_after_time (ticks : Nat) (target : Goal) (goals : List Goal) :
    waitBudget (advance ticks target) (goals.map (advance ticks)) = waitBudget target goals := by
  induction goals with
  | nil => rfl
  | cons goal goals ih =>
      simp only [List.map_cons, waitBudget, capacity, ih,
        (time_preserves_accounting ticks target).1,
        (time_preserves_accounting ticks target).2,
        (time_preserves_accounting ticks goal).1,
        (time_preserves_accounting ticks goal).2]

/-- Clock advances are arbitrary, including zero. A finite opportunity list
does not promise that those opportunities occur in bounded wall time. -/
def timedTrace : List Nat → List Goal → List Nat
  | [], _ => []
  | elapsed :: rest, goals =>
      let aged := goals.map (advance elapsed)
      match select aged with
      | none => timedTrace rest aged
      | some chosen => chosen.id :: timedTrace rest (charge chosen.id 1 aged)

theorem timed_service_within_budget (opportunities : List Nat) (goals : List Goal) (target : Goal)
    (member : target ∈ goals) (available : runnable target = true)
    (enough : waitBudget target goals < opportunities.length) :
    target.id ∈ timedTrace opportunities goals := by
  induction opportunities generalizing goals target with
  | nil => simp at enough
  | cons elapsed rest ih =>
      let aged := goals.map (advance elapsed)
      have targetMember : advance elapsed target ∈ aged :=
        List.mem_map.mpr ⟨target, member, rfl⟩
      have stillAvailable := runnable_after_time elapsed target available
      have sameId : (advance elapsed target).id = target.id := by
        unfold advance; split <;> rfl
      cases selected : select aged with
      | none =>
          have impossible := (select_none_iff aged).mp selected (advance elapsed target) targetMember
          simp [stillAvailable] at impossible
      | some chosen =>
          obtain ⟨chosenMember, _, minimum⟩ := selection_contract aged chosen selected
          change target.id ∈ (match select aged with
            | none => timedTrace rest aged
            | some goal => goal.id :: timedTrace rest (charge goal.id 1 aged))
          rw [selected]
          by_cases same : target.id = chosen.id
          · exact List.mem_cons.mpr (Or.inl same)
          · apply List.mem_cons.mpr; right
            rw [← sameId]
            apply ih _ (advance elapsed target)
              (charge_keeps_other (advance elapsed target) aged chosen.id 1 targetMember
                (by simpa only [sameId] using same)) stillAvailable
            have decreased := charge_budget_lt (advance elapsed target) chosen aged 1
              chosenMember ((runnable_contract _).mp stillAvailable).2 (by decide)
              (minimum _ targetMember stillAvailable)
            have unchanged := waitBudget_after_time elapsed target goals
            change waitBudget (advance elapsed target) aged = waitBudget target goals at unchanged
            simp only [List.length_cons] at enough
            omega

/-- A queue's service discrepancy, without division. A charged quantum of
at most `quantum` can overshoot another goal by at most that quantum divided
by the charged goal's share. This bounds proportional-service error. -/
def WithinQuantum (quantum : Nat) (goals : List Goal) : Prop :=
  ∀ a ∈ goals, ∀ b ∈ goals,
    a.service * b.share ≤ b.service * a.share + quantum * b.share

def UniqueIds (goals : List Goal) : Prop :=
  (goals.map Goal.id).Nodup

instance (goals : List Goal) : Decidable (UniqueIds goals) :=
  inferInstanceAs (Decidable (goals.map Goal.id).Nodup)

theorem unique_id_injective (goals : List Goal) (unique : UniqueIds goals)
    (a : Goal) (ma : a ∈ goals) (b : Goal) (mb : b ∈ goals) (same : a.id = b.id) : a = b := by
  induction goals with
  | nil => simp at ma
  | cons head tail ih =>
      obtain ⟨absent, tailUnique⟩ := List.nodup_cons.mp unique
      rcases List.mem_cons.mp ma with rfl | aTail
      · rcases List.mem_cons.mp mb with rfl | bTail
        · rfl
        · exact False.elim (absent (List.mem_map.mpr ⟨b, bTail, same.symm⟩))
      · rcases List.mem_cons.mp mb with rfl | bTail
        · exact False.elim (absent (List.mem_map.mpr ⟨a, aTail, same⟩))
        · exact ih tailUnique aTail bTail

theorem charge_service_monotone (id units : Nat) (goal : Goal) :
    goal.service ≤ (chargeGoal id units goal).service := by
  unfold chargeGoal
  split <;> simp

theorem charge_preserves_unique (goals : List Goal) (id units : Nat)
    (unique : UniqueIds goals) : UniqueIds (charge id units goals) := by
  have sameIds : (charge id units goals).map Goal.id = goals.map Goal.id := by
    simp only [charge, List.map_map]
    congr 1
    funext goal
    exact (charge_preserves_goal_meaning id units goal).1
  unfold UniqueIds
  rw [sameIds]
  exact unique

def totalService (goals : List Goal) : Nat := (goals.map Goal.service).sum

theorem charge_absent (goals : List Goal) (id units : Nat)
    (absent : id ∉ goals.map Goal.id) : charge id units goals = goals := by
  induction goals with
  | nil => rfl
  | cons head tail ih =>
      have different : head.id ≠ id := by
        intro equal
        exact absent (List.mem_map.mpr ⟨head, List.mem_cons_self, equal⟩)
      have tailAbsent : id ∉ tail.map Goal.id := by
        intro member
        exact absent (List.mem_cons_of_mem _ member)
      simp only [charge, List.map_cons, chargeGoal, different, ↓reduceIte]
      exact congrArg (head :: ·) (ih tailAbsent)

theorem charge_exactly_one_account (goals : List Goal) (chosen : Goal) (units : Nat)
    (unique : UniqueIds goals) (member : chosen ∈ goals) :
    totalService (charge chosen.id units goals) = totalService goals + units := by
  induction goals with
  | nil => simp at member
  | cons head tail ih =>
      obtain ⟨absent, tailUnique⟩ := List.nodup_cons.mp unique
      rcases List.mem_cons.mp member with equal | member
      · subst head
        have tailSame := charge_absent tail chosen.id units absent
        have headCharged : chargeGoal chosen.id units chosen =
            { chosen with service := chosen.service + units } := by simp [chargeGoal]
        change (chargeGoal chosen.id units chosen).service + totalService (charge chosen.id units tail) =
          chosen.service + totalService tail + units
        rw [headCharged, tailSame]
        exact Nat.add_right_comm _ _ _
      · have different : head.id ≠ chosen.id := by
          intro equal
          exact absent (List.mem_map.mpr ⟨chosen, member, equal.symm⟩)
        have unchanged : chargeGoal chosen.id units head = head := by simp [chargeGoal, different]
        simp only [charge, List.map_cons, List.sum_cons, totalService, unchanged]
        have tailSum := ih tailUnique member
        change totalService (charge chosen.id units tail) = totalService tail + units at tailSum
        simp only [totalService, charge] at tailSum
        rw [tailSum]
        omega

theorem charge_preserves_runnable (goals : List Goal) (id units : Nat)
    (available : ∀ goal ∈ goals, runnable goal = true) :
    ∀ goal ∈ charge id units goals, runnable goal = true := by
  intro goal member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  rw [(charge_preserves_goal_meaning id units original).2.2.2.2.2]
  exact available original originalMember

theorem selected_charge_preserves_proportional_bound
    (goals : List Goal) (chosen : Goal) (units quantum : Nat)
    (unique : UniqueIds goals) (available : ∀ goal ∈ goals, runnable goal = true)
    (selected : select goals = some chosen) (bounded : units ≤ quantum)
    (before : WithinQuantum quantum goals) :
    WithinQuantum quantum (charge chosen.id units goals) := by
  obtain ⟨chosenMember, _, minimum⟩ := selection_contract goals chosen selected
  intro a ma b mb
  obtain ⟨a0, ma0, rfl⟩ := List.mem_map.mp ma
  obtain ⟨b0, mb0, rfl⟩ := List.mem_map.mp mb
  have bShare := (charge_preserves_goal_meaning chosen.id units b0).2.1
  have bLarger := Nat.mul_le_mul_right a0.share
    (charge_service_monotone chosen.id units b0)
  by_cases charged : a0.id = chosen.id
  · have same := unique_id_injective goals unique a0 ma0 chosen chosenMember charged
    have least := minimum b0 mb0 (available b0 mb0)
    have cost := Nat.mul_le_mul_right b0.share bounded
    subst a0
    have chargedGoal : chargeGoal chosen.id units chosen =
        { chosen with service := chosen.service + units } := by simp [chargeGoal]
    rw [chargedGoal, bShare]
    simp only [Nat.add_mul]
    unfold serviceLE at least
    omega
  · have unchanged : chargeGoal chosen.id units a0 = a0 := by simp [chargeGoal, charged]
    rw [unchanged, bShare]
    have old := before a0 ma0 b0 mb0
    omega

def allocate (units : Nat) (goals : List Goal) : List Goal :=
  match select goals with
  | none => goals
  | some goal => charge goal.id units goals

def run : List Nat → List Goal → List Goal
  | [], goals => goals
  | units :: rest, goals => run rest (allocate units goals)

theorem run_preserves_proportional_bound (costs : List Nat) (goals : List Goal) (quantum : Nat)
    (unique : UniqueIds goals) (available : ∀ goal ∈ goals, runnable goal = true)
    (bounded : ∀ units ∈ costs, units ≤ quantum) (before : WithinQuantum quantum goals) :
    WithinQuantum quantum (run costs goals) := by
  induction costs generalizing goals with
  | nil => exact before
  | cons units costs ih =>
      simp only [run]
      cases selected : select goals with
      | none =>
          simp only [allocate, selected]
          exact ih goals unique available (fun u h => bounded u (List.mem_cons_of_mem _ h)) before
      | some chosen =>
          simp only [allocate, selected]
          exact ih _ (charge_preserves_unique goals chosen.id units unique)
            (charge_preserves_runnable goals chosen.id units available)
            (fun u h => bounded u (List.mem_cons_of_mem _ h))
            (selected_charge_preserves_proportional_bound goals chosen units quantum
              unique available selected (bounded units List.mem_cons_self) before)

theorem zero_service_within_quantum (goals : List Goal) (quantum : Nat)
    (fresh : ∀ goal ∈ goals, goal.service = 0) : WithinQuantum quantum goals := by
  intro a ma b mb
  simp [fresh a ma, fresh b mb]

/-- A conservative repeat-service bound depending on shares and the largest
quantum, not on how long the system has been running. -/
def shareBudget (quantum : Nat) (target : Goal) : List Goal → Nat
  | [] => 0
  | goal :: goals => quantum * goal.share / target.share + 1 + shareBudget quantum target goals

theorem capacity_bounded_by_shares (target other : Goal) (quantum : Nat)
    (positive : 0 < target.share)
    (bounded : target.service * other.share ≤ other.service * target.share + quantum * other.share) :
    capacity target other ≤ quantum * other.share / target.share + 1 := by
  have quotient := Nat.div_le_div_right (c := target.share) bounded
  have exactDivision : (other.service * target.share + quantum * other.share) / target.share =
      other.service + quantum * other.share / target.share := by
    simpa only [Nat.mul_comm other.service target.share] using
      Nat.mul_add_div positive other.service (quantum * other.share)
  rw [exactDivision] at quotient
  have subtract (a b c : Nat) (h : a ≤ b + c) : a + 1 - b ≤ c + 1 := by omega
  exact subtract _ _ _ quotient

theorem waitBudget_bounded_by_shares (target : Goal) (goals : List Goal) (quantum : Nat)
    (positive : 0 < target.share)
    (bounded : ∀ other ∈ goals,
      target.service * other.share ≤ other.service * target.share + quantum * other.share) :
    waitBudget target goals ≤ shareBudget quantum target goals := by
  induction goals with
  | nil => rfl
  | cons goal goals ih =>
      exact Nat.add_le_add
        (capacity_bounded_by_shares target goal quantum positive (bounded goal List.mem_cons_self))
        (ih (fun other member => bounded other (List.mem_cons_of_mem _ member)))

theorem repeat_service_within_share_bound (goals : List Goal) (target : Goal) (quantum : Nat)
    (member : target ∈ goals) (available : runnable target = true)
    (balanced : WithinQuantum quantum goals) :
    target.id ∈ trace (shareBudget quantum target goals + 1) goals := by
  apply service_within_budget _ goals target member available
  have bound := waitBudget_bounded_by_shares target goals quantum
    ((runnable_contract target).mp available).2 (balanced target member)
  omega

end FairGoalScheduling
