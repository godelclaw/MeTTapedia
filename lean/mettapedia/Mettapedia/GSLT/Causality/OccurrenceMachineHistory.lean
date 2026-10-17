import Mettapedia.GSLT.Core.InferenceControl
import Mettapedia.GSLT.Core.InferenceRecordingPrefix
import Mettapedia.GSLT.Core.RouteTrace
import Mettapedia.OSLF.Syntax.RewriteEventHistoryForward
import Mettapedia.CategoryTheory.RunAccount
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Executable occurrence traces as event histories

Successor positions of a finite-branching machine are the generators of the
existing proof-relevant history category. Replaying their index lists agrees
with the machine's independently defined `follow` function. Equal endpoints
do not identify parallel occurrences.

Replay here fixes the machine and initial state. An index list alone does not
identify a source version, an external-service response, or a physical worker
schedule. These are separate requirements of a concrete replay interface.

`recordedMachine` keeps that base machine. Each expansion computes `base.next`
once and writes the successor position into the existing bounded prefix with
`Prefix.push`. `next` reads that prefix in order to write the successor
records. The base-state projection and the answer do not depend on it.
Successor order stays the base list order; a different schedule is not
assumed to agree.

Unrecorded execution is the base state and carries no prefix. Stopping retains
the prefix a run has already produced, with its original start and interval
endpoint, and continues from that base endpoint. It does not build a history.
Forgetting projects the prefix away. Restarting attaches a fresh bounded
prefix at the current base state and does not restore an earlier interval.
A complete prefix may be checked from its original start. The trace readout
does not consult the stored endpoint. The endpoint readout accepts only when
that replay is the stored state by exact equality, where that equality is
decidable. Stopping yields a plain diary pair: the original start, the
recorded prefix, and the base continuation. That pair is replay data. Exact
equality validates the endpoint the pair claims. It does not authenticate an
arbitrary supplied root, and it does not seal or authorize the diary. Exact
endpoint equality, storage lifetime, and current authority remain
independent. `ofTrace` is the optional history witness, and an omission does
not decode. Neither readout issues a live continuation or a one-shot token.
These are source observations. They are not `IndexedAuthority.transport`,
not `ResourceOwnership.framedHistoryRelease`, and not compiled-C
verification.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.OccurrenceMachineHistory

open _root_.CategoryTheory
open Mettapedia.Machines
open Mettapedia.GSLT.ProofRelevant
open Mettapedia.GSLT.Core.InferenceControl

open Mettapedia.OSLF.Binding

variable {Term State Answer : Type}
variable {V : Type} [Monoid V]

/-- The endpoint relation forgets only the successor position. -/
abbrev theory (machine : OccurrenceMachineCore Term State Answer) : GSLT where
  Term := State
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites source target := target ∈ machine.next source
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-- Two positions remain two events even when their successor states agree. -/
abbrev system (machine : OccurrenceMachineCore Term State Answer) : ProofRelevantGSLT where
  theory := theory machine
  steps := {
    Evidence := fun source target => {index : Nat // (machine.next source)[index]? = some target}
    erases_iff := by
      intro source target
      constructor
      · rintro ⟨⟨index, found⟩⟩
        exact List.mem_iff_getElem?.mpr ⟨index, found⟩
      · intro member
        obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
        exact ⟨⟨index, found⟩⟩ }

abbrev History (machine : OccurrenceMachineCore Term State Answer) (source target : State) :=
  RewriteEventHistory.History (system machine) ⟨source⟩ ⟨target⟩

/-- Read the ordered successor positions from the retained event path. -/
def indices (machine : OccurrenceMachineCore Term State Answer)
    {source target : RewriteEventHistory.State (system machine)} : RewriteEventHistory.History (system machine) source target → List Nat
  | .nil => []
  | .cons past event => indices machine past ++ [event.val]

@[simp] theorem indices_nil (machine : OccurrenceMachineCore Term State Answer)
    (source : RewriteEventHistory.State (system machine)) : indices machine (.nil : Quiver.Path source source) = [] := rfl

theorem indices_comp (machine : OccurrenceMachineCore Term State Answer)
    {source middle target : RewriteEventHistory.State (system machine)}
    (first : Quiver.Path source middle) (second : Quiver.Path middle target) :
    indices machine (first.comp second) = indices machine first ++ indices machine second := by
  induction second with
  | nil => simp [Quiver.Path.comp, indices]
  | cons past event ih => simp [Quiver.Path.comp, indices, ih, List.append_assoc]

/-- Every retained event path is accepted by the executable replay function. -/
theorem follow_indices (machine : OccurrenceMachineCore Term State Answer)
    {source target : RewriteEventHistory.State (system machine)}
    (history : RewriteEventHistory.History (system machine) source target) :
    machine.follow source.term (indices machine history) = some target.term := by
  induction history with
  | nil => rfl
  | cons past event ih =>
      rw [indices, WorkOccurrence.follow_append, ih]
      simp [OccurrenceMachineCore.follow, event.property]

/-- Construct a history only after every selected successor position exists.
No answer-value equality is used to select or merge events. -/
def ofTrace (machine : OccurrenceMachineCore Term State Answer) :
    {source target : State} → (trace : List Nat) →
      machine.follow source trace = some target → History machine source target
  | source, target, [], accepted => by
      have equal : source = target := Option.some.inj accepted
      subst target
      exact .nil
  | source, target, index :: rest, accepted =>
      match found : (machine.next source)[index]? with
      | none => by simp [OccurrenceMachineCore.follow, found] at accepted
      | some middle =>
          (Quiver.Hom.toPath (⟨index, found⟩ :
            (⟨source⟩ : RewriteEventHistory.State (system machine)) ⟶ ⟨middle⟩)).comp
              (ofTrace machine rest (by
                simpa [OccurrenceMachineCore.follow, found] using accepted))

/-- Validation and construction preserve the exact occurrence list. -/
theorem indices_ofTrace (machine : OccurrenceMachineCore Term State Answer)
    {source target : State} (trace : List Nat)
    (accepted : machine.follow source trace = some target) :
    indices machine (ofTrace machine trace accepted) = trace := by
  induction trace generalizing source with
  | nil =>
      have equal : source = target := Option.some.inj accepted
      subst target
      rfl
  | cons index rest ih =>
      simp only [ofTrace]
      split
      · next found => simp [OccurrenceMachineCore.follow, found] at accepted
      · rw [indices_comp, ih]
        rfl

/-- The constructed history does not depend on which acceptance proof is supplied. -/
private theorem ofTrace_proof_irrel (machine : OccurrenceMachineCore Term State Answer)
    {source target : State} (trace : List Nat)
    (left right : machine.follow source trace = some target) :
    ofTrace machine trace left = ofTrace machine trace right := rfl

private theorem ofTrace_cons (machine : OccurrenceMachineCore Term State Answer)
    {source target middle : State} (index : Nat) (rest : List Nat)
    (found : (machine.next source)[index]? = some middle)
    (accepted : machine.follow source (index :: rest) = some target) :
    ofTrace machine (index :: rest) accepted =
      (Quiver.Hom.toPath (⟨index, found⟩ :
        (⟨source⟩ : RewriteEventHistory.State (system machine)) ⟶ ⟨middle⟩)).comp
        (ofTrace machine rest (by
          simp [OccurrenceMachineCore.follow, found] at accepted
          exact accepted)) := by
  rw [ofTrace_proof_irrel machine rest _
    (by simpa [OccurrenceMachineCore.follow, found] using accepted)]
  simp only [ofTrace]
  split
  · next bad =>
    rw [bad] at found
    cases found
  · next middle' found' =>
    obtain rfl := Option.some.inj (found.symm.trans found')
    congr 1

private theorem ofTrace_nil (machine : OccurrenceMachineCore Term State Answer)
    {source : State} (accepted : machine.follow source [] = some source) :
    ofTrace machine [] accepted =
      (Quiver.Path.nil : History machine source source) := by
  simp only [ofTrace]

/-- Two accepted index paths compose to the accepted concatenated path. -/
theorem accepted_append (machine : OccurrenceMachineCore Term State Answer)
    {source middle target : State} (first second : List Nat)
    (acceptedFirst : machine.follow source first = some middle)
    (acceptedSecond : machine.follow middle second = some target) :
    machine.follow source (first ++ second) = some target := by
  rw [WorkOccurrence.follow_append, acceptedFirst]
  exact acceptedSecond

/-- Concatenating accepted index paths concatenates the constructed histories. -/
theorem ofTrace_append (machine : OccurrenceMachineCore Term State Answer)
    {source middle target : State} (first second : List Nat)
    (acceptedFirst : machine.follow source first = some middle)
    (acceptedSecond : machine.follow middle second = some target) :
    ofTrace machine (first ++ second)
        (accepted_append machine first second acceptedFirst acceptedSecond) =
      (ofTrace machine first acceptedFirst).comp
        (ofTrace machine second acceptedSecond) := by
  induction first generalizing source middle with
  | nil =>
    obtain rfl := Option.some.inj acceptedFirst
    rw [ofTrace_nil machine acceptedFirst, Quiver.Path.nil_comp]
    exact ofTrace_proof_irrel machine second _ _
  | cons index rest ih =>
    cases found : (machine.next source)[index]? with
    | none => simp [OccurrenceMachineCore.follow, found] at acceptedFirst
    | some next =>
      have acceptedRest : machine.follow next rest = some middle := by
        simpa [OccurrenceMachineCore.follow, found] using acceptedFirst
      simp only [List.cons_append]
      rw [ofTrace_cons machine index (rest ++ second) found
          (accepted_append machine (index :: rest) second acceptedFirst acceptedSecond),
        ofTrace_cons machine index rest found acceptedFirst,
        Quiver.Path.comp_assoc]
      congr 1
      rw [ofTrace_proof_irrel machine (rest ++ second) _
        (accepted_append machine rest second acceptedRest acceptedSecond)]
      exact ih acceptedRest acceptedSecond

/-- One accepted index is that occurrence, not merely its endpoint. -/
private theorem ofTrace_singleton (machine : OccurrenceMachineCore Term State Answer)
    {source target : State} (index : Nat)
    (found : (machine.next source)[index]? = some target)
    (accepted : machine.follow source [index] = some target) :
    ofTrace machine [index] accepted =
      (Quiver.Hom.toPath (⟨index, found⟩ :
        (⟨source⟩ : RewriteEventHistory.State (system machine)) ⟶ ⟨target⟩)) := by
  rw [ofTrace_cons machine index [] found accepted]
  rw [ofTrace_proof_irrel machine [] _ (by rfl)]
  rw [ofTrace_nil machine (by rfl)]
  exact Quiver.Path.comp_nil _

/-- The occurrence indices of a history reconstruct that history.
Duplicate indices stay duplicate events: agreement of the endpoints is not the inverse. -/
theorem ofTrace_indices (machine : OccurrenceMachineCore Term State Answer)
    {source target : RewriteEventHistory.State (system machine)}
    (history : Quiver.Path source target) :
    ofTrace machine (indices machine history) (follow_indices machine history) = history := by
  induction history with
  | nil =>
    simp only [indices_nil]
    rw [ofTrace_proof_irrel machine [] _ (by rfl)]
    exact ofTrace_nil machine (by rfl)
  | @cons middle after past event ih =>
    have step : machine.follow middle.term [event.val] = some after.term := by
      simp only [OccurrenceMachineCore.follow, event.property]
      rfl
    have indicesSplit : indices machine (past.cons event) =
        indices machine past ++ [event.val] := rfl
    simp only [indicesSplit]
    rw [ofTrace_proof_irrel machine (indices machine past ++ [event.val]) _
        (accepted_append machine (indices machine past) [event.val]
          (follow_indices machine past) step)]
    rw [ofTrace_append machine (indices machine past) [event.val]
        (follow_indices machine past) step]
    rw [ih, ofTrace_singleton machine event.val event.property step,
      Quiver.Path.comp_toPath_eq_cons]
    exact congrArg (fun edge => past.cons edge) (Subtype.eta event _)

/-- Moving the endpoint does not change the constructed history. -/
private theorem ofTrace_target_heq (machine : OccurrenceMachineCore Term State Answer)
    {source target target' : State} (trace : List Nat)
    (accepted : machine.follow source trace = some target)
    (accepted' : machine.follow source trace = some target')
    (sameTarget : target = target') :
    HEq (ofTrace machine trace accepted) (ofTrace machine trace accepted') :=
  Eq.rec
    (motive := fun state _ =>
      ∀ accepted' : machine.follow source trace = some state,
        HEq (ofTrace machine trace accepted) (ofTrace machine trace accepted'))
    (fun accepted' => heq_of_eq (ofTrace_proof_irrel machine trace accepted accepted'))
    sameTarget
    accepted'

/-- Concatenation is path composition for whichever proof accepts the concatenated indices.
An existing endpoint equation may change the codomain; it does not choose the path. -/
theorem ofTrace_append_eq (machine : OccurrenceMachineCore Term State Answer)
    {source middle target target' : State} (first second : List Nat)
    (acceptedFirst : machine.follow source first = some middle)
    (acceptedSecond : machine.follow middle second = some target)
    (trace : List Nat)
    (accepted : machine.follow source trace = some target')
    (sameTrace : trace = first ++ second)
    (sameTarget : target = target') :
    HEq (ofTrace machine trace accepted)
      ((ofTrace machine first acceptedFirst).comp
        (ofTrace machine second acceptedSecond)) := by
  cases sameTrace
  exact (ofTrace_target_heq machine (first ++ second) accepted
      (accepted_append machine first second acceptedFirst acceptedSecond) sameTarget.symm).trans
    (heq_of_eq (ofTrace_append machine first second acceptedFirst acceptedSecond))

/-- A supplied trace denotes exactly a history with those occurrences. -/
theorem follow_iff_history (machine : OccurrenceMachineCore Term State Answer)
    {source target : State} (trace : List Nat) :
    machine.follow source trace = some target ↔
      ∃ history : History machine source target, indices machine history = trace := by
  constructor
  · intro accepted
    exact ⟨ofTrace machine trace accepted, indices_ofTrace machine trace accepted⟩
  · rintro ⟨history, equal⟩
    rw [← equal]
    exact follow_indices machine history

/-- The replay certificate is relative to its starting state. -/
theorem replay_endpoint_unique (machine : OccurrenceMachineCore Term State Answer)
    {source first second : State} {trace : List Nat}
    (one : machine.follow source trace = some first)
    (two : machine.follow source trace = some second) : first = second :=
  Option.some.inj (one.symm.trans two)

/-- A machine state as an object of the free history category.
The path-category instance is `categoryPaths` on this synonym. -/
def historyVertex (machine : OccurrenceMachineCore Term State Answer) (state : State) :
    RewriteEventHistory.HistoryCategory (system machine) :=
  ⟨state⟩

/-- A retained history is that path in the free history category.
Its root is the path category, and its right object is the current endpoint. -/
def retained (machine : OccurrenceMachineCore Term State Answer)
    {source target : State} (history : History machine source target) :
    Under (historyVertex machine source) :=
  Under.mk (Y := historyVertex machine target) history

theorem retained_right (machine : OccurrenceMachineCore Term State Answer)
    {source target : State} (history : History machine source target) :
    (retained machine history).right = historyVertex machine target :=
  Under.mk_right history

/-- Forgetting projects the retained endpoint. It does not replay the path. -/
theorem retained_forgets (machine : OccurrenceMachineCore Term State Answer)
    {source target : State} (history : History machine source target) :
    (Under.forget (historyVertex machine source)).obj (retained machine history) =
      (retained machine history).right :=
  rfl

/-- A later diary is rooted at the retained endpoint and contains only its own
path. Remembering a prefix that is still in hand is precomposition by `Under.map`.
The endpoint projection does not store that prefix. -/
theorem retained_suffix (machine : OccurrenceMachineCore Term State Answer)
    {source target later : State}
    (past : History machine source target)
    (suffix : History machine target later) :
    (Under.forget (historyVertex machine source)).obj (retained machine past) =
        historyVertex machine target ∧
      (retained machine suffix).hom = suffix ∧
      ((Under.map past).obj (retained machine suffix)).hom =
        past ≫ (retained machine suffix).hom ∧
      ((Under.map past).obj (retained machine suffix)).right =
        (retained machine suffix).right := by
  refine ⟨?_, rfl, Under.map_obj_hom, Under.map_obj_right⟩
  rw [retained_forgets, retained_right]

/-- Post a retained diary along an existing path-valued realization.
The posted hom is the implementing history, and the posted endpoint is the
image of the source endpoint. -/
theorem retained_posted
    {Target : ProofRelevantGSLT}
    (machine : OccurrenceMachineCore Term State Answer)
    (realization : RewriteEventHistory.PathEvidenceMap (system machine) Target)
    {source targetState : State} (history : History machine source targetState) :
    ((Under.post realization.histories).obj (retained machine history)).hom =
        realization.histories.map history ∧
      ((Under.post realization.histories).obj (retained machine history)).right =
        realization.histories.obj (historyVertex machine targetState) :=
  ⟨rfl, congrArg realization.histories.obj (retained_right machine history)⟩

/-- Forgetting after transport applies the realization to the forgotten
source endpoint. The transported diary does not select another target state. -/
theorem retained_posted_forgets
    {Target : ProofRelevantGSLT}
    (machine : OccurrenceMachineCore Term State Answer)
    (realization : RewriteEventHistory.PathEvidenceMap (system machine) Target)
    {source targetState : State} (history : History machine source targetState) :
    (Under.forget (realization.histories.obj (historyVertex machine source))).obj
        ((Under.post realization.histories).obj (retained machine history)) =
      realization.histories.obj
        ((Under.forget (historyVertex machine source)).obj (retained machine history)) ∧
      (Under.forget (realization.histories.obj (historyVertex machine source))).obj
        ((Under.post realization.histories).obj (retained machine history)) =
      realization.histories.obj (historyVertex machine targetState) :=
  ⟨rfl, congrArg realization.histories.obj (retained_right machine history)⟩

/-- Posting a known source suffix agrees with precomposing its implementing
image. Successive realizations compose by `PathEvidenceMap.histories_comp`
and `Under.post_comp`. -/
theorem retained_posted_suffix
    {Target : ProofRelevantGSLT}
    (machine : OccurrenceMachineCore Term State Answer)
    (realization : RewriteEventHistory.PathEvidenceMap (system machine) Target)
    {source targetState later : State}
    (past : History machine source targetState)
    (suffix : History machine targetState later) :
    ((Under.post realization.histories).obj
        ((Under.map past).obj (retained machine suffix))).hom =
      ((Under.map (realization.histories.map past)).obj
        ((Under.post realization.histories).obj (retained machine suffix))).hom ∧
      ((Under.post realization.histories).obj
        ((Under.map past).obj (retained machine suffix))).right =
        ((Under.post realization.histories).obj (retained machine suffix)).right :=
  ⟨realization.histories.map_comp past suffix, rfl⟩

/-- The account of a transported diary is the declared image of the source
account. Transport does not introduce a charge of its own. -/
theorem retained_posted_account
    {Target : ProofRelevantGSLT} {M N : Type} [Monoid M] [Monoid N]
    (machine : OccurrenceMachineCore Term State Answer)
    (realization : RewriteEventHistory.PathEvidenceMap (system machine) Target)
    (sourceAccount : Mettapedia.Effects.RunAccount
      (RewriteEventHistory.HistoryCategory (system machine)) M)
    (targetAccount : Mettapedia.Effects.RunAccount
      (RewriteEventHistory.HistoryCategory Target) N)
    (change : M →* N)
    (preserved : targetAccount.comap realization.histories = sourceAccount.map change)
    {source targetState : State} (history : History machine source targetState) :
    targetAccount.of
        ((Under.post realization.histories).obj (retained machine history)).hom =
      change (sourceAccount.of history) :=
  congrArg (fun account => account.of history) preserved

/-- Interpret each real event in a monoid, keeping chronological multiplication.
This uses the existing free history category and run-account interface. -/
def eventAccount (machine : OccurrenceMachineCore Term State Answer)
    (value : State → State → Nat → V) :
    Mettapedia.Effects.RunAccount (RewriteEventHistory.HistoryCategory (system machine)) V :=
  Mettapedia.Effects.RunAccount.ofFunctor
    (RewriteEventHistory.interpret (system machine) {
      obj _ := SingleObj.star Vᵐᵒᵖ
      map {source target} event := MulOpposite.op (value source.term target.term event.val) })

/-- A one-event account is the supplied value of that occurrence. -/
theorem eventAccount_generator (machine : OccurrenceMachineCore Term State Answer)
    (value : State → State → Nat → V)
    {source target : RewriteEventHistory.State (system machine)} (event : source ⟶ target) :
    (eventAccount machine value).of event.toPath = value source.term target.term event.val := by
  dsimp only [eventAccount, Mettapedia.Effects.RunAccount.ofFunctor]
  rw [RewriteEventHistory.interpret_generator]
  rfl

/-- Extending a history multiplies by the new event on the right. -/
theorem eventAccount_cons (machine : OccurrenceMachineCore Term State Answer)
    (value : State → State → Nat → V)
    {source middle target : RewriteEventHistory.State (system machine)}
    (history : Quiver.Path source middle) (event : middle ⟶ target) :
    (eventAccount machine value).of (history.cons event) =
      (eventAccount machine value).of history * value middle.term target.term event.val := by
  calc
    _ = (eventAccount machine value).of history *
        (eventAccount machine value).of event.toPath :=
      (eventAccount machine value).of_comp history event.toPath
    _ = _ := by rw [eventAccount_generator]

/-- Monotonicity on real primitive edges extends along every history. -/
theorem potential_path_le (machine : OccurrenceMachineCore Term State Answer)
    (potential : State → Nat)
    (mono : ∀ (before after : State) (index : Nat),
      (machine.next before)[index]? = some after → potential before ≤ potential after)
    {source target : RewriteEventHistory.State (system machine)}
    (history : Quiver.Path source target) :
    potential source.term ≤ potential target.term := by
  induction history with
  | nil => exact Nat.le_refl _
  | @cons _middle _after past event ih =>
      exact Nat.le_trans ih (mono _ _ event.val event.property)

/-- Each real edge is charged by the potential difference of its own states.
Those local charges multiply to the potential difference of the path's
endpoints. Edge monotonicity is the hypothesis; the endpoint equality is
derived from it. -/
theorem potential_path_account (machine : OccurrenceMachineCore Term State Answer)
    (potential : State → Nat)
    (value : State → State → Nat → Multiplicative Nat)
    (charges : ∀ (before after : State) (index : Nat),
      value before after index =
        Multiplicative.ofAdd (potential after - potential before))
    (mono : ∀ (before after : State) (index : Nat),
      (machine.next before)[index]? = some after → potential before ≤ potential after)
    {source target : RewriteEventHistory.State (system machine)}
    (history : Quiver.Path source target) :
    (eventAccount machine value).of history =
      Multiplicative.ofAdd (potential target.term - potential source.term) := by
  induction history with
  | nil =>
      rw [Nat.sub_self, ofAdd_zero]
      rfl
  | @cons middle after past event ih =>
      rw [eventAccount_cons, ih, charges middle.term after.term event.val]
      have earlier := potential_path_le machine potential mono past
      have later := mono middle.term after.term event.val event.property
      rw [← ofAdd_add]
      apply congrArg Multiplicative.ofAdd
      omega

/-- Changing the account algebra commutes with interpreting a history.
The homomorphism must preserve ordered multiplication, not just final values. -/
theorem eventAccount_map {W : Type} [Monoid W]
    (machine : OccurrenceMachineCore Term State Answer)
    (value : State → State → Nat → V) (change : V →* W) :
    (eventAccount machine value).map change =
      eventAccount machine (fun before after index => change (value before after index)) := by
  apply Mettapedia.Effects.RunAccount.ext
  funext source target history
  change change ((eventAccount machine value).of history) = _
  induction history with
  | nil => exact change.map_one
  | cons past event ih =>
      erw [eventAccount_cons, change.map_mul, ih, eventAccount_cons]

open Mettapedia.GSLT.Ultrainfinite.Route

/-- A history realizes its declared observations while retaining the count
of every underlying machine step, including steps with no visible event. -/
theorem history_observed_trace {Event : Type}
    (machine : OccurrenceMachineCore Term State Answer)
    (observe : State → State → Nat → List Event)
    {source target : RewriteEventHistory.State (system machine)}
    (history : Quiver.Path source target) :
    ObservedTrace (Step := (system machine).steps.Evidence)
      (fun {before after} event => observe before after event.val)
      (indices machine history).length source.term target.term
      (FreeMonoid.toList ((eventAccount machine
        (fun before after index => FreeMonoid.ofList (observe before after index))).of history)) := by
  induction history with
  | nil => exact .refl _
  | @cons middle after past event ih =>
      have last : ObservedTrace (Step := (system machine).steps.Evidence)
          (fun {before after} event => observe before after event.val)
          1 middle.term after.term (observe middle.term after.term event.val) := by
        simpa using ObservedTrace.cons
          (Step := (system machine).steps.Evidence)
          (observe := fun {before after} event => observe before after event.val)
          (edge := ⟨event.val, event.property⟩) (ObservedTrace.refl after.term)
      have joined := ObservedTrace.comp _ ih last
      simpa only [indices, List.length_append, List.length_singleton,
        eventAccount_cons, FreeMonoid.toList_mul, FreeMonoid.toList_ofList] using joined

/-- Every trace of actual step evidence is covered by a history. The event
observation need not identify that history uniquely. -/
theorem observed_trace_history {Event : Type}
    (machine : OccurrenceMachineCore Term State Answer)
    (observe : State → State → Nat → List Event)
    {count : Nat} {source target : State} {observations : List Event}
    (admitted : ObservedTrace (Step := (system machine).steps.Evidence)
      (fun {before after} event => observe before after event.val)
      count source target observations) :
    ∃ history : History machine source target,
      (indices machine history).length = count ∧
      FreeMonoid.toList ((eventAccount machine
        (fun before after index => FreeMonoid.ofList (observe before after index))).of history) =
          observations := by
  induction admitted with
  | refl state => exact ⟨.nil, rfl, rfl⟩
  | @cons count before middle after observations edge rest ih =>
      obtain ⟨history, length, events⟩ := ih
      let event : (⟨before⟩ : RewriteEventHistory.State (system machine)) ⟶ ⟨middle⟩ := edge
      refine ⟨event.toPath.comp history, ?_, ?_⟩
      · rw [indices_comp]
        change ([edge.val] ++ indices machine history).length = _
        simp [length]
      · change FreeMonoid.toList
          ((eventAccount machine
            (fun before after index => FreeMonoid.ofList (observe before after index))).of
              (event.toPath ≫ history)) = _
        erw [Mettapedia.Effects.RunAccount.of_comp, FreeMonoid.toList_mul, events]
        rw [eventAccount_generator]
        rfl

/-- The ordered trace is an instance of the shared compositional run account.
Its multiplication is concatenation, with no exchange law. -/
def traceAccount (machine : OccurrenceMachineCore Term State Answer) :
    Mettapedia.Effects.RunAccount
      (RewriteEventHistory.HistoryCategory (system machine)) (FreeMonoid Nat) where
  of history := FreeMonoid.ofList (indices machine history)
  of_id _ := rfl
  of_comp first second := indices_comp machine first second

/-- Recording successor indices is the free-monoid instance of event accounting. -/
theorem eventAccount_trace (machine : OccurrenceMachineCore Term State Answer) :
    eventAccount machine (fun _ _ index => FreeMonoid.of index) = traceAccount machine := by
  apply Mettapedia.Effects.RunAccount.ext
  funext source target history
  induction history with
  | nil => rfl
  | cons past event ih =>
      erw [eventAccount_cons, ih]
      rfl

/-- Base state plus the bounded prefix of successor positions taken so far.
Capacity lives in the prefix. Zero remaining capacity is still this state. -/
structure RecordedState (baseState : Type) where
  base : baseState
  record : Recording.Prefix Nat

/-- One expansion charges every current successor position into its own
prefix. `base.next` is read once. `Prefix.push` demands the position only
while storage remains. The base machine is unchanged. -/
def recordedMachine (machine : OccurrenceMachineCore Term State Answer) :
    OccurrenceMachineCore (Term × Nat) (RecordedState State) Answer where
  load
    | (term, capacity) => ⟨machine.load term, Recording.Prefix.initial capacity⟩
  next state :=
    (machine.next state.base).zipIdx.map fun (target, index) =>
      ⟨target, state.record.push (fun () => index)⟩
  answer state := machine.answer state.base
  answer_final := by
    intro state value observed
    have closed : machine.next state.base = [] :=
      machine.answer_final state.base value observed
    simp [closed, List.zipIdx_nil]

/-- The position stored at a successor is that successor's own index. -/
theorem recordedMachine_next_getElem?
    (machine : OccurrenceMachineCore Term State Answer)
    (state : RecordedState State) (index : Nat) :
    ((recordedMachine machine).next state)[index]? =
      (machine.next state.base)[index]?.map fun target =>
        ⟨target, state.record.push (fun () => index)⟩ := by
  simp only [recordedMachine, List.getElem?_map, List.getElem?_zipIdx, Nat.zero_add,
    Option.map_map]
  cases (machine.next state.base)[index]? <;> rfl

/-- Forgetting every recorded successor restores the base successor list,
including its order and duplicate states. -/
theorem recordedMachine_next_base
    (machine : OccurrenceMachineCore Term State Answer)
    (state : RecordedState State) :
    ((recordedMachine machine).next state).map (·.base) = machine.next state.base := by
  apply List.ext_getElem?
  intro index
  simp only [List.getElem?_map, recordedMachine_next_getElem?]
  cases (machine.next state.base)[index]? <;> rfl

/-- A single live successor is recorded at position `0` during that expansion. -/
theorem recordedMachine_head
    (machine : OccurrenceMachineCore Term State Answer)
    (state : RecordedState State) (target : State)
    (only : machine.next state.base = [target]) :
    (recordedMachine machine).next state =
      [⟨target, state.record.push (fun () => 0)⟩] := by
  simp [recordedMachine, only, List.zipIdx_cons, List.zipIdx_nil]

private theorem push_index_ne (record : Recording.Prefix Nat)
    {i j : Nat} (distinct : i ≠ j) (room : record.remaining ≠ 0) :
    record.push (fun () => i) ≠ record.push (fun () => j) := by
  cases record with
  | mk _reversed remaining _omitted =>
    cases remaining with
    | zero => exact absurd rfl room
    | succ _left =>
        intro same
        have heads := congrArg Recording.Prefix.reversed same
        simp [Recording.Prefix.push] at heads
        exact distinct heads

/-- While storage remains, two positions of one successor state stay two
recorded occurrences. Exhausting capacity drops the stored positions and
does not remove either successor from `next`. -/
theorem recordedMachine_duplicate_positions
    (machine : OccurrenceMachineCore Term State Answer)
    (state : RecordedState State) (i j : Nat) (target : State)
    (left : (machine.next state.base)[i]? = some target)
    (right : (machine.next state.base)[j]? = some target)
    (distinct : i ≠ j) (room : state.record.remaining ≠ 0) :
    ((recordedMachine machine).next state)[i]? ≠
      ((recordedMachine machine).next state)[j]? := by
  rw [recordedMachine_next_getElem?, recordedMachine_next_getElem?, left, right]
  simp only [Option.map_some, ne_eq, Option.some.injEq]
  intro same
  exact push_index_ne state.record distinct room (congrArg RecordedState.record same)

/-- Projecting `next` to base states, and reading `answer`, does not depend on
the prefix. `next` itself reads the prefix when it writes each successor
record. This is observer noninterference for the base projection and the
answer. It is not an authority or capability judgment. -/
theorem recordedMachine_ignores_record
    (machine : OccurrenceMachineCore Term State Answer)
    (base : State) (left right : Recording.Prefix Nat) :
    ((recordedMachine machine).next ⟨base, left⟩).map (·.base) =
      ((recordedMachine machine).next ⟨base, right⟩).map (·.base) ∧
      (recordedMachine machine).answer ⟨base, left⟩ =
        (recordedMachine machine).answer ⟨base, right⟩ := by
  constructor
  · simp [recordedMachine_next_base]
  · rfl

theorem recordedMachine_answer
    (machine : OccurrenceMachineCore Term State Answer)
    (state : RecordedState State) :
    (recordedMachine machine).answer state = machine.answer state.base :=
  rfl

/-- Following selected positions projects to the base endpoint and appends
those positions, omissions included, in order. -/
theorem recordedMachine_follow
    (machine : OccurrenceMachineCore Term State Answer)
    (start : State) (record : Recording.Prefix Nat) (trace : List Nat) :
    (recordedMachine machine).follow ⟨start, record⟩ trace =
      (machine.follow start trace).map fun target =>
        ⟨target, record.append trace⟩ := by
  induction trace generalizing start record with
  | nil => simp [OccurrenceMachineCore.follow, Recording.Prefix.append]
  | cons index rest ih =>
      cases found : (machine.next start)[index]? with
      | none =>
          simp [OccurrenceMachineCore.follow, recordedMachine_next_getElem?, found]
      | some middle =>
          have later := ih middle (record.push (fun () => index))
          simp only [OccurrenceMachineCore.follow, recordedMachine_next_getElem?, found,
            Option.map_some]
          change (some ⟨middle, record.push (fun () => index)⟩).bind
              (fun done => (recordedMachine machine).follow done rest) =
            Option.map (fun done => ⟨done, record.append (index :: rest)⟩)
              ((some middle).bind fun next => machine.follow next rest)
          rw [Option.bind_some, Option.bind_some, later]
          simp [Recording.Prefix.append]

/-- Forgetting the recorded run leaves the base machine's selected endpoint. -/
theorem recordedMachine_forget
    (machine : OccurrenceMachineCore Term State Answer)
    (start : State) (record : Recording.Prefix Nat) (trace : List Nat) :
    ((recordedMachine machine).follow ⟨start, record⟩ trace).map (·.base) =
      machine.follow start trace := by
  rw [recordedMachine_follow]
  cases machine.follow start trace <;> rfl

/-- Loading at capacity zero is still a recorder. Its state is the base
load paired with an empty prefix, not the base machine. -/
theorem recordedMachine_zero_load
    (machine : OccurrenceMachineCore Term State Answer) (term : Term) :
    (recordedMachine machine).load (term, 0) =
      ⟨machine.load term, Recording.Prefix.initial 0⟩ :=
  rfl

/-- A zero-capacity run keeps the base endpoint, retains no positions, and
counts every selected position as an omission. Replay from the original
start succeeds only for the empty trace. -/
theorem recordedMachine_zero
    (machine : OccurrenceMachineCore Term State Answer)
    (start : State) (trace : List Nat) (target : State)
    (accepted : machine.follow start trace = some target) :
    (recordedMachine machine).follow ⟨start, Recording.Prefix.initial 0⟩ trace =
      some ⟨target, (Recording.Prefix.initial 0).append trace⟩ ∧
    ((Recording.Prefix.initial 0).append trace).items = [] ∧
    ((Recording.Prefix.initial 0).append trace).omitted = trace.length ∧
    (((Recording.Prefix.initial 0).append trace).complete?.bind (machine.follow start) =
      some target ↔ trace = []) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [accepted] using
      recordedMachine_follow machine start (Recording.Prefix.initial 0) trace
  · simpa using Recording.Prefix.initial_items 0 trace
  · simpa using Recording.Prefix.initial_omitted 0 trace
  · rw [Recording.Prefix.complete_bind_iff]
    simp only [accepted, and_true, Nat.le_zero, List.length_eq_zero_iff]

/-- A complete prefix replays by `follow` from the original base state.
An omission leaves that checker unconsulted. -/
theorem recordedMachine_replay
    (machine : OccurrenceMachineCore Term State Answer)
    (start : State) (capacity : Nat) (trace : List Nat) (target : State) :
    ((recordedMachine machine).follow ⟨start, Recording.Prefix.initial capacity⟩ trace).bind
        (fun finished => finished.record.complete?.bind (machine.follow start)) =
      some target ↔
      trace.length ≤ capacity ∧ machine.follow start trace = some target := by
  rw [recordedMachine_follow]
  cases followed : machine.follow start trace with
  | none =>
      simp only [Option.map_none, Option.bind_none]
      constructor
      · intro h
        cases h
      · intro h
        cases h.2
  | some _reached =>
      simp only [Option.map_some, Option.bind_some]
      have key := Recording.Prefix.complete_bind_iff
        (machine.follow start) capacity trace target
      rwa [followed] at key

/-- The local charge is the base potential difference. Omission changes only
the prefix, so every real recorded history has that same endpoint account. -/
def recordedEdge (potential : State → Nat)
    (before after : RecordedState State) (_index : Nat) : Multiplicative Nat :=
  Multiplicative.ofAdd (potential after.base - potential before.base)

theorem recordedMachine_account
    (machine : OccurrenceMachineCore Term State Answer)
    (potential : State → Nat)
    (mono : ∀ (before after : State) (index : Nat),
      (machine.next before)[index]? = some after → potential before ≤ potential after)
    {source target : RewriteEventHistory.State (system (recordedMachine machine))}
    (history : Quiver.Path source target) :
    (eventAccount (recordedMachine machine) (recordedEdge potential)).of history =
      Multiplicative.ofAdd (potential target.term.base - potential source.term.base) := by
  refine potential_path_account (recordedMachine machine) (fun state => potential state.base)
      (recordedEdge potential) (fun _before _after _index => rfl)
      (fun before after index found => ?_) history
  rw [recordedMachine_next_getElem?] at found
  cases baseLookup : (machine.next before.base)[index]? with
  | none => simp [baseLookup] at found
  | some baseTarget =>
      simp only [baseLookup, Option.map_some, Option.some.injEq] at found
      cases found
      exact mono before.base baseTarget index baseLookup

/-- Drop the prefix. The base state stays. This is not physical reclamation
of storage shared with another owner, and it grants no step authority. -/
def forgetRecording (state : RecordedState State) : State :=
  state.base

/-- Retain the prefix `finished` already holds, with the original `start`
and that interval's endpoint. The second component is the base continuation
and carries no prefix. This reads no trace, builds no history, and does not
choose a future length. -/
def stopRecording (start : State) (finished : RecordedState State) :
    (State × RecordedState State) × State :=
  ((start, finished), forgetRecording finished)

/-- An accepted recorded run agrees with the stopped diary. The diary is
replay data: the original start, the retained prefix, and the base
continuation. The base `follow` reaches that continuation, and the retained
prefix is the bounded append, omissions included. The acceptance proof is
not stored. Exact endpoint equality does not authenticate the supplied
start. -/
theorem stopRecording_projects
    (machine : OccurrenceMachineCore Term State Answer)
    (start : State) (opened : Recording.Prefix Nat) (trace : List Nat)
    (finished : RecordedState State)
    (accepted : (recordedMachine machine).follow ⟨start, opened⟩ trace = some finished) :
    machine.follow start trace = some (stopRecording start finished).2 ∧
      (stopRecording start finished).1.2.record = opened.append trace ∧
      (stopRecording start finished).1.1 = start := by
  have projected := accepted
  rw [recordedMachine_follow] at projected
  cases baseFollow : machine.follow start trace with
  | none =>
      simp only [baseFollow, Option.map_none] at projected
      cases projected
  | some target =>
      rw [baseFollow] at projected
      simp only [Option.map_some, Option.some.injEq] at projected
      subst projected
      refine ⟨?_, ?_, ?_⟩
      · rw [stopRecording, forgetRecording]
      · rw [stopRecording]
      · rw [stopRecording]

/-- The continuation drops the prefix. The stopped pair keeps the prefix the
run produced. This projection is not a history readout, a seal, or an
authority update. -/
theorem stopRecording_forgets (start : State) (finished : RecordedState State) :
    (stopRecording start finished).2 = forgetRecording finished ∧
      (stopRecording start finished).1.2.record = finished.record ∧
      (stopRecording start finished).1 = (start, finished) :=
  ⟨rfl, rfl, rfl⟩

/-- Proof witness, not the stopped diary. The account of an accepted source
path is the base potential difference of the stopped continuation. The
prefix does not change that charge, and it does not have to be complete. -/
theorem stopRecording_account
    (machine : OccurrenceMachineCore Term State Answer)
    (potential : State → Nat)
    (mono : ∀ (before after : State) (index : Nat),
      (machine.next before)[index]? = some after → potential before ≤ potential after)
    (start : State) (opened : Recording.Prefix Nat) (trace : List Nat)
    (finished : RecordedState State)
    (accepted : (recordedMachine machine).follow ⟨start, opened⟩ trace = some finished) :
    (eventAccount (recordedMachine machine) (recordedEdge potential)).of
        (ofTrace (recordedMachine machine) trace accepted) =
      Multiplicative.ofAdd
        (potential (stopRecording start finished).2 - potential start) := by
  rw [stopRecording, forgetRecording]
  exact recordedMachine_account machine potential mono
    (ofTrace (recordedMachine machine) trace accepted)

/-- A later base interval appends at the stopped endpoint. The continuation
is the base runner. The stopped pair stays the prefix already produced. -/
theorem stopRecording_suffix
    (machine : OccurrenceMachineCore Term State Answer)
    (start : State) (opened : Recording.Prefix Nat) (past suffix : List Nat)
    (finished : RecordedState State) (later : State)
    (accepted : (recordedMachine machine).follow ⟨start, opened⟩ past = some finished)
    (continued : machine.follow (stopRecording start finished).2 suffix = some later) :
    machine.follow start (past ++ suffix) = some later ∧
      (stopRecording start finished).1 = (start, finished) := by
  refine ⟨?_, rfl⟩
  have basePast := (stopRecording_projects machine start opened past finished accepted).1
  rw [WorkOccurrence.follow_append, basePast]
  change (some (stopRecording start finished).2).bind
      (fun middle => machine.follow middle suffix) = some later
  rw [Option.bind_some, continued]

/-- Trace readout. Completeness and the supplied indices, then `follow` from
the diary's recorded start. This does not compare the replayed state with
the stored endpoint, and it does not authenticate that start. The result is
not a live continuation. -/
def checkStoppedTrace
    (machine : OccurrenceMachineCore Term State Answer)
    (diary : State × RecordedState State)
    (supplied : List Nat) : Option State :=
  diary.2.record.complete?.bind fun stored =>
    if stored = supplied then machine.follow diary.1 supplied else none

theorem checkStoppedTrace_agrees
    (machine : OccurrenceMachineCore Term State Answer)
    (diary : State × RecordedState State)
    (supplied : List Nat) (target : State) :
    checkStoppedTrace machine diary supplied = some target ↔
      diary.2.record.complete? = some supplied ∧
        machine.follow diary.1 supplied = some target := by
  unfold checkStoppedTrace
  cases complete : diary.2.record.complete? with
  | none =>
      rw [Option.bind_none]
      constructor
      · intro rejected
        cases rejected
      · intro rejected
        cases rejected.1
  | some stored =>
      rw [Option.bind_some]
      by_cases same : stored = supplied
      · rw [if_pos same]
        constructor
        · intro followed
          exact ⟨congrArg some same, followed⟩
        · intro accepted
          exact accepted.2
      · rw [if_neg same]
        constructor
        · intro rejected
          cases rejected
        · intro accepted
          exact absurd (Option.some.inj accepted.1) same

theorem checkStoppedTrace_omitted
    (machine : OccurrenceMachineCore Term State Answer)
    (diary : State × RecordedState State)
    (supplied : List Nat)
    (lost : diary.2.record.omitted ≠ 0) :
    checkStoppedTrace machine diary supplied = none := by
  unfold checkStoppedTrace
  rw [Recording.Prefix.complete?, if_neg lost]
  exact Option.bind_none _

/-- Endpoint readout. The trace must replay to the stored endpoint by the
state's exact equality. That equality validates the endpoint the diary
claims. It does not authenticate an arbitrary supplied root. Exact endpoint
equality, storage lifetime, and current authority stay independent. A forged
endpoint fails even when the indices replay. The verdict does not issue a
live continuation or a one-shot token. -/
def checkStopped [DecidableEq State]
    (machine : OccurrenceMachineCore Term State Answer)
    (diary : State × RecordedState State)
    (supplied : List Nat) : Option State :=
  (checkStoppedTrace machine diary supplied).bind fun reached =>
    if reached = diary.2.base then some reached else none

theorem checkStopped_agrees [DecidableEq State]
    (machine : OccurrenceMachineCore Term State Answer)
    (diary : State × RecordedState State)
    (supplied : List Nat) (target : State) :
    checkStopped machine diary supplied = some target ↔
      diary.2.record.complete? = some supplied ∧
        machine.follow diary.1 supplied = some target ∧
        target = diary.2.base := by
  unfold checkStopped
  constructor
  · intro accepted
    cases traced : checkStoppedTrace machine diary supplied with
    | none =>
        rw [traced, Option.bind_none] at accepted
        cases accepted
    | some reached =>
        rw [traced, Option.bind_some] at accepted
        by_cases same : reached = diary.2.base
        · rw [if_pos same] at accepted
          have reachedTarget : reached = target := Option.some.inj accepted
          obtain ⟨stored, followed⟩ :=
            (checkStoppedTrace_agrees machine diary supplied reached).mp traced
          rw [reachedTarget] at followed same
          exact ⟨stored, followed, same⟩
        · rw [if_neg same] at accepted
          cases accepted
  · intro accepted
    obtain ⟨stored, followed, same⟩ := accepted
    have traced :=
      (checkStoppedTrace_agrees machine diary supplied target).mpr ⟨stored, followed⟩
    rw [traced, Option.bind_some, if_pos same]

/-- A replayed trace with a different stored endpoint is refused. -/
theorem checkStopped_rejects_endpoint [DecidableEq State]
    (machine : OccurrenceMachineCore Term State Answer)
    (diary : State × RecordedState State)
    (supplied : List Nat) (reached : State)
    (traced : checkStoppedTrace machine diary supplied = some reached)
    (changed : reached ≠ diary.2.base) :
    checkStopped machine diary supplied = none := by
  unfold checkStopped
  rw [traced, Option.bind_some, if_neg changed]

/-- Any omission refuses both readouts. The retained items and the omission
count stay in the prefix. -/
theorem checkStopped_omitted [DecidableEq State]
    (machine : OccurrenceMachineCore Term State Answer)
    (diary : State × RecordedState State)
    (supplied : List Nat)
    (lost : diary.2.record.omitted ≠ 0) :
    checkStopped machine diary supplied = none := by
  unfold checkStopped
  rw [checkStoppedTrace_omitted machine diary supplied lost]
  exact Option.bind_none _

/-- Knowing an accepted trace does not complete an omitted prefix. Stop keeps
the omission, and the stopped diary does not decode as that trace. -/
theorem stopRecording_incomplete [DecidableEq State]
    (machine : OccurrenceMachineCore Term State Answer)
    (start : State) (opened : Recording.Prefix Nat) (trace : List Nat)
    (finished : RecordedState State)
    (accepted : (recordedMachine machine).follow ⟨start, opened⟩ trace = some finished)
    (lost : (opened.append trace).omitted ≠ 0) :
    (stopRecording start finished).1.2.record.omitted ≠ 0 ∧
      checkStopped machine (stopRecording start finished).1 trace = none := by
  have stored := (stopRecording_projects machine start opened trace finished accepted).2.1
  have omitted : (stopRecording start finished).1.2.record.omitted ≠ 0 := by
    rw [stored]
    exact lost
  exact ⟨omitted, checkStopped_omitted machine (stopRecording start finished).1 trace omitted⟩

/-- Requested readout. A history witness exists only after the endpoint check
accepts. Its target is the stored endpoint. `ofTrace` recomputes that
witness; `stopRecording` does not store it. The witness is not a live
continuation or a one-shot token. -/
theorem decodeStopped [DecidableEq State]
    (machine : OccurrenceMachineCore Term State Answer)
    (diary : State × RecordedState State)
    (supplied : List Nat) (target : State)
    (checked : checkStopped machine diary supplied = some target) :
    target = diary.2.base ∧
      ∃ history : History machine diary.1 target,
        indices machine history = supplied ∧
          machine.follow diary.1 supplied = some target := by
  obtain ⟨_, followed, same⟩ :=
    (checkStopped_agrees machine diary supplied target).mp checked
  exact ⟨same, ofTrace machine supplied followed,
    indices_ofTrace machine supplied followed, followed⟩

/-- Attach a fresh bounded prefix at the current base state. -/
def restartRecording (base : State) (capacity : Nat) : RecordedState State :=
  ⟨base, Recording.Prefix.initial capacity⟩

/-- The fresh prefix stores none of an earlier interval. Later events fill
only the new capacity. -/
theorem restartRecording_excludes
    (base : State) (capacity : Nat) (earlier : List Nat) :
    (restartRecording base capacity).record.items = [] ∧
      (restartRecording base capacity).record.omitted = 0 ∧
      ((restartRecording base capacity).record.append earlier).items =
        earlier.take capacity := by
  refine ⟨rfl, rfl, ?_⟩
  exact Recording.Prefix.initial_items capacity earlier

/-- A complete restarted prefix replays `follow` from the restart base only.
It does not reconstruct an earlier start, and acceptance is not step authority. -/
theorem restartRecording_replay
    (machine : OccurrenceMachineCore Term State Answer)
    (base : State) (capacity : Nat) (suffix : List Nat) (target : State) :
    ((recordedMachine machine).follow (restartRecording base capacity) suffix).bind
        (fun finished => finished.record.complete?.bind (machine.follow base)) =
      some target ↔
      suffix.length ≤ capacity ∧ machine.follow base suffix = some target :=
  recordedMachine_replay machine base capacity suffix target

/-- Restart does not continue the stopped recorder. The base may agree while
the prefix is new. Restart is not a seal and not an authority transfer. -/
theorem restartRecording_differs
    (finished : RecordedState State) (capacity : Nat)
    (kept : finished.record ≠ Recording.Prefix.initial capacity) :
    restartRecording finished.base capacity ≠ finished := by
  intro same
  have records : finished.record = Recording.Prefix.initial capacity := by
    rw [← same, restartRecording]
  exact kept records

/-- The same index sequence is replayable after a position-preserving change
of machine representation. The hypothesis retains duplicates and branch order. -/
def forward {TargetTerm TargetState TargetAnswer : Type}
    (machine : OccurrenceMachineCore Term State Answer)
    (target : OccurrenceMachineCore TargetTerm TargetState TargetAnswer)
    (mapState : State → TargetState)
    (next : ∀ state, target.next (mapState state) = (machine.next state).map mapState) :
    RewriteEventHistory.ForwardEvidenceMap (system machine) (system target) where
  mapTerm := mapState
  mapEquiv := fun equal => congrArg mapState equal
  mapEvidence := by
    intro source destination event
    refine ⟨event.val, ?_⟩
    rw [next, List.getElem?_map, event.property]
    rfl

/-- Transport changes states and their representation, preserving every
selected occurrence in its original order. -/
theorem forward_indices {TargetTerm TargetState TargetAnswer : Type}
    (machine : OccurrenceMachineCore Term State Answer)
    (target : OccurrenceMachineCore TargetTerm TargetState TargetAnswer)
    (mapState : State → TargetState)
    (next : ∀ state, target.next (mapState state) = (machine.next state).map mapState)
    {source destination : RewriteEventHistory.State (system machine)}
    (history : Quiver.Path source destination) :
    indices target ((forward machine target mapState next).histories.map history) =
      indices machine history := by
  induction history with
  | nil => rfl
  | cons past event ih =>
      change indices target
          (((forward machine target mapState next).histories.map past).cons
            ((forward machine target mapState next).mapEvidence event)) = _
      simp only [indices, ih]
      rfl

/-- The history transport theorem gives replay preservation against the
independently executable target machine. -/
theorem forward_replay {TargetTerm TargetState TargetAnswer : Type}
    (machine : OccurrenceMachineCore Term State Answer)
    (target : OccurrenceMachineCore TargetTerm TargetState TargetAnswer)
    (mapState : State → TargetState)
    (next : ∀ state, target.next (mapState state) = (machine.next state).map mapState)
    {source destination : State} {trace : List Nat}
    (accepted : machine.follow source trace = some destination) :
    target.follow (mapState source) trace = some (mapState destination) := by
  have replay := follow_indices target
    ((forward machine target mapState next).histories.map (ofTrace machine trace accepted))
  rw [forward_indices, indices_ofTrace] at replay
  exact replay

/-- Position-preserving representation change reflects failed as well as
successful replay. No target branch is introduced at a represented state. -/
theorem follow_map {TargetTerm TargetState TargetAnswer : Type}
    (machine : OccurrenceMachineCore Term State Answer)
    (target : OccurrenceMachineCore TargetTerm TargetState TargetAnswer)
    (mapState : State → TargetState)
    (next : ∀ state, target.next (mapState state) = (machine.next state).map mapState)
    (source : State) (trace : List Nat) :
    target.follow (mapState source) trace = (machine.follow source trace).map mapState := by
  induction trace generalizing source with
  | nil => rfl
  | cons index rest ih =>
      simp only [OccurrenceMachineCore.follow, next, List.getElem?_map]
      cases found : (machine.next source)[index]? with
      | none => rfl
      | some middle => simpa using ih middle

/-- Every replayed target endpoint from an image state comes from a source
history with the same occurrence list. -/
theorem replay_reflects {TargetTerm TargetState TargetAnswer : Type}
    (machine : OccurrenceMachineCore Term State Answer)
    (target : OccurrenceMachineCore TargetTerm TargetState TargetAnswer)
    (mapState : State → TargetState)
    (next : ∀ state, target.next (mapState state) = (machine.next state).map mapState)
    {source : State} {destination : TargetState} {trace : List Nat}
    (accepted : target.follow (mapState source) trace = some destination) :
    ∃ endpoint, machine.follow source trace = some endpoint ∧ mapState endpoint = destination := by
  rw [follow_map machine target mapState next] at accepted
  cases replay : machine.follow source trace with
  | none => simp [replay] at accepted
  | some endpoint =>
      refine ⟨endpoint, rfl, ?_⟩
      simpa [replay] using accepted

/-- Pulling back the target's account along the existing history functor
recovers the source account. Identity and composition of these functors are
the shared `ForwardEvidenceMap.histories_id` and `histories_comp` laws. -/
theorem forward_account {TargetTerm TargetState TargetAnswer : Type}
    (machine : OccurrenceMachineCore Term State Answer)
    (target : OccurrenceMachineCore TargetTerm TargetState TargetAnswer)
    (mapState : State → TargetState)
    (next : ∀ state, target.next (mapState state) = (machine.next state).map mapState) :
    (traceAccount target).comap (forward machine target mapState next).histories =
      traceAccount machine := by
  apply Mettapedia.Effects.RunAccount.ext
  funext source destination history
  exact congrArg FreeMonoid.ofList (forward_indices machine target mapState next history)

/-- Preservation on primitive events extends to every history, including a
change of coefficient monoid. No exchange or commutativity law is used. -/
theorem eventAccount_forward {TargetTerm TargetState TargetAnswer W : Type} [Monoid W]
    (machine : OccurrenceMachineCore Term State Answer)
    (target : OccurrenceMachineCore TargetTerm TargetState TargetAnswer)
    (mapState : State → TargetState)
    (next : ∀ state, target.next (mapState state) = (machine.next state).map mapState)
    (sourceValue : State → State → Nat → V)
    (targetValue : TargetState → TargetState → Nat → W) (mapValue : V →* W)
    (onEvent : ∀ (source destination : State) (index : Nat),
      (machine.next source)[index]? = some destination →
      targetValue (mapState source) (mapState destination) index =
        mapValue (sourceValue source destination index)) :
    (eventAccount target targetValue).comap (forward machine target mapState next).histories =
      (eventAccount machine sourceValue).map mapValue := by
  apply RewriteEventHistory.PathEvidenceMap.account_preserved
    (RewriteEventHistory.PathEvidenceMap.ofForward (forward machine target mapState next))
    (eventAccount machine sourceValue) (eventAccount target targetValue) mapValue
  intro source destination event
  simp only [RewriteEventHistory.PathEvidenceMap.ofForward, eventAccount_generator]
  exact onEvent source.term destination.term event.val event.property

/-- Replay of a path-valued interpretation uses the implementing occurrence
list. The original list generally has a different length and is not a valid
target replay certificate. -/
theorem path_replay {TargetTerm TargetState TargetAnswer : Type}
    (machine : OccurrenceMachineCore Term State Answer)
    (target : OccurrenceMachineCore TargetTerm TargetState TargetAnswer)
    (realization : RewriteEventHistory.PathEvidenceMap (system machine) (system target))
    {source destination : State} {trace : List Nat}
    (accepted : machine.follow source trace = some destination) :
    target.follow (realization.mapTerm source)
      (indices target (realization.histories.map (ofTrace machine trace accepted))) =
        some (realization.mapTerm destination) :=
  follow_indices target (realization.histories.map (ofTrace machine trace accepted))

def duplicateFirst : History OccurrenceMachineCore.duplicateExample .root .done :=
  ofTrace _ [0] rfl

def duplicateSecond : History OccurrenceMachineCore.duplicateExample .root .done :=
  ofTrace _ [1] rfl

/-- Equal endpoints do not collapse two physical successor occurrences. -/
theorem duplicate_histories_distinct : duplicateFirst ≠ duplicateSecond := by
  intro equal
  have traces := congrArg (indices OccurrenceMachineCore.duplicateExample) equal
  have impossible : ([0] : List Nat) = [1] := traces
  cases impossible

/-- Both occurrences retain the same endpoint. That endpoint does not determine
which occurrence was taken, so a forgotten prefix cannot be read back from it. -/
theorem endpoint_does_not_determine_past :
    (retained OccurrenceMachineCore.duplicateExample duplicateFirst).right =
      (retained OccurrenceMachineCore.duplicateExample duplicateSecond).right ∧
    (retained OccurrenceMachineCore.duplicateExample duplicateFirst).hom ≠
      (retained OccurrenceMachineCore.duplicateExample duplicateSecond).hom := by
  refine ⟨?_, duplicate_histories_distinct⟩
  rw [retained_right, retained_right]

/-- Replay rejects a missing occurrence even when another occurrence reaches
the requested endpoint. -/
theorem missing_occurrence_rejected :
    ¬ ∃ history : History OccurrenceMachineCore.duplicateExample .root .done,
      indices OccurrenceMachineCore.duplicateExample history = [2] := by
  rw [← follow_iff_history]
  decide

namespace Controls

private def alternating : OccurrenceMachineCore Unit Bool Empty where
  load _ := false
  next state := [!state]
  answer _ := none
  answer_final _ _ returned := by cases returned

private def twoEvents : History alternating false false := ofTrace _ [0, 0] rfl

/-- The two executed events retain their original order. -/
theorem history_account_is_ordered :
    (eventAccount alternating (fun before _ _ => FreeMonoid.of before)).of twoEvents =
      FreeMonoid.ofList [false, true] := rfl

/-- Reversing an account fails even though the history returns to its source. -/
theorem reversing_event_account_changes_observation :
    (eventAccount alternating (fun before _ _ => FreeMonoid.of before)).of twoEvents ≠
      FreeMonoid.ofList [true, false] := by
  rw [history_account_is_ordered]
  change ([false, true] : List Bool) ≠ [true, false]
  decide

/-- A vanishing coefficient does not erase the two physical events. -/
theorem zero_account_keeps_both_events :
    (eventAccount alternating (fun _ _ _ => (0 : Nat))).of twoEvents = 0 ∧
      indices alternating twoEvents = [0, 0] := ⟨rfl, rfl⟩

/-- A declared observer may suppress every label while the trace judgment
still retains the actual number of transitions. -/
theorem unobserved_steps_still_count :
    ObservedTrace (Step := (system alternating).steps.Evidence)
      (fun {_ _} _ => ([] : List Nat)) 2 false false [] :=
  history_observed_trace alternating (fun _ _ _ => ([] : List Nat)) twoEvents

/-- Equal observation records do not reconstruct the hidden history. Here
the empty run and a two-step cycle both report the empty record. -/
theorem empty_record_does_not_recover_history :
    (eventAccount alternating (fun _ _ _ => FreeMonoid.ofList ([] : List Nat))).of twoEvents =
      (eventAccount alternating (fun _ _ _ => FreeMonoid.ofList ([] : List Nat))).of
        (Quiver.Path.nil : History alternating false false) ∧
    indices alternating twoEvents ≠
      indices alternating (Quiver.Path.nil : History alternating false false) :=
  ⟨rfl, by decide⟩

end Controls

namespace LoweringControls

inductive TargetState where
  | root
  | prepared
  | done
deriving DecidableEq

/-- The first source choice takes a preparation step. The optional third
edge is an unauthorized duplicate answer, used only by the negative control. -/
def target (extra : Bool) : OccurrenceMachineCore Unit TargetState Nat where
  load _ := .root
  next
    | .root => if extra then [.prepared, .done, .done] else [.prepared, .done]
    | .prepared => [.done]
    | .done => []
  answer
    | .done => some 7
    | _ => none
  answer_final := by
    intro state answer returned
    cases state <;> simp_all

def lowerState : OccurrenceMachineCore.DuplicateExampleState → TargetState
  | .root => .root
  | .done => .done

/-- Two equal source endpoints receive different implementing paths because
the source occurrence index is retained. -/
def lowering (extra : Bool) :
    RewriteEventHistory.PathEvidenceMap
      (system OccurrenceMachineCore.duplicateExample) (system (target extra)) where
  mapTerm := lowerState
  mapEquiv := fun equal => congrArg lowerState equal
  mapEvidence := by
    intro before after event
    obtain ⟨index, found⟩ := event
    cases before with
    | done => simp [OccurrenceMachineCore.duplicateExample] at found
    | root =>
        cases index with
        | zero =>
            simp [OccurrenceMachineCore.duplicateExample] at found
            subst after
            exact ofTrace (target extra) [0, 0] (by cases extra <;> rfl)
        | succ index =>
            cases index with
            | zero =>
                simp [OccurrenceMachineCore.duplicateExample] at found
                subst after
                exact ofTrace (target extra) [1] (by cases extra <;> rfl)
            | succ index => simp [OccurrenceMachineCore.duplicateExample] at found

def fuseState : TargetState → OccurrenceMachineCore.DuplicateExampleState
  | .root | .prepared => .root
  | .done => .done

/-- The preparation is administrative under the answer observation. The
following commit retains the first choice, and the direct path retains the
second. This is a nontrivial fusion of a two-step implementation. -/
def fusion : RewriteEventHistory.PathEvidenceMap
    (system (target false)) (system OccurrenceMachineCore.duplicateExample) where
  mapTerm := fuseState
  mapEquiv := fun equal => congrArg fuseState equal
  mapEvidence := by
    intro before after event
    obtain ⟨index, found⟩ := event
    cases before with
    | done => simp [target] at found
    | prepared =>
        cases index with
        | zero =>
            simp [target] at found
            subst after
            exact duplicateFirst
        | succ index => simp [target] at found
    | root =>
        cases index with
        | zero =>
            simp [target] at found
            subst after
            exact Quiver.Path.nil
        | succ index =>
            cases index with
            | zero =>
                simp [target] at found
                subst after
                exact duplicateSecond
            | succ index => simp [target] at found

/-- Fusion preserves the independently declared answer observation at every
target state, including the intermediate preparation state. -/
theorem fusion_preserves_answer (state : TargetState) :
    OccurrenceMachineCore.duplicateExample.answer (fuseState state) =
      (target false).answer state := by
  cases state <;> rfl

/-- Lowering followed by fusion recovers every source history, not merely
its final answer or its number of transitions. -/
theorem fusion_retracts_lowering :
    ((lowering false).comp fusion).histories =
      𝟭 (RewriteEventHistory.HistoryCategory (system OccurrenceMachineCore.duplicateExample)) := by
  symm
  apply Paths.lift_unique
  fapply Prefunctor.ext
  · intro state
    obtain ⟨state⟩ := state
    cases state <;> rfl
  · intro a b event
    obtain ⟨before⟩ := a
    obtain ⟨after⟩ := b
    obtain ⟨index, found⟩ := event
    cases before with
    | done => simp [OccurrenceMachineCore.duplicateExample] at found
    | root =>
        cases index with
        | zero =>
            simp [OccurrenceMachineCore.duplicateExample] at found
            subst after
            rfl
        | succ index =>
            cases index with
            | zero =>
                simp [OccurrenceMachineCore.duplicateExample] at found
                subst after
                rfl
            | succ index => simp [OccurrenceMachineCore.duplicateExample] at found

def sourceWord (_before _after : OccurrenceMachineCore.DuplicateExampleState)
    (index : Nat) : FreeMonoid Nat :=
  if index = 0 then FreeMonoid.ofList [10, 11] else FreeMonoid.of 20

def targetWord (before _after : TargetState) (index : Nat) : FreeMonoid Nat :=
  match before with
  | .root => if index = 0 then FreeMonoid.of 10 else FreeMonoid.of 20
  | .prepared => FreeMonoid.of 11
  | .done => 1

/-- The account on the two source choices is checked against the actual
implementing events. Chronological multiplication is preserved without
assuming that coefficients commute. -/
theorem lowering_preserves_ordered_account :
    (eventAccount (target false) targetWord).comap (lowering false).histories =
      eventAccount OccurrenceMachineCore.duplicateExample sourceWord := by
  have preserved := RewriteEventHistory.PathEvidenceMap.account_preserved
    (lowering false) (eventAccount OccurrenceMachineCore.duplicateExample sourceWord)
    (eventAccount (target false) targetWord) (MonoidHom.id (FreeMonoid Nat))
  apply preserved
  intro a b event
  obtain ⟨before⟩ := a
  obtain ⟨after⟩ := b
  obtain ⟨index, found⟩ := event
  cases before with
  | done => simp [OccurrenceMachineCore.duplicateExample] at found
  | root =>
      cases index with
      | zero =>
          simp [OccurrenceMachineCore.duplicateExample] at found
          subst after
          rfl
      | succ index =>
          cases index with
          | zero =>
              simp [OccurrenceMachineCore.duplicateExample] at found
              subst after
              rfl
          | succ index => simp [OccurrenceMachineCore.duplicateExample] at found

/-- Equal endpoints do not fix the cost of their implementing paths. -/
theorem implementing_work_differs :
    (eventAccount (target false) (fun _ _ _ => Multiplicative.ofAdd (1 : Nat))).of
        ((lowering false).histories.map duplicateFirst) = Multiplicative.ofAdd 2 ∧
      (eventAccount (target false) (fun _ _ _ => Multiplicative.ofAdd (1 : Nat))).of
        ((lowering false).histories.map duplicateSecond) = Multiplicative.ofAdd 1 :=
  ⟨rfl, rfl⟩

/-- Answer-preserving fusion cannot also preserve a unit charge for every
physical target event: the administrative preparation has been removed. -/
theorem fusion_does_not_preserve_unit_work :
    (eventAccount OccurrenceMachineCore.duplicateExample
      (fun _ _ _ => Multiplicative.ofAdd (1 : Nat))).comap fusion.histories ≠
        eventAccount (target false) (fun _ _ _ => Multiplicative.ofAdd (1 : Nat)) := by
  intro equal
  have preparation := congrArg
    (fun account : Mettapedia.Effects.RunAccount
        (RewriteEventHistory.HistoryCategory (system (target false))) (Multiplicative Nat) =>
      account.of (ofTrace (target false) (source := .root) (target := .prepared) [0] rfl)) equal
  have impossible : (0 : Nat) = 1 := congrArg Multiplicative.toAdd preparation
  cases impossible

/-- Lowering retains both authored choices even though their implementations
have different lengths and the same answer. -/
theorem distinct_implementing_paths (extra : Bool) :
    indices (target extra) ((lowering extra).histories.map duplicateFirst) = [0, 0] ∧
      indices (target extra) ((lowering extra).histories.map duplicateSecond) = [1] := by
  cases extra <;> exact ⟨rfl, rfl⟩

/-- The two native trace certificates execute against the target machine. -/
theorem implementing_paths_replay :
    (target false).follow .root [0, 0] = some .done ∧
      (target false).follow .root [1] = some .done ∧
      (target false).follow .root [0] = some .prepared := ⟨rfl, rfl, rfl⟩

/-- The retained source diaries post along the unequal lowering. The first
source occurrence replays by the preparation indices `[0, 0]`, and the second
by `[1]`. `forward_realization_allows_extra_answer` keeps the unauthorized
target edge outside this forward image. -/
theorem retained_lowering_replays_by_implementing_indices (extra : Bool) :
    indices (target extra)
        ((Under.post (lowering extra).histories).obj
          (retained OccurrenceMachineCore.duplicateExample duplicateFirst)).hom = [0, 0] ∧
      indices (target extra)
        ((Under.post (lowering extra).histories).obj
          (retained OccurrenceMachineCore.duplicateExample duplicateSecond)).hom = [1] ∧
      (target extra).follow .root
        (indices (target extra)
          ((Under.post (lowering extra).histories).obj
            (retained OccurrenceMachineCore.duplicateExample duplicateFirst)).hom) =
        some .done ∧
      (target extra).follow .root
        (indices (target extra)
          ((Under.post (lowering extra).histories).obj
            (retained OccurrenceMachineCore.duplicateExample duplicateSecond)).hom) =
        some .done ∧
      ((Under.post (lowering extra).histories).obj
          (retained OccurrenceMachineCore.duplicateExample duplicateFirst)).right =
        (lowering extra).histories.obj
          (historyVertex OccurrenceMachineCore.duplicateExample .done) := by
  have firstPosted := retained_posted OccurrenceMachineCore.duplicateExample
    (lowering extra) duplicateFirst
  have secondPosted := retained_posted OccurrenceMachineCore.duplicateExample
    (lowering extra) duplicateSecond
  refine ⟨?_, ?_, ?_, ?_, firstPosted.2⟩
  · rw [firstPosted.1]
    exact (distinct_implementing_paths extra).1
  · rw [secondPosted.1]
    exact (distinct_implementing_paths extra).2
  · rw [firstPosted.1]
    exact path_replay OccurrenceMachineCore.duplicateExample (target extra)
      (lowering extra) (source := .root) (destination := .done) (trace := [0]) rfl
  · rw [secondPosted.1]
    exact path_replay OccurrenceMachineCore.duplicateExample (target extra)
      (lowering extra) (source := .root) (destination := .done) (trace := [1]) rfl

/-- The posted accounts stay the declared source accounts. The first source
label is `sourceWord`. `implementing_work_differs` is the separate unit charge
of these implementing paths. -/
theorem retained_lowering_keeps_declared_account :
    (eventAccount (target false) targetWord).of
        ((Under.post (lowering false).histories).obj
          (retained OccurrenceMachineCore.duplicateExample duplicateFirst)).hom =
      (eventAccount OccurrenceMachineCore.duplicateExample sourceWord).of
        duplicateFirst ∧
      (eventAccount (target false) targetWord).of
        ((Under.post (lowering false).histories).obj
          (retained OccurrenceMachineCore.duplicateExample duplicateSecond)).hom =
      (eventAccount OccurrenceMachineCore.duplicateExample sourceWord).of
        duplicateSecond :=
  ⟨retained_posted_account OccurrenceMachineCore.duplicateExample (lowering false)
      (eventAccount OccurrenceMachineCore.duplicateExample sourceWord)
      (eventAccount (target false) targetWord) (MonoidHom.id (FreeMonoid Nat))
      lowering_preserves_ordered_account duplicateFirst,
    retained_posted_account OccurrenceMachineCore.duplicateExample (lowering false)
      (eventAccount OccurrenceMachineCore.duplicateExample sourceWord)
      (eventAccount (target false) targetWord) (MonoidHom.id (FreeMonoid Nat))
      lowering_preserves_ordered_account duplicateSecond⟩

/-- The shorter cut retains the unfinished first branch. A source depth
budget cannot simply be reused as a target depth budget. -/
theorem lowering_changes_depth_cut :
    OccurrenceMachineCore.duplicateExample.expand 1 .root =
      ⟨[(7, [0]), (7, [1])], []⟩ ∧
    (target false).expand 1 .root =
      ⟨[(7, [1])], [(.prepared, [0])]⟩ := ⟨rfl, rfl⟩

/-- Beyond its actual maximum depth, the target has exactly the two
implementations and no residual. This checks the target exploration itself. -/
theorem complete_lowered_search (extraFuel : Nat) :
    (target false).expand (extraFuel + 2) .root =
      ⟨[(7, [0, 0]), (7, [1])], []⟩ := by
  cases extraFuel <;> rfl

/-- Both source choices have implementations even in the bad target, which
also emits an unauthorized third occurrence. Forward realization alone
therefore does not establish multiplicity-preserving hosting. -/
theorem forward_realization_allows_extra_answer (extraFuel : Nat) :
    (target true).expand (extraFuel + 2) .root =
      ⟨[(7, [0, 0]), (7, [1]), (7, [2])], []⟩ ∧
      (target true).answerOccurrences (extraFuel + 2) .root ≠
        OccurrenceMachineCore.duplicateExample.answerOccurrences (extraFuel + 1) .root := by
  cases extraFuel <;> refine ⟨rfl, ?_⟩ <;>
    change ([7, 7, 7] : List Nat) ≠ [7, 7] <;> decide

end LoweringControls

end Mettapedia.GSLT.Causality.OccurrenceMachineHistory
