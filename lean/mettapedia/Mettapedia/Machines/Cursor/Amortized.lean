import Mettapedia.Machines.Cursor.Protocol
import Mettapedia.GSLT.Dynamics.LeaseReservations

/-!
# Amortized cursor costs over live residuals

A local potential inequality composes over any bounded interactive client,
including one that is suspended rather than finished. Construction savings
cannot hide transfer charges when they are included in the actual meter.
The result can be instantiated independently for any natural-valued resource
coordinate. It is not a statement that a receipt equals measured wall time.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial

universe u

variable {Base : Type u} {Index : Base → Type u}
variable {P : IndexedPolynomial.{u, u, u, u} Base Index}
variable {Return : (base : Base) → Index base → Type u}
variable {source target : Provider P}

abbrev Potential (M : Provider P) :=
  {base : Base} → {index : Index base} → M.State base index → Nat

def outcomePotential (C : Client (P := P) (Return := Return))
    (potential : Potential source) {base : Base} : Outcome source C base → Nat
  | .paused packet => potential packet.2.2
  | .done result => potential result.2.2

/-- The debit/credit obligation is local to one request and its real successor.
It permits expensive operations paid for by decreases of stored potential. -/
def Amortized (h : Hom source target) (sourceCost : Charge source)
    (targetCost : Charge target) (potential : Potential source) : Prop :=
  ∀ {base index} (state : source.State base index) (request : P.Shape base index),
    sourceCost state request + potential (source.step state request).2 ≤
      targetCost (h.map state) request + potential state

/-- Local accounting yields a bound on the whole executed prefix, retaining
the potential of the actual suspended or completed state. -/
theorem advance_amortized (C : Client (P := P) (Return := Return))
    (h : Hom source target) (sourceCost : Charge source)
    (targetCost : Charge target) (potential : Potential source)
    (localBound : Amortized h sourceCost targetCost potential)
    (fuel : Nat) {base : Base} (packet : Packet source C base) :
    (advance source C sourceCost fuel packet).1 +
        outcomePotential C potential (advance source C sourceCost fuel packet).2 ≤
      (advance target C targetCost fuel (h.packet C packet)).1 +
        potential packet.2.2 := by
  induction fuel generalizing packet with
  | zero => simp [advance, outcomePotential]
  | succ fuel ih =>
      rcases packet with ⟨index, control, state⟩
      change (advance source C sourceCost (fuel + 1) ⟨index, control, state⟩).1 +
          outcomePotential C potential
            (advance source C sourceCost (fuel + 1) ⟨index, control, state⟩).2 ≤
        (advance target C targetCost (fuel + 1) ⟨index, control, h.map state⟩).1 +
          potential state
      cases eq : C.str base index control with
      | mk shape children =>
          cases shape with
          | inl value => simp [advance, eq, outcomePotential]
          | inr request =>
              dsimp only [withHoles] at children
              simp only [advance, eq]
              dsimp only [withHoles]
              rw [← h.step state request]
              have next := ih ⟨_, children (source.step state request).1,
                (source.step state request).2⟩
              have debit := localBound state request
              dsimp only [Hom.packet] at next
              dsimp only at next debit ⊢
              omega

/-- A zero initial potential gives a direct whole-prefix work bound. -/
theorem advance_cost_le (C : Client (P := P) (Return := Return))
    (h : Hom source target) (sourceCost : Charge source)
    (targetCost : Charge target) (potential : Potential source)
    (localBound : Amortized h sourceCost targetCost potential)
    (fuel : Nat) {base : Base} (packet : Packet source C base)
    (initial : potential packet.2.2 = 0) :
    (advance source C sourceCost fuel packet).1 ≤
      (advance target C targetCost fuel (h.packet C packet)).1 := by
  have bound := advance_amortized C h sourceCost targetCost potential localBound fuel packet
  rw [initial, Nat.add_zero] at bound
  omega

/-- Two independently justified representation layers compose their potential
accounts. This avoids reproving every client for every backend combination. -/
theorem Amortized.comp {third : Provider P}
    (first : Hom source target) (second : Hom target third)
    (sourceCost : Charge source) (targetCost : Charge target) (thirdCost : Charge third)
    (firstPotential : Potential source) (secondPotential : Potential target)
    (firstBound : Amortized first sourceCost targetCost firstPotential)
    (secondBound : Amortized second targetCost thirdCost secondPotential) :
    Amortized (first.comp second) sourceCost thirdCost
      (fun state => firstPotential state + secondPotential (first.map state)) := by
  intro base index state request
  have a := firstBound state request
  have b := secondBound (first.map state) request
  rw [← first.step state request] at b
  dsimp only [Hom.comp] at a b ⊢
  omega

variable (C : Client (P := P) (Return := Return))

/-- A constant retained potential stays constant at both completed and suspended outcomes. -/
@[simp] theorem outcomePotential_const (amount : Nat) {base : Base}
    (value : Outcome source C base) :
    outcomePotential C (fun _ => amount) value = amount := by
  cases value <;> rfl

/-! ## Selected finite work leases

The selected provider carries the existing lease ledger beside its ordinary
state and spends once for each actual request. The ordinary provider remains
a separate, unmetered selection. A finite zero balance is not that selection.
The charge word is a mathematical observation of the common cursor's requests,
not a mandatory journal or a substitute evaluator. Prices count the declared
resource; callback latency, bookkeeping and validation need separate bounds.
-/

namespace Lease

open Mettapedia.GSLT.Dynamics.ParallelFuelLease

noncomputable section

variable (M : Provider P) (charge : Charge M) {Owner : Type u} (owner : Owner)

/-- One debit accompanies the response of the actual source provider. Validity
is supplied by an admitted reservation; an unfunded image is not an execution
certificate. No independent balance representation is introduced. -/
def provider : Provider P where
  State base index := M.State base index × Ledger Owner
  step state request :=
    let response := M.step state.1 request
    ⟨response.1, (response.2, (Spend.mk owner (charge state.1 request)).apply state.2)⟩

def price : Charge (provider M charge owner) := fun state request => charge state.1 request

/-- Forget only the selected financial state. Every source response and every
ordinary state field, including occurrence history, remains. -/
def forget : Hom (provider M charge owner) M where
  map state := state.1
  step _ _ := rfl

def attachPacket (ledger : Ledger Owner) {base : Base} (packet : Packet M C base) :
    Packet (provider M charge owner) C base :=
  ⟨packet.1, packet.2.1, packet.2.2, ledger⟩

def attachOutcome (ledger : Ledger Owner) {base : Base} :
    Outcome M C base → Outcome (provider M charge owner) C base
  | .paused packet => .paused (attachPacket C M charge owner ledger packet)
  | .done result => .done ⟨result.1, result.2.1, result.2.2, ledger⟩

def ledgerOf {base : Base} : Outcome (provider M charge owner) C base → Ledger Owner
  | .paused packet => packet.2.2.2
  | .done result => result.2.2.2

@[simp] theorem forget_attachPacket (ledger : Ledger Owner) {base : Base}
    (packet : Packet M C base) :
    (forget M charge owner).packet C (attachPacket C M charge owner ledger packet) = packet := by
  cases packet; rfl

@[simp] theorem forget_attachOutcome (ledger : Ledger Owner) {base : Base}
    (outcome : Outcome M C base) :
    (forget M charge owner).outcome C (attachOutcome C M charge owner ledger outcome) = outcome := by
  cases outcome with
  | paused packet => cases packet; rfl
  | done result => cases result; rfl

@[simp] theorem ledgerOf_attachOutcome (ledger : Ledger Owner) {base : Base}
    (outcome : Outcome M C base) :
    ledgerOf C M charge owner (attachOutcome C M charge owner ledger outcome) = ledger := by
  cases outcome <;> rfl

/-- Observe precisely the requests selected by the actual reply-dependent
continuations. Return inspections do not create a provider charge. -/
def charges : Nat → {base : Base} → Packet M C base → List Nat
  | 0, _, _ => []
  | fuel + 1, base, ⟨index, control, state⟩ =>
      match C.str base index control with
      | ⟨.inl _, _⟩ => []
      | ⟨.inr request, children⟩ =>
          let response := M.step state request
          charge state request :: charges fuel ⟨_, children response.1, response.2⟩

def suffixCharges (fuel : Nat) {base : Base} : Outcome M C base → List Nat
  | .paused packet => charges C M charge fuel packet
  | .done _ => []

theorem charges_sum (fuel : Nat) {base : Base} (packet : Packet M C base) :
    (charges C M charge fuel packet).sum = (advance M C charge fuel packet).1 := by
  induction fuel generalizing packet with
  | zero => rfl
  | succ fuel ih =>
      rcases packet with ⟨index, control, state⟩
      cases exposed : C.str base index control with
      | mk shape children =>
          cases shape with
          | inl value => simp [charges, advance, exposed]
          | inr request =>
              dsimp only [withHoles] at children
              simp only [charges, advance, exposed]
              dsimp only [withHoles]
              rw [List.sum_cons, ih]

theorem charges_split (first second : Nat) {base : Base} (packet : Packet M C base) :
    charges C M charge (first + second) packet =
      charges C M charge first packet ++
        suffixCharges C M charge second (advance M C charge first packet).2 := by
  induction first generalizing packet with
  | zero => simp [charges, advance, suffixCharges]
  | succ first ih =>
      rcases packet with ⟨index, control, state⟩
      rw [Nat.succ_add]
      cases exposed : C.str base index control with
      | mk shape children =>
          cases shape with
          | inl value => simp [charges, advance, suffixCharges, exposed]
          | inr request =>
              dsimp only [withHoles] at children
              simp only [charges, advance, exposed]
              dsimp only [withHoles]
              rw [ih]
              rfl

theorem resume_paid (fuel : Nat) {base : Base} (previous : Nat × Outcome M C base) :
    (resume M C charge fuel previous).1 =
      previous.1 + (suffixCharges C M charge fuel previous.2).sum := by
  rcases previous with ⟨paid, outcome⟩
  cases outcome <;> simp [resume, suffixCharges, charges_sum]

/-- Actual lease execution and ordinary cursor execution have the same paid
prefix and exact residual. The ledger is obtained by spending each observed
request charge, including requests whose replies do not return an answer. -/
theorem advance_exact (fuel : Nat) {base : Base} (packet : Packet M C base)
    (ledger : Ledger Owner) :
    advance (provider M charge owner) C (price M charge owner) fuel
        (attachPacket C M charge owner ledger packet) =
      ((advance M C charge fuel packet).1,
        attachOutcome C M charge owner (spendWord owner (charges C M charge fuel packet) ledger)
          (advance M C charge fuel packet).2) := by
  induction fuel generalizing packet ledger with
  | zero => cases packet; rfl
  | succ fuel ih =>
      rcases packet with ⟨index, control, state⟩
      change advance (provider M charge owner) C (price M charge owner) (fuel + 1)
          ⟨index, control, (state, ledger)⟩ = _
      cases exposed : C.str base index control with
      | mk shape children =>
          cases shape with
          | inl value => simp only [advance, exposed, charges, spendWord, attachOutcome]
          | inr request =>
              dsimp only [withHoles] at children
              simp only [advance, exposed, charges, spendWord]
              dsimp only [withHoles, provider, price]
              exact congrArg (fun result => (charge state request + result.1, result.2))
                (ih ⟨_, children (M.step state request).1, (M.step state request).2⟩
                  ((Spend.mk owner (charge state request)).apply ledger))

theorem resume_exact (fuel paid : Nat) {base : Base} (outcome : Outcome M C base)
    (ledger : Ledger Owner) :
    resume (provider M charge owner) C (price M charge owner) fuel
        (paid, attachOutcome C M charge owner ledger outcome) =
      ((resume M C charge fuel (paid, outcome)).1,
        attachOutcome C M charge owner
          (spendWord owner (suffixCharges C M charge fuel outcome) ledger)
          (resume M C charge fuel (paid, outcome)).2) := by
  cases outcome with
  | done result => rfl
  | paused packet => simp only [resume, attachOutcome, suffixCharges, advance_exact]

theorem advance_erases (fuel : Nat) {base : Base}
    (packet : Packet (provider M charge owner) C base) :
    ((advance (provider M charge owner) C (price M charge owner) fuel packet).1,
      (forget M charge owner).outcome C
        (advance (provider M charge owner) C (price M charge owner) fuel packet).2) =
      advance M C charge fuel ((forget M charge owner).packet C packet) :=
  (forget M charge owner).advance_account C (price M charge owner) charge (fun _ _ => rfl) fuel packet

theorem advance_admitted (fuel : Nat) {base : Base} (packet : Packet M C base)
    (ledger : Ledger Owner) (affordable : ((advance M C charge fuel packet).1 : ℤ) ≤ ledger.balances owner) :
    Execution ledger
      (ledgerOf C M charge owner (advance (provider M charge owner) C (price M charge owner) fuel
        (attachPacket C M charge owner ledger packet)).2) := by
  rw [advance_exact, ledgerOf_attachOutcome]
  apply spendWord_execution
  rwa [charges_sum]

theorem advance_spent (fuel : Nat) {base : Base} (packet : Packet M C base)
    (ledger : Ledger Owner) :
    (ledgerOf C M charge owner
      (advance (provider M charge owner) C (price M charge owner) fuel
        (attachPacket C M charge owner ledger packet)).2).spent =
      ledger.spent + ((advance M C charge fuel packet).1 : ℤ) := by
  rw [advance_exact, ledgerOf_attachOutcome, spendWord_spent, charges_sum]

theorem advance_balance (fuel : Nat) {base : Base} (packet : Packet M C base)
    (ledger : Ledger Owner) :
    (ledgerOf C M charge owner
      (advance (provider M charge owner) C (price M charge owner) fuel
        (attachPacket C M charge owner ledger packet)).2).balances owner =
      ledger.balances owner - ((advance M C charge fuel packet).1 : ℤ) := by
  rw [advance_exact, ledgerOf_attachOutcome, spendWord_at_owner, charges_sum]

/-- Only the new suffix is spent. The incoming paid coordinate is retained
in the cursor result and is not charged a second time. -/
theorem resume_admitted (fuel paid : Nat) {base : Base} (outcome : Outcome M C base)
    (ledger : Ledger Owner)
    (affordable : ((resume M C charge fuel (paid, outcome)).1 : ℤ) - (paid : ℤ) ≤
      ledger.balances owner) :
    Execution ledger
      (ledgerOf C M charge owner
        (resume (provider M charge owner) C (price M charge owner) fuel
          (paid, attachOutcome C M charge owner ledger outcome)).2) := by
  rw [resume_exact, ledgerOf_attachOutcome]
  apply spendWord_execution
  rw [resume_paid, Nat.cast_add] at affordable
  simpa only [add_sub_cancel_left] using affordable

theorem spending_split (first second : Nat) {base : Base} (packet : Packet M C base)
    (ledger : Ledger Owner) :
    spendWord owner (charges C M charge (first + second) packet) ledger =
      spendWord owner (suffixCharges C M charge second (advance M C charge first packet).2)
        (spendWord owner (charges C M charge first packet) ledger) := by
  have appendWord (left right : List Nat) (before : Ledger Owner) :
      spendWord owner (left ++ right) before = spendWord owner right (spendWord owner left before) := by
    induction left generalizing before with
    | nil => rfl
    | cons head tail ih => simpa only [List.cons_append, spendWord] using ih _
  rw [charges_split, appendWord]

/-- Arbitrary admitted sibling reservations, nested grants and cancellations
may precede or follow this real service suffix. They all use the same ledger;
the cursor contributes its actual execution, not an assumed charge word. -/
theorem admitted_interleaving (fuel paid : Nat) {base : Base} (outcome : Outcome M C base)
    (initial before final : Ledger Owner) (valid : initial.Nonnegative)
    (beforeExecution : Execution initial before)
    (affordable : ((resume M C charge fuel (paid, outcome)).1 : ℤ) - (paid : ℤ) ≤
      before.balances owner)
    (suffix : Execution
      (ledgerOf C M charge owner
        (resume (provider M charge owner) C (price M charge owner) fuel
          (paid, attachOutcome C M charge owner before outcome)).2) final) :
    Execution initial final ∧ final.Nonnegative ∧ final.total = initial.total := by
  have execution := beforeExecution.append ((resume_admitted C M charge owner fuel paid outcome before
    affordable).append suffix)
  exact ⟨execution, execution.nonnegative_preserved valid, execution.total_conserved⟩

theorem advance_price_bound (bound : Nat)
    (localPrice : ∀ {base index} (state : M.State base index) (request : P.Shape base index),
      charge state request ≤ bound)
    (fuel : Nat) {base : Base} (packet : Packet M C base) :
    (advance M C charge fuel packet).1 ≤ fuel * bound := by
  induction fuel generalizing packet with
  | zero => simp [advance]
  | succ fuel ih =>
      rcases packet with ⟨index, control, state⟩
      cases exposed : C.str base index control with
      | mk shape children =>
          cases shape with
          | inl value => simp [advance, exposed]
          | inr request =>
              dsimp only [withHoles] at children
              simp only [advance, exposed]
              dsimp only [withHoles]
              have rest := ih ⟨_, children (M.step state request).1, (M.step state request).2⟩
              have head := localPrice state request
              nlinarith

/-- A local request price supplies a pre-execution reservation bound. The
financial execution retains the ordinary cursor's actual unfinished outcome;
refunding does not certify semantic completion or erase paid work. -/
theorem reserved_advance (parent : Owner) (distinct : owner ≠ parent)
    (bound : Nat)
    (localPrice : ∀ {base index} (state : M.State base index) (request : P.Shape base index),
      charge state request ≤ bound)
    (fuel : Nat) {base : Base} (packet : Packet M C base)
    (ledger : Ledger Owner) (valid : ledger.Nonnegative) (empty : ledger.balances owner = 0)
    (available : ((fuel * bound : Nat) : ℤ) ≤ ledger.balances parent) :
    let granted := reserved parent owner distinct ledger (fuel * bound)
    let reached := advance (provider M charge owner) C (price M charge owner) fuel
      (attachPacket C M charge owner granted packet)
    let used := ledgerOf C M charge owner reached.2
    let final := (refundTransfer used owner parent distinct).apply used
    Execution ledger final ∧ final.Nonnegative ∧ final.total = ledger.total ∧
      final.balances parent = ledger.balances parent - ((advance M C charge fuel packet).1 : ℤ) ∧
      final.balances owner = 0 ∧
      final.spent = ledger.spent + ((advance M C charge fuel packet).1 : ℤ) := by
  dsimp only
  rw [advance_exact, ledgerOf_attachOutcome]
  change
    Execution ledger (finishReservation parent owner distinct ledger (fuel * bound)
      (charges C M charge fuel packet)) ∧ _
  have bounded : (charges C M charge fuel packet).sum ≤ fuel * bound := by
    rw [charges_sum]
    exact advance_price_bound C M charge bound localPrice fuel packet
  have execution := reservation_execution parent owner distinct ledger (fuel * bound)
    (charges C M charge fuel packet) valid empty available bounded
  refine ⟨execution, execution.nonnegative_preserved valid, execution.total_conserved, ?_,
    reservation_final_child _ _ _ _ _ _, ?_⟩
  · simpa only [finishReservation, charges_sum] using
      reservation_final_parent parent owner distinct ledger (fuel * bound)
        (charges C M charge fuel packet) empty
  · simpa only [finishReservation, charges_sum] using
      reservation_spent parent owner distinct ledger (fuel * bound)
        (charges C M charge fuel packet)

/-- A copied positive refund movement is not admitted at its post-refund
ledger. Recomputing a full refund there transfers zero, rather than paying
the old unspent balance twice. -/
theorem positive_refund_not_replayable (ledger : Ledger Owner) (parent : Owner)
    (distinct : owner ≠ parent) (positive : 0 < ledger.balances owner) :
    ¬ (refundTransfer ledger owner parent distinct).Admissible
      ((refundTransfer ledger owner parent distinct).apply ledger) := by
  intro admitted
  have funded := admitted.funded
  rw [Transfer.balance_at_source] at funded
  change ledger.balances owner ≤ ledger.balances owner - ledger.balances owner at funded
  omega

namespace Controls

open Mettapedia.GSLT.Logic.AbstractSeparationLogic

def faultStep (state : Nat) (_ : Unit) : Nat × Except Unit Nat := (state + 1, .error ())
abbrev faultProvider := PrimitiveProgram.provider faultStep
abbrev faultClient := PrimitiveProgram.client Unit (fun _ => Nat) Nat Unit
def faultPrice : Charge faultProvider := PrimitiveProgram.charge (fun _ _ => 4) faultStep
def faultPacket : Packet faultProvider faultClient PUnit.unit :=
  ⟨PUnit.unit, .ok (.call () fun value => .ret value), 0⟩
def faultBank : Ledger Nat := ⟨Finsupp.single 1 4, 0⟩

/-- A primitive returns a genuine error after changing its world. Its request
is still paid, and the financial erasure retains that exact error and world. -/
theorem a_faulted_request_is_not_free :
    let reached := advance (provider faultProvider faultPrice 1) faultClient
      (price faultProvider faultPrice 1) 2
      (attachPacket faultClient faultProvider faultPrice 1 faultBank faultPacket)
    reached.1 = 4 ∧
      (ledgerOf faultClient faultProvider faultPrice 1 reached.2).spent = 4 ∧
      (ledgerOf faultClient faultProvider faultPrice 1 reached.2).balances 1 = 0 ∧
      PrimitiveProgram.readOutcome faultStep
        ((forget faultProvider faultPrice 1).outcome faultClient reached.2) =
          (.inl (.error ()), 1) := by
  dsimp only
  refine ⟨rfl, ?_, ?_, rfl⟩
  · rw [advance_spent]
    rfl
  · rw [advance_balance]
    rw [show (advance faultProvider faultClient faultPrice 2 faultPacket).1 = 4 from rfl]
    norm_num [faultBank]

end Controls

end
end Lease

end Mettapedia.Machines.Cursor
