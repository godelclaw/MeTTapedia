import Mettapedia.Machines.Cursor.Protocol
import Mettapedia.GSLT.Distinction.ProductiveBlocks

/-!
# Indexed cursor execution as an ordered labelled run

The cursor scheduler and the labelled finite-run machine have independent
drivers. This adapter preserves the complete reply-indexed packet and records
each actual provider request and reply as an ordered occurrence. Its readback
is the original cursor driver, and its account is the original cursor charge.

A provider transition remains atomic at this interface. Neither the cursor's
inspection budget nor these request receipts bound work inside that transition.
Waiting and failure belong to the chosen protocol's reply and return types.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ProductiveBlocks

open Mettapedia.TypeTheory
open Mettapedia.GSLT.Distinction.ProductiveBlocks

variable {Base : Type} {Index : Base → Type}
variable {P : IndexedPolynomial Base Index}
variable {Return : (base : Base) → Index base → Type}
variable (M : Provider P) (C : Client (P := P) (Return := Return))

/-- A physical request occurrence retains its capability index, source state,
request and selected reply. Equal replies need not be the same occurrence. -/
structure Receipt (base : Base) where
  index : Index base
  before : M.State base index
  request : P.Shape base index
  reply : P.Position request

/-- One cursor inspection is one labelled transition. The provider is invoked
only on the request branch, and its exact reply selects the continuation. -/
def machine (base : Base) :
    Machine (Packet M C base) (Receipt M base)
      (Finished M (Return := Return) base) Empty where
  step packet := some <|
    match C.str base packet.1 packet.2.1 with
    | ⟨.inl value, _⟩ => .finish ⟨packet.1, value, packet.2.2⟩
    | ⟨.inr request, children⟩ =>
        let response := M.step packet.2.2 request
        .publish [⟨packet.1, packet.2.2, request, response.1⟩]
          ⟨_, children response.1, response.2⟩

/-- Recover the original cursor's exact completion or retained packet. -/
def readback {base : Base} :
    Mettapedia.GSLT.Distinction.ProductiveBlocks.Outcome
        (Packet M C base) (Finished M (Return := Return) base) Empty →
      Option (Cursor.Outcome M C base)
  | .finished result => some (.done result)
  | .exhausted packet | .stuck packet => some (.paused packet)
  | .suspended request _ => nomatch request
  | .faulted => none

/-- Both independently recursive drivers retain the same control, provider
state, capability index and completion status after every finite budget. -/
theorem run_readback (charge : Charge M) (fuel : Nat) {base : Base}
    (packet : Packet M C base) :
    readback M C ((machine M C base).run fuel packet).2 =
      some (Cursor.advance M C charge fuel packet).2 := by
  induction fuel generalizing packet with
  | zero => rfl
  | succ fuel ih =>
      rcases packet with ⟨index, control, state⟩
      cases inspected : C.str base index control with
      | mk shape children =>
          cases shape with
          | inl value =>
              simp [Machine.run, machine, inspected, readback, Cursor.advance]
          | inr request =>
              simpa only [Machine.run, machine, inspected, Cursor.advance] using
                ih ⟨_, children (M.step state request).1, (M.step state request).2⟩

/-- A retained labelled-run packet is precisely the packet retained by the
original scheduler, rather than a reconstruction from its delivered replies. -/
theorem saved_packet_exact (charge : Charge M) (fuel : Nat) {base : Base}
    (packet residual : Packet M C base) (events : List (Receipt M base))
    (paused : (machine M C base).run fuel packet = (events, .exhausted residual)) :
    (Cursor.advance M C charge fuel packet).2 = .paused residual := by
  have equal := run_readback M C charge fuel packet
  rw [paused] at equal
  exact (Option.some.inj equal).symm

/-- The scheduler's price is zero on a return inspection and is the provider's
declared charge on a request inspection. -/
def price (charge : Charge M) {base : Base} (packet : Packet M C base) : Nat :=
  match C.str base packet.1 packet.2.1 with
  | ⟨.inl _, _⟩ => 0
  | ⟨.inr request, _⟩ => charge packet.2.2 request

/-- The labelled machine and the original cursor accumulate exactly the same
account, including runs which stop before the client returns. -/
theorem spent_eq_advance (charge : Charge M) (fuel : Nat) {base : Base}
    (packet : Packet M C base) :
    (machine M C base).spent (price M C charge) fuel packet =
      (Cursor.advance M C charge fuel packet).1 := by
  induction fuel generalizing packet with
  | zero => rfl
  | succ fuel ih =>
      rcases packet with ⟨index, control, state⟩
      cases inspected : C.str base index control with
      | mk shape children =>
          cases shape with
          | inl value =>
              simp [Machine.spent, machine, inspected, price, Cursor.advance]
          | inr request =>
              simpa only [Machine.spent, machine, inspected, price, Cursor.advance] using
                congrArg (charge state request + ·)
                  (ih ⟨_, children (M.step state request).1, (M.step state request).2⟩)

/-- Each retained receipt has the charge of the actual source request. -/
def receiptCharge (charge : Charge M) {base : Base} (receipt : Receipt M base) : Nat :=
  charge receipt.before receipt.request

/-- The ordered request history accounts for all and only the cursor's charged
operations. Completion does not insert a request or a charge. -/
theorem receipt_charge_sum (charge : Charge M) (fuel : Nat) {base : Base}
    (packet : Packet M C base) :
    (((machine M C base).run fuel packet).1.map (receiptCharge M charge)).sum =
      (Cursor.advance M C charge fuel packet).1 := by
  induction fuel generalizing packet with
  | zero => rfl
  | succ fuel ih =>
      rcases packet with ⟨index, control, state⟩
      cases inspected : C.str base index control with
      | mk shape children =>
          cases shape with
          | inl value =>
              simp [Machine.run, machine, inspected, Cursor.advance]
          | inr request =>
              simpa [Machine.run, machine, inspected, Cursor.advance,
                receiptCharge] using
                congrArg (charge state request + ·)
                  (ih ⟨_, children (M.step state request).1, (M.step state request).2⟩)

/-- Prefix resumption now uses the same labelled-run law as source answer
streaming, retaining the entire indexed client/provider packet. -/
theorem resume_after_prefix (first second : Nat) {base : Base}
    (packet residual : Packet M C base) (events : List (Receipt M base))
    (paused : (machine M C base).run first packet = (events, .exhausted residual)) :
    (machine M C base).run (first + second) packet =
      (events ++ ((machine M C base).run second residual).1,
        ((machine M C base).run second residual).2) :=
  (machine M C base).established_and_pending first second packet residual events paused

/-- More inspection budget extends the actual request/reply occurrence list. -/
theorem observation_prefix (first second : Nat) {base : Base}
    (packet : Packet M C base) :
    ((machine M C base).observe first packet).Prefix
      ((machine M C base).observe (first + second) packet) :=
  (machine M C base).observe_prefix first second packet

/-- Inspection has no silent transitions at this granularity. Internal
provider execution is outside this claim and needs its own work account. -/
def productive (base : Base) : (machine M C base).Productive where
  rank _ := 0
  silent_decreases := by
    intro packet next stepped
    rcases packet with ⟨index, control, state⟩
    cases inspected : C.str base index control with
    | mk shape children =>
        cases shape <;> simp [machine, inspected] at stepped
  moves packet := by simp [machine]

end Mettapedia.Machines.Cursor.ProductiveBlocks
