import Mettapedia.Machines.Cursor.ProductiveBlocks
import Mettapedia.Machines.Cursor.Sequence

/-!
# Ordered cursor receipts and exact saved packets

Duplicate replies retain distinct source occurrences. Resuming after a reply
continues its own child and provider tail; restarting a provider repeats a
request against the wrong source state. Return inspection emits no receipt.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ProductiveBlocks.Controls

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Sequence

abbrev Answers := fun (_ : Unit) (_ : Unit) => List (Option Nat)

def afterFirst (first : Option Nat) : (protocol Nat).Free Answers () () :=
  Free.node (protocol Nat) () fun second =>
    Free.node (protocol Nat) () fun third =>
      Free.pure (protocol Nat) [first, second, third]

def threePulls : (protocol Nat).Free Answers () () :=
  Free.node (protocol Nat) () afterFirst

def client : Client (P := protocol Nat) (Return := Answers) :=
  CoalgebraicPlans.retainedPlanRealizer

def initial : Packet (tails Nat) client () := ⟨(), threePulls, [7, 7, 9]⟩
def residual : Packet (tails Nat) client () := ⟨(), afterFirst (some 7), [7, 9]⟩

def firstReceipt : Receipt (tails Nat) () := ⟨(), [7, 7, 9], (), some 7⟩
def secondReceipt : Receipt (tails Nat) () := ⟨(), [7, 9], (), some 7⟩
def thirdReceipt : Receipt (tails Nat) () := ⟨(), [9], (), some 9⟩

theorem pause_after_first :
    (machine (tails Nat) client ()).run 1 initial =
      ([firstReceipt], .exhausted residual) := rfl

theorem saved_reply_child_and_tail :
    (Cursor.advance (tails Nat) client (requested Nat) 1 initial).2 =
      .paused residual :=
  saved_packet_exact (tails Nat) client (requested Nat) 1 initial residual
    [firstReceipt] pause_after_first

theorem completed_receipts :
    (machine (tails Nat) client ()).run 4 initial =
      ([firstReceipt, secondReceipt, thirdReceipt],
        .finished ⟨(), [some 7, some 7, some 9], []⟩) := rfl

theorem duplicate_replies_are_distinct_occurrences :
    firstReceipt.reply = secondReceipt.reply ∧
      firstReceipt.before ≠ secondReceipt.before := by
  constructor
  · rfl
  · change ([7, 7, 9] : List Nat) ≠ [7, 9]
    decide

theorem resume_retains_order_and_multiplicity :
    (machine (tails Nat) client ()).run 4 initial =
      ([firstReceipt] ++ ((machine (tails Nat) client ()).run 3 residual).1,
        ((machine (tails Nat) client ()).run 3 residual).2) :=
  resume_after_prefix (tails Nat) client 1 3 initial residual
    [firstReceipt] pause_after_first

theorem three_requests_have_three_charges :
    (machine (tails Nat) client ()).spent
        (price (tails Nat) client (requested Nat)) 4 initial = 3 := rfl

theorem return_emits_no_request :
    ((machine (tails Nat) client ()).run 1
      ⟨(), Free.pure (protocol Nat) [some 7], [9]⟩).1 = [] := rfl

theorem wrong_provider_tail_changes_the_next_reply :
    (((machine (tails Nat) client ()).run 1
      ⟨(), afterFirst (some 7), [7, 8, 9]⟩).1.map (fun event => event.reply)) ≠
      (((machine (tails Nat) client ()).run 1
        ⟨(), afterFirst (some 7), [8, 9]⟩).1.map (fun event => event.reply)) := by
  decide

end Mettapedia.Machines.Cursor.ProductiveBlocks.Controls
