import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence.RholangForms

/-!
# `select` with join arms

Rholang's `select` chooses among branches whose receipts are linear joins:

    select { p₁ <- a & q₁ <- b => P ; r <- c => Q }

`RholangForms` defines it, as the guest library does, by one parked choice over one transform per
arm that takes every bind of the arm:

    select { … arm … } = await (choose (transform (, (take p₁ @ a) (take q₁ @ b)) P) …)

and proves that Rholang's rules and these definitions correspond exactly
(`Rholang.rholang_correspond`), so bisimilarity is preserved and reflected
(`Rholang.bisimilar_rholang_iff`). A select whose arms bind one channel each is the fragment of arms
with no further bind (`Rholang.oneBind`, `Rholang.select_oneBind`).

## Controls

A join arm commits its whole receipt in one step: the select's rule takes the select and one message
per bind (`Controls.join_arm_takes_all`). Encoding a join arm by its first bind alone, as a one-bind
arm would be, identifies a select over a join with a select over a single receive, so that encoding
is not injective and cannot be exact (`Controls.firstBind_not_injective`); the encoding of
`RholangForms` tells them apart (`Controls.encode_separates`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence.Rholang.SelectJoins

open Agents

namespace Controls

/-- A two-channel join arm and a one-bind arm over the same first bind. -/
def joinArm : Arm Nat Unit Unit := ((0, ()), [(1, ())], ())
def singleArm : Arm Nat Unit Unit := ((0, ()), [], ())

/-- **Positive**: the select over a join arm takes the select and one message on each channel, in
one rule. -/
theorem join_arm_takes_all :
    RhoRule (Ch := Nat) (Val := Nat) (fun _ _ => True) (fun _ _ => 0)
      ⟨(([.recv (.select [joinArm]), .msg 0 7, .msg 1 8] : List (RhoLbl Nat Nat Unit Unit)) :
          Multiset (RhoLbl Nat Nat Unit Unit)), 0, 0, fun _ => false⟩ := by
  have := RhoRule.select (Ch := Nat) (Val := Nat) (sat := fun _ _ => True) (body := fun _ _ => 0)
    (arms := [joinArm]) (b := (0, ())) (bs := [(1, ())]) (k := ()) (vals := [7, 8])
    (List.mem_singleton.mpr rfl) (List.Forall₂.cons trivial (List.Forall₂.cons trivial List.Forall₂.nil))
  simpa [msgs] using this

/-- **Positive**: a select over one-bind arms takes the select and one message, as Rholang's
one-bind `select` does. -/
theorem single_arm_takes_one :
    RhoRule (Ch := Nat) (Val := Nat) (fun _ _ => True) (fun _ _ => 0)
      ⟨{.recv (.select ([((0 : Nat), (), ())].map oneBind)), .msg 0 7}, 0, 0, fun _ => false⟩ :=
  select_oneBind (List.mem_singleton.mpr rfl) trivial

/-- The encoding of an arm by its first bind alone. -/
def firstBindTr (a : Arm Nat Unit Unit) : Tr Nat Unit Unit := ⟨asSources .take [a.1], a.2.2⟩

/-- **Negative**: encoded by first binds, a select over a join arm and a select over a single
receive become the same parked choice, so that encoding is not injective. -/
theorem firstBind_not_injective :
    (Agent.choose ([joinArm].map firstBindTr) : Agent (Tr Nat Unit Unit)) =
      Agent.choose ([singleArm].map firstBindTr) ∧
    (Recv.select [joinArm] : Recv Nat Unit Unit) ≠ Recv.select [singleArm] := by
  refine ⟨rfl, ?_⟩
  decide

/-- The encoding of `RholangForms` tells them apart. -/
theorem encode_separates :
    encodeRecv (Recv.select [joinArm] : Recv Nat Unit Unit) ≠ encodeRecv (Recv.select [singleArm]) := by
  decide

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence.Rholang.SelectJoins
