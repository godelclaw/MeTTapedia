import Mettapedia.GSLT.Dynamics.CollapseAlgebra

/-!
# Receipt erasure at a materialized collection boundary

An ordered value collector does not inspect an occurrence's auxiliary
receipt. Replacing those receipts preserves every answer, its multiplicity
and its position. This permits omitting exports that the collector discards
after answer materialization; it does not permit dropping bindings still
needed to resolve an answer, delayed goal or owned resource.

These are finite observation-stream laws. They do not establish the C
materializer's correctness, resource lifetime or continuation correspondence.
-/

namespace Mettapedia.GSLT.Dynamics.Collapse.Publication

variable {Ans Receipt Receipt' : Type}

/-- Change only auxiliary receipts; retain ordered occurrence payloads. -/
def mapReceipts (f : Receipt → Receipt')
    (observations : List (Obs Ans Receipt)) : List (Obs Ans Receipt') :=
  observations.map fun o => ⟨o.answer, o.multiplicity, f o.receipt⟩

theorem foldCollect_mapReceipts (f : Receipt → Receipt')
    (observations : List (Obs Ans Receipt)) :
    foldStream (Collect Ans Receipt') (mapReceipts f observations) =
      foldStream (Collect Ans Receipt) observations := by
  induction observations with
  | nil => rfl
  | cons o rest ih =>
      simp only [mapReceipts, List.map_cons, foldStream_cons] at ih ⊢
      rw [ih]
      rfl

/-- Equality is two-sided at the collector's exact ordered observation. -/
theorem collect_mapReceipts (f : Receipt → Receipt')
    (observations : List (Obs Ans Receipt)) :
    collapseWith (Collect Ans Receipt') (mapReceipts f observations) =
      collapseWith (Collect Ans Receipt) observations :=
  foldCollect_mapReceipts f observations

theorem mapReceipts_append (f : Receipt → Receipt')
    (left right : List (Obs Ans Receipt)) :
    mapReceipts f (left ++ right) =
      mapReceipts f left ++ mapReceipts f right := by
  simp [mapReceipts]

/-- Materialized repeated answers retain both their repeats and their order. -/
theorem erase_receipts_positive :
    collapseWith (Collect Nat (Option Nat))
      (mapReceipts (fun (_ : Nat) => (none : Option Nat))
        [⟨7, 2, 31⟩, ⟨3, 1, 99⟩]) = [7, 7, 3] := by
  decide

/-- Receipt erasure gives no license to reorder occurrences. -/
theorem reorder_negative :
    collapseWith (Collect Nat Nat) [⟨7, 2, 31⟩, ⟨3, 1, 99⟩] ≠
      collapseWith (Collect Nat Nat) [⟨3, 1, 99⟩, ⟨7, 2, 31⟩] := by
  decide

/-- A consumer that exposes receipts has a stronger observation contract. -/
def CollectWithReceipts (Ans Receipt : Type) :
    CollapseAlgebra (Obs Ans Receipt) (List (Ans × Receipt))
      (List (Ans × Receipt)) where
  zero := []
  emit o := List.replicate o.multiplicity (o.answer, o.receipt)
  combine := (· ++ ·)
  finish := id

theorem receipt_sensitive_negative :
    collapseWith (CollectWithReceipts Nat (Option Nat)) [⟨7, 1, some 31⟩] ≠
      collapseWith (CollectWithReceipts Nat (Option Nat))
        (mapReceipts (fun _ => none) [⟨7, 1, some 31⟩]) := by
  decide

/-- Here the receipt contributes to the answer's meaning, as an unresolved
binding environment would. It cannot be erased before materialization. -/
def ReceiptDependentAnswer :
    CollapseAlgebra (Obs Nat Nat) (List Nat) (List Nat) where
  zero := []
  emit o := List.replicate o.multiplicity (o.answer + o.receipt)
  combine := (· ++ ·)
  finish := id

theorem unresolved_answer_negative :
    collapseWith ReceiptDependentAnswer [⟨0, 1, 7⟩] ≠
      collapseWith ReceiptDependentAnswer
        (mapReceipts (fun _ => 0) [⟨0, 1, 7⟩]) := by
  decide

end Mettapedia.GSLT.Dynamics.Collapse.Publication
