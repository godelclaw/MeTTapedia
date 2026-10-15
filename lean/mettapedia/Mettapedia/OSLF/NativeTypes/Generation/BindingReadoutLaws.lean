import Mettapedia.OSLF.NativeTypes.Generation.BindingPipeline

/-!
# Independent outgoing readout contracts

All conclusions refer to the independently specified scoped firing relation.
Positive possibilities and universal counterexamples retain actual firing
witnesses. Absence and positive outgoing universals use proved coverage after
the actual matcher and premise agenda has drained without obligations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.BindingPipeline.Installed

open Mettapedia.OSLF.MeTTaIL GeneralPremise

variable (installed : BindingPipeline.Installed)

theorem possibility_proved (source : Source) (predicate : Syntax.Pattern → Bool)
    (state : installed.ExecutionState source)
    (proved : installed.possibility source predicate state = .proved) :
    ∃ target, installed.HasSuccessor source target ∧ predicate target = true := by
  unfold possibility at proved
  split at proved
  · rename_i observed
    obtain ⟨receipt, _, positive⟩ := List.any_eq_true.mp observed
    exact ⟨receipt.target, installed.receipt_sound source receipt, positive⟩
  · split at proved <;> cases proved

theorem outgoingAll_refuted (source : Source) (predicate : Syntax.Pattern → Bool)
    (state : installed.ExecutionState source)
    (refuted : installed.outgoingAll source predicate state = .refuted) :
    ∃ target, installed.HasSuccessor source target ∧ predicate target = false := by
  unfold outgoingAll at refuted
  split at refuted
  · rename_i observed
    obtain ⟨receipt, _, negative⟩ := List.any_eq_true.mp observed
    exact ⟨receipt.target, installed.receipt_sound source receipt,
      by simpa only [Bool.not_eq_true'] using negative⟩
  · split at refuted <;> cases refuted

theorem possibility_refuted (source : Source) (predicate : Syntax.Pattern → Bool) (budget : Nat)
    (refuted : installed.possibility source predicate
      (installed.resume source budget (installed.begin source)) = .refuted) :
    ∀ target, installed.HasSuccessor source target → predicate target = false := by
  unfold possibility at refuted
  split at refuted
  · cases refuted
  · rename_i none
    split at refuted
    · rename_i completed
      have drained := ((Scheduler.complete_iff _).mp completed).1
      intro target possible
      obtain ⟨receipt, member, equal⟩ := List.mem_map.mp
        ((installed.drained_successors source budget drained target).mpr possible)
      have negative : predicate receipt.target = false := by
        cases value : predicate receipt.target with
        | false => rfl
        | true =>
            exact False.elim (none (List.any_eq_true.mpr ⟨receipt, member, value⟩))
      simpa only [equal] using negative
    · cases refuted

theorem outgoingAll_proved (source : Source) (predicate : Syntax.Pattern → Bool) (budget : Nat)
    (proved : installed.outgoingAll source predicate
      (installed.resume source budget (installed.begin source)) = .proved) :
    ∀ target, installed.HasSuccessor source target → predicate target = true := by
  unfold outgoingAll at proved
  split at proved
  · cases proved
  · rename_i none
    split at proved
    · rename_i completed
      have drained := ((Scheduler.complete_iff _).mp completed).1
      intro target possible
      obtain ⟨receipt, member, equal⟩ := List.mem_map.mp
        ((installed.drained_successors source budget drained target).mpr possible)
      have positive : predicate receipt.target = true := by
        cases value : predicate receipt.target with
        | true => rfl
        | false =>
            exact False.elim (none (List.any_eq_true.mpr
              ⟨receipt, member, by simp only [value, Bool.not_false]⟩))
      simpa only [equal] using positive
    · cases proved

theorem unfinished_empty_unknown (source : Source) (predicate : Syntax.Pattern → Bool)
    (state : installed.ExecutionState source) (empty : installed.receipts state = [])
    (unfinished : Scheduler.complete state = false) :
    installed.possibility source predicate state = .unknown ∧
      installed.outgoingAll source predicate state = .unknown := by
  simp only [possibility, outgoingAll, empty, List.any_nil, Bool.false_eq_true,
    if_false, unfinished, and_self]

end Mettapedia.OSLF.NativeTypes.Generation.BindingPipeline.Installed
