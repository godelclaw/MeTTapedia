import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.IndexedAppendExecution

/-! # Positive and negative controls for the composed program -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.IndexedAppendExecution.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.OSLF.NativeTypes.Decision.Spatial
open Mettapedia.OSLF.NativeTypes.Consumers.IndexedAppend (sizeExactly_admitted)

def value (n : Nat) : Atom := .grounded (.int n)

theorem duplicates_proved (before : Effects.State) :
    ∃ rounds, VerdictCompletes before (BagModel.sizeExactly 2) (sizeExactly_admitted 2)
      [value 7] [value 7] rounds (some true) :=
  (length_iff before 2 [value 7] [value 7]).mpr rfl

theorem missing_copy_refuted (before : Effects.State) :
    ∃ rounds, VerdictCompletes before (BagModel.sizeExactly 2) (sizeExactly_admitted 2)
      [value 7] [] rounds (some false) :=
  (wrong_length_iff before 2 [value 7] []).mpr (by decide)

theorem correct_length_not_refuted (before : Effects.State) (rounds : List Nat) :
    ¬ VerdictCompletes before (BagModel.sizeExactly 2) (sizeExactly_admitted 2)
      [value 7] [value 7] rounds (some false) := by
  intro completed
  exact (wrong_length_iff before 2 [value 7] [value 7]).mp ⟨rounds, completed⟩ rfl

theorem unfinished_true_claim_unknown (before : Effects.State) :
    VerdictCompletes before (BagModel.sizeExactly 2) (sizeExactly_admitted 2)
      [value 7] [value 7] [] none ∧
    ¬ VerdictCompletes before (BagModel.sizeExactly 2) (sizeExactly_admitted 2)
      [value 7] [value 7] [] (some false) :=
  ⟨no_work_completes _ _ _ _ _, no_work_not_decided _ _ _ _ _ false⟩

def initial : Execution.Session := IndexedAppend.session 2 [value 1, value 2]

def checks : List (String × Bool) :=
  [ ("composed-keeps-order", decide (observation [value 1, value 2] initial ≠
      observation [value 2, value 1] initial))
  , ("composed-keeps-copies", decide (observation [value 7, value 7] initial ≠
      observation [value 7] initial))
  , ("composed-unknown-not-refuted", decide (observation [value 1, value 2] initial ≠
      verdictPacket [value 1, value 2] initial (some false)))
  , ("composed-unknown-not-proved", decide (observation [value 1, value 2] initial ≠
      verdictPacket [value 1, value 2] initial (some true)))
  , ("composed-resumes", decide
      (SpatialRuntime.sessionTerm (result (BagModel.sizeExactly 2) (sizeExactly_admitted 2)
        [value 1] [value 2] [3, 29]) = SpatialRuntime.sessionTerm (initial.resume 32))) ]

theorem checks_pass : checks.all Prod.snd = true := by decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.IndexedAppendExecution.Controls
