import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.IndexedAppend

/-! Source, shared-checker and target-strategy controls for append length. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.IndexedAppend.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.OSLF.NativeTypes
open Decision.Spatial

def value (n : Nat) : Atom := .grounded (.int n)

structure Fixture where
  label : String
  left : List Atom
  right : List Atom
  count : Nat
  first : Nat
  more : Nat

def fixtures : List Fixture :=
  [ ⟨"empty", [], [], 0, 1000, 0⟩
  , ⟨"two-values", [value 1], [value 2], 2, 1000, 0⟩
  , ⟨"duplicate-values", [value 7], [value 7], 2, 1000, 0⟩
  , ⟨"too-short", [value 7], [value 7], 1, 1000, 0⟩
  , ⟨"too-long", [value 7], [value 7], 3, 1000, 0⟩
  , ⟨"zero-budget", [value 1], [value 2], 2, 0, 0⟩
  , ⟨"interrupted", [value 1], [value 2], 2, 3, 0⟩
  , ⟨"resumed", [value 1], [value 2], 2, 3, 997⟩
  , ⟨"wide-payload", [value (2^128)], [value (2^128 + 1)], 2, 1000, 0⟩
  , ⟨"payload-order", [value 2], [value 1], 2, 1000, 0⟩ ]

def Fixture.result (test : Fixture) : Execution.Session :=
  ((session test.count (test.left ++ test.right)).resume test.first).resume test.more

def shared (count : Nat) (values : List Atom) (budget : Nat) :=
  Consumers.IndexedAppend.check count (observe values) budget

def checks : List (String × Bool) :=
  [ ("shared-length", decide ((shared 2 [value 1, value 2] 1000).readout = .judgment (.decided true)))
  , ("shared-duplicates", decide ((shared 2 [value 7, value 7] 1000).readout = .judgment (.decided true)))
  , ("shared-missing", decide ((shared 2 [value 7] 1000).readout = .judgment (.decided false)))
  , ("shared-extra", decide ((shared 1 [value 7, value 7] 1000).readout = .judgment (.decided false)))
  , ("shared-unknown", decide ((shared 2 [value 7, value 7] 0).readout = .judgment .unknown))
  , ("shared-resume", decide ((Executable.resume 997 (shared 2 [value 7, value 7] 3)).readout =
      (shared 2 [value 7, value 7] 1000).readout))
  , ("reject-empty-packet", observePacket [] == none)
  , ("reject-two-answers", observePacket [.expression [], .expression []] == none)
  , ("reject-non-array", observePacket [value 7] == none)
  , ("retain-duplicates", observePacket [.expression [value 7, value 7]] == some [marker, marker])
  , ("strategy-resume", Execution.answer (fixtures[7].result.cursor) == some true)
  , ("strategy-unknown", Execution.answer (fixtures[5].result.cursor) == none) ]

theorem duplicate_length : BagModel.holds (BagModel.sizeExactly 2) (observe [value 7, value 7]) :=
  (BagModel.sizeExactly_iff _ _).mpr rfl

theorem missing_copy_refused : ¬ BagModel.holds (BagModel.sizeExactly 2) (observe [value 7]) := by
  rw [BagModel.sizeExactly_iff]
  decide

/-- Length alone cannot establish the ordered-payload contract. -/
theorem changed_payload_same_length :
    observe [value 1, value 2] = observe [value 2, value 1] ∧
      ([value 1, value 2] : List Atom) ≠ [value 2, value 1] := by decide

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.IndexedAppend.Controls
