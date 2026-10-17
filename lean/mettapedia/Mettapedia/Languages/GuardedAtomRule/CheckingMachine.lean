import Mettapedia.Languages.GuardedAtomRule.Evidence
import Mettapedia.OSLF.NativeTypes.Certificates.DerivationGraph
import Mettapedia.Machines.Cursor.ProofChecking
import Mettapedia.GSLT.Distinction.SimulationComposition

/-!
# Checking realizations of the guarded atom-rule calculus

The original conditional atom judgments define the source calculus. Shared
proof graphs and retained source-address checking realize those judgments;
they do not change this calculus into HE or PeTTa evaluation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.GuardedAtomRule.CheckingMachine

open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.GuardedAtomRule.Evidence
open Mettapedia.Languages.GuardedAtomRule.Evidence.Source
open Mettapedia.OSLF.NativeTypes.Certificates

/-- The guarded atom-rule calculus uses its own existing rule presentation
on the common retained checker. The source rows are its original conditional
atom program; they are not MeTTa evaluation judgments. -/
def checkingObject (rows : List OSLFCore.Atom)
    (source : Mettapedia.Logic.DerivationGraph.BorrowedCursor.Store
      Judgment (presentation rows).Rule Nat) :=
  Mettapedia.GSLT.Distinction.ProductiveBlocks.ObservedMachine.of
    (Mettapedia.Machines.Cursor.ProofChecking.machine (presentation rows).ruleWitness source)

/-- A common-cursor root has the original guarded atom-rule meaning. -/
theorem checked_root_meaning (rows : List OSLFCore.Atom)
    (source : Mettapedia.Logic.DerivationGraph.BorrowedCursor.Store
      Judgment (presentation rows).Rule Nat)
    (cursor : Mettapedia.Logic.DerivationGraph.BorrowedCursor.CheckedCursor
      (presentation rows).ruleWitness source)
    (address : Nat) (judgment : Judgment)
    (found : Mettapedia.Logic.DerivationGraph.BorrowedCursor.rootAt cursor.state address =
      some judgment) : Meaning rows judgment := by
  obtain ⟨schedule, checked⟩ := cursor.checkedPrefix
  have derived := Mettapedia.Logic.DerivationGraph.BorrowedCursor.root_derivable
    (presentation rows).ruleWitness source schedule cursor.state checked address judgment found
  obtain ⟨proof⟩ := (Presentation.nonempty_derivation_iff_derives (presentation rows) judgment).mpr derived
  exact derivation_sound rows proof

/-- Coverage refers to the original conditional atom calculus and preserves
the difference between shared graph data and its semantic judgment. -/
theorem meaning_iff_common_graph (rows : List OSLFCore.Atom) (judgment : Judgment) :
    Meaning rows judgment ↔
      ∃ (nodes : List (Mettapedia.Logic.DerivationGraph.Node Judgment
          (presentation rows).Rule Nat)) (cache : Array Judgment) (root : Nat),
        Mettapedia.Logic.DerivationGraph.replay (presentation rows).ruleWitness nodes = some cache ∧
          cache[root]? = some judgment := by
  have exactSource : Meaning rows judgment ↔ Nonempty ((presentation rows).Derivation judgment) :=
    ⟨meaning_complete rows judgment, fun ⟨proof⟩ => derivation_sound rows proof⟩
  exact exactSource.trans
    (PresentationGraph.nonempty_derivation_iff_graph (P := presentation rows) (0 : Nat) judgment)

end Mettapedia.Languages.GuardedAtomRule.CheckingMachine
