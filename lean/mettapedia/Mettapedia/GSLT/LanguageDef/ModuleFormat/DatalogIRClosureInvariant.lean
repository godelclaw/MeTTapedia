import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClosureReady

/-! Live closure states retain a closed provider and a ready shared search.
Fault states stop immediately; they do not need an executable search state. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClosureMachine

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open Complete.Footprint

def Ready (prepared : Executable.Prepared) (machine : Machine prepared) : Prop :=
  machine.fault = none → closed prepared machine.facts = true ∧
    CompleteExecution.SearchReady [] (.base "DlStatement")
      (declaredFootprint (Executable.plan prepared machine.facts)) machine.run

theorem begin_ready (prepared : Executable.Prepared)
    (admitted : (Executable.plan prepared prepared.seedFacts.eraseDups).complete = true) :
    Ready prepared (begin prepared) := by
  have closed : ClosureMachine.closed prepared prepared.seedFacts.eraseDups = true :=
    (GeneralExecutionAdmission.complete_snapshot_checks admitted).2.2.1
  intro _
  exact ⟨closed,initial_search_ready prepared _ _ admitted closed⟩

theorem tick_ready (prepared : Executable.Prepared) (before : List Pattern)
    (admitted : (Executable.plan prepared before).complete = true) (machine : Machine prepared)
    (ready : Ready prepared machine) (quantum : Nat) : Ready prepared (tick prepared machine quantum) := by
  unfold tick
  split
  · exact ready
  · rename_i active
    have noFault : machine.fault = none := by
      cases found : machine.fault with
      | none => rfl
      | some fault => simp [found] at active
    obtain ⟨closed,searchReady⟩ := ready noFault
    have scope := (admitted_scope prepared before machine.facts admitted closed).1
    have resumed : CompleteExecution.SearchReady [] (.base "DlStatement")
        (declaredFootprint (Executable.plan prepared machine.facts))
        ((search prepared machine.facts).resume machine.run quantum) :=
      CompleteExecution.searchReady_rounds scope quantum searchReady
    dsimp only
    split
    · intro _
      exact ⟨closed,resumed⟩
    · try dsimp only
      split
      · intro impossible
        cases impossible
      · rename_i facts keys committed
        try dsimp only
        split
        · intro _
          exact ⟨closed,resumed⟩
        · split
          · rename_i nextClosed
            intro _
            exact ⟨nextClosed,initial_search_ready prepared before facts admitted nextClosed⟩
          · intro impossible
            cases impossible

theorem advance_ready (prepared : Executable.Prepared) (before : List Pattern)
    (admitted : (Executable.plan prepared before).complete = true) (machine : Machine prepared)
    (ready : Ready prepared machine) (ticks quantum : Nat) : Ready prepared (advance prepared ticks quantum machine) := by
  induction ticks generalizing machine with
  | zero => exact ready
  | succ ticks ih => exact ih (tick prepared machine quantum) (tick_ready prepared before admitted machine ready quantum)

#print axioms begin_ready
#print axioms tick_ready
#print axioms advance_ready

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClosureMachine
