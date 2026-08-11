import Mettapedia.Logic.LP.RuntimeException
import Mettapedia.Logic.LP.RuntimeMaterializeSoundness

/-!
# Exception packet soundness

The durable exception protocol reuses canonical finite readback and canonical
term materialization.  This module connects those two already-executable
mechanisms: installing a packet extends the supplied memory and its returned
root reads back as the packet's injectively freshened term.
-/

namespace Mettapedia.Logic.LP
namespace RuntimeException

open RuntimeTerm RuntimeReadback
open RuntimeUnificationSoundness

/-- Packet installation is an exact finite-term round trip through the one
canonical heap representation. -/
theorem Packet.install_roundtrip [DecidableEq σ.scoped.vars]
    {packet : Packet σ} {memory : Memory σ.scoped} {nextScope : Nat}
    {installed : Installed σ}
    (hInstall : packet.install memory nextScope = .ok installed) :
    Extends memory installed.memory ∧
      Heap.readTerm installed.memory.heap installed.root =
        .ok (packet.freshTerm nextScope) ∧
      Heap.WellFormed installed.memory.heap := by
  simp only [Packet.install] at hInstall
  cases hMaterialize : RuntimeMaterialize.materializeTerm memory
      (packet.freshTerm nextScope) with
  | error error => simp [hMaterialize] at hInstall
  | ok result =>
      simp [hMaterialize] at hInstall
      cases hInstall
      obtain ⟨hExtends, hRead, hWellFormed, _⟩ :=
        materializeTerm_roundtrip hMaterialize
      exact ⟨hExtends, hRead, hWellFormed⟩

end RuntimeException
end Mettapedia.Logic.LP
