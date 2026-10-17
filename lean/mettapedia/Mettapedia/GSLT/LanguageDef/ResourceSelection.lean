import Mettapedia.GSLT.LanguageDef.ResourcePreorder
import Mettapedia.GSLT.LanguageDef.ResourceComputation
import Mettapedia.GSLT.LanguageDef.ResourceExecutionControls
import Mathlib.Order.Preorder.Finite

/-!
# Resource frontiers of qualified checking routes

Every candidate retains its original packet compiler, exact refusal theorem,
and target checker execution. Selection restricts an already qualified finite
family. It does not generate missing adequacy evidence or change the source
authority. The task includes its certificate; this is route selection after
proof discovery, not an automatic proof-search algorithm.

The coordinates distinguish complete target packet symbols, proved translation
and checking clocks, and actual peak cells of the joined execution. They use
the chosen abstract machine and encodings, not native elapsed time or bytes.
The frontier is mathematical: no bound on computing or discovering these
costs is inferred. In particular, measuring a run's peak can require that run.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ResourceTranslation.ResourceSelection

open Turing

/-- Alternatives may have different target theories and physical encodings. -/
structure Route (source : EncodedAuthority) where
  target : EncodedAuthority
  compiler : ExecutedTranslation source.authority target.authority
    source.encoding target.encoding
  exactReplay : compiler.toTranslation.Exact
  checker : CheckerExecution target.authority target.encoding

namespace Route

variable {source : EncodedAuthority}

/-- The selected compiler and checker execute through the original physical
handoff, including refused certificates. -/
noncomputable def implementation (route : Route source) :
    CheckerExecution source.authority source.encoding :=
  route.compiler.thenCheck route.exactReplay route.checker

inductive Coordinate where
  | packetSymbols | translationClock | checkingClock | peakCells
  deriving DecidableEq

abbrev Profile := Coordinate → Nat

noncomputable def profile (route : Route source) (packet : Packet source.authority) : Profile
  | .packetSymbols => (route.target.encoding.encode (route.compiler.packet packet)).length
  | .translationClock => route.compiler.time packet
  | .checkingClock => route.checker.time (route.compiler.packet packet)
  | .peakCells => route.implementation.microPeak packet

/-- Each clock bounds its own original run. It is not merely a supplied score. -/
theorem translation_steps_le (route : Route source) (packet : Packet source.authority) :
    (route.compiler.outputs packet).steps ≤ route.profile packet .translationClock :=
  (route.compiler.outputs packet).steps_le_m

theorem checking_steps_le (route : Route source) (packet : Packet source.authority) :
    (route.checker.outputs (route.compiler.packet packet)).steps ≤
      route.profile packet .checkingClock :=
  (route.checker.outputs (route.compiler.packet packet)).steps_le_m

/-- Joining the clocks pays both passes over the entire intermediate packet. -/
theorem joined_steps_le (route : Route source) (packet : Packet source.authority) :
    (route.implementation.outputs packet).steps ≤
      route.profile packet .translationClock + 2 * route.profile packet .packetSymbols + 2 +
        route.profile packet .checkingClock :=
  (route.implementation.outputs packet).steps_le_m

theorem translation_clock_positive (route : Route source) (packet : Packet source.authority) :
    0 < route.profile packet .translationClock := route.compiler.clock_positive packet

/-- Independently authored source meaning follows from an actual accepting run
of the selected route, regardless of which resource policy selected it. -/
theorem accepted_meaning (route : Route source) (packet : Packet source.authority)
    (run : TM2Outputs route.implementation.tm
      ((source.encoding.encode packet).map route.implementation.inputAlphabet.symm)
      (some ([true].map route.implementation.outputAlphabet.symm))) :
    source.theory.Meaning packet.1 packet.2.1 :=
  route.implementation.accepted_meaning packet run

end Route

open Route

variable {Index : Type} {source : EncodedAuthority}

/-- The filter is exact: a supplied route is feasible precisely when all four
coordinates meet the budget. No scalarization discards a resource dimension. -/
noncomputable def feasible (routes : Index → Route source) (licensed : Finset Index)
    (packet : Packet source.authority) (budget : Profile) : Finset Index := by
  classical
  exact licensed.filter (fun index => (routes index).profile packet ≤ budget)

theorem mem_feasible (routes : Index → Route source) (licensed : Finset Index)
    (packet : Packet source.authority) (budget : Profile) (index : Index) :
    index ∈ feasible routes licensed packet budget ↔
      index ∈ licensed ∧ (routes index).profile packet ≤ budget := by
  classical
  exact Finset.mem_filter

/-- A frontier member has no feasible route that improves some coordinate
without worsening another. Equal-cost routes retain their distinct evidence. -/
def OnFrontier (routes : Index → Route source) (licensed : Finset Index)
    (packet : Packet source.authority) (budget : Profile) (index : Index) : Prop :=
  MinimalFor (fun candidate => candidate ∈ feasible routes licensed packet budget)
    (fun candidate => (routes candidate).profile packet) index

theorem exists_frontier (routes : Index → Route source) (licensed : Finset Index)
    (packet : Packet source.authority) (budget : Profile)
    (nonempty : (feasible routes licensed packet budget).Nonempty) :
    ∃ index, OnFrontier routes licensed packet budget index :=
  (feasible routes licensed packet budget).exists_minimalFor
    (fun candidate => (routes candidate).profile packet) nonempty

theorem frontier_budget (routes : Index → Route source) (licensed : Finset Index)
    (packet : Packet source.authority) (budget : Profile) {index : Index}
    (selected : OnFrontier routes licensed packet budget index) :
    index ∈ licensed ∧ (routes index).profile packet ≤ budget :=
  (mem_feasible routes licensed packet budget index).mp selected.1

theorem frontier_no_strict_improvement (routes : Index → Route source) (licensed : Finset Index)
    (packet : Packet source.authority) (budget : Profile) {index competitor : Index}
    (selected : OnFrontier routes licensed packet budget index)
    (eligible : competitor ∈ feasible routes licensed packet budget) :
    ¬ (routes competitor).profile packet < (routes index).profile packet := by
  intro strict
  exact (not_le_of_gt strict) (selected.2 eligible strict.le)

theorem selected_joined_steps (routes : Index → Route source) (licensed : Finset Index)
    (packet : Packet source.authority) (budget : Profile) {index : Index}
    (selected : OnFrontier routes licensed packet budget index) :
    ((routes index).implementation.outputs packet).steps ≤
      budget .translationClock + 2 * budget .packetSymbols + 2 + budget .checkingClock := by
  have bounded := (frontier_budget routes licensed packet budget selected).2
  have joined := (routes index).joined_steps_le packet
  have translation : (routes index).profile packet .translationClock ≤ budget .translationClock :=
    bounded .translationClock
  have symbols : (routes index).profile packet .packetSymbols ≤ budget .packetSymbols :=
    bounded .packetSymbols
  have checking : (routes index).profile packet .checkingClock ≤ budget .checkingClock :=
    bounded .checkingClock
  omega

theorem selected_peak (routes : Index → Route source) (licensed : Finset Index)
    (packet : Packet source.authority) (budget : Profile) {index : Index}
    (selected : OnFrontier routes licensed packet budget index) :
    (routes index).implementation.microPeak packet ≤ budget .peakCells :=
  (frontier_budget routes licensed packet budget selected).2 .peakCells

/-- More budget cannot remove a previously feasible, qualified route. Its
frontier status can change when a new competitor becomes feasible. -/
theorem feasible_mono (routes : Index → Route source) (licensed : Finset Index)
    (packet : Packet source.authority) {small large : Profile} (increase : small ≤ large) :
    feasible routes licensed packet small ⊆ feasible routes licensed packet large := by
  intro index membership
  obtain ⟨recognized, bounded⟩ := (mem_feasible routes licensed packet small index).mp membership
  exact (mem_feasible routes licensed packet large index).mpr ⟨recognized, bounded.trans increase⟩

/-- An impossible resource request has no feasible route, even for a theorem. -/
theorem zero_translation_budget (routes : Index → Route source) (licensed : Finset Index)
    (packet : Packet source.authority) (budget : Profile) (zero : budget .translationClock = 0) :
    feasible routes licensed packet budget = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro index membership
  have bounded := ((mem_feasible routes licensed packet budget index).mp membership).2
  have positive := (routes index).translation_clock_positive packet
  have bound : (routes index).profile packet .translationClock ≤ budget .translationClock :=
    bounded .translationClock
  omega

namespace Controls

/-- A finite frontier need not contain a route best in every coordinate. -/
def tradeoff (index : Bool) : Fin 2 → Nat :=
  if index then ![1, 10] else ![10, 1]

theorem incomparable : ¬ tradeoff false ≤ tradeoff true ∧ ¬ tradeoff true ≤ tradeoff false := by
  constructor
  · intro h; have := h 0; norm_num [tradeoff] at this
  · intro h; have := h 1; norm_num [tradeoff] at this

theorem no_least_tradeoff : ¬ ∃ chosen : Bool, ∀ competitor, tradeoff chosen ≤ tradeoff competitor := by
  rintro ⟨chosen, least⟩
  cases chosen
  · exact incomparable.1 (least true)
  · exact incomparable.2 (least false)

def booleanSource : EncodedAuthority where
  Kind := Unit
  theory := ExecutionControls.theory
  authority := ExecutionControls.authority
  Alphabet := Bool
  encoding := ExecutionControls.encoding

noncomputable def booleanRoute : Route booleanSource where
  target := booleanSource
  compiler := ExecutedTranslation.ofPolynomial ExecutionControls.compiler
  exactReplay := Translation.exact_identity
  checker := ExecutionControls.implementation

theorem admitted_route_has_frontier :
    ∃ index, OnFrontier (fun (_ : Unit) => booleanRoute) {()}
      (ExecutionControls.packet true) (booleanRoute.profile (ExecutionControls.packet true)) index := by
  apply exists_frontier
  refine ⟨(), (mem_feasible _ _ _ _ _).mpr ?_⟩
  exact ⟨by simp, le_rfl⟩

theorem zero_budget_does_not_refute :
    checkPacket booleanSource.authority (ExecutionControls.packet true) = true ∧
    feasible (fun (_ : Unit) => booleanRoute) {()}
      (ExecutionControls.packet true) (fun _ => 0) = ∅ := by
  exact ⟨rfl, zero_translation_budget _ _ _ _ rfl⟩

end Controls

end Mettapedia.GSLT.LanguageDef.ResourceTranslation.ResourceSelection
