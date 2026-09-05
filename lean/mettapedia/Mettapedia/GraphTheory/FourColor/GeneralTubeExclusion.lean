import Mettapedia.GraphTheory.FourColor.GeneralTubeChain
import Mettapedia.GraphTheory.FourColor.TubeCorridorExclusion

/-!
# No long periodic corridor of any shape in a least counterexample

The exclusion theorem of `TubeCorridorExclusion`, for chains of copies of an
arbitrary slab shape `T` whose relation stabilises at index `m`: literal shore
nodes whose vertex sides form such a chain of `n` slabs number at most
`m + k!·k!·(6w+1)`.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace TubeSlab

open GoertzelV24RotationCutDartDecomposition
open GoertzelV24OpenTangleComposition
open GoertzelV24PhysicalClosedCountBridge
open GoertzelV24ClosedCountReplacement
open GoertzelV24ConnectedEdgeShoreStructuralData
open GoertzelV24MajorityShoreNormalizedState
open GoertzelV24NormalizedTaitSupport
open GoertzelV24NormalizedSeamState
open GoertzelV24MajorityShoreStateDescent
open GoertzelV24ShoreStateDescent
open GoertzelV24RawNooseCountPumping
open GoertzelV24TwoEdgeCutMinimality

universe u

variable {V : Type u} [Fintype V] [DecidableEq V] {k : Nat} [NeZero k]

theorem sideWords_congr {E : Type u} [Fintype E] [DecidableEq E] {RS : RotationSystem.{u, u, u} V E}
    {p q : V → Prop} (h : p = q) (e : Fin k ≃ BoundaryDart RS p) :
    sideWords p e = sideWords q (e.trans (castBoundary h)) := by
  subst h
  rfl

theorem TubeOf.sideWords_eq_of_le {E : Type u} [Fintype E] [DecidableEq E]
    {RS : RotationSystem.{u, u, u} V E} {Vt It : Type u}
    {T : TwoSidedOpenTangleData Vt It (Fin k) (Fin k)} {m : Nat}
    (hstab : ∀ W : Set (Fin k → Color), (relImage T)^[m + 1] W = (relImage T)^[m] W)
    {inner : V → Prop} {n : Nat} (t : TubeOf RS T inner n) (hc : t.Coherent) (j : Nat)
    (hn : m + j ≤ n) :
    sideWords (t.side (m + j)) (t.sideEquiv (m + j)) = sideWords (t.side m) (t.sideEquiv m) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show m + (j + 1) = m + 1 + j by omega, TubeOf.sideWords_stable hstab t hc j (by omega)]
    exact ih (by omega)

section Nodes

variable {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]

local instance gtNodesEdgeSetFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance gtNodesEdgeSetDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable {rotation : SimpleGraphDartRotation.Data G}

/-- membership in a node's support is membership of a word in the tube-coordinate side words -/
theorem mem_support_iff_sideWords (shore : Finset G.edgeSet)
    (outer : RetainedDart rotation.toRotationSystem (majorityRetainedKeep G shore))
    (hw : boundaryWidth rotation shore = k)
    {side : V → Prop} (hkeep : majorityRetainedKeep G shore = side)
    (e : Fin k ≃ BoundaryDart rotation.toRotationSystem side) (word : CutWord (StandardPort.{u} k)) :
    word ∈ (normalizedState rotation shore outer k hw).support ↔
      (fun i => cutWordColor word (sigma rotation shore hw hkeep e i)) ∈ sideWords side e := by
  rw [mem_normalizedState_support_iff]
  simp only [sideWords, Set.mem_setOf_eq]
  rw [← sideSupport_congr hkeep.symm]
  constructor
  · intro h
    convert h using 2
    simp [sigma, Equiv.apply_symm_apply]
  · intro h
    convert h using 2
    simp [sigma, Equiv.apply_symm_apply]

/-- **No long periodic corridor of any shape.** -/
theorem le_of_tubeOf_nodes
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    {w : Nat} {Vt It : Type u} {T : TwoSidedOpenTangleData Vt It (Fin k) (Fin k)} {m : Nat}
    (hstab : ∀ W : Set (Fin k → Color), (relImage T)^[m + 1] W = (relImage T)^[m] W)
    {inner : V → Prop} {n : Nat}
    (t : TubeOf rotation.toRotationSystem T inner n) (hc : t.Coherent)
    (nodes : Fin (n + 1) → LiteralShoreNode rotation k w)
    (hkeep : ∀ r : Fin (n + 1), majorityRetainedKeep G (nodes r).shore = t.side r)
    (hnested : ∀ r r' : Fin (n + 1), r < r' → (nodes r).shore ⊂ (nodes r').shore) :
    n + 1 - m ≤ Nat.factorial k * (Nat.factorial k * (6 * w + 1)) := by
  by_contra hlt
  have hlt : Nat.factorial k * (Nat.factorial k * (6 * w + 1)) < n + 1 - m := Nat.lt_of_not_le hlt
  let idx : Fin (n + 1 - m) → Fin (n + 1) := fun j => ⟨m + j, by omega⟩
  have hw : ∀ r : Fin (n + 1), boundaryWidth rotation (nodes r).shore = k := fun r =>
    boundaryWidth_eq_of_equiv rotation _ ((t.sideEquiv r).trans (castBoundary (hkeep r).symm))
  let f : Fin (n + 1 - m) → Carrier.{u} k w := fun j =>
    (sigma rotation (nodes (idx j)).shore (hw _) (hkeep (idx j)) (t.sideEquiv (idx j)),
      (normalizedState rotation (nodes (idx j)).shore (nodes (idx j)).innerOuter k (hw _)).hubRotation,
      shoreCardPhase w (nodes (idx j)).shore)
  have hcard : Fintype.card (Carrier.{u} k w) < Fintype.card (Fin (n + 1 - m)) := by
    rw [card_carrier, Fintype.card_fin]; exact hlt
  obtain ⟨j, j', hne, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hstate : ∀ a b : Fin (n + 1 - m), f a = f b →
      (nodes (idx a)).cardPhasedState = (nodes (idx b)).cardPhasedState := by
    intro a b hab
    simp only [f, Prod.mk.injEq] at hab
    obtain ⟨hσ, hhub, hphase⟩ := hab
    unfold LiteralShoreNode.cardPhasedState LiteralShoreNode.state
    rw [boundedNormalizedState_eq_of_width rotation _ _ _ (hw (idx a)),
      boundedNormalizedState_eq_of_width rotation _ _ _ (hw (idx b)), hphase]
    congr 2
    apply State.ext' hhub
    ext word
    rw [mem_support_iff_sideWords _ (nodes (idx a)).innerOuter (hw _) (hkeep (idx a))
        (t.sideEquiv (idx a)),
      mem_support_iff_sideWords _ (nodes (idx b)).innerOuter (hw _) (hkeep (idx b))
        (t.sideEquiv (idx b)), hσ]
    have hside : sideWords (t.side (idx a)) (t.sideEquiv (idx a)) =
        sideWords (t.side (idx b)) (t.sideEquiv (idx b)) := by
      show sideWords (t.side (m + a)) (t.sideEquiv (m + a)) =
        sideWords (t.side (m + b)) (t.sideEquiv (m + b))
      rw [TubeOf.sideWords_eq_of_le hstab t hc a (by omega),
        TubeOf.sideWords_eq_of_le hstab t hc b (by omega)]
    rw [hside]
  rcases lt_or_gt_of_ne hne with hjj | hjj
  · exact cardPhasedState_ne_of_ssubset rotation minimal (nodes (idx j')) (nodes (idx j))
      (hnested _ _ (by simp only [idx, Fin.mk_lt_mk]; omega)) (hstate j' j hf.symm)
  · exact cardPhasedState_ne_of_ssubset rotation minimal (nodes (idx j)) (nodes (idx j'))
      (hnested _ _ (by simp only [idx, Fin.mk_lt_mk]; omega)) (hstate j j' hf)

end Nodes

end TubeSlab
end Mettapedia.GraphTheory.FourColor
