import Mettapedia.GraphTheory.FourColor.TubeChain
import Mettapedia.GraphTheory.FourColor.GoertzelV24MajorityShoreStateDescent

/-!
# No long zigzag tube in a least counterexample

Literal shore nodes of the compositional stack whose vertex sides form a
coherent chain of zigzag slabs: past ring `k-1` their supports are stationary
in tube coordinates (`TubeChain`), so their normalised states are determined
by the coordinate map, the hub rotation and the shore-size phase.  A
pigeonhole over those `k!·k!·(6w+1)` values yields two nested nodes with equal
phased state, which the stack's splice forbids.
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
open ZigzagRing
open TubeRingOrbit

universe u

variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable {RS : RotationSystem.{u, u, u} V E} {k : Nat} [NeZero k]

/-! ## Transport along an equality of sides -/

/-- transport boundary darts along an equality of sides -/
def castBoundary {p q : V → Prop} (h : p = q) : BoundaryDart RS p ≃ BoundaryDart RS q :=
  h ▸ Equiv.refl _

theorem sideSupport_congr {p q : V → Prop} (h : p = q) (f : BoundaryDart RS q → Color) :
    (fun b => f (castBoundary h b)) ∈ sideSupport RS p ↔ f ∈ sideSupport RS q := by
  subst h
  rfl

theorem sideSet_congr {p q : V → Prop} (h : p = q) (e : Fin k ≃ BoundaryDart RS p) :
    sideSet p e = sideSet q (e.trans (castBoundary h)) := by
  subst h
  rfl

/-! ## Stationarity past ring `k-1` -/

theorem Tube.sideSet_eq_of_le {inner : V → Prop} {n : Nat} (h : stabilizes k = true)
    (t : Tube RS k inner n) (hc : t.Coherent) (j : Nat) (hn : k - 1 + j ≤ n) :
    sideSet (t.side (k - 1 + j)) (t.sideEquiv (k - 1 + j)) =
      sideSet (t.side (k - 1)) (t.sideEquiv (k - 1)) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hk : 0 < k := NeZero.pos k
    have h1 : k - 1 + (j + 1) = k + j := by omega
    rw [h1, Tube.sideSet_stable h t hc j (by omega)]
    exact ih (by omega)

/-! ## The pigeonhole carrier -/

/-- coordinate map, hub rotation, shore-size phase -/
abbrev Carrier (k w : Nat) :=
  (Fin k ≃ StandardPort.{u} k) × Equiv.Perm (StandardPort.{u} k) × Fin (6 * w + 1)

theorem card_carrier (k w : Nat) :
    Fintype.card (Carrier.{u} k w) = Nat.factorial k * (Nat.factorial k * (6 * w + 1)) := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_equiv Equiv.ulift.symm,
    Fintype.card_perm, Fintype.card_fin]
  simp [StandardPort, Fintype.card_ulift, Fintype.card_fin]

/-! ## Nodes whose sides are tube sides -/

section Nodes

variable {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]

local instance nodesEdgeSetFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance nodesEdgeSetDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable (rotation : SimpleGraphDartRotation.Data G)

/-- a side with a `Fin k`-labelled boundary has boundary width `k` -/
theorem boundaryWidth_eq_of_equiv (shore : Finset G.edgeSet)
    (e : Fin k ≃ BoundaryDart rotation.toRotationSystem (majorityRetainedKeep G shore)) :
    boundaryWidth rotation shore = k := by
  unfold boundaryWidth
  rw [Fintype.card_congr e.symm, Fintype.card_fin]

/-- the bounded state at exact width `k` -/
theorem boundedNormalizedState_eq_of_width (shore : Finset G.edgeSet)
    (outer : RetainedDart rotation.toRotationSystem (majorityRetainedKeep G shore))
    (hbound : boundaryWidth rotation shore ≤ k) (hw : boundaryWidth rotation shore = k) :
    boundedNormalizedState rotation shore outer k hbound =
      ⟨⟨k, Nat.lt_succ_self k⟩, normalizedState rotation shore outer k hw⟩ := by
  unfold boundedNormalizedState
  subst hw
  rfl

/-- membership in a node's support, read on the side -/
theorem mem_normalizedState_support_iff (shore : Finset G.edgeSet)
    (outer : RetainedDart rotation.toRotationSystem (majorityRetainedKeep G shore))
    (hw : boundaryWidth rotation shore = k) (word : CutWord (StandardPort.{u} k)) :
    word ∈ (normalizedState rotation shore outer k hw).support ↔
      (fun b => cutWordColor word (boundaryCoordinate rotation shore k hw b)) ∈
        sideSupport rotation.toRotationSystem (majorityRetainedKeep G shore) := by
  rw [normalizedState_support, mem_normalizedTaitInnerSupport]
  show cutWordColor word ∈ innerSupport (rightClosedPortTangle
    (OpenTangleData.ofVertexSide rotation.toRotationSystem (majorityRetainedKeep G shore) outer)
    (boundaryCoordinate rotation shore k hw).symm) ↔ _
  rw [mem_innerSupport_ofVertexSide_iff]
  simp only [Equiv.symm_symm]

theorem cutWordColor_ne_zero (word : CutWord (StandardPort.{u} k)) (p : StandardPort.{u} k) :
    cutWordColor word p ≠ 0 := (word p).2

/-- the coordinate map of a node relative to tube coordinates -/
noncomputable def sigma (shore : Finset G.edgeSet) (hw : boundaryWidth rotation shore = k)
    {side : V → Prop} (hkeep : majorityRetainedKeep G shore = side)
    (e : Fin k ≃ BoundaryDart rotation.toRotationSystem side) :
    Fin k ≃ StandardPort.{u} k :=
  (e.trans (castBoundary hkeep.symm)).trans (boundaryCoordinate rotation shore k hw)

/-- membership in a node's support is membership of a numeral in the tube-coordinate side set -/
theorem mem_support_iff_sideSet (shore : Finset G.edgeSet)
    (outer : RetainedDart rotation.toRotationSystem (majorityRetainedKeep G shore))
    (hw : boundaryWidth rotation shore = k)
    {side : V → Prop} (hkeep : majorityRetainedKeep G shore = side)
    (e : Fin k ≃ BoundaryDart rotation.toRotationSystem side) (word : CutWord (StandardPort.{u} k)) :
    word ∈ (normalizedState rotation shore outer k hw).support ↔
      encW k (fun i => cutWordColor word (sigma rotation shore hw hkeep e i)) ∈ sideSet side e := by
  rw [mem_normalizedState_support_iff]
  have hnz : ∀ i, (fun i => cutWordColor word (sigma rotation shore hw hkeep e i)) i ≠ 0 :=
    fun i => cutWordColor_ne_zero word _
  simp only [sideSet, Set.mem_setOf_eq, wordOf_encW k _ hnz, encW_lt, true_and]
  rw [← sideSupport_congr hkeep.symm]
  constructor
  · intro h
    convert h using 2
    simp [sigma, Equiv.apply_symm_apply]
  · intro h
    convert h using 2
    simp [sigma, Equiv.apply_symm_apply]

theorem State.ext' {s s' : State.{u} k} (h1 : s.hubRotation = s'.hubRotation)
    (h2 : s.support = s'.support) : s = s' := by
  cases s; cases s'; simp_all

variable {rotation}

/-- **No long zigzag tube in a least counterexample.**  Literal shore nodes whose
vertex sides form a coherent chain of `n` zigzag slabs number at most
`k - 1 + k!·k!·(6w+1)`. -/
theorem le_of_tube_nodes
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    {w : Nat} (hk : stabilizes k = true) {inner : V → Prop} {n : Nat}
    (t : Tube rotation.toRotationSystem k inner n) (hc : t.Coherent)
    (nodes : Fin (n + 1) → LiteralShoreNode rotation k w)
    (hkeep : ∀ r : Fin (n + 1), majorityRetainedKeep G (nodes r).shore = t.side r)
    (hnested : ∀ r r' : Fin (n + 1), r < r' → (nodes r).shore ⊂ (nodes r').shore) :
    n + 2 - k ≤ Nat.factorial k * (Nat.factorial k * (6 * w + 1)) := by
  have hkpos : 0 < k := NeZero.pos k
  by_contra hlt
  have hlt : Nat.factorial k * (Nat.factorial k * (6 * w + 1)) < n + 2 - k := Nat.lt_of_not_le hlt
  -- the nodes past ring `k-1`
  let idx : Fin (n + 2 - k) → Fin (n + 1) := fun j => ⟨k - 1 + j, by omega⟩
  have hw : ∀ r : Fin (n + 1), boundaryWidth rotation (nodes r).shore = k := fun r =>
    boundaryWidth_eq_of_equiv rotation _ ((t.sideEquiv r).trans (castBoundary (hkeep r).symm))
  let f : Fin (n + 2 - k) → Carrier.{u} k w := fun j =>
    (sigma rotation (nodes (idx j)).shore (hw _) (hkeep (idx j)) (t.sideEquiv (idx j)),
      (normalizedState rotation (nodes (idx j)).shore (nodes (idx j)).innerOuter k (hw _)).hubRotation,
      shoreCardPhase w (nodes (idx j)).shore)
  have hcard : Fintype.card (Carrier.{u} k w) < Fintype.card (Fin (n + 2 - k)) := by
    rw [card_carrier, Fintype.card_fin]; exact hlt
  obtain ⟨j, j', hne, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  -- equal phased states for the two nodes
  have hstate : ∀ a b : Fin (n + 2 - k), f a = f b →
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
    rw [mem_support_iff_sideSet rotation _ (nodes (idx a)).innerOuter (hw _) (hkeep (idx a))
        (t.sideEquiv (idx a)),
      mem_support_iff_sideSet rotation _ (nodes (idx b)).innerOuter (hw _) (hkeep (idx b))
        (t.sideEquiv (idx b)), hσ]
    have hside : sideSet (t.side (idx a)) (t.sideEquiv (idx a)) =
        sideSet (t.side (idx b)) (t.sideEquiv (idx b)) := by
      show sideSet (t.side (k - 1 + a)) (t.sideEquiv (k - 1 + a)) =
        sideSet (t.side (k - 1 + b)) (t.sideEquiv (k - 1 + b))
      rw [Tube.sideSet_eq_of_le hk t hc a (by omega), Tube.sideSet_eq_of_le hk t hc b (by omega)]
    rw [hside]
  rcases lt_or_gt_of_ne hne with hjj | hjj
  · exact cardPhasedState_ne_of_ssubset rotation minimal (nodes (idx j')) (nodes (idx j))
      (hnested _ _ (by simp only [idx, Fin.mk_lt_mk]; omega)) (hstate j' j hf.symm)
  · exact cardPhasedState_ne_of_ssubset rotation minimal (nodes (idx j)) (nodes (idx j'))
      (hnested _ _ (by simp only [idx, Fin.mk_lt_mk]; omega)) (hstate j j' hf)

end Nodes

end TubeSlab
end Mettapedia.GraphTheory.FourColor
