import Mettapedia.GraphTheory.FourColor.GeneralTubeAny
import Mettapedia.GraphTheory.FourColor.SideParity
import Mettapedia.GraphTheory.FourColor.ColorOrbits

/-!
# Nested nodes through the compressed state

A node's normalized support is a set of zero-sum words closed under the six
colour permutations (`SideParity`), hence determined by its orbit keys
(`ColorOrbits`).  Pigeonholing on phase, hub rotation and key set bounds a
strictly nested family of width-`k` nodes by `(6w+1)·k!·2^(orbitCount k)`:
`3809280` at width 5, `37·720·2^31` at width 6.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace TubeSlab

open GoertzelV24ConnectedEdgeShoreMajority
open GoertzelV24ConnectedEdgeShoreStructuralData
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24OpenTangleComposition
open GoertzelV24PhysicalClosedCountBridge
open GoertzelV24ClosedCountReplacement
open GoertzelV24MajorityShoreNormalizedState
open GoertzelV24NormalizedTaitSupport
open GoertzelV24NormalizedSeamState
open GoertzelV24MajorityShoreStateDescent
open GoertzelV24ShoreStateDescent
open GoertzelV24RawNooseCountPumping
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph ZigzagRing ColorOrbits

universe u

/-! ## Digits of a Tait cut word -/

section Digits

variable {k : Nat}

/-- the digit word of a Tait cut word -/
def toDigits (w : CutWord (StandardPort.{u} k)) : DWord k :=
  fun i => ⟨idx (w (ULift.up i)).1, idx_lt _⟩

theorem toDigits_injective : Function.Injective (toDigits (k := k)) := by
  intro w w' h
  funext p
  have hp := congrFun h p.down
  simp only [toDigits, Fin.mk.injEq] at hp
  have h1 := congrArg col hp
  rw [col_idx (w (ULift.up p.down)).2, col_idx (w' (ULift.up p.down)).2] at h1
  exact Subtype.ext h1

theorem csum_toDigits (w : CutWord (StandardPort.{u} k)) :
    csum (toDigits w) = ∑ p : StandardPort.{u} k, (w p).1 := by
  unfold csum toDigits
  rw [← Equiv.sum_comp Equiv.ulift.symm (fun p => (w p).1)]
  exact Finset.sum_congr rfl fun i _ => col_idx (w _).2

/-- the inverse table of the six permutations -/
def pinv : Fin 6 → Fin 6 := ![0, 1, 2, 4, 3, 5]

theorem perm_pinv : ∀ a i, perm (pinv a) (perm a i) = i := by decide

theorem perm_pinv' : ∀ a i, perm a (perm (pinv a) i) = i := by decide

/-- the colour bijection of a digit permutation -/
def colorMap (a : Fin 6) (c : Color) : Color :=
  if c = 0 then 0 else col (perm a ⟨idx c, idx_lt c⟩).val

theorem colorMap_colorMap : ∀ a c, colorMap (pinv a) (colorMap a c) = c := by decide

theorem colorMap_colorMap' : ∀ a c, colorMap a (colorMap (pinv a) c) = c := by decide

def colorEquiv (a : Fin 6) : Color ≃ Color where
  toFun := colorMap a
  invFun := colorMap (pinv a)
  left_inv c := colorMap_colorMap a c
  right_inv c := colorMap_colorMap' a c

theorem colorEquiv_zero (a : Fin 6) : colorEquiv a 0 = 0 := by
  show colorMap a 0 = 0; simp [colorMap]

theorem colorEquiv_ne_zero (a : Fin 6) {c : Color} (hc : c ≠ 0) : colorEquiv a c ≠ 0 := fun h =>
  hc ((colorEquiv a).injective (h.trans (colorEquiv_zero a).symm))

/-- a colour permutation applied to a Tait cut word -/
def relabelWord (a : Fin 6) (w : CutWord (StandardPort.{u} k)) : CutWord (StandardPort.{u} k) :=
  fun p => ⟨colorEquiv a (w p).1, colorEquiv_ne_zero a (w p).2⟩

theorem toDigits_relabelWord (a : Fin 6) (w : CutWord (StandardPort.{u} k)) :
    toDigits (relabelWord a w) = act a (toDigits w) := by
  funext i
  apply Fin.ext
  show idx (colorMap a (w (ULift.up i)).1) = (perm a ⟨idx (w (ULift.up i)).1, _⟩).val
  unfold colorMap
  rw [if_neg (w (ULift.up i)).2, idx_col (Fin.isLt _)]

end Digits

/-! ## The node support is a zero-sum invariant set -/

section Graph

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]
variable {rotation : SimpleGraphDartRotation.Data G} {k : Nat} [NeZero k]

/-- the digit support of a node -/
noncomputable def digitSupport (shore : Finset G.edgeSet)
    (outer : RetainedDart rotation.toRotationSystem (majorityRetainedKeep G shore))
    (hw : boundaryWidth rotation shore = k) : Finset (DWord k) :=
  (normalizedState rotation shore outer k hw).support.image toDigits

theorem csum_eq_zero_of_mem_support (hcubic : rotation.toRotationSystem.IsCubic)
    (shore : Finset G.edgeSet)
    (outer : RetainedDart rotation.toRotationSystem (majorityRetainedKeep G shore))
    (hw : boundaryWidth rotation shore = k) {w : CutWord (StandardPort.{u} k)}
    (h : w ∈ (normalizedState rotation shore outer k hw).support) : csum (toDigits w) = 0 := by
  rw [mem_normalizedState_support_iff] at h
  have hsum := sum_eq_zero_of_mem_sideSupport hcubic h
  rw [csum_toDigits, ← Equiv.sum_comp (boundaryCoordinate rotation shore k hw)]
  exact hsum

theorem relabelWord_mem_support (shore : Finset G.edgeSet)
    (outer : RetainedDart rotation.toRotationSystem (majorityRetainedKeep G shore))
    (hw : boundaryWidth rotation shore = k) (a : Fin 6) {w : CutWord (StandardPort.{u} k)}
    (h : w ∈ (normalizedState rotation shore outer k hw).support) :
    relabelWord a w ∈ (normalizedState rotation shore outer k hw).support := by
  rw [mem_normalizedState_support_iff] at h ⊢
  exact relabel_mem_sideSupport (colorEquiv a) (colorEquiv_zero a) h

theorem digitSupport_zeroSum (hcubic : rotation.toRotationSystem.IsCubic)
    (shore : Finset G.edgeSet)
    (outer : RetainedDart rotation.toRotationSystem (majorityRetainedKeep G shore))
    (hw : boundaryWidth rotation shore = k) :
    ∀ d ∈ digitSupport shore outer hw, csum d = 0 := by
  intro d hd
  obtain ⟨w, hw', rfl⟩ := Finset.mem_image.mp hd
  exact csum_eq_zero_of_mem_support hcubic shore outer hw hw'

theorem digitSupport_invariant (shore : Finset G.edgeSet)
    (outer : RetainedDart rotation.toRotationSystem (majorityRetainedKeep G shore))
    (hw : boundaryWidth rotation shore = k) :
    ∀ a : Fin 6, ∀ d ∈ digitSupport shore outer hw, act a d ∈ digitSupport shore outer hw := by
  intro a d hd
  obtain ⟨w, hw', rfl⟩ := Finset.mem_image.mp hd
  rw [← toDigits_relabelWord]
  exact Finset.mem_image_of_mem _ (relabelWord_mem_support shore outer hw a hw')

/-- **the key set of a node** -/
noncomputable def keySet (shore : Finset G.edgeSet)
    (outer : RetainedDart rotation.toRotationSystem (majorityRetainedKeep G shore))
    (hw : boundaryWidth rotation shore = k) : Finset Nat :=
  (digitSupport shore outer hw).image key

theorem keySet_subset (hcubic : rotation.toRotationSystem.IsCubic) (shore : Finset G.edgeSet)
    (outer : RetainedDart rotation.toRotationSystem (majorityRetainedKeep G shore))
    (hw : boundaryWidth rotation shore = k) : keySet shore outer hw ⊆ keys k := by
  intro x hx
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
  exact mem_keys (digitSupport_zeroSum hcubic shore outer hw d hd)

/-- equal key sets give equal supports -/
theorem support_eq_of_keySet_eq (shore shore' : Finset G.edgeSet)
    (outer : RetainedDart rotation.toRotationSystem (majorityRetainedKeep G shore))
    (outer' : RetainedDart rotation.toRotationSystem (majorityRetainedKeep G shore'))
    (hw : boundaryWidth rotation shore = k) (hw' : boundaryWidth rotation shore' = k)
    (h : keySet shore outer hw = keySet shore' outer' hw') :
    (normalizedState rotation shore outer k hw).support =
      (normalizedState rotation shore' outer' k hw').support := by
  have hd := eq_of_image_key_eq (digitSupport_invariant shore outer hw)
    (digitSupport_invariant shore' outer' hw') h
  exact Finset.image_injective toDigits_injective hd

/-- **Nested width-`k` nodes are few, through the compressed state**: at most
`(6w+1)·k!·2^(orbitCount k)`. -/
theorem le_of_nested_nodes_orbit (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    {w n : Nat} (nodes : Fin (n + 1) → LiteralShoreNode rotation k w)
    (hw : ∀ r, boundaryWidth rotation (nodes r).shore = k)
    (hnested : ∀ r r' : Fin (n + 1), r < r' → (nodes r).shore ⊂ (nodes r').shore) :
    n + 1 ≤ (6 * w + 1) * (Nat.factorial k * 2 ^ orbitCount k) := by
  have hcubic : rotation.toRotationSystem.IsCubic := minimal.spherical.cubic
  by_contra hlt
  have hlt : (6 * w + 1) * (Nat.factorial k * 2 ^ orbitCount k) < n + 1 := Nat.lt_of_not_le hlt
  let f : Fin (n + 1) → Fin (6 * w + 1) × Equiv.Perm (StandardPort.{u} k) × Finset Nat := fun r =>
    (shoreCardPhase w (nodes r).shore,
      (normalizedState rotation (nodes r).shore (nodes r).innerOuter k (hw r)).hubRotation,
      keySet (nodes r).shore (nodes r).innerOuter (hw r))
  let t : Finset (Fin (6 * w + 1) × Equiv.Perm (StandardPort.{u} k) × Finset Nat) :=
    Finset.univ ×ˢ Finset.univ ×ˢ (keys k).powerset
  have hcard : t.card < (Finset.univ : Finset (Fin (n + 1))).card := by
    simp only [t, Finset.card_product, Finset.card_univ, Fintype.card_fin, Fintype.card_perm,
      Fintype.card_ulift, Finset.card_powerset]
    exact hlt
  have hmaps : ∀ r ∈ (Finset.univ : Finset (Fin (n + 1))), f r ∈ t := by
    intro r _
    simp only [t, f, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_powerset]
    exact keySet_subset hcubic _ _ _
  obtain ⟨j, _, j', _, hne, hf⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  have hstate : ∀ a b : Fin (n + 1), f a = f b →
      (nodes a).cardPhasedState = (nodes b).cardPhasedState := by
    intro a b hab
    simp only [f, Prod.mk.injEq] at hab
    obtain ⟨hphase, hhub, hkeys⟩ := hab
    unfold LiteralShoreNode.cardPhasedState LiteralShoreNode.state
    rw [boundedNormalizedState_eq_of_width rotation _ _ _ (hw a),
      boundedNormalizedState_eq_of_width rotation _ _ _ (hw b), hphase]
    congr 2
    exact State.ext' hhub (support_eq_of_keySet_eq _ _ _ _ _ _ hkeys)
  rcases lt_or_gt_of_ne hne with hjj | hjj
  · exact cardPhasedState_ne_of_ssubset rotation minimal (nodes j') (nodes j)
      (hnested _ _ hjj) (hstate j' j hf.symm)
  · exact cardPhasedState_ne_of_ssubset rotation minimal (nodes j) (nodes j')
      (hnested _ _ hjj) (hstate j j' hf)

/-- **Nested good sides of width `k` are few**, compressed. -/
theorem le_of_nested_sides_orbit (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (hk2 : 2 ≤ k) {n : Nat} (side : Fin (n + 1) → (V → Prop))
    (e : ∀ r, Fin k ≃ BoundaryDart rotation.toRotationSystem (side r))
    (hgood : ∀ r, GoodSide (G := G) (side r))
    (hconn : ∀ r, EdgeShoreConnected G (sideShore (side r)))
    (hcconn : ∀ r, EdgeShoreConnected G (ZigzagSlab.compShore (side r)))
    (hnested : ∀ r r' : Fin (n + 1), r < r' → sideShore (G := G) (side r) ⊂ sideShore (side r')) :
    n + 1 ≤ (6 * k + 1) * (Nat.factorial k * 2 ^ orbitCount k) := by
  let nodes : Fin (n + 1) → LiteralShoreNode rotation k k := fun r =>
    mkNode ⟨hgood r, hconn r, hcconn r⟩ (e r) hk2
  refine le_of_nested_nodes_orbit minimal nodes (fun r => ?_) hnested
  exact boundaryWidth_eq_of_equiv rotation _ ((e r).trans (castBoundary (mkNode_keep _ _ _).symm))

/-- width 5: at most `3809280` nested good sides -/
theorem le_of_nested_sides_five (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    {n : Nat} (side : Fin (n + 1) → (V → Prop))
    (e : ∀ r, Fin 5 ≃ BoundaryDart rotation.toRotationSystem (side r))
    (hgood : ∀ r, GoodSide (G := G) (side r))
    (hconn : ∀ r, EdgeShoreConnected G (sideShore (side r)))
    (hcconn : ∀ r, EdgeShoreConnected G (ZigzagSlab.compShore (side r)))
    (hnested : ∀ r r' : Fin (n + 1), r < r' → sideShore (G := G) (side r) ⊂ sideShore (side r')) :
    n + 1 ≤ 3809280 := by
  have := le_of_nested_sides_orbit minimal (by norm_num) side e hgood hconn hcconn hnested
  rwa [orbitCount_five, show (6 * 5 + 1) * (Nat.factorial 5 * 2 ^ 10) = 3809280 by
    norm_num [Nat.factorial]] at this

end Graph

end TubeSlab
end Mettapedia.GraphTheory.FourColor
