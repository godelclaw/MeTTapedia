import Mettapedia.GraphTheory.FourColor.CubicRotationByteCertificate
import Mettapedia.GraphTheory.FourColor.DualTruncateConstructionGSLT

/-!
# Exact representation adapters for compact dual-and-truncate inputs

The retained vertex permutation and local cyclic offsets determine a dart
bijection. Its compatibility check includes every opposite dart. Vertex and
rotation compatibility follow algebraically, so the saved target receives
the uniform reconstruction rather than a table of target colourings.
-/

namespace Mettapedia.GraphTheory.FourColor.DualTruncateByteCertificate

open CubicRotationByteCertificate GoertzelV24FiniteTransitionWeakSelfLoop
open DualTruncateColoring
open GoertzelV24FaceDualConnectedness GoertzelV24TwoEdgeCutMinimality
open TubeSlab.VertexTransfer VertexCodeSourceGeometry SourceVertexCodeTrace
open VertexConstructionGSLT

structure Adapter (n N : Nat) where
  forward : Table
  backward : Table
  offsets : Table

namespace Adapter

variable {n N : Nat} [NeZero n] [NeZero N] (a : Adapter n N)

def vertex (d : Position n) : Fin N := Fin.ofNat N (a.forward.read (index d))
def back (v : Fin N) : Position n := position n (a.backward.read v.val)
def offset (d : Position n) : Fin 3 := Fin.ofNat 3 (a.offsets.read (index d))

def Valid : Prop :=
  a.forward.WellFormed (3 * n) ∧ a.backward.WellFormed N ∧
  a.offsets.WellFormed (3 * n) ∧
  (∀ d : Position n, a.forward.read (index d) < N ∧ a.offsets.read (index d) < 3) ∧
  (∀ v : Fin N, a.backward.read v.val < 3 * n) ∧
  (∀ d, a.back (a.vertex d) = d) ∧ (∀ v, a.vertex (a.back v) = v)

instance : Decidable a.Valid := by unfold Valid; infer_instance

def vertexEquiv (h : a.Valid) : Position n ≃ Fin N where
  toFun := a.vertex
  invFun := a.back
  left_inv := h.2.2.2.2.2.1
  right_inv := h.2.2.2.2.2.2

def dart (x : Position n × Fin 3) : Position N :=
  (a.vertex x.1, x.2 + a.offset x.1)

def dartEquiv (h : a.Valid) : Position n × Fin 3 ≃ Position N where
  toFun := a.dart
  invFun x := (a.back x.1, x.2 - a.offset (a.back x.1))
  left_inv := by
    rintro ⟨d, i⟩
    simp [dart, h.2.2.2.2.2.1 d]
  right_inv := by
    rintro ⟨v, i⟩
    simp [dart, h.2.2.2.2.2.2 v]

variable {m M : Nat} [NeZero m] [NeZero M]
  (source : CubicRotationByteCertificate.Code n m) (hs : source.Valid)
  (target : CubicRotationByteCertificate.Code N M)

/-- The finite check preserves all edge pairs of the literal construction. -/
def Compatible : Prop :=
  ∀ x : Position n × Fin 3,
    a.dart (flip (source.rotation hs) x) = target.mate (a.dart x)

instance : Decidable (a.Compatible source hs target) := by
  unfold Compatible
  infer_instance

theorem alpha_compatible (ha : a.Valid) (ht : target.Valid)
    (hc : a.Compatible source hs target) (x : (rotation (source.rotation hs)).D) :
    a.dartEquiv ha ((rotation (source.rotation hs)).alpha x) =
      (target.rotation ht).alpha (a.dartEquiv ha x) := hc x

theorem vertex_compatible (ha : a.Valid) (ht : target.Valid)
    (x : (rotation (source.rotation hs)).D) :
    a.vertexEquiv ha ((rotation (source.rotation hs)).vertOf x) =
      (target.rotation ht).vertOf (a.dartEquiv ha x) := rfl

theorem rotation_compatible (ha : a.Valid) (ht : target.Valid)
    (x : (rotation (source.rotation hs)).D) :
    a.dartEquiv ha ((rotation (source.rotation hs)).rho x) =
      (target.rotation ht).rho (a.dartEquiv ha x) := by
  rcases x with ⟨d, i⟩
  change (a.vertex d, (i + 1) + a.offset d) =
    (a.vertex d, (i + a.offset d) + 1)
  exact Prod.ext rfl (by ac_rfl)

/-- The target witness is obtained from the uniform source reconstruction. -/
theorem tait (ha : a.Valid) (ht : target.Valid)
    (hc : a.Compatible source hs target) (word : ByteArray)
    (hw : ProperWord source word) : RotationSystemTaitColorable (target.rotation ht) :=
  DualTruncateConstructionGSLT.tait_relabelled (source.rotation hs)
    (target.rotation ht) (a.dartEquiv ha) (a.vertexEquiv ha)
    (a.alpha_compatible source hs target ha ht hc)
    (a.vertex_compatible source hs target ha ht)
    (threeVertexColoring source hs word hw)

/-- Compatible choices are reconstructed on every complete saved-target sweep. -/
theorem supported_route (ha : a.Valid) (ht : target.Valid)
    (hc : a.Compatible source hs target) (word : ByteArray)
    (hw : ProperWord source word) (order : List (Fin N)) (hn : order.Nodup)
    (he : order ≠ []) (hcover : ∀ v, visited order v) :
    VertexConstructionGSLT.colouring.Supports
      (route (encodeClosed (target.cubic ht)
        (RotationSystemExactTransport.rotationCyclic
          (rotation (source.rotation hs)) (target.rotation ht)
          (a.dartEquiv ha) (a.vertexEquiv ha)
          (a.vertex_compatible source hs target ha ht)
          (a.rotation_compatible source hs target ha ht)
          (DualTruncateConstructionGSLT.rotationCyclic (source.rotation hs)))
        order hn he hcover).trace) Fin.elim0 Fin.elim0 :=
  (SourceConstructionGSLT.encoded_support_iff (target.cubic ht)
    (RotationSystemExactTransport.rotationCyclic
      (rotation (source.rotation hs)) (target.rotation ht)
      (a.dartEquiv ha) (a.vertexEquiv ha)
      (a.vertex_compatible source hs target ha ht)
      (a.rotation_compatible source hs target ha ht)
      (DualTruncateConstructionGSLT.rotationCyclic (source.rotation hs)))
    order hn he hcover).mpr (a.tait source hs target ha ht hc word hw)

/-- The certified representation supplies both its cyclic-order proof and
compatible construction witnesses; no complete route is supplied as input. -/
theorem supported_route_exists (ha : a.Valid) (ht : target.Valid)
    (hc : a.Compatible source hs target) (word : ByteArray)
    (hw : ProperWord source word) (order : List (Fin N)) (hn : order.Nodup)
    (he : order ≠ []) (hcover : ∀ v, visited order v) :
    ∃ cyclic : VertexRotationCyclic (target.rotation ht),
      VertexConstructionGSLT.colouring.Supports
        (route (encodeClosed (target.cubic ht) cyclic order hn he hcover).trace)
        Fin.elim0 Fin.elim0 :=
  ⟨_, a.supported_route source hs target ha ht hc word hw order hn he hcover⟩

end Adapter
end Mettapedia.GraphTheory.FourColor.DualTruncateByteCertificate
