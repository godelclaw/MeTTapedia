import FourColor.CfMap
import MettapediaFourColor.HypermapTransport
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# An executable presentation of classical configuration maps

The reference constructs permutations from bijectivity. Its forward maps are
explicit, but its inverse maps use choice. The triangular hypermap identity
already specifies every inverse: each is the composite of the other two maps.
Using those inverses gives an executable presentation, equal to the original
pointed map, for the `R`, `U`, `Y` and `H` construction language.

This changes no graph, rotation or reference dart. In particular, any proved
property of the executable map transports to the reference configuration.
The construction and its interpretation follow Gonthier's configuration
language as formalized in Chris Emery's Lean development.
-/

namespace FourColor.ExecutableConfiguration

open Equiv

/-- The cancellation identity supplies explicit inverses for all three maps. -/
def ofCancel3 {D : Type*} [Finite D] (e n f : D → D)
    (h : ∀ x, n (f (e x)) = x) : Hypermap D where
  edge :=
    { toFun := e
      invFun := n ∘ f
      left_inv := h
      right_inv := (Hypermap.ofCancel3 e n f h).faceK }
  node :=
    { toFun := n
      invFun := f ∘ e
      left_inv := (Hypermap.ofCancel3 e n f h).nodeK
      right_inv := h }
  face :=
    { toFun := f
      invFun := e ∘ n
      left_inv := (Hypermap.ofCancel3 e n f h).faceK
      right_inv := (Hypermap.ofCancel3 e n f h).nodeK }
  node_face_edge := Equiv.ext h

theorem ofCancel3_eq {D : Type*} [Finite D] (e n f : D → D)
    (h : ∀ x, n (f (e x)) = x) :
    ofCancel3 e n f h = Hypermap.ofCancel3 e n f h :=
  Hypermap.ext (Equiv.ext fun _ => rfl) (Equiv.ext fun _ => rfl)
    (Equiv.ext fun _ => rfl)

/-- The actual two-dart starting map with explicit inverse functions. -/
def zero : PointedMap :=
  ⟨Bool, inferInstance, inferInstance,
    ofCancel3 (fun b => !b) (fun b => !b) id (by decide), true⟩

theorem zero_eq : zero = PointedMap.cpmap0 := by
  unfold zero PointedMap.cpmap0 PointedMap.cpmap0Map
  rw [ofCancel3_eq]

/-- Rotate the reference dart using the explicit inverse permutation. -/
def rotate (n : ℕ) (M : PointedMap) : PointedMap :=
  ⟨M.Dart, M.finite, M.decEq, M.map, M.map.ecpRPoint M.point n⟩

theorem rotate_eq (n : ℕ) (M : PointedMap) : rotate n M = M.ecpR n := rfl

/-- Add the two darts of the reference `U` operation. -/
def add (M : PointedMap) : PointedMap :=
  ⟨EcpDart M.Dart, inferInstance, inferInstance,
    ofCancel3 (Hypermap.ecpEdge M.map) (Hypermap.ecpUNode M.map M.point)
      (Hypermap.ecpUFace M.map M.point) (Hypermap.ecpU_cancel3 M.map M.point), .X⟩

theorem add_eq (M : PointedMap) : add M = M.ecpU := by
  unfold add PointedMap.ecpU Hypermap.ecpUMap
  rw [ofCancel3_eq]

/-- Close a face by the reference `N` operation. -/
def close (M : PointedMap) : PointedMap :=
  ⟨EcpDart M.Dart, inferInstance, inferInstance,
    ofCancel3 (Hypermap.ecpEdge M.map) (Hypermap.ecpNNode M.map M.point)
      (Hypermap.ecpNFace M.map M.point) (Hypermap.ecpN_cancel3 M.map M.point), .X⟩

theorem close_eq (M : PointedMap) : close M = M.ecpN := by
  unfold close PointedMap.ecpN Hypermap.ecpNMap
  rw [ofCancel3_eq]

/-- The explicit fragment used by the configuration catalogue. -/
inductive Step where
  | rotate (n : ℕ)
  | add
  | fork
  | join
  deriving DecidableEq

def Step.reference : Step → CpStep
  | .rotate n => .R n
  | .add => .U
  | .fork => .Y
  | .join => .H

def Step.apply : Step → PointedMap → PointedMap
  | .rotate n, M => ExecutableConfiguration.rotate n M
  | .add, M => ExecutableConfiguration.add M
  | .fork, M => close (ExecutableConfiguration.add M)
  | .join, M => close (close (ExecutableConfiguration.add M))

/-- Execute the construction from right to left, as in the reference. -/
def evaluate : List Step → PointedMap
  | [] => zero
  | s :: p => s.apply (evaluate p)

/-- Equality of the complete pointed hypermaps, including cyclic order. -/
theorem evaluate_eq (p : List Step) : evaluate p = cpmap (p.map Step.reference) := by
  induction p with
  | nil => exact zero_eq
  | cons s p ih =>
    cases s <;>
      simp only [evaluate, Step.apply, List.map_cons, Step.reference, cpmap, ih,
        rotate_eq, add_eq, close_eq, PointedMap.ecpY, PointedMap.ecpH]

/-- Adding two darts extends any explicit numbering of the old darts. -/
def extendIndex {n : ℕ} {D : Type} (e : Fin n ≃ D) : Fin (n + 2) ≃ EcpDart D :=
  (finSuccEquiv (n + 1)).trans
    ((Equiv.optionCongr ((finSuccEquiv n).trans (Equiv.optionCongr e))).trans
      (EcpDart.equivOption D).symm)

def Step.size : Step → ℕ → ℕ
  | .rotate _, n => n
  | .add, n => n + 2
  | .fork, n => n + 2 + 2
  | .join, n => n + 2 + 2 + 2

def size : List Step → ℕ
  | [] => 2
  | s :: p => s.size (size p)

def Step.index (s : Step) (M : PointedMap) {n : ℕ} (e : Fin n ≃ M.Dart) :
    Fin (s.size n) ≃ (s.apply M).Dart :=
  match s with
  | .rotate _ => e
  | .add => extendIndex e
  | .fork => extendIndex (extendIndex e)
  | .join => extendIndex (extendIndex (extendIndex e))

/-- A bijective numbering, rather than an unchecked array representation. -/
def index : (p : List Step) → Fin (size p) ≃ (evaluate p).Dart
  | [] => finTwoEquiv
  | s :: p => s.index (evaluate p) (index p)

/-- The exact executable hypermap on a finite ordinal. -/
def numbered (p : List Step) : Hypermap (Fin (size p)) :=
  (evaluate p).map.relabel (index p).symm

def point (p : List Step) : Fin (size p) := (index p).symm (evaluate p).point

/-- Numbering retains all colouring witnesses. -/
theorem coloring_iff (p : List Step) (k : Fin (size p) → Color) :
    (numbered p).Coloring k ↔ (evaluate p).map.Coloring (k ∘ (index p).symm) :=
  Hypermap.coloring_relabel (evaluate p).map (index p).symm k

end FourColor.ExecutableConfiguration
