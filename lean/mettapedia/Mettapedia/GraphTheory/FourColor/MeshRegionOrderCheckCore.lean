import Mettapedia.GraphTheory.FourColor.MeshRegionOrderGraph

/-! # Executable full-component checks for the region-ordering witness -/

namespace Mettapedia.GraphTheory.FourColor.MeshRegionOrderObstruction
open GoertzelV24MeshIsoperimetry MeshRegionOrderData
set_option maxRecDepth 100000

def marked (w : Nat) : Set (Fin 180) := {v | w.testBit v.val = true}

instance (w : Nat) : DecidablePred (fun v => v ∈ marked w) :=
  fun _ => inferInstanceAs (Decidable (_ = true))

def selected (t : Cases) : Finset (Fin 8) :=
  Finset.univ.filter fun i => (stateMasks.getD t.val 0).testBit i.val = true

def rawMask (s : Finset (Fin 8)) : Nat :=
  (List.ofFn fun i : Fin 8 => if i ∈ s then cellMasks.getD i.val 0 else 0).foldl Nat.lor 0

def raw (t : Cases) : Nat := rawMasks.getD t.val 0
def component (t : Cases) : Nat := componentMasks.getD t.val 0
def parentEdge (t : Cases) (v : Fin 180) : Fin 270 :=
  edge (parentNumbers.getD (180 * t.val + v.val) 0)
def parent (t : Cases) (v : Fin 180) : Fin 180 :=
  let e := parentEdge t v
  if ambient.fst e = v then ambient.snd e else ambient.fst e
def rank (t : Cases) (v : Fin 180) : Nat := rankNumbers.getD (180 * t.val + v.val) 0

def componentCheck (t : Cases) : Bool := decide (
  anchor ∈ marked (component t) ∧
  (∀ v : Fin 180, v ∈ marked (component t) → v ∉ marked (raw t)) ∧
  (∀ v : Fin 180, v ∈ marked (component t) → v ≠ anchor →
    parent t v ∈ marked (component t) ∧
    (ambient.fst (parentEdge t v) = v ∨ ambient.snd (parentEdge t v) = v) ∧
    rank t (parent t v) < rank t v) ∧
  (∀ e : Fin 270,
    (ambient.fst e ∈ marked (component t) → ambient.snd e ∉ marked (raw t) →
      ambient.snd e ∈ marked (component t)) ∧
    (ambient.snd e ∈ marked (component t) → ambient.fst e ∉ marked (raw t) →
      ambient.fst e ∈ marked (component t))))

def computedBoundary (t : Cases) : Finset (Fin 270) :=
  Finset.univ.filter fun e =>
    (component t).testBit (ambient.fst e).val ≠ (component t).testBit (ambient.snd e).val

theorem computedBoundary_eq (t : Cases) : computedBoundary t =
    boundaryEdges ambient (Finset.univ.filter fun v => (component t).testBit v.val = false) := by
  ext e
  simp only [computedBoundary, boundaryEdges, IsBoundaryEdge, Finset.mem_filter,
    Finset.mem_univ, true_and]
  cases (component t).testBit (ambient.fst e).val <;>
    cases (component t).testBit (ambient.snd e).val <;> decide


def caseCheck (t : Cases) : Bool := decide (
  rawMask (selected t) = raw t ∧ componentCheck t = true ∧
  ((selected t).card = 6 → 16 ≤ (computedBoundary t).card) ∧
  ((selected t).card = 1 → (computedBoundary t).card ≤ 15))

end Mettapedia.GraphTheory.FourColor.MeshRegionOrderObstruction
