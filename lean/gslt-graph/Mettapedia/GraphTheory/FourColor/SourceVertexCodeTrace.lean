import Mettapedia.GraphTheory.FourColor.VertexCodeSourceGeometry
import Mettapedia.GraphTheory.FourColor.VertexCodeTrace

/-!
# Constructing geometry-faithful code traces from source vertex sweeps

Every nonempty duplicate-free sweep of a cubic source with cyclic vertex
rotations encodes to a valid trace. Its decoder is isomorphic to the actual
swept side in the specified boundary coordinates. The sweep processes its
tail first, as does the existing source Count recurrence. No planar or
colourability assumption, and no uniform width claim, is needed here.
-/

namespace Mettapedia.GraphTheory.FourColor.SourceVertexCodeTrace

open GoertzelV24OpenTangleComposition GoertzelV24RotationCutDartDecomposition
open GoertzelV24FaceDualConnectedness
open TubeSlab.VertexTransfer VertexCodeCyclicEncoder VertexCodeSourceGeometry
open VertexCodeTrace VertexCodeRealization

noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable {RS : RotationSystem.{u,u,u} V E}

def root (hc : RS.IsCubic) (v : V) : At RS v := by
  have h : (RS.dartsAt v).Nonempty := Finset.card_pos.mp (by rw [hc]; omega)
  exact ⟨h.choose, (Finset.mem_filter.mp h.choose_spec).2⟩

def coordinates (keep : V → Prop) :
    Fin (Fintype.card (BoundaryDart RS keep)) ≃ BoundaryDart RS keep :=
  (Fintype.equivFin _).symm

structure Encoding {r : ℕ} {keep : V → Prop} (mo : Fin r ≃ BoundaryDart RS keep) where
  trace : Trace r
  model : Model trace.realize mo

def first (hc : RS.IsCubic) (hcyc : VertexRotationCyclic RS) (v : V)
    {r : ℕ} (mo : Fin r ≃ BoundaryDart RS (visited [v])) : Encoding mo where
  trace := .first (cyclicEncode (inner := fun _ : V => False) hc not_false hcyc (root hc v) emptyCoords mo)
    (cyclicEncode_valid emptyCoords mo hc not_false hcyc (root hc v))
  model := firstModel (cyclicStarEquiv hc not_false hcyc (root hc v)) mo
    (cyclicStarEquiv_succ hc not_false hcyc (root hc v))

def extend (hc : RS.IsCubic) (hcyc : VertexRotationCyclic RS)
    {keep : V → Prop} {l r : ℕ} {mi : Fin l ≃ BoundaryDart RS keep}
    (before : Encoding mi) (v : V) (hv : ¬ keep v)
    (mo : Fin r ≃ BoundaryDart RS (enlarged keep v)) : Encoding mo where
  trace := .step before.trace (cyclicEncode hc hv hcyc (root hc v) mi mo)
    (cyclicEncode_valid mi mo hc hv hcyc (root hc v))
  model := Model.step (cyclicStarEquiv hc hv hcyc (root hc v)) mi mo before.model hv
    (cyclicStarEquiv_succ hc hv hcyc (root hc v))

/-- Construct the trace and its geometric round trip together. The output
coordinates are supplied; intermediate finite coordinates are chosen here. -/
def encodeOrder (hc : RS.IsCubic) (hcyc : VertexRotationCyclic RS) :
    (order : List V) → order.Nodup → order ≠ [] →
    {r : ℕ} → (mo : Fin r ≃ BoundaryDart RS (visited order)) → Encoding mo
  | [], _, he, _, _ => (he rfl).elim
  | [v], _, _, _, mo => first hc hcyc v mo
  | v :: w :: rest, hn, _, _, mo =>
    extend hc hcyc
      (encodeOrder hc hcyc (w :: rest) (List.nodup_cons.mp hn).2 (by simp)
        (coordinates (visited (w :: rest)))) v
      (fun hv => (List.nodup_cons.mp hn).1 ((visited_iff_mem _ _).mp hv)) mo

/-- Every source sweep is covered by an actual valid code trace, preserving
all geometry recorded in Model, not merely the source colouring relation. -/
theorem source_covered (hc : RS.IsCubic) (hcyc : VertexRotationCyclic RS)
    (order : List V) (hn : order.Nodup) (he : order ≠ [])
    {r : ℕ} (mo : Fin r ≃ BoundaryDart RS (visited order)) :
    ∃ t : Trace r, Nonempty (Model t.realize mo) :=
  ⟨(encodeOrder hc hcyc order hn he mo).trace,
    ⟨(encodeOrder hc hcyc order hn he mo).model⟩⟩

def terminalCoordinates (order : List V) (hcover : ∀ v, visited order v) :
    Fin 0 ≃ BoundaryDart RS (visited order) where
  toFun := Fin.elim0
  invFun b := (b.2 (hcover _)).elim
  left_inv i := i.elim0
  right_inv b := (b.2 (hcover _)).elim

/-- Complete source sweeps produce closed traces; no completion or smoothing
hypothesis is smuggled into this construction. -/
def encodeClosed (hc : RS.IsCubic) (hcyc : VertexRotationCyclic RS)
    (order : List V) (hn : order.Nodup) (he : order ≠ [])
    (hcover : ∀ v, visited order v) : Encoding (terminalCoordinates (RS := RS) order hcover) :=
  encodeOrder hc hcyc order hn he (terminalCoordinates order hcover)

end
end Mettapedia.GraphTheory.FourColor.SourceVertexCodeTrace
