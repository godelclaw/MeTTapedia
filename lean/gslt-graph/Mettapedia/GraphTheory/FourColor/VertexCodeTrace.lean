import Mettapedia.GraphTheory.FourColor.VertexCodeRealization

/-!
# Literal realization of complete finite vertex-code runs

Every nonempty well-typed run constructs an actual open cubic tangle.
Induction identifies its support with relational evaluation of the codes.
At the empty terminal boundary, acceptance means a proper colouring of
the closed constructed object. No bound on the width of arbitrary graphs,
nor spherical validity of an arbitrary run, is inferred.
-/

namespace Mettapedia.GraphTheory.FourColor.VertexCodeTrace

open TubeSlab.VertexTransfer VertexCodePartition VertexCodeRealization
open GoertzelV24OpenTangleComposition TwoSidedOpenTangleData

inductive Trace : ℕ → Type where
  | first {r} (a : Code 0 r) (valid : Valid a) : Trace r
  | step {l r} (before : Trace l) (a : Code l r) (valid : Valid a) : Trace r

namespace Trace

def Vertex : {r : ℕ} → Trace r → Type
  | _, .first _ _ => Unit
  | _, .step t _ _ => Vertex t ⊕ Unit

def Interior : {r : ℕ} → Trace r → Type
  | _, .first _ _ => Empty
  | _, .step t a _ => (Interior t ⊕ Empty) ⊕ (Consumed a ⊕ Consumed a)

instance vertexFintype : {r : ℕ} → (t : Trace r) → Fintype t.Vertex
  | _, .first _ _ => inferInstanceAs (Fintype Unit)
  | _, .step t _ _ => @instFintypeSum t.Vertex Unit (vertexFintype t) inferInstance

instance interiorFintype : {r : ℕ} → (t : Trace r) → Fintype t.Interior
  | _, .first _ _ => inferInstanceAs (Fintype Empty)
  | _, .step t a _ =>
    @instFintypeSum (t.Interior ⊕ Empty) (Consumed a ⊕ Consumed a)
      (@instFintypeSum t.Interior Empty (interiorFintype t) inferInstance) inferInstance

noncomputable def realize : {r : ℕ} → (t : Trace r) →
    TwoSidedOpenTangleData t.Vertex t.Interior (Fin 0) (Fin r)
  | _, .first a h => initial a h
  | _, .step t a h => attach a h (realize t)

def Evaluates : {r : ℕ} → Trace r → (Fin r → Color) → Prop
  | _, .first a _ , y => CodeAccepts a Fin.elim0 y
  | _, .step t a _, y => ∃ x, Evaluates t x ∧ CodeAccepts a x y

theorem support_exact {r} (t : Trace r) (y : Fin r → Color) :
    Supports t.realize y ↔ t.Evaluates y := by
  induction t with
  | first a h => exact initial_support a h y
  | step t a h ih =>
    change Supports (attach a h t.realize) y ↔ _
    rw [supports_attach_iff]
    exact exists_congr (fun x => and_congr_left (fun _ => ih x))

/-- Literal terminal acceptance, not mere nonemptiness of an open fibre. -/
theorem closed_exact (t : Trace 0) :
    (∃ c, t.realize.IsTaitColoring c) ↔ t.Evaluates Fin.elim0 := by
  rw [← support_exact]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, hc, funext (fun p => p.elim0), funext (fun p => p.elim0)⟩
  · rintro ⟨c, hc, _, _⟩
    exact ⟨c, hc⟩

end Trace
end Mettapedia.GraphTheory.FourColor.VertexCodeTrace
