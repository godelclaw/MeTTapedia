import Mettapedia.GraphTheory.Kempe.PairDecomposition
import Mettapedia.GraphTheory.FourColor.KempeChainCertificate
import Mettapedia.GraphTheory.FourColor.ShortPathReconstruction
import Mettapedia.GraphTheory.FourColor.IncidenceKempeSwitch

/-!
# Recolouring paths which stay reconstructible across a short path

For a deleted path of one or two edges, a smaller component switch whose
two endpoints both reconstruct gives a finite Kempe history on the old
graph. The unique endpoint colours force every restored edge to undergo
either the same transposition or no change; properness then decomposes
the change into actual old components.

Consequently a path through reconstructible smaller colourings lifts,
allowing several old switches for one smaller switch. An escape from an
old Kempe class must leave this image of reconstruction somewhere along
its smaller path. No existence of an escape is assumed or concluded.
-/

namespace Mettapedia.GraphTheory.FourColor.ShortPathKempeLifting

open GoertzelV24ForkInterfaceSupport IncidenceKempeSwitch KempeChainCertificate
open Mettapedia.GSLT.Ultrainfinite

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E]
variable {inc : E → Finset V} {S : Finset E} (p : OrderedEdgePath.Path inc S)
variable (A : Finset E)

/-- A proper old colouring witnessing membership in the image of restriction. -/
def Reconstructible (C : (graph inc A).Coloring (Fin 3)) : Prop :=
  ∃ D : (graph inc (A ∪ S)).Coloring (Fin 3), ∀ x ∈ A, D x = C x

/-- The image uses the actual smaller colourings and their usual steps. -/
abbrev ImageColouring := {C : (graph inc A).Coloring (Fin 3) // Reconstructible (S := S) A C}

abbrev ImageStep (C D : ImageColouring (inc := inc) (S := S) A) := Step C.val D.val

/-- One smaller switch lifts to a finite old history when both proper
reconstructions exist. Unretained identifiers are kept unchanged. -/
theorem step_lifts (hshort : p.length ≤ 2) (hAS : Disjoint A S)
    (C : (graph inc A).Coloring (Fin 3)) (r s : Fin 3)
    (K : (C.bicoloredSubgraph r s).ConnectedComponent)
    (old next : (graph inc (A ∪ S)).Coloring (Fin 3))
    (hold : ∀ x ∈ A, old x = C x)
    (hnext : ∀ x ∈ A, next x = C.swapOnKempeComponent r s K x)
    (hout : ∀ x ∉ A ∪ S, next x = old x)
    (m n : Fin 3)
    (hm : ∀ q, q ∉ profile inc A C p.first ↔ q = m)
    (hn : ∀ q, q ∉ profile inc A C p.last ↔ q = n) :
    Nonempty (History old next) := by
  apply nonempty_history_iff.mpr
  apply old.mem_kempeClosure_of_pointwise_swap next r s
  have before := p.end_colours_of_extension A hAS C old m n hm hn (proper _ _ old) hold
  have after := p.end_colours_of_extension A hAS (C.swapOnKempeComponent r s K) next _ _
    (missing_switch C r s K hm) (missing_switch C r s K hn) (proper _ _ next) hnext
  intro x
  by_cases hx : x ∈ A ∪ S
  · rcases Finset.mem_union.mp hx with hx | hx
    · rw [hold x hx, hnext x hx]
      by_cases hK : x ∈ C.kempeComponentSet r s K
      · exact Or.inr (C.swapOnKempeComponent_apply_of_mem hK)
      · exact Or.inl (C.swapOnKempeComponent_apply_of_not_mem hK)
    · rcases p.edge_eq_first_or_last hshort hx with rfl | rfl
      · rw [before.1, after.1]
        split_ifs <;> simp
      · rw [before.2, after.2]
        split_ifs <;> simp
  · exact Or.inl (hout x hx)

/-- Change only retained identifiers when choosing an old reconstruction. -/
def normalize (reference witness : (graph inc (A ∪ S)).Coloring (Fin 3)) :
    (graph inc (A ∪ S)).Coloring (Fin 3) :=
  colouring inc (A ∪ S) (EdgeColouringGluing.glue (A ∪ S) witness reference) (by
    intro x hx y hy hxy hmeet
    rw [EdgeColouringGluing.glue_left _ _ _ hx, EdgeColouringGluing.glue_left _ _ _ hy]
    exact proper inc (A ∪ S) witness x hx y hy hxy hmeet)

omit [Fintype E] in
theorem normalize_inside (reference witness : (graph inc (A ∪ S)).Coloring (Fin 3))
    {x : E} (hx : x ∈ A ∪ S) : normalize A reference witness x = witness x :=
  EdgeColouringGluing.glue_left _ _ _ hx

omit [Fintype E] in
theorem normalize_outside (reference witness : (graph inc (A ∪ S)).Coloring (Fin 3))
    {x : E} (hx : x ∉ A ∪ S) : normalize A reference witness x = reference x := by
  change EdgeColouringGluing.glue (A ∪ S) witness reference x = reference x
  simp [EdgeColouringGluing.glue, hx]

/-- Every smaller path staying in the reconstruction image lifts. The
profile hypothesis is about the two attachment vertices, not repair supply. -/
theorem image_route_lifts (hshort : p.length ≤ 2) (hAS : Disjoint A S)
    (hprofiles : ∀ C : (graph inc A).Coloring (Fin 3), ∃ m n : Fin 3,
      (∀ q, q ∉ profile inc A C p.first ↔ q = m) ∧
      (∀ q, q ∉ profile inc A C p.last ↔ q = n))
    {C D : ImageColouring (inc := inc) (S := S) A}
    (history : Route (ImageStep A) C D)
    (old : (graph inc (A ∪ S)).Coloring (Fin 3))
    (hold : ∀ x ∈ A, old x = C.val x) :
    ∃ next : (graph inc (A ∪ S)).Coloring (Fin 3),
      Nonempty (History old next) ∧ ∀ x ∈ A, next x = D.val x := by
  induction history generalizing old with
  | refl => exact ⟨old, ⟨.refl _⟩, hold⟩
  | @cons C middle D step rest ih =>
    obtain ⟨witness, hwitness⟩ := middle.property
    let next := normalize A old witness
    have hnext : ∀ x ∈ A, next x = middle.val x := fun x hx =>
      (normalize_inside A old witness (Finset.mem_union_left S hx)).trans (hwitness x hx)
    have hstep : Nonempty (History old next) := by
      obtain ⟨m, n, hm, hn⟩ := hprofiles C.val
      obtain ⟨r, s, K, heq⟩ := step.toKempeStep
      apply step_lifts p A hshort hAS C.val r s K old next hold
        (fun x hx => (hnext x hx).trans (DFunLike.congr_fun heq x))
        (fun _ hx => normalize_outside A old witness hx) m n hm hn
    obtain ⟨last, ⟨tail⟩, hlast⟩ := ih next hnext
    obtain ⟨head⟩ := hstep
    exact ⟨last, ⟨head.append tail⟩, hlast⟩

end Mettapedia.GraphTheory.FourColor.ShortPathKempeLifting
