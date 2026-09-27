import FourColor.Pilot.CompatibleTraces
import FourColor.Pilot.PatchWitness
import Mettapedia.GSLT.Core.RelationalRouteSemantics

/-!
# Classical reconstruction with retained colouring witnesses

A contract colouring first supplies a compatible pair of colourings by the
classical C-reducibility argument. The chosen assignments remain data at the
middle interface of a GSLT route. Its gluing operation returns the explicitly
constructed ambient colouring and reads back the selected exterior unchanged.
The selected exterior may differ from the original contract colouring.

Selection uses classical choice and the reference's Kempe-closure theorem;
this module does not extract an executable sequence of Kempe moves. It invokes
neither minimal-counterexample existence nor an unconditional colouring theorem.
The geometric and reducibility argument is due to Gonthier and Werner, following
Chris Emery's Lean formalization.
-/

namespace FourColor.Hypermap

universe u
variable {Dc Dm : Type u} [Finite Dc] [Finite Dm]
variable {Gc : Hypermap Dc} {Gm : Hypermap Dm}
variable {rc cc : List Dc} {h : Dc → Dm}

/-- Geometric hypotheses and the classical certificate for one embedded
reduction. These are the hypotheses consumed by the reference reconstruction. -/
structure EmbeddedReduction (Gc : Hypermap Dc) (Gm : Hypermap Dm)
    (rc cc : List Dc) (h : Dc → Dm) : Prop where
  embeddable : Gc.Embeddable rc
  planar : Gm.Planar
  plain : Gm.Plain
  bridgeless : Gm.Bridgeless
  connected : Gm.Connected
  cubic : Gm.Cubic
  birkhoff : Gm.BirkhoffRings
  pentagonal : Gm.Pentagonal
  preembedding : Preembedding Gc Gm h {z | Gc.Kernel rc z}
  reducible : Gc.CReducible rc cc

namespace EmbeddedReduction

variable (R : EmbeddedReduction Gc Gm rc cc h)

include R in
theorem injection : Function.Injective (embdd Gc Gm rc h) :=
  embdd_inj R.embeddable R.planar R.plain R.bridgeless R.connected R.cubic
    R.birkhoff R.pentagonal R.preembedding

/-- The actual contract assignment, not just its existence. -/
abbrev ContractColor := {k : Dm → Color //
  Gm.CcColoring (cc.map (embed Gc Gm rc h)) k}

/-- Actual colourings of the embedded disk and its geometric exterior. -/
abbrev Matches := Patch.TraceMatch
  (embedDisk Gc rc R.embeddable)
  (embedRem Gc Gm rc h R.embeddable R.plain R.cubic R.preembedding R.injection)
  (embdRing Gc rc R.embeddable)
  (embrRing Gc Gm rc h R.embeddable R.injection)

theorem patch : Patch Gm
    (embedDisk Gc rc R.embeddable)
    (embedRem Gc Gm rc h R.embeddable R.plain R.cubic R.preembedding R.injection)
    (embdd Gc Gm rc h) (embr Gc Gm rc h R.embeddable)
    (embdRing Gc rc R.embeddable)
    (embrRing Gc Gm rc h R.embeddable R.injection) :=
  embed_patch R.embeddable R.plain R.cubic R.preembedding R.injection

/-- C-reducibility produces a nonempty interface of compatible assignments.
The reversal and rotation in the classical ring convention are discharged here. -/
theorem matches_nonempty (k : ContractColor (Gc := Gc) (Gm := Gm)
    (rc := rc) (cc := cc) (h := h)) : Nonempty R.Matches := by
  obtain ⟨et, ⟨kc, hkc, hetceq⟩, ⟨kr, hkr, hetreq⟩⟩ :=
    compatibleTraces_of_contractColoring R.embeddable R.planar R.plain R.bridgeless
      R.connected R.cubic R.birkhoff R.pentagonal R.preembedding R.injection
      R.reducible k.property
  refine ⟨{
    disk := fun x => kc (embd rc x)
    remainder := kr
    disk_valid := ⟨?_, ?_⟩
    remainder_valid := hkr
    boundary := ?_ }⟩
  · intro x
    change kc (embdEdge Gc rc x.1) ≠ kc x.1
    by_cases hx : Gc.edge x.1 ∈ rc
    · rw [embdEdge_of_mem hx,
        ← hkc.face (Gc.edge (Gc.node (Gc.edge x.1))), Gc.nodeK]
      exact hkc.edge x.1
    · rw [embdEdge_of_not_mem hx]
      exact hkc.edge x.1
  · intro x
    exact (hkc.cface ((cface_embd R.embeddable).mp
      ((embedDisk Gc rc R.embeddable).cface_face x))).symm
  · have hEc : (embdRing Gc rc R.embeddable).map (fun x => kc (embd rc x))
        = (rc.map Gc.edge).map kc := by
      have h1 : (fun x => kc (embd rc x)) = kc ∘ embd rc := rfl
      rw [h1, ← List.map_map, map_embd_ring R.embeddable]
    rw [hEc]
    rw [map_reverse_ring_rotate R.embeddable hkc.face, trace_rotate] at hetceq
    rw [List.map_rotate, trace_rotate,
      length_embr_ring R.embeddable R.injection] at hetreq
    exact List.rotate_injective (rc.length - 1) (hetceq.symm.trans hetreq)

/-- One selected pair; both colour functions remain visible in the result. -/
noncomputable def chooseMatch (k : ContractColor (Gc := Gc) (Gm := Gm)
    (rc := rc) (cc := cc) (h := h)) : R.Matches :=
  Classical.choice (R.matches_nonempty k)

noncomputable def glue (m : R.Matches) : {k : Dm → Color // Gm.Coloring k} :=
  m.glue R.patch

noncomputable def reconstruct (k : ContractColor (Gc := Gc) (Gm := Gm)
    (rc := rc) (cc := cc) (h := h)) : {k : Dm → Color // Gm.Coloring k} :=
  R.glue (R.chooseMatch k)

theorem reconstruct_remainder (k : ContractColor (Gc := Gc) (Gm := Gm)
    (rc := rc) (cc := cc) (h := h))
    (x : {x : Dm // x ∉ embdInner Gc Gm rc h R.embeddable}) :
    (R.reconstruct k).val (embr Gc Gm rc h R.embeddable x) =
      (R.chooseMatch k).remainder x :=
  (R.chooseMatch k).glue_remainder R.patch x

theorem reconstruct_disk (k : ContractColor (Gc := Gc) (Gm := Gm)
    (rc := rc) (cc := cc) (h := h)) (x : {x : Dc // x ∉ rc}) :
    (R.reconstruct k).val (embdd Gc Gm rc h x) =
      Patch.ringShift (embdRing Gc rc R.embeddable)
        (embrRing Gc Gm rc h R.embeddable R.injection)
        (R.chooseMatch k).disk (R.chooseMatch k).remainder + (R.chooseMatch k).disk x :=
  (R.chooseMatch k).glue_disk R.patch x

inductive Phase where
  | contract | matched | colored

inductive Step : Phase → Phase → Type where
  | select : Step .contract .matched
  | glue : Step .matched .colored

open Mettapedia.GSLT.RelationalRouteSemantics
open Mettapedia.GSLT.LooseRelationEquipment
open Mettapedia.GSLT.Ultrainfinite

/-- The operational interpretation retains the selected assignments at the
middle interface. Only the second operation glues the pieces. -/
noncomputable def semantics : Semantics Step where
  State
    | .contract => ContractColor (Gc := Gc) (Gm := Gm) (rc := rc) (cc := cc) (h := h)
    | .matched => R.Matches
    | .colored => {k : Dm → Color // Gm.Coloring k}
  step
    | .select => companion R.chooseMatch
    | .glue => companion R.glue

def route : Route Step .contract .colored :=
  .cons Step.select (.cons Step.glue (.refl Phase.colored))

/-- A compatible route containing the chosen pair and both operation witnesses. -/
noncomputable def routeWitness (k : ContractColor (Gc := Gc) (Gm := Gm)
    (rc := rc) (cc := cc) (h := h)) :
    R.semantics.Witness route k (R.reconstruct k) :=
  ⟨R.chooseMatch k, ⟨⟨rfl⟩⟩, R.reconstruct k, ⟨⟨rfl⟩⟩, ⟨⟨rfl⟩⟩⟩

/-- Every witness for this selected route has the explicit reconstructed output. -/
theorem route_output (k : ContractColor (Gc := Gc) (Gm := Gm)
    (rc := rc) (cc := cc) (h := h)) {z : {k : Dm → Color // Gm.Coloring k}}
    (w : R.semantics.Witness route k z) : R.reconstruct k = z := by
  rcases w with ⟨m, hm, q, hq, hz⟩
  have hm' : R.chooseMatch k = m := hm.down.down
  have hq' : R.glue m = q := hq.down.down
  have hz' : q = z := hz.down.down
  exact (congrArg R.glue hm').trans (hq'.trans hz')

/-- Compose with any subsequent witness relation on the actual repaired
colouring. The intermediate assignment and both witnesses are retained. -/
noncomputable def continueWitness (k : ContractColor (Gc := Gc) (Gm := Gm)
    (rc := rc) (cc := cc) (h := h)) {Target : Type u}
    (next : Loose {k : Dm → Color // Gm.Coloring k} Target)
    {z : Target} (w : next (R.reconstruct k) z) :
    comp (R.semantics.Witness route) next k z :=
  ⟨R.reconstruct k, R.routeWitness k, w⟩

#print axioms matches_nonempty
#print axioms reconstruct
#print axioms reconstruct_remainder
#print axioms reconstruct_disk
#print axioms routeWitness
#print axioms route_output

end EmbeddedReduction
end FourColor.Hypermap
