import MettapediaFourColor.PatchDiskPlanar
import MettapediaFourColor.PatchDiskSources
import MettapediaFourColor.StripSixJointReconstruction

/-! # Actual strip reconstruction with automatically supplied exterior geometry

Deleting the D0099 core supplies the planar exterior and its Kempe closure.
The two-form joint repair therefore reconstructs an ambient colouring from
an initial exterior colouring in that class. The ambient graph has no size
bound. Distinct boundary ports may denote the same vertex.
The initial class and occurrence supply are still explicit obligations.
-/

namespace FourColor.PatchDiskRepair

open SimpleGraph PatchDisk PatchDisk.Reading PatchDiskSources
open TriangleStripAnchors StripResponseSummary
open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation ExceptionalOverlap

noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {data : Data G}

/-- No hypothesis about the geometry or closure of the deleted graph is
required. The source reading and ambient spherical triangulation supply it. -/
theorem d0099_repair (r : Reading d0099 data)
    (tri : Triangular data) (cyclic : data.IsVertexwiseCyclic)
    (conn : G.Connected) (ambient : (SimpleGraphBridge.rotationHypermap data).Planar)
    (s : Bool) (C : (G.induce (keep r)).Coloring Color)
    (initial : ∀ j, C (PatchDisk.Reading.port r j) = StripSixConnection.input s j) :
    Fintype.card (keep r) < Fintype.card V ∧
      ∃ D : (G.induce (keep r)).Coloring Color, ∃ K : G.Coloring Color,
        ∀ w, K w.val = D w := by
  let e : (G.induce (keep r)) ↪g G :=
    { toFun := Subtype.val, inj' := Subtype.val_injective, map_rel_iff' := Iff.rfl }
  have stars (i : Fin 19) (hi : 11 ≤ i.val) (v : V) (edge : G.Adj (r.hom i) v) :
      ∃ j, input0099.graph.Adj i j ∧ r.hom j = v := by
    obtain ⟨j,hj,adj⟩ := r.core_stars cyclic i hi v edge
    exact ⟨j,adj,hj⟩
  exact StripSixJointRepair.whole_repair_of_core_injective r.hom r.core_injective r.no_capture
    e (fun w => w.property) (fun v hv => ⟨⟨v,hv⟩,rfl⟩) stars (PatchDisk.Reading.port r)
    (fun _ => rfl) (r.exterior_closed tri cyclic conn ambient) s C initial

end
end FourColor.PatchDiskRepair
