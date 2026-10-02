import MettapediaFourColor.CompatibleTraces

/-!
# Reconstruction from a directly certified disk embedding

The restriction argument is adapted from Gonthier and Werner's embedding
proof, ported to Lean by Chris Emery (MIT; the reference notice is retained
with the dependency). It needs injectivity of the actual disk dart map.
Global Birkhoff and pentagonal hypotheses were used to establish that
injectivity; they are unnecessary once a local geometric proof supplies it.
-/

namespace FourColor.InjectiveEmbeddedRepair

open Hypermap

variable {Dc Dm : Type*} [Finite Dc] [Finite Dm]
  {Gc : Hypermap Dc} {Gm : Hypermap Dm} {rc : List Dc} {h : Dc → Dm}

private theorem edge_mem_insertE (plain : Gc.Plain) {cc : List Dc} {z : Dc}
    (hz : z ∈ Gc.insertE cc) : Gc.edge z ∈ Gc.insertE cc := by
  obtain ⟨w, hw, hzw⟩ := (mem_insertE plain).mp hz
  exact (mem_insertE plain).mpr ⟨w, hw, Equiv.Perm.sameCycle_apply_left.mpr hzw⟩

/-- Restrict the supplied contract witness to the patch and its genuine
exterior. The actual disk injection is the only embedding-separation input. -/
theorem contract_traces (hemb : Gc.Embeddable rc) (hplainm : Gm.Plain) (hcubm : Gm.Cubic)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z})
    (hinj : Function.Injective (embdd Gc Gm rc h)) {cc : List Dc}
    (hvc : Gc.ValidContract rc cc) {k : Dm → Color}
    (hk : Gm.CcColoring (cc.map (embed Gc Gm rc h)) k) :
    ∃ et, Gc.CcRingTrace cc rc.reverse et ∧
      embedCotrace Gc Gm rc h hemb hplainm hcubm hpre hinj et := by
  classical
  have hplainc : Gc.Plain := hemb.base.base.base.base.plain
  have hk1face : ∀ z : Dc,
      k (embed Gc Gm rc h (Gc.face z)) = k (embed Gc Gm rc h z) :=
    fun z => (hk.cface (cface_embed hemb hplainm hcubm hpre hinj (Gc.cface_face z))).symm
  have hmapinsert : Gm.insertE (cc.map (embed Gc Gm rc h))
      = (Gc.insertE cc).map (embed Gc Gm rc h) :=
    insertE_map_embed hemb hplainm hcubm hpre cc
  have hk1cc : Gc.CcColoring cc (fun z => k (embed Gc Gm rc h z)) := by
    refine ⟨?_, hk1face⟩
    have key : ∀ z : Dc, z ∉ rc →
        (k (embed Gc Gm rc h (Gc.edge z)) = k (embed Gc Gm rc h z) ↔ z ∈ Gc.insertE cc) := by
      intro z hz
      rw [embedE hemb hplainm hcubm hpre z, hk.edge, hmapinsert]
      constructor
      · intro hm
        obtain ⟨y, hy, hyz⟩ := List.mem_map.mp hm
        have eq : y = z := congrArg Subtype.val
          (hinj (a₁ := ⟨y, hvc.off_ring y hy⟩) (a₂ := ⟨z, hz⟩) hyz)
        rwa [eq] at hy
      · intro hm
        exact List.mem_map.mpr ⟨z, hm, rfl⟩
    intro z
    by_cases hz : z ∈ rc
    · have hez : Gc.edge z ∉ rc := (edge_perimeter hemb z).resolve_left (not_not_intro hz)
      have h2 := key (Gc.edge z) hez
      rw [hplainc.edge_edge] at h2
      constructor
      · intro hcon
        have h4 := edge_mem_insertE hplainc (h2.mp hcon.symm)
        rwa [hplainc.edge_edge] at h4
      · intro hcon
        exact (h2.mpr (edge_mem_insertE hplainc hcon)).symm
    · exact key z hz
  refine ⟨trace ((rc.reverse).map (fun z => k (embed Gc Gm rc h z))),
    ⟨_, hk1cc, rfl⟩, ⟨fun w => k (embr Gc Gm rc h hemb w), ⟨?_, ?_⟩, ?_⟩⟩
  · intro w
    change k (Gm.edge (embr Gc Gm rc h hemb w)) ≠ k (embr Gc Gm rc h hemb w)
    intro hcon
    rw [hk.edge, hmapinsert] at hcon
    obtain ⟨y, hy, hyw⟩ := List.mem_map.mp hcon
    have hey : Gc.edge y ∈ Gc.insertE cc := edge_mem_insertE hplainc hy
    have heybc : Gc.edge y ∉ rc := hvc.off_ring _ hey
    refine w.2 ⟨⟨y, hvc.off_ring y hy⟩, ?_, hyw⟩
    intro hmem
    rw [mem_embd_ring_iff hemb] at hmem
    obtain ⟨z, hzrc, hzy⟩ := List.mem_map.mp hmem
    have hzy' : Gc.edge z = y := hzy
    exact heybc (by rw [← hzy', hplainc.edge_edge]; exact hzrc)
  · intro w
    exact (hk.cface ((embed_patch hemb hplainm hcubm hpre hinj).cface_hr w)).symm
  · rw [map_reverse_ring_eq hemb hinj hk1face]

/-- A local disk injection, planar ambient geometry and compatible repair
suffice for full reconstruction. No global short-ring hypothesis is needed. -/
theorem colorable (hemb : Gc.Embeddable rc) (planar : Gm.Planar)
    (plain : Gm.Plain) (cubic : Gm.Cubic)
    (pre : Preembedding Gc Gm h {z | Gc.Kernel rc z})
    (injection : Function.Injective (embdd Gc Gm rc h)) {cc : List Dc}
    (repair : Gc.CReducible rc cc) {k : Dm → Color}
    (initial : Gm.CcColoring (cc.map (embed Gc Gm rc h)) k) : Gm.FourColorable := by
  obtain ⟨et, inside, outside⟩ := contract_traces hemb plain cubic pre injection repair.base initial
  exact colorable_of_compatibleTraces hemb plain cubic pre injection
    (repair.coclosure et inside _ (embed_closure hemb planar plain cubic pre injection) outside)

end FourColor.InjectiveEmbeddedRepair
