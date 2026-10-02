import MettapediaFourColor.InjectiveEmbeddedRepair

/-!
# Local faithfulness extends to the complete embedded disk

The kernel-to-disk argument is adapted from the embedding proof of Gonthier
and Werner, ported by Chris Emery (MIT; reference attribution retained).
It isolates two local facts: injectivity on the kernel and reflection of
edges between its images. A consumer may establish these from an induced
core and complete cyclic stars rather than from global Birkhoff rings.
-/

namespace FourColor.FaithfulKernelEmbedding

open Hypermap

variable {Dc Dm : Type*} [Finite Dc] [Finite Dm]
  (Gc : Hypermap Dc) (Gm : Hypermap Dm) (rc : List Dc) (h : Dc → Dm)

/-- The shared kernel witness retains dart identity and reflects actual
edge reversals. Both fields refer to the same preembedding map. -/
structure FaithfulKernel : Prop where
  injective : Set.InjOn h {x | Gc.Kernel rc x}
  reflects_edge : ∀ {x y}, Gc.Kernel rc x → Gc.Kernel rc y →
    Gm.edge (h x) = h y → Gc.edge x = y

variable {Gc Gm rc h}

omit [Finite Dm] in
private theorem kernel_node_of_not (hemb : Gc.Embeddable rc)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z}) {z : Dc} (hzbc : z ∉ rc)
    (hkz : ¬ Gc.Kernel rc z) (hkez : ¬ Gc.Kernel rc (Gc.edge z)) :
    Gc.Kernel rc (Gc.node z) := by
  have hnotnez : ¬ Gc.Kernel rc (Gc.node (Gc.edge z)) := by
    intro hc
    have h1 : Gc.node (Gc.edge z) ∉ rc := not_mem_of_kernel hc
    have h2 : Gc.edge z ∉ rc := fun hm => h1 ((node_mem_ring_iff hemb _).mpr hm)
    rcases chordless_perimeter hemb hpre hzbc h2 with hk | hk
    · exact hkz hk
    · exact hkez hk
  rcases embed_cases hemb hpre z with hc | hc
  · exact absurd hc (by rw [not_or]; exact ⟨hkz, hkez⟩)
  · exact hc.resolve_right hnotnez

omit [Finite Dm] in
/-- Local kernel injectivity and edge reflection suffice to exclude every
off-perimeter dart collision, including collisions involving boundary faces. -/
theorem off_ring_injective (hemb : Gc.Embeddable rc) (hplainm : Gm.Plain)
    (hcubm : Gm.Cubic) (faithful : FaithfulKernel Gc Gm rc h)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z}) {x y : Dc} (hxbc : x ∉ rc)
    (hybc : y ∉ rc) (heq : embed Gc Gm rc h x = embed Gc Gm rc h y) : x = y := by
  classical
  have hplainc : Gc.Plain := hemb.base.base.base.base.plain
  have key : ∀ u v : Dc, Gc.Kernel rc u → v ∉ rc →
      embed Gc Gm rc h u = embed Gc Gm rc h v → u = v := by
    intro u v hku hvbc heq'
    rw [embed_of_kernel hku] at heq'
    by_cases hkv : Gc.Kernel rc v
    · rw [embed_of_kernel hkv] at heq'
      exact faithful.injective hku
        hkv heq'
    · by_cases hkev : Gc.Kernel rc (Gc.edge v)
      · rw [embed_of_kernel_edge hkv hkev] at heq'
        have h1 : Gc.edge (Gc.edge v) = u :=
          faithful.reflects_edge hkev hku
            heq'.symm
        rw [hplainc.edge_edge] at h1
        exact h1.symm
      · have hknv : Gc.Kernel rc (Gc.node v) := kernel_node_of_not hemb hpre hvbc hkv hkev
        rw [embed_of_kernel_node hkv hkev hknv] at heq'
        have hkenu : Gc.Kernel rc (Gc.edge (Gc.node u)) := by
          rw [← kernel_face, Gc.nodeK u]; exact hku
        have h2 : h u = Gm.face (h (Gc.edge (Gc.node u))) := by
          have h3 := hpre.face _ hkenu
          rwa [Gc.nodeK u] at h3
        rw [h2] at heq'
        have h4 : h (Gc.edge (Gc.node u)) = Gm.edge (h (Gc.node v)) := Gm.face.injective heq'
        have h5 : Gc.edge (Gc.node v) = Gc.edge (Gc.node u) :=
          faithful.reflects_edge hknv hkenu
            h4.symm
        exact (Gc.node.injective (Gc.edge.injective h5)).symm
  by_cases hkx : Gc.Kernel rc x
  · exact key x y hkx hybc heq
  · by_cases hky : Gc.Kernel rc y
    · exact (key y x hky hxbc heq.symm).symm
    · by_cases hknx : Gc.Kernel rc (Gc.node x)
      · have h2 : Gc.node y ∉ rc := fun hm => hybc ((node_mem_ring_iff hemb y).mp hm)
        have h3 : embed Gc Gm rc h (Gc.node x) = embed Gc Gm rc h (Gc.node y) := by
          rw [embedN hemb hplainm hcubm hpre hxbc, embedN hemb hplainm hcubm hpre hybc, heq]
        exact Gc.node.injective (key _ _ hknx h2 h3)
      · by_cases hkny : Gc.Kernel rc (Gc.node y)
        · have h2 : Gc.node x ∉ rc := fun hm => hxbc ((node_mem_ring_iff hemb x).mp hm)
          have h3 : embed Gc Gm rc h (Gc.node y) = embed Gc Gm rc h (Gc.node x) := by
            rw [embedN hemb hplainm hcubm hpre hybc, embedN hemb hplainm hcubm hpre hxbc,
              heq]
          exact (Gc.node.injective (key _ _ hkny h2 h3)).symm
        · have hkex : Gc.Kernel rc (Gc.edge x) := by
            by_contra hc
            exact hknx (kernel_node_of_not hemb hpre hxbc hkx hc)
          have hkey : Gc.Kernel rc (Gc.edge y) := by
            by_contra hc
            exact hkny (kernel_node_of_not hemb hpre hybc hky hc)
          have h2 : Gc.edge y ∉ rc := not_mem_of_kernel hkey
          have h3 : embed Gc Gm rc h (Gc.edge x) = embed Gc Gm rc h (Gc.edge y) := by
            rw [embedE hemb hplainm hcubm hpre, embedE hemb hplainm hcubm hpre, heq]
          exact Gc.edge.injective (key _ _ hkex h2 h3)

/-- The actual disk projection is injective even if distinct boundary faces
have the same ambient image. -/
theorem disk_injective (hemb : Gc.Embeddable rc) (plain : Gm.Plain) (cubic : Gm.Cubic)
    (pre : Preembedding Gc Gm h {z | Gc.Kernel rc z})
    (faithful : FaithfulKernel Gc Gm rc h) :
    Function.Injective (embdd Gc Gm rc h) := by
  intro u v eq
  exact Subtype.ext (off_ring_injective hemb plain cubic faithful pre u.2 v.2 eq)

/-- The same local geometric contract supports the entire repair and
reconstruction argument. -/
theorem colorable (hemb : Gc.Embeddable rc) (planar : Gm.Planar)
    (plain : Gm.Plain) (cubic : Gm.Cubic)
    (pre : Preembedding Gc Gm h {z | Gc.Kernel rc z})
    (faithful : FaithfulKernel Gc Gm rc h) {cc : List Dc}
    (repair : Gc.CReducible rc cc) {k : Dm → Color}
    (initial : Gm.CcColoring (cc.map (embed Gc Gm rc h)) k) : Gm.FourColorable :=
  InjectiveEmbeddedRepair.colorable hemb planar plain cubic pre
    (disk_injective hemb plain cubic pre faithful) repair initial

end FourColor.FaithfulKernelEmbedding
