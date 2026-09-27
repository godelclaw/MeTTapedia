import FourColor.Embed

/-!
The witness interface of classical C-reducibility. The geometric and Kempe
lemmas are those of Gonthier and Werner, as formalized in this development by
Chris Emery. This factors the trace-selection step of `not_embed_reducible`
without assuming a minimal counterexample or the Four Colour Theorem.
-/

namespace FourColor.Hypermap

variable {Dc Dm : Type*} [Finite Dc] [Finite Dm]
variable {Gc : Hypermap Dc} {Gm : Hypermap Dm}
variable {rc : List Dc} {h : Dc → Dm} {cc : List Dc}

/-- A contract colouring supplies compatible trace witnesses for the piece
and its actual exterior. The exterior colouring may change. -/
theorem compatibleTraces_of_contractColoring
    (hemb : Gc.Embeddable rc) (hplanm : Gm.Planar) (hplainm : Gm.Plain)
    (hbridgem : Gm.Bridgeless) (hconnm : Gm.Connected) (hcubm : Gm.Cubic)
    (hBm : Gm.BirkhoffRings) (hpentm : Gm.Pentagonal)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z})
    (hinj : Function.Injective (embdd Gc Gm rc h))
    (hcred : Gc.CReducible rc cc) {k : Dm → Color}
    (hk : Gm.CcColoring (cc.map (embed Gc Gm rc h)) k) :
    ∃ et, Gc.RingTrace rc.reverse et ∧
      embedCotrace Gc Gm rc h hemb hplainm hcubm hpre hinj et := by
  obtain ⟨et, hcontract, hexterior⟩ :=
    embed_contract hemb hplanm hplainm hbridgem hconnm hcubm hBm hpentm hpre
      hinj hcred.base hk
  exact hcred.coclosure et hcontract _
    (embed_closure hemb hplanm hplainm hcubm hpre hinj) hexterior

#print axioms compatibleTraces_of_contractColoring

/-- Matching traces colour the actual ambient map, with the perimeter
orientation handled by the geometric patch theorem. -/
theorem colorable_of_compatibleTraces
    (hemb : Gc.Embeddable rc) (hplainm : Gm.Plain) (hcubm : Gm.Cubic)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z})
    (hinj : Function.Injective (embdd Gc Gm rc h))
    (matched : ∃ et, Gc.RingTrace rc.reverse et ∧
      embedCotrace Gc Gm rc h hemb hplainm hcubm hpre hinj et) :
    Gm.FourColorable := by
  classical
  obtain ⟨et, ⟨kc, hkc, hetceq⟩, ⟨kr, hkr, hetreq⟩⟩ := matched
  refine ((embed_patch hemb hplainm hcubm hpre hinj).colorable_patch).mpr
    ⟨trace ((embdRing Gc rc hemb).map (fun u => kc (embd rc u))),
      ⟨fun u => kc (embd rc u), ⟨?_, ?_⟩, rfl⟩, ⟨kr, hkr, ?_⟩⟩
  · intro u
    change kc (embdEdge Gc rc u.1) ≠ kc u.1
    by_cases hu : Gc.edge u.1 ∈ rc
    · rw [embdEdge_of_mem hu, ← hkc.face (Gc.edge (Gc.node (Gc.edge u.1))), Gc.nodeK]
      exact hkc.edge u.1
    · rw [embdEdge_of_not_mem hu]
      exact hkc.edge u.1
  · intro u
    exact (hkc.cface ((cface_embd hemb).mp
      ((embedDisk Gc rc hemb).cface_face u))).symm
  · have hEc : (embdRing Gc rc hemb).map (fun u => kc (embd rc u))
        = (rc.map Gc.edge).map kc := by
      have h1 : (fun u => kc (embd rc u)) = kc ∘ (embd rc) := rfl
      rw [h1, ← List.map_map, map_embd_ring hemb]
    rw [hEc, ← trace_reverse]
    rw [map_reverse_ring_rotate hemb hkc.face, trace_rotate] at hetceq
    rw [List.map_rotate, trace_rotate, length_embr_ring hemb hinj] at hetreq
    exact (List.rotate_injective (rc.length - 1) (hetreq.symm.trans hetceq)).symm

/-- Reconstruct a colouring through an embedded C-reducible configuration.
The starting contract colouring is consumed explicitly; no minimality or
unconditional Four Colour theorem is a premise. -/
theorem colorable_of_contractColoring
    (hemb : Gc.Embeddable rc) (hplanm : Gm.Planar) (hplainm : Gm.Plain)
    (hbridgem : Gm.Bridgeless) (hconnm : Gm.Connected) (hcubm : Gm.Cubic)
    (hBm : Gm.BirkhoffRings) (hpentm : Gm.Pentagonal)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z})
    (hcred : Gc.CReducible rc cc) {k : Dm → Color}
    (hk : Gm.CcColoring (cc.map (embed Gc Gm rc h)) k) :
    Gm.FourColorable := by
  have hinj := embdd_inj hemb hplanm hplainm hbridgem hconnm hcubm hBm hpentm hpre
  exact colorable_of_compatibleTraces hemb hplainm hcubm hpre hinj
    (compatibleTraces_of_contractColoring hemb hplanm hplainm hbridgem hconnm
      hcubm hBm hpentm hpre hinj hcred hk)

#print axioms colorable_of_compatibleTraces
#print axioms colorable_of_contractColoring

end FourColor.Hypermap
