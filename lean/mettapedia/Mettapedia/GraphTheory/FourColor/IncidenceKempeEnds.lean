import Mettapedia.GraphTheory.FourColor.IncidenceKempeSwitch
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeTerminalProfile

/-!
# Terminal contacts of a physical two-colour component

For ordinary edges, a component can meet at most two distinct vertices
at which one of its selected colours is missing. The statement uses
the retained original edge identifiers and their actual incidence.
-/

namespace Mettapedia.GraphTheory.FourColor.IncidenceKempeSwitch

open GoertzelV24ForkInterfaceSupport
open GoertzelV24KempeEndpoint

noncomputable section
attribute [local instance] Classical.propDecidable
set_option autoImplicit false

variable {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]
variable {inc : E → Finset V} {S : Finset E}
variable (C : (graph inc S).Coloring (Fin 3)) (r s : Fin 3)

omit [Fintype E] in
/-- At a vertex missing a selected colour, there is at most one retained
edge with either selected colour. -/
theorem active_incident_eq_of_missing {v : V}
    (hm : r ∉ profile inc S C v ∨ s ∉ profile inc S C v)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S)
    (hvx : v ∈ inc x) (hvy : v ∈ inc y)
    (hcx : C x = r ∨ C x = s) (hcy : C y = r ∨ C y = s) : x = y := by
  have hmx : C x ∈ profile inc S C v :=
    Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hvx⟩, rfl⟩
  have hmy : C y ∈ profile inc S C v :=
    Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, hvy⟩, rfl⟩
  by_contra hne
  have hcol := C.valid ⟨hne, hx, hy, v, Finset.mem_inter.mpr ⟨hvx, hvy⟩⟩
  rcases hm with hm | hm
  · exact hcol ((hcx.resolve_left (fun h => hm (h ▸ hmx))).trans
      (hcy.resolve_left (fun h => hm (h ▸ hmy))).symm)
  · exact hcol ((hcx.resolve_right (fun h => hm (h ▸ hmx))).trans
      (hcy.resolve_right (fun h => hm (h ▸ hmy))).symm)

variable (hsize : ∀ x : E, (inc x).card ≤ 2)

include hsize

/-- Neighbours in the two-colour line graph inject into the two ends
of the central original edge. -/
theorem incidence_bicolored_degree_bound (x : C.bicoloredSet r s) :
    ((C.bicoloredSubgraph r s).neighborSet x).ncard ≤ 2 := by
  classical
  let H := C.bicoloredSubgraph r s
  let common : H.neighborSet x → {v // v ∈ inc x.val} := fun y =>
    ⟨Classical.choose y.property.2.2.2,
      (Finset.mem_inter.mp (Classical.choose_spec y.property.2.2.2)).1⟩
  have hcommon (y : H.neighborSet x) : (common y).val ∈ inc y.val.val :=
    (Finset.mem_inter.mp (Classical.choose_spec y.property.2.2.2)).2
  have hinj : Function.Injective common := by
    intro y z heq
    apply Subtype.ext
    apply Subtype.ext
    by_contra hne
    have hcol := bicolored_neighbor_colors_eq C r s y.property z.property
    exact C.valid ⟨hne, y.property.2.2.1, z.property.2.2.1,
      (common y).val, Finset.mem_inter.mpr
        ⟨hcommon y, (congrArg Subtype.val heq).symm ▸ hcommon z⟩⟩ hcol
  calc
    (H.neighborSet x).ncard = Fintype.card (H.neighborSet x) :=
      (Set.fintypeCard_eq_ncard _).symm
    _ ≤ Fintype.card {v // v ∈ inc x.val} := Fintype.card_le_of_injective common hinj
    _ = (inc x.val).card := Fintype.card_coe _
    _ ≤ 2 := hsize x.val

omit [Fintype E] [DecidableEq E] in
/-- A terminal contact in the original incidence makes its active edge
a terminal vertex of the two-colour line graph. -/
theorem incidence_terminal_neighborSet {v : V} {x : C.bicoloredSet r s}
    (hvx : v ∈ inc x.val)
    (hm : r ∉ profile inc S C v ∨ s ∉ profile inc S C v) :
    ((C.bicoloredSubgraph r s).neighborSet x).Subsingleton := by
  intro y hy z hz
  obtain ⟨a, ha⟩ := hy.2.2.2
  obtain ⟨b, hb⟩ := hz.2.2.2
  obtain ⟨hax, hay⟩ := Finset.mem_inter.mp ha
  obtain ⟨hbx, hbz⟩ := Finset.mem_inter.mp hb
  have hav : a ≠ v := by
    intro heq
    exact hy.1 (active_incident_eq_of_missing C r s hm hy.2.1 hy.2.2.1
      hvx (heq ▸ hay) x.property y.property)
  have hbv : b ≠ v := by
    intro heq
    exact hz.1 (active_incident_eq_of_missing C r s hm hz.2.1 hz.2.2.1
      hvx (heq ▸ hbz) x.property z.property)
  have hab : a = b := by
    by_contra hne
    have := Finset.two_lt_card_iff.mpr ⟨v, a, b, hvx, hax, hbx,
      Ne.symm hav, Ne.symm hbv, hne⟩
    have := hsize x.val
    omega
  apply Subtype.ext
  by_contra hne
  exact C.valid ⟨hne, hy.2.2.1, hz.2.2.1, a,
    Finset.mem_inter.mpr ⟨hay, hab.symm ▸ hbz⟩⟩
    (bicolored_neighbor_colors_eq C r s hy hz)

omit [Fintype E] [DecidableEq E] in
/-- An active edge terminal at two distinct original vertices is isolated
in the two-colour line graph. -/
theorem incidence_isolated_of_two_terminals {u v : V} (huv : u ≠ v)
    {x : C.bicoloredSet r s} (hux : u ∈ inc x.val) (hvx : v ∈ inc x.val)
    (hu : r ∉ profile inc S C u ∨ s ∉ profile inc S C u)
    (hv : r ∉ profile inc S C v ∨ s ∉ profile inc S C v) :
    (C.bicoloredSubgraph r s).neighborSet x = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  obtain ⟨a, ha⟩ := hy.2.2.2
  obtain ⟨hax, hay⟩ := Finset.mem_inter.mp ha
  have hau : a ≠ u := by
    intro heq
    exact hy.1 (active_incident_eq_of_missing C r s hu hy.2.1 hy.2.2.1
      hux (heq ▸ hay) x.property y.property)
  have hav : a ≠ v := by
    intro heq
    exact hy.1 (active_incident_eq_of_missing C r s hv hy.2.1 hy.2.2.1
      hvx (heq ▸ hay) x.property y.property)
  have := Finset.two_lt_card_iff.mpr ⟨u, v, a, hux, hvx, hax,
    huv, Ne.symm hau, Ne.symm hav⟩
  have := hsize x.val
  omega

/-- One physical component has at most two distinct terminal contacts.
No planarity or supplied boundary pairing is needed for this bound. -/
theorem terminal_contacts_card_le_two
    (K : (C.bicoloredSubgraph r s).ConnectedComponent) (ports : Finset V)
    (hm : ∀ v ∈ ports, r ∉ profile inc S C v ∨ s ∉ profile inc S C v)
    (ht : ∀ v ∈ ports, Touches C r s K v) : ports.card ≤ 2 := by
  classical
  let H := C.bicoloredSubgraph r s
  let edgeAt : ports → E := fun p => Classical.choose (ht p.val p.property)
  have hi (p : ports) : p.val ∈ inc (edgeAt p) :=
    (Classical.choose_spec (ht p.val p.property)).2.1
  have hc (p : ports) : edgeAt p ∈ C.kempeComponentSet r s K :=
    (Classical.choose_spec (ht p.val p.property)).2.2
  let vertexAt : ports → C.bicoloredSet r s := fun p => ⟨edgeAt p, (hc p).1⟩
  let inComponent : ports → K := fun p => ⟨vertexAt p, (hc p).2⟩
  have hterminal (p : ports) : (H.neighborSet (vertexAt p)).Subsingleton :=
    incidence_terminal_neighborSet C r s hsize (hi p) (hm p.val p.property)
  by_cases hinj : Function.Injective inComponent
  · have hdegree (x : K) : (K.toSimpleGraph.neighborSet x).ncard ≤ 2 := by
      let neighborEquiv : K.toSimpleGraph.neighborSet x ≃ H.neighborSet x.val :=
        { toFun := fun y => ⟨y.val.val, y.property⟩
          invFun := fun y => ⟨⟨y.val, K.mem_supp_of_adj_mem_supp x.property y.property⟩,
            y.property⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [Set.ncard_congr' neighborEquiv]
      exact incidence_bicolored_degree_bound C r s hsize x.val
    let terminals := Finset.univ.filter fun x : K =>
      (K.toSimpleGraph.neighborSet x).Subsingleton
    have himage : Finset.univ.image inComponent ⊆ terminals := by
      intro x hx
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro y hy z hz
      exact Subtype.ext (hterminal p hy hz)
    have hcard := Finset.card_le_card himage
    have hbound := terminalVertices_card_le_two K.toSimpleGraph K.connected_toSimpleGraph hdegree
    have heq : (Finset.univ.image inComponent).card = ports.card := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe]
    change terminals.card ≤ 2 at hbound
    omega
  · rw [Function.Injective] at hinj
    push Not at hinj
    obtain ⟨p, q, heq, hpq⟩ := hinj
    have hpqV : p.val ≠ q.val := fun h => hpq (Subtype.ext h)
    have hedge : edgeAt p = edgeAt q := congrArg (fun x : K => x.val.val) heq
    have hiso : H.neighborSet (vertexAt p) = ∅ :=
      incidence_isolated_of_two_terminals C r s hsize hpqV (hi p)
        (by change q.val ∈ inc (edgeAt p); rw [hedge]; exact hi q)
        (hm p.val p.property) (hm q.val q.property)
    have hsame (z : ports) : edgeAt z = edgeAt p := by
      have hreach : H.Reachable (vertexAt p) (vertexAt z) :=
        _root_.SimpleGraph.ConnectedComponent.exact ((hc p).2.trans (hc z).2.symm)
      have hv : vertexAt p = vertexAt z := by
        by_contra hne
        exact H.not_reachable_of_neighborSet_left_eq_empty hne hiso hreach
      exact (congrArg Subtype.val hv).symm
    have hsub : ports ⊆ inc (edgeAt p) := by
      intro v hv
      have := hi ⟨v, hv⟩
      rwa [hsame ⟨v, hv⟩] at this
    exact (Finset.card_le_card hsub).trans (hsize _)

end
end Mettapedia.GraphTheory.FourColor.IncidenceKempeSwitch
