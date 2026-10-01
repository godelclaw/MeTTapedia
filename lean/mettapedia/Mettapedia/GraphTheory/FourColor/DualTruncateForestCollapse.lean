import Mettapedia.GraphTheory.FiniteForestBranching
import Mettapedia.GraphTheory.FourColor.DualTruncateOpenPatch
import Mettapedia.GraphTheory.FourColor.DualTruncateCornerCoherence

/-!
# Forest geometry forces exact corner collapse

Cyclic corner differences agree across source edges and sum to zero around
each source vertex. Their nonzero support has no leaf when the source has no
parallel edges. If the support is confined to an induced forest it vanishes.

For an actual open patch, at most one selected neighbour at every exterior
source vertex makes all its corners visible. Paired exterior observations
then force the exterior differences to zero. Thus a selected source forest
retains its entire colouring fibre when collapsed to source vertex colours.
This is an exact constraint law, not yet a smaller embedded graph operation.
-/

namespace Mettapedia.GraphTheory.FourColor.DualTruncateForestCollapse

open DualTruncateColoring DualTruncateCornerSemantics DualTruncateCornerCoherence
open DualTruncateOpenPatch GoertzelV24FaceDualConnectedness
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

universe u
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (RS : RotationSystem.{u,u,u} V E)

/-- Actual darts based at the same vertex have distinct opposite vertices. -/
def SimpleSource : Prop :=
  ∀ d e : RS.D, RS.vertOf d = RS.vertOf e →
    RS.vertOf (RS.alpha d) = RS.vertOf (RS.alpha e) → d = e

/-- An exterior source vertex has at most one selected neighbour. -/
def Separated (selected : V → Prop) : Prop :=
  ∀ v, ¬selected v → ∀ a b, selected a → selected b →
    (rotationPrimalGraph RS).Adj v a → (rotationPrimalGraph RS).Adj v b → a = b

theorem difference_sum_zero (q : RS.D → Color) (v : V) :
    ∑ d ∈ RS.dartsAt v, difference RS q d = 0 := by
  have himage : (RS.dartsAt v).image RS.rho = RS.dartsAt v := by
    ext d
    constructor
    · rintro hd
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hd
      simpa only [RotationSystem.dartsAt, Finset.mem_filter, Finset.mem_univ,
        true_and, RS.vert_rho] using he
    · intro hd
      refine Finset.mem_image.mpr ⟨RS.rho.symm d, ?_, by simp⟩
      have hv : RS.vertOf d = v := by simpa [RotationSystem.dartsAt] using hd
      have he : RS.vertOf (RS.rho.symm d) = RS.vertOf d := by
        simpa only [Equiv.apply_symm_apply] using (RS.vert_rho (RS.rho.symm d)).symm
      simp [RotationSystem.dartsAt, he, hv]
  have hsum : (∑ d ∈ RS.dartsAt v, q (RS.rho d)) = ∑ d ∈ RS.dartsAt v, q d := by
    calc
      _ = ∑ d ∈ (RS.dartsAt v).image RS.rho, q d :=
        (Finset.sum_image RS.rho.injective.injOn).symm
      _ = _ := by rw [himage]
  simp only [difference, Finset.sum_add_distrib]
  rw [hsum, color_add_self]

theorem other_nonzero_difference {q : RS.D → Color} {d : RS.D}
    (hd : difference RS q d ≠ 0) :
    ∃ e, RS.vertOf e = RS.vertOf d ∧ e ≠ d ∧ difference RS q e ≠ 0 := by
  by_contra! h
  have hs : (∑ e ∈ RS.dartsAt (RS.vertOf d), difference RS q e) = difference RS q d := by
    apply Finset.sum_eq_single d
    · intro e he hne
      exact h e (by simpa [RotationSystem.dartsAt] using he) hne
    · intro hn
      exact False.elim (hn (by simp [RotationSystem.dartsAt]))
  exact hd (hs.symm.trans (difference_sum_zero RS q _))

/-- The nonzero difference support on the actual selected source vertices. -/
def activeGraph (selected : V → Prop) (q : RS.D → Color) (hq : Valid RS q) :
    SimpleGraph {v : V // selected v} where
  Adj a b := ∃ d : RS.D, RS.vertOf d = a.val ∧
    RS.vertOf (RS.alpha d) = b.val ∧ difference RS q d ≠ 0
  symm := ⟨by
    rintro a b ⟨d,ha,hb,hn⟩
    refine ⟨RS.alpha d,hb,?_,?_⟩
    · simpa only [RS.alpha_involutive] using ha
    · rw [difference_alpha RS hq]
      exact hn⟩
  loopless := ⟨by
    rintro a ⟨d,ha,hb,_⟩
    exact RS.no_self_loops d (ha.trans hb.symm)⟩

/-- No conservative nonzero difference can remain inside a source forest. -/
theorem difference_zero_of_forest (selected : V → Prop) (hsimple : SimpleSource RS)
    (hforest : ((rotationPrimalGraph RS).induce {v | selected v}).IsAcyclic)
    (q : RS.D → Color) (hq : Valid RS q)
    (hout : ∀ d, ¬selected (RS.vertOf d) → difference RS q d = 0) :
    ∀ d, difference RS q d = 0 := by
  let A := activeGraph RS selected q hq
  have ha : A.IsAcyclic := hforest.anti (by
    rintro a b ⟨d,hd,he,_⟩
    exact ⟨d,hd,he⟩)
  have hbranch : ∀ {a b}, A.Adj a b → ∃ w, A.Adj a w ∧ w ≠ b := by
    rintro a b ⟨d,hd,he,hn⟩
    obtain ⟨e,hv,hne,hqne⟩ := other_nonzero_difference RS hn
    have hselected : selected (RS.vertOf (RS.alpha e)) := by
      by_contra hs
      have hz := hout (RS.alpha e) hs
      rw [difference_alpha RS hq] at hz
      exact hqne hz
    refine ⟨⟨RS.vertOf (RS.alpha e),hselected⟩,⟨e,hv.trans hd,rfl,hqne⟩,?_⟩
    intro hw
    have heq : RS.vertOf (RS.alpha e) = RS.vertOf (RS.alpha d) :=
      (congrArg Subtype.val hw).trans he.symm
    exact hne (hsimple e d hv heq)
  have hempty := FiniteForestBranching.eq_bot A ha hbranch
  intro d
  by_contra hn
  have hd : selected (RS.vertOf d) := by
    by_contra hs
    exact hn (hout d hs)
  have he : selected (RS.vertOf (RS.alpha d)) := by
    by_contra hs
    exact hn ((difference_alpha RS hq d).symm.trans (hout (RS.alpha d) hs))
  have hadj : A.Adj ⟨RS.vertOf d,hd⟩ ⟨RS.vertOf (RS.alpha d),he⟩ :=
    ⟨d,rfl,rfl,hn⟩
  simp only [hempty, SimpleGraph.bot_adj] at hadj

/-- Separation exposes every corner at an exterior source vertex, including
the one whose target vertex lies inside the selected patch. -/
theorem outside_visible (selected : V → Prop) (hsimple : SimpleSource RS)
    (hsep : Separated RS selected) (hfix : ∀ d, RS.rho d ≠ d)
    (d : RS.D) (hd : ¬selected (RS.vertOf d)) :
    Visible RS (vertexRegion RS selected) d := by
  by_cases hk : vertexRegion RS selected d
  · have hop : selected (RS.vertOf (RS.alpha d)) := hk.resolve_left hd
    let e := RS.rho.symm d
    have hv : RS.vertOf e = RS.vertOf d := by
      simpa only [e, Equiv.apply_symm_apply] using (RS.vert_rho (RS.rho.symm d)).symm
    have hphi : RS.phi.symm d = RS.alpha e := by
      apply RS.phi.injective
      simp only [Equiv.apply_symm_apply, RotationSystem.phi_apply, RS.alpha_involutive, e]
    have hnot : ¬selected (RS.vertOf (RS.alpha e)) := by
      intro he
      have hp := hsep _ hd _ _ hop he ⟨d,rfl,rfl⟩ ⟨e,hv,rfl⟩
      have hde : d = e := hsimple d e hv.symm hp
      apply hfix d
      rw [hde]
      simpa only [e, Equiv.apply_symm_apply] using hde
    apply Or.inr
    rw [hphi]
    change ¬(selected (RS.vertOf (RS.alpha e)) ∨ selected (RS.vertOf (RS.alpha (RS.alpha e))))
    simpa only [RS.alpha_involutive, hv] using not_or.mpr ⟨hnot,hd⟩
  · exact Or.inl hk

theorem rho_fixfree (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS)
    (d : RS.D) : RS.rho d ≠ d := by
  intro he
  exact VertexCodeCyclicEncoder.rot_ne hcubic hrotation
    (⟨d,rfl⟩ : VertexCodeCyclicEncoder.At RS (RS.vertOf d)) (Subtype.ext he)

/-- Pairing describes only visible exterior observations; no colouring of
the selected source vertices is assumed. -/
def PairedExterior (selected : V → Prop) (base : Edge RS → Color) (c : V → Color) : Prop :=
  ∀ d, Visible RS (vertexRegion RS selected) d → corner RS base d = c (RS.vertOf d)

theorem outside_corners (selected : V → Prop) (hsimple : SimpleSource RS)
    (hsep : Separated RS selected) (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS)
    (base : Edge RS → Color) (c : V → Color) (hp : PairedExterior RS selected base c)
    (q : RS.D → Color) (hq : Summary RS (vertexRegion RS selected) base q) :
    ∀ d, ¬selected (RS.vertOf d) → q d = c (RS.vertOf d) := by
  intro d hd
  have hv := outside_visible RS selected hsimple hsep (rho_fixfree RS hcubic hrotation) d hd
  exact (hq.2 d hv).trans (hp d hv)

/-- Every compatible corner witness on this geometric family is coherent;
the collapse loses neither witnesses nor their counts. -/
theorem coherent (selected : V → Prop) (hsimple : SimpleSource RS)
    (hsep : Separated RS selected) (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS)
    (hforest : ((rotationPrimalGraph RS).induce {v | selected v}).IsAcyclic)
    (base : Edge RS → Color)
    (hout : ∀ d, ¬vertexRegion RS selected d → Star RS base d)
    (c : V → Color) (hp : PairedExterior RS selected base c)
    (q : RS.D → Color) (hq : Summary RS (vertexRegion RS selected) base q) : Coherent RS q := by
  have hv := summary_valid RS (vertexRegion_closed RS selected) hout hq
  have ho := outside_corners RS selected hsimple hsep hcubic hrotation base c hp q hq
  apply coherent_of_difference_zero RS hrotation
  apply difference_zero_of_forest RS selected hsimple hforest q hv
  intro d hd
  unfold difference
  rw [ho d hd, ho (RS.rho d) (by simpa only [RS.vert_rho] using hd), RS.vert_rho,
    color_add_self]

/-- The source witness is derived from the exact patch choices and fixes
every supplied exterior source value. -/
theorem source_witness (selected : V → Prop) (hsimple : SimpleSource RS)
    (hsep : Separated RS selected) (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS)
    (hforest : ((rotationPrimalGraph RS).induce {v | selected v}).IsAcyclic)
    (base : Edge RS → Color)
    (hout : ∀ d, ¬vertexRegion RS selected d → Star RS base d)
    (c : V → Color) (hp : PairedExterior RS selected base c)
    (q : RS.D → Color) (hq : Summary RS (vertexRegion RS selected) base q) :
    ∃ s : ThreeVertexColoring RS, (∀ d, s.colour (RS.vertOf d) = q d) ∧
      ∀ v, ¬selected v → s.colour v = c v := by
  have hv := summary_valid RS (vertexRegion_closed RS selected) hout hq
  have hc := coherent RS selected hsimple hsep hcubic hrotation hforest base hout c hp q hq
  have ho := outside_corners RS selected hsimple hsep hcubic hrotation base c hp q hq
  refine ⟨sourceColouring RS q hv hc,vertexColour_dart RS hc,?_⟩
  intro v hn
  have hpos : 0 < (RS.dartsAt v).card := by rw [hcubic v]; decide
  obtain ⟨d,hd⟩ := Finset.card_pos.mp hpos
  have he : RS.vertOf d = v := by simpa [RotationSystem.dartsAt] using hd
  rw [← he]
  change vertexColour RS q (RS.vertOf d) = c (RS.vertOf d)
  rw [vertexColour_dart RS hc]
  exact ho d (by simpa only [he] using hn)

theorem visible_outside_source (selected : V → Prop) {d : RS.D}
    (hd : Visible RS (vertexRegion RS selected) d) : ¬selected (RS.vertOf d) := by
  intro hs
  rcases hd with hd | hd
  · exact hd (Or.inl hs)
  · apply hd
    apply Or.inr
    simpa only [vert_alpha_phi_symm] using hs

theorem source_corners (s : ThreeVertexColoring RS) :
    corner RS (DualTruncateColoring.colouring RS s) = fun d => s.colour (RS.vertOf d) := by
  funext d
  exact star_colour_two RS s.colour d

/-- Source choices satisfying the supplied exterior values. Interior values
are variables, rather than part of the supplied exterior contract. -/
abbrev SourceFibre (selected : V → Prop) (c : V → Color) :=
  {s : ThreeVertexColoring RS // ∀ v, ¬selected v → s.colour v = c v}

theorem source_summary (selected : V → Prop) (base : Edge RS → Color)
    (c : V → Color) (hp : PairedExterior RS selected base c)
    (s : SourceFibre RS selected c) :
    Summary RS (vertexRegion RS selected) base (fun d => s.val.colour (RS.vertOf d)) := by
  have hv := corners_valid RS (DualTruncateColoring.colouring RS s.val)
    (colouring_nonzero RS s.val)
  rw [source_corners] at hv
  refine ⟨fun d _ => ⟨hv.1 d,hv.1 (RS.phi d),hv.2.1 d,hv.2.2 d⟩,?_⟩
  intro d hd
  exact (s.property _ (visible_outside_source RS selected hd)).trans (hp d hd).symm

theorem source_ext {s t : ThreeVertexColoring RS} (h : s.colour = t.colour) : s = t := by
  cases s
  cases t
  cases h
  rfl

variable (selected : V → Prop) (hsimple : SimpleSource RS)
  (hsep : Separated RS selected) (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS)
  (hforest : ((rotationPrimalGraph RS).induce {v | selected v}).IsAcyclic)
  (base : Edge RS → Color)
  (hout : ∀ d, ¬vertexRegion RS selected d → Star RS base d)
  (c : V → Color) (hp : PairedExterior RS selected base c)

/-- Eliminate corner differences using the proved geometric family law. -/
def toSource (q : {q : RS.D → Color // Summary RS (vertexRegion RS selected) base q}) :
    SourceFibre RS selected c :=
  let h := source_witness RS selected hsimple hsep hcubic hrotation hforest base hout c hp
    q.val q.property
  ⟨h.choose,h.choose_spec.2⟩

theorem toSource_dart
    (q : {q : RS.D → Color // Summary RS (vertexRegion RS selected) base q}) (d : RS.D) :
    (toSource RS selected hsimple hsep hcubic hrotation hforest base hout c hp q).val.colour
      (RS.vertOf d) = q.val d :=
  (source_witness RS selected hsimple hsep hcubic hrotation hforest base hout c hp
    q.val q.property).choose_spec.1 d

/-- Exact source-vertex and joint-corner representations of the same fibre. -/
def cornerSourceEquiv :
    {q : RS.D → Color // Summary RS (vertexRegion RS selected) base q} ≃
      SourceFibre RS selected c where
  toFun := toSource RS selected hsimple hsep hcubic hrotation hforest base hout c hp
  invFun s := ⟨fun d => s.val.colour (RS.vertOf d),source_summary RS selected base c hp s⟩
  left_inv q := by
    apply Subtype.ext
    funext d
    exact toSource_dart RS selected hsimple hsep hcubic hrotation hforest base hout c hp q d
  right_inv s := by
    apply Subtype.ext
    apply source_ext RS
    funext v
    have hpos : 0 < (RS.dartsAt v).card := by rw [hcubic v]; decide
    obtain ⟨d,hd⟩ := Finset.card_pos.mp hpos
    have he : RS.vertOf d = v := by simpa [RotationSystem.dartsAt] using hd
    simpa only [he] using toSource_dart RS selected hsimple hsep hcubic hrotation hforest
      base hout c hp ⟨fun d => s.val.colour (RS.vertOf d),source_summary RS selected base c hp s⟩ d

/-- Every actual target extension is reconstructed from its source choices,
and every compatible source choice reconstructs the same exterior exactly. -/
def extensionSourceEquiv :
    {t : (rotation RS).EdgeColoring Color //
      (rotation RS).IsTaitEdgeColoring t ∧ Extends RS (vertexRegion RS selected) base t} ≃
      SourceFibre RS selected c :=
  (extensionEquiv RS (vertexRegion_closed RS selected) hout).trans
    (cornerSourceEquiv RS selected hsimple hsep hcubic hrotation hforest base hout c hp)

include hsimple hsep hcubic hrotation hforest hout hp in
/-- Counts are preserved on the stated geometric domain, not merely support. -/
theorem extension_source_count :
    Nat.card {t : (rotation RS).EdgeColoring Color //
      (rotation RS).IsTaitEdgeColoring t ∧ Extends RS (vertexRegion RS selected) base t} =
      Nat.card (SourceFibre RS selected c) :=
  Nat.card_congr (extensionSourceEquiv RS selected hsimple hsep hcubic hrotation hforest
    base hout c hp)

end
end Mettapedia.GraphTheory.FourColor.DualTruncateForestCollapse
