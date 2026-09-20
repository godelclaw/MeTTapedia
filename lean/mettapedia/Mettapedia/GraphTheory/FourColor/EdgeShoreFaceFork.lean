import Mettapedia.GraphTheory.FourColor.OpenTangleReplacementEuler
import Mettapedia.GraphTheory.FourColor.PermutationFirstReturnRestriction
import Mettapedia.GraphTheory.FourColor.FaceReturnSum

/-!
# Face gluing across a partition of edges

Two edge pieces meet at vertices, so their face permutations cannot simply be
sewn as though their vertex rotations had disjoint carriers. First restrict
the vertex rotation to each dart shore by first return. The correction back
to the original rotation is supported only at turns crossing between shores.
Conjugating that correction by the edge permutation turns it into a supported
face rewire. The existing boundary-rewiring calculus then computes the exact
parent face count, including faces that disappear from the interface.

No planarity or cubicity is needed for the permutation identity. A bound on
the number of marked darts is a separate hypothesis supplied by a width bound.
-/

namespace Mettapedia.GraphTheory.FourColor.EdgeShoreFaceFork

open Equiv Equiv.Perm
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24RetainedSpliceFaceCount
open PermutationFirstReturnRestriction BoundaryRewireCycles
open OpenTangleReplacementEuler

noncomputable section
attribute [local instance] Classical.propDecidable

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The disjoint union of the two restricted vertex rotations. -/
def splitRotation (rho : Perm D) (side : D → Prop) : Perm D :=
  (Equiv.sumCompl side).permCongr
    (Equiv.sumCongr (nextHitPerm rho side) (nextHitPerm rho (fun d => ¬ side d)))

theorem splitRotation_apply_pos (rho : Perm D) (side : D → Prop)
    (d : D) (hd : side d) :
    splitRotation rho side d = (nextHitPerm rho side ⟨d, hd⟩).1 := by
  simp [splitRotation, Equiv.permCongr_apply, Equiv.sumCompl_symm_apply_of_pos hd]

theorem splitRotation_apply_neg (rho : Perm D) (side : D → Prop)
    (d : D) (hd : ¬ side d) :
    splitRotation rho side d = (nextHitPerm rho (fun x => ¬ side x) ⟨d, hd⟩).1 := by
  simp [splitRotation, Equiv.permCongr_apply, Equiv.sumCompl_symm_apply_of_neg hd]

/-- Turns which change their edge shore. -/
def Crossing (rho : Perm D) (side : D → Prop) (d : D) : Prop :=
  ¬ (side (rho d) ↔ side d)

theorem splitRotation_eq_of_not_crossing (rho : Perm D) (side : D → Prop)
    (d : D) (hd : ¬ Crossing rho side d) : splitRotation rho side d = rho d := by
  have hs : side (rho d) ↔ side d := not_not.mp hd
  by_cases h : side d
  · rw [splitRotation_apply_pos rho side d h]
    exact nextHit_apply_of_step rho side ⟨d, h⟩ (hs.mpr h)
  · rw [splitRotation_apply_neg rho side d h]
    exact nextHit_apply_of_step rho (fun x => ¬ side x) ⟨d, h⟩
      (fun h' => h (hs.mp h'))

/-- A bounded, kernel-evaluable certificate for a proposed split rotation.
The certificate records first return, not merely membership in the same orbit. -/
theorem splitRotation_eq_of_arcs (rho q : Perm D) (side : D → Prop)
    (bound : ℕ) (hq : ∀ d, side (q d) ↔ side d)
    (harcs : ∀ d, ∃ n : Fin bound, 0 < n.val ∧ (rho ^ n.val) d = q d ∧
      ∀ i : Fin n.val, 0 < i.val → ¬ (side ((rho ^ i.val) d) ↔ side d)) :
    splitRotation rho side = q := by
  ext d
  obtain ⟨n, hn, heq, hmiss⟩ := harcs d
  have ha : ReturnArc rho (fun x => side x ↔ side d) d (q d) n.val :=
    ⟨hn, heq, fun i hi hil => hmiss ⟨i, hil⟩ hi⟩
  by_cases hd : side d
  · rw [splitRotation_apply_pos rho side d hd]
    exact congrArg Subtype.val (nextHit_eq_of_returnArc rho side
      ⟨d, hd⟩ ⟨q d, (hq d).mpr hd⟩ (by simpa [hd] using ha))
  · rw [splitRotation_apply_neg rho side d hd]
    exact congrArg Subtype.val (nextHit_eq_of_returnArc rho (fun x => ¬ side x)
      ⟨d, hd⟩ ⟨q d, fun h => hd ((hq d).mp h)⟩ (by simpa [hd] using ha))

/-- Child faces before their shared vertex turns are restored. -/
def before (rho alpha : Perm D) (side : D → Prop) : Perm D :=
  splitRotation rho side * alpha

/-- The face correction is the vertex correction transported across edges. -/
def rewire (rho alpha : Perm D) (side : D → Prop) : Perm D :=
  alpha⁻¹ * (splitRotation rho side)⁻¹ * rho * alpha

/-- The left child has only its own darts and their induced cyclic order. -/
def leftFace (rho alpha : Perm D) (side : D → Prop)
    (hside : ∀ d, side (alpha d) ↔ side d) : Perm {d // side d} :=
  nextHitPerm rho side * alpha.subtypePerm hside

/-- The complementary child, with its independently restricted rotation. -/
def rightFace (rho alpha : Perm D) (side : D → Prop)
    (hside : ∀ d, side (alpha d) ↔ side d) : Perm {d // ¬ side d} :=
  nextHitPerm rho (fun d => ¬ side d) *
    alpha.subtypePerm (fun d => not_congr (hside d))

/-- The existing edge-shore presentation keeps the ambient vertex rotation
and fixes darts of omitted edges. Restricting its faces to the retained darts
gives exactly the child face permutation used here. -/
theorem leftFace_eq_raw_return (rho alpha : Perm D) (side : D → Prop) [DecidablePred side]
    (hside : ∀ d, side (alpha d) ↔ side d) :
    leftFace rho alpha side hside =
      nextHitPerm (rho * ofSubtype (alpha.subtypePerm hside)) side := by
  exact (GoertzelV24RetainedRegionBoundaryOrder.nextHitPerm_mul_ofSubtype rho side _).symm

theorem rightFace_eq_raw_return (rho alpha : Perm D) (side : D → Prop) [DecidablePred side]
    (hside : ∀ d, side (alpha d) ↔ side d) :
    rightFace rho alpha side hside =
      nextHitPerm (rho * ofSubtype
        (alpha.subtypePerm (p := fun d => ¬ side d)
          (fun d => not_congr (hside d)))) (fun d => ¬ side d) := by
  exact (GoertzelV24RetainedRegionBoundaryOrder.nextHitPerm_mul_ofSubtype
    rho (fun d => ¬ side d) _).symm

/-- For an edge shore, edge partners stay in the same child. Splitting the
vertex turns then makes the pre-sewing faces a literal disjoint union. -/
theorem before_eq_sum (rho alpha : Perm D) (side : D → Prop)
    (hside : ∀ d, side (alpha d) ↔ side d) :
    before rho alpha side = (Equiv.sumCompl side).permCongr
      (Equiv.sumCongr (leftFace rho alpha side hside)
        (rightFace rho alpha side hside)) := by
  apply Equiv.ext
  intro d
  by_cases hd : side d
  · have ha := (hside d).mpr hd
    simp only [before, Perm.mul_apply, splitRotation_apply_pos rho side (alpha d) ha,
      Equiv.permCongr_apply, Equiv.sumCompl_symm_apply_of_pos hd,
      Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
    rfl
  · have ha : ¬ side (alpha d) := fun h => hd ((hside d).mp h)
    simp only [before, Perm.mul_apply, splitRotation_apply_neg rho side (alpha d) ha,
      Equiv.permCongr_apply, Equiv.sumCompl_symm_apply_of_neg hd,
      Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]
    rfl

theorem before_face_count (rho alpha : Perm D) (side : D → Prop)
    (hside : ∀ d, side (alpha d) ↔ side d) :
    (before rho alpha side).partition.parts.card =
      (leftFace rho alpha side hside).partition.parts.card +
        (rightFace rho alpha side hside).partition.parts.card := by
  rw [before_eq_sum rho alpha side hside, card_permCongr_partition_parts, cycle_count_sum]

theorem before_left (rho alpha : Perm D) (side : D → Prop)
    (hside : ∀ d, side (alpha d) ↔ side d) (d : {d // side d}) :
    before rho alpha side d.val = (leftFace rho alpha side hside d).val := by
  rw [before, Perm.mul_apply,
    splitRotation_apply_pos rho side (alpha d.val) ((hside d.val).mpr d.property)]
  rfl

theorem before_right (rho alpha : Perm D) (side : D → Prop)
    (hside : ∀ d, side (alpha d) ↔ side d) (d : {d // ¬ side d}) :
    before rho alpha side d.val = (rightFace rho alpha side hside d).val := by
  rw [before, Perm.mul_apply, splitRotation_apply_neg rho side (alpha d.val)
    (fun h => d.property ((hside d.val).mp h))]
  rfl

/-- The return record before gluing is read independently from the left
child. No traversal of the other child's interior is needed. -/
theorem before_return_left (rho alpha : Perm D) (side hit : D → Prop)
    (hside : ∀ d, side (alpha d) ↔ side d)
    (d : {d : {d // side d} // hit d.val}) :
    (nextHitPerm (before rho alpha side) hit ⟨d.val.val, d.property⟩).val =
      (nextHitPerm (leftFace rho alpha side hside) (fun x => hit x.val) d).val.val := by
  exact FaceReturnSum.nextHit_map _ _ Subtype.val
    (before_left rho alpha side hside) _ _ (fun _ => Iff.rfl) d

theorem before_return_right (rho alpha : Perm D) (side hit : D → Prop)
    (hside : ∀ d, side (alpha d) ↔ side d)
    (d : {d : {d // ¬ side d} // hit d.val}) :
    (nextHitPerm (before rho alpha side) hit ⟨d.val.val, d.property⟩).val =
      (nextHitPerm (rightFace rho alpha side hside) (fun x => hit x.val) d).val.val := by
  exact FaceReturnSum.nextHit_map _ _ Subtype.val
    (before_right rho alpha side hside) _ _ (fun _ => Iff.rfl) d

/-- Only partners of crossing vertex turns need to be named. -/
def Mark (rho alpha : Perm D) (side : D → Prop) (d : D) : Prop :=
  Crossing rho side (alpha d)

omit [DecidableEq D] in
/-- The rewire has bounded size when crossing turns lie over a bounded
middle-vertex set. In a cubic map the fibre bound is three. -/
theorem card_mark_le {V : Type*} [Fintype V] [DecidableEq V]
    (rho alpha : Perm D) (side : D → Prop) (vertex : D → V)
    (middle : Finset V) (degree : ℕ)
    (hcross : ∀ d, Crossing rho side d → vertex d ∈ middle)
    (hdegree : ∀ v, Fintype.card {d // vertex d = v} ≤ degree) :
    Fintype.card {d // Mark rho alpha side d} ≤ middle.card * degree := by
  let f : {d // Mark rho alpha side d} →
      (v : {v // v ∈ middle}) × {d // vertex d = v.val} :=
    fun d => ⟨⟨vertex (alpha d.val), hcross _ d.property⟩, ⟨alpha d.val, rfl⟩⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply alpha.injective
    exact congrArg (fun x => x.2.val) h
  have hc := Fintype.card_le_of_injective f hf
  have hb : Fintype.card ((v : {v // v ∈ middle}) × {d // vertex d = v.val}) ≤
      middle.card * degree := by
    rw [Fintype.card_sigma]
    calc
      ∑ v : {v // v ∈ middle}, Fintype.card {d // vertex d = v.val} ≤
          ∑ _v : {v // v ∈ middle}, degree := Finset.sum_le_sum (fun v _ => hdegree v.val)
      _ = middle.card * degree := by simp
  exact hc.trans hb

/-- A shared vertex is incident with a dart from each child. -/
def Mixed {V : Type*} (vertex : D → V) (side : D → Prop) (v : V) : Prop :=
  ∃ d e, vertex d = v ∧ vertex e = v ∧ side d ∧ ¬ side e

omit [Fintype D] [DecidableEq D] in
theorem crossing_mixed {V : Type*} (rho : Perm D) (side : D → Prop)
    (vertex : D → V) (hvertex : ∀ d, vertex (rho d) = vertex d)
    (d : D) (hd : Crossing rho side d) : Mixed vertex side (vertex d) := by
  by_cases hs : side d
  · refine ⟨d, rho d, rfl, hvertex d, hs, ?_⟩
    intro ht
    exact hd ⟨fun _ => hs, fun _ => ht⟩
  · have ht : side (rho d) := by
      by_contra hn
      exact hd ⟨fun h => False.elim (hn h), fun h => False.elim (hs h)⟩
    exact ⟨rho d, d, hvertex d, rfl, ht, hs⟩

omit [DecidableEq D] in
/-- Width is measured at actual shared vertices. No mark-supply premise is
needed: vertex preservation proves every changed turn lies at such a vertex. -/
theorem card_mark_le_of_middle_width {V : Type*} [Fintype V] [DecidableEq V]
    (rho alpha : Perm D) (side : D → Prop) (vertex : D → V)
    (hvertex : ∀ d, vertex (rho d) = vertex d) (degree width : ℕ)
    (hdegree : ∀ v, Fintype.card {d // vertex d = v} ≤ degree)
    (hwidth : (Finset.univ.filter (Mixed vertex side)).card ≤ width) :
    Fintype.card {d // Mark rho alpha side d} ≤ width * degree := by
  apply (card_mark_le rho alpha side vertex
    (Finset.univ.filter (Mixed vertex side)) degree ?_ hdegree).trans
      (Nat.mul_le_mul_right degree hwidth)
  intro d hd
  simpa using crossing_mixed rho side vertex hvertex d hd

theorem before_mul_rewire (rho alpha : Perm D) (side : D → Prop) :
    before rho alpha side * rewire rho alpha side = rho * alpha := by
  simp [before, rewire, mul_assoc]

theorem rewire_fixed_of_not_mark (rho alpha : Perm D) (side : D → Prop)
    (d : D) (hd : ¬ Mark rho alpha side d) : rewire rho alpha side d = d := by
  have h := splitRotation_eq_of_not_crossing rho side (alpha d) hd
  simp only [rewire, Perm.mul_apply]
  change alpha.symm ((splitRotation rho side).symm (rho (alpha d))) = d
  rw [← h, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem rewire_mark_iff (rho alpha : Perm D) (side : D → Prop) (d : D) :
    Mark rho alpha side (rewire rho alpha side d) ↔ Mark rho alpha side d := by
  constructor
  · intro h
    by_contra hd
    exact hd (rewire_fixed_of_not_mark rho alpha side d hd ▸ h)
  · intro h
    by_contra hd
    have he := rewire_fixed_of_not_mark rho alpha side (rewire rho alpha side d) hd
    have he' := (rewire rho alpha side).injective he
    exact hd (he'.symm ▸ h)

/-- External interface marks can be retained alongside the fork's own
crossing marks; the rewire still preserves that enlarged marked carrier. -/
theorem rewire_hit_iff (rho alpha : Perm D) (side hit : D → Prop)
    (hmark : ∀ d, Mark rho alpha side d → hit d) (d : D) :
    hit (rewire rho alpha side d) ↔ hit d := by
  have fixed (x : D) (hx : ¬ hit x) : rewire rho alpha side x = x :=
    rewire_fixed_of_not_mark rho alpha side x (fun h => hx (hmark x h))
  constructor
  · intro h
    by_contra hd
    exact hd (fixed d hd ▸ h)
  · intro h
    by_contra hd
    have he := (rewire rho alpha side).injective (fixed _ hd)
    exact hd (he.symm ▸ h)

def boundaryRewireOn (rho alpha : Perm D) (side hit : D → Prop)
    (hmark : ∀ d, Mark rho alpha side d → hit d) : Perm {d // hit d} :=
  (rewire rho alpha side).subtypePerm (rewire_hit_iff rho alpha side hit hmark)

theorem boundaryRewireOn_extend (rho alpha : Perm D) (side hit : D → Prop)
    (hmark : ∀ d, Mark rho alpha side d → hit d) :
    ofSubtype (boundaryRewireOn rho alpha side hit hmark) = rewire rho alpha side := by
  apply ofSubtype_subtypePerm
  intro d hd
  by_contra h
  exact hd (rewire_fixed_of_not_mark rho alpha side d (fun hm => h (hmark d hm)))

theorem parent_return_on (rho alpha : Perm D) (side hit : D → Prop)
    (hmark : ∀ d, Mark rho alpha side d → hit d) :
    nextHitPerm (rho * alpha) hit =
      nextHitPerm (before rho alpha side) hit * boundaryRewireOn rho alpha side hit hmark := by
  have hp : rho * alpha = before rho alpha side *
      ofSubtype (boundaryRewireOn rho alpha side hit hmark) := by
    rw [boundaryRewireOn_extend, before_mul_rewire]
  rw [hp]
  exact MarkedFaceReturnRewire.nextHitPerm_rewire _ _ _

/-- After sewing, forget marks internalized at the parent. One may take
`hit` to be the union of crossing marks and the desired outgoing interface. -/
theorem parent_return_project (rho alpha : Perm D) (side hit keep : D → Prop)
    (hmark : ∀ d, Mark rho alpha side d → hit d)
    (hkeep : ∀ d, keep d → hit d) :
    nextHitPerm (nextHitPerm (before rho alpha side) hit *
        boundaryRewireOn rho alpha side hit hmark) (fun d => keep d.val) =
      (nestedMarks keep hit hkeep).permCongr (nextHitPerm (rho * alpha) keep) := by
  rw [← parent_return_on rho alpha side hit hmark]
  exact nextHit_nested (rho * alpha) keep hit hkeep

def boundaryRewire (rho alpha : Perm D) (side : D → Prop) :
    Perm {d // Mark rho alpha side d} :=
  (rewire rho alpha side).subtypePerm (rewire_mark_iff rho alpha side)

theorem boundaryRewire_extend (rho alpha : Perm D) (side : D → Prop) :
    ofSubtype (boundaryRewire rho alpha side) = rewire rho alpha side := by
  apply ofSubtype_subtypePerm
  intro d hd
  by_contra h
  exact hd (rewire_fixed_of_not_mark rho alpha side d h)

/-- The literal parent face permutation, not merely its cycle count. -/
theorem parent_face (rho alpha : Perm D) (side : D → Prop) :
    rho * alpha = before rho alpha side * ofSubtype (boundaryRewire rho alpha side) := by
  rw [boundaryRewire_extend, before_mul_rewire]

/-- The parent return record is obtained from child returns by finite rewiring. -/
theorem parent_return (rho alpha : Perm D) (side : D → Prop) :
    nextHitPerm (rho * alpha) (Mark rho alpha side) =
      nextHitPerm (before rho alpha side) (Mark rho alpha side) *
        boundaryRewire rho alpha side := by
  rw [parent_face rho alpha side]
  exact MarkedFaceReturnRewire.nextHitPerm_rewire _ _ _

/-- Exact correction, including face cycles invisible at the interface. -/
theorem parent_face_count (rho alpha : Perm D) (side : D → Prop) :
    (rho * alpha).partition.parts.card +
        (nextHitPerm (before rho alpha side) (Mark rho alpha side)).partition.parts.card =
      (before rho alpha side).partition.parts.card +
        (nextHitPerm (before rho alpha side) (Mark rho alpha side) *
          boundaryRewire rho alpha side).partition.parts.card := by
  rw [parent_face rho alpha side]
  exact cycle_count_rewire _ _ _

/-- A two-child face-count law for actual edge-shore splitting. All dependence
on the shared vertices occurs in the named boundary return and its rewire. -/
theorem fork_face_count (rho alpha : Perm D) (side : D → Prop)
    (hside : ∀ d, side (alpha d) ↔ side d) :
    (rho * alpha).partition.parts.card +
        (nextHitPerm (before rho alpha side) (Mark rho alpha side)).partition.parts.card =
      (leftFace rho alpha side hside).partition.parts.card +
        (rightFace rho alpha side hside).partition.parts.card +
        (nextHitPerm (before rho alpha side) (Mark rho alpha side) *
          boundaryRewire rho alpha side).partition.parts.card := by
  rw [← before_face_count rho alpha side hside]
  exact parent_face_count rho alpha side

end
end Mettapedia.GraphTheory.FourColor.EdgeShoreFaceFork
