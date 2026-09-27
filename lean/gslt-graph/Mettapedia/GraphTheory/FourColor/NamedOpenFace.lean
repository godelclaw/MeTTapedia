import Mettapedia.GraphTheory.FourColor.NamedFaceRecord
import Mettapedia.GraphTheory.FourColor.FaceReturnSum
import Mettapedia.GraphTheory.FourColor.OpenTangleMarkedFace

/-!
# Named face records for an open side

Ports are always observed in standard boundary coordinates. Persistent
dart names may be absent or aliased, including aliases of ports. Equality
of side records preserves both the cyclic returns and the port matching
used by actual tangle sewing.
-/

namespace Mettapedia.GraphTheory.FourColor.NamedOpenFace

open GoertzelV24OpenTangleComposition GoertzelV24OrderedCutFaceReturnProfile
open OpenTangleMarkedFace FaceReturnSum

noncomputable section
attribute [local instance] Classical.propDecidable

variable {M K J R J' R' : Type*}
  [Fintype M] [Fintype K] [Fintype J] [DecidableEq J]
  [Fintype R] [DecidableEq R] [Fintype J'] [DecidableEq J']
  [Fintype R'] [DecidableEq R']

def names (c : R ≃ K) (obs : M → Option (J ⊕ R)) : K ⊕ M → Option (J ⊕ R)
  | .inl k => some (.inr (c.symm k))
  | .inr m => obs m

abbrev Hit (c : R ≃ K) (obs : M → Option (J ⊕ R)) := NamedFaceRecord.Hit (names c obs)

abbrev Point (c : R ≃ K) (obs : M → Option (J ⊕ R)) := NamedFaceRecord.Point (names c obs)

theorem port_hit (c : R ≃ K) (obs : M → Option (J ⊕ R)) (r : R) :
    Hit c obs (.inr r) := by
  exact ⟨.inl (c r), by simp [names]⟩

def port (c : R ≃ K) (obs : M → Option (J ⊕ R)) (k : K) : Point c obs :=
  ⟨.inr (c.symm k), port_hit c obs _⟩

def record {W : Type*} (right : OpenTangleData W J R) (c : R ≃ K)
    (obs : M → Option (J ⊕ R)) : NamedFaceRecord.Record (K ⊕ M) :=
  NamedFaceRecord.record (openPhi right) (names c obs)

variable {W W' : Type*} (old : OpenTangleData W J R) (new : OpenTangleData W' J' R')
  (oc : R ≃ K) (nc : R' ≃ K)
  (oo : M → Option (J ⊕ R)) (no : M → Option (J' ⊕ R'))
  (heq : record old oc oo = record new nc no)

def matching : Point oc oo ≃ Point nc no :=
  NamedFaceRecord.matching (openPhi old) (names oc oo) (openPhi new) (names nc no) heq

theorem matching_port (k : K) :
    matching old new oc nc oo no heq (port oc oo k) = port nc no k := by
  have h := NamedFaceRecord.matching_point
    (openPhi old) (names oc oo) (openPhi new) (names nc no) heq (.inl k)
  have ho : NamedFaceRecord.point (names oc oo) (.inl k) = some (port oc oo k) :=
    (NamedFaceRecord.point_some_iff _ _ _).mpr rfl
  have hn : NamedFaceRecord.point (names nc no) (.inl k) = some (port nc no k) :=
    (NamedFaceRecord.point_some_iff _ _ _).mpr rfl
  simp only [ho, hn, Option.map_some, Option.some.injEq] at h
  exact h

theorem matching_return (a : Point oc oo) :
    matching old new oc nc oo no heq (nextHitPerm (openPhi old) (Hit oc oo) a) =
      nextHitPerm (openPhi new) (Hit nc no) (matching old new oc nc oo no heq a) :=
  NamedFaceRecord.matching_return _ _ _ _ heq a

theorem matching_point (m : M) :
    (NamedFaceRecord.point (names oc oo) (.inr m)).map (matching old new oc nc oo no heq) =
      NamedFaceRecord.point (names nc no) (.inr m) :=
  NamedFaceRecord.matching_point _ _ _ _ heq _

variable {I L : Type*} [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L]
  (leftHit : I ⊕ L → Prop) (hleft : ∀ l, leftHit (.inr l)) (outside : L ≃ K)

def totalHit (c : R ≃ K) (obs : M → Option (J ⊕ R)) : Carrier I J L R → Prop :=
  Sum.elim leftHit (Hit c obs)

include hleft in
theorem seam_hit (c : R ≃ K) (obs : M → Option (J ⊕ R))
    (d : Carrier I J L R) (hd : IsSeam d) : totalHit leftHit c obs d := by
  rcases d with (i | l) | (j | r)
  · exact hd.elim
  · exact hleft l
  · exact hd.elim
  · exact port_hit c obs r

def totalMatching : {d // totalHit leftHit oc oo d} ≃ {d // totalHit leftHit nc no d} :=
  sumMatching leftHit (matching old new oc nc oo no heq)

theorem totalMatching_return (left : Equiv.Perm (I ⊕ L)) :
    (totalMatching old new oc nc oo no heq leftHit).permCongr
      (nextHitPerm (Equiv.sumCongr left (openPhi old)) (totalHit leftHit oc oo)) =
      nextHitPerm (Equiv.sumCongr left (openPhi new)) (totalHit leftHit nc no) :=
  sumMatching_permCongr left (openPhi old) (openPhi new) leftHit _ _ _
    (matching_return old new oc nc oo no heq)

/-- The record-induced dart correspondence commutes with the actual seam
partner swap. In particular an interior observation cannot become a port:
all port names have already been matched injectively. -/
theorem totalMatching_swap (d : {d // totalHit leftHit oc oo d}) :
    totalMatching old new oc nc oo no heq leftHit
        (observedSwap (outside.trans oc.symm) (totalHit leftHit oc oo)
          (seam_hit leftHit hleft oc oo) d) =
      observedSwap (outside.trans nc.symm) (totalHit leftHit nc no)
        (seam_hit leftHit hleft nc no)
        (totalMatching old new oc nc oo no heq leftHit d) := by
  apply Subtype.ext
  rcases d with ⟨(i | l) | (j | r), hd⟩
  · rfl
  · change Sum.inr (matching old new oc nc oo no heq (port oc oo (outside l))).val =
      Sum.inr (port nc no (outside l)).val
    rw [matching_port]
  · let a : Point oc oo := ⟨Sum.inl j, hd⟩
    have hnot (r' : R') : (matching old new oc nc oo no heq a).val ≠ Sum.inr r' := by
      intro h
      have hm : matching old new oc nc oo no heq a = port nc no (nc r') := by
        apply Subtype.ext
        simpa [port] using h
      have ha := (matching old new oc nc oo no heq).injective
        (hm.trans (matching_port old new oc nc oo no heq (nc r')).symm)
      have hv := congrArg Subtype.val ha
      simp [a, port] at hv
    change Sum.inr (matching old new oc nc oo no heq a).val =
      seamSwap (outside.trans nc.symm) (Sum.inr (matching old new oc nc oo no heq a).val)
    cases h : (matching old new oc nc oo no heq a).val with
    | inl j' => rfl
    | inr r' => exact (hnot r' h).elim
  · have hm : matching old new oc nc oo no heq ⟨Sum.inr r, hd⟩ = port nc no (oc r) := by
      simpa [port] using matching_port old new oc nc oo no heq (oc r)
    change Sum.inl (Sum.inr ((outside.trans oc.symm).symm r)) =
      seamSwap (outside.trans nc.symm)
        (Sum.inr (matching old new oc nc oo no heq ⟨Sum.inr r, hd⟩).val)
    rw [hm]
    simp [seamSwap, port]

theorem totalMatching_swap_permCongr :
    (totalMatching old new oc nc oo no heq leftHit).permCongr
        (observedSwap (outside.trans oc.symm) (totalHit leftHit oc oo)
          (seam_hit leftHit hleft oc oo)) =
      observedSwap (outside.trans nc.symm) (totalHit leftHit nc no)
        (seam_hit leftHit hleft nc no) := by
  apply Equiv.ext
  intro d
  obtain ⟨a, rfl⟩ := (totalMatching old new oc nc oo no heq leftHit).surjective d
  simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply] using
    totalMatching_swap old new oc nc oo no heq leftHit hleft outside a

variable {V : Type*} [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W] [Fintype W'] [DecidableEq W']

include hleft in
/-- Equal finite per-side records preserve all observed cofaciality when
sewn to the same exterior, with the supplied standard port coordinates.
Both sides of this equivalence refer to `composeRotationSystem` itself. -/
theorem compose_sameCycle_iff (left : OpenTangleData V I L)
    (a b : {d // totalHit leftHit oc oo d}) :
    (left.composeRotationSystem old (outside.trans oc.symm)).phi.SameCycle
        (composeDartEquiv a.val) (composeDartEquiv b.val) ↔
      (left.composeRotationSystem new (outside.trans nc.symm)).phi.SameCycle
        (composeDartEquiv (totalMatching old new oc nc oo no heq leftHit a).val)
        (composeDartEquiv (totalMatching old new oc nc oo no heq leftHit b).val) := by
  apply (OpenTangleMarkedFace.compose_sameCycle_iff left old (outside.trans oc.symm)
    (totalHit leftHit oc oo) (seam_hit leftHit hleft oc oo) a b).trans
  apply Iff.trans _ (OpenTangleMarkedFace.compose_sameCycle_iff left new (outside.trans nc.symm)
    (totalHit leftHit nc no) (seam_hit leftHit hleft nc no)
    (totalMatching old new oc nc oo no heq leftHit a)
    (totalMatching old new oc nc oo no heq leftHit b)).symm
  rw [← totalMatching_return old new oc nc oo no heq leftHit (openPhi left),
    ← totalMatching_swap_permCongr old new oc nc oo no heq leftHit hleft outside,
    ← Equiv.permCongr_mul]
  exact (permCongr_sameCycle_iff (totalMatching old new oc nc oo no heq leftHit) _ a b).symm

def Observes (lo : M → Option (I ⊕ L)) (ro : M → Option (J ⊕ R))
    (m : M) : Carrier I J L R → Prop :=
  Sum.elim (fun d => lo m = some d) (fun d => ro m = some d)

def PhysicalCofacial (left : OpenTangleData V I L) (right : OpenTangleData W J R)
    (seam : L ≃ R) (lo : M → Option (I ⊕ L)) (ro : M → Option (J ⊕ R)) (m n : M) : Prop :=
  ∃ a b, Observes lo ro m a ∧ Observes lo ro n b ∧
    (left.composeRotationSystem right seam).phi.SameCycle (composeDartEquiv a) (composeDartEquiv b)

theorem observes_hit (lo : M → Option (I ⊕ L)) (ro : M → Option (J ⊕ R))
    (c : R ≃ K) (m : M) (d : Carrier I J L R) (hd : Observes lo ro m d) :
    totalHit (Hit outside lo) c ro d := by
  rcases d with a | b <;> exact ⟨.inr m, hd⟩

theorem matching_observes_iff (lo : M → Option (I ⊕ L)) (m : M)
    (d : {d // totalHit (Hit outside lo) oc oo d}) :
    Observes lo oo m d.val ↔
      Observes lo no m (totalMatching old new oc nc oo no heq (Hit outside lo) d).val := by
  rcases d with ⟨a | b, h⟩
  · rfl
  · exact NamedFaceRecord.matching_named_iff (openPhi old) (names oc oo)
      (openPhi new) (names nc no) heq (.inr m) ⟨b, h⟩

theorem physicalCofacial_iff_observed (left : OpenTangleData V I L)
    (right : OpenTangleData W J R) (c : R ≃ K)
    (lo : M → Option (I ⊕ L)) (ro : M → Option (J ⊕ R)) (m n : M) :
    PhysicalCofacial left right (outside.trans c.symm) lo ro m n ↔
      ∃ a b : {d // totalHit (Hit outside lo) c ro d},
        Observes lo ro m a.val ∧ Observes lo ro n b.val ∧
        (left.composeRotationSystem right (outside.trans c.symm)).phi.SameCycle
          (composeDartEquiv a.val) (composeDartEquiv b.val) := by
  constructor
  · rintro ⟨a, b, ha, hb, hc⟩
    exact ⟨⟨a, observes_hit outside lo ro c m a ha⟩,
      ⟨b, observes_hit outside lo ro c n b hb⟩, ha, hb, hc⟩
  · rintro ⟨a, b, ha, hb, hc⟩
    exact ⟨a.val, b.val, ha, hb, hc⟩

include heq in
/-- The named-dart formulation used by vertex-side reassembly. Absence and
aliasing are handled by the record, rather than additional disjointness
assumptions on the observations. -/
theorem physicalCofacial_iff (left : OpenTangleData V I L)
    (lo : M → Option (I ⊕ L)) (m n : M) :
    PhysicalCofacial left old (outside.trans oc.symm) lo oo m n ↔
      PhysicalCofacial left new (outside.trans nc.symm) lo no m n := by
  rw [physicalCofacial_iff_observed outside, physicalCofacial_iff_observed outside]
  have hs := compose_sameCycle_iff old new oc nc oo no heq (Hit outside lo)
    (port_hit outside lo) outside left
  constructor
  · rintro ⟨a, b, ha, hb, hc⟩
    exact ⟨totalMatching old new oc nc oo no heq (Hit outside lo) a,
      totalMatching old new oc nc oo no heq (Hit outside lo) b,
      (matching_observes_iff old new oc nc oo no heq outside lo m a).mp ha,
      (matching_observes_iff old new oc nc oo no heq outside lo n b).mp hb,
      (hs a b).mp hc⟩
  · rintro ⟨a, b, ha, hb, hc⟩
    obtain ⟨a, rfl⟩ := (totalMatching old new oc nc oo no heq (Hit outside lo)).surjective a
    obtain ⟨b, rfl⟩ := (totalMatching old new oc nc oo no heq (Hit outside lo)).surjective b
    exact ⟨a, b,
      (matching_observes_iff old new oc nc oo no heq outside lo m a).mpr ha,
      (matching_observes_iff old new oc nc oo no heq outside lo n b).mpr hb,
      (hs a b).mpr hc⟩

end
end Mettapedia.GraphTheory.FourColor.NamedOpenFace
