import Mettapedia.GraphTheory.FourColor.LockedKempeOrbitGeometry
import Mettapedia.GraphTheory.FourColor.ShortPathReconstruction
import Mettapedia.GraphTheory.FourColor.ShortPathKempeLifting

/-!
# A facial rollback crosses a trapped Kempe family

Remove face 1 from the spherical witness, freeing the path 4-10-8.
Two physical component switches on the smaller retained graph admit a
complete reconstruction. Both components are certified by saturated
chains, and their history is an actual GSLT route. Restoring the face
produces an old colouring unreachable by any Kempe history on the old
graph. Thus restriction can merge colouring classes whose physical
histories cannot be lifted back to the original patch.

All rollback and reconstruction regions have connected complementary
facial shores. This is a constructive certificate for this witness; no
universal rollback bound or repair-supply theorem is asserted.
-/

namespace Mettapedia.GraphTheory.FourColor.FacialRollbackKempeRepair

open GoertzelV24ForkInterfaceSupport IncidenceKempeSwitch KempeChainCertificate
open LockedKempeOrbit LockedKempeOrbitGeometry
open Mettapedia.GSLT.Ultrainfinite

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def coreFaces : Finset Face := selected.erase 1
def core : Finset Edge := old \ {11, 15}

theorem core_subset : core ⊆ old := Finset.sdiff_subset

/-- The rollback deletes exactly the two edges incident with vertex 10
in the old patch. The actual face and incidence representations agree. -/
theorem rollback_geometry :
    connectedRegion coreFaces ∧ connectedRegion coreFacesᶜ ∧
      insert 1 coreFaces = selected ∧ coreFaces.biUnion boundary = core ∧
      old \ core = {11, 15} ∧ inc 11 = {4, 10} ∧ inc 15 = {8, 10} := by
  decide +kernel

def restricted : (IncidenceKempeSwitch.graph inc core).Coloring (Fin 3) :=
  colouring inc core base (proper_of_subset core_subset (proper inc old base))

theorem restricted_apply (x : Edge) : restricted x = base x := rfl

def afterFirst : (IncidenceKempeSwitch.graph inc core).Coloring (Fin 3) :=
  colouring inc core ![1,0,2,2,0,1,1,0,2,0,2,1,1,2,0,0,1,0] (by decide +kernel)

def afterSecond : (IncidenceKempeSwitch.graph inc core).Coloring (Fin 3) :=
  colouring inc core ![1,2,0,2,0,1,1,2,0,0,2,1,1,0,0,0,1,2] (by decide +kernel)

private def firstChain : List Edge := [4,5,1,0]
private def secondChain : List Edge := [2,1,8,7,13,17]

local instance coreAdjDecidable : DecidableRel (IncidenceKempeSwitch.graph inc core).Adj :=
  IncidenceKempeSwitch.graphDecidableRel inc core

private theorem first_chain_certificate :
    firstChain.IsChain (IncidenceKempeSwitch.graph inc core).Adj ∧
      (∀ x ∈ firstChain, restricted x = 0 ∨ restricted x = 1) ∧
      (∀ x ∈ firstChain, ∀ y, (IncidenceKempeSwitch.graph inc core).Adj x y →
        (restricted y = 0 ∨ restricted y = 1) → y ∈ firstChain) := by
  unfold firstChain
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel

private theorem second_chain_certificate :
    secondChain.IsChain (IncidenceKempeSwitch.graph inc core).Adj ∧
      (∀ x ∈ secondChain, afterFirst x = 0 ∨ afterFirst x = 2) ∧
      (∀ x ∈ secondChain, ∀ y, (IncidenceKempeSwitch.graph inc core).Adj x y →
        (afterFirst y = 0 ∨ afterFirst y = 2) → y ∈ secondChain) := by
  unfold secondChain
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel

def firstComponent : (restricted.bicoloredSubgraph 0 1).ConnectedComponent :=
  (restricted.bicoloredSubgraph 0 1).connectedComponentMk ⟨4, Or.inr rfl⟩

def secondComponent : (afterFirst.bicoloredSubgraph 0 2).ConnectedComponent :=
  (afterFirst.bicoloredSubgraph 0 2).connectedComponentMk ⟨2, Or.inr rfl⟩

theorem first_step : afterFirst = restricted.swapOnKempeComponent 0 1 firstComponent := by
  obtain ⟨hc, ha, hs⟩ := first_chain_certificate
  apply DFunLike.ext
  intro x
  rw [restricted.swap_apply_of_chain 0 1 firstComponent firstChain hc ha hs
    (by decide : (4 : Edge) ∈ firstChain) (show (4 : Edge) ∈
      restricted.kempeComponentSet 0 1 firstComponent from ⟨Or.inr rfl, rfl⟩)]
  revert x
  decide +kernel

theorem second_step : afterSecond = afterFirst.swapOnKempeComponent 0 2 secondComponent := by
  obtain ⟨hc, ha, hs⟩ := second_chain_certificate
  apply DFunLike.ext
  intro x
  rw [afterFirst.swap_apply_of_chain 0 2 secondComponent secondChain hc ha hs
    (by decide : (2 : Edge) ∈ secondChain) (show (2 : Edge) ∈
      afterFirst.kempeComponentSet 0 2 secondComponent from ⟨Or.inr rfl, rfl⟩)]
  revert x
  decide +kernel

/-- The smaller patch carries an authored, two-step physical history. -/
def repairHistory : History restricted afterSecond :=
  .cons (first_step ▸ Step.switch restricted 0 1 firstComponent)
    (.cons (second_step ▸ Step.switch afterFirst 0 2 secondComponent) (.refl afterSecond))

theorem repairHistory_length : repairHistory.length = 2 := rfl

def completion : Edge → Fin 3 := ![1,2,0,2,0,1,1,2,0,0,2,0,1,0,1,2,1,2]

theorem completion_proper : Proper inc Finset.univ completion := by decide +kernel

theorem completion_agrees_core : ∀ x ∈ core, completion x = afterSecond x := by decide +kernel

/-- Reconstruction uses the existing literal gluing operation and keeps
every edge of the final smaller colouring. -/
def assembled : Edge → Fin 3 := EdgeColouringGluing.glue core afterSecond completion

theorem assembled_eq : assembled = completion := by
  funext x
  by_cases hx : x ∈ core
  · exact (EdgeColouringGluing.glue_left core afterSecond completion hx).trans
      (completion_agrees_core x hx).symm
  · simp [assembled, EdgeColouringGluing.glue, hx]

theorem assembled_proper : Proper inc Finset.univ assembled := assembled_eq ▸ completion_proper

theorem assembled_agrees_core : ∀ x ∈ core, assembled x = afterSecond x :=
  fun _ hx => EdgeColouringGluing.glue_left core afterSecond completion hx

def returned : (IncidenceKempeSwitch.graph inc old).Coloring (Fin 3) :=
  colouring inc old assembled (proper_of_subset (Finset.subset_univ _) assembled_proper)

/-- No history on the original retained graph can realize this return. -/
theorem return_not_reachable : ¬ Nonempty (History base returned) := by
  rintro ⟨p⟩
  exact no_history_strict_extension p (by decide : old ⊂ Finset.univ)
    ⟨assembled, assembled_proper, fun _ _ => rfl⟩

/-- The rolled-back edges are a literal simple path on the original
identifiers, so the generic short-path uniqueness theorem applies. -/
def erasedPath : OrderedEdgePath.Path inc ({11, 15} : Finset Edge) where
  length := 2
  positive := by decide
  vertex := ![4,10,8]
  vertex_injective := by decide +kernel
  edge := {
    toFun := fun i => ⟨![11,15] i, by fin_cases i <;> decide⟩
    invFun := fun x => if x.val = 11 then 0 else 1
    left_inv := by decide +kernel
    right_inv := by decide +kernel }
  endpoints := by decide +kernel

theorem core_union_path : core ∪ {11, 15} = old := by decide +kernel

/-- The first smaller switch leaves the image of restriction: both
deleted end edges would need colour 0 at their common vertex. -/
theorem intermediate_has_no_return :
    ¬ ∃ C : (IncidenceKempeSwitch.graph inc old).Coloring (Fin 3),
      ∀ x ∈ core, C x = afterFirst x := by
  rintro ⟨C, hC⟩
  have hends := erasedPath.end_colours_of_extension core
    (by decide : Disjoint core ({11,15} : Finset Edge)) afterFirst C 0 0
    (by decide +kernel) (by decide +kernel)
    (by rw [core_union_path]; exact proper inc old C) hC
  change C 11 = 0 ∧ C 15 = 0 at hends
  exact (proper inc old C) 11 (by decide) 15 (by decide) (by decide)
    ⟨10, by decide⟩ (hends.1.trans hends.2.symm)

theorem restored_end_colours :
    (∀ q, q ∉ profile inc core afterSecond erasedPath.first ↔ q = 0) ∧
      (∀ q, q ∉ profile inc core afterSecond erasedPath.last ↔ q = 2) := by decide +kernel

/-- The final smaller witness has a unique reconstruction on all old
edges, even though its history cannot lift to the old graph. -/
theorem unique_return (C : (IncidenceKempeSwitch.graph inc old).Coloring (Fin 3))
    (hC : ∀ x ∈ core, C x = afterSecond x) : ∀ x ∈ old, C x = assembled x := by
  have h := erasedPath.extension_unique_of_length_le_two (by decide) core
    (by decide : Disjoint core ({11,15} : Finset Edge)) afterSecond C assembled 0 2
    restored_end_colours.1 restored_end_colours.2
    (by rw [core_union_path]; exact proper inc old C)
    (by rw [core_union_path]; exact proper_of_subset (Finset.subset_univ _) assembled_proper)
    hC assembled_agrees_core
  rwa [core_union_path] at h

/-- The smaller history therefore cannot be the restriction of an old
history with any endpoint that agrees on the whole smaller patch. -/
theorem history_does_not_lift :
    ¬ ∃ C : (IncidenceKempeSwitch.graph inc old).Coloring (Fin 3),
      Nonempty (History base C) ∧ ∀ x ∈ core, C x = afterSecond x := by
  rintro ⟨C, ⟨p⟩, hC⟩
  exact no_history_strict_extension p (by decide : old ⊂ Finset.univ)
    ⟨assembled, assembled_proper, fun x hx => (unique_return C hC x hx).symm⟩

/-- These particular exterior edges retain their colours at every stage.
The certificate does not claim that the whole old colouring is retained. -/
def fixedEdges : Finset Edge := {3, 6, 10, 12, 16}

theorem fixed_preserved : ∀ x ∈ fixedEdges,
    x ∈ core ∧ afterFirst x = base x ∧ afterSecond x = base x ∧ completion x = base x := by
  decide +kernel

/-- Restore the rolled-back face, add the previously blocked face, then
close the remaining triangle. Face 4 stays the designated outer face. -/
def regions : Fin 4 → Finset Face := ![coreFaces, selected, selectedNext, insert 6 selectedNext]

theorem reconstruction_geometry :
    (∀ i, connectedRegion (regions i) ∧ connectedRegion (regions i)ᶜ) ∧
      regions 1 = insert 1 (regions 0) ∧ regions 2 = insert 5 (regions 1) ∧
      regions 3 = insert 6 (regions 2) ∧
      (regions 3).biUnion boundary = Finset.univ := by decide +kernel

theorem completion_on_rotation : Proper rotation.endpoints Finset.univ assembled := by
  rw [show rotation.endpoints = inc from funext endpoints_eq]
  exact assembled_proper

private theorem pair_missing (a b : Fin 3) (hab : a ≠ b) :
    ∃ m : Fin 3, ∀ q, q ∉ ({a,b} : Finset (Fin 3)) ↔ q = m := by
  have hcard : (({a,b} : Finset (Fin 3))ᶜ).card = 1 := by
    rw [Finset.card_compl]
    simp [hab]
  obtain ⟨m, hm, unique⟩ : ∃! m : Fin 3, m ∉ ({a,b} : Finset (Fin 3)) := by
    simpa only [Finset.mem_compl] using Finset.card_eq_one_iff_existsUnique.mp hcard
  exact ⟨m, fun q => ⟨unique q, fun h => h.symm ▸ hm⟩⟩

/-- The endpoint hypothesis of the lifting theorem follows from the two
actual retained edges at each end, for every proper smaller colouring. -/
theorem all_endpoint_colours (C : (IncidenceKempeSwitch.graph inc core).Coloring (Fin 3)) :
    ∃ m n : Fin 3,
      (∀ q, q ∉ profile inc core C erasedPath.first ↔ q = m) ∧
      (∀ q, q ∉ profile inc core C erasedPath.last ↔ q = n) := by
  have firstProfile : profile inc core C erasedPath.first = {C 0, C 10} := by
    change (core.filter fun e => (4 : Vertex) ∈ inc e).image C = _
    rw [show core.filter (fun e => (4 : Vertex) ∈ inc e) = {0,10} by decide +kernel]
    simp
  have lastProfile : profile inc core C erasedPath.last = {C 2, C 16} := by
    change (core.filter fun e => (8 : Vertex) ∈ inc e).image C = _
    rw [show core.filter (fun e => (8 : Vertex) ∈ inc e) = {2,16} by decide +kernel]
    simp
  obtain ⟨m, hm⟩ := pair_missing (C 0) (C 10)
    ((proper inc core C) 0 (by decide) 10 (by decide) (by decide) ⟨4, by decide⟩)
  obtain ⟨n, hn⟩ := pair_missing (C 2) (C 16)
    ((proper inc core C) 2 (by decide) 16 (by decide) (by decide) ⟨8, by decide⟩)
  exact ⟨m, n, firstProfile ▸ hm, lastProfile ▸ hn⟩

def initialImage : ShortPathKempeLifting.ImageColouring
    (inc := inc) (S := ({11,15} : Finset Edge)) core :=
  ⟨restricted, colouring inc (core ∪ {11,15}) base
    (by rw [core_union_path]; exact proper inc old base), fun _ _ => rfl⟩

def finalImage : ShortPathKempeLifting.ImageColouring
    (inc := inc) (S := ({11,15} : Finset Edge)) core :=
  ⟨afterSecond, colouring inc (core ∪ {11,15}) assembled
    (by rw [core_union_path]; exact proper_of_subset (Finset.subset_univ _) assembled_proper),
    assembled_agrees_core⟩

/-- Every smaller path between these endpoints must leave the image of
reconstruction, not only the displayed two-step repair. -/
theorem no_reconstructible_route :
    ¬ Nonempty (Route (ShortPathKempeLifting.ImageStep core) initialImage finalImage) := by
  rintro ⟨history⟩
  let initialOld := colouring inc (core ∪ {11,15}) base
    (by rw [core_union_path]; exact proper inc old base)
  obtain h := ShortPathKempeLifting.image_route_lifts erasedPath core (by decide)
    (by decide) all_endpoint_colours history initialOld (fun _ _ => rfl)
  change ∃ next : (graph inc (core ∪ {11,15})).Coloring (Fin 3),
    Nonempty (History initialOld next) ∧ ∀ x ∈ core, next x = afterSecond x at h
  have transfer (B : Finset Edge) (hB : B = old) (hb : Proper inc B base)
      (h : ∃ next : (graph inc B).Coloring (Fin 3),
        Nonempty (History (colouring inc B base hb) next) ∧
          ∀ x ∈ core, next x = afterSecond x) : False := by
    subst B
    have hbase : colouring inc old base hb = base := by
      apply DFunLike.ext
      intro x
      rfl
    apply history_does_not_lift
    simpa only [hbase] using h
  exact transfer _ core_union_path _ h

end Mettapedia.GraphTheory.FourColor.FacialRollbackKempeRepair
