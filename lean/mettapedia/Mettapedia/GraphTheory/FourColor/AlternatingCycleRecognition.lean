import Mettapedia.GraphTheory.FourColor.CycleFrameWalk
import Mettapedia.GraphTheory.FourColor.HexagonalCollarProgress
import Mettapedia.GraphTheory.FourColor.FacialCycleChord

/-!
# Simple alternating cycles supply complete geometric rows

The input is a simple cyclic vertex order with alternating local turns in
the actual rotation system. Spherical separation constructs its facial
sides; short port faces then exclude chords and construct both complete
interfaces. Neither an interior region nor its boundary maps are assumed.
-/

namespace Mettapedia.GraphTheory.FourColor.AlternatingCycleRecognition

open InducedCycleLayer FacialCycleLayer SimpleGraphDartRotation ZigzagRing
open GoertzelV24FaceOrbitIncidence GoertzelV24PrimalCycleFacialBond
open GoertzelV24TwoEdgeCutMinimality PhysicalForkCodeFaces
open GoertzelV24FaceDualConnectedness
open Fin.NatCast

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]
  {k : ℕ} [NeZero k] (C : Frame G k) (hk : 2 ≤ k)
  (hG : G.IsRegularOfDegree 3) (data : Data G)

local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- Local turns, inspected on the original graph's three-dart stars. -/
structure AlternatingTurns : Prop where
  incoming : ∀ i, (RS data).rho (C.star hk hG (.inl i) 1) = C.star hk hG (.inl i) 2
  outgoing : ∀ i,
    (RS data).rho (C.star hk hG (.inr i) 1) = C.star hk hG (.inr i) 0 ∧
    (RS data).rho (C.star hk hG (.inr i) 0) = C.star hk hG (.inr i) 2

variable {C hk hG data} (turns : AlternatingTurns C hk hG data)

private theorem all_of_next (P : Vtx k → Prop)
    (step : ∀ v, P (next k v) ↔ P v) (v : Vtx k) : P v ↔ P (.inl 0) := by
  have hi (n : ℕ) : P (.inl (n : Fin k)) ↔ P (.inl 0) := by
    induction n with
    | zero => simp
    | succ n ih =>
      exact (by simpa only [next, Nat.cast_add, Nat.cast_one] using
        (step (.inr (n : Fin k))).trans ((step (.inl (n : Fin k))).trans ih))
  cases v with
  | inl i => simpa only [Fin.cast_val_eq_self] using hi i.val
  | inr i => exact (step (.inl i)).trans (by simpa only [Fin.cast_val_eq_self] using hi i.val)

variable {root : V} (walk : G.Walk root root)
  (exactEdges : ∀ d : G.Dart, d.edge ∈ walk.edges ↔
    ∃ v, d = C.star hk hG v 1 ∨ d = C.star hk hG v 2)
  (R : Finset (OrbitFace (RS data)))
  (separator : ∀ d : G.Dart, d.edge ∈ walk.edges ↔
    ((dartOrbitFace (RS data) d ∈ R ∧ dartOrbitFace (RS data) d.symm ∉ R) ∨
      (dartOrbitFace (RS data) d ∉ R ∧ dartOrbitFace (RS data) d.symm ∈ R)))

include exactEdges separator

private theorem port_same_side (v : Vtx k) :
    dartOrbitFace (RS data) (C.star hk hG v 0) ∈ R ↔
      dartOrbitFace (RS data) (C.star hk hG v 0).symm ∈ R := by
  have hn : (C.star hk hG v 0).edge ∉ walk.edges := by
    intro he
    obtain ⟨w, h | h⟩ := (exactEdges _).mp he
    · have hh := congrArg Prod.snd (C.star_injective hk hG (a₁ := (v, 0)) (a₂ := (w, 1)) h)
      exact (by decide : (0 : Fin 3) ≠ 1) hh
    · have hh := congrArg Prod.snd (C.star_injective hk hG (a₁ := (v, 0)) (a₂ := (w, 2)) h)
      exact (by decide : (0 : Fin 3) ≠ 2) hh
  rw [separator] at hn
  tauto

include turns

private theorem backward_next (v : Vtx k) :
    dartOrbitFace (RS data) (C.star hk hG (next k v) 2) ∈ R ↔
      dartOrbitFace (RS data) (C.star hk hG v 2) ∈ R := by
  rw [← star_forward_symm]
  change dartOrbitFace (RS data) ((RS data).alpha (C.star hk hG v 1)) ∈ R ↔ _
  rw [dartOrbitFace_alpha_eq_dartOrbitFace_rho]
  cases v with
  | inl i => rw [turns.incoming]
  | inr i =>
    rw [(turns.outgoing i).1]
    have hs := port_same_side walk exactEdges R separator (.inr i)
    change _ ↔ dartOrbitFace (RS data) ((RS data).alpha (C.star hk hG (.inr i) 0)) ∈ R at hs
    rw [dartOrbitFace_alpha_eq_dartOrbitFace_rho, (turns.outgoing i).2] at hs
    exact hs

private theorem bounds_of_separator
    (base : dartOrbitFace (RS data) (C.star hk hG (.inl 0) 2) ∉ R) :
    BoundsFaces C hk hG data R := by
  have hb (v : Vtx k) : dartOrbitFace (RS data) (C.star hk hG v 2) ∉ R := by
    intro hv
    exact base ((all_of_next (fun w => dartOrbitFace (RS data) (C.star hk hG w 2) ∈ R)
      (backward_next turns walk exactEdges R separator) v).mp hv)
  refine ⟨?_, hb⟩
  intro v
  have he := (separator (C.star hk hG v 1)).mp
    ((exactEdges _).mpr ⟨v, Or.inl rfl⟩)
  rw [star_forward_symm] at he
  exact (he.resolve_right (fun h => hb _ h.2)).1

omit turns exactEdges separator [G.LocallyFinite] in
private theorem complement_separator
    (sep : ∀ d : G.Dart, d.edge ∈ walk.edges ↔
      ((dartOrbitFace (RS data) d ∈ R ∧ dartOrbitFace (RS data) d.symm ∉ R) ∨
        (dartOrbitFace (RS data) d ∉ R ∧ dartOrbitFace (RS data) d.symm ∈ R))) :
    ∀ d : G.Dart, d.edge ∈ walk.edges ↔
      ((dartOrbitFace (RS data) d ∈ Finset.univ \ R ∧
          dartOrbitFace (RS data) d.symm ∉ Finset.univ \ R) ∨
        (dartOrbitFace (RS data) d ∉ Finset.univ \ R ∧
          dartOrbitFace (RS data) d.symm ∈ Finset.univ \ R)) := by
  intro d
  rw [sep]
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
  tauto

variable (ambient : BridgelessSphericalCubicMapData (RS data))

include ambient in
omit walk exactEdges R separator in
/-- A simple alternating cycle determines both connected facial shores.
The side is chosen from the actual orientation of its darts. -/
theorem exists_facial_sides :
    ∃ R : Finset (OrbitFace (RS data)), BoundsFaces C hk hG data R ∧
      ((orbitFaceDualGraph data).induce (R : Set _)).Connected ∧
      ((orbitFaceDualGraph data).induce (R : Set _)ᶜ).Connected := by
  obtain ⟨root, walk, hcycle, he⟩ := C.exists_cycle hk hG
  have htwo := GoertzelV24BridgelessFaceTwoSided.BridgelessSphericalCubicMapData.orbitFacesTwoSided
    (RS data) ambient
  obtain ⟨F, hf, _, _⟩ := exists_faceSet_bond_of_isCycle data ambient htwo walk hcycle
  change ∀ d : G.Dart, d.edge ∈ walk.edges ↔ _ at hf
  by_cases hb : dartOrbitFace (RS data) (C.star hk hG (.inl 0) 2) ∈ F
  · let R := Finset.univ \ F
    have hr := complement_separator walk F hf
    have hbase : dartOrbitFace (RS data) (C.star hk hG (.inl 0) 2) ∉ R := by
      simp only [R, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
      exact hb
    refine ⟨R, bounds_of_separator turns walk he R hr hbase, ?_⟩
    exact face_sides_connected_of_isCycle data ambient htwo walk hcycle R hr
  · exact ⟨F, bounds_of_separator turns walk he F hf hb,
      face_sides_connected_of_isCycle data ambient htwo walk hcycle F hf⟩

omit walk exactEdges separator ambient in
/-- The local turn pattern forces the retained degree pattern; it is not
an extra hypothesis on the constructed face region. -/
theorem alternating_degrees (hC : Cubic3 (RS data)) (h : BoundsFaces C hk hG data R) :
    AlternatingDegrees C data R := by
  constructor
  · intro i
    rcases h.rotation_at hC (.inl i) with hgood | hbad
    · exact hgood.1
    · have he := (turns.incoming i).symm.trans hbad.2.2.1
      have hh := congrArg Prod.snd (C.star_injective hk hG (a₁ := (.inl i, 2)) (a₂ := (.inl i, 0)) he)
      exact (by decide : (2 : Fin 3) ≠ 0) hh |>.elim
  · intro i
    rcases h.rotation_at hC (.inr i) with hbad | hgood
    · have he := (turns.outgoing i).1.symm.trans hbad.2.2.1
      have hh := congrArg Prod.snd (C.star_injective hk hG (a₁ := (.inr i, 0)) (a₂ := (.inr i, 2)) he)
      exact (by decide : (0 : Fin 3) ≠ 2) hh |>.elim
    · exact hgood.1


omit walk exactEdges R separator in
/-- The selected shore is constructed by spherical separation. -/
def facialSide : Finset (OrbitFace (RS data)) :=
  Classical.choose (exists_facial_sides turns ambient)

omit walk exactEdges R separator in
theorem facialSide_spec :
    BoundsFaces C hk hG data (facialSide turns ambient) ∧
      ((orbitFaceDualGraph data).induce (facialSide turns ambient : Set _)).Connected ∧
      ((orbitFaceDualGraph data).induce (facialSide turns ambient : Set _)ᶜ).Connected :=
  Classical.choose_spec (exists_facial_sides turns ambient)

omit walk exactEdges R separator in
/-- The simple alternating cycle supplies an actual slab. Chordlessness,
the interior region and both complete ordered interfaces are derived. -/
def row
    (short : ∀ v, ((RS data).faceOrbit (C.star hk hG v 0)).card = 5 ∨
      ((RS data).faceOrbit (C.star hk hG v 0)).card = 6) :
    TubeSlab.ZigzagSlab (RS data) k (Interior data (facialSide turns ambient)) :=
  let h := facialSide_spec turns ambient
  FacialCycleChord.toSlab h.1
    (alternating_degrees turns _ (cubic3_of _ ambient.spherical.cubic ambient.vertexRotationCyclic) h.1)
    short ambient h.2.1 h.2.2

variable (short : ∀ v, ((RS data).faceOrbit (C.star hk hG v 0)).card = 5 ∨
  ((RS data).faceOrbit (C.star hk hG v 0)).card = 6)

omit walk exactEdges R separator in
theorem row_vertices (v : Vtx k) : (row turns ambient short).vtx v = C.vertex v := rfl

omit walk exactEdges R separator in
theorem row_darts (d : AllDart k) : (row turns ambient short).ι d = C.embedding hk hG d := rfl

omit walk exactEdges R separator in
theorem row_rotation : (row turns ambient short).RotationCompatible :=
  let h := facialSide_spec turns ambient
  h.1.embedding_rho (cubic3_of _ ambient.spherical.cubic ambient.vertexRotationCyclic)
    (alternating_degrees turns _ (cubic3_of _ ambient.spherical.cubic ambient.vertexRotationCyclic) h.1)

omit walk exactEdges R separator in
/-- Exact joint boundary semantics, including genuine colourings on the
constructed interior and the original row. -/
theorem row_support (y : Fin k → Color) :
    let S := row turns ambient short
    (fun b => y (S.outEquiv.symm b)) ∈ TubeSlab.sideSupport (RS data) S.inner' ↔
      ∃ x : Fin k → Color,
        (fun b => x (S.inEquiv.symm b)) ∈
          TubeSlab.sideSupport (RS data) (Interior data (facialSide turns ambient)) ∧
        Step k x y :=
  (row turns ambient short).mem_sideSupport_inner'_iff y

omit walk exactEdges R separator short in
/-- Recognition feeds geometric growth: no independently supplied shore
or complete boundary maps occur in the hypotheses. -/
theorem recognized_pentagonWithin
    (faces : ∀ d : (RS data).D,
      ((RS data).faceOrbit d).card = 5 ∨ ((RS data).faceOrbit d).card = 6) :
    TubeSlab.ZigzagSlab.PentagonWithin
      (cubic3_of _ ambient.spherical.cubic ambient.vertexRotationCyclic) faces
      (row turns ambient (fun v => faces (C.star hk hG v 0)))
      (row_rotation turns ambient (fun v => faces (C.star hk hG v 0))) (Fintype.card V) :=
  (row turns ambient (fun v => faces (C.star hk hG v 0))).pentagonWithin_card _ faces
    (row_rotation turns ambient (fun v => faces (C.star hk hG v 0)))

omit walk exactEdges R separator short in
/-- The five-port physical reduction consumes the new recognition theorem.
Only the simple alternating cycle is supplied, not a completed slab. -/
theorem recognized_pentagonWithin_three (width : k = 5)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (faces : ∀ d : (RS data).D,
      ((RS data).faceOrbit d).card = 5 ∨ ((RS data).faceOrbit d).card = 6) :
    TubeSlab.ZigzagSlab.PentagonWithin
      (cubic3_of _ ambient.spherical.cubic ambient.vertexRotationCyclic) faces
      (row turns ambient (fun v => faces (C.star hk hG v 0)))
      (row_rotation turns ambient (fun v => faces (C.star hk hG v 0))) 3 := by
  subst k
  exact (row turns ambient (fun v => faces (C.star hk hG v 0))).pentagonWithin_three
    data minimal faces (row_rotation turns ambient (fun v => faces (C.star hk hG v 0)))

end
end Mettapedia.GraphTheory.FourColor.AlternatingCycleRecognition
