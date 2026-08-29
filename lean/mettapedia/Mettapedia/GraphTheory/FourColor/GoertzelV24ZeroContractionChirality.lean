import Mettapedia.GraphTheory.FourColor.GoertzelV24InducedHexCorridorTypes
import Mettapedia.GraphTheory.FourColor.RotationSystemEdgeColoring

/-!
# The local chirality law for contraction of one Tait colour

Contract an oriented edge `dart` of a cubic rotation system.  The link of the
contracted vertex consists, in cyclic order, of the two remaining darts at the
first endpoint followed by the two remaining darts at the second endpoint.
A proper Tait colouring allows exactly two same-colour pairings on this
four-point link:

* equal endpoint order gives the alternating pairing `(0,2), (1,3)`;
* reversed endpoint order gives the adjacent pairing `(0,3), (1,2)`.

Thus contraction does not in general make the two surviving bichromatic
systems mutually disjoint.  It exposes a single local chirality bit which a
joint post-contraction state must retain.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24FaceDualConnectedness
open GoertzelV24InducedHexCorridorTypes

namespace GoertzelV24ZeroContractionChirality

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-! ## The four-point link -/

/-- The cyclic link of the vertex obtained by contracting the edge represented
by `dart`.  Positions `0,1` come from the endpoint of `dart`; positions `2,3`
come from the endpoint of `alpha dart`. -/
def linkDart (RS : RotationSystem V E) (dart : RS.D) : Fin 4 → RS.D
  | 0 => RS.rho dart
  | 1 => RS.rho (RS.rho dart)
  | 2 => RS.rho (RS.alpha dart)
  | 3 => RS.rho (RS.rho (RS.alpha dart))

/-- The Tait colour word around a contracted-edge link. -/
def linkColor (RS : RotationSystem V E) (C : RS.EdgeColoring Color)
    (dart : RS.D) (position : Fin 4) : Color :=
  C (RS.edgeOf (linkDart RS dart position))

/-- The two endpoint rotations agree when their first surviving darts have the
same colour.  Proper cubic Tait colouring then forces their second surviving
darts to have the same colour as well. -/
def EndpointOrdersAgree (RS : RotationSystem V E)
    (C : RS.EdgeColoring Color) (dart : RS.D) : Prop :=
  linkColor RS C dart 0 = linkColor RS C dart 2

/-- Endpoint-order agreement is a property of the contracted edge, independent
of which of its two darts is chosen as the orientation. -/
theorem endpointOrdersAgree_alpha_iff (RS : RotationSystem V E)
    (C : RS.EdgeColoring Color) (dart : RS.D) :
    EndpointOrdersAgree RS C (RS.alpha dart) ↔
      EndpointOrdersAgree RS C dart := by
  simp only [EndpointOrdersAgree, linkColor, linkDart, RS.alpha_involutive]
  exact eq_comm

/-- The alternating same-colour mate map on four cyclic positions. -/
def alternatingMate : Fin 4 → Fin 4
  | 0 => 2
  | 1 => 3
  | 2 => 0
  | 3 => 1

/-- The adjacent same-colour mate map on four cyclic positions. -/
def adjacentMate : Fin 4 → Fin 4
  | 0 => 3
  | 1 => 2
  | 2 => 1
  | 3 => 0

/-- The same-colour partner forced by the endpoint chirality. -/
noncomputable def sameColorMate (RS : RotationSystem V E)
    (C : RS.EdgeColoring Color) (dart : RS.D) : Fin 4 → Fin 4 :=
  by
    classical
    exact if EndpointOrdersAgree RS C dart then alternatingMate else adjacentMate

/-- Two chords in a four-point cyclic link cross when their endpoints
alternate in the displayed linearization of the cyclic order. -/
def ChordsCross4 (first second third fourth : Fin 4) : Prop :=
  let a := min first.1 second.1
  let b := max first.1 second.1
  let c := min third.1 fourth.1
  let d := max third.1 fourth.1
  (a < c ∧ c < b ∧ b < d) ∨ (c < a ∧ a < d ∧ d < b)

private instance chordsCross4Decidable
    (first second third fourth : Fin 4) :
    Decidable (ChordsCross4 first second third fourth) := by
  unfold ChordsCross4
  infer_instance

/-! ## Local Tait facts -/

private theorem rho_triple_pairwise_ne
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS) (dart : RS.D) :
    dart ≠ RS.rho dart ∧
      dart ≠ RS.rho (RS.rho dart) ∧
      RS.rho dart ≠ RS.rho (RS.rho dart) := by
  have hdart : dart ∈ RS.dartsAt (RS.vertOf dart) := by
    simp [RotationSystem.dartsAt]
  have hnontrivialFinset :
      (RS.dartsAt (RS.vertOf dart)).Nontrivial := by
    apply Finset.one_lt_card_iff_nontrivial.mp
    rw [hcubic (RS.vertOf dart)]
    omega
  have hnontrivial :
      (RS.dartsAt (RS.vertOf dart) : Set RS.D).Nontrivial := by
    simpa only [Finset.coe_sort_coe] using hnontrivialFinset
  have hstep : RS.rho dart ≠ dart :=
    (rho_isCycleOn_dartsAt RS hrotation (RS.vertOf dart)).apply_ne
      hnontrivial hdart
  have hnext : RS.rho (RS.rho dart) ≠ RS.rho dart := by
    exact fun heq => hstep (RS.rho.injective heq)
  have hfirstThird : dart ≠ RS.rho (RS.rho dart) := by
    intro heq
    have hcube := rho_cube_apply_of_isCubic RS hcubic hrotation dart
    have hrho := congrArg RS.rho heq
    rw [hcube] at hrho
    exact hstep hrho
  exact ⟨hstep.symm, hfirstThird, hnext.symm⟩

private theorem local_colors_pairwise_ne
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    (C : RS.EdgeColoring Color) (dart : RS.D) :
    C (RS.edgeOf dart) ≠ C (RS.edgeOf (RS.rho dart)) ∧
      C (RS.edgeOf dart) ≠ C (RS.edgeOf (RS.rho (RS.rho dart))) ∧
      C (RS.edgeOf (RS.rho dart)) ≠
        C (RS.edgeOf (RS.rho (RS.rho dart))) := by
  have hne := rho_triple_pairwise_ne RS hcubic hrotation dart
  have hdart : dart ∈ RS.dartsAt (RS.vertOf dart) := by
    simp [RotationSystem.dartsAt]
  have hrho : RS.rho dart ∈ RS.dartsAt (RS.vertOf dart) := by
    simp [RotationSystem.dartsAt, RS.vert_rho]
  have hrho2 : RS.rho (RS.rho dart) ∈ RS.dartsAt (RS.vertOf dart) := by
    simp [RotationSystem.dartsAt, RS.vert_rho]
  have hedge01 : RS.edgeOf dart ≠ RS.edgeOf (RS.rho dart) := by
    intro hedge
    exact hne.1 (RS.edgeOf_injOn_dartsAt (RS.vertOf dart)
      hdart hrho hedge)
  have hedge02 : RS.edgeOf dart ≠ RS.edgeOf (RS.rho (RS.rho dart)) := by
    intro hedge
    exact hne.2.1 (RS.edgeOf_injOn_dartsAt (RS.vertOf dart)
      hdart hrho2 hedge)
  have hedge12 :
      RS.edgeOf (RS.rho dart) ≠ RS.edgeOf (RS.rho (RS.rho dart)) := by
    intro hedge
    exact hne.2.2 (RS.edgeOf_injOn_dartsAt (RS.vertOf dart)
      hrho hrho2 hedge)
  have hdartIncident : RS.edgeOf dart ∈ RS.incidentEdges (RS.vertOf dart) :=
    (RS.mem_incidentEdges_iff).2 ⟨dart, rfl, rfl⟩
  have hrhoIncident :
      RS.edgeOf (RS.rho dart) ∈ RS.incidentEdges (RS.vertOf dart) :=
    (RS.mem_incidentEdges_iff).2
      ⟨RS.rho dart, rfl, RS.vert_rho dart⟩
  have hrho2Incident :
      RS.edgeOf (RS.rho (RS.rho dart)) ∈
        RS.incidentEdges (RS.vertOf dart) :=
    (RS.mem_incidentEdges_iff).2
      ⟨RS.rho (RS.rho dart), rfl,
        (RS.vert_rho (RS.rho dart)).trans (RS.vert_rho dart)⟩
  exact ⟨
    C.valid (RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      hedge01 hdartIncident hrhoIncident),
    C.valid (RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      hedge02 hdartIncident hrho2Incident),
    C.valid (RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
      hedge12 hrhoIncident hrho2Incident)⟩

private theorem third_color_eq_add
    {a b c : Color}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    c = a + b := by
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero a ha with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero b hb with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero c hc with rfl | rfl | rfl <;>
    simp_all [red, blue, purple]

private theorem remaining_color_pairing
    {a b c b' c' : Color}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hb' : b' ≠ 0) (hc' : c' ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hab' : a ≠ b') (hac' : a ≠ c') (hbc' : b' ≠ c') :
    (b = b' ∧ c = c') ∨ (b = c' ∧ c = b') := by
  have hcEq : c = a + b :=
    third_color_eq_add ha hb hc hab hac hbc
  have hc'Eq : c' = a + b' :=
    third_color_eq_add ha hb' hc' hab' hac' hbc'
  by_cases hbb' : b = b'
  · left
    exact ⟨hbb', hcEq.trans (hbb' ▸ hc'Eq.symm)⟩
  · right
    have hb'Eq : b' = a + b :=
      third_color_eq_add ha hb hb' hab hab' hbb'
    have hbEq : b = a + b' :=
      third_color_eq_add ha hb' hb hab' hab (fun h => hbb' h.symm)
    exact ⟨hbEq.trans hc'Eq.symm, hcEq.trans hb'Eq.symm⟩

/-! ## Chirality determines crossing -/

/-- At a contracted Tait-coloured cubic edge, the two endpoint colour orders
either agree exactly or are exactly reversed. -/
theorem linkColor_pairing_dichotomy
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (dart : RS.D) :
    (linkColor RS C dart 0 = linkColor RS C dart 2 ∧
        linkColor RS C dart 1 = linkColor RS C dart 3) ∨
      (linkColor RS C dart 0 = linkColor RS C dart 3 ∧
        linkColor RS C dart 1 = linkColor RS C dart 2) := by
  have hleft := local_colors_pairwise_ne RS hcubic hrotation C dart
  have hright := local_colors_pairwise_ne RS hcubic hrotation C (RS.alpha dart)
  have hcontractedColor :
      C (RS.edgeOf (RS.alpha dart)) = C (RS.edgeOf dart) := by
    rw [RS.edge_alpha]
  have hpair := remaining_color_pairing
    (hC (RS.edgeOf dart))
    (hC (RS.edgeOf (RS.rho dart)))
    (hC (RS.edgeOf (RS.rho (RS.rho dart))))
    (hC (RS.edgeOf (RS.rho (RS.alpha dart))))
    (hC (RS.edgeOf (RS.rho (RS.rho (RS.alpha dart)))))
    hleft.1 hleft.2.1 hleft.2.2
    (hcontractedColor ▸ hright.1)
    (hcontractedColor ▸ hright.2.1)
    hright.2.2
  simpa [linkColor, linkDart] using hpair

/-- Agreement is the alternating case: both opposite link positions have the
same colour. -/
theorem endpointOrdersAgree_iff_alternating
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (dart : RS.D) :
    EndpointOrdersAgree RS C dart ↔
      linkColor RS C dart 0 = linkColor RS C dart 2 ∧
        linkColor RS C dart 1 = linkColor RS C dart 3 := by
  constructor
  · intro hagree
    rcases linkColor_pairing_dichotomy RS hcubic hrotation C hC dart with
      halternating | hadjacent
    · exact halternating
    · exfalso
      have hleft := local_colors_pairwise_ne RS hcubic hrotation C dart
      exact hleft.2.2 (by
        calc
          C (RS.edgeOf (RS.rho dart)) = linkColor RS C dart 0 := by
            rfl
          _ = linkColor RS C dart 2 := hagree
          _ = linkColor RS C dart 1 := hadjacent.2.symm
          _ = C (RS.edgeOf (RS.rho (RS.rho dart))) := by
            rfl)
  · exact fun halternating => halternating.1

/-- Disagreement is the adjacent case: the same-colour pairs occupy adjacent
positions in the four-point link. -/
theorem not_endpointOrdersAgree_iff_adjacent
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (dart : RS.D) :
    ¬ EndpointOrdersAgree RS C dart ↔
      linkColor RS C dart 0 = linkColor RS C dart 3 ∧
        linkColor RS C dart 1 = linkColor RS C dart 2 := by
  constructor
  · intro hnot
    rcases linkColor_pairing_dichotomy RS hcubic hrotation C hC dart with
      halternating | hadjacent
    · exact False.elim (hnot halternating.1)
    · exact hadjacent
  · intro hadjacent hagree
    have hleft := local_colors_pairwise_ne RS hcubic hrotation C dart
    exact hleft.2.2 (by
      calc
        C (RS.edgeOf (RS.rho dart)) = linkColor RS C dart 0 := by
          rfl
        _ = linkColor RS C dart 2 := hagree
        _ = linkColor RS C dart 1 := hadjacent.2.symm
        _ = C (RS.edgeOf (RS.rho (RS.rho dart))) := by
          rfl)

/-- The mate chosen from the chirality has the same colour at every link
position. -/
theorem linkColor_sameColorMate
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (dart : RS.D) (position : Fin 4) :
    linkColor RS C dart (sameColorMate RS C dart position) =
      linkColor RS C dart position := by
  by_cases hagree : EndpointOrdersAgree RS C dart
  · have hpair :=
      (endpointOrdersAgree_iff_alternating RS hcubic hrotation C hC dart).1 hagree
    fin_cases position <;>
      simp [sameColorMate, hagree, alternatingMate, hpair.1, hpair.2]
  · have hpair :=
      (not_endpointOrdersAgree_iff_adjacent RS hcubic hrotation C hC dart).1 hagree
    fin_cases position <;>
      simp [sameColorMate, hagree, adjacentMate, hpair.1, hpair.2]

/-- The positional mate map crosses exactly in its alternating branch. -/
theorem chosen_chords_cross_iff_endpointOrdersAgree
    (RS : RotationSystem V E) (C : RS.EdgeColoring Color) (dart : RS.D) :
    ChordsCross4 0 (sameColorMate RS C dart 0)
        1 (sameColorMate RS C dart 1) ↔
      EndpointOrdersAgree RS C dart := by
  by_cases hagree : EndpointOrdersAgree RS C dart
  · simp [sameColorMate, hagree, alternatingMate, ChordsCross4]
  · simp [sameColorMate, hagree, adjacentMate, ChordsCross4]

/-- Consumer-facing local correction to the v23 zero-contraction argument.
The chirality-selected mates really carry the same Tait colours, and their
chords cross exactly when the endpoint colour orders agree. -/
theorem sameColor_pairing_and_crossing_iff_endpointOrdersAgree
    (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (hrotation : VertexRotationCyclic RS)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (dart : RS.D) :
    (∀ position : Fin 4,
        linkColor RS C dart (sameColorMate RS C dart position) =
          linkColor RS C dart position) ∧
      (ChordsCross4 0 (sameColorMate RS C dart 0)
          1 (sameColorMate RS C dart 1) ↔
        EndpointOrdersAgree RS C dart) := by
  exact ⟨linkColor_sameColorMate RS hcubic hrotation C hC dart,
    chosen_chords_cross_iff_endpointOrdersAgree RS C dart⟩

end GoertzelV24ZeroContractionChirality

end Mettapedia.GraphTheory.FourColor
