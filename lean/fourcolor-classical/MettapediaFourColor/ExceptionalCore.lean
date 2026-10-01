import MettapediaFourColor.ExceptionalOverlap

/-!
# Exact D1774 core readings forced by the exceptional overlap

D1774.conf is from near-linear-4ct/reducible-configurations at revision
c2ce7a96e35256201526e2abb51a39d04a588b53, copyright 2026 Yuta Inoue (MIT).
The original file and licence are retained in tools/fourcolor/near-linear.

The conclusion retains all core edges and prescribed degrees in an actual
ambient graph. A core homomorphism alone is not a reducibility certificate:
injectivity, cyclic ring completion and compatible repair remain obligations.
-/

namespace FourColor.ExceptionalCore

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ExceptionalPattern ExceptionalOverlap LocalCoverageAssembly NearLinearDiamondData

set_option maxRecDepth 32768

def input : Input 19 11 where
  source := "19 11\n12 8 10 11 19 17 15 18 16 9\n13 5 7 8 16 18 6\n14 5 3 4 15 17 2\n15 7 5 6 18 12 17 14 4\n16 5 9 12 18 13 8\n17 5 14 15 12 19 2\n18 5 13 16 12 15 6\n19 5 2 17 12 11 1\n"
  valid := by decide +kernel

def core : SimpleGraph (Fin 8) := input.graph.comap (fun i => i.natAdd 11)
instance : DecidableRel core.Adj := by unfold core; infer_instance

def coreDegree (i : Fin 8) : ℕ := (coreRow input.source i.val).getD 1 0
def oldLabel : Fin 7 → Fin 17 := ![14, 3, 16, 5, 13, 15, 4]

theorem old_edges : ∀ i j : Fin 7,
    core.Adj i.castSucc j.castSucc ↔ ExceptionalPattern.graph.Adj (oldLabel i) (oldLabel j) := by
  decide +kernel

theorem new_edges : ∀ i : Fin 7, core.Adj i.castSucc 7 ↔ i = 0 ∨ i = 5 := by
  decide +kernel

theorem old_degrees : ∀ i : Fin 7, coreDegree i.castSucc = prescribed (oldLabel i) := by
  decide +kernel

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {rotation : Data G}
  (x : Occurrence rotation)

def coreVertex (i : Fin 8) : V :=
  if h : i.val < 7 then x.vertex (oldLabel ⟨i.val, h⟩) else (closingDart x).snd

theorem vertex_old (i : Fin 7) : coreVertex x i.castSucc = x.vertex (oldLabel i) := by
  simp [coreVertex, i.isLt]

theorem vertex_new : coreVertex x 7 = (closingDart x).snd := rfl

/-- All thirteen core edges are transported; neither a sketch nor just the
new edge is substituted for the source graph. -/
def coreHom (tri : Triangular rotation) : core →g G where
  toFun := coreVertex x
  map_rel' := by
    intro a b h
    have cases (i : Fin 8) : i = 7 ∨ ∃ j : Fin 7, i = j.castSucc := by
      by_cases hi : i.val < 7
      · exact Or.inr ⟨⟨i.val, hi⟩, by apply Fin.ext; rfl⟩
      · left; apply Fin.ext; change i.val = 7; omega
    rcases cases a with rfl | ⟨i, rfl⟩ <;> rcases cases b with rfl | ⟨j, rfl⟩
    · exact (core.irrefl h).elim
    · rw [vertex_new, vertex_old]
      rcases (new_edges j).mp h.symm with rfl | rfl
      · exact (closing_edges x tri).1.symm
      · exact (closing_edges x tri).2.symm
    · rw [vertex_old, vertex_new]
      rcases (new_edges i).mp h with rfl | rfl
      · exact (closing_edges x tri).1
      · exact (closing_edges x tri).2
    · rw [vertex_old, vertex_old]
      exact x.edge _ _ ((old_edges i j).mp h)

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem core_degrees (cyclic : rotation.IsVertexwiseCyclic)
    (y : Occurrence rotation) (aligned : y.vertex 0 = x.vertex 14) :
    ∀ i, G.degree (coreVertex x i) = coreDegree i := by
  intro i
  by_cases hi : i.val < 7
  · let j : Fin 7 := ⟨i.val, hi⟩
    have he : i = j.castSucc := by apply Fin.ext; rfl
    rw [he, vertex_old, x.degree, ← old_degrees]
  · have he : i = 7 := by apply Fin.ext; change i.val = 7; omega
    rw [he, vertex_new]
    exact closing_degree x cyclic y aligned

/-- The new corner lies one step beyond the prescribed second centre. -/
theorem core_near (i : Fin 8) : coreVertex x i ∈ closedBall G (x.vertex 0) 3 := by
  by_cases hi : i.val < 7
  · simp only [coreVertex, dite_eq_left hi]
    exact ball_mono G (by decide : 2 ≤ 3) (x.vertex_near _)
  · simp only [coreVertex, dite_eq_right hi]
    have h1 : (closingDart x).snd ∈ closedBall G (x.vertex 14) 1 := by
      let p : G.Walk (x.vertex 14) (closingDart x).snd :=
        .cons (by simpa [closing_fst] using (closingDart x).adj) .nil
      simpa [closedBall, p] using p.edist_le
    exact ball_recenter G x.next_centre.1 h1

/-- The deliberately limited geometric output: a degree-preserving core
homomorphism. Additional occurrence and repair obligations are not fields
asserted without proof. -/
structure Reading (G : SimpleGraph V) [G.LocallyFinite] where
  map : core →g G
  degree : ∀ i, G.degree (map i) = coreDegree i

def reading (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (y : Occurrence rotation) (aligned : y.vertex 0 = x.vertex 14) : Reading G :=
  ⟨coreHom x tri, core_degrees x cyclic y aligned⟩

/-- Retain both source occurrences and their alignment for subsequent
boundary reconstruction. The observed core is tied to the first occurrence;
its edge and degree proofs use the shared second occurrence. -/
structure JointReading (rotation : Data G) where
  first : Occurrence rotation
  second : Occurrence rotation
  aligned : second.vertex 0 = first.vertex 14
  core : Reading G
  realizes : ∀ i, core.map i = coreVertex first i

def jointReading (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (y : Occurrence rotation) (aligned : y.vertex 0 = x.vertex 14) :
    JointReading rotation :=
  ⟨x, y, aligned, reading x tri cyclic y aligned, fun _ => rfl⟩

/-- Include the retained source observations, not only the derived core. -/
def support (r : JointReading rotation) : Set V :=
  Set.range r.first.vertex ∪ Set.range r.second.vertex ∪ Set.range r.core.map

theorem joint_support_near (tri : Triangular rotation)
    (cyclic : rotation.IsVertexwiseCyclic) (y : Occurrence rotation)
    (aligned : y.vertex 0 = x.vertex 14) :
    support (jointReading x tri cyclic y aligned) ⊆ closedBall G (x.vertex 0) 4 := by
  change (Set.range x.vertex ∪ Set.range y.vertex ∪ Set.range (coreVertex x)) ⊆ _
  rintro v ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩)
  · exact ball_mono G (by decide : 2 ≤ 4) (x.vertex_near i)
  · have h := y.vertex_near i
    rw [aligned] at h
    exact ball_recenter G x.next_centre.1 h
  · exact ball_mono G (by decide : 3 ≤ 4) (core_near x i)

/-- The source-encoded next-centre and joint core-reading branches fill the
scaffold. Classification and promotion of a core reading to a reducible
occurrence remain explicit; this theorem does not claim that promotion. -/
theorem overlap_supply (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (zero : V → Prop)
    (classify : ∀ c, G.degree c = 8 → OnBall G c 1 zero →
      OnBall G c 3 (fun v => G.degree v ≤ 8) →
      Occurs G (support (rotation := rotation)) (fun _ => True) c 3 ∨
        Nonempty (Centered rotation c)) :
    EightOverlapSupply G (support (rotation := rotation)) (fun _ => True) zero
      (Centered rotation) (Mate (rotation := rotation)) where
  classify := classify
  next := next_centered
  close := by
    intro c first u placed second
    have aligned : second.val.vertex 0 = first.val.vertex 14 := second.property.trans placed
    refine ⟨jointReading first.val tri cyclic second.val aligned, trivial, ?_⟩
    have h := joint_support_near first.val tri cyclic second.val aligned
    rw [first.property] at h
    exact h.trans (ball_mono G (by decide : 4 ≤ 5))

end FourColor.ExceptionalCore
