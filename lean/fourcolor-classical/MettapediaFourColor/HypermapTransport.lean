import FourColor.Combinatorial
import Mathlib.Data.Fintype.EquivFin

/-!
# Exact relabelling of classical hypermaps

Conjugating all three permutations preserves components, face cycles,
planarity and colourings. In particular the finite classical theorem can be
used on dart types in any universe, by relabelling through a finite ordinal.
-/

namespace FourColor.Hypermap

open Equiv Equiv.Perm

variable {D D' : Type*}

/-- Change the dart carrier without forgetting any of the three permutations. -/
def relabel (G : Hypermap D) (e : D ≃ D') : Hypermap D' where
  edge := e.permCongr G.edge
  node := e.permCongr G.node
  face := e.permCongr G.face
  node_face_edge := by
    change e.permCongrHom G.node * e.permCongrHom G.face * e.permCongrHom G.edge = 1
    rw [← map_mul e.permCongrHom, ← map_mul e.permCongrHom,
      G.node_face_edge, map_one]

@[simp] theorem relabel_edge (G : Hypermap D) (e : D ≃ D') (x : D) :
    (G.relabel e).edge (e x) = e (G.edge x) := by simp [relabel]

@[simp] theorem relabel_node (G : Hypermap D) (e : D ≃ D') (x : D) :
    (G.relabel e).node (e x) = e (G.node x) := by simp [relabel]

@[simp] theorem relabel_face (G : Hypermap D) (e : D ≃ D') (x : D) :
    (G.relabel e).face (e x) = e (G.face x) := by simp [relabel]

theorem sameCycle_relabel (e : D ≃ D') (f : Perm D) (x y : D) :
    (e.permCongr f).SameCycle (e x) (e y) ↔ f.SameCycle x y := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, e.injective ?_⟩
    change (e.permCongrHom f ^ n) (e x) = e y at hn
    rw [← map_zpow e.permCongrHom] at hn
    simpa using hn
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    change (e.permCongrHom f ^ n) (e x) = e y
    rw [← map_zpow e.permCongrHom]
    simpa using congrArg e hn

theorem glink_relabel (G : Hypermap D) (e : D ≃ D') (x y : D) :
    (G.relabel e).GLink (e x) (e y) ↔ G.GLink x y := by
  simp [GLink]

theorem component_relabel (G : Hypermap D) (e : D ≃ D') (x y : D) :
    Relation.EqvGen (G.relabel e).GLink (e x) (e y) ↔
      Relation.EqvGen G.GLink x y := by
  have forward : ∀ a b, Relation.EqvGen G.GLink a b →
      Relation.EqvGen (G.relabel e).GLink (e a) (e b) := by
    intro a b h
    induction h with
    | rel a b h => exact .rel _ _ ((glink_relabel G e a b).mpr h)
    | refl a => exact .refl _
    | symm a b _ ih => exact .symm _ _ ih
    | trans a b c _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂
  refine ⟨?_, forward x y⟩
  intro h
  have back : ∀ a b, Relation.EqvGen (G.relabel e).GLink a b →
      Relation.EqvGen G.GLink (e.symm a) (e.symm b) := by
    intro a b hab
    induction hab with
    | rel a b hab =>
      exact .rel _ _ ((glink_relabel G e _ _).mp (by simpa using hab))
    | refl a => exact .refl _
    | symm a b _ ih => exact .symm _ _ ih
    | trans a b c _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂
  simpa using back _ _ h

theorem compCount_relabel (G : Hypermap D) (e : D ≃ D') :
    (G.relabel e).compCount = G.compCount :=
  (compCount_congr e (fun x y => (component_relabel G e x y).symm)).symm

theorem cycleCount_relabel (e : D ≃ D') (f : Perm D) :
    cycleCount (e.permCongr f) = cycleCount f :=
  (cycleCount_congr e (fun x y => (sameCycle_relabel e f x y).symm)).symm

theorem planar_relabel (G : Hypermap D) (e : D ≃ D') :
    (G.relabel e).Planar ↔ G.Planar := by
  simp only [Planar, genus, EulerLhs, EulerRhs, compCount_relabel,
    show Nat.card D' = Nat.card D from (Nat.card_congr e).symm]
  change (2 * G.compCount + Nat.card D -
    (cycleCount (e.permCongr G.edge) +
      (cycleCount (e.permCongr G.node) + cycleCount (e.permCongr G.face)))) / 2 = 0 ↔ _
  simp only [cycleCount_relabel]

theorem bridgeless_relabel (G : Hypermap D) (e : D ≃ D') :
    (G.relabel e).Bridgeless ↔ G.Bridgeless := by
  constructor
  · intro h x
    have hx := h (e x)
    rw [relabel_edge] at hx
    exact fun hs => hx ((sameCycle_relabel e G.face x (G.edge x)).mpr hs)
  · intro h y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [relabel_edge]
    exact fun hs => h x ((sameCycle_relabel e G.face x (G.edge x)).mp hs)

/-- Pull back the actual face assignment, rather than only its existence. -/
theorem coloring_relabel (G : Hypermap D) (e : D ≃ D') (k : D' → Color) :
    (G.relabel e).Coloring k ↔ G.Coloring (k ∘ e) := by
  constructor
  · intro h
    exact ⟨fun x => by simpa using h.edge (e x),
      fun x => by simpa using h.face (e x)⟩
  · intro h
    refine ⟨?_, ?_⟩
    · intro x
      obtain ⟨y, rfl⟩ := e.surjective x
      simpa using h.edge y
    · intro x
      obtain ⟨y, rfl⟩ := e.surjective x
      simpa using h.face y

/-- A universe-zero unavoidability proof colours all finite dart carriers. -/
theorem fourColorable_of_small_unavoidability
    (noCounterexample : ∀ {A : Type} [Finite A] (H : Hypermap A),
      ¬ H.MinimalCounterExample)
    [Finite D] (G : Hypermap D) (hG : G.PlanarBridgeless) : G.FourColorable := by
  classical
  let := Fintype.ofFinite D
  let e := Fintype.equivFin D
  have hsmall : (G.relabel e).PlanarBridgeless :=
    ⟨(planar_relabel G e).mpr hG.planar,
      (bridgeless_relabel G e).mpr hG.bridgeless⟩
  obtain ⟨k, hk⟩ := fourColorable_of_no_minimalCounterExample
    noCounterexample (G.relabel e) hsmall
  exact ⟨k ∘ e, (coloring_relabel G e k).mp hk⟩

#print axioms fourColorable_of_small_unavoidability

end FourColor.Hypermap
