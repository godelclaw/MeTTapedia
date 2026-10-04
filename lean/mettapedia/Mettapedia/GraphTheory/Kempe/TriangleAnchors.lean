import Mettapedia.GraphTheory.Kempe.CycleAnchors

/-!
# Cycle-breaking colours from a triangle-elimination order

An injective vertex rank whose later neighbours form a clique, together with
a proper three-colouring, supplies a cycle-breaking set: delete any one of
the three structural colour classes. The remaining graph is a forest.

The structural colouring is independent of the physical colouring being
repaired. Retaining the physical colours on that set makes the existing
forest guard exact for whole Kempe histories, in arbitrary surrounding graphs.
This does not assert feasibility of an anchor assignment or a guarded move.
-/

namespace SimpleGraph.KempeTriangleAnchors

open Relation

universe u w

variable {V : Type u} {G : SimpleGraph V}

/-- An injective order with at most one later neighbour cannot contain a cycle. -/
theorem acyclic_of_unique_later (rank : V → ℕ) (inject : Function.Injective rank)
    (later : ∀ v x y, G.Adj v x → G.Adj v y →
      rank v < rank x → rank v < rank y → x = y) : G.IsAcyclic := by
  classical
  intro v p hp
  obtain ⟨m, hm, least⟩ := p.support.toFinset.exists_min_image rank
    ⟨v, List.mem_toFinset.mpr p.start_mem_support⟩
  have hm' : m ∈ p.support := List.mem_toFinset.mp hm
  let q := p.rotate m hm'
  have hq : q.IsCycle := hp.rotate hm'
  have minimum (x : V) (hx : x ∈ q.support) : rank m ≤ rank x :=
    least x (List.mem_toFinset.mpr ((p.mem_support_rotate_iff m hm').mp hx))
  have hs := q.adj_snd hq.not_nil
  have ht := (q.adj_penultimate hq.not_nil).symm
  have ls : rank m < rank q.snd := lt_of_le_of_ne
    (minimum _ (q.getVert_mem_support 1)) (fun h => hs.ne (inject h))
  have lt : rank m < rank q.penultimate := lt_of_le_of_ne
    (minimum _ (q.getVert_mem_support (q.length - 1))) (fun h => ht.ne (inject h))
  exact hq.snd_ne_penultimate (later m q.snd q.penultimate hs ht ls lt)

/-- Every bichromatic subgraph of a three-coloured graph with a supplied
perfect elimination order is a forest. The rank need not be consecutive. -/
theorem delete_class_acyclic (rank : V → ℕ) (inject : Function.Injective rank)
    (laterClique : ∀ v x y, G.Adj v x → G.Adj v y →
      rank v < rank x → rank v < rank y → x ≠ y → G.Adj x y)
    (colour : G.Coloring (Fin 3)) (a : Fin 3) :
    (G.induce {v | colour v ≠ a}).IsAcyclic := by
  apply acyclic_of_unique_later (fun x => rank x.val)
    (fun _ _ h => Subtype.ext (inject h))
  intro v x y hx hy rx ry
  by_contra different
  have edge := laterClique v x y hx hy rx ry (fun h => different (Subtype.ext h))
  have vx := colour.valid hx
  have vy := colour.valid hy
  have xy := colour.valid edge
  have va := v.property
  have xa := x.property
  have ya := y.property
  have finite : ∀ b c d a : Fin 3,
      b ≠ c → b ≠ d → c ≠ d → b ≠ a → c ≠ a → d ≠ a → False := by
    intro b c d a
    omega
  exact finite _ _ _ a vx vy xy va xa ya

/-- Local rank and colour data need hold only on the hidden patch. No
constraint on degrees, cycles or colours of the exterior is imposed. -/
theorem hidden_forest (S : Set V) (rank : V → ℕ) (colour : V → Fin 3)
    (inject : S.InjOn rank)
    (proper : ∀ x ∈ S, ∀ y ∈ S, G.Adj x y → colour x ≠ colour y)
    (laterClique : ∀ v ∈ S, ∀ x ∈ S, ∀ y ∈ S,
      G.Adj v x → G.Adj v y → rank v < rank x → rank v < rank y →
      x ≠ y → G.Adj x y) (a : Fin 3) :
    (G.induce (S \ {v | colour v = a})).IsAcyclic := by
  let c : (G.induce S).Coloring (Fin 3) :=
    .mk (fun x => colour x) (fun {x y} h => proper x x.property y y.property h)
  have forest := delete_class_acyclic (G := G.induce S) (fun x => rank x.val)
    (fun x y h => Subtype.ext (inject x.property y.property h))
    (fun v x y hvx hvy rx ry ne => laterClique v v.property x x.property y y.property
      hvx hvy rx ry (fun h => ne (Subtype.ext h))) c a
  let f : G.induce (S \ {v | colour v = a}) →g
      (G.induce S).induce {v | c v ≠ a} :=
    ⟨fun x => ⟨⟨x.val, x.property.1⟩, x.property.2⟩, fun h => h⟩
  exact forest.comap f (fun _ _ h => Subtype.ext (congrArg (fun x => x.val.val) h))

/-- The structural data give an exact physical repair interface, uniformly
over physical palettes and all actual full-colouring endpoints. -/
theorem history_iff {α : Type w} [Fintype V] [DecidableEq α]
    (S : Set V) (rank : V → ℕ) (colour : V → Fin 3)
    (inject : S.InjOn rank)
    (proper : ∀ x ∈ S, ∀ y ∈ S, G.Adj x y → colour x ≠ colour y)
    (laterClique : ∀ v ∈ S, ∀ x ∈ S, ∀ y ∈ S,
      G.Adj v x → G.Adj v y → rank v < rank x → rank v < rank y →
      x ≠ y → G.Adj x y) (a : Fin 3) (C D : G.Coloring α) :
    ReflTransGen (KempeGuardedLift.Step (S \ {v | colour v = a}) Sᶜ)
      (C.restrictInduce (S \ {v | colour v = a})ᶜ)
      (D.restrictInduce (S \ {v | colour v = a})ᶜ) ↔
      ReflTransGen (G.KempeStepAvoiding Sᶜ) C D :=
  KempeCycleAnchors.history_iff S {v | colour v = a}
    (hidden_forest S rank colour inject proper laterClique a) C D

/-- The anchor set of an exact induced occurrence. Exterior vertices are not
anchors, and extra edges within the occurrence cannot be silently discarded. -/
def anchors {W : Type*} {H : SimpleGraph W} (S : Set V)
    (read : G.induce S ≃g H) (colour : W → Fin 3) (a : Fin 3) : Set V :=
  {v | ∃ h : v ∈ S, colour (read ⟨v, h⟩) = a}

theorem occurrence_forest {W : Type*} {H : SimpleGraph W} (S : Set V)
    (read : G.induce S ≃g H) (rank : W → ℕ) (inject : Function.Injective rank)
    (laterClique : ∀ v x y, H.Adj v x → H.Adj v y →
      rank v < rank x → rank v < rank y → x ≠ y → H.Adj x y)
    (colour : H.Coloring (Fin 3)) (a : Fin 3) :
    (G.induce (S \ anchors S read colour a)).IsAcyclic := by
  let f : G.induce (S \ anchors S read colour a) →g
      H.induce {w | colour w ≠ a} :=
    ⟨fun x => ⟨read ⟨x.val, x.property.1⟩,
      fun h => x.property.2 ⟨x.property.1, h⟩⟩,
     fun {x y} h => read.map_rel_iff.mpr h⟩
  apply (delete_class_acyclic rank inject laterClique colour a).comap f
  intro x y h
  exact Subtype.ext (congrArg (fun z : S => z.val)
    (read.injective (congrArg Subtype.val h)))

/-- One structural certificate supplies an exact guarded repair contract
in every ambient graph containing the patch as an induced subgraph. -/
theorem occurrence_history_iff {W : Type*} {H : SimpleGraph W}
    {α : Type w} [Fintype V] [DecidableEq α] (S : Set V)
    (read : G.induce S ≃g H) (rank : W → ℕ) (inject : Function.Injective rank)
    (laterClique : ∀ v x y, H.Adj v x → H.Adj v y →
      rank v < rank x → rank v < rank y → x ≠ y → H.Adj x y)
    (colour : H.Coloring (Fin 3)) (a : Fin 3) (C D : G.Coloring α) :
    ReflTransGen (KempeGuardedLift.Step (S \ anchors S read colour a) Sᶜ)
      (C.restrictInduce (S \ anchors S read colour a)ᶜ)
      (D.restrictInduce (S \ anchors S read colour a)ᶜ) ↔
      ReflTransGen (G.KempeStepAvoiding Sᶜ) C D :=
  KempeCycleAnchors.history_iff S (anchors S read colour a)
    (occurrence_forest S read rank inject laterClique colour a) C D

end SimpleGraph.KempeTriangleAnchors
