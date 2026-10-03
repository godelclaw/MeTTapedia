import Mettapedia.GraphTheory.Kempe.GuardedLift

/-!
# Fixed-exterior recolouring through a hidden forest

List-colourings of a finite forest are connected by proper partial colour
transpositions that respect every list. Leaf removal proves this for arbitrary
palettes and lists. Gluing the fixed exterior back turns those transpositions
into actual Kempe histories. No boundary degree bound or state enumeration is
used. Guarded history equivalence follows for every induced hidden forest.
-/

namespace SimpleGraph.KempeForestFibre

open Relation

universe u w

variable {V : Type u} {α : Type w} {G : SimpleGraph V} [DecidableEq α]

/-- A proper colouring respecting a separate allowed set at each vertex. -/
def State (G : SimpleGraph V) (L : V → Set α) :=
  {C : G.Coloring α // ∀ x, C x ∈ L x}

/-- One proper partial transposition, with both list-compatible endpoints. -/
def Move {L : V → Set α} (C D : State G L) : Prop :=
  ∃ a b, ∀ x, D.val x = C.val x ∨ D.val x = Equiv.swap a b (C.val x)

private theorem move_one {L : V → Set α} (v : V) (C D : State G L)
    (agree : ∀ x, x ≠ v → C.val x = D.val x) : Move C D := by
  refine ⟨C.val v, D.val v, fun x => ?_⟩
  by_cases hx : x = v
  · subst x; simp
  · exact Or.inl (agree x hx).symm

/-- One eliminated vertex can bridge a partial transposition whenever both
endpoints exist. Fixed forbidden colours enforce its original list. -/
private theorem lift_vertex_pair {L : V → Set α} (v : V) (C D : State G L)
    (a b : α) (pair : ∀ x, x ≠ v →
      D.val x = C.val x ∨ D.val x = Equiv.swap a b (C.val x)) :
    ReflTransGen Move C D := by
  classical
  let old : V ⊕ α → α := Sum.elim C.val id
  let next : V ⊕ α → α := Sum.elim D.val id
  let N : Set (V ⊕ α) := {x | Sum.elim (G.Adj v) (fun c => c ∉ L v) x}
  obtain ⟨z, z', hz, hz', related⟩ := KempeIndependentLift.colour_bridge
    a b (C.val v) (D.val v) old next N
    (by intro x hx; cases x with
        | inl x => exact C.val.valid hx
        | inr c => exact fun h => hx (by have he : C.val v = c := h; exact he ▸ C.property v))
    (by intro x hx; cases x with
        | inl x => exact D.val.valid hx
        | inr c => exact fun h => hx (by have he : D.val v = c := h; exact he ▸ D.property v))
    (by intro x hx; cases x with
        | inl x => exact pair x hx.ne.symm
        | inr c => exact Or.inl rfl)
  have zmem : z ∈ L v := by
    by_contra h
    exact hz (Sum.inr z) h rfl
  have z'mem : z' ∈ L v := by
    by_contra h
    exact hz' (Sum.inr z') h rfl
  let E : State G L := ⟨.mk (fun x => if x = v then z else C.val x) (by
    intro x y hxy
    by_cases hx : x = v <;> by_cases hy : y = v
    · exact (hxy.ne (hx.trans hy.symm)).elim
    · subst x; simpa [hy, old] using hz (Sum.inl y) hxy
    · subst y; simpa [hx, old] using (hz (Sum.inl x) hxy.symm).symm
    · simpa [hx, hy] using C.val.valid hxy), by
      intro x
      change (if x = v then z else C.val x) ∈ L x
      by_cases hx : x = v
      · subst x; simpa using zmem
      · simpa [hx] using C.property x⟩
  let F : State G L := ⟨.mk (fun x => if x = v then z' else D.val x) (by
    intro x y hxy
    by_cases hx : x = v <;> by_cases hy : y = v
    · exact (hxy.ne (hx.trans hy.symm)).elim
    · subst x; simpa [hy, next] using hz' (Sum.inl y) hxy
    · subst y; simpa [hx, next] using (hz' (Sum.inl x) hxy.symm).symm
    · simpa [hx, hy] using D.val.valid hxy), by
      intro x
      change (if x = v then z' else D.val x) ∈ L x
      by_cases hx : x = v
      · subst x; simpa using z'mem
      · simpa [hx] using D.property x⟩
  have applyE (x : V) : E.val x = if x = v then z else C.val x := rfl
  have applyF (x : V) : F.val x = if x = v then z' else D.val x := rfl
  have first : Move C E := move_one v C E (by intro x hx; simp [applyE, hx])
  have last : Move F D := move_one v F D (by intro x hx; simp [applyF, hx])
  have middle : Move E F := by
    refine ⟨a, b, fun x => ?_⟩
    by_cases hx : x = v
    · subst x; simpa [applyE, applyF] using related
    · simpa [applyE, applyF, hx] using pair x hx
  exact ((ReflTransGen.single first).tail middle).tail last

/-- Every nonempty finite forest supplies a leaf; no supplied peeling order is required. -/
theorem exists_leaf [Fintype V] [Nonempty V] (acyclic : G.IsAcyclic) :
    ∃ v : V, ∀ x y, G.Adj v x → G.Adj v y → x = y := by
  classical
  obtain ⟨v, w, p, hp, longest⟩ := Walk.exists_isPath_forall_isPath_length_le_length G
  have only (x : V) (hx : G.Adj v x) : x = p.snd := by
    apply acyclic.eq_snd_of_adj_start hp hx
    by_contra outside
    have longer := longest x w (p.cons hx.symm) (hp.cons outside)
    simp only [Walk.length_cons] at longer
    omega
  exact ⟨v, fun x y hx hy => (only x hx).trans (only y hy).symm⟩

private noncomputable def extend_vertex {L : V → Set α} (v : V)
    (E : (G.induce ({v} : Set V)ᶜ).Coloring α) (z : α) (hz : z ∈ L v)
    (allowed : ∀ x : ↥(({v} : Set V)ᶜ), E x ∈ L x)
    (good : ∀ x : ↥(({v} : Set V)ᶜ), G.Adj v x → z ≠ E x) : State G L := by
  classical
  exact ⟨.mk (fun x => if hx : x = v then z else E ⟨x, hx⟩) (by
    intro x y hxy
    by_cases hx : x = v <;> by_cases hy : y = v
    · exact (hxy.ne (hx.trans hy.symm)).elim
    · subst x; simpa [hy] using good ⟨y, hy⟩ hxy
    · subst y; simpa [hx] using (good ⟨x, hx⟩ hxy.symm).symm
    · simpa [hx, hy] using E.valid
        (show (G.induce ({v} : Set V)ᶜ).Adj ⟨x, hx⟩ ⟨y, hy⟩ from hxy)), by
      intro x
      change (if hx : x = v then z else E ⟨x, hx⟩) ∈ L x
      by_cases hx : x = v
      · subst x; simpa using hz
      · simpa [hx] using allowed ⟨x, hx⟩⟩

/-- A single induction handles all finite forests, arbitrary palettes and
arbitrary vertex lists. No assumption on the number of allowed colours is made. -/
theorem list_connected [Fintype V] (acyclic : G.IsAcyclic) (L : V → Set α)
    (C D : State G L) : ReflTransGen Move C D := by
  classical
  suffices ∀ n : ℕ, ∀ (V : Type u) [Fintype V] (G : SimpleGraph V),
      Fintype.card V = n → G.IsAcyclic → ∀ (L : V → Set α) (C D : State G L),
      ReflTransGen Move C D from this _ V G rfl acyclic L C D
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V inst G count acyclic L C D
    by_cases inhabited : Nonempty V
    · have := inhabited
      obtain ⟨v, leaf⟩ := exists_leaf acyclic
      let X : Set V := ({v} : Set V)ᶜ
      let H := G.induce X
      let L' : X → Set α := fun x => {c | c ∈ L x ∧
        (C.val v = D.val v → G.Adj v x → c ≠ C.val v)}
      let c : State H L' := ⟨C.val.restrictInduce X,
        fun x => ⟨C.property x, fun _ h => (C.val.valid h).symm⟩⟩
      let d : State H L' := ⟨D.val.restrictInduce X,
        fun x => ⟨D.property x, fun equal h => equal.symm ▸ (D.val.valid h).symm⟩⟩
      have extension (E : State H L') :
          ∃ F : State G L, ∀ x : X, F.val x = E.val x := by
        suffices ∃ z ∈ L v, ∀ x : X, G.Adj v x → z ≠ E.val x by
          obtain ⟨z, hz, good⟩ := this
          exact ⟨extend_vertex v E.val z hz (fun x => (E.property x).1) good,
            fun x => by
              change (if hx : x.val = v then z else E.val ⟨x, hx⟩) = E.val x
              exact dite_eq_right x.property⟩
        by_cases equal : C.val v = D.val v
        · exact ⟨C.val v, C.property v, fun x hx => ((E.property x).2 equal hx).symm⟩
        · by_cases edge : ∃ x : X, G.Adj v x
          · obtain ⟨x, hx⟩ := edge
            by_cases clash : C.val v = E.val x
            · refine ⟨D.val v, D.property v, fun y hy => ?_⟩
              have same : y = x := Subtype.ext (leaf y x hy hx)
              subst y
              exact fun hd => equal (clash.trans hd.symm)
            · refine ⟨C.val v, C.property v, fun y hy => ?_⟩
              have same : y = x := Subtype.ext (leaf y x hy hx)
              simpa [same] using clash
          · exact ⟨C.val v, C.property v, fun x hx => (edge ⟨x, hx⟩).elim⟩
      choose extend agrees using extension
      have shorter : Fintype.card X < n := by
        rw [← count]
        exact Fintype.card_subtype_lt (x := v) (by simp [X])
      have path := ih (Fintype.card X) shorter X H rfl (acyclic.induce X) L' c d
      have lifted : ReflTransGen Move (extend c) (extend d) :=
        ReflTransGen.lift' extend (by
          intro E F step
          obtain ⟨a, b, pair⟩ := step
          apply lift_vertex_pair v (extend E) (extend F) a b
          intro x hx
          simpa only [agrees E ⟨x, hx⟩, agrees F ⟨x, hx⟩] using pair ⟨x, hx⟩) _ _ path
      have first : Move C (extend c) := move_one v _ _ (fun x hx =>
        (agrees c ⟨x, hx⟩).symm)
      have last : Move (extend d) D := move_one v _ _ (fun x hx => agrees d ⟨x, hx⟩)
      exact (ReflTransGen.single first).trans (lifted.tail last)
    · have eq : C = D := Subtype.ext (DFunLike.ext _ _ (fun x => (inhabited ⟨x⟩).elim))
      subst D
      exact .refl

/-- All extensions of the same exterior are physically connected whenever
the induced hidden graph is a forest. The ambient graph is unrestricted. -/
theorem fibre_path [Fintype V] (S : Set V) (forest : (G.induce S).IsAcyclic)
    (C D : G.Coloring α) (agree : ∀ x, x ∉ S → C x = D x) :
    ReflTransGen (G.KempeStepAvoiding Sᶜ) C D := by
  classical
  let L : S → Set α := fun x => {c | ∀ y, y ∉ S → G.Adj x y → c ≠ C y}
  let c : State (G.induce S) L := ⟨C.restrictInduce S, fun _ _ _ h => C.valid h⟩
  let d : State (G.induce S) L := ⟨D.restrictInduce S, fun _ y hy h => by
    simpa [agree y hy] using D.valid h⟩
  let extend (E : State (G.induce S) L) : G.Coloring α :=
    KempeGuardedLift.glue S (C.restrictInduce Sᶜ) E.val
      (fun x y h => E.property x y y.property h)
  have hidden (E : State (G.induce S) L) (x : S) : extend E x = E.val x :=
    KempeGuardedLift.glue_hidden S _ _ _ x
  have outside (E : State (G.induce S) L) (x : ↥(Sᶜ)) : extend E x = C x :=
    KempeGuardedLift.glue_retained S _ _ _ x
  have path : ReflTransGen (G.KempeStepAvoiding Sᶜ) (extend c) (extend d) :=
    ReflTransGen.lift' extend (by
      intro E F step
      obtain ⟨a, b, pair⟩ := step
      apply Coloring.avoiding_of_pointwise_swap _ _ a b Sᶜ
      · intro x hx; rw [outside E ⟨x, hx⟩, outside F ⟨x, hx⟩]
      · intro x
        by_cases hx : x ∈ S
        · simpa only [hidden E ⟨x, hx⟩, hidden F ⟨x, hx⟩] using pair ⟨x, hx⟩
        · exact Or.inl ((outside F ⟨x, hx⟩).trans (outside E ⟨x, hx⟩).symm)) _ _
      (list_connected forest L c d)
  have initial : extend c = C := DFunLike.ext _ _ (fun x => by
    by_cases hx : x ∈ S
    · exact hidden c ⟨x, hx⟩
    · exact outside c ⟨x, hx⟩)
  have final : extend d = D := DFunLike.ext _ _ (fun x => by
    by_cases hx : x ∈ S
    · exact hidden d ⟨x, hx⟩
    · exact (outside d ⟨x, hx⟩).trans (agree x hx))
  exact initial ▸ final ▸ path

theorem fibres [Fintype V] (S : Set V) (forest : (G.induce S).IsAcyclic) :
    G.FibreConnected α Sᶜ := by
  intro C D equal
  exact fibre_path S forest C D (fun x hx => Coloring.boundaryWord_eq_iff.mp equal x hx)

/-- Exact guarded history equivalence for an arbitrarily large hidden forest.
The guards retain the full joint before/after constraint; no assertion that
the interface is an ordinary smaller graph is made. -/
theorem history_iff [Fintype V] (S : Set V) (forest : (G.induce S).IsAcyclic)
    (B : Set V) (retained : B ⊆ Sᶜ) (C D : G.Coloring α) :
    ReflTransGen (KempeGuardedLift.Step S B)
      (C.restrictInduce Sᶜ) (D.restrictInduce Sᶜ) ↔
      ReflTransGen (G.KempeStepAvoiding B) C D :=
  KempeGuardedLift.history_iff S B retained (fibres S forest) C D

end SimpleGraph.KempeForestFibre
