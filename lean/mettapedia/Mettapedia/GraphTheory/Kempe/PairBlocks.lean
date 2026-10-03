import Mettapedia.GraphTheory.Kempe.GuardedLift

/-!
# Simultaneous guarded elimination of isolated vertices and pairs

Hidden vertices carry block labels, all hidden edges stay within a block,
and each nonempty block has at most two vertices. Their restriction fibres
are connected. The joint transition guard factors into one local condition
per block, even when different blocks share retained neighbours.

The number of blocks and the ambient graph are unrestricted. All local
conditions use the same retained colouring and the same transposition.
-/

namespace SimpleGraph.KempePairBlocks

open Relation KempeGuardedLift

variable {V α ι : Type*} {G : SimpleGraph V}

def block (S : Set V) (label : V → ι) (i : ι) : Set V :=
  {x | x ∈ S ∧ label x = i}

/-- Distinct hidden blocks have no edges between them. Sharing retained
neighbours is allowed. -/
def Separated (G : SimpleGraph V) (S : Set V) (label : V → ι) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, G.Adj x y → label x = label y

/-- Every nonempty block is contained in a pair of its own vertices.
The two vertices may be equal, covering singleton blocks. -/
def Small (S : Set V) (label : V → ι) : Prop :=
  ∀ x ∈ S, ∃ y ∈ S, label y = label x ∧
    ∀ z ∈ S, label z = label x → z = x ∨ z = y

variable [DecidableEq α]

/-- Correct one block at a time. The endpoint discrepancy strictly decreases;
all intermediate physical switches avoid the entire retained graph. -/
theorem fibre_path [Fintype V] (S : Set V) (label : V → ι)
    (sep : Separated G S label) (small : Small S label)
    (C D : G.Coloring α) (agree : ∀ x, x ∉ S → C x = D x) :
    ReflTransGen (G.KempeStepAvoiding Sᶜ) C D := by
  classical
  suffices ∀ n : ℕ, ∀ C : G.Coloring α,
      (Finset.univ.filter fun x => C x ≠ D x).card = n →
      (∀ x, x ∉ S → C x = D x) →
      ReflTransGen (G.KempeStepAvoiding Sᶜ) C D from this _ C rfl agree
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro C hcard agree
    by_cases heq : C = D
    · subst C; exact .refl
    obtain ⟨u, hu⟩ : ∃ u, C u ≠ D u := by
      by_contra! equal
      exact heq (DFunLike.ext _ _ equal)
    have huS : u ∈ S := by by_contra h; exact hu (agree u h)
    obtain ⟨v, hvS, hvlabel, cover⟩ := small u huS
    let T := block S label (label u)
    have outside (x y : V) (hx : x ∈ T) (hy : y ∉ T) (hxy : G.Adj x y) : y ∉ S := by
      intro hyS
      exact hy ⟨hyS, (sep x hx.1 y hyS hxy).symm.trans hx.2⟩
    let E : G.Coloring α := .mk (fun x => if x ∈ T then D x else C x) (by
      intro x y hxy
      by_cases hx : x ∈ T <;> by_cases hy : y ∈ T
      · simpa [hx, hy] using D.valid hxy
      · simpa [hx, hy, agree y (outside x y hx hy hxy)] using D.valid hxy
      · simpa [hx, hy, agree x (outside y x hy hx hxy.symm)] using D.valid hxy
      · simpa [hx, hy] using C.valid hxy)
    have applyE (x : V) : E x = if x ∈ T then D x else C x := rfl
    have first : ReflTransGen (G.KempeStepAvoiding Sᶜ) C E :=
      ReflTransGen.mono (fun _ _ step => step.mono (by
        intro x hx hpair
        rcases hpair with rfl | rfl
        · exact hx huS
        · exact hx hvS)) _ _
        (KempeTwoVertexFibre.fibre_path u v C E (by
          intro x hxu hxv
          have hx : x ∉ T := fun h => (cover x h.1 h.2).elim hxu hxv
          simp [applyE, hx]))
    let bad := Finset.univ.filter fun x => C x ≠ D x
    let remaining := Finset.univ.filter fun x => E x ≠ D x
    have sub : remaining ⊆ bad := by
      intro x hx
      have hne := (Finset.mem_filter.mp hx).2
      have hout : x ∉ T := fun ht => hne (by simp [applyE, ht])
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [applyE, hout] using hne⟩
    have uBad : u ∈ bad := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩
    have uDone : u ∉ remaining := by
      intro h
      exact (Finset.mem_filter.mp h).2 (by simp [applyE, T, block, huS])
    have decrease : remaining.card < n := by
      rw [← hcard]
      exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
        ⟨sub, fun h => uDone (h.symm ▸ uBad)⟩)
    exact first.trans (ih remaining.card decrease E rfl (by
      intro x hx
      have hout : x ∉ T := fun h => hx h.1
      simpa [applyE, hout] using agree x hx))

theorem fibres [Fintype V] (S : Set V) (label : V → ι)
    (sep : Separated G S label) (small : Small S label) :
    G.FibreConnected α Sᶜ := by
  intro C D equal
  exact fibre_path S label sep small C D
    (fun x hx => Coloring.boundaryWord_eq_iff.mp equal x hx)

/-- One block's before/after assignments, with the common retained neighbours
observed jointly. There are at most four colour variables for pair blocks. -/
def LocalTransition (S : Set V) (label : V → ι) (i : ι)
    (C D : (G.induce Sᶜ).Coloring α) (a b : α) : Prop :=
  ∃ h k : (G.induce (block S label i)).Coloring α,
    (∀ (x : block S label i) (y : ↥(Sᶜ)), G.Adj x y → h x ≠ C y) ∧
    (∀ (x : block S label i) (y : ↥(Sᶜ)), G.Adj x y → k x ≠ D y) ∧
    ∀ x, k x = h x ∨ k x = Equiv.swap a b (h x)

omit [DecidableEq α] in
private theorem select_eq (S : Set V) (label : V → ι)
    (h : ∀ i, (G.induce (block S label i)).Coloring α) (x : S)
    (i : ι) (same : label x = i) :
    h (label x) ⟨x, x.property, rfl⟩ = h i ⟨x, x.property, same⟩ := by
  subst i
  rfl

/-- The local conditions assemble exact joint witnesses. This factorization
uses separation, but not a bound on block size. -/
theorem transition_iff (S : Set V) (label : V → ι) (sep : Separated G S label)
    (C D : (G.induce Sᶜ).Coloring α) (a b : α) :
    Transition S C D a b ↔ ∀ i, LocalTransition S label i C D a b := by
  classical
  constructor
  · rintro ⟨h, k, hf, kf, related⟩ i
    let f : G.induce (block S label i) →g G.induce S :=
      ⟨fun x => ⟨x, x.property.1⟩, fun hxy => hxy⟩
    exact ⟨h.comp f, k.comp f, fun x y hxy => hf (f x) y hxy,
      fun x y hxy => kf (f x) y hxy, fun x => related (f x)⟩
  · intro allBlocks
    choose h k hf kf related using allBlocks
    let H : (G.induce S).Coloring α := .mk
      (fun x => h (label x) ⟨x, x.property, rfl⟩) (by
        intro x y hxy
        have same := sep x x.property y y.property hxy
        have ne := (h (label x)).valid
          (show (G.induce (block S label (label x))).Adj
            ⟨x, x.property, rfl⟩ ⟨y, y.property, same.symm⟩ from hxy)
        exact fun equal => ne (equal.trans (select_eq S label h y (label x) same.symm)))
    let K : (G.induce S).Coloring α := .mk
      (fun x => k (label x) ⟨x, x.property, rfl⟩) (by
        intro x y hxy
        have same := sep x x.property y y.property hxy
        have ne := (k (label x)).valid
          (show (G.induce (block S label (label x))).Adj
            ⟨x, x.property, rfl⟩ ⟨y, y.property, same.symm⟩ from hxy)
        exact fun equal => ne (equal.trans (select_eq S label k y (label x) same.symm)))
    exact ⟨H, K, fun x y hxy => hf (label x) ⟨x, x.property, rfl⟩ y hxy,
      fun x y hxy => kf (label x) ⟨x, x.property, rfl⟩ y hxy,
      fun x => related (label x) ⟨x, x.property, rfl⟩⟩

/-- A single transposition is shared by all block guards. -/
def Step (S : Set V) (label : V → ι) (B : Set V)
    (C D : (G.induce Sᶜ).Coloring α) : Prop :=
  (∃ a b, (∀ x, D x = C x ∨ D x = Equiv.swap a b (C x)) ∧
    ∀ i, LocalTransition S label i C D a b) ∧
    ∀ x : ↥(Sᶜ), x.val ∈ B → C x = D x

theorem step_iff (S : Set V) (label : V → ι) (sep : Separated G S label)
    (B : Set V) (C D : (G.induce Sᶜ).Coloring α) :
    Step S label B C D ↔ KempeGuardedLift.Step S B C D := by
  simp only [Step, KempeGuardedLift.Step, transition_iff S label sep]

/-- Simultaneous elimination of any number of isolated vertices and pairs
preserves exactly the physical histories when the local guards are retained. -/
theorem history_iff [Fintype V] (S : Set V) (label : V → ι)
    (sep : Separated G S label) (small : Small S label)
    (B : Set V) (retained : B ⊆ Sᶜ) (C D : G.Coloring α) :
    ReflTransGen (Step S label B) (C.restrictInduce Sᶜ) (D.restrictInduce Sᶜ) ↔
      ReflTransGen (G.KempeStepAvoiding B) C D := by
  have steps : Step (G := G) (α := α) S label B = KempeGuardedLift.Step S B :=
    funext fun E => funext fun F => propext (step_iff S label sep B E F)
  rw [steps]
  exact KempeGuardedLift.history_iff S B retained (fibres S label sep small) C D

end SimpleGraph.KempePairBlocks
