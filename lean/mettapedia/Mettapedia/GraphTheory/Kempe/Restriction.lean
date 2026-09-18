import Mettapedia.GraphTheory.Kempe.Boundary
import Mettapedia.Combinatorics.Reconfiguration.Composition

/-!
# Restriction to a sub-tangle: the concrete composition theorem

A graph `G` (for edge colourings, the line graph of a tangle), an input set
`B`, and a near side `X ⊇ B`.  Restricting a colouring of `G` to the subgraph
induced on `X` is a projection from the boundary-avoiding Kempe dynamics of `G`
to that of `G[X]`.  This is the fibration in the proof of Lemma 8.18 of the v23
manuscript, with `X` the upstream tangle and the rest of `G` the downstream one.

* **Fibres.**  Two colourings with the same restriction to `X` agree on `X`, so
  the far side's LKR_in with all of `X` fixed, `G.FibreConnected α X`, joins
  them by switches avoiding `X`, hence avoiding `B`.
* **Switch restriction** (the conclusion of Lemma 8.17).  If a two-colour
  component of `G` meets `X` in exactly a two-colour component of `G[X]`, then
  switching it restricts to switching that component.
* **Lifting from preparation** (Step 1 of Lemma 8.18, with the preparation made
  a hypothesis).  If for each near-side switch the far side can be moved, with
  `X` fixed, so that the component through the switched set meets `X` in exactly
  that set, every near-side switch lifts.

The concrete composition theorem `fibreConnected_of_restriction` takes the
lifting hypothesis only for moves whose target extends to `G`, as
`Reconfiguration.fibresConnected_of_parts` does, and its prepared form
`fibreConnected_of_restriction_of_prepared` asks the preparation only for those
moves.  The manuscript's form, preparation for every move
(`PairingPreparable`), yields the corollary
`fibreConnected_of_restriction_of_preparable`; for two gadgets in series that
hypothesis is false, because it would lift a move whose target has no
extension (`Kempe.TauSeries.not_pairingPreparable`).
-/

namespace SimpleGraph

open Relation
open Mettapedia.Combinatorics.Reconfiguration

variable {V α : Type*} {G : SimpleGraph V}

namespace Coloring

/-- Restriction of a colouring to the subgraph induced on `X`. -/
def restrictInduce (C : G.Coloring α) (X : Set V) : (G.induce X).Coloring α :=
  C.comp (Embedding.induce X).toHom

@[simp] theorem restrictInduce_apply (C : G.Coloring α) (X : Set V) (v : X) :
    C.restrictInduce X v = C v :=
  rfl

theorem restrictInduce_eq_iff {C D : G.Coloring α} {X : Set V} :
    C.restrictInduce X = D.restrictInduce X ↔ C.boundaryWord X = D.boundaryWord X := by
  constructor
  · intro h
    funext v
    exact congrArg (fun E : (G.induce X).Coloring α => E v) h
  · intro h
    ext v : 1
    exact congrFun h v

theorem mem_bicoloredSet_restrictInduce_iff (C : G.Coloring α) (X : Set V) {a b : α}
    (v : X) : v ∈ (C.restrictInduce X).bicoloredSet a b ↔ v.1 ∈ C.bicoloredSet a b :=
  Iff.rfl

variable [DecidableEq α]

/-- **Switch restriction.**  Let `C₁` agree with `C` on `X`.  If a two-colour
component `K₁` of `C₁` meets `X` in exactly the two-colour component `K` of the
restriction of `C`, then switching `K₁` restricts to switching `K`. -/
theorem restrictInduce_swapOnKempeComponent_of_eq {C₁ C : G.Coloring α} {X : Set V}
    (hres : C₁.restrictInduce X = C.restrictInduce X) {a b : α}
    (K₁ : (C₁.bicoloredSubgraph a b).ConnectedComponent)
    (K : ((C.restrictInduce X).bicoloredSubgraph a b).ConnectedComponent)
    (hK : ∀ v : X, v.1 ∈ C₁.kempeComponentSet a b K₁ ↔
      v ∈ (C.restrictInduce X).kempeComponentSet a b K) :
    (C₁.swapOnKempeComponent a b K₁).restrictInduce X =
      (C.restrictInduce X).swapOnKempeComponent a b K := by
  have hcol : ∀ v : X, C₁ v = C v := fun v =>
    congrArg (fun E : (G.induce X).Coloring α => E v) hres
  ext v : 1
  rw [restrictInduce_apply]
  by_cases hv : v ∈ (C.restrictInduce X).kempeComponentSet a b K
  · rw [C₁.swapOnKempeComponent_apply_of_mem ((hK v).2 hv),
      swapOnKempeComponent_apply_of_mem _ hv, restrictInduce_apply, hcol v]
  · rw [C₁.swapOnKempeComponent_apply_of_not_mem (fun h => hv ((hK v).1 h)),
      swapOnKempeComponent_apply_of_not_mem _ hv, restrictInduce_apply, hcol v]

/-- The case `C₁ = C`: the conclusion of Lemma 8.17. -/
theorem restrictInduce_swapOnKempeComponent (C : G.Coloring α) (X : Set V) {a b : α}
    (K' : (C.bicoloredSubgraph a b).ConnectedComponent)
    (K : ((C.restrictInduce X).bicoloredSubgraph a b).ConnectedComponent)
    (hK : ∀ v : X, v.1 ∈ C.kempeComponentSet a b K' ↔
      v ∈ (C.restrictInduce X).kempeComponentSet a b K) :
    (C.swapOnKempeComponent a b K').restrictInduce X =
      (C.restrictInduce X).swapOnKempeComponent a b K :=
  restrictInduce_swapOnKempeComponent_of_eq rfl K' K hK

end Coloring

variable [DecidableEq α]

/-- Moves of the near side: switches of the colouring of `G[X]` avoiding the
input `B`. -/
abbrev nearStep (G : SimpleGraph V) (X B : Set V) :
    (G.induce X).Coloring α → (G.induce X).Coloring α → Prop :=
  (G.induce X).KempeStepAvoiding (Subtype.val ⁻¹' B)

/-- Restriction to the near side. -/
abbrev nearProj (X : Set V) (C : G.Coloring α) : (G.induce X).Coloring α :=
  C.restrictInduce X

/-- **Fibres of restriction are connected** as soon as the far side satisfies
LKR_in with the whole near side fixed. -/
theorem fibresConnected_nearProj {X B : Set V} (hBX : B ⊆ X)
    (hfar : G.FibreConnected α X) :
    FibresConnected (G.KempeStepAvoiding (α := α) B) (nearProj (G := G) X) := by
  intro C D hCD
  have hword : C.boundaryWord X = D.boundaryWord X := Coloring.restrictInduce_eq_iff.1 hCD
  exact (hfar C D hword).mono fun _ _ h => h.mono hBX

/-- Preparation for one near-side switch: after switches avoiding `X`, some
two-colour component meets `X` in exactly the switched set. -/
def PreparedFor (C : G.Coloring α) (X : Set V) (a b : α)
    (K : ((C.restrictInduce X).bicoloredSubgraph a b).ConnectedComponent) : Prop :=
  ∃ C₁, ReflTransGen (G.KempeStepAvoiding X) C C₁ ∧
    ∃ K₁ : (C₁.bicoloredSubgraph a b).ConnectedComponent,
      ∀ v : X, v.1 ∈ C₁.kempeComponentSet a b K₁ ↔
        v ∈ (C.restrictInduce X).kempeComponentSet a b K

/-- The manuscript's preparation hypothesis: every input-avoiding near-side
switch can be prepared. -/
def PairingPreparable (G : SimpleGraph V) (α : Type*) [DecidableEq α] (X B : Set V) : Prop :=
  ∀ (C : G.Coloring α) (a b : α)
    (K : ((C.restrictInduce X).bicoloredSubgraph a b).ConnectedComponent),
    Disjoint ((C.restrictInduce X).kempeComponentSet a b K) (Subtype.val ⁻¹' B) →
      PreparedFor C X a b K

/-- Preparation asked only of switches whose target extends to `G`. -/
def PairingPreparableOnImage (G : SimpleGraph V) (α : Type*) [DecidableEq α]
    (X B : Set V) : Prop :=
  ∀ (C : G.Coloring α) (a b : α)
    (K : ((C.restrictInduce X).bicoloredSubgraph a b).ConnectedComponent),
    Disjoint ((C.restrictInduce X).kempeComponentSet a b K) (Subtype.val ⁻¹' B) →
    (∃ D : G.Coloring α,
      D.restrictInduce X = (C.restrictInduce X).swapOnKempeComponent a b K) →
      PreparedFor C X a b K

theorem PairingPreparable.onImage {X B : Set V} (h : G.PairingPreparable α X B) :
    G.PairingPreparableOnImage α X B :=
  fun C a b K hK _ => h C a b K hK

/-- **One prepared switch lifts.**  After the preparation, switching the
prepared component avoids `B` and restricts to the near-side switch. -/
theorem lift_of_preparedFor {X B : Set V} (hBX : B ⊆ X) {C : G.Coloring α} {a b : α}
    {K : ((C.restrictInduce X).bicoloredSubgraph a b).ConnectedComponent}
    (hK : Disjoint ((C.restrictInduce X).kempeComponentSet a b K) (Subtype.val ⁻¹' B))
    (hprep : PreparedFor C X a b K) :
    ∃ D : G.Coloring α,
      D.restrictInduce X = (C.restrictInduce X).swapOnKempeComponent a b K ∧
        ReflTransGen (G.KempeStepAvoiding B) C D := by
  obtain ⟨C₁, hpath, K₁, hK₁⟩ := hprep
  have hres : C₁.restrictInduce X = C.restrictInduce X :=
    Coloring.restrictInduce_eq_iff.2 (reflTransGen_kempeStepAvoiding_boundaryWord hpath)
  refine ⟨C₁.swapOnKempeComponent a b K₁,
    Coloring.restrictInduce_swapOnKempeComponent_of_eq hres K₁ K hK₁,
    (hpath.mono fun _ _ h => h.mono hBX).tail ⟨a, b, K₁, ?_, rfl⟩⟩
  rw [Set.disjoint_left]
  intro w hw hwB
  have hwX : w ∈ X := hBX hwB
  exact Set.disjoint_left.1 hK ((hK₁ ⟨w, hwX⟩).1 hw) hwB

/-- **Lifting from preparation on the image.** -/
theorem liftsSteps_nearProj_of_preparableOnImage {X B : Set V} (hBX : B ⊆ X)
    (hprep : G.PairingPreparableOnImage α X B) :
    LiftsSteps (G.KempeStepAvoiding (α := α) B)
      (ImageStep (nearStep G X B) (nearProj (G := G) X)) (nearProj (G := G) X) := by
  rintro C β ⟨⟨a, b, K, hK, rfl⟩, hext⟩
  obtain ⟨D, hD, hpath⟩ := lift_of_preparedFor hBX hK (hprep C a b K hK hext)
  exact ⟨D, hD, hpath⟩

/-- **Lifting from preparation**, the manuscript's form. -/
theorem liftsSteps_nearProj_of_preparable {X B : Set V} (hBX : B ⊆ X)
    (hprep : G.PairingPreparable α X B) :
    LiftsSteps (G.KempeStepAvoiding (α := α) B) (nearStep G X B) (nearProj (G := G) X) := by
  rintro C β ⟨a, b, K, hK, rfl⟩
  obtain ⟨D, hD, hpath⟩ := lift_of_preparedFor hBX hK (hprep C a b K hK)
  exact ⟨D, hD, hpath⟩

/-- **The concrete composition theorem.**  With input `B` inside the near side
`X`:

* `hfar` — the far side satisfies LKR_in with `X` fixed;
* `hlift` — every input-avoiding near-side switch from a restriction to a
  colouring that extends lifts to a path of input-avoiding switches of `G`;
* `hnear` — restrictions of two colourings with the same input word are joined
  by input-avoiding near-side switches through colourings that extend.

Then `G` satisfies LKR_in relative to `B`. -/
theorem fibreConnected_of_restriction {X B : Set V} (hBX : B ⊆ X)
    (hfar : G.FibreConnected α X)
    (hlift : LiftsSteps (G.KempeStepAvoiding (α := α) B)
      (ImageStep (nearStep G X B) (nearProj (G := G) X)) (nearProj (G := G) X))
    (hnear : ∀ C D : G.Coloring α, C.boundaryWord B = D.boundaryWord B →
      ReflTransGen (ImageStep (nearStep G X B) (nearProj (G := G) X))
        (C.restrictInduce X) (D.restrictInduce X)) :
    G.FibreConnected α B :=
  fibresConnected_of_parts (fun β : (G.induce X).Coloring α => fun v : B => β ⟨v.1, hBX v.2⟩)
    (fibresConnected_nearProj hBX hfar) hlift hnear

/-- The composition theorem with lifting supplied by preparation on the
image. -/
theorem fibreConnected_of_restriction_of_prepared {X B : Set V} (hBX : B ⊆ X)
    (hfar : G.FibreConnected α X) (hprep : G.PairingPreparableOnImage α X B)
    (hnear : ∀ C D : G.Coloring α, C.boundaryWord B = D.boundaryWord B →
      ReflTransGen (ImageStep (nearStep G X B) (nearProj (G := G) X))
        (C.restrictInduce X) (D.restrictInduce X)) :
    G.FibreConnected α B :=
  fibreConnected_of_restriction hBX hfar
    (liftsSteps_nearProj_of_preparableOnImage hBX hprep) hnear

/-- **The manuscript's argument for Lemma 8.18**, with its preparation step as an
explicit hypothesis: far-side LKR_in, near-side LKR_in, and preparation of every
near-side switch give LKR_in of the whole. -/
theorem fibreConnected_of_restriction_of_preparable {X B : Set V} (hBX : B ⊆ X)
    (hfar : G.FibreConnected α X) (hprep : G.PairingPreparable α X B)
    (hnear : (G.induce X).FibreConnected α (Subtype.val ⁻¹' B)) :
    G.FibreConnected α B := by
  have h := fibresConnected_of_parts_of_liftsSteps
    (fun β : (G.induce X).Coloring α => β.boundaryWord (Subtype.val ⁻¹' B))
    (fibresConnected_nearProj hBX hfar) (liftsSteps_nearProj_of_preparable hBX hprep) hnear
  refine h.of_imp fun C D hCD => ?_
  funext v
  exact congrFun hCD ⟨v.1.1, v.2⟩

end SimpleGraph
