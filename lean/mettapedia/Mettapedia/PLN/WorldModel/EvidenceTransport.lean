import Mettapedia.PLN.WorldModel.EvidenceSpaces

/-!
# Transporting evidence along a change of representation

Truth of quantified observations transports along a map exactly when the map
covers the valid values (`HOL.GuardedQuantifierTransport.all_observations_iff_image`):
a projection that identifies values still transports every truth. Evidence
counts how many samples support a proposition, so it depends on how samples
are carried across.

* Carried as a bag, samples transport evidence along **every** map: the
  evidence of `φ` over the pushed-forward bag is the evidence of `φ ∘ f` over
  the original (`ofSamples_map`).
* Carried as a set, they transport evidence for every proposition **exactly
  when the map is injective** on the samples (`ofSamples_image_iff`): a set
  image merges the samples a map identifies.
* The projection `Prod.fst : Bool × Bool → Bool` transports every truth, and
  the evidence of `fun b => b` over its set image is `(1, 1)` against `(2, 2)`
  over the four samples (`Controls.projection_truth_not_counts`); the bag image
  keeps `(2, 2)`.

So an answer set read through a non-injective representation change keeps its
truths and loses its counts; answers read as multisets keep both.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.EvidenceTransport

open Mettapedia.PLN.WorldModel.EvidenceSpaces
open Mettapedia.PLN.WorldModel.EvidenceSpaces.Evidence

variable {A B : Type*}

/-- **A bag of samples transports evidence along every map.** -/
theorem ofSamples_map (φ : B → Bool) (f : A → B) (bag : Multiset A) :
    ofSamples φ (bag.map f) = ofSamples (φ ∘ f) bag := by
  simp only [ofSamples, Multiset.map_map]
  rfl

/-- The positive count of the proposition that always holds is the number of
samples. -/
theorem ofSamples_true_pos (bag : Multiset A) : (ofSamples (fun _ => true) bag).pos = bag.card := by
  induction bag using Multiset.induction_on with
  | empty => simp
  | cons a bag ih =>
      rw [ofSamples_cons, Evidence.add_pos, ih, Multiset.card_cons, add_comm]
      simp [sampleEvidence, positive]

/-- **A set of samples transports evidence for every proposition exactly when
the map is injective on it.** -/
theorem ofSamples_image_iff [DecidableEq B] (s : Finset A) (f : A → B) :
    (∀ φ : B → Bool, ofSamples φ (s.image f).val = ofSamples (φ ∘ f) s.val) ↔ Set.InjOn f s := by
  constructor
  · intro transports
    have counts := congrArg Evidence.pos (transports fun _ => true)
    rw [ofSamples_true_pos] at counts
    have : (s.image f).card = s.card := by
      have source : (ofSamples ((fun _ : B => true) ∘ f) s.val).pos = s.val.card :=
        ofSamples_true_pos s.val
      rw [source] at counts
      exact counts
    exact Finset.card_image_iff.mp this
  · intro injective φ
    rw [Finset.image_val_of_injOn injective, ofSamples_map]

namespace Controls

/-- **A projection transports every truth and not the counts.** Over the four
pairs of Booleans, the first projection preserves every existential and
universal observation, the set image reads the evidence of `fun b => b` as
`(1, 1)` instead of `(2, 2)`, and the bag image keeps `(2, 2)`. -/
theorem projection_truth_not_counts :
    (∀ P : Bool → Prop,
        ((∃ v : Bool × Bool, P v.1) ↔ ∃ b, P b) ∧ ((∀ v : Bool × Bool, P v.1) ↔ ∀ b, P b)) ∧
      ofSamples (fun b => b) ((Finset.univ : Finset (Bool × Bool)).image Prod.fst).val = ⟨1, 1⟩ ∧
      ofSamples ((fun b => b) ∘ Prod.fst) (Finset.univ : Finset (Bool × Bool)).val = ⟨2, 2⟩ ∧
      ofSamples (fun b => b) ((Finset.univ : Finset (Bool × Bool)).val.map Prod.fst) = ⟨2, 2⟩ := by
  refine ⟨fun P => ⟨⟨fun ⟨v, h⟩ => ⟨v.1, h⟩, fun ⟨b, h⟩ => ⟨(b, false), h⟩⟩,
      ⟨fun h b => h (b, false), fun h v => h v.1⟩⟩, ?_, ?_, ?_⟩ <;>
    exact Evidence.ext (by decide) (by decide)

end Controls

end Mettapedia.PLN.WorldModel.EvidenceTransport
