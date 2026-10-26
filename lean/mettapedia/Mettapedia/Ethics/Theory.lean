import Mettapedia.Ethics.Core

set_option autoImplicit false

namespace Mettapedia.Ethics

universe u v w

namespace Theory

/-- Push a theory forward along a sentence translation function. -/
def map {α : Type u} {β : Type v} (f : α → β) (T : Theory α) : Theory β :=
  fun b => ∃ a, a ∈ T ∧ f a = b

theorem mem_map_of_mem {α : Type u} {β : Type v} {f : α → β} {T : Theory α} {a : α}
    (h : a ∈ T) : f a ∈ map f T :=
  ⟨a, h, rfl⟩

theorem map_singleton {α : Type u} {β : Type v} (f : α → β) (a : α) :
    map f ({a} : Theory α) = ({f a} : Theory β) :=
  Set.image_singleton

end Theory

/--
Semantic entailment under an additional model-side premise `C`.

For ethics this is the contextual form used when a theory is evaluated inside a
particular situation description.
-/
def EntailsUnder {S : Type u} {M : Type v}
    (sem : Semantics S M) (T : Theory S) (C : M → Prop) (φ : S) : Prop :=
  ∀ m, C m → Models sem m T → sem.Sat m φ

section SentenceTranslation

variable {S₁ : Type u} {S₂ : Type v} {M : Type w}
  (sem₁ : Semantics S₁ M) (sem₂ : Semantics S₂ M) (f : S₁ → S₂)
  (h_sat : ∀ m s, sem₁.Sat m s ↔ sem₂.Sat m (f s))

include h_sat

theorem models_map_iff
    (m : M) (T : Theory S₁) :
    Models sem₁ m T ↔ Models sem₂ m (Theory.map f T) := by
  change (∀ s ∈ T, sem₁.Sat m s) ↔ ∀ s ∈ f '' T, sem₂.Sat m s
  rw [Set.forall_mem_image]
  exact forall_congr' fun s => imp_congr_right fun _ => h_sat m s

theorem entails_map_iff
    (T : Theory S₁) (s : S₁) :
    Entails sem₁ T s ↔ Entails sem₂ (Theory.map f T) (f s) :=
  forall_congr' fun m =>
    imp_congr (models_map_iff sem₁ sem₂ f h_sat m T) (h_sat m s)

theorem entails_map_iff_under
    (T : Theory S₁) (C : M → Prop) (s : S₁) :
    EntailsUnder sem₁ T C s ↔ EntailsUnder sem₂ (Theory.map f T) C (f s) :=
  forall_congr' fun m => imp_congr_right fun _ =>
    imp_congr (models_map_iff sem₁ sem₂ f h_sat m T) (h_sat m s)

end SentenceTranslation

/-- A theory is satisfiable if it has at least one model. -/
def Satisfiable {S : Type u} {M : Type v} (sem : Semantics S M) (T : Theory S) : Prop :=
  ∃ m, Models sem m T

/-- Two theories are equivalent if they have the same semantic consequences. -/
def Equivalent {S : Type u} {M : Type v} (sem : Semantics S M) (T₁ T₂ : Theory S) : Prop :=
  ∀ φ, Entails sem T₁ φ ↔ Entails sem T₂ φ

end Mettapedia.Ethics
