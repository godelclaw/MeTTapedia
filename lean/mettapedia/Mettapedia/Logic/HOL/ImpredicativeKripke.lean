import Mettapedia.Logic.HOL.ProofSyntaxModuloKripke
import Mettapedia.Logic.HOL.ImpredicativeProofModulo

/-!
# The impredicative connectives in Kripke models

In a Kripke model of proofs modulo conversion the quantifier over propositions ranges over every upward-closed set,
so the impredicative definitions of the derived connectives (`ImpredicativeProofModulo`) mean what they should:

* the primitive formers mean their clauses (`holds_all`, `holds_imp`, `holds_and`, `holds_ex`, `holds_eq`);
* `⊥ := ∀r. r` holds nowhere (`holds_falsity`), and `p → ⊥` holds where `p` fails at every later world
  (`holds_negation`);
* `p ∧ q := ∀r. (p → q → r) → r` holds where both hold (`holds_conjunctionFormula`);
* `p ∨ q := ∀r. (p → r) → (q → r) → r` holds where one of them holds (`holds_disjunctionFormula`);
* `∃x. φ := ∀r. (∀x. φ → r) → r` holds where some element has `φ` (`holds_existentialInline`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.KripkeModulo.Model

open Mettapedia.Logic.HOL.ImpredicativeConnectives (falsity conjunctionFormula disjunctionFormula existentialInline)

universe u v

variable {Base : Type u} {Const : Ty Base → Type v} (M : Model Base Const)
variable {Γ : Ctx Base}

theorem holds_all {σ : Ty Base} (b : Formula Const (σ :: Γ)) (ρ : M.Valuation Γ) (w : M.frame.World) :
    (M.denote (.all b) ρ).holds w ↔ ∀ x, (M.denote b (M.extend ρ x)).holds w := Iff.rfl

theorem holds_imp (p q : Formula Const Γ) (ρ : M.Valuation Γ) (w : M.frame.World) :
    (M.denote (.imp p q) ρ).holds w ↔ ∀ v, M.frame.le w v → (M.denote p ρ).holds v → (M.denote q ρ).holds v :=
  Iff.rfl

theorem holds_and (p q : Formula Const Γ) (ρ : M.Valuation Γ) (w : M.frame.World) :
    (M.denote (.and p q) ρ).holds w ↔ (M.denote p ρ).holds w ∧ (M.denote q ρ).holds w := Iff.rfl

theorem holds_ex {σ : Ty Base} (b : Formula Const (σ :: Γ)) (ρ : M.Valuation Γ) (w : M.frame.World) :
    (M.denote (.ex b) ρ).holds w ↔ ∃ x, (M.denote b (M.extend ρ x)).holds w := Iff.rfl

theorem holds_eq {τ : Ty Base} (l r : Term Const Γ τ) (ρ : M.Valuation Γ) (w : M.frame.World) :
    (M.denote (.eq l r) ρ).holds w ↔ M.denote l ρ = M.denote r ρ := Iff.rfl

theorem holds_of_eq {d e : M.frame.Up} (same : d = e) (w : M.frame.World) : d.holds w → e.holds w :=
  same ▸ id

theorem holds_falsity (ρ : M.Valuation Γ) (w : M.frame.World) :
    (M.denote (falsity : Formula Const Γ) ρ).holds w ↔ False :=
  ⟨fun everything => everything (M.frame.constUp False), False.elim⟩

theorem holds_negation (p : Formula Const Γ) (ρ : M.Valuation Γ) (w : M.frame.World) :
    (M.denote (.imp p falsity) ρ).holds w ↔ ∀ v, M.frame.le w v → ¬ (M.denote p ρ).holds v :=
  ⟨fun refuted v hwv holds => (M.holds_falsity ρ v).mp (refuted v hwv holds),
    fun never v hwv holds => (never v hwv holds).elim⟩

theorem holds_conjunctionFormula (p q : Formula Const Γ) (ρ : M.Valuation Γ) (w : M.frame.World) :
    (M.denote (conjunctionFormula p q) ρ).holds w ↔ (M.denote p ρ).holds w ∧ (M.denote q ρ).holds w := by
  have hp : ∀ r : M.D .prop, M.denote (weaken p) (M.extend ρ r) = M.denote p ρ := M.denote_weaken p ρ
  have hq : ∀ r : M.D .prop, M.denote (weaken q) (M.extend ρ r) = M.denote q ρ := M.denote_weaken q ρ
  constructor
  · intro both
    refine both (M.frame.andUp (M.denote p ρ) (M.denote q ρ)) w (M.frame.le_refl w) fun u _ held t hut held' => ?_
    replace held := M.holds_of_eq (hp _) u held
    replace held' := M.holds_of_eq (hq _) t held'
    exact And.intro ((M.denote p ρ).mono hut held) held'
  · rintro ⟨held, held'⟩ r v hwv elim
    have first := M.holds_of_eq (hp r).symm v ((M.denote p ρ).mono hwv held)
    have second := M.holds_of_eq (hq r).symm v ((M.denote q ρ).mono hwv held')
    exact elim v (M.frame.le_refl v) first v (M.frame.le_refl v) second

theorem holds_disjunctionFormula (p q : Formula Const Γ) (ρ : M.Valuation Γ) (w : M.frame.World) :
    (M.denote (disjunctionFormula p q) ρ).holds w ↔ (M.denote p ρ).holds w ∨ (M.denote q ρ).holds w := by
  have hp : ∀ r : M.D .prop, M.denote (weaken p) (M.extend ρ r) = M.denote p ρ := M.denote_weaken p ρ
  have hq : ∀ r : M.D .prop, M.denote (weaken q) (M.extend ρ r) = M.denote q ρ := M.denote_weaken q ρ
  constructor
  · intro either
    refine either (M.frame.orUp (M.denote p ρ) (M.denote q ρ)) w (M.frame.le_refl w) (fun u _ held => ?_) w
      (M.frame.le_refl w) fun u _ held => ?_
    · exact Or.inl (M.holds_of_eq (hp _) u held)
    · exact Or.inr (M.holds_of_eq (hq _) u held)
  · rintro (held | held) r v hwv left t hvt right
    · have first := M.holds_of_eq (hp r).symm v ((M.denote p ρ).mono hwv held)
      exact r.mono hvt (left v (M.frame.le_refl v) first)
    · have second := M.holds_of_eq (hq r).symm t ((M.denote q ρ).mono (M.frame.le_trans hwv hvt) held)
      exact right t (M.frame.le_refl t) second

theorem holds_existentialInline {σ : Ty Base} (φ : Formula Const (σ :: Γ)) (ρ : M.Valuation Γ)
    (w : M.frame.World) :
    (M.denote (existentialInline φ) ρ).holds w ↔ ∃ x, (M.denote φ (M.extend ρ x)).holds w := by
  have lifted : ∀ (r : M.D .prop) (x : M.D σ),
      M.denote (rename (Rename.lift Rename.weaken) φ) (M.extend (M.extend ρ r) x) = M.denote φ (M.extend ρ x) := by
    intro r x
    rw [M.denote_rename]
    congr 1
    funext τ i
    cases i <;> rfl
  constructor
  · intro some
    refine some (M.frame.exUp fun x => M.denote φ (M.extend ρ x)) w (M.frame.le_refl w) fun x u _ held => ?_
    exact ⟨x, M.holds_of_eq (lifted _ x) u held⟩
  · rintro ⟨x, held⟩ r v hwv elim
    have found := M.holds_of_eq (lifted r x).symm v ((M.denote φ (M.extend ρ x)).mono hwv held)
    exact elim x v (M.frame.le_refl v) found

end Mettapedia.Logic.HOL.KripkeModulo.Model
