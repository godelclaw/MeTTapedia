import Mettapedia.Logic.HOL.SevenVirtues.Completeness
import Mettapedia.Logic.HOL.SevenVirtues.Expressiveness
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# Virtue 6: one sentence separates standard from general validity

The sentence `choice` says that the predicates on the individuals have a
choice function:

  `∃ c : (ι ⇒ prop) ⇒ ι. ∀ P : ι ⇒ prop. (∃ x. P x) → P (c P)`.

It holds in every full model with a nonempty base (`models_choice_of_full`),
by the ambient axiom of choice. It fails in an extensional Henkin model built
by the Fraenkel–Mostowski method (Andrews 1972 adapted that method to type
theory to show that choice is not derivable):

* the individuals are the atoms `ℕ`; permutations of the atoms act on every
  type, trivially on truth values and by conjugation on functions (`act`);
* a value is admissible when it maps admissible values to admissible values,
  respects the logical relation `Rel`, and is fixed by every permutation that
  fixes some finite set of atoms (`Adm`, `Supported`);
* term denotations commute with the action (`act_denote`) and are admissible
  and related under related valuations (`fundamental`), so this is a Henkin
  model (`permutationModel`), and it is extensional
  (`permutationModel_extensional`);
* a choice function `c` with finite support `S` would choose, for the
  predicate "outside `S`", an atom outside `S` that every permutation fixing
  `S` fixes; swapping it with another atom outside `S` moves it
  (`permutationModel_not_choice`).

Consequences: `choice_separates` (true in all full models with nonempty base,
false in an extensional Henkin model), and neither `choice` nor its negation is
derivable with excluded middle (`choice_not_provable`,
`not_choice_not_provable`). The model satisfies the axiom of descriptions
(`permutationModel_description`), so choice is not derivable from descriptions
either (`choice_not_provable_with_description`, Andrews 1972). In the same
model every admissible injection of the atoms is onto: the sentence `finite ι`
holds although there are infinitely many atoms
(`permutationModel_finite_but_infinite`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.SevenVirtues.Choice

open ClosedTheorySet

universe w

/-- The type of individuals. -/
abbrev ι : Ty Unit := .base ()

/-- No constants. -/
abbrev Pure : Ty Unit → Type := fun _ => Empty

/-! ## The sentence and its standard truth -/

section Sentence

variable {Const : Ty Unit → Type}

/-- `∃ c : (ι ⇒ prop) ⇒ ι. ∀ P : ι ⇒ prop. (∃ x. P x) → P (c P)`. -/
def choice : ClosedFormula Const :=
  .ex (σ := (ι ⇒ .prop) ⇒ ι) (.all (σ := ι ⇒ .prop) (.imp
    (.ex (.app (.var (.vs .vz)) (.var (.vz : Var [ι, ι ⇒ .prop, (ι ⇒ .prop) ⇒ ι] ι))))
    (.app (.var .vz) (.app (.var (.vs .vz)) (.var .vz)))))

/-- In a Henkin model, `choice` asks for an admissible choice function on the
admissible predicates. -/
theorem models_choice_iff (M : HenkinModel.{0, 0, w} Unit Const) :
    M.models choice ↔
      ∃ c : (M.Carrier () → ULift.{max 1 w} Prop) → M.Carrier (),
        M.adm ((ι ⇒ .prop) ⇒ ι) c ∧
          ∀ P : M.Carrier () → ULift.{max 1 w} Prop, M.adm (ι ⇒ .prop) P →
            (∃ x, (P x).down) → (P (c P)).down := by
  constructor
  · rintro ⟨c, hc, h⟩
    exact ⟨c, hc, fun P hP ⟨x, hx⟩ => h P hP ⟨x, M.base_mem () x, hx⟩⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨c, hc, fun P hP ⟨x, _, hx⟩ => h P hP ⟨x, hx⟩⟩

/-- **Standard truth.** Every full model with a nonempty base satisfies
`choice`. -/
theorem models_choice_of_full (M : HenkinModel.{0, 0, w} Unit Const) (full : M.FullDomains)
    [Nonempty (M.Carrier ())] : M.models choice := by
  classical
  rw [models_choice_iff]
  refine ⟨fun P => if h : ∃ x, (P x).down then Classical.choose h else Classical.arbitrary _,
    full _ _, fun P _ hP => ?_⟩
  simp only [dif_pos hP]
  exact Classical.choose_spec hP

end Sentence

/-! ## Atoms and the action of permutations -/

/-- The atoms. -/
abbrev Atom : Type 1 := ULift.{1} ℕ

/-- Carriers: the atoms at the base type. -/
abbrev Car : Unit → Type 1 := fun _ => Atom

/-- Ambient values at a type. -/
abbrev D (τ : Ty Unit) : Type 1 := Ty.denote.{0, 0} Car τ

/-- Permutations act trivially on truth values, by application on atoms and by
conjugation on functions. -/
def act : (τ : Ty Unit) → Equiv.Perm Atom → D τ → D τ
  | .prop, _, p => p
  | .base _, π, a => π a
  | .arr σ τ, π, f => fun x => act τ π (f (act σ π⁻¹ x))

theorem perm_inv_apply (π : Equiv.Perm Atom) (a : Atom) : π⁻¹ (π a) = a :=
  Equiv.Perm.inv_eq_iff_eq.mpr rfl

theorem perm_apply_inv (π : Equiv.Perm Atom) (a : Atom) : π (π⁻¹ a) = a := by
  have := perm_inv_apply π⁻¹ a
  rwa [inv_inv] at this

theorem act_inv_act : ∀ (τ : Ty Unit) (π : Equiv.Perm Atom) (x : D τ), act τ π⁻¹ (act τ π x) = x
  | .prop, _, _ => rfl
  | .base _, π, a => perm_inv_apply π a
  | .arr σ τ, π, f => by
      funext x
      change act τ π⁻¹ (act τ π (f (act σ π⁻¹ (act σ π⁻¹⁻¹ x)))) = f x
      rw [inv_inv, act_inv_act σ π, act_inv_act τ π]

theorem act_act_inv (τ : Ty Unit) (π : Equiv.Perm Atom) (x : D τ) : act τ π (act τ π⁻¹ x) = x := by
  simpa using act_inv_act τ π⁻¹ x

theorem act_mul : ∀ (τ : Ty Unit) (π ρ : Equiv.Perm Atom) (x : D τ),
    act τ π (act τ ρ x) = act τ (π * ρ) x
  | .prop, _, _, _ => rfl
  | .base _, π, ρ, a => (Equiv.Perm.mul_apply π ρ a).symm
  | .arr σ τ, π, ρ, f => by
      funext x
      change act τ π (act τ ρ (f (act σ ρ⁻¹ (act σ π⁻¹ x)))) = act τ (π * ρ) (f (act σ (π * ρ)⁻¹ x))
      rw [act_mul σ ρ⁻¹ π⁻¹, act_mul τ π ρ, mul_inv_rev]

/-- The action at a function type, applied to an acted argument. -/
theorem act_arr_apply (σ τ : Ty Unit) (π : Equiv.Perm Atom) (f : D (σ ⇒ τ)) (x : D σ) :
    act (σ ⇒ τ) π f (act σ π x) = act τ π (f x) := by
  change act τ π (f (act σ π⁻¹ (act σ π x))) = _
  rw [act_inv_act]

/-- `π` fixes every atom of `S`. -/
def Fixes (S : Finset Atom) (π : Equiv.Perm Atom) : Prop := ∀ a ∈ S, π a = a

/-- `x` is fixed by every permutation fixing some finite set of atoms. -/
def Supported (τ : Ty Unit) (x : D τ) : Prop :=
  ∃ S : Finset Atom, ∀ π, Fixes S π → act τ π x = x

/-- A permutation fixing `S` pointwise preserves membership in `S`, through its
inverse. -/
theorem fixes_inv_mem {S : Finset Atom} {π : Equiv.Perm Atom} (hπ : Fixes S π) (a : Atom) :
    π⁻¹ a ∈ S ↔ a ∈ S := by
  constructor
  · intro h
    have hfix : π (π⁻¹ a) = π⁻¹ a := hπ _ h
    rw [perm_apply_inv] at hfix
    rwa [hfix]
  · intro h
    have hfix : π a = a := hπ a h
    have : π⁻¹ a = a := by
      conv_lhs => rw [← hfix]
      exact perm_inv_apply π a
    rwa [this]

/-! ## Admissibility and the logical relation -/

/-- Admissibility and the logical relation, by recursion on types. -/
def info : (τ : Ty Unit) → (D τ → Prop) × (D τ → D τ → Prop)
  | .prop => (fun _ => True, fun p q => (p.down ↔ q.down))
  | .base _ => (fun _ => True, fun a b => a = b)
  | .arr σ τ =>
      (fun f => (∀ x, (info σ).1 x → (info τ).1 (f x)) ∧
          (∀ x y, (info σ).1 x → (info σ).1 y → (info σ).2 x y → (info τ).2 (f x) (f y)) ∧
          Supported (σ ⇒ τ) f,
       fun f g => ∀ x, (info σ).1 x → (info τ).2 (f x) (g x))

/-- Admissible values. -/
def Adm (τ : Ty Unit) : D τ → Prop := (info τ).1

/-- The logical relation. -/
def Rel (τ : Ty Unit) : D τ → D τ → Prop := (info τ).2

theorem adm_arr {σ τ : Ty Unit} (f : D (σ ⇒ τ)) :
    Adm (σ ⇒ τ) f ↔ (∀ x, Adm σ x → Adm τ (f x)) ∧
      (∀ x y, Adm σ x → Adm σ y → Rel σ x y → Rel τ (f x) (f y)) ∧ Supported (σ ⇒ τ) f :=
  Iff.rfl

theorem rel_arr {σ τ : Ty Unit} (f g : D (σ ⇒ τ)) :
    Rel (σ ⇒ τ) f g ↔ ∀ x, Adm σ x → Rel τ (f x) (g x) := Iff.rfl

theorem rel_symm : ∀ (τ : Ty Unit) {x y : D τ}, Rel τ x y → Rel τ y x
  | .prop, _, _, h => Iff.symm h
  | .base _, _, _, h => Eq.symm h
  | .arr _ τ, _, _, h => fun x hx => rel_symm τ (h x hx)

theorem rel_trans : ∀ (τ : Ty Unit) {x y z : D τ}, Rel τ x y → Rel τ y z → Rel τ x z
  | .prop, _, _, _, h₁, h₂ => Iff.trans h₁ h₂
  | .base _, _, _, _, h₁, h₂ => Eq.trans h₁ h₂
  | .arr _ τ, _, _, _, h₁, h₂ => fun x hx => rel_trans τ (h₁ x hx) (h₂ x hx)

theorem rel_refl : ∀ (τ : Ty Unit) {x : D τ}, Adm τ x → Rel τ x x
  | .prop, _, _ => Iff.rfl
  | .base _, _, _ => rfl
  | .arr _ τ, _, hf => fun x hx => rel_refl τ (hf.1 x hx)

theorem supported_of_adm : ∀ (τ : Ty Unit) {x : D τ}, Adm τ x → Supported τ x
  | .prop, _, _ => ⟨∅, fun _ _ => rfl⟩
  | .base _, a, _ => ⟨{a}, fun _ hπ => hπ a (Finset.mem_singleton_self a)⟩
  | .arr _ _, _, hf => hf.2.2

/-- **Equivariance of the relation and of admissibility.** -/
theorem equivariant : ∀ τ : Ty Unit,
    (∀ (π : Equiv.Perm Atom) (x y : D τ), Rel τ (act τ π x) (act τ π y) ↔ Rel τ x y) ∧
      (∀ (π : Equiv.Perm Atom) (x : D τ), Adm τ x → Adm τ (act τ π x))
  | .prop => ⟨fun _ _ _ => Iff.rfl, fun _ _ h => h⟩
  | .base _ => ⟨fun π _ _ => π.injective.eq_iff, fun _ _ _ => trivial⟩
  | .arr σ τ => by
      obtain ⟨relσ, admσ⟩ := equivariant σ
      obtain ⟨relτ, admτ⟩ := equivariant τ
      have admσ' : ∀ (π : Equiv.Perm Atom) (x : D σ), Adm σ (act σ π x) ↔ Adm σ x := by
        intro π x
        refine ⟨fun h => ?_, admσ π x⟩
        have := admσ π⁻¹ _ h
        rwa [act_inv_act] at this
      have relArr : ∀ (π : Equiv.Perm Atom) (f g : D (σ ⇒ τ)),
          Rel (σ ⇒ τ) (act (σ ⇒ τ) π f) (act (σ ⇒ τ) π g) ↔ Rel (σ ⇒ τ) f g := by
        intro π f g
        rw [rel_arr, rel_arr]
        constructor
        · intro h y hy
          have := h (act σ π y) ((admσ' π y).mpr hy)
          rwa [act_arr_apply, act_arr_apply, relτ] at this
        · intro h x hx
          have hy : Adm σ (act σ π⁻¹ x) := admσ π⁻¹ x hx
          have := (relτ π _ _).mpr (h _ hy)
          rwa [← act_arr_apply σ τ π f, ← act_arr_apply σ τ π g, act_act_inv] at this
      refine ⟨relArr, fun π f hf => ?_⟩
      obtain ⟨hmap, hresp, ⟨S, hS⟩⟩ := (adm_arr f).mp hf
      refine (adm_arr _).mpr ⟨?_, ?_, ?_⟩
      · intro x hx
        exact admτ π _ (hmap _ (admσ π⁻¹ x hx))
      · intro x y hx hy hxy
        change Rel τ (act τ π (f (act σ π⁻¹ x))) (act τ π (f (act σ π⁻¹ y)))
        rw [relτ]
        exact hresp _ _ (admσ π⁻¹ x hx) (admσ π⁻¹ y hy) ((relσ π⁻¹ x y).mpr hxy)
      · refine ⟨S.map π.toEmbedding, fun ρ hρ => ?_⟩
        have hconj : Fixes S (π⁻¹ * (ρ * π)) := by
          intro a ha
          have hρa : ρ (π a) = π a := hρ (π a) (Finset.mem_map_of_mem _ ha)
          simp [Equiv.Perm.mul_apply, hρa]
        calc act (σ ⇒ τ) ρ (act (σ ⇒ τ) π f)
            = act (σ ⇒ τ) π (act (σ ⇒ τ) π⁻¹ (act (σ ⇒ τ) ρ (act (σ ⇒ τ) π f))) :=
              (act_act_inv _ π _).symm
          _ = act (σ ⇒ τ) π (act (σ ⇒ τ) (π⁻¹ * (ρ * π)) f) := by
              rw [act_mul _ ρ π, act_mul _ π⁻¹ (ρ * π)]
          _ = act (σ ⇒ τ) π f := by rw [hS _ hconj]

theorem adm_act (τ : Ty Unit) (π : Equiv.Perm Atom) (x : D τ) : Adm τ (act τ π x) ↔ Adm τ x := by
  refine ⟨fun h => ?_, (equivariant τ).2 π x⟩
  have := (equivariant τ).2 π⁻¹ _ h
  rwa [act_inv_act] at this

theorem rel_act (τ : Ty Unit) (π : Equiv.Perm Atom) (x y : D τ) :
    Rel τ (act τ π x) (act τ π y) ↔ Rel τ x y :=
  (equivariant τ).1 π x y

/-! ## The premodel and its denotations -/

/-- The permutation premodel over the pure signature. -/
def permPreModel : PreModel.{0, 0, 0} Unit Pure where
  Carrier := Car
  adm := Adm
  base_mem := fun _ _ => trivial
  prop_mem := fun _ => trivial
  app_mem := fun hf hx => hf.1 _ hx
  constDen := fun c => nomatch c
  const_mem := fun c => nomatch c

theorem eqv_iff_rel : ∀ (τ : Ty Unit) (x y : D τ), permPreModel.Eqv τ x y ↔ Rel τ x y
  | .prop, _, _ => Iff.rfl
  | .base _, _, _ => Iff.rfl
  | .arr σ τ, f, g => by
      change (∀ x, Adm σ x → permPreModel.Eqv τ (f x) (g x)) ↔ ∀ x, Adm σ x → Rel τ (f x) (g x)
      simp only [eqv_iff_rel τ]

/-- Act on a valuation pointwise. -/
def actVal {Γ : Ctx Unit} (π : Equiv.Perm Atom) (ρ : permPreModel.Valuation Γ) :
    permPreModel.Valuation Γ := fun v => act _ π (ρ v)

theorem actVal_extend {Γ : Ctx Unit} {σ : Ty Unit} (π : Equiv.Perm Atom)
    (ρ : permPreModel.Valuation Γ) (x : D σ) :
    (fun {τ} (v : Var (σ :: Γ) τ) => actVal π (permPreModel.extend ρ x) v) =
      (fun {τ} (v : Var (σ :: Γ) τ) => permPreModel.extend (actVal π ρ) (act σ π x) v) := by
  funext τ v
  cases v <;> rfl

/-- **Denotation commutes with the action**, literally, at every valuation. -/
theorem act_denote {Γ : Ctx Unit} {τ : Ty Unit} (t : Term Pure Γ τ) (π : Equiv.Perm Atom)
    (ρ : permPreModel.Valuation Γ) :
    act τ π (permPreModel.denote t ρ) = permPreModel.denote t (actVal π ρ) := by
  induction t with
  | var v => rfl
  | const c => exact nomatch c
  | @app Γ σ τ f a ihf iha =>
      have h1 := act_arr_apply σ τ π (permPreModel.denote f ρ) (permPreModel.denote a ρ)
      rw [ihf, iha] at h1
      exact h1.symm
  | @lam σ Γ τ b ih =>
      funext x
      change act τ π (permPreModel.denote b (permPreModel.extend ρ (act σ π⁻¹ x))) =
        permPreModel.denote b (permPreModel.extend (actVal π ρ) x)
      rw [ih, actVal_extend, act_act_inv]
  | top => rfl
  | bot => rfl
  | and p q ihp ihq =>
      change ULift.up ((permPreModel.denote p ρ).down ∧ (permPreModel.denote q ρ).down) =
        ULift.up ((permPreModel.denote p (actVal π ρ)).down ∧
          (permPreModel.denote q (actVal π ρ)).down)
      rw [← ihp, ← ihq]
      rfl
  | or p q ihp ihq =>
      change ULift.up ((permPreModel.denote p ρ).down ∨ (permPreModel.denote q ρ).down) =
        ULift.up ((permPreModel.denote p (actVal π ρ)).down ∨
          (permPreModel.denote q (actVal π ρ)).down)
      rw [← ihp, ← ihq]
      rfl
  | imp p q ihp ihq =>
      change ULift.up ((permPreModel.denote p ρ).down → (permPreModel.denote q ρ).down) =
        ULift.up ((permPreModel.denote p (actVal π ρ)).down →
          (permPreModel.denote q (actVal π ρ)).down)
      rw [← ihp, ← ihq]
      rfl
  | not p ih =>
      change ULift.up (¬ (permPreModel.denote p ρ).down) =
        ULift.up (¬ (permPreModel.denote p (actVal π ρ)).down)
      rw [← ih]
      rfl
  | @eq Γ τ t s iht ihs =>
      change ULift.up (permPreModel.Eqv τ (permPreModel.denote t ρ) (permPreModel.denote s ρ)) =
        ULift.up (permPreModel.Eqv τ (permPreModel.denote t (actVal π ρ))
          (permPreModel.denote s (actVal π ρ)))
      rw [← iht, ← ihs]
      apply congrArg ULift.up
      apply propext
      exact (eqv_iff_rel τ _ _).trans ((rel_act τ π _ _).symm.trans (eqv_iff_rel τ _ _).symm)
  | @all σ Γ b ih =>
      change ULift.up (∀ x, Adm σ x → (permPreModel.denote b (permPreModel.extend ρ x)).down) =
        ULift.up (∀ x, Adm σ x →
          (permPreModel.denote b (permPreModel.extend (actVal π ρ) x)).down)
      apply congrArg ULift.up
      apply propext
      constructor
      · intro h x hx
        have := ih (permPreModel.extend ρ (act σ π⁻¹ x))
        rw [actVal_extend, act_act_inv] at this
        rw [← this]
        exact h _ ((adm_act σ π⁻¹ x).mpr hx)
      · intro h x hx
        have := ih (permPreModel.extend ρ x)
        rw [actVal_extend] at this
        change (act .prop π (permPreModel.denote b (permPreModel.extend ρ x))).down
        rw [this]
        exact h _ ((adm_act σ π x).mpr hx)
  | @ex σ Γ b ih =>
      change ULift.up (∃ x, Adm σ x ∧ (permPreModel.denote b (permPreModel.extend ρ x)).down) =
        ULift.up (∃ x, Adm σ x ∧
          (permPreModel.denote b (permPreModel.extend (actVal π ρ) x)).down)
      apply congrArg ULift.up
      apply propext
      constructor
      · rintro ⟨x, hx, hb⟩
        refine ⟨act σ π x, (adm_act σ π x).mpr hx, ?_⟩
        have := ih (permPreModel.extend ρ x)
        rw [actVal_extend] at this
        rw [← this]
        exact hb
      · rintro ⟨x, hx, hb⟩
        refine ⟨act σ π⁻¹ x, (adm_act σ π⁻¹ x).mpr hx, ?_⟩
        have := ih (permPreModel.extend ρ (act σ π⁻¹ x))
        rw [actVal_extend, act_act_inv] at this
        change (act .prop π (permPreModel.denote b (permPreModel.extend ρ (act σ π⁻¹ x)))).down
        rw [this]
        exact hb

/-- Values of a valuation over a finite context have a common finite support. -/
theorem exists_common_support : ∀ {Γ : Ctx Unit} (ρ : permPreModel.Valuation Γ),
    (∀ {σ : Ty Unit} (v : Var Γ σ), Supported σ (ρ v)) →
      ∃ S : Finset Atom, ∀ π, Fixes S π → ∀ {σ : Ty Unit} (v : Var Γ σ), act σ π (ρ v) = ρ v
  | [], _, _ => ⟨∅, fun _ _ _ v => nomatch v⟩
  | σ :: Γ, ρ, h => by
      obtain ⟨S₀, hS₀⟩ := h (.vz : Var (σ :: Γ) σ)
      obtain ⟨S₁, hS₁⟩ := exists_common_support (Γ := Γ) (fun v => ρ (.vs v)) (fun v => h (.vs v))
      refine ⟨S₀ ∪ S₁, fun π hπ τ v => ?_⟩
      cases v with
      | vz => exact hS₀ π (fun a ha => hπ a (Finset.mem_union_left _ ha))
      | vs v => exact hS₁ π (fun a ha => hπ a (Finset.mem_union_right _ ha)) v

/-- Related, admissible, supported pairs of valuations. -/
def Good {Γ : Ctx Unit} (ρ ρ' : permPreModel.Valuation Γ) : Prop :=
  ∀ {σ : Ty Unit} (v : Var Γ σ), Adm σ (ρ v) ∧ Adm σ (ρ' v) ∧ Rel σ (ρ v) (ρ' v)

theorem good_symm {Γ : Ctx Unit} {ρ ρ' : permPreModel.Valuation Γ} (h : Good ρ ρ') : Good ρ' ρ :=
  fun v => ⟨(h v).2.1, (h v).1, rel_symm _ (h v).2.2⟩

theorem good_extend {Γ : Ctx Unit} {σ : Ty Unit} {ρ ρ' : permPreModel.Valuation Γ}
    (h : Good ρ ρ') {x y : D σ} (hx : Adm σ x) (hy : Adm σ y) (hxy : Rel σ x y) :
    Good (permPreModel.extend ρ x) (permPreModel.extend ρ' y) := by
  intro τ v
  cases v with
  | vz => exact ⟨hx, hy, hxy⟩
  | vs v => exact h v

/-- **The fundamental lemma.** Under related admissible valuations, a term
denotes admissible, related values. -/
theorem fundamental {Γ : Ctx Unit} {τ : Ty Unit} (t : Term Pure Γ τ) :
    ∀ (ρ ρ' : permPreModel.Valuation Γ), Good ρ ρ' →
      Adm τ (permPreModel.denote t ρ) ∧
        Rel τ (permPreModel.denote t ρ) (permPreModel.denote t ρ') := by
  induction t with
  | var v => intro ρ ρ' h; exact ⟨(h v).1, (h v).2.2⟩
  | const c => exact nomatch c
  | app f a ihf iha =>
      intro ρ ρ' h
      obtain ⟨hF, hFF'⟩ := ihf ρ ρ' h
      obtain ⟨hA, hAA'⟩ := iha ρ ρ' h
      obtain ⟨hA', _⟩ := iha ρ' ρ (good_symm h)
      refine ⟨hF.1 _ hA, ?_⟩
      exact rel_trans _ (hF.2.1 _ _ hA hA' hAA') (hFF' _ hA')
  | @lam σ Γ τ b ih =>
      intro ρ ρ' h
      have hρ : Good ρ ρ := fun v => ⟨(h v).1, (h v).1, rel_refl _ (h v).1⟩
      refine ⟨(adm_arr _).mpr ⟨?_, ?_, ?_⟩, ?_⟩
      · intro x hx
        exact (ih _ _ (good_extend hρ hx hx (rel_refl _ hx))).1
      · intro x y hx hy hxy
        exact (ih _ _ (good_extend hρ hx hy hxy)).2
      · obtain ⟨S, hS⟩ := exists_common_support ρ (fun v => supported_of_adm _ (h v).1)
        refine ⟨S, fun π hπ => ?_⟩
        have hval : (fun {σ} (v : Var Γ σ) => actVal π ρ v) = (fun {σ} (v : Var Γ σ) => ρ v) := by
          funext σ v
          exact hS π hπ v
        have := act_denote (.lam b) π ρ
        rw [hval] at this
        exact this
      · intro x hx
        exact (ih _ _ (good_extend h hx hx (rel_refl _ hx))).2
  | top => intro _ _ _; exact ⟨trivial, Iff.rfl⟩
  | bot => intro _ _ _; exact ⟨trivial, Iff.rfl⟩
  | and p q ihp ihq =>
      intro ρ ρ' h
      exact ⟨trivial, and_congr (ihp ρ ρ' h).2 (ihq ρ ρ' h).2⟩
  | or p q ihp ihq =>
      intro ρ ρ' h
      exact ⟨trivial, or_congr (ihp ρ ρ' h).2 (ihq ρ ρ' h).2⟩
  | imp p q ihp ihq =>
      intro ρ ρ' h
      exact ⟨trivial, imp_congr (ihp ρ ρ' h).2 (ihq ρ ρ' h).2⟩
  | not p ih =>
      intro ρ ρ' h
      exact ⟨trivial, not_congr (ih ρ ρ' h).2⟩
  | @eq Γ τ t s iht ihs =>
      intro ρ ρ' h
      refine ⟨trivial, ?_⟩
      have ht := (iht ρ ρ' h).2
      have hs := (ihs ρ ρ' h).2
      refine (eqv_iff_rel τ _ _).trans (Iff.trans ?_ (eqv_iff_rel τ _ _).symm)
      constructor
      · intro hts
        exact rel_trans _ (rel_trans _ (rel_symm _ ht) hts) hs
      · intro hts
        exact rel_trans _ (rel_trans _ ht hts) (rel_symm _ hs)
  | @all σ Γ b ih =>
      intro ρ ρ' h
      refine ⟨trivial, ?_⟩
      change (∀ x, Adm σ x → _) ↔ (∀ x, Adm σ x → _)
      exact forall_congr' fun x => imp_congr_right fun hx =>
        (ih _ _ (good_extend h hx hx (rel_refl _ hx))).2
  | @ex σ Γ b ih =>
      intro ρ ρ' h
      refine ⟨trivial, ?_⟩
      change (∃ x, Adm σ x ∧ _) ↔ (∃ x, Adm σ x ∧ _)
      exact exists_congr fun x => ⟨fun ⟨hx, hb⟩ =>
        ⟨hx, (ih _ _ (good_extend h hx hx (rel_refl _ hx))).2.mp hb⟩,
        fun ⟨hx, hb⟩ => ⟨hx, (ih _ _ (good_extend h hx hx (rel_refl _ hx))).2.mpr hb⟩⟩

/-- **The permutation model**: an extensional Henkin model over the atoms. -/
def permutationModel : HenkinModel.{0, 0, 0} Unit Pure where
  toPreModel := permPreModel
  term_closed := by
    intro Γ τ t ρ hρ
    exact (fundamental t ρ ρ (fun v => ⟨hρ v, hρ v, rel_refl _ (hρ v)⟩)).1

theorem permutationModel_extensional : permutationModel.FunctionsRespectEqv := by
  intro σ τ f x y hf hx hy hxy
  have key : Rel τ ((show D σ → D τ from f) x) ((show D σ → D τ from f) y) :=
    hf.2.1 x y hx hy ((eqv_iff_rel σ x y).mp hxy)
  exact (eqv_iff_rel τ _ _).mpr key

/-- **Choice fails in the permutation model.** -/
theorem permutationModel_not_choice : ¬ permutationModel.models choice := by
  rw [models_choice_iff]
  rintro ⟨c, hc, hchoice⟩
  obtain ⟨S, hS⟩ := supported_of_adm ((ι ⇒ .prop) ⇒ ι) hc
  -- the predicate "outside `S`"
  let P : Atom → ULift.{1} Prop := fun a => .up (a ∉ S)
  have hPfix : ∀ π, Fixes S π → act (ι ⇒ .prop) π P = P := by
    intro π hπ
    refine funext fun (a : Atom) => ULift.ext _ _ (propext ?_)
    change π⁻¹ a ∉ S ↔ a ∉ S
    exact not_congr (fixes_inv_mem hπ a)
  have hPadm : Adm (ι ⇒ .prop) P := by
    refine (adm_arr (σ := ι) (τ := .prop) P).mpr ⟨fun _ _ => trivial, ?_, ⟨S, hPfix⟩⟩
    intro x y _ _ hxy
    change x = y at hxy
    subst hxy
    exact Iff.rfl
  obtain ⟨b, hb⟩ := Infinite.exists_notMem_finset S
  have hcP : (c P : Atom) ∉ S := hchoice P hPadm ⟨b, hb⟩
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : Atom, c P = a₀ := ⟨_, rfl⟩
  rw [ha₀] at hcP
  obtain ⟨d, hd⟩ := Infinite.exists_notMem_finset (insert a₀ S)
  have hdS : d ∉ S := fun h => hd (Finset.mem_insert_of_mem h)
  have hdc : d ≠ a₀ := fun h => hd (h ▸ Finset.mem_insert_self _ _)
  have hπ : Fixes S (Equiv.swap a₀ d) := by
    intro a ha
    exact Equiv.swap_apply_of_ne_of_ne (fun h => hcP (h ▸ ha)) (fun h => hdS (h ▸ ha))
  have hstay : act ι (Equiv.swap a₀ d) (c P) = c P := by
    have := act_arr_apply (ι ⇒ .prop) ι (Equiv.swap a₀ d) c P
    rw [hS _ hπ, hPfix _ hπ] at this
    exact this.symm
  rw [ha₀] at hstay
  have hmove : (Equiv.swap a₀ d) a₀ = d := Equiv.swap_apply_left a₀ d
  exact hdc (hmove.symm.trans hstay)

/-- Positive control: the type of choice functions is inhabited in the
permutation model, by a constant function. -/
theorem permutationModel_choiceType_inhabited :
    permutationModel.adm ((ι ⇒ .prop) ⇒ ι) (fun _ => (⟨0⟩ : Atom)) := by
  refine (adm_arr (σ := ι ⇒ .prop) (τ := ι) _).mpr ⟨fun _ _ => trivial, fun _ _ _ _ _ => rfl, ?_⟩
  refine ⟨{⟨0⟩}, fun π hπ => ?_⟩
  funext P
  exact hπ _ (Finset.mem_singleton_self _)

/-- A finitely supported function on the atoms commutes with every permutation
fixing its support. -/
theorem supported_commute {g : Atom → Atom} {S : Finset Atom}
    (hS : ∀ π, Fixes S π → act (ι ⇒ ι) π g = g) {π : Equiv.Perm Atom} (hπ : Fixes S π)
    (a : Atom) : g (π a) = π (g a) := by
  have := act_arr_apply ι ι π g a
  rw [hS π hπ] at this
  exact this

/-- **The atoms are Dedekind-finite in the permutation model**: every admissible
injective function on them is surjective, although there are infinitely many
atoms. -/
theorem permutationModel_not_dedekindInfinite :
    ¬ permutationModel.models (dedekindInfinite ()) := by
  classical
  rw [models_dedekindInfinite_iff_general]
  rintro ⟨f, hf, hinj, hsurj⟩
  obtain ⟨g, rfl⟩ : ∃ g : Atom → Atom, g = f := ⟨f, rfl⟩
  obtain ⟨S, hS⟩ := supported_of_adm (ι ⇒ ι) hf
  have hcomm : ∀ {π : Equiv.Perm Atom}, Fixes S π → ∀ a : Atom, g (π a) = π (g a) :=
    fun hπ a => supported_commute (g := g) hS hπ a
  -- `f` maps the support into itself.
  have hInto : ∀ s ∈ S, g s ∈ S := by
    intro s hs
    by_contra hfs
    obtain ⟨b, hb⟩ := Infinite.exists_notMem_finset (insert (g s) S)
    have hbS : b ∉ S := fun h => hb (Finset.mem_insert_of_mem h)
    have hbf : b ≠ g s := fun h => hb (h ▸ Finset.mem_insert_self _ _)
    have hπ : Fixes S (Equiv.swap (g s) b) := fun a ha =>
      Equiv.swap_apply_of_ne_of_ne (fun h => hfs (h ▸ ha)) (fun h => hbS (h ▸ ha))
    have := hcomm hπ s
    rw [hπ s hs, Equiv.swap_apply_left] at this
    exact hbf this.symm
  -- hence onto the support
  have hOnto : ∀ y ∈ S, ∃ s ∈ S, g s = y := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := Finset.surj_on_of_inj_on_of_card_le (s := S) (t := S)
      (fun a _ => g a) (fun a ha => hInto a ha) (fun a₁ a₂ _ _ h => hinj h) le_rfl y hy
    exact ⟨s, hs, rfl⟩
  -- and the identity outside it
  have hOut : ∀ a ∉ S, g a = a := by
    intro a ha
    by_contra hfa
    by_cases hfaS : g a ∈ S
    · obtain ⟨s, hs, hsa⟩ := hOnto (g a) hfaS
      exact ha (hinj hsa ▸ hs)
    · obtain ⟨b, hb⟩ := Infinite.exists_notMem_finset (insert a (insert (g a) S))
      have hbS : b ∉ S := fun h => hb (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
      have hba : b ≠ a := fun h => hb (h ▸ Finset.mem_insert_self _ _)
      have hbf : b ≠ g a := fun h => hb (h ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      have hπ : Fixes S (Equiv.swap a b) := fun x hx =>
        Equiv.swap_apply_of_ne_of_ne (fun h => ha (h ▸ hx)) (fun h => hbS (h ▸ hx))
      have := hcomm hπ a
      rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hfa (Ne.symm hbf)] at this
      exact hba (hinj this)
  apply hsurj
  intro y
  by_cases hy : y ∈ S
  · obtain ⟨s, _, hs⟩ := hOnto y hy
    exact ⟨s, hs⟩
  · exact ⟨y, hOut y hy⟩

/-- The permutation model satisfies `finite ι` although its base carrier is
infinite: in general models the sentence no longer means finiteness
(compare `models_finite_iff`). -/
theorem permutationModel_finite_but_infinite :
    permutationModel.models (finite ()) ∧ Infinite (permutationModel.Carrier ()) :=
  ⟨permutationModel_not_dedekindInfinite, inferInstanceAs (Infinite (ULift.{1} ℕ))⟩

/-! ## Descriptions hold in the permutation model -/

section Description

variable {Const : Ty Unit → Type}

/-- The axiom of descriptions: `∃ i : (ι ⇒ prop) ⇒ ι. ∀ x. i (λy. y = x) = x`. -/
def description : ClosedFormula Const :=
  .ex (σ := (ι ⇒ .prop) ⇒ ι) (.all (σ := ι)
    (.eq (.app (.var (.vs .vz)) (.lam (.eq (.var (.vz : Var [ι, ι, (ι ⇒ .prop) ⇒ ι] ι))
      (.var (.vs .vz))))) (.var .vz)))

end Description

open Classical in
/-- The description operator on the atoms: the unique element when there is
one, and the atom `0` otherwise. -/
noncomputable def descriptionOperator (P : Atom → ULift.{1} Prop) : Atom :=
  if h : ∃! x, (P x).down then Classical.choose h.exists else ⟨0⟩

theorem descriptionOperator_singleton (x : Atom) :
    descriptionOperator (fun y => ULift.up (y = x)) = x := by
  have h : ∃! y : Atom, (ULift.up (y = x) : ULift.{1} Prop).down := ⟨x, rfl, fun _ hy => hy⟩
  unfold descriptionOperator
  rw [dif_pos h]
  exact Classical.choose_spec h.exists

/-- **Descriptions hold in the permutation model** (Andrews 1972): the
description operator is fixed by every permutation fixing the atom `0`. -/
theorem permutationModel_description : permutationModel.models (description (Const := Pure)) := by
  classical
  have hadm : Adm ((ι ⇒ .prop) ⇒ ι) descriptionOperator := by
    refine (adm_arr (σ := ι ⇒ .prop) (τ := ι) _).mpr ⟨fun _ _ => trivial, ?_, ?_⟩
    · intro P Q _ _ hPQ
      have hEq : P = Q := funext fun a => ULift.ext _ _ (propext (hPQ a trivial))
      change descriptionOperator P = descriptionOperator Q
      rw [hEq]
    · refine ⟨{⟨0⟩}, fun π hπ => ?_⟩
      funext P
      obtain ⟨Q, rfl⟩ : ∃ Q : Atom → ULift.{1} Prop, Q = P := ⟨P, rfl⟩
      change π (descriptionOperator (act (ι ⇒ .prop) π⁻¹ Q)) = descriptionOperator Q
      have hcomp : act (ι ⇒ .prop) π⁻¹ Q = fun a => Q (π a) := by
        funext a
        change Q (π⁻¹⁻¹ a) = Q (π a)
        rw [inv_inv]
      rw [hcomp]
      by_cases h : ∃! x, (Q x).down
      · obtain ⟨x, hx, huniq⟩ := h
        have hu : ∃! x', (Q x').down := ⟨x, hx, huniq⟩
        have hxπ : (Q (π (π⁻¹ x))).down := by rw [perm_apply_inv]; exact hx
        have hu' : ∃! y, (Q (π y)).down :=
          ⟨π⁻¹ x, hxπ, fun y hy => by rw [← huniq (π y) hy, perm_inv_apply]⟩
        have hx' : descriptionOperator Q = x := by
          unfold descriptionOperator
          rw [dif_pos hu]
          exact huniq _ (Classical.choose_spec hu.exists)
        have hy' : descriptionOperator (fun a => Q (π a)) = π⁻¹ x := by
          unfold descriptionOperator
          rw [dif_pos hu']
          exact hu'.unique (Classical.choose_spec hu'.exists) hxπ
        rw [hx', hy', perm_apply_inv]
      · have hn' : ¬ ∃! y, (Q (π y)).down := by
          rintro ⟨y, hy, huniq⟩
          refine h ⟨π y, hy, fun z hz => ?_⟩
          have hzπ : (Q (π (π⁻¹ z))).down := by rw [perm_apply_inv]; exact hz
          rw [← huniq (π⁻¹ z) hzπ, perm_apply_inv]
        unfold descriptionOperator
        rw [dif_neg hn', dif_neg h]
        exact hπ ⟨0⟩ (Finset.mem_singleton_self _)
  refine ⟨descriptionOperator, hadm, fun x _ => ?_⟩
  change permPreModel.Eqv ι (descriptionOperator (fun y => ULift.up (permPreModel.Eqv ι y x))) x
  exact descriptionOperator_singleton x

/-- **Choice is not derivable even with descriptions** (Andrews 1972). -/
theorem choice_not_provable_with_description :
    ¬ Provable (Const := Pure) (insert excludedMiddle {description}) choice := fun h =>
  permutationModel_not_choice
    (soundness h permutationModel permutationModel_extensional (fun ψ hψ => by
      rw [Set.mem_singleton_iff] at hψ
      subst hψ
      exact permutationModel_description))

/-! ## Consequences -/

/-- **One sentence separates standard and general validity.** `choice` holds in
every full model with a nonempty base, and fails in an extensional Henkin
model. -/
theorem choice_separates :
    (∀ M : HenkinModel.{0, 0, 0} Unit Pure, M.FullDomains → Nonempty (M.Carrier ()) →
      M.models choice) ∧
    ∃ M : HenkinModel.{0, 0, 0} Unit Pure, M.FunctionsRespectEqv ∧ ¬ M.models choice :=
  ⟨fun M full _ => models_choice_of_full M full,
    ⟨permutationModel, permutationModel_extensional, permutationModel_not_choice⟩⟩

/-- The standard model on the atoms. -/
def atomModel : HenkinModel.{0, 0, 0} Unit Pure :=
  HenkinModel.standard Car (fun {_} c => nomatch c)

/-- **Choice is not derivable** with excluded middle (Andrews 1972). -/
theorem choice_not_provable :
    ¬ Provable (Const := Pure) (insert excludedMiddle ∅) choice := fun h =>
  permutationModel_not_choice
    (soundness h permutationModel permutationModel_extensional (fun _ h => absurd h id))

/-- Nor is its negation: the standard model on the atoms satisfies `choice`. -/
theorem not_choice_not_provable :
    ¬ Provable (Const := Pure) (insert excludedMiddle ∅) (.not choice) := fun h => by
  have hFull : atomModel.FullDomains := HenkinModel.fullDomains_standard _ _
  have : Nonempty (atomModel.Carrier ()) := ⟨⟨0⟩⟩
  exact (HenkinModel.models_not atomModel).mp
    (soundness h atomModel (atomModel.functionsRespectEqv_of_fullDomains hFull)
      (fun _ h => absurd h id))
    (models_choice_of_full atomModel hFull)

#print axioms models_choice_of_full
#print axioms permutationModel
#print axioms permutationModel_extensional
#print axioms permutationModel_not_choice
#print axioms choice_separates
#print axioms permutationModel_not_dedekindInfinite
#print axioms permutationModel_finite_but_infinite
#print axioms choice_not_provable
#print axioms permutationModel_description
#print axioms choice_not_provable_with_description
#print axioms not_choice_not_provable

end Mettapedia.Logic.HOL.SevenVirtues.Choice
