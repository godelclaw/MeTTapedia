import Mathlib.Order.CompleteBooleanAlgebra
import Mettapedia.Logic.HOL.Semantics.FullTypeStructure
import Mettapedia.Logic.HOL.Semantics.HeytingGeneral

/-!
# Frame-valued models of the EM-free calculus

Let `H` be a frame (a complete Heyting algebra) and `C` a family of base
carriers.  Over the full type structure with truth values in `H`, every type
gets an `H`-valued equality and a notion of admissible element:

* at `prop`, equality is bi-implication and every truth value is admissible;
* at a base type, equality is crisp and every element is admissible;
* at `σ ⇒ τ`, equality is the meet over admissible arguments, and a function is
  admissible when it maps admissible arguments to admissible values and
  respects equality.

Quantifiers range over admissible elements, `∀` as a meet and `∃` as a join.
Naming every admissible element by a constant makes the quantifier values
exact over closed instances, so the structure is a `HeytingGeneralModel` of the
signature of names.  This is the Heyting-valued (Rasiowa–Sikorski) reading of
higher-order logic; DeMarco and Lipton (J. Logic Comput. 15(6), 2005, §4)
call such structures global models.

The point of a frame that is not completely distributive: a meet over an
infinite family need not distribute over a binary join, so the
constant-domain schema fails (`ConstantDomainCountermodel`).
-/

namespace Mettapedia.Logic.HOL
namespace FrameValued

universe u w

variable {Base : Type u}

/-! ## Bi-implication -/

section Biimp

variable {H : Type w} [Order.Frame H]

/-- Bi-implication in a frame. -/
def biimp (p q : H) : H := (p ⇨ q) ⊓ (q ⇨ p)

theorem le_biimp {ω p q : H} (h₁ : ω ⊓ p ≤ q) (h₂ : ω ⊓ q ≤ p) : ω ≤ biimp p q :=
  le_inf (le_himp_iff.mpr h₁) (le_himp_iff.mpr h₂)

theorem inf_le_of_le_biimp_left {ω p q : H} (h : ω ≤ biimp p q) : ω ⊓ p ≤ q :=
  le_himp_iff.mp (h.trans inf_le_left)

theorem inf_le_of_le_biimp_right {ω p q : H} (h : ω ≤ biimp p q) : ω ⊓ q ≤ p :=
  le_himp_iff.mp (h.trans inf_le_right)

theorem biimp_self (p : H) : biimp p p = ⊤ := by
  simp [biimp]

theorem biimp_comm (p q : H) : biimp p q = biimp q p :=
  inf_comm _ _

theorem biimp_trans (p q r : H) : biimp p q ⊓ biimp q r ≤ biimp p r := by
  have hpq : biimp p q ⊓ biimp q r ≤ biimp p q := inf_le_left
  have hqr : biimp p q ⊓ biimp q r ≤ biimp q r := inf_le_right
  refine le_biimp ?_ ?_
  · calc biimp p q ⊓ biimp q r ⊓ p
        ≤ biimp p q ⊓ biimp q r ⊓ q :=
          le_inf inf_le_left (inf_le_of_le_biimp_left hpq)
      _ ≤ r := inf_le_of_le_biimp_left hqr
  · calc biimp p q ⊓ biimp q r ⊓ r
        ≤ biimp p q ⊓ biimp q r ⊓ q :=
          le_inf inf_le_left (inf_le_of_le_biimp_right hqr)
      _ ≤ p := inf_le_of_le_biimp_right hpq

theorem biimp_inf_congr {ω a a' b b' : H} (ha : ω ≤ biimp a a') (hb : ω ≤ biimp b b') :
    ω ≤ biimp (a ⊓ b) (a' ⊓ b') := by
  refine le_biimp (le_inf ?_ ?_) (le_inf ?_ ?_)
  · exact (inf_le_inf_left ω inf_le_left).trans (inf_le_of_le_biimp_left ha)
  · exact (inf_le_inf_left ω inf_le_right).trans (inf_le_of_le_biimp_left hb)
  · exact (inf_le_inf_left ω inf_le_left).trans (inf_le_of_le_biimp_right ha)
  · exact (inf_le_inf_left ω inf_le_right).trans (inf_le_of_le_biimp_right hb)

theorem biimp_sup_congr {ω a a' b b' : H} (ha : ω ≤ biimp a a') (hb : ω ≤ biimp b b') :
    ω ≤ biimp (a ⊔ b) (a' ⊔ b') := by
  refine le_biimp ?_ ?_
  · rw [inf_sup_left]
    exact sup_le_sup (inf_le_of_le_biimp_left ha) (inf_le_of_le_biimp_left hb)
  · rw [inf_sup_left]
    exact sup_le_sup (inf_le_of_le_biimp_right ha) (inf_le_of_le_biimp_right hb)

theorem biimp_himp_congr {ω a a' b b' : H} (ha : ω ≤ biimp a a') (hb : ω ≤ biimp b b') :
    ω ≤ biimp (a ⇨ b) (a' ⇨ b') := by
  refine le_biimp (le_himp_iff.mpr ?_) (le_himp_iff.mpr ?_)
  · calc ω ⊓ (a ⇨ b) ⊓ a'
        ≤ ω ⊓ ((a ⇨ b) ⊓ a) :=
          le_inf (inf_le_left.trans inf_le_left)
            (le_inf (inf_le_left.trans inf_le_right)
              (le_inf (inf_le_left.trans inf_le_left) inf_le_right |>.trans
                (inf_le_of_le_biimp_right ha)))
      _ ≤ ω ⊓ b := inf_le_inf_left ω himp_inf_le
      _ ≤ b' := inf_le_of_le_biimp_left hb
  · calc ω ⊓ (a' ⇨ b') ⊓ a
        ≤ ω ⊓ ((a' ⇨ b') ⊓ a') :=
          le_inf (inf_le_left.trans inf_le_left)
            (le_inf (inf_le_left.trans inf_le_right)
              (le_inf (inf_le_left.trans inf_le_left) inf_le_right |>.trans
                (inf_le_of_le_biimp_left ha)))
      _ ≤ ω ⊓ b' := inf_le_inf_left ω himp_inf_le
      _ ≤ b := inf_le_of_le_biimp_right hb

theorem biimp_compl_congr {ω a a' : H} (ha : ω ≤ biimp a a') :
    ω ≤ biimp aᶜ a'ᶜ := by
  have h := biimp_himp_congr ha (le_top.trans (biimp_self (⊥ : H)).ge)
  simpa only [himp_bot] using h

theorem biimp_iInf_congr {ι : Sort*} {ω : H} {f g : ι → H}
    (h : ∀ i, ω ≤ biimp (f i) (g i)) : ω ≤ biimp (⨅ i, f i) (⨅ i, g i) := by
  refine le_biimp (le_iInf fun i => ?_) (le_iInf fun i => ?_)
  · exact (inf_le_inf_left ω (iInf_le f i)).trans (inf_le_of_le_biimp_left (h i))
  · exact (inf_le_inf_left ω (iInf_le g i)).trans (inf_le_of_le_biimp_right (h i))

theorem biimp_iSup_congr {ι : Sort*} {ω : H} {f g : ι → H}
    (h : ∀ i, ω ≤ biimp (f i) (g i)) : ω ≤ biimp (⨆ i, f i) (⨆ i, g i) := by
  refine le_biimp ?_ ?_
  · rw [inf_iSup_eq]
    exact iSup_le fun i => (inf_le_of_le_biimp_left (h i)).trans (le_iSup g i)
  · rw [inf_iSup_eq]
    exact iSup_le fun i => (inf_le_of_le_biimp_right (h i)).trans (le_iSup f i)

end Biimp

/-! ## Admissible elements and `H`-valued equality -/

variable (H : Type w) [Order.Frame H] (C : Base → Type w)

/-- Admissibility and `H`-valued equality on one carrier. -/
structure Reading (X : Type w) where
  adm : X → Prop
  eqv : X → X → H

open Classical in
/-- Admissibility and `H`-valued equality, by recursion on types. -/
noncomputable def reading : (τ : Ty Base) → Reading H (Ty.full H C τ)
  | .prop => ⟨fun _ => True, fun p q => biimp p q⟩
  | .base _ => ⟨fun _ => True, fun d e => if d = e then ⊤ else ⊥⟩
  | .arr σ τ =>
      ⟨fun f => (∀ d, (reading σ).adm d → (reading τ).adm (f d)) ∧
          ∀ d e, (reading σ).adm d → (reading σ).adm e →
            (reading σ).eqv d e ≤ (reading τ).eqv (f d) (f e),
        fun f g => ⨅ d : {d // (reading σ).adm d}, (reading τ).eqv (f d.1) (g d.1)⟩

/-- Admissible elements of a type. -/
def Adm (τ : Ty Base) (d : Ty.full H C τ) : Prop := (reading H C τ).adm d

/-- The `H`-valued equality of a type. -/
noncomputable def Eqv (τ : Ty Base) (d e : Ty.full H C τ) : H := (reading H C τ).eqv d e

theorem adm_prop (p : H) : Adm H C .prop p := trivial

theorem adm_base {b : Base} (d : C b) : Adm H C (.base b) d := trivial

theorem adm_arr {σ τ : Ty Base} (f : Ty.full H C (σ ⇒ τ)) :
    Adm H C (σ ⇒ τ) f ↔
      (∀ d, Adm H C σ d → Adm H C τ (f d)) ∧
        ∀ d e, Adm H C σ d → Adm H C σ e → Eqv H C σ d e ≤ Eqv H C τ (f d) (f e) :=
  Iff.rfl

theorem eqv_prop (p q : H) : Eqv H C .prop p q = biimp p q := rfl

open Classical in
theorem eqv_base_self {b : Base} (d : C b) : Eqv H C (.base b) d d = ⊤ := by
  show (if d = d then (⊤ : H) else ⊥) = ⊤
  exact if_pos rfl

open Classical in
theorem eqv_base_of_ne {b : Base} {d e : C b} (h : d ≠ e) : Eqv H C (.base b) d e = ⊥ := by
  show (if d = e then (⊤ : H) else ⊥) = ⊥
  exact if_neg h

theorem eqv_arr {σ τ : Ty Base} (f g : Ty.full H C (σ ⇒ τ)) :
    Eqv H C (σ ⇒ τ) f g = ⨅ d : {d // Adm H C σ d}, Eqv H C τ (f d.1) (g d.1) := rfl

variable {H C}

theorem eqv_refl : ∀ {τ : Ty Base} {d : Ty.full H C τ}, Adm H C τ d → Eqv H C τ d d = ⊤
  | .prop, p, _ => biimp_self (H := H) p
  | .base _, d, _ => eqv_base_self H C d
  | .arr _ _, _, hf => iInf_eq_top.mpr fun d => eqv_refl (hf.1 d.1 d.2)

theorem eqv_symm : ∀ {τ : Ty Base} (d e : Ty.full H C τ), Eqv H C τ d e = Eqv H C τ e d
  | .prop, p, q => biimp_comm (H := H) p q
  | .base _, d, e => by
      by_cases h : d = e
      · subst h; rfl
      · rw [eqv_base_of_ne H C h, eqv_base_of_ne H C (Ne.symm h)]
  | .arr _ _, f, g => iInf_congr fun d => eqv_symm (f d.1) (g d.1)

theorem eqv_trans : ∀ {τ : Ty Base} (d e k : Ty.full H C τ),
    Eqv H C τ d e ⊓ Eqv H C τ e k ≤ Eqv H C τ d k
  | .prop, p, q, r => biimp_trans (H := H) p q r
  | .base _, d, e, k => by
      by_cases hde : d = e
      · subst hde
        exact inf_le_right
      · rw [eqv_base_of_ne H C hde]
        exact inf_le_left.trans bot_le
  | .arr _ _, f, g, h => le_iInf fun d =>
      (inf_le_inf (iInf_le _ d) (iInf_le _ d)).trans (eqv_trans (f d.1) (g d.1) (h d.1))

/-! ## A chosen admissible element of every type -/

section Default

variable (H C) [∀ b, Nonempty (C b)]

/-- A chosen element of every type: `⊥` at `prop`, any element at a base type,
and constant functions at arrow types. -/
noncomputable def defaultElem : (τ : Ty Base) → Ty.full H C τ
  | .prop => (⊥ : H)
  | .base b => Classical.choice (inferInstance : Nonempty (C b))
  | .arr _ τ => fun _ => defaultElem τ

/-- The chosen element is admissible. -/
theorem adm_defaultElem : ∀ τ : Ty Base, Adm H C τ (defaultElem H C τ)
  | .prop => trivial
  | .base _ => trivial
  | .arr _ τ => ⟨fun _ _ => adm_defaultElem τ,
      fun _ _ _ _ => le_top.trans (eqv_refl (adm_defaultElem τ)).ge⟩

end Default

/-! ## The signature of names and its full type structure -/

variable (H C)

/-- The signature with one constant naming each admissible element. -/
def Names (τ : Ty Base) : Type w := {d : Ty.full H C τ // Adm H C τ d}

/-- The full type structure over `H`: lattice operations on truth values,
`H`-valued equality, quantifiers as meets and joins over the admissible
elements; a name denotes the element it names. -/
@[reducible] noncomputable def typeStructure : FullTypeStructure.{u, w, w} Base (Names H C) where
  Truth := H
  Carrier := C
  top := ⊤
  bot := ⊥
  and := (· ⊓ ·)
  or := (· ⊔ ·)
  imp := (· ⇨ ·)
  not := fun p => pᶜ
  eq := fun τ d e => Eqv H C τ d e
  all := fun σ F => ⨅ d : {d // Adm H C σ d}, F d.1
  ex := fun σ F => ⨆ d : {d // Adm H C σ d}, F d.1
  const := fun c => c.1

local notation "𝕊" => typeStructure H C

variable {H C}

/-- A valuation is admissible when every variable is sent to an admissible
element. -/
def AdmVal {Γ : Ctx Base} (ρ : (𝕊).Valuation Γ) : Prop :=
  ∀ {σ} (v : Var Γ σ), Adm H C σ (ρ v)

theorem admVal_empty : AdmVal (H := H) (C := C) (𝕊).emptyVal :=
  fun v => nomatch v

theorem admVal_extend {Γ : Ctx Base} {σ : Ty Base} {ρ : (𝕊).Valuation Γ}
    (hρ : AdmVal ρ) {d : Ty.full H C σ} (hd : Adm H C σ d) :
    AdmVal ((𝕊).extend ρ d) := by
  intro τ v
  cases v with
  | vz => exact hd
  | vs v => exact hρ v

/-- **Fundamental lemma.**  Under admissible valuations every term denotes an
admissible element, and the denotation respects `H`-valued equality of the
valuations. -/
theorem fundamental {Γ : Ctx Base} {τ : Ty Base} (t : Term (Names H C) Γ τ) :
    ∀ ρ : (𝕊).Valuation Γ, AdmVal ρ →
      Adm H C τ ((𝕊).denote t ρ) ∧
        ∀ ρ' : (𝕊).Valuation Γ, AdmVal ρ' → ∀ ω : H,
          (∀ {σ} (v : Var Γ σ), ω ≤ Eqv H C σ (ρ v) (ρ' v)) →
            ω ≤ Eqv H C τ ((𝕊).denote t ρ) ((𝕊).denote t ρ') := by
  induction t with
  | var v => exact fun ρ hρ => ⟨hρ v, fun _ _ _ hω => hω v⟩
  | const c => exact fun _ _ => ⟨c.2, fun _ _ _ _ => le_top.trans (eqv_refl c.2).ge⟩
  | app f t ihf iht =>
      intro ρ hρ
      obtain ⟨hf, hf'⟩ := ihf ρ hρ
      obtain ⟨ht, ht'⟩ := iht ρ hρ
      refine ⟨hf.1 _ ht, fun ρ' hρ' ω hω => ?_⟩
      have ha' := (iht ρ' hρ').1
      exact (le_inf ((ht' ρ' hρ' ω hω).trans (hf.2 _ _ ht ha'))
        ((hf' ρ' hρ' ω hω).trans (iInf_le _ ⟨_, ha'⟩))).trans (eqv_trans _ _ _)
  | lam t iht =>
      intro ρ hρ
      refine ⟨⟨fun d hd => (iht _ (admVal_extend hρ hd)).1, fun d e hd he => ?_⟩,
        fun ρ' hρ' ω hω => ?_⟩
      · refine (iht _ (admVal_extend hρ hd)).2 _ (admVal_extend hρ he) _ ?_
        intro σ v
        cases v with
        | vz => exact le_rfl
        | vs v => exact le_top.trans (eqv_refl (hρ v)).ge
      · refine le_iInf fun d => (iht _ (admVal_extend hρ d.2)).2 _
          (admVal_extend hρ' d.2) ω ?_
        intro σ v
        cases v with
        | vz => exact le_top.trans (eqv_refl d.2).ge
        | vs v => exact hω v
  | top => exact fun _ _ => ⟨trivial, fun _ _ _ _ => le_top.trans (biimp_self (H := H) ⊤).ge⟩
  | bot => exact fun _ _ => ⟨trivial, fun _ _ _ _ => le_top.trans (biimp_self (H := H) ⊥).ge⟩
  | and φ ψ ihφ ihψ =>
      exact fun ρ hρ => ⟨trivial, fun ρ' hρ' ω hω =>
        biimp_inf_congr ((ihφ ρ hρ).2 ρ' hρ' ω hω) ((ihψ ρ hρ).2 ρ' hρ' ω hω)⟩
  | or φ ψ ihφ ihψ =>
      exact fun ρ hρ => ⟨trivial, fun ρ' hρ' ω hω =>
        biimp_sup_congr ((ihφ ρ hρ).2 ρ' hρ' ω hω) ((ihψ ρ hρ).2 ρ' hρ' ω hω)⟩
  | imp φ ψ ihφ ihψ =>
      exact fun ρ hρ => ⟨trivial, fun ρ' hρ' ω hω =>
        biimp_himp_congr ((ihφ ρ hρ).2 ρ' hρ' ω hω) ((ihψ ρ hρ).2 ρ' hρ' ω hω)⟩
  | not φ ihφ =>
      exact fun ρ hρ => ⟨trivial, fun ρ' hρ' ω hω =>
        biimp_compl_congr ((ihφ ρ hρ).2 ρ' hρ' ω hω)⟩
  | eq t u iht ihu =>
      intro ρ hρ
      refine ⟨trivial, fun ρ' hρ' ω hω => ?_⟩
      have ht := (iht ρ hρ).2 ρ' hρ' ω hω
      have hu := (ihu ρ hρ).2 ρ' hρ' ω hω
      refine le_biimp ?_ ?_
      · calc ω ⊓ Eqv H C _ ((𝕊).denote t ρ) ((𝕊).denote u ρ)
            ≤ Eqv H C _ ((𝕊).denote t ρ') ((𝕊).denote t ρ) ⊓
                Eqv H C _ ((𝕊).denote t ρ) ((𝕊).denote u ρ) ⊓
                Eqv H C _ ((𝕊).denote u ρ) ((𝕊).denote u ρ') :=
              le_inf (le_inf (inf_le_left.trans (ht.trans (eqv_symm _ _).le)) inf_le_right)
                (inf_le_left.trans hu)
          _ ≤ Eqv H C _ ((𝕊).denote t ρ') ((𝕊).denote u ρ) ⊓
                Eqv H C _ ((𝕊).denote u ρ) ((𝕊).denote u ρ') :=
              inf_le_inf_right _ (eqv_trans _ _ _)
          _ ≤ _ := eqv_trans _ _ _
      · calc ω ⊓ Eqv H C _ ((𝕊).denote t ρ') ((𝕊).denote u ρ')
            ≤ Eqv H C _ ((𝕊).denote t ρ) ((𝕊).denote t ρ') ⊓
                Eqv H C _ ((𝕊).denote t ρ') ((𝕊).denote u ρ') ⊓
                Eqv H C _ ((𝕊).denote u ρ') ((𝕊).denote u ρ) :=
              le_inf (le_inf (inf_le_left.trans ht) inf_le_right)
                (inf_le_left.trans (hu.trans (eqv_symm _ _).le))
          _ ≤ Eqv H C _ ((𝕊).denote t ρ) ((𝕊).denote u ρ') ⊓
                Eqv H C _ ((𝕊).denote u ρ') ((𝕊).denote u ρ) :=
              inf_le_inf_right _ (eqv_trans _ _ _)
          _ ≤ _ := eqv_trans _ _ _
  | all φ ihφ =>
      intro ρ hρ
      refine ⟨trivial, fun ρ' hρ' ω hω => biimp_iInf_congr fun d => ?_⟩
      refine (ihφ _ (admVal_extend hρ d.2)).2 _ (admVal_extend hρ' d.2) ω ?_
      intro σ v
      cases v with
      | vz => exact le_top.trans (eqv_refl d.2).ge
      | vs v => exact hω v
  | ex φ ihφ =>
      intro ρ hρ
      refine ⟨trivial, fun ρ' hρ' ω hω => biimp_iSup_congr fun d => ?_⟩
      refine (ihφ _ (admVal_extend hρ d.2)).2 _ (admVal_extend hρ' d.2) ω ?_
      intro σ v
      cases v with
      | vz => exact le_top.trans (eqv_refl d.2).ge
      | vs v => exact hω v

/-- Closed terms denote admissible elements. -/
theorem adm_denote_closed {τ : Ty Base} (t : ClosedTerm (Names H C) τ) :
    Adm H C τ ((𝕊).denote t (𝕊).emptyVal) :=
  (fundamental t _ admVal_empty).1

/-! ## The Heyting-valued substitutional model -/

/-- The truth value of a formula under a valuation. -/
noncomputable def truth {Γ : Ctx Base} (φ : Formula (Names H C) Γ) (ρ : (𝕊).Valuation Γ) : H :=
  (𝕊).denote φ ρ

section ModelFields

variable {σ τ : Ty Base}

theorem truth_instantiate (t : ClosedTerm (Names H C) σ) (φ : Formula (Names H C) [σ]) :
    truth (instantiate t φ) (𝕊).emptyVal =
      truth φ ((𝕊).extend (𝕊).emptyVal ((𝕊).denote t (𝕊).emptyVal)) :=
  FullTypeStructure.denote_instantiate_closed _ t φ

theorem all_le (φ : Formula (Names H C) [σ]) (t : ClosedTerm (Names H C) σ) :
    (⨅ d : {d // Adm H C σ d}, truth φ ((𝕊).extend (𝕊).emptyVal d.1)) ≤
      truth (instantiate t φ) (𝕊).emptyVal := by
  rw [truth_instantiate]
  exact iInf_le (fun d : {d // Adm H C σ d} => truth φ ((𝕊).extend (𝕊).emptyVal d.1))
    ⟨_, adm_denote_closed t⟩

theorem le_all (φ : Formula (Names H C) [σ]) (ω : H)
    (h : ∀ t : ClosedTerm (Names H C) σ, ω ≤ truth (instantiate t φ) (𝕊).emptyVal) :
    ω ≤ ⨅ d : {d // Adm H C σ d}, truth φ ((𝕊).extend (𝕊).emptyVal d.1) := by
  refine le_iInf fun d => ?_
  have hd := h (.const d)
  rw [truth_instantiate] at hd
  exact hd

theorem ex_le (φ : Formula (Names H C) [σ]) (ω : H)
    (h : ∀ t : ClosedTerm (Names H C) σ, truth (instantiate t φ) (𝕊).emptyVal ≤ ω) :
    (⨆ d : {d // Adm H C σ d}, truth φ ((𝕊).extend (𝕊).emptyVal d.1)) ≤ ω := by
  refine iSup_le fun d => ?_
  have hd := h (.const d)
  rw [truth_instantiate] at hd
  exact hd

theorem le_ex (φ : Formula (Names H C) [σ]) (t : ClosedTerm (Names H C) σ) :
    truth (instantiate t φ) (𝕊).emptyVal ≤
      ⨆ d : {d // Adm H C σ d}, truth φ ((𝕊).extend (𝕊).emptyVal d.1) := by
  rw [truth_instantiate]
  exact le_iSup (fun d : {d // Adm H C σ d} => truth φ ((𝕊).extend (𝕊).emptyVal d.1))
    ⟨_, adm_denote_closed t⟩

theorem eq_app_le (f g : ClosedTerm (Names H C) (σ ⇒ τ)) (t : ClosedTerm (Names H C) σ) :
    Eqv H C (σ ⇒ τ) ((𝕊).denote f (𝕊).emptyVal) ((𝕊).denote g (𝕊).emptyVal) ≤
      Eqv H C τ ((𝕊).denote f (𝕊).emptyVal ((𝕊).denote t (𝕊).emptyVal))
        ((𝕊).denote g (𝕊).emptyVal ((𝕊).denote t (𝕊).emptyVal)) := by
  rw [eqv_arr]
  exact iInf_le (fun d : {d // Adm H C σ d} =>
    Eqv H C τ ((𝕊).denote f (𝕊).emptyVal d.1) ((𝕊).denote g (𝕊).emptyVal d.1))
    ⟨_, adm_denote_closed t⟩

theorem eq_lam (t u : Term (Names H C) [σ] τ) (ω : H)
    (h : ∀ w : ClosedTerm (Names H C) σ,
      ω ≤ Eqv H C τ ((𝕊).denote (instantiate w t) (𝕊).emptyVal)
        ((𝕊).denote (instantiate w u) (𝕊).emptyVal)) :
    ω ≤ Eqv H C (σ ⇒ τ) ((𝕊).denote (.lam t) (𝕊).emptyVal)
      ((𝕊).denote (.lam u) (𝕊).emptyVal) := by
  rw [eqv_arr]
  refine le_iInf fun d => ?_
  have hd := h (.const d)
  rw [FullTypeStructure.denote_instantiate_closed,
    FullTypeStructure.denote_instantiate_closed] at hd
  exact hd

theorem funExt_le (f g : ClosedTerm (Names H C) (σ ⇒ τ)) :
    (⨅ d : {d // Adm H C σ d},
        Eqv H C τ
          ((𝕊).denote (weaken (σ := σ) f) ((𝕊).extend (𝕊).emptyVal d.1) d.1)
          ((𝕊).denote (weaken (σ := σ) g) ((𝕊).extend (𝕊).emptyVal d.1) d.1)) ≤
      Eqv H C (σ ⇒ τ) ((𝕊).denote f (𝕊).emptyVal) ((𝕊).denote g (𝕊).emptyVal) := by
  have hf : ∀ d : Ty.full H C σ,
      (𝕊).denote (weaken (σ := σ) f) ((𝕊).extend (𝕊).emptyVal d) d =
        (𝕊).denote f (𝕊).emptyVal d :=
    fun d => congrFun ((𝕊).denote_weaken f (𝕊).emptyVal d) d
  have hg : ∀ d : Ty.full H C σ,
      (𝕊).denote (weaken (σ := σ) g) ((𝕊).extend (𝕊).emptyVal d) d =
        (𝕊).denote g (𝕊).emptyVal d :=
    fun d => congrFun ((𝕊).denote_weaken g (𝕊).emptyVal d) d
  rw [eqv_arr]
  exact le_of_eq (iInf_congr fun d => by rw [hf d.1, hg d.1])

theorem beta_top (t : ClosedTerm (Names H C) σ) (u : Term (Names H C) [σ] τ) :
    ⊤ ≤ Eqv H C τ ((𝕊).denote (.app (.lam u) t) (𝕊).emptyVal)
      ((𝕊).denote (instantiate t u) (𝕊).emptyVal) := by
  have hβ : (𝕊).denote (.app (.lam u) t) (𝕊).emptyVal =
      (𝕊).denote (instantiate t u) (𝕊).emptyVal :=
    (FullTypeStructure.denote_instantiate_closed _ t u).symm
  rw [hβ]
  exact (eqv_refl (adm_denote_closed _)).ge

theorem eta_top (f : ClosedTerm (Names H C) (σ ⇒ τ)) :
    ⊤ ≤ Eqv H C (σ ⇒ τ)
      ((𝕊).denote (.lam (.app (weaken (σ := σ) f) (.var .vz))) (𝕊).emptyVal)
      ((𝕊).denote f (𝕊).emptyVal) := by
  have hη : (𝕊).denote (.lam (.app (weaken (σ := σ) f) (.var .vz))) (𝕊).emptyVal =
      (𝕊).denote f (𝕊).emptyVal :=
    funext fun d => congrFun ((𝕊).denote_weaken f (𝕊).emptyVal d) d
  rw [hη]
  exact (eqv_refl (adm_denote_closed _)).ge

end ModelFields

variable (H C)

/-- The frame-valued model of the signature of names, as a Heyting-valued
substitutional model. -/
noncomputable def model : HeytingSem.HeytingGeneralModel.{u, w, w} Base (Names H C) where
  Ω := H
  le := (· ≤ ·)
  le_refl := le_refl
  le_trans := le_trans
  top := ⊤
  bot := ⊥
  inf := (· ⊓ ·)
  sup := (· ⊔ ·)
  himp := (· ⇨ ·)
  le_top _ := le_top
  bot_le _ := bot_le
  inf_le_left _ _ := inf_le_left
  inf_le_right _ _ := inf_le_right
  le_inf := le_inf
  le_sup_left _ _ := le_sup_left
  le_sup_right _ _ := le_sup_right
  sup_le := sup_le
  himp_adjoint_mp h := le_himp_iff.mp h
  himp_adjoint_intro h := le_himp_iff.mpr h
  inf_sup_distrib a b c := (inf_sup_left a b c).le
  val φ := truth φ (𝕊).emptyVal
  val_top := rfl
  val_bot := rfl
  val_and _ _ := rfl
  val_or _ _ := rfl
  val_imp _ _ := rfl
  val_not_le _ := (himp_bot _).ge
  le_val_not _ := (himp_bot _).le
  val_all_le φ t := all_le φ t
  le_val_all φ ω h := le_all φ ω h
  val_ex_le φ ω h := ex_le φ ω h
  le_val_ex φ t := le_ex φ t
  val_eq_refl t := (eqv_refl (adm_denote_closed t)).ge
  val_eq_symm _ _ := (eqv_symm _ _).le
  val_eq_trans _ _ _ := eqv_trans _ _ _
  val_eq_app f g t := eq_app_le f g t
  val_eq_appArg f t u :=
    (adm_denote_closed f).2 _ _ (adm_denote_closed t) (adm_denote_closed u)
  val_eq_propI _ _ := le_rfl
  val_eq_propEL _ _ := inf_le_left
  val_eq_propER _ _ := inf_le_right
  val_eq_lam t u ω h := eq_lam t u ω h
  val_funExt f g := funExt_le f g
  val_beta t u := beta_top t u
  val_eta f := eta_top f

theorem model_val (φ : ClosedFormula (Names H C)) :
    (model H C).val φ = truth φ (typeStructure H C).emptyVal := rfl

/-- **Soundness for frame-valued models.**  A closed EM-free theorem over the
names has truth value `⊤`. -/
theorem truth_eq_top_of_derivation {φ : ClosedFormula (Names H C)}
    (d : ExtDerivation (Names H C) [] φ) :
    truth φ (typeStructure H C).emptyVal = ⊤ := by
  have h := HeytingSem.sound d (model H C) HeytingSem.emptySubst
  have hclosed : subst (HeytingSem.emptySubst (Base := Base) (Const := Names H C)) φ = φ :=
    KripkeHenkin.ClosedEnv.subst_empty (Base := Base) (Const := Names H C) _ φ
  rw [hclosed] at h
  exact top_le_iff.mp h

end FrameValued

end Mettapedia.Logic.HOL
