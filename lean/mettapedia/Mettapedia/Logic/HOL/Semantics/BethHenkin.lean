import Mettapedia.Logic.HOL.Semantics.HeytingGeneral
import Mettapedia.Logic.HOL.Semantics.ConstantDomain

/-!
# Beth semantics for the EM-free HOL calculus

A Beth structure (`BethHenkin`) has a preordered set of worlds with a covering
system, and forces closed formulas.  Domains are constant: at every world the
quantifiers at a type `σ`, including function types and `prop`, range over all
closed terms of type `σ`.  Disjunction and the existential are forced when they
are forced on a cover.

* `W ⊩ φ ∨ ψ` iff some cover of `W` consists of worlds forcing `φ` or `ψ`.
* `W ⊩ ∃x. φ` iff some cover of `W` consists of worlds each forcing an
  instance of `φ`.
* `W ⊩ ∀x. φ` iff `W` forces every instance of `φ`.
* `W ⊩ φ → ψ` iff every later world forcing `φ` forces `ψ`.
* `⊥` is forced nowhere.  Forcing is monotone, and local: a formula forced at
  every world of a cover of `W` is forced at `W`.
* Equality is a forced congruence satisfying the propositional, functional
  and lambda extensionality laws and `β`, `η`.

Covers form a Grothendieck topology on the preorder: a world covers itself,
covers may be enlarged by later worlds, they restrict along the order, and
they are transitive (`covers_local`).  In Beth's tree models the covers of a
node are its bars; this file works with arbitrary covering systems on a
preorder, and its canonical structures are not trees.

## Results

* `HeytingSem.ofBethHenkin`: a Beth structure is a Heyting-valued model over
  its monotone local sets of worlds.  Hence soundness,
  `BethHenkin.forces_of_provable`.
* `BethHenkin.ofHeyting`: a Heyting-valued model is a Beth structure.  Its
  worlds are the values not below `⊥`, ordered by reverse order; a family
  covers `a` when every upper bound of the family is above `a`; and `a`
  forces `φ` iff `a ≤ val φ` (`ofHeyting_forces`).  For a frame-valued model
  the covers of `a` are the families below `a` whose join is above `a`
  (`frameValued_covers_iff`); over the open sets of a space, open covers.
* `provable_iff_bethConsequence_param_free`: soundness and completeness for
  parameter-free theories over the parameter language.  No countability or
  inhabitation hypothesis.
* `constantDomain_not_bethConsequence`: the constant-domain sentence is not a
  Beth consequence; `realLine_not_forces_constantDomain` exhibits the Beth
  structure on the nonempty open subsets of `ℝ`, with open covers and a
  constant domain, whose top world does not force it.
* `BethHenkin.ofKripkeHenkin`: with the trivial covering system, in which a
  family covers `W` when it contains `W`, every substitutional Kripke structure
  is a Beth structure; those force the constant-domain sentence
  (`ofKripkeHenkin_forces_constantDomain`).
* `Bar`: in the tree of finite sequences, bars satisfy the covering axioms, so
  Beth's tree models are instances.  A bar is met by every infinite path.

So constant domains are compatible with completeness once disjunction and the
existential are forced on covers.  Completeness is proved through the
Lindenbaum algebra, not through a direct canonical Beth construction, and the
quantifiers range over closed terms: this is completeness for general
(Henkin-style) Beth structures, not for standard models.  Soundness uses no
choice.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL

universe u v w

/-- A substitutional Beth structure with constant domains. -/
structure BethHenkin (Base : Type u) (Const : Ty Base → Type v) where
  World : Type w
  le : World → World → Prop
  le_refl : ∀ W, le W W
  le_trans : ∀ {U V W}, le U V → le V W → le U W
  Covers : World → Set World → Prop
  covers_le : ∀ {W : World} {B : Set World}, Covers W B → ∀ V ∈ B, le W V
  covers_self : ∀ W, Covers W {W}
  covers_mono : ∀ {W : World} {B B' : Set World},
    Covers W B → B ⊆ B' → (∀ V ∈ B', le W V) → Covers W B'
  covers_restrict : ∀ {W V : World} {B : Set World}, Covers W B → le W V →
    Covers V {U | le V U ∧ ∃ U' ∈ B, le U' U}
  covers_local : ∀ {W : World} {B R : Set World}, Covers W B →
    (∀ V ∈ B, Covers V {U | le V U ∧ U ∈ R}) → Covers W {U | le W U ∧ U ∈ R}
  forces : World → ClosedFormula Const → Prop
  forces_mono : ∀ {U V : World} {φ : ClosedFormula Const}, le U V → forces U φ → forces V φ
  forces_local : ∀ {W : World} {B : Set World} {φ : ClosedFormula Const},
    Covers W B → (∀ V ∈ B, forces V φ) → forces W φ
  forces_top : ∀ {W : World}, forces W (.top : ClosedFormula Const)
  forces_bot : ∀ {W : World}, ¬ forces W (.bot : ClosedFormula Const)
  forces_and : ∀ {W : World} {φ ψ : ClosedFormula Const},
    forces W (.and φ ψ) ↔ forces W φ ∧ forces W ψ
  forces_or : ∀ {W : World} {φ ψ : ClosedFormula Const},
    forces W (.or φ ψ) ↔ ∃ B, Covers W B ∧ ∀ V ∈ B, forces V φ ∨ forces V ψ
  forces_imp : ∀ {W : World} {φ ψ : ClosedFormula Const},
    forces W (.imp φ ψ) ↔ ∀ V, le W V → forces V φ → forces V ψ
  forces_not : ∀ {W : World} {φ : ClosedFormula Const},
    forces W (.not φ) ↔ ∀ V, le W V → ¬ forces V φ
  forces_all : ∀ {W : World} {σ : Ty Base} {φ : Formula Const [σ]},
    forces W (.all φ) ↔ ∀ t : ClosedTerm Const σ, forces W (instantiate (Base := Base) t φ)
  forces_ex : ∀ {W : World} {σ : Ty Base} {φ : Formula Const [σ]},
    forces W (.ex φ) ↔ ∃ B, Covers W B ∧
      ∀ V ∈ B, ∃ t : ClosedTerm Const σ, forces V (instantiate (Base := Base) t φ)
  forces_eq_refl : ∀ {W : World} {τ : Ty Base} (t : ClosedTerm Const τ), forces W (.eq t t)
  forces_eq_symm : ∀ {W : World} {τ : Ty Base} {t u : ClosedTerm Const τ},
    forces W (.eq t u) → forces W (.eq u t)
  forces_eq_trans : ∀ {W : World} {τ : Ty Base} {t u r : ClosedTerm Const τ},
    forces W (.eq t u) → forces W (.eq u r) → forces W (.eq t r)
  forces_eq_app : ∀ {W : World} {σ τ : Ty Base} {f g : ClosedTerm Const (σ ⇒ τ)}
    (t : ClosedTerm Const σ), forces W (.eq f g) → forces W (.eq (.app f t) (.app g t))
  forces_eq_appArg : ∀ {W : World} {σ τ : Ty Base} (f : ClosedTerm Const (σ ⇒ τ))
    {t u : ClosedTerm Const σ}, forces W (.eq t u) → forces W (.eq (.app f t) (.app f u))
  forces_eq_propI : ∀ {W : World} {p q : ClosedFormula Const},
    forces W (.imp p q) → forces W (.imp q p) → forces W (.eq p q)
  forces_eq_propEL : ∀ {W : World} {p q : ClosedFormula Const},
    forces W (.eq p q) → forces W (.imp p q)
  forces_eq_propER : ∀ {W : World} {p q : ClosedFormula Const},
    forces W (.eq p q) → forces W (.imp q p)
  forces_eq_lam : ∀ {W : World} {σ τ : Ty Base} {t u : Term Const [σ] τ},
    (∀ r : ClosedTerm Const σ,
      forces W (.eq (instantiate (Base := Base) r t) (instantiate (Base := Base) r u))) →
      forces W (.eq (.lam t) (.lam u))
  forces_funExt : ∀ {W : World} {σ τ : Ty Base} {f g : ClosedTerm Const (σ ⇒ τ)},
    forces W (.all (.eq (.app (weaken (Base := Base) (σ := σ) f) (.var .vz))
      (.app (weaken (Base := Base) (σ := σ) g) (.var .vz)))) → forces W (.eq f g)
  forces_eq_beta : ∀ {W : World} {σ τ : Ty Base} (t : ClosedTerm Const σ)
    (u : Term Const [σ] τ), forces W (.eq (.app (.lam u) t) (instantiate (Base := Base) t u))
  forces_eq_eta : ∀ {W : World} {σ τ : Ty Base} (f : ClosedTerm Const (σ ⇒ τ)),
    forces W (.eq (.lam (.app (weaken (Base := Base) (σ := σ) f) (.var .vz))) f)

namespace HeytingSem

variable {Base : Type u} {Const : Ty Base → Type v}

/-- The Heyting-valued model of a Beth structure: its monotone local sets of
worlds, with forcing as valuation. -/
def ofBethHenkin (B : BethHenkin.{u, v, w} Base Const) :
    HeytingGeneralModel.{u, v, w} Base Const where
  Ω := {S : B.World → Prop // (∀ {U V : B.World}, B.le U V → S U → S V) ∧
    ∀ {W : B.World} {C : Set B.World}, B.Covers W C → (∀ V ∈ C, S V) → S W}
  le S T := ∀ W, S.1 W → T.1 W
  le_refl _ := fun _ h => h
  le_trans h₁ h₂ := fun W h => h₂ W (h₁ W h)
  top := ⟨fun _ => True, fun _ _ => trivial, fun _ _ => trivial⟩
  bot := ⟨fun _ => False, fun _ h => h,
    fun hC h => B.forces_bot (B.forces_local hC fun V hV => (h V hV).elim)⟩
  inf S T := ⟨fun W => S.1 W ∧ T.1 W, fun hUV h => ⟨S.2.1 hUV h.1, T.2.1 hUV h.2⟩,
    fun hC h => ⟨S.2.2 hC fun V hV => (h V hV).1, T.2.2 hC fun V hV => (h V hV).2⟩⟩
  sup S T := ⟨fun W => ∃ C, B.Covers W C ∧ ∀ V ∈ C, S.1 V ∨ T.1 V,
    fun hUV h => by
      obtain ⟨C, hC, hST⟩ := h
      refine ⟨_, B.covers_restrict hC hUV, fun X hX => ?_⟩
      obtain ⟨_, Y, hY, hYX⟩ := hX
      exact (hST Y hY).elim (fun hs => Or.inl (S.2.1 hYX hs)) (fun ht => Or.inr (T.2.1 hYX ht)),
    fun {W C} hC h => by
      refine ⟨_, B.covers_local (R := {X | S.1 X ∨ T.1 X}) hC fun V hV => ?_, fun X hX => hX.2⟩
      obtain ⟨D, hD, hDST⟩ := h V hV
      exact B.covers_mono hD (fun X hX => ⟨B.covers_le hD X hX, hDST X hX⟩) fun X hX => hX.1⟩
  himp S T := ⟨fun W => ∀ V, B.le W V → S.1 V → T.1 V,
    fun hUV h V hV hs => h V (B.le_trans hUV hV) hs,
    fun {W C} hC h V hWV hs => T.2.2 (B.covers_restrict hC hWV) fun X hX => by
      obtain ⟨hVX, Y, hY, hYX⟩ := hX
      exact h Y hY X hYX (S.2.1 hVX hs)⟩
  le_top _ := fun _ _ => trivial
  bot_le _ := fun _ h => h.elim
  inf_le_left _ _ := fun _ h => h.1
  inf_le_right _ _ := fun _ h => h.2
  le_inf h₁ h₂ := fun W h => ⟨h₁ W h, h₂ W h⟩
  le_sup_left _ _ := fun W h =>
    ⟨{W}, B.covers_self W, fun V hV => Or.inl (by rw [Set.mem_singleton_iff.mp hV]; exact h)⟩
  le_sup_right _ _ := fun W h =>
    ⟨{W}, B.covers_self W, fun V hV => Or.inr (by rw [Set.mem_singleton_iff.mp hV]; exact h)⟩
  sup_le {_ _ c} h₁ h₂ := fun _ h => by
    obtain ⟨C, hC, hST⟩ := h
    exact c.2.2 hC fun V hV => (hST V hV).elim (h₁ V) (h₂ V)
  himp_adjoint_mp h := fun W hab => h W hab.1 W (B.le_refl W) hab.2
  himp_adjoint_intro {a _ _} h := fun _ ha V hV hb => h V ⟨a.2.1 hV ha, hb⟩
  inf_sup_distrib a _ _ := fun _ h => by
    obtain ⟨ha, C, hC, hbc⟩ := h
    exact ⟨C, hC, fun V hV => (hbc V hV).elim
      (fun hb => Or.inl ⟨a.2.1 (B.covers_le hC V hV) ha, hb⟩)
      (fun hc => Or.inr ⟨a.2.1 (B.covers_le hC V hV) ha, hc⟩)⟩
  val φ := ⟨fun W => B.forces W φ, B.forces_mono, B.forces_local⟩
  val_top := Subtype.ext (funext fun _ => propext ⟨fun _ => trivial, fun _ => B.forces_top⟩)
  val_bot := Subtype.ext (funext fun _ => propext ⟨fun h => B.forces_bot h, False.elim⟩)
  val_and _ _ := Subtype.ext (funext fun _ => propext B.forces_and)
  val_or _ _ := Subtype.ext (funext fun _ => propext B.forces_or)
  val_imp _ _ := Subtype.ext (funext fun _ => propext B.forces_imp)
  val_not_le _ := fun _ h => B.forces_not.mp h
  le_val_not _ := fun _ h => B.forces_not.mpr h
  val_all_le _ t := fun _ h => B.forces_all.mp h t
  le_val_all _ _ h := fun W hω => B.forces_all.mpr fun t => h t W hω
  val_ex_le _ ω h := fun _ hex => by
    obtain ⟨C, hC, hV⟩ := B.forces_ex.mp hex
    exact ω.2.2 hC fun V hVC => by
      obtain ⟨t, ht⟩ := hV V hVC
      exact h t V ht
  le_val_ex _ t := fun W h => B.forces_ex.mpr
    ⟨{W}, B.covers_self W, fun V hV => ⟨t, by rw [Set.mem_singleton_iff.mp hV]; exact h⟩⟩
  val_eq_refl t := fun _ _ => B.forces_eq_refl t
  val_eq_symm _ _ := fun _ h => B.forces_eq_symm h
  val_eq_trans _ _ _ := fun _ h => B.forces_eq_trans h.1 h.2
  val_eq_app _ _ t := fun _ h => B.forces_eq_app t h
  val_eq_appArg f _ _ := fun _ h => B.forces_eq_appArg f h
  val_eq_propI _ _ := fun _ h => B.forces_eq_propI h.1 h.2
  val_eq_propEL _ _ := fun _ h => B.forces_eq_propEL h
  val_eq_propER _ _ := fun _ h => B.forces_eq_propER h
  val_eq_lam _ _ _ h := fun W hω => B.forces_eq_lam fun r => h r W hω
  val_funExt _ _ := fun _ h => B.forces_funExt h
  val_beta t u := fun _ _ => B.forces_eq_beta t u
  val_eta f := fun _ _ => B.forces_eq_eta f

end HeytingSem

namespace BethHenkin

variable {Base : Type u} {Const : Ty Base → Type v}

/-! ## Soundness -/

theorem hypVal_ofBethHenkin (B : BethHenkin.{u, v, w} Base Const) {W : B.World} :
    ∀ {Δ : List (ClosedFormula Const)}, (∀ ψ ∈ Δ, B.forces W ψ) →
      ((HeytingSem.ofBethHenkin B).hypVal Δ).1 W
  | [], _ => trivial
  | ψ :: _, h => ⟨h ψ List.mem_cons_self,
      hypVal_ofBethHenkin B fun χ hχ => h χ (List.mem_cons_of_mem _ hχ)⟩

/-- **Soundness of the Beth semantics**: a world forcing a theory forces what
the theory proves. -/
theorem forces_of_provable (B : BethHenkin.{u, v, w} Base Const)
    {T : ClosedTheorySet Const} {θ : ClosedFormula Const}
    (h : ClosedTheorySet.Provable (Const := Const) T θ) {W : B.World}
    (hW : ∀ ψ ∈ T, B.forces W ψ) : B.forces W θ := by
  obtain ⟨Γ, hΓ, d⟩ := h
  have hclosed : ∀ ψ : ClosedFormula Const,
      subst (HeytingSem.emptySubst (Base := Base) (Const := Const)) ψ = ψ := fun ψ =>
    KripkeHenkin.ClosedEnv.subst_empty (Base := Base) (Const := Const) _ ψ
  have hs := HeytingSem.sound d (HeytingSem.ofBethHenkin B) HeytingSem.emptySubst
  rw [hclosed θ] at hs
  refine hs W (hypVal_ofBethHenkin B ?_)
  intro ψ hψ
  obtain ⟨χ, hχ, rfl⟩ := List.mem_map.mp hψ
  rw [hclosed χ]
  exact hW χ (hΓ χ hχ)

/-! ## Heyting-valued models as Beth structures -/

/-- Below a least upper bound `x` of `S`, a value `a` lies below every bound of
the values not below `⊥` that lie below `a` and below a member of `S`.  This
is why such values cover `a`. -/
theorem le_of_le_lub (M : HeytingSem.HeytingGeneralModel.{u, v, w} Base Const)
    {S : Set M.Ω} {x : M.Ω} (hlub : ∀ c, (∀ s ∈ S, M.le s c) → M.le x c)
    {a : M.Ω} (ha : M.le a x) (c : M.Ω)
    (hc : ∀ b : {a : M.Ω // ¬ M.le a M.bot}, M.le b.1 a → (∃ s ∈ S, M.le b.1 s) → M.le b.1 c) :
    M.le a c := by
  classical
  have hs : ∀ s ∈ S, M.le s (M.himp a c) := by
    intro s hs
    refine M.himp_adjoint_intro (M.le_trans (M.inf_comm_le _ _) ?_)
    by_cases hbot : M.le (M.inf a s) M.bot
    · exact M.le_trans hbot (M.bot_le c)
    · exact hc ⟨_, hbot⟩ (M.inf_le_left _ _) ⟨s, hs, M.inf_le_right _ _⟩
  exact M.le_trans (M.le_inf (M.le_refl _) (M.le_refl _))
    (M.himp_adjoint_mp (M.le_trans ha (hlub _ hs)))

/-- The Beth structure of a Heyting-valued model.  Worlds are the values not
below `⊥`, later worlds are smaller values, a family covers `a` when every
upper bound of the family is above `a`, and `a` forces `φ` when
`a ≤ val φ`. -/
def ofHeyting (M : HeytingSem.HeytingGeneralModel.{u, v, w} Base Const) :
    BethHenkin.{u, v, w} Base Const where
  World := {a : M.Ω // ¬ M.le a M.bot}
  le a b := M.le b.1 a.1
  le_refl a := M.le_refl a.1
  le_trans h₁ h₂ := M.le_trans h₂ h₁
  Covers a C := (∀ b ∈ C, M.le b.1 a.1) ∧ ∀ c : M.Ω, (∀ b ∈ C, M.le b.1 c) → M.le a.1 c
  covers_le h := h.1
  covers_self a :=
    ⟨fun b hb => by rw [Set.mem_singleton_iff.mp hb]; exact M.le_refl _,
      fun _ h => h a rfl⟩
  covers_mono hC hsub hle := ⟨hle, fun c h => hC.2 c fun b hb => h b (hsub hb)⟩
  covers_restrict {a b C} hC hab := by
    classical
    refine ⟨fun x hx => hx.1, fun c h => ?_⟩
    have hx : ∀ x ∈ C, M.le x.1 (M.himp b.1 c) := by
      intro x hx
      refine M.himp_adjoint_intro ?_
      by_cases hbot : M.le (M.inf x.1 b.1) M.bot
      · exact M.le_trans hbot (M.bot_le c)
      · exact h ⟨M.inf x.1 b.1, hbot⟩ ⟨M.inf_le_right _ _, x, hx, M.inf_le_left _ _⟩
    have hab' : M.le b.1 (M.himp b.1 c) := M.le_trans hab (hC.2 _ hx)
    exact M.le_trans (M.le_inf (M.le_refl _) (M.le_refl _)) (M.himp_adjoint_mp hab')
  covers_local {a C R} hC h := ⟨fun _ hU => hU.1, fun c hc => hC.2 c fun b hb =>
    (h b hb).2 c fun U hU => hc U ⟨M.le_trans hU.1 (hC.1 b hb), hU.2⟩⟩
  forces a φ := M.le a.1 (M.val φ)
  forces_mono h hφ := M.le_trans h hφ
  forces_local hC h := hC.2 _ h
  forces_top := by
    intro a
    show M.le a.1 (M.val .top)
    rw [M.val_top]
    exact M.le_top _
  forces_bot := by
    intro a h
    change M.le a.1 (M.val .bot) at h
    rw [M.val_bot] at h
    exact a.2 h
  forces_and := by
    intro a φ ψ
    show M.le a.1 (M.val (.and φ ψ)) ↔ M.le a.1 (M.val φ) ∧ M.le a.1 (M.val ψ)
    rw [M.val_and]
    exact ⟨fun h => ⟨M.le_trans h (M.inf_le_left _ _), M.le_trans h (M.inf_le_right _ _)⟩,
      fun h => M.le_inf h.1 h.2⟩
  forces_or := by
    classical
    intro a φ ψ
    show M.le a.1 (M.val (.or φ ψ)) ↔ ∃ C : Set {a : M.Ω // ¬ M.le a M.bot},
      ((∀ b ∈ C, M.le b.1 a.1) ∧ ∀ c : M.Ω, (∀ b ∈ C, M.le b.1 c) → M.le a.1 c) ∧
        ∀ V ∈ C, M.le V.1 (M.val φ) ∨ M.le V.1 (M.val ψ)
    rw [M.val_or]
    constructor
    · intro h
      refine ⟨{V | M.le V.1 a.1 ∧ (M.le V.1 (M.val φ) ∨ M.le V.1 (M.val ψ))},
        ⟨fun b hb => hb.1, fun c hc => ?_⟩, fun V hV => hV.2⟩
      refine le_of_le_lub M (S := {M.val φ, M.val ψ})
        (fun c hc => M.sup_le (hc _ (Set.mem_insert _ _)) (hc _ (Set.mem_insert_of_mem _ rfl)))
        h c fun b hb hbs => hc b ⟨hb, ?_⟩
      obtain ⟨s, hs, hbs⟩ := hbs
      rcases hs with rfl | rfl
      · exact Or.inl hbs
      · exact Or.inr hbs
    · rintro ⟨C, hC, h⟩
      exact hC.2 _ fun V hV => (h V hV).elim
        (fun h' => M.le_trans h' (M.le_sup_left _ _))
        (fun h' => M.le_trans h' (M.le_sup_right _ _))
  forces_imp := by
    classical
    intro a φ ψ
    show M.le a.1 (M.val (.imp φ ψ)) ↔
      ∀ V : {a : M.Ω // ¬ M.le a M.bot}, M.le V.1 a.1 → M.le V.1 (M.val φ) → M.le V.1 (M.val ψ)
    rw [M.val_imp]
    constructor
    · intro h V hVa hVφ
      exact M.le_trans (M.le_inf (M.le_refl _) hVφ)
        (M.himp_adjoint_mp (M.le_trans hVa h))
    · intro h
      refine M.himp_adjoint_intro ?_
      by_cases hbot : M.le (M.inf a.1 (M.val φ)) M.bot
      · exact M.le_trans hbot (M.bot_le _)
      · exact h ⟨M.inf a.1 (M.val φ), hbot⟩ (M.inf_le_left _ _) (M.inf_le_right _ _)
  forces_not := by
    classical
    intro a φ
    show M.le a.1 (M.val (.not φ)) ↔
      ∀ V : {a : M.Ω // ¬ M.le a M.bot}, M.le V.1 a.1 → ¬ M.le V.1 (M.val φ)
    constructor
    · intro h V hVa hVφ
      exact V.2 (M.le_trans (M.le_inf (M.le_refl _) hVφ)
        (M.himp_adjoint_mp (M.le_trans hVa (M.le_trans h (M.val_not_le φ)))))
    · intro h
      refine M.le_trans (M.himp_adjoint_intro ?_) (M.le_val_not φ)
      by_contra hbot
      exact h ⟨M.inf a.1 (M.val φ), hbot⟩ (M.inf_le_left _ _) (M.inf_le_right _ _)
  forces_all := by
    intro a σ φ
    exact ⟨fun h t => M.le_trans h (M.val_all_le φ t), fun h => M.le_val_all φ a.1 h⟩
  forces_ex := by
    classical
    intro a σ φ
    show M.le a.1 (M.val (.ex φ)) ↔ ∃ C : Set {a : M.Ω // ¬ M.le a M.bot},
      ((∀ b ∈ C, M.le b.1 a.1) ∧ ∀ c : M.Ω, (∀ b ∈ C, M.le b.1 c) → M.le a.1 c) ∧
        ∀ V ∈ C, ∃ t : ClosedTerm Const σ, M.le V.1 (M.val (instantiate (Base := Base) t φ))
    constructor
    · intro h
      refine ⟨{V | M.le V.1 a.1 ∧
          ∃ t : ClosedTerm Const σ, M.le V.1 (M.val (instantiate (Base := Base) t φ))},
        ⟨fun b hb => hb.1, fun c hc => ?_⟩, fun V hV => hV.2⟩
      refine le_of_le_lub M (S := Set.range fun t => M.val (instantiate (Base := Base) t φ))
        (fun c hc => M.val_ex_le φ c fun t => hc _ ⟨t, rfl⟩) h c fun b hb hbs => ?_
      obtain ⟨_, ⟨t, rfl⟩, hbt⟩ := hbs
      exact hc b ⟨hb, t, hbt⟩
    · rintro ⟨C, hC, h⟩
      refine hC.2 _ fun V hV => ?_
      obtain ⟨t, ht⟩ := h V hV
      exact M.le_trans ht (M.le_val_ex φ t)
  forces_eq_refl t := M.le_trans (M.le_top _) (M.val_eq_refl t)
  forces_eq_symm h := M.le_trans h (M.val_eq_symm _ _)
  forces_eq_trans h₁ h₂ := M.le_trans (M.le_inf h₁ h₂) (M.val_eq_trans _ _ _)
  forces_eq_app t h := M.le_trans h (M.val_eq_app _ _ t)
  forces_eq_appArg := fun {_} {_ _} f {t u} h => M.le_trans h (M.val_eq_appArg f t u)
  forces_eq_propI h₁ h₂ := M.le_trans (M.le_inf h₁ h₂) (M.val_eq_propI _ _)
  forces_eq_propEL h := M.le_trans h (M.val_eq_propEL _ _)
  forces_eq_propER h := M.le_trans h (M.val_eq_propER _ _)
  forces_eq_lam := fun h => M.val_eq_lam _ _ _ h
  forces_funExt h := M.le_trans h (M.val_funExt _ _)
  forces_eq_beta t u := M.le_trans (M.le_top _) (M.val_beta t u)
  forces_eq_eta f := M.le_trans (M.le_top _) (M.val_eta f)

theorem ofHeyting_forces (M : HeytingSem.HeytingGeneralModel.{u, v, w} Base Const)
    (a : (ofHeyting M).World) (φ : ClosedFormula Const) :
    (ofHeyting M).forces a φ ↔ M.le a.1 (M.val φ) := Iff.rfl

/-- For a frame-valued model, a family covers `a` exactly when it lies below
`a` and its join is above `a`: over the open sets of a space, the covers are
the open covers. -/
theorem frameValued_covers_iff {H : Type w} [Order.Frame H] {C : Base → Type w}
    (a : (ofHeyting (FrameValued.model H C)).World) (S : Set (ofHeyting (FrameValued.model H C)).World) :
    (ofHeyting (FrameValued.model H C)).Covers a S ↔
      (∀ b ∈ S, @id H b.1 ≤ @id H a.1) ∧ @id H a.1 ≤ sSup ((fun b => @id H b.1) '' S) := by
  constructor
  · rintro ⟨hS, hJ⟩
    exact ⟨hS, hJ _ fun b hb => le_sSup ⟨b, hb, rfl⟩⟩
  · rintro ⟨hS, hJ⟩
    refine ⟨hS, fun c hc => hJ.trans (sSup_le ?_)⟩
    rintro _ ⟨b, hb, rfl⟩
    exact hc b hb

/-! ## Kripke structures as Beth structures -/

/-- A substitutional Kripke structure is a Beth structure for the trivial
covering system, in which a family covers `W` when it contains `W`. -/
def ofKripkeHenkin (K : KripkeHenkin.{u, v, w} Base Const) : BethHenkin.{u, v, w} Base Const where
  World := K.World
  le := K.le
  le_refl := K.le_refl
  le_trans := K.le_trans
  Covers W B := W ∈ B ∧ ∀ V ∈ B, K.le W V
  covers_le h := h.2
  covers_self W :=
    ⟨Set.mem_singleton W, fun V hV => by rw [Set.mem_singleton_iff.mp hV]; exact K.le_refl W⟩
  covers_mono hC hsub hle := ⟨hsub hC.1, hle⟩
  covers_restrict {W V _} hC hWV := ⟨⟨K.le_refl V, W, hC.1, hWV⟩, fun _ hU => hU.1⟩
  covers_local {W _ _} hC h := ⟨⟨K.le_refl W, (h W hC.1).1.2⟩, fun _ hU => hU.1⟩
  forces := K.forces
  forces_mono := K.forces_mono
  forces_local hC h := h _ hC.1
  forces_top := K.forces_top
  forces_bot := K.forces_bot
  forces_and := K.forces_and
  forces_or := by
    intro W φ ψ
    constructor
    · intro h
      refine ⟨{W}, ⟨Set.mem_singleton W, fun V hV => ?_⟩, fun V hV => ?_⟩
      · rw [Set.mem_singleton_iff.mp hV]; exact K.le_refl W
      · rw [Set.mem_singleton_iff.mp hV]; exact K.forces_or.mp h
    · rintro ⟨_, hB, h⟩
      exact K.forces_or.mpr (h W hB.1)
  forces_imp := K.forces_imp
  forces_not := K.forces_not
  forces_all := by
    intro W σ φ
    exact ⟨fun h t => K.forces_all.mp h W (K.le_refl W) t,
      fun h => K.forces_all.mpr fun V hV t => K.forces_mono hV (h t)⟩
  forces_ex := by
    intro W σ φ
    constructor
    · intro h
      obtain ⟨t, ht⟩ := K.forces_ex.mp h
      refine ⟨{W}, ⟨Set.mem_singleton W, fun V hV => ?_⟩, fun V hV => ⟨t, ?_⟩⟩
      · rw [Set.mem_singleton_iff.mp hV]; exact K.le_refl W
      · rw [Set.mem_singleton_iff.mp hV]; exact ht W (K.le_refl W)
    · rintro ⟨_, hB, h⟩
      obtain ⟨t, ht⟩ := h W hB.1
      exact K.forces_ex.mpr ⟨t, fun V hV => K.forces_mono hV ht⟩
  forces_eq_refl t := K.forces_eq.mpr (K.eq_refl _ t)
  forces_eq_symm h := K.forces_eq.mpr (K.eq_symm (K.forces_eq.mp h))
  forces_eq_trans h₁ h₂ := K.forces_eq.mpr (K.eq_trans (K.forces_eq.mp h₁) (K.forces_eq.mp h₂))
  forces_eq_app t h := K.forces_eq.mpr (K.eq_app_congr (K.forces_eq.mp h) (K.eq_refl _ t))
  forces_eq_appArg := fun {W} {_ _} f {_ _} h =>
    K.forces_eq.mpr (K.eq_app_congr (K.eq_refl W f) (K.forces_eq.mp h))
  forces_eq_propI h₁ h₂ := K.forces_eq.mpr (K.eq_prop_intro h₁ h₂)
  forces_eq_propEL h := K.eq_prop_elim_left (K.forces_eq.mp h)
  forces_eq_propER h := K.eq_prop_elim_right (K.forces_eq.mp h)
  forces_eq_lam := fun {W} {_ _} {t u} h => K.forces_eq.mpr (K.eq_funext fun r =>
    K.eq_trans (K.eq_beta (W := W) r t)
      (K.eq_trans (K.forces_eq.mp (h r)) (K.eq_symm (K.eq_beta (W := W) r u))))
  forces_funExt := fun {W} {_ _} {f g} h => (HeytingSem.ofKripkeHenkin K).val_funExt f g W h
  forces_eq_beta t u := K.forces_eq.mpr (K.eq_beta t u)
  forces_eq_eta f := K.forces_eq.mpr (K.eq_eta f)

/-- Negative instance: Beth structures with trivial covers force the
constant-domain sentence. -/
theorem ofKripkeHenkin_forces_constantDomain (K : KripkeHenkin.{u, v, w} Base Const)
    (W : (ofKripkeHenkin K).World) (σ : Ty Base) :
    (ofKripkeHenkin K).forces W (constantDomain σ) :=
  KripkeHenkin.forces_constantDomain K W σ

/-! ## Bars of a tree

In Beth's tree models a node is covered by its bars.  In the tree of finite
sequences over `α`, ordered by prefix, a bar of `s` is a set of extensions of
`s` that every infinite path through `s` meets.  Bars satisfy the covering
axioms of `BethHenkin` (`Bar.isBar_self`, `Bar.IsBar.mono`,
`Bar.IsBar.restrict`, `Bar.IsBar.trans`), so tree models with bars are Beth
structures.  The cover clauses for disjunction and the existential quantify
over all paths: along every path the disjunction or the instance is eventually
forced. -/

namespace Bar

variable {α : Type*}

/-- The first `n` entries of an infinite path. -/
def pref (p : ℕ → α) (n : ℕ) : List α := List.ofFn fun i : Fin n => p i

/-- An infinite path passes through a node when the node is one of its
prefixes. -/
def Through (p : ℕ → α) (s : List α) : Prop := ∀ i (h : i < s.length), s[i] = p i

/-- A bar of `s`: extensions of `s` such that every infinite path through `s`
passes through one of them. -/
def IsBar (s : List α) (B : Set (List α)) : Prop :=
  (∀ t ∈ B, s <+: t) ∧ ∀ p : ℕ → α, Through p s → ∃ t ∈ B, Through p t

theorem through_pref (p : ℕ → α) (n : ℕ) : Through p (pref p n) := by
  intro i h
  simp [pref]

theorem Through.of_prefix {p : ℕ → α} {s t : List α} (hst : s <+: t) (ht : Through p t) :
    Through p s := by
  intro i h
  rw [hst.getElem h]
  exact ht i _

theorem prefix_of_through {p : ℕ → α} {s t : List α} (hs : Through p s) (ht : Through p t)
    (hlen : s.length ≤ t.length) : s <+: t := by
  rw [List.prefix_iff_eq_take]
  refine List.ext_getElem (by simp [hlen]) fun i h₁ h₂ => ?_
  rw [List.getElem_take, hs i h₁, ht i (by omega)]

theorem isBar_self (s : List α) : IsBar s {s} :=
  ⟨fun _ ht => (Set.mem_singleton_iff.mp ht) ▸ List.prefix_refl s,
    fun _ hp => ⟨s, rfl, hp⟩⟩

theorem IsBar.mono {s : List α} {B B' : Set (List α)} (h : IsBar s B) (hsub : B ⊆ B')
    (hle : ∀ t ∈ B', s <+: t) : IsBar s B' :=
  ⟨hle, fun p hp => by
    obtain ⟨t, ht, hpt⟩ := h.2 p hp
    exact ⟨t, hsub ht, hpt⟩⟩

theorem IsBar.restrict {s t : List α} {B : Set (List α)} (h : IsBar s B) (hst : s <+: t) :
    IsBar t {u | t <+: u ∧ ∃ u' ∈ B, u' <+: u} := by
  refine ⟨fun u hu => hu.1, fun p hp => ?_⟩
  obtain ⟨u', hu', hpu'⟩ := h.2 p (hp.of_prefix hst)
  refine ⟨pref p (max t.length u'.length),
    ⟨prefix_of_through hp (through_pref p _) (by simp [pref]),
      u', hu', prefix_of_through hpu' (through_pref p _) (by simp [pref])⟩,
    through_pref p _⟩

theorem IsBar.trans {s : List α} {B R : Set (List α)} (h : IsBar s B)
    (hB : ∀ b ∈ B, IsBar b {u | b <+: u ∧ u ∈ R}) : IsBar s {u | s <+: u ∧ u ∈ R} := by
  refine ⟨fun u hu => hu.1, fun p hp => ?_⟩
  obtain ⟨b, hb, hpb⟩ := h.2 p hp
  obtain ⟨u, hu, hpu⟩ := (hB b hb).2 p hpb
  exact ⟨u, ⟨(h.1 b hb).trans hu.1, hu.2⟩, hpu⟩

/-- A schedule serves `x` infinitely often iff, from every node of the tree over
an inhabited alphabet, the extensions past a time serving `x` form a bar.  The
fairness required of the Henkin schedulers is the condition that on every path,
from every point, service eventually happens. -/
theorem infinitelyOften_iff_isBar [Inhabited α] {β : Type*} (serve : ℕ → β) (x : β) :
    (∀ N, ∃ n, N ≤ n ∧ serve n = x) ↔
      ∀ s : List α, IsBar s {t | s <+: t ∧ ∃ n, s.length ≤ n ∧ n < t.length ∧ serve n = x} := by
  constructor
  · intro h s
    obtain ⟨n, hn, hx⟩ := h s.length
    refine ⟨fun t ht => ht.1, fun p hp => ⟨pref p (n + 1), ⟨prefix_of_through hp
      (through_pref p _) (by simp [pref]; omega), n, hn, by simp [pref], hx⟩, through_pref p _⟩⟩
  · intro h N
    obtain ⟨_, ⟨_, n, hn, _, hx⟩, _⟩ :=
      (h (List.replicate N default)).2 (fun _ => default) fun i hi => by simp
    exact ⟨n, by simpa using hn, hx⟩

/-- Positive instance: the two one-step extensions bar the root of the binary
tree. -/
theorem isBar_root_bool : IsBar ([] : List Bool) {[false], [true]} := by
  refine ⟨fun t _ => List.nil_prefix, fun p _ => ?_⟩
  cases hp : p 0 with
  | false => exact ⟨[false], Or.inl rfl, fun i h => by
      have hi : i = 0 := by simpa using h
      subst hi; exact hp.symm⟩
  | true => exact ⟨[true], Or.inr rfl, fun i h => by
      have hi : i = 0 := by simpa using h
      subst hi; exact hp.symm⟩

/-- Negative instance: one extension does not bar the root; the constantly
`false` path avoids it. -/
theorem not_isBar_root_true : ¬ IsBar ([] : List Bool) {[true]} := by
  rintro ⟨-, h⟩
  obtain ⟨t, ht, hpt⟩ := h (fun _ => false) fun i h => absurd h (Nat.not_lt_zero i)
  rw [Set.mem_singleton_iff.mp ht] at hpt
  exact Bool.noConfusion (hpt 0 (Nat.zero_lt_one))

end Bar

end BethHenkin

/-! ## Completeness -/

/-- Consequence over all Beth structures: every world forcing the theory forces
the conclusion. -/
def BethConsequence {Base : Type u} {Const : Ty Base → Type v}
    (T : ClosedTheorySet Const) (θ : ClosedFormula Const) : Prop :=
  ∀ (B : BethHenkin.{u, v, max u v} Base Const) (W : B.World),
    (∀ ψ ∈ T, B.forces W ψ) → B.forces W θ

section Completeness

variable {Base : Type u} {Const : Ty Base → Type v}

open Mettapedia.Logic.HOL.WithParams

theorem bethConsequence_of_provable {T : ClosedTheorySet Const} {θ : ClosedFormula Const}
    (h : ClosedTheorySet.Provable (Const := Const) T θ) : BethConsequence T θ :=
  fun B _ hW => B.forces_of_provable h hW

/-- **Completeness of the Beth semantics** for parameter-free theories over the
parameter language. -/
theorem provable_of_bethConsequence_param_free
    {T : ClosedTheorySet (WithParams Const)} {θ : ClosedFormula (WithParams Const)}
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) ψ)
    (hSem : BethConsequence (Base := Base) T θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ := by
  classical
  let L := HeytingSem.Lindenbaum.lindenbaumModel (Base := Base) T hT0
  have hTop : L.le L.top (L.val θ) := by
    by_cases hbot : L.le L.top L.bot
    · exact L.le_trans hbot (L.bot_le _)
    · exact hSem (BethHenkin.ofHeyting L) ⟨L.top, hbot⟩ fun ψ hψ =>
        HeytingSem.Lindenbaum.provable_mono (Set.subset_insert _ _)
          (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hψ)
  exact HeytingSem.Lindenbaum.provable_cut hTop
    (ClosedTheorySet.provable_top (Const := WithParams Const) T)

/-- **Soundness and completeness of the Beth semantics** for parameter-free
theories over the parameter language. -/
theorem provable_iff_bethConsequence_param_free
    {T : ClosedTheorySet (WithParams Const)} {θ : ClosedFormula (WithParams Const)}
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) ψ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ ↔
      BethConsequence (Base := Base) T θ :=
  ⟨bethConsequence_of_provable, provable_of_bethConsequence_param_free hT0⟩

/-- On parameter-free theories, Beth consequence and Heyting-valued consequence
agree. -/
theorem bethConsequence_iff_heytingConsequence_param_free
    {T : ClosedTheorySet (WithParams Const)} {θ : ClosedFormula (WithParams Const)}
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) ψ) :
    BethConsequence (Base := Base) T θ ↔ HeytingSem.HeytingConsequence (Base := Base) T θ := by
  rw [← provable_iff_bethConsequence_param_free hT0,
    HeytingSem.provable_iff_heytingConsequence_param_free hT0]

/-! ## The constant-domain sentence -/

/-- **Constant domains without the constant-domain sentence**: it is not a
Beth consequence of the empty theory, at any base type. -/
theorem constantDomain_not_bethConsequence (b : Base) :
    ¬ BethConsequence (Base := Base) (Const := WithParams Const) ∅
      (constantDomain (.base b)) := fun h =>
  constantDomain_not_provable (Const := WithParams Const) b
    (provable_of_bethConsequence_param_free (fun _ h => h.elim) h)

/-- Every Kripke structure is a Beth structure, so Beth consequence implies
Kripke consequence. -/
theorem kripkeHenkinConsequence_of_bethConsequence {T : ClosedTheorySet Const}
    {θ : ClosedFormula Const} (h : BethConsequence (Base := Base) T θ) :
    KripkeHenkin.Consequence.{u, v, max u v} (Base := Base) T θ :=
  fun K W hW => h (BethHenkin.ofKripkeHenkin K) W fun _ hψ => hW hψ

/-- The constant-domain sentence separates the two consequence relations: a
Kripke consequence of the empty theory that is not a Beth consequence. -/
theorem constantDomain_separates_kripke_beth (b : Base) :
    KripkeHenkin.Consequence.{u, v, max u v} (Base := Base) (Const := WithParams Const) ∅
        (constantDomain (.base b)) ∧
      ¬ BethConsequence (Base := Base) (Const := WithParams Const) ∅
        (constantDomain (.base b)) :=
  ⟨KripkeHenkin.consequence_constantDomain _, constantDomain_not_bethConsequence b⟩

/-- Positive control, over the signature with one base type and no constants:
`⊤` is a Beth consequence of the empty theory, and the completeness direction
returns its derivation. -/
theorem top_provable_of_bethConsequence :
    ClosedTheorySet.Provable (Const := WithParams fun _ : Ty Unit => Empty) ∅
      (.top : ClosedFormula (WithParams fun _ : Ty Unit => Empty)) :=
  (provable_iff_bethConsequence_param_free (Base := Unit) (Const := fun _ : Ty Unit => Empty)
    (T := ∅) (fun _ h => h.elim)).mpr fun B _ _ => B.forces_top

open ConstantDomainCountermodel in
/-- Positive instance: the Beth structure on the nonempty open subsets of `ℝ`,
whose covers are open covers (`frameValued_covers_iff`) and whose domain
is constant, does not force the constant-domain sentence at `ℝ`. -/
theorem realLine_not_forces_constantDomain (b : Base) :
    ∃ W : (BethHenkin.ofHeyting (FrameValued.model (Base := Base) H C)).World,
      ¬ (BethHenkin.ofHeyting (FrameValued.model (Base := Base) H C)).forces W
        (constantDomain (.base b)) := by
  refine ⟨⟨(⊤ : H), fun h => top_ne_bot (le_bot_iff.mp h)⟩, fun h => ?_⟩
  exact truth_constantDomain_ne_top b (top_le_iff.mp h)

open ConstantDomainCountermodel in
/-- Positive control for soundness: the top world of the Beth structure on the
open subsets of `ℝ` forces the derivable sentence `⊤`. -/
theorem realLine_forces_top :
    (BethHenkin.ofHeyting (FrameValued.model (Base := Unit) H C)).forces
      ⟨(⊤ : H), fun h => top_ne_bot (le_bot_iff.mp h)⟩ (.top : ClosedFormula _) :=
  BethHenkin.forces_of_provable _ (T := ∅)
    ⟨[], fun _ h => absurd h List.not_mem_nil, .topI⟩ fun _ h => h.elim

end Completeness

end Mettapedia.Logic.HOL
