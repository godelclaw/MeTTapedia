import Mettapedia.Logic.HOL.Semantics.BethHenkin
import Mettapedia.Logic.HOL.Semantics.KripkeVaryingCanonical

/-!
# Frame-valued completeness through Beth structures

The monotone local sets of worlds of a Beth structure (`BethHenkin.LocalSet`)
are the truth values of `HeytingSem.ofBethHenkin`.  They form a frame: joins
are the worlds covered by members of a family, meets are intersections
(`Order.Frame` instance), and the model's operations are the frame's
(`ofBethHenkin_himp_eq`).

For a Heyting-valued model `M`, `rep M x` is the set of worlds of
`BethHenkin.ofHeyting M` below `x`.

* Truth lemma: the value of `φ` in `HeytingSem.ofBethHenkin (ofHeyting M)` is
  `rep M (M.val φ)` (`val_ofHeyting`, by definition).
* `rep` reflects and preserves the order (`rep_le_rep_iff`) and preserves `⊤`,
  `⊥`, meets, joins and implication (`rep_top`, `rep_bot`, `rep_inf`,
  `rep_sup`, `rep_himp`), and every existing least upper bound and greatest
  lower bound (`rep_isLUB`, `rep_isGLB`).  So the interpretations of the
  quantifiers, which are such bounds over closed instances, are preserved.
* `provable_iff_frameConsequence_param_free`: soundness and completeness for
  Heyting-valued substitutional models whose truth values form a frame.
* `frameValued_isFrameModel`: the frame-valued models of `FrameValued` are such
  models; `constantDomain_not_frameConsequence` is the negative instance.
* `varyingConsequence_iff_bethConsequence`: over a countable signature with a
  closed term at every base type, the two ways around the constant-domain
  sentence give the same consequence relation: varying domains with Kripke
  clauses, and constant domains with cover clauses.

The completion used here is the frame of local sets for the covering system
of `ofHeyting`, in which a family covers `a` when every upper bound of the
family is above `a`; it is not the MacNeille completion.  The quantifiers
range over closed terms: these are substitutional frame-valued models, not
frame-valued type structures with full function spaces.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL

universe u v w

namespace BethHenkin

variable {Base : Type u} {Const : Ty Base → Type v}

/-- The truth values of a Beth structure: its monotone local sets of worlds. -/
abbrev LocalSet (B : BethHenkin.{u, v, w} Base Const) : Type w := (HeytingSem.ofBethHenkin B).Ω

section Frame

variable (B : BethHenkin.{u, v, w} Base Const)

/-- The join of a family of local sets: the worlds covered by members of the
family. -/
def localSSup (𝒮 : Set (LocalSet B)) : LocalSet B :=
  ⟨fun W => ∃ C, B.Covers W C ∧ ∀ V ∈ C, ∃ S ∈ 𝒮, S.1 V,
    fun hUV h => by
      obtain ⟨C, hC, hS⟩ := h
      refine ⟨_, B.covers_restrict hC hUV, fun X hX => ?_⟩
      obtain ⟨_, Y, hY, hYX⟩ := hX
      obtain ⟨S, hS𝒮, hSY⟩ := hS Y hY
      exact ⟨S, hS𝒮, S.2.1 hYX hSY⟩,
    fun {W C} hC h => by
      refine ⟨_, B.covers_local (R := {X | ∃ S ∈ 𝒮, S.1 X}) hC fun V hV => ?_, fun X hX => hX.2⟩
      obtain ⟨D, hD, hDS⟩ := h V hV
      exact B.covers_mono hD (fun X hX => ⟨B.covers_le hD X hX, hDS X hX⟩) fun X hX => hX.1⟩

/-- The meet of a family of local sets: their intersection. -/
def localSInf (𝒮 : Set (LocalSet B)) : LocalSet B :=
  ⟨fun W => ∀ S ∈ 𝒮, S.1 W, fun hUV h S hS => S.2.1 hUV (h S hS),
    fun hC h S hS => S.2.2 hC fun V hV => h V hV S hS⟩

instance : CompleteLattice (LocalSet B) where
  le := (HeytingSem.ofBethHenkin B).le
  le_refl := (HeytingSem.ofBethHenkin B).le_refl
  le_trans _ _ _ := (HeytingSem.ofBethHenkin B).le_trans
  le_antisymm S T h₁ h₂ := Subtype.ext (funext fun W => propext ⟨h₁ W, h₂ W⟩)
  sup := (HeytingSem.ofBethHenkin B).sup
  le_sup_left := (HeytingSem.ofBethHenkin B).le_sup_left
  le_sup_right := (HeytingSem.ofBethHenkin B).le_sup_right
  sup_le _ _ _ := (HeytingSem.ofBethHenkin B).sup_le
  inf := (HeytingSem.ofBethHenkin B).inf
  inf_le_left := (HeytingSem.ofBethHenkin B).inf_le_left
  inf_le_right := (HeytingSem.ofBethHenkin B).inf_le_right
  le_inf _ _ _ := (HeytingSem.ofBethHenkin B).le_inf
  sSup := localSSup B
  isLUB_sSup 𝒮 :=
    ⟨fun S hS W h =>
      ⟨{W}, B.covers_self W, fun V hV => ⟨S, hS, by rw [Set.mem_singleton_iff.mp hV]; exact h⟩⟩,
    fun T h W hW => by
      obtain ⟨C, hC, hS⟩ := hW
      exact T.2.2 hC fun V hV => by
        obtain ⟨S, hS𝒮, hSV⟩ := hS V hV
        exact h hS𝒮 V hSV⟩
  sInf := localSInf B
  isGLB_sInf 𝒮 := ⟨fun S hS W h => h S hS, fun T h W hT S hS => h hS W hT⟩
  top := (HeytingSem.ofBethHenkin B).top
  le_top := (HeytingSem.ofBethHenkin B).le_top
  bot := (HeytingSem.ofBethHenkin B).bot
  bot_le := (HeytingSem.ofBethHenkin B).bot_le

/-- **The local sets of a Beth structure form a frame.** -/
instance : Order.Frame (LocalSet B) :=
  Order.Frame.ofMinimalAxioms
    { inf_sSup_le_iSup_inf := fun a s => by
        rw [← sSup_image]
        intro W hW
        obtain ⟨ha, C, hC, hS⟩ := hW
        refine ⟨C, hC, fun V hV => ?_⟩
        obtain ⟨S, hS𝒮, hSV⟩ := hS V hV
        exact ⟨_, ⟨S, hS𝒮, rfl⟩, a.2.1 (B.covers_le hC V hV) ha, hSV⟩ }

theorem ofBethHenkin_le_iff (S T : LocalSet B) :
    (HeytingSem.ofBethHenkin B).le S T ↔ S ≤ T := Iff.rfl

/-- The implication of the model is the frame's. -/
theorem ofBethHenkin_himp_eq (S T : LocalSet B) :
    (HeytingSem.ofBethHenkin B).himp S T = S ⇨ T := by
  apply le_antisymm
  · exact le_himp_iff.mpr
      ((HeytingSem.ofBethHenkin B).himp_adjoint_mp ((HeytingSem.ofBethHenkin B).le_refl _))
  · exact (HeytingSem.ofBethHenkin B).himp_adjoint_intro (himp_inf_le : (S ⇨ T) ⊓ S ≤ T)

end Frame

/-! ## The representation of a Heyting-valued model -/

section Representation

variable (M : HeytingSem.HeytingGeneralModel.{u, v, w} Base Const)

/-- The worlds of `ofHeyting M` below a value. -/
def rep (x : M.Ω) : LocalSet (ofHeyting M) :=
  ⟨fun a => M.le a.1 x, fun h hx => M.le_trans h hx, fun hC h => hC.2 x h⟩

/-- **Truth lemma**: the value of a formula in the frame-valued model of
`ofHeyting M` is the representation of its value in `M`. -/
theorem val_ofHeyting (φ : ClosedFormula Const) :
    (HeytingSem.ofBethHenkin (ofHeyting M)).val φ = rep M (M.val φ) := rfl

variable {M}

theorem rep_le_rep_iff {x y : M.Ω} : rep M x ≤ rep M y ↔ M.le x y := by
  classical
  constructor
  · intro h
    by_cases hx : M.le x M.bot
    · exact M.le_trans hx (M.bot_le y)
    · exact h ⟨x, hx⟩ (M.le_refl x)
  · intro h _ ha
    exact M.le_trans ha h

variable (M)

theorem rep_top : rep M M.top = ⊤ :=
  Subtype.ext (funext fun _ => propext ⟨fun _ => trivial, fun _ => M.le_top _⟩)

theorem rep_bot : rep M M.bot = ⊥ :=
  Subtype.ext (funext fun a => propext ⟨fun h => a.2 h, False.elim⟩)

theorem rep_inf (x y : M.Ω) : rep M (M.inf x y) = rep M x ⊓ rep M y :=
  Subtype.ext (funext fun _ => propext
    ⟨fun h => ⟨M.le_trans h (M.inf_le_left _ _), M.le_trans h (M.inf_le_right _ _)⟩,
      fun h => M.le_inf h.1 h.2⟩)

/-- `rep` sends an existing least upper bound to the join. -/
theorem rep_isLUB {S : Set M.Ω} {x : M.Ω} (hub : ∀ s ∈ S, M.le s x)
    (hlub : ∀ c, (∀ s ∈ S, M.le s c) → M.le x c) :
    rep M x = sSup (rep M '' S) := by
  apply le_antisymm
  · intro a ha
    refine ⟨{b | M.le b.1 a.1 ∧ ∃ s ∈ S, M.le b.1 s}, ⟨fun b hb => hb.1, fun c hc =>
      le_of_le_lub M hlub ha c fun b hb hbs => hc b ⟨hb, hbs⟩⟩, fun V hV => ?_⟩
    obtain ⟨_, s, hs, hVs⟩ := hV
    exact ⟨rep M s, ⟨s, hs, rfl⟩, hVs⟩
  · refine sSup_le ?_
    rintro _ ⟨s, hs, rfl⟩
    exact rep_le_rep_iff.mpr (hub s hs)

/-- `rep` sends an existing greatest lower bound to the meet. -/
theorem rep_isGLB {S : Set M.Ω} {x : M.Ω} (hlb : ∀ s ∈ S, M.le x s)
    (hglb : ∀ c, (∀ s ∈ S, M.le c s) → M.le c x) :
    rep M x = sInf (rep M '' S) := by
  apply le_antisymm
  · refine le_sInf ?_
    rintro _ ⟨s, hs, rfl⟩
    exact rep_le_rep_iff.mpr (hlb s hs)
  · intro a ha
    exact hglb a.1 fun s hs => ha (rep M s) ⟨s, hs, rfl⟩

theorem rep_sup (x y : M.Ω) : rep M (M.sup x y) = rep M x ⊔ rep M y := by
  rw [rep_isLUB M (S := {x, y}) (x := M.sup x y)
    (by
      rintro s (rfl | rfl)
      · exact M.le_sup_left _ _
      · exact M.le_sup_right _ _)
    (fun c hc => M.sup_le (hc x (Set.mem_insert _ _)) (hc y (Set.mem_insert_of_mem _ rfl))),
    Set.image_pair, sSup_pair]

theorem rep_himp (x y : M.Ω) : rep M (M.himp x y) = rep M x ⇨ rep M y := by
  classical
  apply le_antisymm
  · refine le_himp_iff.mpr ?_
    rw [← rep_inf]
    exact rep_le_rep_iff.mpr (M.himp_adjoint_mp (M.le_refl _))
  · intro a ha
    refine M.himp_adjoint_intro ?_
    by_cases hbot : M.le (M.inf a.1 x) M.bot
    · exact M.le_trans hbot (M.bot_le y)
    · have hb : (rep M x ⇨ rep M y).1 ⟨M.inf a.1 x, hbot⟩ :=
        (rep M x ⇨ rep M y).2.1 (M.inf_le_left a.1 x) ha
      exact (himp_inf_le : (rep M x ⇨ rep M y) ⊓ rep M x ≤ rep M y) _
        ⟨hb, M.inf_le_right a.1 x⟩

end Representation

end BethHenkin

/-! ## Frame-valued completeness -/

/-- Consequence over the Heyting-valued substitutional models whose truth
values form a frame ordered by the model's order. -/
def FrameConsequence {Base : Type u} {Const : Ty Base → Type v}
    (T : ClosedTheorySet Const) (θ : ClosedFormula Const) : Prop :=
  ∀ (M : HeytingSem.HeytingGeneralModel.{u, v, max u v} Base Const) [Order.Frame M.Ω],
    (∀ a b : M.Ω, M.le a b ↔ a ≤ b) →
      (∀ ψ ∈ T, M.le M.top (M.val ψ)) → M.le M.top (M.val θ)

section FrameCompleteness

variable {Base : Type u} {Const : Ty Base → Type v}

open Mettapedia.Logic.HOL.WithParams

theorem frameConsequence_of_provable {T : ClosedTheorySet Const} {θ : ClosedFormula Const}
    (h : ClosedTheorySet.Provable (Const := Const) T θ) : FrameConsequence T θ :=
  fun M _ _ hT => HeytingSem.heytingConsequence_of_provable h M hT

/-- **Completeness for frame-valued substitutional models**, for
parameter-free theories over the parameter language. -/
theorem provable_of_frameConsequence_param_free
    {T : ClosedTheorySet (WithParams Const)} {θ : ClosedFormula (WithParams Const)}
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) ψ)
    (hSem : FrameConsequence (Base := Base) T θ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ := by
  classical
  let L := HeytingSem.Lindenbaum.lindenbaumModel (Base := Base) T hT0
  have hLT : ∀ ψ ∈ T, L.le L.top (L.val ψ) := fun ψ hψ =>
    HeytingSem.Lindenbaum.provable_mono (Set.subset_insert _ _)
      (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hψ)
  have hW := hSem (HeytingSem.ofBethHenkin (BethHenkin.ofHeyting L)) (fun _ _ => Iff.rfl)
    fun ψ hψ a _ => L.le_trans (L.le_top a.1) (hLT ψ hψ)
  have hTop : L.le L.top (L.val θ) := by
    by_cases hbot : L.le L.top L.bot
    · exact L.le_trans hbot (L.bot_le _)
    · exact hW ⟨L.top, hbot⟩ trivial
  exact HeytingSem.Lindenbaum.provable_cut hTop
    (ClosedTheorySet.provable_top (Const := WithParams Const) T)

/-- **Soundness and completeness for frame-valued substitutional models.** -/
theorem provable_iff_frameConsequence_param_free
    {T : ClosedTheorySet (WithParams Const)} {θ : ClosedFormula (WithParams Const)}
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) ψ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T θ ↔
      FrameConsequence (Base := Base) T θ :=
  ⟨frameConsequence_of_provable, provable_of_frameConsequence_param_free hT0⟩

/-- Positive instance: the frame-valued models of `FrameValued` are ordered by
their frame. -/
theorem frameValued_isFrameModel {H : Type w} [Order.Frame H] {C : Base → Type w}
    (a b : (FrameValued.model H C).Ω) :
    (FrameValued.model H C).le a b ↔ @LE.le H _ a b := Iff.rfl

/-- Negative instance: the constant-domain sentence is not a frame-valued
consequence of the empty theory. -/
theorem constantDomain_not_frameConsequence (b : Base) :
    ¬ FrameConsequence (Base := Base) (Const := WithParams Const) ∅
      (constantDomain (.base b)) := fun h =>
  constantDomain_not_provable (Const := WithParams Const) b
    (provable_of_frameConsequence_param_free (fun _ h => h.elim) h)

open KripkeVarying.Canonical in
/-- **Varying domains and covers agree.**  Over a countable signature with a
closed term at every base type, consequence over varying-domain Kripke
structures coincides with consequence over constant-domain Beth structures for
the parameter language. -/
theorem varyingConsequence_iff_bethConsequence [Countable Base] [∀ τ, Countable (Const τ)]
    (inhBase : ∀ b : Base, ClosedTerm Const (.base b))
    {T : ClosedTheorySet Const} {θ : ClosedFormula Const} :
    KripkeVarying.Consequence.{u, v, max u v} T θ ↔
      BethConsequence (Base := Base)
        ((mapConst (fun c => (inj c : WithParams Const _))) '' T)
        (mapConst (fun c => (inj c : WithParams Const _)) θ) := by
  rw [consequence_iff_heytingConsequence inhBase, bethConsequence_iff_heytingConsequence_param_free]
  rintro _ ⟨ψ, _, rfl⟩ σ k
  exact noConstOccurrence_param_mapConst_inj ψ σ k

/-- Positive control, over the signature with one base type and no constants:
`⊤` is a frame-valued consequence of the empty theory, and the completeness
direction returns its derivation. -/
theorem top_provable_of_frameConsequence :
    ClosedTheorySet.Provable (Const := WithParams fun _ : Ty Unit => Empty) ∅
      (.top : ClosedFormula (WithParams fun _ : Ty Unit => Empty)) :=
  (provable_iff_frameConsequence_param_free (Base := Unit) (Const := fun _ : Ty Unit => Empty)
    (T := ∅) (fun _ h => h.elim)).mpr fun M _ _ _ => by rw [M.val_top]; exact M.le_refl _

open KripkeVarying.Canonical in
/-- Positive control with a base type: `∃ x, x = o` over the one-point signature
is a Beth consequence, through the varying-domain consequence. -/
theorem pointExistsEqO_bethConsequence :
    BethConsequence (Base := Unit)
      ((mapConst (fun c => (inj c : WithParams PointConst _))) '' (∅ : ClosedTheorySet PointConst))
      (mapConst (fun c => (inj c : WithParams PointConst _)) pointExistsEqO) :=
  (varyingConsequence_iff_bethConsequence pointInhabitant).mp pointExistsEqO_consequence

end FrameCompleteness

end Mettapedia.Logic.HOL
