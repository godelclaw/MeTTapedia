import Mettapedia.Logic.HOL.Semantics.KripkeFrameModel
import Mettapedia.Logic.HOL.Semantics.KripkeHenkin

/-!
# Substitutional Kripke-Henkin structures from frames

Over a frame, `KripkeFrameModel.model` interprets every term; its admissible
values do not depend on the world.  Naming every admissible value by a
constant turns the model into a substitutional `KripkeHenkin` structure:
forcing is denotation, and a quantifier over admissible values is a
quantifier over closed terms, because every admissible value is the
denotation of its name.

This gives the substitutional class concrete members.  The two-world frame
`false ≤ true` with the proposition true only at `true` refutes excluded
middle at `false` (`exists_not_forces_excludedMiddle`), so the class is not
classical; `ConstantDomain` shows that it nevertheless validates the
constant-domain schema.
-/

namespace Mettapedia.Logic.HOL

namespace KripkeFrameModel

universe u x

variable {Base : Type u} (F : Frame.{u, x} Base)
variable {Const' : Ty Base → Type x}

/-- The signature naming every admissible value of the frame. -/
def Names (τ : Ty Base) : Type x := {d : F.Val τ // F.Adm τ d}

/-- The full model of the frame over its names. -/
abbrev namedModel : KripkeHenkinGeneral Base (Names F) :=
  model F (fun c => c.1) (fun c => c.2)

/-- Forcing of a closed formula in the named model: its denotation. -/
def forcesNamed (W : F.World) (φ : ClosedFormula (Names F)) : Prop :=
  (namedModel F).denote φ (namedModel F).emptyVal W

/-- World-indexed equality of closed terms in the named model. -/
def eqNamed {τ : Ty Base} (W : F.World) (s t : ClosedTerm (Names F) τ) : Prop :=
  (namedModel F).EqvK W τ ((namedModel F).denote s (namedModel F).emptyVal)
    ((namedModel F).denote t (namedModel F).emptyVal)

variable {F}

theorem eqvK_of_eq {M : KripkePreModel Base Const'} {W : M.World} {τ : Ty Base}
    {d e : Ty.denoteK M.Carrier M.World τ} (hd : M.adm W τ d) (h : d = e) :
    M.EqvK W τ d e :=
  h ▸ M.eqvK_refl hd

theorem adm_closed {τ : Ty Base} (W : F.World) (t : ClosedTerm (Names F) τ) :
    (namedModel F).adm W τ ((namedModel F).denote t (namedModel F).emptyVal) :=
  (namedModel F).term_closed t W _ ((namedModel F).emptyVal_adm W)

theorem forcesNamed_mono {U V : F.World} {φ : ClosedFormula (Names F)} (hUV : F.le U V)
    (h : forcesNamed F U φ) : forcesNamed F V φ :=
  (namedModel F).denote_prop_mono φ ((namedModel F).emptyVal_adm U) hUV h

theorem forcesNamed_instantiate {σ : Ty Base} (W : F.World) (t : ClosedTerm (Names F) σ)
    (φ : Formula (Names F) [σ]) :
    forcesNamed F W (instantiate t φ) ↔
      (namedModel F).denote φ
        ((namedModel F).extend (namedModel F).emptyVal
          ((namedModel F).denote t (namedModel F).emptyVal)) W := by
  exact iff_of_eq (congrFun ((namedModel F).toKripkePreModel.denote_instantiate t φ
    (namedModel F).emptyVal) W)

variable (F)

/-- **The named frame model is a substitutional Kripke-Henkin structure.** -/
def toKripkeHenkin : KripkeHenkin.{u, x, x} Base (Names F) where
  World := F.World
  le := F.le
  le_refl := F.le_refl
  le_trans := F.le_trans
  atom := forcesNamed F
  atom_mono := fun hUV h => forcesNamed_mono hUV h
  eqVal := fun W s t => eqNamed F W s t
  eq_mono := fun hUV h => (namedModel F).eqvK_mono hUV h
  eq_refl := fun W t => (namedModel F).eqvK_refl (adm_closed W t)
  eq_symm := fun h => (namedModel F).eqvK_symm h
  eq_trans := fun h₁ h₂ => (namedModel F).eqvK_trans h₁ h₂
  eq_app_congr := by
    intro σ τ W f g s t hfg hst
    have hft : (namedModel F).EqvK W τ
        ((namedModel F).denote f (namedModel F).emptyVal
          ((namedModel F).denote s (namedModel F).emptyVal))
        ((namedModel F).denote f (namedModel F).emptyVal
          ((namedModel F).denote t (namedModel F).emptyVal)) :=
      (namedModel F).app_congr_arg (adm_closed W f) (adm_closed W s) (adm_closed W t) hst
    exact (namedModel F).eqvK_trans hft (hfg W (F.le_refl W) _ (adm_closed W t))
  eq_funext := by
    intro σ τ W f g h V hV d hd
    exact (namedModel F).eqvK_mono hV (h (.const ⟨d, hd⟩))
  eq_beta := by
    intro σ τ W t u
    exact eqvK_of_eq ((namedModel F).term_closed u W _
      ((namedModel F).toKripkePreModel.extend_adm ((namedModel F).emptyVal_adm W)
        (adm_closed W t)))
      ((namedModel F).toKripkePreModel.denote_instantiate t u
        (namedModel F).emptyVal).symm
  eq_eta := by
    intro σ τ W f
    have hη : (namedModel F).denote (.lam (.app (weaken (σ := σ) f) (.var .vz)))
        (namedModel F).emptyVal = (namedModel F).denote f (namedModel F).emptyVal :=
      funext fun d => congrFun
        ((namedModel F).toKripkePreModel.denote_weaken f (namedModel F).emptyVal d) d
    exact eqvK_of_eq (adm_closed W _) hη
  forces := forcesNamed F
  forces_mono := fun hUV h => forcesNamed_mono hUV h
  forces_atom_const := fun _ => Iff.rfl
  forces_atom_app := fun _ _ => Iff.rfl
  forces_top := trivial
  forces_bot := id
  forces_and := Iff.rfl
  forces_or := Iff.rfl
  forces_imp := Iff.rfl
  forces_not := Iff.rfl
  forces_eq := Iff.rfl
  eq_prop_intro := fun hpq hqp V hV => ⟨hpq V hV, hqp V hV⟩
  eq_prop_elim_left := fun h V hV hp => (h V hV).mp hp
  eq_prop_elim_right := fun h V hV hq => (h V hV).mpr hq
  forces_all := by
    intro W σ φ
    constructor
    · intro h V hV t
      exact (forcesNamed_instantiate V t φ).mpr (h V hV _ (adm_closed V t))
    · intro h V hV d hd
      exact (forcesNamed_instantiate V (.const ⟨d, hd⟩) φ).mp (h V hV (.const ⟨d, hd⟩))
  forces_ex := by
    intro W σ φ
    constructor
    · rintro ⟨d, hd, h⟩
      refine ⟨.const ⟨d, hd⟩, fun V hV => (forcesNamed_instantiate V _ φ).mpr ?_⟩
      exact (namedModel F).denote_prop_mono φ
        ((namedModel F).toKripkePreModel.extend_adm ((namedModel F).emptyVal_adm W) hd) hV h
    · rintro ⟨t, h⟩
      exact ⟨_, adm_closed W t, (forcesNamed_instantiate W t φ).mp (h W (F.le_refl W))⟩

/-! ## A two-world member that refutes excluded middle -/

/-- The frame `false ≤ true` with one-point base carriers. -/
def twoWorlds : Frame.{u, 0} Base where
  World := Bool
  le U V := U = false ∨ V = true
  le_refl W := by cases W <;> simp
  le_trans := by
    intro U V W hUV hVW
    cases U <;> cases V <;> cases W <;> simp_all
  Carrier _ := PUnit

/-- The proposition true only at `true`. -/
def lateProp : Names (twoWorlds (Base := Base)) .prop :=
  ⟨fun W => W = true, by
    intro U V hUV hU
    rcases hUV with h | h
    · subst h; cases hU
    · exact h⟩

/-- **The substitutional class is not classical**: some member does not force
excluded middle for a proposition constant at its root. -/
theorem exists_not_forces_excludedMiddle :
    ¬ (toKripkeHenkin (twoWorlds (Base := Base))).forces false
      (.or (.const lateProp) (.not (.const lateProp))) := by
  rintro (h | h)
  · exact Bool.false_ne_true h
  · exact h true (Or.inl rfl) rfl

end KripkeFrameModel

end Mettapedia.Logic.HOL
