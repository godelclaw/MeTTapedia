import Mettapedia.Logic.HOL.ConstantSubstitutionSemantics
import Mettapedia.Logic.HOL.ProofSyntaxModulo
import Mettapedia.Logic.HOL.CanonicalTheory
import Mettapedia.Logic.HOL.Semantics.ModelProperties

/-!
# The facts a hosted proof library publishes, as source formulas

A proof library that links its proofs publishes facts it can realize:

* reflexivity at a type, `∀x. x = x` (`reflexivityFormula`);
* substitution at a type, `∀P x y. x = y ⇒ P x ⇒ P y` (`substitutionFormula`);
* η at a function type, `∀f. (λx. f x) = f` (`etaFormula`);
* the universal closure of a defining equation, `∀x⃗. l = r`
  (`DefiningEquation.closedFormula`);
* the induction principle of a simple inductive sort, whose constructors take
  recursive fields and fields of other types (`inductionFormula`): for each
  constructor the case `∀x⃗. P r₁ ⇒ ⋯ ⇒ P rₖ ⇒ P (c x⃗)`, with one hypothesis
  per recursive field in field order, and the conclusion `∀t. P t`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

/-- `∀x : τ. x = x`. -/
def reflexivityFormula (τ : Ty Base) : Formula Const [] :=
  .all (σ := τ) (.eq (.var .vz) (.var .vz))

/-- `∀P : τ → prop. ∀x y : τ. x = y ⇒ P x ⇒ P y`. -/
def substitutionFormula (τ : Ty Base) : Formula Const [] :=
  .all (σ := .arr τ .prop) (.all (σ := τ) (.all (σ := τ)
    (.imp (.eq (.var (.vs .vz)) (.var .vz))
      (.imp (.app (.var (.vs (.vs .vz))) (.var (.vs .vz)))
        (.app (.var (.vs (.vs .vz))) (.var .vz))))))

/-- `∀f : σ → τ. (λx. f x) = f`. -/
def etaFormula (σ τ : Ty Base) : Formula Const [] :=
  .all (σ := .arr σ τ) (.eq (.lam (.app (.var (.vs .vz)) (.var .vz))) (.var .vz))

/-- The universal closure of a formula over a context, the oldest variable
outermost. -/
def closeAll : (Θ : Ctx Base) → Formula Const Θ → Formula Const []
  | [], φ => φ
  | τ :: Θ, φ => closeAll Θ (.all (σ := τ) φ)

/-- Universal closure is exactly validity at every admissible valuation.
The statement does not assume that semantic values are denoted by closed terms. -/
theorem models_closeAll_iff (model : HenkinModel.{u, v, w} Base Const)
    (context : Ctx Base) (formula : Formula Const context) :
    model.models (closeAll context formula) ↔
      ∀ valuation : model.Valuation context,
        model.ValuationAdmissible valuation → (model.denote formula valuation).down := by
  induction context with
  | nil =>
      constructor
      · intro valid valuation _
        have equal : model.denote formula valuation =
            model.denote formula (fun index => nomatch index) := by
          congr 1
          funext type index
          nomatch index
        change (model.denote formula (fun index => nomatch index)).down at valid
        rw [equal]
        exact valid
      · intro valid
        exact valid (fun {_} index => nomatch index) (by
          intro type index
          nomatch index)
  | cons type context ih =>
      rw [closeAll, ih]
      constructor
      · intro valid valuation admissible
        let tail : model.Valuation context := fun {_} index => valuation (.vs index)
        have tailAdmissible : model.ValuationAdmissible tail :=
          fun {_} index => admissible (.vs index)
        have quantified := valid tail tailAdmissible
        change ∀ value, model.adm type value →
          (model.denote formula (model.extend tail value)).down at quantified
        have equal : model.denote formula (model.extend tail (valuation .vz)) =
            model.denote formula valuation := by
          congr 1
          funext indexType index
          cases index <;> rfl
        simpa only [equal] using quantified (valuation .vz) (admissible .vz)
      · intro valid valuation admissible
        change ∀ value, model.adm type value →
          (model.denote formula (model.extend valuation value)).down
        intro value valueAdmissible
        exact valid (model.extend valuation value)
          (model.extend_admissible admissible valueAdmissible)

/-- In a full-domain model, universal closure quantifies over all valuations. -/
theorem models_closeAll_iff_of_fullDomains (model : HenkinModel.{u, v, w} Base Const)
    (full : model.FullDomains) (context : Ctx Base) (formula : Formula Const context) :
    model.models (closeAll context formula) ↔
      ∀ valuation : model.Valuation context, (model.denote formula valuation).down := by
  rw [models_closeAll_iff]
  constructor
  · intro valid valuation
    exact valid valuation (fun {type} index => full type (valuation index))
  · intro valid valuation _
    exact valid valuation

/-- Eliminate a universal closure by an arbitrary typed substitution into the
actual ambient context, retaining the same ordered hypotheses. -/
theorem ExtDerivation.closeAll_elim {context target : Ctx Base}
    {hypotheses : List (Formula Const target)} (formula : Formula Const context)
    (substitution : Subst Const context target)
    (proof : ExtDerivation Const hypotheses (weakenCtx target (closeAll context formula))) :
    ExtDerivation Const hypotheses (subst substitution formula) := by
  induction context with
  | nil =>
      have equal : subst substitution formula = weakenCtx target formula :=
        subst_weakenCtx substitution formula
      rw [equal]
      exact proof
  | cons type context ih =>
      let tail : Subst Const context target :=
        fun {_} index => substitution (.vs index)
      have quantified : ExtDerivation Const hypotheses
          (.all (subst (Subst.lift tail) formula)) :=
        ih (.all formula) tail proof
      have eliminated := ExtDerivation.allE (substitution .vz) quantified
      have equal : instantiate (substitution .vz) (subst (Subst.lift tail) formula) =
          subst substitution formula := by
        rw [instantiate, subst_comp]
        apply subst_ext
        intro indexType index
        cases index with
        | vz => rfl
        | vs index =>
            change instantiate (substitution .vz) (weaken (substitution (.vs index))) =
              substitution (.vs index)
            exact instantiate_weaken _ _
      rw [equal] at eliminated
      exact eliminated

/-- A finite proof of a published universal fact yields every closed typed
substitution instance over the same theory. -/
theorem ClosedTheorySet.provable_closeAll_elim (theory : ClosedTheorySet Const)
    {context : Ctx Base} (formula : Formula Const context)
    (substitution : Subst Const context [])
    (proof : theory.Provable (closeAll context formula)) :
    theory.Provable (subst substitution formula) := by
  obtain ⟨hypotheses, members, derivation⟩ := proof
  exact ⟨hypotheses, members, ExtDerivation.closeAll_elim formula substitution derivation⟩

/-- The universal closure `∀x⃗. l = r` of a defining equation. -/
def DefiningEquation.closedFormula (equation : DefiningEquation Const) : Formula Const [] :=
  closeAll equation.context (.eq equation.left equation.right)

/-- `p₁ ⇒ p₂ ⇒ ⋯ ⇒ q`. -/
def hypChain {Γ : Ctx Base} : List (Formula Const Γ) → Formula Const Γ → Formula Const Γ
  | [], q => q
  | p :: ps, q => .imp p (hypChain ps q)

/-- Substitution retains the premise inventory and its authored order. -/
@[simp] theorem subst_hypChain {context target : Ctx Base}
    (substitution : Subst Const context target) (premises : List (Formula Const context))
    (conclusion : Formula Const context) :
    subst substitution (hypChain premises conclusion) =
      hypChain (premises.map (subst substitution)) (subst substitution conclusion) := by
  induction premises with
  | nil => rfl
  | cons premise premises ih => simp only [hypChain, subst, List.map_cons, ih]

/-- An implication chain means that all listed premises imply its conclusion. -/
theorem denote_hypChain_iff (model : HenkinModel.{u, v, w} Base Const)
    {context : Ctx Base} (premises : List (Formula Const context))
    (conclusion : Formula Const context) (valuation : model.Valuation context) :
    (model.denote (hypChain premises conclusion) valuation).down ↔
      ((∀ premise ∈ premises, (model.denote premise valuation).down) →
        (model.denote conclusion valuation).down) := by
  induction premises with
  | nil => simp [hypChain]
  | cons premise premises ih =>
      change ((model.denote premise valuation).down →
        (model.denote (hypChain premises conclusion) valuation).down) ↔ _
      rw [ih]
      constructor
      · intro valid satisfied
        exact valid (satisfied premise (by simp))
          (fun other member => satisfied other (by simp [member]))
      · intro valid first rest
        apply valid
        intro other member
        rcases List.mem_cons.mp member with rfl | member
        · exact first
        · exact rest other member

/-- Replay each premise of a published implication chain in its authored order. -/
theorem ExtDerivation.hypChain_elim {context : Ctx Base}
    {hypotheses : List (Formula Const context)} (premises : List (Formula Const context))
    (conclusion : Formula Const context)
    (proof : ExtDerivation Const hypotheses (hypChain premises conclusion))
    (premiseProofs : ∀ premise ∈ premises, ExtDerivation Const hypotheses premise) :
    ExtDerivation Const hypotheses conclusion := by
  induction premises with
  | nil => exact proof
  | cons premise premises ih =>
      exact ih (ExtDerivation.impE proof (premiseProofs premise (by simp)))
        (fun other member => premiseProofs other (by simp [member]))

/-- Finite derivability from a theory respects each premise of an implication
chain; the witnesses may use different finite subsets of that theory. -/
theorem ClosedTheorySet.provable_hypChain_elim (theory : ClosedTheorySet Const)
    (premises : List (ClosedFormula Const)) (conclusion : ClosedFormula Const)
    (proof : theory.Provable (hypChain premises conclusion))
    (premiseProofs : ∀ premise ∈ premises, theory.Provable premise) :
    theory.Provable conclusion := by
  induction premises with
  | nil => exact proof
  | cons premise premises ih =>
      exact ih (ClosedTheorySet.provable_mp proof (premiseProofs premise (by simp)))
        (fun other member => premiseProofs other (by simp [member]))

namespace PublishedFactsControls

/-- Universal reflexivity is valid without requiring any denoting constants. -/
theorem universal_reflexivity (model : HenkinModel.{u, v, w} Base Const) (type : Ty Base) :
    model.models (closeAll [type] (.eq (.var .vz) (.var .vz) : Formula Const [type])) := by
  apply (models_closeAll_iff model _ _).mpr
  intro valuation admissible
  exact model.eqv_refl (admissible .vz)

/-- Publishing every proposition as true is refused, even with empty base carriers. -/
theorem universal_proposition_refused (model : HenkinModel.{u, v, w} Base Const) :
    ¬ model.models (closeAll [.prop] (.var .vz : Formula Const [.prop])) := by
  intro valid
  let empty : model.Valuation [] := fun {_} index => nomatch index
  let falseValue : Ty.denote model.Carrier .prop := ULift.up False
  have emptyAdmissible : model.ValuationAdmissible empty := by
    intro type index
    nomatch index
  have impossible := (models_closeAll_iff model _ _).mp valid
    (model.extend (σ := .prop) empty falseValue)
    (model.extend_admissible emptyAdmissible (model.prop_mem falseValue))
  exact impossible

end PublishedFactsControls

/-! ## Simple inductive sorts -/

/-- The type of a constructor of `sort` with the given fields: a field is
recursive (`none`) or of a type (`some σ`). -/
def ctorType (sort : Base) : List (Option (Ty Base)) → Ty Base
  | [] => .base sort
  | none :: fields => .arr (.base sort) (ctorType sort fields)
  | some σ :: fields => .arr σ (ctorType sort fields)

/-- A constructor of a simple inductive sort: its fields and its constant. -/
structure InductiveCtor (Const : Ty Base → Type v) (sort : Base) where
  fields : List (Option (Ty Base))
  symbol : Const (ctorType sort fields)

/-- The case of a constructor at the motive `p`: the remaining fields are
quantified, the recursive ones among all fields give hypotheses `p r`, and the
conclusion is `p` at the constructor applied to all fields. -/
def caseFormula (sort : Base) : (fields : List (Option (Ty Base))) → {Γ : Ctx Base} →
    Term Const Γ (.arr (.base sort) .prop) → Term Const Γ (ctorType sort fields) →
    List (Term Const Γ (.base sort)) → Formula Const Γ
  | [], _, p, head, recs => hypChain (recs.map (.app p)) (.app p head)
  | none :: fields, _, p, head, recs =>
      .all (σ := .base sort) (caseFormula sort fields (weaken p) (.app (weaken head) (.var .vz))
        (recs.map weaken ++ [.var .vz]))
  | some σ :: fields, _, p, head, recs =>
      .all (σ := σ) (caseFormula sort fields (weaken p) (.app (weaken head) (.var .vz))
        (recs.map weaken))

/-- The cases of the constructors at `p`, then `∀t. p t`. -/
def inductionChain (sort : Base) (ctors : List (InductiveCtor Const sort)) {Γ : Ctx Base}
    (p : Term Const Γ (.arr (.base sort) .prop)) : Formula Const Γ :=
  hypChain (ctors.map fun c => caseFormula sort c.fields p (.const c.symbol) [])
    (.all (σ := .base sort) (.app (weaken p) (.var .vz)))

/-- The induction principle of a simple inductive sort:
`∀P. case₁ ⇒ ⋯ ⇒ caseₖ ⇒ ∀t. P t`. -/
def inductionFormula (sort : Base) (ctors : List (InductiveCtor Const sort)) : Formula Const [] :=
  .all (σ := .arr (.base sort) .prop) (inductionChain sort ctors (.var .vz))

namespace Term

theorem SymbolsSatisfy.closeAll (allowed : ∀ {type}, Const type → Prop)
    (context : Ctx Base) (formula : Formula Const context) (supported : formula.SymbolsSatisfy allowed) :
    (HOL.closeAll context formula).SymbolsSatisfy allowed := by
  induction context with
  | nil => exact supported
  | cons type context ih => exact ih (.all formula) supported

end Term

end Mettapedia.Logic.HOL
