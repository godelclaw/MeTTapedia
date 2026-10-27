import Mettapedia.Logic.HOL.SelectionProofs

/-!
# Selected projections of a three-argument constructor

The constructor may forget its first argument, as an indexed vector
constructor may erase a redundant index. Its second and third fields must
be determined by its image. Choice then constructs projections with proved
computation equations. Values outside the constructor image have no specified
projection behavior.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.ConstructorProjections

universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
    {first second third carrier : Ty Base}

abbrev Constructor (first second third carrier : Ty Base) := first ⇒ second ⇒ third ⇒ carrier

def apply (constructor : Term Const Γ (Constructor first second third carrier))
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third) : Term Const Γ carrier :=
  .app (.app (.app constructor a) b) c

@[simp] theorem subst_apply (σ : Subst Const Γ Ξ)
    (constructor : Term Const Γ (Constructor first second third carrier))
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third) :
    subst σ (apply constructor a b c) = apply (subst σ constructor) (subst σ a) (subst σ b) (subst σ c) := rfl

/-- Field uniqueness at a particular constructor image; the first field need
not be recoverable. -/
def components (constructor : Term Const Γ (Constructor first second third carrier))
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third) : Formula Const Γ :=
  .all (.all (.all (.imp
    (.eq (apply (weaken (weaken (weaken constructor))) (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))
      (weaken (weaken (weaken (apply constructor a b c)))))
    (.and (.eq (.var (.vs .vz)) (weaken (weaken (weaken b))))
      (.eq (.var .vz) (weaken (weaken (weaken c))))))))

def fieldInjective (constructor : Term Const Γ (Constructor first second third carrier)) : Formula Const Γ :=
  .all (.all (.all (components (weaken (weaken (weaken constructor)))
    (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))))

@[simp] theorem subst_components (σ : Subst Const Γ Ξ)
    (constructor : Term Const Γ (Constructor first second third carrier))
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third) :
    subst σ (components constructor a b c) =
      components (subst σ constructor) (subst σ a) (subst σ b) (subst σ c) := by
  simp [components, subst, subst_weaken, Subst.lift, Rename.weaken]

@[simp] theorem subst_fieldInjective (σ : Subst Const Γ Ξ)
    (constructor : Term Const Γ (Constructor first second third carrier)) :
    subst σ (fieldInjective constructor) = fieldInjective (subst σ constructor) := by
  simp [fieldInjective, subst, subst_weaken, Subst.lift, Rename.weaken]

theorem rename_components (ρ : Rename Base Γ Ξ)
    (constructor : Term Const Γ (Constructor first second third carrier))
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third) :
    rename ρ (components constructor a b c) =
      components (rename ρ constructor) (rename ρ a) (rename ρ b) (rename ρ c) := by
  simpa only [subst_ofRename] using subst_components (Subst.ofRename ρ) constructor a b c

def secondBody (constructor : Term Const Γ (Constructor first second third carrier))
    (value : Term Const Γ carrier) : Formula Const (second :: Γ) :=
  .ex (σ := first) (.ex (σ := third)
    (.eq (apply (weaken (weaken (weaken constructor))) (.var (.vs .vz)) (.var (.vs (.vs .vz))) (.var .vz))
      (weaken (weaken (weaken value)))))

def thirdBody (constructor : Term Const Γ (Constructor first second third carrier))
    (value : Term Const Γ carrier) : Formula Const (third :: Γ) :=
  .ex (σ := first) (.ex (σ := second)
    (.eq (apply (weaken (weaken (weaken constructor))) (.var (.vs .vz)) (.var .vz) (.var (.vs (.vs .vz))))
      (weaken (weaken (weaken value)))))

def secondValue (selection : Term Const Γ (SelectionProofs.Selection second))
    (constructor : Term Const Γ (Constructor first second third carrier)) (value : Term Const Γ carrier) :
    Term Const Γ second := SelectionProofs.selected selection (secondBody constructor value)

def thirdValue (selection : Term Const Γ (SelectionProofs.Selection third))
    (constructor : Term Const Γ (Constructor first second third carrier)) (value : Term Const Γ carrier) :
    Term Const Γ third := SelectionProofs.selected selection (thirdBody constructor value)

def secondProjection (selection : Term Const Γ (SelectionProofs.Selection second))
    (constructor : Term Const Γ (Constructor first second third carrier)) : Term Const Γ (carrier ⇒ second) :=
  .lam (secondValue (weaken selection) (weaken constructor) (.var .vz))

def thirdProjection (selection : Term Const Γ (SelectionProofs.Selection third))
    (constructor : Term Const Γ (Constructor first second third carrier)) : Term Const Γ (carrier ⇒ third) :=
  .lam (thirdValue (weaken selection) (weaken constructor) (.var .vz))

@[simp] theorem subst_secondBody (σ : Subst Const Γ Ξ)
    (constructor : Term Const Γ (Constructor first second third carrier)) (value : Term Const Γ carrier) :
    subst (Subst.lift σ) (secondBody constructor value) = secondBody (subst σ constructor) (subst σ value) := by
  simp [secondBody, subst, subst_weaken, Subst.lift, Rename.weaken]

@[simp] theorem subst_thirdBody (σ : Subst Const Γ Ξ)
    (constructor : Term Const Γ (Constructor first second third carrier)) (value : Term Const Γ carrier) :
    subst (Subst.lift σ) (thirdBody constructor value) = thirdBody (subst σ constructor) (subst σ value) := by
  simp [thirdBody, subst, subst_weaken, Subst.lift, Rename.weaken]

@[simp] theorem subst_secondValue (σ : Subst Const Γ Ξ)
    (selection : Term Const Γ (SelectionProofs.Selection second))
    (constructor : Term Const Γ (Constructor first second third carrier)) (value : Term Const Γ carrier) :
    subst σ (secondValue selection constructor value) =
      secondValue (subst σ selection) (subst σ constructor) (subst σ value) := by
  simp [secondValue, SelectionProofs.selected, subst]

@[simp] theorem subst_thirdValue (σ : Subst Const Γ Ξ)
    (selection : Term Const Γ (SelectionProofs.Selection third))
    (constructor : Term Const Γ (Constructor first second third carrier)) (value : Term Const Γ carrier) :
    subst σ (thirdValue selection constructor value) =
      thirdValue (subst σ selection) (subst σ constructor) (subst σ value) := by
  simp [thirdValue, SelectionProofs.selected, subst]

@[simp] theorem subst_secondProjection (σ : Subst Const Γ Ξ)
    (selection : Term Const Γ (SelectionProofs.Selection second))
    (constructor : Term Const Γ (Constructor first second third carrier)) :
    subst σ (secondProjection selection constructor) = secondProjection (subst σ selection) (subst σ constructor) := by
  simp [secondProjection, subst, subst_weaken, Subst.lift]

@[simp] theorem subst_thirdProjection (σ : Subst Const Γ Ξ)
    (selection : Term Const Γ (SelectionProofs.Selection third))
    (constructor : Term Const Γ (Constructor first second third carrier)) :
    subst σ (thirdProjection selection constructor) = thirdProjection (subst σ selection) (subst σ constructor) := by
  simp [thirdProjection, subst, subst_weaken, Subst.lift]

variable {Δ : List (Formula Const Γ)}

private theorem subst_vars {τ : Ty Base} (term : Term Const Γ τ) :
    subst (fun {σ} (index : Var Γ σ) => Term.var index) term = term := subst_id term

private theorem subst_drop_shift {α τ : Ty Base} (value : Term Const Γ α) (term : Term Const Γ τ) :
    subst (Subst.comp (Subst.single value) (fun index => Term.var (.vs index))) term = term := by
  have identity : (Subst.comp (Subst.single value) (fun index => Term.var (.vs index)) : Subst Const Γ Γ) =
      (fun {τ} (index : Var Γ τ) => Term.var index) := by
    funext type index
    rfl
  rw [identity]
  exact subst_id term

def specialize (constructor : Term Const Γ (Constructor first second third carrier))
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third)
    (proof : ProofSyntax Const Δ (fieldInjective constructor)) :
    ProofSyntax Const Δ (components constructor a b c) := by
  apply ProofSyntax.castIndices rfl ?_ (.allE c (.allE b (.allE a proof)))
  simp [instantiate, subst, subst_weaken, Subst.single, Subst.lift, Rename.weaken,
    subst_rename, subst_comp, subst_drop_shift, subst_vars]

def compare (constructor : Term Const Γ (Constructor first second third carrier))
    (a a' : Term Const Γ first) (b b' : Term Const Γ second) (c c' : Term Const Γ third)
    (proof : ProofSyntax Const Δ (components constructor a b c)) :
    ProofSyntax Const Δ (.imp (.eq (apply constructor a' b' c') (apply constructor a b c))
      (.and (.eq b' b) (.eq c' c))) := by
  apply ProofSyntax.castIndices rfl ?_ (.allE c' (.allE b' (.allE a' proof)))
  simp [instantiate, subst, subst_weaken, Subst.single, Subst.lift, Rename.weaken,
    subst_rename, subst_comp, subst_drop_shift, subst_vars]

def second_exists (constructor : Term Const Γ (Constructor first second third carrier))
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third) :
    ProofSyntax Const Δ (.ex (secondBody constructor (apply constructor a b c))) := by
  refine .exI b (.exI a (.exI c ?_))
  apply ProofSyntax.castIndices rfl ?_ (.eqRefl (apply constructor a b c))
  simp [instantiate, subst, subst_weaken, Subst.single, Subst.lift, Rename.weaken,
    subst_rename, subst_comp, subst_drop_shift, subst_vars]

def third_exists (constructor : Term Const Γ (Constructor first second third carrier))
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third) :
    ProofSyntax Const Δ (.ex (thirdBody constructor (apply constructor a b c))) := by
  refine .exI c (.exI a (.exI b ?_))
  apply ProofSyntax.castIndices rfl ?_ (.eqRefl (apply constructor a b c))
  simp [instantiate, subst, subst_weaken, Subst.single, Subst.lift, Rename.weaken,
    subst_rename, subst_comp, subst_drop_shift, subst_vars]

def second_unique (constructor : Term Const Γ (Constructor first second third carrier))
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third) :
    ProofSyntax Const Δ (.imp (components constructor a b c)
      (.all (.imp (secondBody constructor (apply constructor a b c)) (.eq (.var .vz) (weaken b))))) := by
  apply ProofSyntax.impI
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  apply ProofSyntax.exE (.hyp 0)
  apply ProofSyntax.exE (.hyp 0)
  change ProofSyntax Const _ (.eq (.var (.vs (.vs .vz))) (weaken (weaken (weaken b))))
  refine .andEL (.impE (compare (weaken (weaken (weaken constructor)))
    (weaken (weaken (weaken a))) (.var (.vs .vz))
    (weaken (weaken (weaken b))) (.var (.vs (.vs .vz)))
    (weaken (weaken (weaken c))) (.var .vz) ?_) (.hyp 0))
  apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.hyp ⟨3, by simp [weakenHyps]⟩)
  simp [weakenHyps, weaken, rename_components]

def third_unique (constructor : Term Const Γ (Constructor first second third carrier))
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third) :
    ProofSyntax Const Δ (.imp (components constructor a b c)
      (.all (.imp (thirdBody constructor (apply constructor a b c)) (.eq (.var .vz) (weaken c))))) := by
  apply ProofSyntax.impI
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  apply ProofSyntax.exE (.hyp 0)
  apply ProofSyntax.exE (.hyp 0)
  change ProofSyntax Const _ (.eq (.var (.vs (.vs .vz))) (weaken (weaken (weaken c))))
  refine .andER (.impE (compare (weaken (weaken (weaken constructor)))
    (weaken (weaken (weaken a))) (.var (.vs .vz))
    (weaken (weaken (weaken b))) (.var .vz)
    (weaken (weaken (weaken c))) (.var (.vs (.vs .vz))) ?_) (.hyp 0))
  apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.hyp ⟨3, by simp [weakenHyps]⟩)
  simp [weakenHyps, weaken, rename_components]

/-- An inhabited predicate with one possible witness determines the selected
term. The conclusion is an equality proof, not an added selection axiom. -/
def selected_eq {type : Ty Base} (selection : Term Const Γ (SelectionProofs.Selection type))
    (body : Formula Const (type :: Γ)) (witness : Term Const Γ type)
    (choice : ProofSyntax Const Δ (SelectionProofs.principle selection))
    (existsWitness : ProofSyntax Const Δ (.ex body))
    (unique : ProofSyntax Const Δ (.all (.imp body (.eq (.var .vz) (weaken witness))))) :
    ProofSyntax Const Δ (.eq (SelectionProofs.selected selection body) witness) := by
  have selected := SelectionProofs.specification selection body choice existsWitness
  have identifies : ProofSyntax Const Δ
      (.imp (instantiate (SelectionProofs.selected selection body) body)
        (.eq (SelectionProofs.selected selection body) witness)) := by
    apply ProofSyntax.castIndices rfl ?_ (.allE (SelectionProofs.selected selection body) unique)
    simp [instantiate, subst, Subst.single]
  exact .impE identifies selected

def second_apply (selection : Term Const Γ (SelectionProofs.Selection second))
    (constructor : Term Const Γ (Constructor first second third carrier)) (value : Term Const Γ carrier) :
    ProofSyntax Const Δ (.eq (.app (secondProjection selection constructor) value) (secondValue selection constructor value)) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta value (secondValue (weaken selection) (weaken constructor) (.var .vz)))
  simp [secondProjection, instantiate, subst, Subst.single]

def third_apply (selection : Term Const Γ (SelectionProofs.Selection third))
    (constructor : Term Const Γ (Constructor first second third carrier)) (value : Term Const Γ carrier) :
    ProofSyntax Const Δ (.eq (.app (thirdProjection selection constructor) value) (thirdValue selection constructor value)) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta value (thirdValue (weaken selection) (weaken constructor) (.var .vz)))
  simp [thirdProjection, instantiate, subst, Subst.single]

def second_at (selection : Term Const Γ (SelectionProofs.Selection second))
    (constructor : Term Const Γ (Constructor first second third carrier))
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third)
    (choice : ProofSyntax Const Δ (SelectionProofs.principle selection))
    (injectivity : ProofSyntax Const Δ (fieldInjective constructor)) :
    ProofSyntax Const Δ (.eq (.app (secondProjection selection constructor) (apply constructor a b c)) b) :=
  .eqTrans (second_apply selection constructor (apply constructor a b c))
    (selected_eq selection (secondBody constructor (apply constructor a b c)) b choice
      (second_exists constructor a b c) (.impE (second_unique constructor a b c) (specialize constructor a b c injectivity)))

def third_at (selection : Term Const Γ (SelectionProofs.Selection third))
    (constructor : Term Const Γ (Constructor first second third carrier))
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third)
    (choice : ProofSyntax Const Δ (SelectionProofs.principle selection))
    (injectivity : ProofSyntax Const Δ (fieldInjective constructor)) :
    ProofSyntax Const Δ (.eq (.app (thirdProjection selection constructor) (apply constructor a b c)) c) :=
  .eqTrans (third_apply selection constructor (apply constructor a b c))
    (selected_eq selection (thirdBody constructor (apply constructor a b c)) c choice
      (third_exists constructor a b c) (.impE (third_unique constructor a b c) (specialize constructor a b c injectivity)))

theorem specialize_free (constructor : Term Const Γ (Constructor first second third carrier))
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third)
    (proof : ProofSyntax Const Δ (fieldInjective constructor)) (free : proof.FunctionExtensionalityFree) :
    (specialize constructor a b c proof).FunctionExtensionalityFree := by
  simpa [specialize, ProofSyntax.FunctionExtensionalityFree] using free

theorem selected_eq_free {type : Ty Base} (selection : Term Const Γ (SelectionProofs.Selection type))
    (body : Formula Const (type :: Γ)) (witness : Term Const Γ type)
    (choice : ProofSyntax Const Δ (SelectionProofs.principle selection))
    (existsWitness : ProofSyntax Const Δ (.ex body))
    (unique : ProofSyntax Const Δ (.all (.imp body (.eq (.var .vz) (weaken witness)))))
    (choiceFree : choice.FunctionExtensionalityFree) (existsFree : existsWitness.FunctionExtensionalityFree)
    (uniqueFree : unique.FunctionExtensionalityFree) :
    (selected_eq selection body witness choice existsWitness unique).FunctionExtensionalityFree := by
  simp [selected_eq, ProofSyntax.FunctionExtensionalityFree,
    SelectionProofs.specification_free, choiceFree, existsFree, uniqueFree]

theorem second_at_free (selection : Term Const Γ (SelectionProofs.Selection second))
    (constructor : Term Const Γ (Constructor first second third carrier))
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third)
    (choice : ProofSyntax Const Δ (SelectionProofs.principle selection))
    (injectivity : ProofSyntax Const Δ (fieldInjective constructor))
    (choiceFree : choice.FunctionExtensionalityFree) (injectivityFree : injectivity.FunctionExtensionalityFree) :
    (second_at selection constructor a b c choice injectivity).FunctionExtensionalityFree := by
  unfold second_at
  constructor
  · simp [second_apply, ProofSyntax.FunctionExtensionalityFree]
  · apply selected_eq_free _ _ _ _ _ _ choiceFree
    · simp [second_exists, ProofSyntax.FunctionExtensionalityFree]
    · change (second_unique constructor a b c).FunctionExtensionalityFree ∧ _
      constructor
      · simp [second_unique, compare, ProofSyntax.FunctionExtensionalityFree]
      · exact specialize_free constructor a b c injectivity injectivityFree

theorem third_at_free (selection : Term Const Γ (SelectionProofs.Selection third))
    (constructor : Term Const Γ (Constructor first second third carrier))
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third)
    (choice : ProofSyntax Const Δ (SelectionProofs.principle selection))
    (injectivity : ProofSyntax Const Δ (fieldInjective constructor))
    (choiceFree : choice.FunctionExtensionalityFree) (injectivityFree : injectivity.FunctionExtensionalityFree) :
    (third_at selection constructor a b c choice injectivity).FunctionExtensionalityFree := by
  unfold third_at
  constructor
  · simp [third_apply, ProofSyntax.FunctionExtensionalityFree]
  · apply selected_eq_free _ _ _ _ _ _ choiceFree
    · simp [third_exists, ProofSyntax.FunctionExtensionalityFree]
    · change (third_unique constructor a b c).FunctionExtensionalityFree ∧ _
      constructor
      · simp [third_unique, compare, ProofSyntax.FunctionExtensionalityFree]
      · exact specialize_free constructor a b c injectivity injectivityFree

theorem rename_fieldInjective (ρ : Rename Base Γ Ξ)
    (constructor : Term Const Γ (Constructor first second third carrier)) :
    rename ρ (fieldInjective constructor) = fieldInjective (rename ρ constructor) := by
  simpa only [subst_ofRename] using subst_fieldInjective (Subst.ofRename ρ) constructor

theorem rename_selection {type : Ty Base} (ρ : Rename Base Γ Ξ)
    (selection : Term Const Γ (SelectionProofs.Selection type)) :
    rename ρ (SelectionProofs.principle selection) = SelectionProofs.principle (rename ρ selection) := by
  simp [SelectionProofs.principle, SelectionProofs.instanceFormula, rename, weaken, rename_comp,
    Rename.lift, Rename.weaken]

def secondLaw (constructor : Term Const Γ (Constructor first second third carrier))
    (projection : Term Const Γ (carrier ⇒ second)) : Formula Const Γ :=
  .all (.all (.all (.eq
    (.app (weaken (weaken (weaken projection)))
      (apply (weaken (weaken (weaken constructor))) (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz)))
    (.var (.vs .vz)))))

def thirdLaw (constructor : Term Const Γ (Constructor first second third carrier))
    (projection : Term Const Γ (carrier ⇒ third)) : Formula Const Γ :=
  .all (.all (.all (.eq
    (.app (weaken (weaken (weaken projection)))
      (apply (weaken (weaken (weaken constructor))) (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz)))
    (.var .vz))))

theorem rename_secondProjection (ρ : Rename Base Γ Ξ)
    (selection : Term Const Γ (SelectionProofs.Selection second))
    (constructor : Term Const Γ (Constructor first second third carrier)) :
    rename ρ (secondProjection selection constructor) = secondProjection (rename ρ selection) (rename ρ constructor) := by
  simpa only [subst_ofRename] using subst_secondProjection (Subst.ofRename ρ) selection constructor

theorem rename_thirdProjection (ρ : Rename Base Γ Ξ)
    (selection : Term Const Γ (SelectionProofs.Selection third))
    (constructor : Term Const Γ (Constructor first second third carrier)) :
    rename ρ (thirdProjection selection constructor) = thirdProjection (rename ρ selection) (rename ρ constructor) := by
  simpa only [subst_ofRename] using subst_thirdProjection (Subst.ofRename ρ) selection constructor

theorem weakenCtx_secondProjection (context : Ctx Base)
    (selection : ClosedTerm Const (SelectionProofs.Selection second))
    (constructor : ClosedTerm Const (Constructor first second third carrier)) :
    weakenCtx context (secondProjection selection constructor) =
      secondProjection (weakenCtx context selection) (weakenCtx context constructor) := by
  induction context with
  | nil => rfl
  | cons type context ih =>
    rw [weakenCtx_cons, ih]
    exact rename_secondProjection Rename.weaken _ _

theorem weakenCtx_thirdProjection (context : Ctx Base)
    (selection : ClosedTerm Const (SelectionProofs.Selection third))
    (constructor : ClosedTerm Const (Constructor first second third carrier)) :
    weakenCtx context (thirdProjection selection constructor) =
      thirdProjection (weakenCtx context selection) (weakenCtx context constructor) := by
  induction context with
  | nil => rfl
  | cons type context ih =>
    rw [weakenCtx_cons, ih]
    exact rename_thirdProjection Rename.weaken _ _

def second_law (selection : Term Const Γ (SelectionProofs.Selection second))
    (constructor : Term Const Γ (Constructor first second third carrier))
    (choice : ProofSyntax Const Δ (SelectionProofs.principle selection))
    (injectivity : ProofSyntax Const Δ (fieldInjective constructor)) :
    ProofSyntax Const Δ (secondLaw constructor (secondProjection selection constructor)) := by
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  have choice3 : ProofSyntax (Γ := third :: second :: first :: Γ) Const (weakenHyps (weakenHyps (weakenHyps Δ)))
      (SelectionProofs.principle (weaken (weaken (weaken selection)))) := by
    apply ProofSyntax.castIndices rfl ?_
      (((choice.rename (Rename.weaken (σ := first))).rename (Rename.weaken (σ := second))).rename (Rename.weaken (σ := third)))
    simp only [rename_selection, weaken]
  have injectivity3 : ProofSyntax (Γ := third :: second :: first :: Γ) Const (weakenHyps (weakenHyps (weakenHyps Δ)))
      (fieldInjective (weaken (weaken (weaken constructor)))) := by
    apply ProofSyntax.castIndices rfl ?_
      (((injectivity.rename (Rename.weaken (σ := first))).rename (Rename.weaken (σ := second))).rename (Rename.weaken (σ := third)))
    simp only [rename_fieldInjective, weaken]
  apply ProofSyntax.castIndices rfl ?_
    (second_at (weaken (weaken (weaken selection))) (weaken (weaken (weaken constructor)))
      (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz) choice3 injectivity3)
  simp only [weaken, rename_secondProjection]

def third_law (selection : Term Const Γ (SelectionProofs.Selection third))
    (constructor : Term Const Γ (Constructor first second third carrier))
    (choice : ProofSyntax Const Δ (SelectionProofs.principle selection))
    (injectivity : ProofSyntax Const Δ (fieldInjective constructor)) :
    ProofSyntax Const Δ (thirdLaw constructor (thirdProjection selection constructor)) := by
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  have choice3 : ProofSyntax (Γ := third :: second :: first :: Γ) Const (weakenHyps (weakenHyps (weakenHyps Δ)))
      (SelectionProofs.principle (weaken (weaken (weaken selection)))) := by
    apply ProofSyntax.castIndices rfl ?_
      (((choice.rename (Rename.weaken (σ := first))).rename (Rename.weaken (σ := second))).rename (Rename.weaken (σ := third)))
    simp only [rename_selection, weaken]
  have injectivity3 : ProofSyntax (Γ := third :: second :: first :: Γ) Const (weakenHyps (weakenHyps (weakenHyps Δ)))
      (fieldInjective (weaken (weaken (weaken constructor)))) := by
    apply ProofSyntax.castIndices rfl ?_
      (((injectivity.rename (Rename.weaken (σ := first))).rename (Rename.weaken (σ := second))).rename (Rename.weaken (σ := third)))
    simp only [rename_fieldInjective, weaken]
  apply ProofSyntax.castIndices rfl ?_
    (third_at (weaken (weaken (weaken selection))) (weaken (weaken (weaken constructor)))
      (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz) choice3 injectivity3)
  simp only [weaken, rename_thirdProjection]

theorem second_law_free (selection : Term Const Γ (SelectionProofs.Selection second))
    (constructor : Term Const Γ (Constructor first second third carrier))
    (choice : ProofSyntax Const Δ (SelectionProofs.principle selection))
    (injectivity : ProofSyntax Const Δ (fieldInjective constructor))
    (choiceFree : choice.FunctionExtensionalityFree) (injectivityFree : injectivity.FunctionExtensionalityFree) :
    (second_law selection constructor choice injectivity).FunctionExtensionalityFree := by
  unfold second_law
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply second_at_free
  · simpa [ProofSyntax.FunctionExtensionalityFree] using choiceFree
  · simpa [ProofSyntax.FunctionExtensionalityFree] using injectivityFree

theorem third_law_free (selection : Term Const Γ (SelectionProofs.Selection third))
    (constructor : Term Const Γ (Constructor first second third carrier))
    (choice : ProofSyntax Const Δ (SelectionProofs.principle selection))
    (injectivity : ProofSyntax Const Δ (fieldInjective constructor))
    (choiceFree : choice.FunctionExtensionalityFree) (injectivityFree : injectivity.FunctionExtensionalityFree) :
    (third_law selection constructor choice injectivity).FunctionExtensionalityFree := by
  unfold third_law
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply third_at_free
  · simpa [ProofSyntax.FunctionExtensionalityFree] using choiceFree
  · simpa [ProofSyntax.FunctionExtensionalityFree] using injectivityFree

#print axioms subst_secondProjection
#print axioms second_at
#print axioms third_at
#print axioms second_at_free
#print axioms third_at_free
#print axioms second_law_free
#print axioms third_law_free
end Mettapedia.Logic.HOL.ConstructorProjections
