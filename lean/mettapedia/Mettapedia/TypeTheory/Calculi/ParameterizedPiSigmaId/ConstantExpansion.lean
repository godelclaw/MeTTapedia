import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedSubstitution

/-!
# Closed expansion and contextual constant interpretation

An expansion assigns a closed term to each declaration name. It substitutes
those terms for constants, preserving all other syntax. Expansion is not
normalization: inserted bodies are not expanded again. A declaration package
must independently justify both its chosen bodies and its computation rules.

Contextual interpretation permits primitive values in an actual target telescope.
It acts simultaneously on constants and source variables, weakening both beneath
binders. Source and target substitutions commute with this action. Ordinary
substitution and the original closed expansion are recovered by proved comparisons.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ConstantExpansion

variable {Head : Type} {n m : Nat}

abbrev Bodies (Head : Type) := DeclName → Tm Head 0

/-- Constant names in traversal order, retaining repeated occurrences. Bound
variables and heads contribute no declaration dependencies. -/
def constantNames {n : Nat} : Tm Head n → List DeclName
  | .var _ | .head _ => []
  | .const name => [name]
  | .pi A B | .sigma A B => constantNames A ++ constantNames B
  | .id A a b => constantNames A ++ constantNames a ++ constantNames b
  | .lam body => constantNames body
  | .app f a | .pair f a => constantNames f ++ constantNames a
  | .fst p | .snd p | .refl p => constantNames p

@[simp] theorem constantNames_rename (rho : Ren n m) (term : Tm Head n) :
    constantNames (rename rho term) = constantNames term := by
  induction term generalizing m <;> simp_all [rename, constantNames]

@[simp] theorem constantNames_liftClosed (term : Tm Head 0) :
    constantNames (liftClosed term : Tm Head n) = constantNames term :=
  constantNames_rename Fin.elim0 term

/-- Simultaneous replacement of constants by closed bodies. -/
def expand (bodies : Bodies Head) {n : Nat} : Tm Head n → Tm Head n
  | .var i => .var i
  | .const c => liftClosed (bodies c)
  | .head h => .head h
  | .pi A B => .pi (expand bodies A) (expand bodies B)
  | .sigma A B => .sigma (expand bodies A) (expand bodies B)
  | .id A a b => .id (expand bodies A) (expand bodies a) (expand bodies b)
  | .lam body => .lam (expand bodies body)
  | .app f a => .app (expand bodies f) (expand bodies a)
  | .pair a b => .pair (expand bodies a) (expand bodies b)
  | .fst p => .fst (expand bodies p)
  | .snd p => .snd (expand bodies p)
  | .refl a => .refl (expand bodies a)

/-- Expansion replaces each constant occurrence's support by the support of
its selected body, preserving order and multiplicity even below binders. -/
theorem constantNames_expand (bodies : Bodies Head) (term : Tm Head n) :
    constantNames (expand bodies term) =
      (constantNames term).flatMap (fun name => constantNames (bodies name)) := by
  induction term <;> simp_all [expand, constantNames, List.flatMap_append]

/-- Expansion reads only the constants actually occurring in the term. -/
theorem expand_eq_of_agreement (first second : Bodies Head) (term : Tm Head n)
    (agree : ∀ name ∈ constantNames term, first name = second name) :
    expand first term = expand second term := by
  induction term <;>
    simp_all [constantNames, expand, List.mem_append, or_imp, forall_and]

@[simp] theorem expand_identity (term : Tm Head n) :
    expand (fun name => .const name) term = term := by
  induction term <;> simp_all only [expand, liftClosed, rename]

@[simp] theorem expand_rename (bodies : Bodies Head) (rho : Ren n m)
    (term : Tm Head n) :
    expand bodies (rename rho term) = rename rho (expand bodies term) := by
  induction term generalizing m with
  | var i => rfl
  | const c => exact (rename_liftClosed rho (bodies c)).symm
  | head h => rfl
  | pi A B ihA ihB => simp only [rename, expand, ihA, ihB]
  | sigma A B ihA ihB => simp only [rename, expand, ihA, ihB]
  | id A a b ihA iha ihb => simp only [rename, expand, ihA, iha, ihb]
  | lam body ih => simp only [rename, expand, ih]
  | app f a ihf iha => simp only [rename, expand, ihf, iha]
  | pair a b iha ihb => simp only [rename, expand, iha, ihb]
  | fst p ih => simp only [rename, expand, ih]
  | snd p ih => simp only [rename, expand, ih]
  | refl a ih => simp only [rename, expand, ih]

@[simp] theorem expand_liftClosed (bodies : Bodies Head) (term : Tm Head 0) :
    expand bodies (liftClosed term : Tm Head n) = liftClosed (expand bodies term) :=
  expand_rename bodies Fin.elim0 term

theorem expand_liftSub (bodies : Bodies Head) (sigma : Sub Head n m) :
    (fun i => expand bodies (liftSub sigma i)) =
      liftSub (fun i => expand bodies (sigma i)) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    exact expand_rename bodies wk (sigma j)

/-- Closedness of replacement bodies prevents capture beneath every binder. -/
@[simp] theorem expand_subst (bodies : Bodies Head) (sigma : Sub Head n m)
    (term : Tm Head n) :
    expand bodies (subst sigma term) =
      subst (fun i => expand bodies (sigma i)) (expand bodies term) := by
  induction term generalizing m with
  | var i => rfl
  | const c => exact (subst_liftClosed _ (bodies c)).symm
  | head h => rfl
  | pi A B ihA ihB => simp only [subst, expand, ihA, ihB, expand_liftSub]
  | sigma A B ihA ihB => simp only [subst, expand, ihA, ihB, expand_liftSub]
  | id A a b ihA iha ihb => simp only [subst, expand, ihA, iha, ihb]
  | lam body ih => simp only [subst, expand, ih, expand_liftSub]
  | app f a ihf iha => simp only [subst, expand, ihf, iha]
  | pair a b iha ihb => simp only [subst, expand, iha, ihb]
  | fst p ih => simp only [subst, expand, ih]
  | snd p ih => simp only [subst, expand, ih]
  | refl a ih => simp only [subst, expand, ih]

@[simp] theorem expand_inst0 (bodies : Bodies Head) (argument : Tm Head n)
    (body : Tm Head (n + 1)) :
    expand bodies (inst0 argument body) =
      inst0 (expand bodies argument) (expand bodies body) := by
  rw [inst0, expand_subst, inst0]
  congr 1
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

/-- Conversion of each named constant to its selected body suffices for
conversion of every open term to its expansion. -/
theorem term_conv_expand (bodies : Bodies Head)
    {headEq : Head → Head → Prop} {root : RootComputation Head}
    (constants : ∀ name, Conv headEq (.const name) (bodies name) root)
    (term : Tm Head n) : Conv headEq term (expand bodies term) root := by
  induction term with
  | var i => exact .refl _
  | const c => exact (constants c).renameTerms Fin.elim0
  | head h => exact .refl _
  | pi A B ihA ihB => exact Conv.congPi ihA ihB
  | sigma A B ihA ihB => exact Conv.congSigma ihA ihB
  | id A a b ihA iha ihb => exact Conv.congId ihA iha ihb
  | lam body ih => exact Conv.congLam ih
  | app f a ihf iha => exact Conv.congApp ihf iha
  | pair a b iha ihb => exact Conv.congPair iha ihb
  | fst p ih => exact Conv.mapCompatible Tm.fst (fun h => .congFst h) ih
  | snd p ih => exact Conv.mapCompatible Tm.snd (fun h => .congSnd h) ih
  | refl a ih => exact Conv.mapCompatible Tm.refl (fun h => .congRefl h) ih

/-- Primitive root conversions, together with the binding laws above,
transport every contextual step, including beta and projections. -/
theorem step_expand (bodies : Bodies Head)
    {headEq : Head → Head → Prop} {source target : RootComputation Head}
    (roots : ∀ {k : Nat} {left right : Tm Head k}, source.step left right →
      Conv headEq (expand bodies left) (expand bodies right) target)
    {left right : Tm Head n} (step : Step headEq left right source) :
    Conv headEq (expand bodies left) (expand bodies right) target := by
  induction step with
  | betaPi body argument =>
      simpa only [expand, expand_inst0] using
        (Relation.EqvGen.rel _ _
          (Step.betaPi (root := target) (headEq := headEq)
            (expand bodies body) (expand bodies argument)))
  | betaSigmaFst a b => exact .rel _ _ (.betaSigmaFst _ _)
  | betaSigmaSnd a b => exact .rel _ _ (.betaSigmaSnd _ _)
  | head equality => exact .rel _ _ (.head equality)
  | root equation => exact roots equation
  | congPiDom _ ih => exact Conv.congPi ih (.refl _)
  | congPiCod _ ih => exact Conv.congPi (.refl _) ih
  | congSigmaDom _ ih => exact Conv.congSigma ih (.refl _)
  | congSigmaCod _ ih => exact Conv.congSigma (.refl _) ih
  | congIdTy _ ih => exact Conv.congId ih (.refl _) (.refl _)
  | congIdLeft _ ih => exact Conv.congId (.refl _) ih (.refl _)
  | congIdRight _ ih => exact Conv.congId (.refl _) (.refl _) ih
  | congLam _ ih => exact Conv.congLam ih
  | congAppFun _ ih => exact Conv.congApp ih (.refl _)
  | congAppArg _ ih => exact Conv.congApp (.refl _) ih
  | congPairFst _ ih => exact Conv.congPair ih (.refl _)
  | congPairSnd _ ih => exact Conv.congPair (.refl _) ih
  | congFst _ ih => exact Conv.mapCompatible Tm.fst (fun h => .congFst h) ih
  | congSnd _ ih => exact Conv.mapCompatible Tm.snd (fun h => .congSnd h) ih
  | congRefl _ ih => exact Conv.mapCompatible Tm.refl (fun h => .congRefl h) ih

theorem conv_expand (bodies : Bodies Head)
    {headEq : Head → Head → Prop} {source target : RootComputation Head}
    (roots : ∀ {k : Nat} {left right : Tm Head k}, source.step left right →
      Conv headEq (expand bodies left) (expand bodies right) target)
    {left right : Tm Head n} (conversion : Conv headEq left right source) :
    Conv headEq (expand bodies left) (expand bodies right) target := by
  induction conversion with
  | rel _ _ step => exact step_expand bodies roots step
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ihFirst ihSecond => exact .trans _ _ _ ihFirst ihSecond

/-- Relative expansion preserves and reflects conversion when target roots
remain source roots and every expanded source root converts in the target.
The target may retain native computation; it need not be root-empty. -/
theorem conversion_iff_of_roots (bodies : Bodies Head)
    {headEq : Head → Head → Prop} {source target : RootComputation Head}
    (constants : ∀ name, Conv headEq (.const name) (bodies name) source)
    (roots : ∀ {k : Nat} {left right : Tm Head k}, source.step left right →
      Conv headEq (expand bodies left) (expand bodies right) target)
    (included : ∀ {k : Nat} {left right : Tm Head k},
      target.step left right → source.step left right)
    (left right : Tm Head n) :
    Conv headEq left right source ↔
      Conv headEq (expand bodies left) (expand bodies right) target := by
  constructor
  · exact conv_expand bodies roots
  · intro conversion
    have retained : Conv headEq (expand bodies left) (expand bodies right) source := by
      simpa only [Tm.mapHead_id] using conversion.mapHead
        (fun head => head) (fun equality => equality)
        (targetRoot := source)
        (by intro k a b root; simpa only [Tm.mapHead_id] using included root)
    exact .trans _ _ _ (term_conv_expand bodies constants left)
      (.trans _ _ _ retained (.symm _ _ (term_conv_expand bodies constants right)))

#print axioms expand_eq_of_agreement
#print axioms constantNames_expand
#print axioms expand_identity
#print axioms expand_rename
#print axioms expand_liftClosed
#print axioms expand_liftSub
#print axioms expand_subst
#print axioms expand_inst0
#print axioms term_conv_expand
#print axioms step_expand
#print axioms conv_expand
#print axioms conversion_iff_of_roots

end ConstantExpansion
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.ConstantSubstitution

variable {Head : Type} {n m k : Nat}

/-- Native values for primitive names may depend on the target telescope. -/
abbrev Values (Head : Type) (scope : Nat) := DeclName → Tm Head scope

def liftValues (values : Values Head m) : Values Head (m + 1) :=
  fun name => rename wk (values name)

/-- Simultaneously interpret primitive constants and substitute source
variables. Each binder weakens the primitive values and lifts the variable
substitution; inserted values are not recursively reinterpreted. -/
def interpret : {n m : Nat} → Values Head m → Sub Head n m → Tm Head n → Tm Head m
  | _, _, _, variables, .var index => variables index
  | _, _, values, _, .const name => values name
  | _, _, _, _, .head head => .head head
  | _, _, values, variables, .pi domain codomain => .pi (interpret values variables domain)
      (interpret (liftValues values) (liftSub variables) codomain)
  | _, _, values, variables, .sigma domain codomain => .sigma (interpret values variables domain)
      (interpret (liftValues values) (liftSub variables) codomain)
  | _, _, values, variables, .id type left right => .id (interpret values variables type)
      (interpret values variables left) (interpret values variables right)
  | _, _, values, variables, .lam body => .lam (interpret (liftValues values) (liftSub variables) body)
  | _, _, values, variables, .app function argument => .app (interpret values variables function) (interpret values variables argument)
  | _, _, values, variables, .pair first second => .pair (interpret values variables first) (interpret values variables second)
  | _, _, values, variables, .fst pair => .fst (interpret values variables pair)
  | _, _, values, variables, .snd pair => .snd (interpret values variables pair)
  | _, _, values, variables, .refl term => .refl (interpret values variables term)

private theorem liftSub_precompose (variables : Sub Head m k) (action : Ren n m) :
    (fun index => liftSub variables (liftRen action index)) =
      liftSub (fun index => variables (action index)) := by
  funext index
  exact liftSub_liftRen_apply variables action index

/-- Source renaming changes only the submitted variable assignment. -/
theorem interpret_rename (values : Values Head k) (variables : Sub Head m k)
    (action : Ren n m) (term : Tm Head n) :
    interpret values variables (rename action term) =
      interpret values (fun index => variables (action index)) term := by
  induction term generalizing m k with
  | pi domain codomain ihDomain ihCodomain =>
      simp only [interpret, rename, ihDomain, ihCodomain, liftSub_precompose]
  | sigma domain codomain ihDomain ihCodomain =>
      simp only [interpret, rename, ihDomain, ihCodomain, liftSub_precompose]
  | lam body ih => simp only [interpret, rename, ih, liftSub_precompose]
  | _ => simp_all only [interpret, rename]

private theorem rename_liftValues (values : Values Head m) (action : Ren m k) :
    (fun name => rename (liftRen action) (liftValues values name)) =
      liftValues (fun name => rename action (values name)) := by
  funext name
  simp only [liftValues, rename_comp]
  rfl

private theorem rename_liftVariables (variables : Sub Head n m) (action : Ren m k) :
    (fun index => rename (liftRen action) (liftSub variables index)) =
      liftSub (fun index => rename action (variables index)) := by
  funext index
  exact rename_liftSub action variables index

/-- Native weakening acts on both supplied primitive values and variables. -/
theorem rename_interpret (values : Values Head m) (variables : Sub Head n m)
    (action : Ren m k) (term : Tm Head n) :
    rename action (interpret values variables term) =
      interpret (fun name => rename action (values name))
        (fun index => rename action (variables index)) term := by
  induction term generalizing m k with
  | pi domain codomain ihDomain ihCodomain =>
      simp only [interpret, rename, ihDomain, ihCodomain, rename_liftValues, rename_liftVariables]
  | sigma domain codomain ihDomain ihCodomain =>
      simp only [interpret, rename, ihDomain, ihCodomain, rename_liftValues, rename_liftVariables]
  | lam body ih => simp only [interpret, rename, ih, rename_liftValues, rename_liftVariables]
  | _ => simp_all only [interpret, rename]

private theorem subst_liftValues (values : Values Head m) (action : Sub Head m k) :
    (fun name => subst (liftSub action) (liftValues values name)) =
      liftValues (fun name => subst action (values name)) := by
  funext name
  exact subst_liftSub_wk action (values name)

private theorem subst_liftVariables (variables : Sub Head n m) (action : Sub Head m k) :
    (fun index => subst (liftSub action) (liftSub variables index)) =
      liftSub (fun index => subst action (variables index)) := by
  funext index
  exact liftSub_comp_apply action variables index

/-- Specializing native parameters commutes with the complete interpretation,
including every binder. This does not enumerate primitive function values. -/
theorem subst_interpret (values : Values Head m) (variables : Sub Head n m)
    (action : Sub Head m k) (term : Tm Head n) :
    subst action (interpret values variables term) =
      interpret (fun name => subst action (values name))
        (fun index => subst action (variables index)) term := by
  induction term generalizing m k with
  | pi domain codomain ihDomain ihCodomain =>
      simp only [interpret, subst, ihDomain, ihCodomain, subst_liftValues, subst_liftVariables]
  | sigma domain codomain ihDomain ihCodomain =>
      simp only [interpret, subst, ihDomain, ihCodomain, subst_liftValues, subst_liftVariables]
  | lam body ih => simp only [interpret, subst, ih, subst_liftValues, subst_liftVariables]
  | _ => simp_all only [interpret, subst]

/-- A lifted source assignment is interpreted with the lifted target values. -/
private theorem interpret_liftVariables (values : Values Head k)
    (variables : Sub Head m k) (action : Sub Head n m) :
    (fun index => interpret (liftValues values) (liftSub variables) (liftSub action index)) =
      liftSub (fun index => interpret values variables (action index)) := by
  funext index
  refine Fin.cases ?_ (fun prior => ?_) index
  · rfl
  · simp only [liftSub_succ, interpret_rename, rename_interpret]
    rfl

/-- Source substitution and primitive interpretation commute with the original
capture-aware native substitution, including beneath every binder. -/
theorem interpret_subst (values : Values Head k) (variables : Sub Head m k)
    (action : Sub Head n m) (term : Tm Head n) :
    interpret values variables (subst action term) =
      interpret values (fun index => interpret values variables (action index)) term := by
  induction term generalizing m k with
  | pi domain codomain ihDomain ihCodomain =>
      simp only [interpret, subst, ihDomain, ihCodomain, interpret_liftVariables]
  | sigma domain codomain ihDomain ihCodomain =>
      simp only [interpret, subst, ihDomain, ihCodomain, interpret_liftVariables]
  | lam body ih => simp only [interpret, subst, ih, interpret_liftVariables]
  | _ => simp_all only [interpret, subst]

/-- Opening the newest source binder becomes the actual target beta
substitution. Primitive values stay in their original target context. -/
theorem interpret_inst0 (values : Values Head m) (variables : Sub Head n m)
    (argument : Tm Head n) (body : Tm Head (n + 1)) :
    interpret values variables (inst0 argument body) =
      inst0 (interpret values variables argument)
        (interpret (liftValues values) (liftSub variables) body) := by
  rw [inst0, interpret_subst, inst0, subst_interpret]
  have constants :
      (fun name => subst (subst0 (interpret values variables argument)) (liftValues values name)) =
        values := by
    funext name
    exact inst0_rename_wk _ (values name)
  rw [constants]
  congr 1
  funext index
  refine Fin.cases ?_ (fun prior => ?_) index
  · rfl
  · exact (inst0_rename_wk _ (variables prior)).symm

@[simp] theorem liftValues_constants :
    liftValues (fun name => (.const name : Tm Head m)) =
      (fun name => (.const name : Tm Head (m + 1))) := rfl

@[simp] theorem liftValues_closed (values : ConstantExpansion.Bodies Head) :
    liftValues (fun name => (liftClosed (values name) : Tm Head m)) =
      (fun name => (liftClosed (values name) : Tm Head (m + 1))) := by
  funext name
  exact rename_liftClosed wk (values name)

/-- Ordinary simultaneous substitution is the unchanged-constant case. -/
theorem interpret_constants (variables : Sub Head n m) (term : Tm Head n) :
    interpret (fun name => .const name) variables term = subst variables term := by
  induction term generalizing m <;>
    simp_all only [interpret, subst, liftValues_constants]

/-- Existing closed constant expansion is recovered on the original syntax. -/
theorem interpret_closed (values : ConstantExpansion.Bodies Head) (term : Tm Head n) :
    interpret (fun name => liftClosed (values name)) ids term = ConstantExpansion.expand values term := by
  induction term <;>
    simp_all only [interpret, ConstantExpansion.expand, liftValues_closed, liftSub_ids, ids]


@[simp] theorem interpret_liftClosed (values : Values Head m) (variables : Sub Head n m)
    (term : Tm Head 0) :
    interpret values variables (liftClosed term) = interpret values Fin.elim0 term := by
  rw [liftClosed, interpret_rename]
  congr 1
  funext index
  exact Fin.elim0 index

@[simp] theorem rename_interpret_closed (values : Values Head m) (action : Ren m k)
    (term : Tm Head 0) :
    rename action (interpret values Fin.elim0 term) =
      interpret (fun name => rename action (values name)) Fin.elim0 term := by
  rw [rename_interpret]
  congr 1
  funext index
  exact Fin.elim0 index

@[simp] theorem interpret_weaken (values : Values Head m) (variables : Sub Head n m)
    (term : Tm Head n) :
    interpret (liftValues values) (liftSub variables) (rename wk term) =
      rename wk (interpret values variables term) := by
  rw [interpret_rename, rename_interpret]
  rfl

/-- Root-free templates still have their ordinary native beta computations.
The selected target may provide additional separately authorized root rules. -/
def RootFree (computation : RootComputation Head) : Prop :=
  ∀ {scope : Nat} {first last : Tm Head scope}, ¬ computation.step first last

theorem step_interpret
    {sourceHeads targetHeads : Head → Head → Prop}
    (heads : ∀ {first last}, sourceHeads first last → targetHeads first last)
    {sourceRoot targetRoot : RootComputation Head} (rootFree : RootFree sourceRoot)
    {first last : Tm Head n} (step : Step sourceHeads first last sourceRoot) :
    ∀ {m : Nat} (values : Values Head m) (variables : Sub Head n m),
      Step targetHeads (interpret values variables first) (interpret values variables last) targetRoot := by
  induction step with
  | betaPi body argument =>
      intro m values variables
      simpa only [interpret, interpret_inst0] using
        (Step.betaPi (headEq := targetHeads) (root := targetRoot)
          (interpret (liftValues values) (liftSub variables) body) (interpret values variables argument))
  | betaSigmaFst first second => intro m values variables; exact .betaSigmaFst _ _
  | betaSigmaSnd first second => intro m values variables; exact .betaSigmaSnd _ _
  | head equality => intro m values variables; exact .head (heads equality)
  | root computation => exact False.elim (rootFree computation)
  | congPiDom step ih => intro m values variables; exact .congPiDom (ih values variables)
  | congPiCod step ih => intro m values variables; exact .congPiCod (ih (liftValues values) (liftSub variables))
  | congSigmaDom step ih => intro m values variables; exact .congSigmaDom (ih values variables)
  | congSigmaCod step ih => intro m values variables; exact .congSigmaCod (ih (liftValues values) (liftSub variables))
  | congIdTy step ih => intro m values variables; exact .congIdTy (ih values variables)
  | congIdLeft step ih => intro m values variables; exact .congIdLeft (ih values variables)
  | congIdRight step ih => intro m values variables; exact .congIdRight (ih values variables)
  | congLam step ih => intro m values variables; exact .congLam (ih (liftValues values) (liftSub variables))
  | congAppFun step ih => intro m values variables; exact .congAppFun (ih values variables)
  | congAppArg step ih => intro m values variables; exact .congAppArg (ih values variables)
  | congPairFst step ih => intro m values variables; exact .congPairFst (ih values variables)
  | congPairSnd step ih => intro m values variables; exact .congPairSnd (ih values variables)
  | congFst step ih => intro m values variables; exact .congFst (ih values variables)
  | congSnd step ih => intro m values variables; exact .congSnd (ih values variables)
  | congRefl step ih => intro m values variables; exact .congRefl (ih values variables)

theorem conversion_interpret
    {sourceHeads targetHeads : Head → Head → Prop}
    (heads : ∀ {first last}, sourceHeads first last → targetHeads first last)
    {sourceRoot targetRoot : RootComputation Head} (rootFree : RootFree sourceRoot)
    {first last : Tm Head n} (conversion : Conv sourceHeads first last sourceRoot)
    (values : Values Head m) (variables : Sub Head n m) :
    Conv targetHeads (interpret values variables first) (interpret values variables last) targetRoot := by
  induction conversion with
  | rel first last step => exact .rel _ _ (step_interpret heads rootFree step values variables)
  | refl term => exact .refl _
  | symm first last conversion ih => exact .symm _ _ ih
  | trans first middle last left right ihLeft ihRight => exact .trans _ _ _ ihLeft ihRight

/-- Select primitive constant occurrences to become actual telescope variables.
Names outside the selected finite parameters keep their original declarations. -/
def parameterValues (positions : DeclName → Option (Fin k)) : Values Head k :=
  fun name => match positions name with
    | some index => .var index
    | none => .const name

def specializedValues (positions : DeclName → Option (Fin k)) (arguments : Sub Head k m) :
    Values Head m :=
  fun name => match positions name with
    | some index => arguments index
    | none => .const name

def parameterTerm (positions : DeclName → Option (Fin k)) (term : Tm Head 0) : Tm Head k :=
  interpret (parameterValues positions) Fin.elim0 term

/-- A single parameterized term specializes by ordinary native simultaneous
substitution. Function arguments may be arbitrary well-scoped native values. -/
theorem parameterTerm_specialize (positions : DeclName → Option (Fin k))
    (arguments : Sub Head k m) (term : Tm Head 0) :
    subst arguments (parameterTerm positions term) =
      interpret (specializedValues positions arguments) Fin.elim0 term := by
  rw [parameterTerm, subst_interpret]
  congr 1
  · funext name
    cases chosen : positions name <;>
      simp only [parameterValues, specializedValues, chosen, subst]
  · funext index
    exact Fin.elim0 index


end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.ConstantSubstitution

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.ConstantSubstitution

variable {Head : Type} {n m k : Nat}

/-- Interpretation depends only on the primitive names actually used in the
submitted term, including below binders. -/
theorem interpret_eq_of_agreement (first last : Values Head m) (variables : Sub Head n m)
    (term : Tm Head n)
    (agree : ∀ name ∈ ConstantExpansion.constantNames term, first name = last name) :
    interpret first variables term = interpret last variables term := by
  induction term generalizing m with
  | pi domain codomain ihDomain ihCodomain =>
      apply congrArg₂ Tm.pi
      · apply ihDomain first last variables
        intro name member
        exact agree name (List.mem_append_left _ member)
      · apply ihCodomain (liftValues first) (liftValues last) (liftSub variables)
        intro name member
        exact congrArg (rename wk) (agree name (List.mem_append_right _ member))
  | sigma domain codomain ihDomain ihCodomain =>
      apply congrArg₂ Tm.sigma
      · apply ihDomain first last variables
        intro name member
        exact agree name (List.mem_append_left _ member)
      · apply ihCodomain (liftValues first) (liftValues last) (liftSub variables)
        intro name member
        exact congrArg (rename wk) (agree name (List.mem_append_right _ member))
  | lam body ih =>
      apply congrArg Tm.lam
      apply ih (liftValues first) (liftValues last) (liftSub variables)
      intro name member
      exact congrArg (rename wk) (agree name member)
  | var index => rfl
  | const name => exact agree name (by simp only [ConstantExpansion.constantNames, List.mem_singleton])
  | head head => rfl
  | app function argument ihFunction ihArgument =>
      apply congrArg₂ Tm.app
      · exact ihFunction first last variables (fun name member => agree name (List.mem_append_left _ member))
      · exact ihArgument first last variables (fun name member => agree name (List.mem_append_right _ member))
  | pair left right ihLeft ihRight =>
      apply congrArg₂ Tm.pair
      · exact ihLeft first last variables (fun name member => agree name (List.mem_append_left _ member))
      · exact ihRight first last variables (fun name member => agree name (List.mem_append_right _ member))
  | id type left right ihType ihLeft ihRight =>
      simp only [interpret]
      rw [ihType first last variables (fun name member => agree name
          (List.mem_append_left _ (List.mem_append_left _ member))),
        ihLeft first last variables (fun name member => agree name
          (List.mem_append_left _ (List.mem_append_right _ member))),
        ihRight first last variables (fun name member => agree name (List.mem_append_right _ member))]

  | fst pair ih => exact congrArg Tm.fst (ih first last variables agree)
  | snd pair ih => exact congrArg Tm.snd (ih first last variables agree)
  | refl term ih => exact congrArg Tm.refl (ih first last variables agree)

/-- A type whose primitive names are not abstracted retains its exact closed
declaration type in the parameter context. -/
theorem parameterTerm_eq_liftClosed (positions : DeclName → Option (Fin k))
    (type : Tm Head 0)
    (unselected : ∀ name ∈ ConstantExpansion.constantNames type, positions name = none) :
    parameterTerm positions type = (liftClosed type : Tm Head k) := by
  unfold parameterTerm
  rw [interpret_eq_of_agreement (parameterValues positions) (fun name => .const name)
    Fin.elim0 type (by
      intro name member
      simp only [parameterValues, unselected name member])]
  rw [interpret_constants]
  change subst Fin.elim0 type = rename Fin.elim0 type
  rw [← subst_renSub (rho := Fin.elim0)]
  apply subst_ext
  intro index
  exact Fin.elim0 index

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.ConstantSubstitution

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.ConstantExpansion

variable {Head : Type}

/-- Sequential closed interpretations compose by interpreting each primitive
body. Inserted bodies are traversed only by the subsequent interpretation. -/
theorem expand_comp (first last : Bodies Head) {n : Nat} (term : Tm Head n) :
    expand last (expand first term) = expand (fun name => expand last (first name)) term := by
  induction term <;> simp_all only [expand, expand_liftClosed]

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.ConstantExpansion

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.ConstantSubstitution

theorem RootFree.eq_empty {Head : Type} {root : RootComputation Head} (empty : RootFree root) :
    root = RootComputation.empty := by
  cases root with
  | mk step hRename hSubstitute =>
      have same : @step = @(RootComputation.empty (Head := Head)).step := by
        funext scope first last
        exact propext ⟨fun present => empty present, False.elim⟩
      cases same
      rfl


end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.ConstantSubstitution


namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.ConstantSubstitution

variable {Head : Type} {n m : Nat}

private theorem liftValues_interpretedConstants (values : Values Head m)
    (constants : ConstantExpansion.Bodies Head) :
    liftValues (fun name => interpret values Fin.elim0 (constants name)) =
      (fun name => interpret (liftValues values) Fin.elim0 (constants name)) := by
  funext name
  exact rename_interpret_closed values wk (constants name)

/-- Interpreting a closed expansion specializes each primitive closed image;
no already inserted function value is interpreted a second time. -/
theorem interpret_expand (values : Values Head m) (variables : Sub Head n m)
    (constants : ConstantExpansion.Bodies Head) (term : Tm Head n) :
    interpret values variables (ConstantExpansion.expand constants term) =
      interpret (fun name => interpret values Fin.elim0 (constants name)) variables term := by
  induction term generalizing m <;>
    simp_all only [ConstantExpansion.expand, interpret, interpret_liftClosed,
      liftValues_interpretedConstants]

private theorem expand_liftValues (constants : ConstantExpansion.Bodies Head)
    (values : Values Head m) :
    (fun name => ConstantExpansion.expand constants (liftValues values name)) =
      liftValues (fun name => ConstantExpansion.expand constants (values name)) := by
  funext name
  exact ConstantExpansion.expand_rename constants wk (values name)

/-- Closed operator expansion acts on the supplied function values and
variable values while preserving the existing simultaneous interpretation. -/
theorem expand_interpret (constants : ConstantExpansion.Bodies Head)
    (values : Values Head m) (variables : Sub Head n m) (term : Tm Head n) :
    ConstantExpansion.expand constants (interpret values variables term) =
      interpret (fun name => ConstantExpansion.expand constants (values name))
        (fun index => ConstantExpansion.expand constants (variables index)) term := by
  induction term generalizing m <;>
    simp_all only [interpret, ConstantExpansion.expand,
      ConstantExpansion.expand_liftSub, expand_liftValues]


end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.ConstantSubstitution
