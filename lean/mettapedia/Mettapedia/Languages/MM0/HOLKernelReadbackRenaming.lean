import Mettapedia.Languages.MM0.HOLKernelLogicalFunctionReadback
import Mettapedia.Logic.HOL.Syntax.DecidableEq
import Mettapedia.Languages.MM0.HOLKernelJudgmentReadback
import Mettapedia.Languages.MM0.HOLKernelRuleReadback

/-!
# Renaming and fresh-frame extension for native HOL readback

A name-frame map preserves variable lookup below a stated bound. The native
term reader commutes with the associated intrinsic renaming on expressions
within that bound, including lambda and quantifier bodies. The logical-function
dictionary is natural, so the same comparison holds for mixed judgments and
for formulas after licensed Boolean-equivalence expansion.

Adding a name beyond the bound gives weakening. A captured-name control
separates this operation from inserting a colliding name. All structural and nonbinding local rule readings commute with this frame
change, retaining their exact theorem declarations and native instances.

A partial-map embedding gives a second law: every successful reading is
preserved, even if newly bound names let previously unresolved expressions
be read. A fresh variable disjoint from the constant dictionary therefore
weakens any successful term reading, without bounding its internal binders.
This law deliberately does not preserve failed readings; the bounded exact-map
law above retains that stronger conclusion under its stronger hypotheses. Whole
proof-tree admission through context-changing binding steps is separate.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelTermReadback
open Mettapedia.Logic Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax
open NamedElaboration (BinderNames SomeVar SomeTerm)
universe u
variable {Const : Ty Unit → Type u} {gamma delta : Ctx Unit}

def Decoded.rename (rho : Rename Unit gamma delta) (source : Decoded Const gamma) : Decoded Const delta :=
  ⟨source.type, HOL.rename rho source.term⟩

theorem varsBelow_var {bound index : Nat} (bounded : Preterm.VarsBelow bound (.var index)) : index < bound := bounded

theorem varsBelow_function {bound : Nat} {function argument : Preterm}
    (bounded : Preterm.VarsBelow bound (.app function argument)) : Preterm.VarsBelow bound function := bounded.1

theorem varsBelow_argument {bound : Nat} {function argument : Preterm}
    (bounded : Preterm.VarsBelow bound (.app function argument)) : Preterm.VarsBelow bound argument := bounded.2

def NamesRel (bound : Nat) (rho : Rename Unit gamma delta) (source : Names gamma) (target : Names delta) : Prop :=
  ∀ index < bound, target.lookup? index =
    (source.lookup? index).map (fun resolved => ⟨resolved.1, rho resolved.2⟩)

theorem NamesRel.cons {bound : Nat} {rho : Rename Unit gamma delta} {source : Names gamma} {target : Names delta}
    (related : NamesRel bound rho source target) (domain : Ty Unit) (binder : Nat) :
    NamesRel bound (Rename.lift rho) (BinderNames.cons (type := domain) binder source)
      (BinderNames.cons (type := domain) binder target) := by
  intro index smaller
  by_cases same : binder = index
  · subst index
    simp [Rename.lift]
  · rw [BinderNames.lookup?_cons_of_ne same, BinderNames.lookup?_cons_of_ne same,
      related index smaller]
    cases source.lookup? index <;> rfl

theorem NamesRel.weaken {bound : Nat} (source : Names gamma) (domain : Ty Unit) (fresh : Nat)
    (later : bound ≤ fresh) :
    NamesRel bound (fun {_} index => Var.vs (σ := domain) index) source (BinderNames.cons fresh source) := by
  intro index smaller
  have different : fresh ≠ index := by omega
  rw [BinderNames.lookup?_cons_of_ne different]

theorem expect_rename (rho : Rename Unit gamma delta) (expected : Ty Unit) (source : Decoded Const gamma) :
    expect expected (source.rename rho) = (expect expected source).map (HOL.rename rho) := by
  rcases source with ⟨type, term⟩
  by_cases same : type = expected
  · subst type
    simp [Decoded.rename, expect_same]
  · simp only [expect, NamedElaboration.expectType, Decoded.rename, same, ↓reduceDIte]
    rfl

theorem readVariable_rename (constants : Nat → Option (NamedElaboration.SomeConst Const))
    {bound : Nat} {rho : Rename Unit gamma delta} {source : Names gamma} {target : Names delta}
    (related : NamesRel bound rho source target) (index : Nat) (smaller : index < bound) :
    readVariable constants target index = (readVariable constants source index).map (Decoded.rename rho) := by
  unfold readVariable
  rw [related index smaller]
  cases source.lookup? index with
  | none => cases constants index <;> rfl
  | some resolved => rfl


theorem application_rename (rho : Rename Unit gamma delta) (function argument : Decoded Const gamma) :
    application (function.rename rho) (argument.rename rho) =
      (application function argument).map (Decoded.rename rho) := by
  rcases function with ⟨type, term⟩
  cases type with
  | base name => rfl
  | prop => rfl
  | arr domain codomain =>
      change (expect domain (argument.rename rho)).map
        (fun value => (⟨codomain, Term.app (HOL.rename rho term) value⟩ : Decoded Const delta)) =
        ((expect domain argument).map (fun value => (⟨codomain, Term.app term value⟩ : Decoded Const gamma))).map
          (Decoded.rename rho)
      rw [expect_rename]
      cases expect domain argument <;> rfl

theorem logicalBinary_rename (rho : Rename Unit gamma delta)
    (sourceOp : Formula Const gamma → Formula Const gamma → Formula Const gamma)
    (targetOp : Formula Const delta → Formula Const delta → Formula Const delta)
    (natural : ∀ first second, HOL.rename rho (sourceOp first second) =
      targetOp (HOL.rename rho first) (HOL.rename rho second))
    (first second : Decoded Const gamma) :
    logicalBinary targetOp (first.rename rho) (second.rename rho) =
      (logicalBinary sourceOp first second).map (Decoded.rename rho) := by
  simp only [logicalBinary, expect_rename]
  cases hfirst : expect .prop first <;> cases hsecond : expect .prop second <;>
    simp [Decoded.rename, natural]


theorem readTermWith_rename
    (extras : {context : Ctx Unit} → Preterm → Option (Decoded Const context))
    (extrasNatural : ∀ {first second : Ctx Unit} (rho : Rename Unit first second) (native : Preterm),
      extras (context := second) native = (extras (context := first) native).map (Decoded.rename rho))
    (references : HOLKernelSyntax.Symbol → Nat)
    (constants : Nat → Option (NamedElaboration.SomeConst Const)) (parameters bound : Nat)
    (sourceNames : Names gamma) (native : Preterm) :
    ∀ {delta : Ctx Unit} (rho : Rename Unit gamma delta) (targetNames : Names delta),
      NamesRel bound rho sourceNames targetNames → Preterm.VarsBelow bound native →
      readTermWith extras references constants parameters targetNames native =
        (readTermWith extras references constants parameters sourceNames native).map (Decoded.rename rho) := by
  induction gamma, sourceNames, native using readTermWith.induct references parameters with
  | case1 gamma index names =>
      intro delta rho target related bounded
      simpa only [readTermWith] using readVariable_rename constants related index (varsBelow_var bounded)
  | case2 gamma index head names =>
      intro delta rho target related bounded
      simp [readTermWith, head, Decoded.rename, HOL.rename]
  | case3 gamma index head names =>
      intro delta rho target related bounded
      simp [readTermWith, head, Decoded.rename, HOL.rename]
  | case4 gamma index names notTruth notFalse =>
      intro delta rho target related bounded
      simp [readTermWith, extrasNatural rho]
  | case5 gamma index body head names ih =>
      intro delta rho target related bounded
      have bodyRead := ih rho target related (varsBelow_argument bounded)
      simp only [readTermWith, head, ↓reduceIte, bodyRead]
      cases found : readTermWith extras references constants parameters names body with
      | none => simp []
      | some value =>
          simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, expect_rename]
          cases expect .prop value <;> rfl
  | case6 gamma index body notNot names =>
      intro delta rho target related bounded
      simp [readTermWith, notNot, extrasNatural rho]
  | case7 gamma index first second names ihFirst ihSecond =>
      intro delta rho target related bounded
      have firstRead := ihFirst rho target related (varsBelow_argument (varsBelow_function bounded))
      have secondRead := ihSecond rho target related (varsBelow_argument bounded)
      simp only [readTermWith, firstRead, secondRead]
      cases hfirst : readTermWith extras references constants parameters names first <;>
        cases hsecond : readTermWith extras references constants parameters names second <;>
        simp only [Option.map_none, Option.map_some,
          Option.bind_eq_bind, Option.bind_none, Option.bind_some]
      next firstValue secondValue =>
        cases hhead : readHead references index with
        | none => rfl
        | some symbol =>
            cases symbol <;> simp only [Option.map_none] <;>
              first | rfl | exact application_rename rho firstValue secondValue |
                exact logicalBinary_rename rho _ _ (fun _ _ => rfl) firstValue secondValue
  | case8 gamma index first second third head noType names =>
      intro delta rho target related bounded
      unfold readTermWith
      simp [head, noType]
  | case9 gamma index first second third head type foundType names ihSecond ihThird =>
      intro delta rho target related bounded
      have secondRead := ihSecond rho target related (varsBelow_argument (varsBelow_function bounded))
      have thirdRead := ihThird rho target related (varsBelow_argument bounded)
      unfold readTermWith
      simp only [head, foundType, secondRead, thirdRead]
      cases secondResult : readTermWith extras references constants parameters names second with
      | none => simp
      | some secondValue =>
          cases thirdResult : readTermWith extras references constants parameters names third with
          | none => simp
          | some thirdValue =>
              simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, expect_rename]
              cases expect type secondValue <;> cases expect type thirdValue <;> rfl
  | case10 gamma index second third head binder small names =>
      intro delta rho target related bounded
      simp [readTermWith, head, small]
  | case11 gamma index second third head binder large noType names =>
      intro delta rho target related bounded
      simp [readTermWith, head, large, noType]
  | case12 gamma index second third head binder large type foundType names ih =>
      intro delta rho target related bounded
      have bodyRead := ih (Rename.lift rho) (BinderNames.cons binder target)
        (related.cons type binder) (varsBelow_argument bounded)
      simp only [readTermWith, head, large, foundType, ↓reduceIte, bodyRead]
      cases readTermWith extras references constants parameters (BinderNames.cons (type := type) binder names) third <;> rfl
  | case13 gamma index first second third head names notVar =>
      intro delta rho target related bounded
      cases first with
      | var binder => exact False.elim (notVar binder rfl)
      | term symbol => simp [readTermWith, head]
      | app function argument => simp [readTermWith, head]
  | case14 gamma index second third head binder small names =>
      intro delta rho target related bounded
      simp [readTermWith, head, small]
  | case15 gamma index second third head binder large noType names =>
      intro delta rho target related bounded
      simp [readTermWith, head, large, noType]
  | case16 gamma index second third head binder large type foundType names ih =>
      intro delta rho target related bounded
      have bodyRead := ih (Rename.lift rho) (BinderNames.cons binder target)
        (related.cons type binder) (varsBelow_argument bounded)
      simp only [readTermWith, head, large, foundType, ↓reduceIte, bodyRead]
      cases result : readTermWith extras references constants parameters (BinderNames.cons (type := type) binder names) third with
      | none => simp []
      | some value =>
          simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, expect_rename]
          cases expect .prop value <;> rfl
  | case17 gamma index first second third head names notVar =>
      intro delta rho target related bounded
      cases first with
      | var binder => exact False.elim (notVar binder rfl)
      | term symbol => simp [readTermWith, head]
      | app function argument => simp [readTermWith, head]
  | case18 gamma index second third head binder small names =>
      intro delta rho target related bounded
      simp [readTermWith, head, small]
  | case19 gamma index second third head binder large noType names =>
      intro delta rho target related bounded
      simp [readTermWith, head, large, noType]
  | case20 gamma index second third head binder large type foundType names ih =>
      intro delta rho target related bounded
      have bodyRead := ih (Rename.lift rho) (BinderNames.cons binder target)
        (related.cons type binder) (varsBelow_argument bounded)
      simp only [readTermWith, head, large, foundType, ↓reduceIte, bodyRead]
      cases result : readTermWith extras references constants parameters (BinderNames.cons (type := type) binder names) third with
      | none => simp []
      | some value =>
          simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, expect_rename]
          cases expect .prop value <;> rfl
  | case21 gamma index first second third head names notVar =>
      intro delta rho target related bounded
      cases first with
      | var binder => exact False.elim (notVar binder rfl)
      | term symbol => simp [readTermWith, head]
      | app function argument => simp [readTermWith, head]
  | case22 gamma index first second third names noEq noLam noAll noEx =>
      intro delta rho target related bounded
      unfold readTermWith
      simp []
  | case23 gamma native noVar noTerm noUnary noBinary noTernary names =>
      intro delta rho target related bounded
      unfold readTermWith
      split <;> simp_all
      exact False.elim (noTernary _ _ _ _ rfl rfl rfl rfl)


theorem logical_value_rename (rho : Rename Unit gamma delta)
    (operator : HOLKernelLogicalOperations.Operator) (domain : Ty Unit) :
    (HOLKernelLogicalFunctionReadback.value operator domain : Decoded Const gamma).rename rho =
      (HOLKernelLogicalFunctionReadback.value operator domain : Decoded Const delta) := by
  cases operator <;> rfl

theorem logical_atoms_rename
    {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
    {theorems : TheoremSignature} {signature : Signature sorts terms}
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (rho : Rename Unit gamma delta) (native : Preterm) :
    (HOLKernelLogicalFunctionReadback.atoms profile native : Option (Decoded Const delta)) =
      (HOLKernelLogicalFunctionReadback.atoms profile native : Option (Decoded Const gamma)).map (Decoded.rename rho) := by
  cases native with
  | var index => rfl
  | term index =>
      simp only [HOLKernelLogicalFunctionReadback.atoms]
      split_ifs <;> simp [logical_value_rename]
  | app function argument =>
      cases function with
      | var index => rfl
      | app first second => rfl
      | term index =>
          simp only [HOLKernelLogicalFunctionReadback.atoms]
          cases readType signature.symbol argument with
          | none => rfl
          | some domain => split_ifs <;> simp [logical_value_rename]

/-- A frame map preserves resolved variables and leaves existing constants unshadowed. Unresolved names may become bound. -/
structure LookupPreserving (constants : Nat → Option (NamedElaboration.SomeConst Const))
    (rho : Rename Unit gamma delta) (source : Names gamma) (target : Names delta) : Prop where
  variableLookup : ∀ index, source.lookup? index ≠ none →
    target.lookup? index = (source.lookup? index).map (fun value => ⟨value.1, rho value.2⟩)
  constantLookup : ∀ index, source.lookup? index = none → constants index ≠ none → target.lookup? index = none

theorem LookupPreserving.cons {constants : Nat → Option (NamedElaboration.SomeConst Const)}
    {rho : Rename Unit gamma delta} {source : Names gamma} {target : Names delta}
    (embedded : LookupPreserving constants rho source target) (domain : Ty Unit) (binder : Nat) :
    LookupPreserving constants (Rename.lift rho) (BinderNames.cons (type := domain) binder source)
      (BinderNames.cons (type := domain) binder target) := by
  constructor
  · intro index present
    by_cases same : binder = index
    · subst index
      simp [Rename.lift]
    · have oldPresent : source.lookup? index ≠ none := by
        intro absent
        simp [BinderNames.lookup?_cons_of_ne same, absent] at present
      simp only [BinderNames.lookup?_cons_of_ne same, embedded.variableLookup index oldPresent]
      cases source.lookup? index <;> rfl
  · intro index absent constant
    by_cases same : binder = index
    · subst index
      simp at absent
    · have oldAbsent : source.lookup? index = none := by
        cases found : source.lookup? index with
        | none => rfl
        | some value => simp [BinderNames.lookup?_cons_of_ne same, found] at absent
      simp only [BinderNames.lookup?_cons_of_ne same, embedded.constantLookup index oldAbsent constant, Option.map_none]

theorem LookupPreserving.weaken (constants : Nat → Option (NamedElaboration.SomeConst Const))
    (source : Names gamma) (domain : Ty Unit) (name : Nat)
    (variableAbsent : source.lookup? name = none) (constantAbsent : constants name = none) :
    LookupPreserving constants (Rename.weaken (σ := domain)) source (BinderNames.cons name source) := by
  constructor
  · intro index present
    have apart : name ≠ index := by intro same; subst index; exact present variableAbsent
    rw [BinderNames.lookup?_cons_of_ne apart]
    rfl
  · intro index absent constant
    have apart : name ≠ index := by intro same; subst index; exact constant constantAbsent
    simp only [BinderNames.lookup?_cons_of_ne apart, absent, Option.map_none]

theorem LookupPreserving.comp {target : Ctx Unit} {constants : Nat → Option (NamedElaboration.SomeConst Const)}
    {rho : Rename Unit gamma delta} {sigma : Rename Unit delta target}
    {first : Names gamma} {second : Names delta} {third : Names target}
    (one : LookupPreserving constants rho first second)
    (two : LookupPreserving constants sigma second third) :
    LookupPreserving constants (fun index => sigma (rho index)) first third := by
  constructor
  · intro index present
    have middle := one.variableLookup index present
    have middlePresent : second.lookup? index ≠ none := by
      rw [middle]
      cases found : first.lookup? index with
      | none => exact False.elim (present found)
      | some value => simp
    rw [two.variableLookup index middlePresent, middle]
    cases first.lookup? index <;> rfl
  · intro index absent constant
    exact two.constantLookup index (one.constantLookup index absent constant) constant

theorem LookupPreserving.refl (constants : Nat → Option (NamedElaboration.SomeConst Const))
    (names : Names gamma) : LookupPreserving constants Rename.id names names := by
  constructor
  · intro index _
    cases names.lookup? index <;> rfl
  · intro index absent _
    exact absent

theorem LookupPreserving.nameOf
    {constants : Nat → Option (NamedElaboration.SomeConst Const)}
    {rho : Rename Unit gamma delta} {source : Names gamma} {target : Names delta}
    (related : LookupPreserving constants rho source target) (nodup : source.toList.Nodup)
    {type : Ty Unit} (index : Var gamma type) : target.nameOf (rho index) = source.nameOf index := by
  have found := BinderNames.lookup?_nameOf source nodup index
  have moved := related.variableLookup (source.nameOf index) (by rw [found]; simp)
  simp only [found, Option.map_some] at moved
  exact BinderNames.lookup?_sound target moved

theorem readVariable_rename_of_present
    (constants : Nat → Option (NamedElaboration.SomeConst Const))
    {rho : Rename Unit gamma delta} {source : Names gamma} {target : Names delta}
    (embedded : LookupPreserving constants rho source target) (index : Nat)
    (present : readVariable constants source index ≠ none) :
    readVariable constants target index = (readVariable constants source index).map (Decoded.rename rho) := by
  cases found : source.lookup? index with
  | none =>
      have constant : constants index ≠ none := by
        intro absent
        simp [readVariable, found, absent] at present
      simp only [readVariable, found, embedded.constantLookup index found constant]
      cases constants index <;> rfl
  | some value =>
      have targetFound := embedded.variableLookup index (by simp [found])
      simp only [found, Option.map_some] at targetFound
      simp [readVariable, found, targetFound, Decoded.rename, HOL.rename]

/-- Successful readings commute with a lookup-preserving frame map. The target may also resolve expressions that were unreadable in the source frame. -/
theorem readTermWith_rename_of_present
    (extras : {context : Ctx Unit} → Preterm → Option (Decoded Const context))
    (extrasNatural : ∀ {first second : Ctx Unit} (rho : Rename Unit first second) (native : Preterm),
      extras (context := second) native = (extras (context := first) native).map (Decoded.rename rho))
    (references : HOLKernelSyntax.Symbol → Nat)
    (constants : Nat → Option (NamedElaboration.SomeConst Const)) (parameters : Nat)
    (sourceNames : Names gamma) (native : Preterm) :
    ∀ {delta : Ctx Unit} (rho : Rename Unit gamma delta) (targetNames : Names delta),
      LookupPreserving constants rho sourceNames targetNames →
      readTermWith extras references constants parameters sourceNames native ≠ none →
      readTermWith extras references constants parameters targetNames native =
        (readTermWith extras references constants parameters sourceNames native).map (Decoded.rename rho) := by
  induction gamma, sourceNames, native using readTermWith.induct references parameters with
  | case1 gamma index names =>
      intro delta rho target related successful
      simpa only [readTermWith] using readVariable_rename_of_present constants related index (by simpa only [readTermWith] using successful)
  | case2 gamma index head names =>
      intro delta rho target related successful
      simp [readTermWith, head, Decoded.rename, HOL.rename]
  | case3 gamma index head names =>
      intro delta rho target related successful
      simp [readTermWith, head, Decoded.rename, HOL.rename]
  | case4 gamma index names notTruth notFalse =>
      intro delta rho target related successful
      simp [readTermWith, extrasNatural rho]
  | case5 gamma index body head names ih =>
      intro delta rho target related successful
      have bodyRead := ih rho target related (by intro absent; simp [readTermWith, head, absent] at successful)
      simp only [readTermWith, head, ↓reduceIte, bodyRead]
      cases found : readTermWith extras references constants parameters names body with
      | none => simp []
      | some value =>
          simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, expect_rename]
          cases expect .prop value <;> rfl
  | case6 gamma index body notNot names =>
      intro delta rho target related successful
      simp [readTermWith, notNot, extrasNatural rho]
  | case7 gamma index first second names ihFirst ihSecond =>
      intro delta rho target related successful
      have firstRead := ihFirst rho target related (by intro absent; simp [readTermWith, absent] at successful)
      have secondRead := ihSecond rho target related (by intro absent; simp [readTermWith, absent] at successful)
      simp only [readTermWith, firstRead, secondRead]
      cases hfirst : readTermWith extras references constants parameters names first <;>
        cases hsecond : readTermWith extras references constants parameters names second <;>
        simp only [Option.map_none, Option.map_some,
          Option.bind_eq_bind, Option.bind_none, Option.bind_some]
      next firstValue secondValue =>
        cases hhead : readHead references index with
        | none => rfl
        | some symbol =>
            cases symbol <;> simp only [Option.map_none] <;>
              first | rfl | exact application_rename rho firstValue secondValue |
                exact logicalBinary_rename rho _ _ (fun _ _ => rfl) firstValue secondValue
  | case8 gamma index first second third head noType names =>
      intro delta rho target related successful
      unfold readTermWith
      simp [head, noType]
  | case9 gamma index first second third head type foundType names ihSecond ihThird =>
      intro delta rho target related successful
      have secondRead := ihSecond rho target related (by intro absent; unfold readTermWith at successful; simp [head, foundType, absent] at successful)
      have thirdRead := ihThird rho target related (by intro absent; unfold readTermWith at successful; simp [head, foundType, absent] at successful)
      unfold readTermWith
      simp only [head, foundType, secondRead, thirdRead]
      cases secondResult : readTermWith extras references constants parameters names second with
      | none => simp
      | some secondValue =>
          cases thirdResult : readTermWith extras references constants parameters names third with
          | none => simp
          | some thirdValue =>
              simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, expect_rename]
              cases expect type secondValue <;> cases expect type thirdValue <;> rfl
  | case10 gamma index second third head binder small names =>
      intro delta rho target related successful
      simp [readTermWith, head, small]
  | case11 gamma index second third head binder large noType names =>
      intro delta rho target related successful
      simp [readTermWith, head, large, noType]
  | case12 gamma index second third head binder large type foundType names ih =>
      intro delta rho target related successful
      have bodyRead := ih (Rename.lift rho) (BinderNames.cons binder target)
        (related.cons type binder) (by intro absent; simp [readTermWith, head, large, foundType, absent] at successful)
      simp only [readTermWith, head, large, foundType, ↓reduceIte, bodyRead]
      cases readTermWith extras references constants parameters (BinderNames.cons (type := type) binder names) third <;> rfl
  | case13 gamma index first second third head names notVar =>
      intro delta rho target related successful
      cases first with
      | var binder => exact False.elim (notVar binder rfl)
      | term symbol => simp [readTermWith, head]
      | app function argument => simp [readTermWith, head]
  | case14 gamma index second third head binder small names =>
      intro delta rho target related successful
      simp [readTermWith, head, small]
  | case15 gamma index second third head binder large noType names =>
      intro delta rho target related successful
      simp [readTermWith, head, large, noType]
  | case16 gamma index second third head binder large type foundType names ih =>
      intro delta rho target related successful
      have bodyRead := ih (Rename.lift rho) (BinderNames.cons binder target)
        (related.cons type binder) (by intro absent; simp [readTermWith, head, large, foundType, absent] at successful)
      simp only [readTermWith, head, large, foundType, ↓reduceIte, bodyRead]
      cases result : readTermWith extras references constants parameters (BinderNames.cons (type := type) binder names) third with
      | none => simp []
      | some value =>
          simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, expect_rename]
          cases expect .prop value <;> rfl
  | case17 gamma index first second third head names notVar =>
      intro delta rho target related successful
      cases first with
      | var binder => exact False.elim (notVar binder rfl)
      | term symbol => simp [readTermWith, head]
      | app function argument => simp [readTermWith, head]
  | case18 gamma index second third head binder small names =>
      intro delta rho target related successful
      simp [readTermWith, head, small]
  | case19 gamma index second third head binder large noType names =>
      intro delta rho target related successful
      simp [readTermWith, head, large, noType]
  | case20 gamma index second third head binder large type foundType names ih =>
      intro delta rho target related successful
      have bodyRead := ih (Rename.lift rho) (BinderNames.cons binder target)
        (related.cons type binder) (by intro absent; simp [readTermWith, head, large, foundType, absent] at successful)
      simp only [readTermWith, head, large, foundType, ↓reduceIte, bodyRead]
      cases result : readTermWith extras references constants parameters (BinderNames.cons (type := type) binder names) third with
      | none => simp []
      | some value =>
          simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, expect_rename]
          cases expect .prop value <;> rfl
  | case21 gamma index first second third head names notVar =>
      intro delta rho target related successful
      cases first with
      | var binder => exact False.elim (notVar binder rfl)
      | term symbol => simp [readTermWith, head]
      | app function argument => simp [readTermWith, head]
  | case22 gamma index first second third names noEq noLam noAll noEx =>
      intro delta rho target related successful
      unfold readTermWith
      simp []
  | case23 gamma native noVar noTerm noUnary noBinary noTernary names =>
      intro delta rho target related successful
      unfold readTermWith
      split <;> simp_all
      exact False.elim (noTernary _ _ _ _ rfl rfl rfl rfl)

#print axioms readTermWith_rename_of_present

/-- A fresh frame entry weakens a successful reading, including terms that bind the same name internally. -/
theorem readTermWith_weaken_of_read
    (extras : {context : Ctx Unit} → Preterm → Option (Decoded Const context))
    (extrasNatural : ∀ {first second : Ctx Unit} (rho : Rename Unit first second) (native : Preterm),
      extras (context := second) native = (extras (context := first) native).map (Decoded.rename rho))
    (references : HOLKernelSyntax.Symbol → Nat)
    (constants : Nat → Option (NamedElaboration.SomeConst Const)) (parameters : Nat)
    (names : Names gamma) (native : Preterm) (domain : Ty Unit) (name : Nat)
    (variableAbsent : names.lookup? name = none) (constantAbsent : constants name = none)
    {type : Ty Unit} (source : Term Const gamma type)
    (read : readTermWith extras references constants parameters names native = some ⟨type, source⟩) :
    readTermWith extras references constants parameters (BinderNames.cons (type := domain) name names) native =
      some ⟨type, HOL.weaken source⟩ := by
  have result := readTermWith_rename_of_present extras extrasNatural references constants parameters names native
    (Rename.weaken (σ := domain)) (BinderNames.cons name names)
    (LookupPreserving.weaken constants names domain name variableAbsent constantAbsent)
    (by rw [read]; simp)
  simpa only [read, Option.map_some, Decoded.rename, HOL.weaken] using result

#print axioms readTermWith_weaken_of_read

/-- The logical-function reader inherits successful-read weakening from its natural auxiliary dictionary. -/
theorem logical_reader_rename_of_read
    {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
    {theorems : TheoremSignature} {signature : Signature sorts terms}
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (constants : Nat → Option (NamedElaboration.SomeConst Const)) (parameters : Nat)
    (sourceNames : Names gamma) (targetNames : Names delta) (rho : Rename Unit gamma delta)
    (related : LookupPreserving constants rho sourceNames targetNames) (native : Preterm)
    {type : Ty Unit} (source : Term Const gamma type)
    (read : HOLKernelLogicalFunctionReadback.reader profile constants parameters sourceNames native = some ⟨type, source⟩) :
    HOLKernelLogicalFunctionReadback.reader profile constants parameters targetNames native = some ⟨type, HOL.rename rho source⟩ := by
  have result := readTermWith_rename_of_present (HOLKernelLogicalFunctionReadback.atoms profile)
    (fun rho term => logical_atoms_rename profile rho term) signature.symbol constants parameters sourceNames native rho targetNames related
    (by change HOLKernelLogicalFunctionReadback.reader profile constants parameters sourceNames native ≠ none; rw [read]; simp)
  change HOLKernelLogicalFunctionReadback.reader profile constants parameters targetNames native =
    (HOLKernelLogicalFunctionReadback.reader profile constants parameters sourceNames native).map (Decoded.rename rho) at result
  simpa only [read, Option.map_some, Decoded.rename] using result

theorem logical_reader_weaken_of_read
    {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
    {theorems : TheoremSignature} {signature : Signature sorts terms}
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (constants : Nat → Option (NamedElaboration.SomeConst Const)) (parameters : Nat)
    (names : Names gamma) (native : Preterm) (domain : Ty Unit) (name : Nat)
    (variableAbsent : names.lookup? name = none) (constantAbsent : constants name = none)
    {type : Ty Unit} (source : Term Const gamma type)
    (read : HOLKernelLogicalFunctionReadback.reader profile constants parameters names native = some ⟨type, source⟩) :
    HOLKernelLogicalFunctionReadback.reader profile constants parameters (BinderNames.cons (type := domain) name names) native =
      some ⟨type, HOL.weaken source⟩ :=
  readTermWith_weaken_of_read (HOLKernelLogicalFunctionReadback.atoms profile)
    (fun rho term => logical_atoms_rename profile rho term)
    signature.symbol constants parameters names native domain name variableAbsent constantAbsent source read

#print axioms logical_reader_weaken_of_read

theorem logical_reader_rename
    {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
    {theorems : TheoremSignature} {signature : Signature sorts terms}
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (constants : Nat → Option (NamedElaboration.SomeConst Const)) (parameters bound : Nat)
    (source : Names gamma) (target : Names delta) (rho : Rename Unit gamma delta)
    (related : NamesRel bound rho source target) (native : Preterm) (bounded : Preterm.VarsBelow bound native) :
    HOLKernelLogicalFunctionReadback.reader profile constants parameters target native =
      (HOLKernelLogicalFunctionReadback.reader profile constants parameters source native).map (Decoded.rename rho) :=
  readTermWith_rename (HOLKernelLogicalFunctionReadback.atoms profile)
    (fun rho term => logical_atoms_rename profile rho term)
    signature.symbol constants parameters bound source native rho target related bounded

theorem captured_name_not_related :
    ¬ NamesRel 1 (fun {_} index => Var.vs (σ := Ty.prop) index)
      (BinderNames.cons (type := Ty.prop) 0 BinderNames.nil)
      (BinderNames.cons (type := Ty.prop) 0 (BinderNames.cons (type := Ty.prop) 0 BinderNames.nil)) := by
  intro related
  have captured := related 0 (by decide)
  simp at captured

#print axioms logical_reader_rename
#print axioms captured_name_not_related

#print axioms readTermWith_rename

#print axioms application_rename
#print axioms logicalBinary_rename

#print axioms NamesRel.cons
#print axioms NamesRel.weaken
#print axioms expect_rename
#print axioms readVariable_rename
theorem readObjectWith_rename
    (reader : TermReader Const) (rho : Rename Unit gamma delta)
    (source : Names gamma) (target : Names delta) (type : Ty Unit) (native : Preterm)
    (natural : reader target native = (reader source native).map (Decoded.rename rho)) :
    readObjectWith reader target type native =
      (readObjectWith reader source type native).map (HOL.rename rho) := by
  simp only [readObjectWith, natural, Option.bind_eq_bind, Option.bind_map, Option.map_bind,
    Function.comp_def, expect_rename]

end Mettapedia.Languages.MM0.HOLKernelTermReadback

namespace Mettapedia.Languages.MM0.HOLKernelJudgmentReadback
open Mettapedia.Logic Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelTermReadback
universe u
variable {Const : Ty Unit → Type u} {gamma delta : Ctx Unit}

def Judgment.rename (rho : Rename Unit gamma delta) : Judgment Const gamma → Judgment Const delta
  | .typing term => .typing (HOL.rename rho term)
  | .assertion formula => .assertion (HOL.rename rho formula)
  | .conjunction first second => .conjunction (first.rename rho) (second.rename rho)
  | .consequence first second => .consequence (first.rename rho) (second.rename rho)

theorem Judgment.rename_formula (rho : Rename Unit gamma delta) (judgment : Judgment Const gamma) :
    (judgment.rename rho).formula = HOL.rename rho judgment.formula := by
  induction judgment <;> simp_all [Judgment.rename, Judgment.formula, HOL.rename]

theorem readTypingWith_rename
    (reader : TermReader Const) (references : HOLKernelSyntax.Symbol → Nat)
    (rho : Rename Unit gamma delta) (source : Names gamma) (target : Names delta)
    (nativeTerm nativeType : Preterm)
    (termRead : reader target nativeTerm = (reader source nativeTerm).map (Decoded.rename rho)) :
    readTypingWith reader references target nativeTerm nativeType =
      (readTypingWith reader references source nativeTerm nativeType).map (Judgment.rename rho) := by
  cases typeRead : readType references nativeType with
  | none => simp [readTypingWith, typeRead]
  | some type =>
      simp only [readTypingWith, typeRead]
      change ((reader target nativeTerm).bind fun decoded =>
          (expect type decoded).bind (fun term => some (Judgment.typing term))) =
        ((reader source nativeTerm).bind fun decoded =>
          (expect type decoded).bind (fun term => some (Judgment.typing term))).map (Judgment.rename rho)
      rw [termRead]
      cases reader source nativeTerm with
      | none => rfl
      | some decoded =>
          simp only [Option.map_some, Option.bind_some, expect_rename]
          cases expect type decoded <;> rfl

theorem readJudgmentWith_rename
    (reader : TermReader Const) (references : HOLKernelSyntax.Symbol → Nat)
    (bound : Nat) (rho : Rename Unit gamma delta) (source : Names gamma) (target : Names delta)
    (readerNatural : ∀ native : Preterm, Preterm.VarsBelow bound native →
      reader target native = (reader source native).map (Decoded.rename rho))
    (native : Preterm) (bounded : Preterm.VarsBelow bound native) :
    readJudgmentWith reader references target native =
      (readJudgmentWith reader references source native).map (Judgment.rename rho) := by
  induction native using readJudgmentWith.induct references with
  | case1 index object head =>
      have objectRead := readerNatural object (varsBelow_argument bounded)
      simp only [readJudgmentWith, head, ↓reduceIte, objectRead]
      cases reader source object with
      | none => rfl
      | some decoded =>
          simp only [Option.map_some, Option.bind_some, expect_rename]
          cases expect .prop decoded <;> rfl
  | case2 index object notThm => simp [readJudgmentWith, notThm]
  | case3 index first second head =>
      simpa only [readJudgmentWith, head] using
        readTypingWith_rename reader references rho source target first second
          (readerNatural first (varsBelow_argument (varsBelow_function bounded)))
  | case4 index first second head ihFirst ihSecond =>
      rw [readJudgmentWith, head]
      rw [ihFirst (varsBelow_argument (varsBelow_function bounded)), ihSecond (varsBelow_argument bounded)]
      simp only [readJudgmentWith, head]
      cases readJudgmentWith reader references source first <;>
        cases readJudgmentWith reader references source second <;> rfl
  | case5 index first second head ihFirst ihSecond =>
      rw [readJudgmentWith, head]
      rw [ihFirst (varsBelow_argument (varsBelow_function bounded)), ihSecond (varsBelow_argument bounded)]
      simp only [readJudgmentWith, head]
      cases readJudgmentWith reader references source first <;>
        cases readJudgmentWith reader references source second <;> rfl
  | case6 index first second noTy noAn noIm =>
      simp [readJudgmentWith]
  | case7 native noUnary noBinary =>
      unfold readJudgmentWith
      split <;> simp_all

theorem logical_judgment_rename
    {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
    {theorems : TheoremSignature} {signature : Signature sorts terms}
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (constants : Nat → Option (NamedElaboration.SomeConst Const)) (parameters bound : Nat)
    (source : Names gamma) (target : Names delta) (rho : Rename Unit gamma delta)
    (related : NamesRel bound rho source target) (native : Preterm) (bounded : Preterm.VarsBelow bound native) :
    readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile constants parameters)
      signature.symbol target native =
      (readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile constants parameters)
        signature.symbol source native).map (Judgment.rename rho) :=
  readJudgmentWith_rename _ signature.symbol bound rho source target
    (fun term support => logical_reader_rename profile constants parameters bound source target rho related term support)
    native bounded

#print axioms readJudgmentWith_rename
#print axioms logical_judgment_rename

#print axioms Judgment.rename_formula
#print axioms readTypingWith_rename
theorem readTypingWith_rename_of_present
    (reader : TermReader Const) (references : HOLKernelSyntax.Symbol → Nat)
    (rho : Rename Unit gamma delta) (source : Names gamma) (target : Names delta)
    (readerNatural : ∀ native : Preterm, reader source native ≠ none →
      reader target native = (reader source native).map (Decoded.rename rho))
    (nativeTerm nativeType : Preterm)
    (present : readTypingWith reader references source nativeTerm nativeType ≠ none) :
    readTypingWith reader references target nativeTerm nativeType =
      (readTypingWith reader references source nativeTerm nativeType).map (Judgment.rename rho) := by
  apply readTypingWith_rename reader references rho source target nativeTerm nativeType
  apply readerNatural
  intro absent
  cases found : readType references nativeType <;> simp [readTypingWith, found, absent] at present

theorem readJudgmentWith_rename_of_present
    (reader : TermReader Const) (references : HOLKernelSyntax.Symbol → Nat)
    (rho : Rename Unit gamma delta) (source : Names gamma) (target : Names delta)
    (readerNatural : ∀ native : Preterm, reader source native ≠ none →
      reader target native = (reader source native).map (Decoded.rename rho))
    (native : Preterm) (present : readJudgmentWith reader references source native ≠ none) :
    readJudgmentWith reader references target native =
      (readJudgmentWith reader references source native).map (Judgment.rename rho) := by
  induction native using readJudgmentWith.induct references with
  | case1 index object head =>
      have objectRead := readerNatural object (by intro absent; simp [readJudgmentWith, head, absent] at present)
      simp only [readJudgmentWith, head, ↓reduceIte, objectRead]
      cases reader source object with
      | none => rfl
      | some decoded =>
          simp only [Option.map_some, Option.bind_some, expect_rename]
          cases expect .prop decoded <;> rfl
  | case2 index object notThm => simp [readJudgmentWith, notThm]
  | case3 index first second head =>
      simpa only [readJudgmentWith, head] using
        readTypingWith_rename_of_present reader references rho source target readerNatural first second
          (by simpa only [readJudgmentWith, head] using present)
  | case4 index first second head ihFirst ihSecond =>
      rw [readJudgmentWith, head]
      rw [ihFirst (by intro absent; simp [readJudgmentWith, head, absent] at present), ihSecond (by intro absent; simp [readJudgmentWith, head, absent] at present)]
      simp only [readJudgmentWith, head]
      cases readJudgmentWith reader references source first <;>
        cases readJudgmentWith reader references source second <;> rfl
  | case5 index first second head ihFirst ihSecond =>
      rw [readJudgmentWith, head]
      rw [ihFirst (by intro absent; simp [readJudgmentWith, head, absent] at present), ihSecond (by intro absent; simp [readJudgmentWith, head, absent] at present)]
      simp only [readJudgmentWith, head]
      cases readJudgmentWith reader references source first <;>
        cases readJudgmentWith reader references source second <;> rfl
  | case6 index first second noTy noAn noIm =>
      simp [readJudgmentWith]
  | case7 native noUnary noBinary =>
      unfold readJudgmentWith
      split <;> simp_all

theorem logical_judgment_rename_of_read
    {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
    {theorems : TheoremSignature} {signature : Signature sorts terms}
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (constants : Nat → Option (NamedElaboration.SomeConst Const)) (parameters : Nat)
    (source : Names gamma) (target : Names delta) (rho : Rename Unit gamma delta)
    (related : LookupPreserving constants rho source target) (native : Preterm) (judgment : Judgment Const gamma)
    (read : readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile constants parameters)
      signature.symbol source native = some judgment) :
    readJudgmentWith (HOLKernelLogicalFunctionReadback.reader profile constants parameters)
      signature.symbol target native = some (judgment.rename rho) := by
  have result := readJudgmentWith_rename_of_present
    (HOLKernelLogicalFunctionReadback.reader profile constants parameters) signature.symbol rho source target
    (fun term present => readTermWith_rename_of_present (HOLKernelLogicalFunctionReadback.atoms profile)
      (fun rho term => logical_atoms_rename profile rho term) signature.symbol constants parameters source term rho target related present)
    native (by rw [read]; simp)
  simpa only [read, Option.map_some] using result

#print axioms logical_judgment_rename_of_read
end Mettapedia.Languages.MM0.HOLKernelJudgmentReadback

namespace Mettapedia.Languages.MM0.HOLKernelRuleInstances
open Mettapedia.Logic Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelTermReadback HOLKernelJudgmentReadback
universe u
variable {Const : Ty Unit → Type u} {gamma delta : Ctx Unit}

theorem readStructuralArguments_rename
    (reader : TermReader Const) (references : HOLKernelSyntax.Symbol → Nat)
    (bound : Nat) (rho : Rename Unit gamma delta) (source : Names gamma) (target : Names delta)
    (natural : ∀ native : Preterm, Preterm.VarsBelow bound native →
      reader target native = (reader source native).map (Decoded.rename rho))
    (rule : HOLKernelStructuralRules.Rule) (arguments : List Preterm)
    (bounded : ∀ native ∈ arguments, Preterm.VarsBelow bound native) :
    readStructuralArguments reader references target rule arguments =
      (readStructuralArguments reader references source rule arguments).map (StructuralArguments.rename rho) := by
  have contextNatural (native : Preterm) (support : Preterm.VarsBelow bound native) :
      (readJudgmentWith reader references target native).map Judgment.formula =
        ((readJudgmentWith reader references source native).map Judgment.formula).map (HOL.rename rho) := by
    rw [readJudgmentWith_rename reader references bound rho source target natural native support]
    simp only [Option.map_map, Function.comp_def, Judgment.rename_formula]
  rcases arguments with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;>
    cases rule <;> simp only [readStructuralArguments] <;> try rfl
  all_goals simp_all [Option.bind_eq_bind, Option.bind_map, Option.map_bind, Function.comp_def, StructuralArguments.rename]

theorem readInferenceArguments_rename
    (reader : TermReader Const) (references : HOLKernelSyntax.Symbol → Nat)
    (bound : Nat) (rho : Rename Unit gamma delta) (source : Names gamma) (target : Names delta)
    (natural : ∀ native : Preterm, Preterm.VarsBelow bound native →
      reader target native = (reader source native).map (Decoded.rename rho))
    (rule : HOLKernelInferenceRules.Rule) (arguments : List Preterm)
    (bounded : ∀ native ∈ arguments, Preterm.VarsBelow bound native) :
    readInferenceArguments reader references target rule arguments =
      (readInferenceArguments reader references source rule arguments).map (InferenceArguments.rename rho) := by
  have contextNatural (native : Preterm) (support : Preterm.VarsBelow bound native) :
      (readJudgmentWith reader references target native).map Judgment.formula =
        ((readJudgmentWith reader references source native).map Judgment.formula).map (HOL.rename rho) := by
    rw [readJudgmentWith_rename reader references bound rho source target natural native support]
    simp only [Option.map_map, Function.comp_def, Judgment.rename_formula]
  have formulaNatural (native : Preterm) (support : Preterm.VarsBelow bound native) :
      (reader target native).bind (expect .prop) =
        ((reader source native).bind (expect .prop)).map (HOL.rename rho) := by
    rw [natural native support]
    simp only [Option.bind_map, Option.map_bind, Function.comp_def, expect_rename]
  have objectNatural (type : Ty Unit) (native : Preterm) (support : Preterm.VarsBelow bound native) :
      readObjectWith reader target type native =
        (readObjectWith reader source type native).map (HOL.rename rho) :=
    readObjectWith_rename reader rho source target type native (natural native support)
  rcases arguments with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, rest⟩⟩⟩⟩⟩⟩⟩ <;>
    cases rule <;> simp only [readInferenceArguments] <;> try rfl
  all_goals simp_all [Option.bind_eq_bind, Option.bind_map, Option.map_bind, Function.comp_def,
    InferenceArguments.rename, Option.bind_assoc, expect_rename]
  all_goals split <;> simp_all [Option.map_bind, Function.comp_def, InferenceArguments.rename]

end Mettapedia.Languages.MM0.HOLKernelRuleInstances

namespace Mettapedia.Languages.MM0.HOLKernelRuleReadback
open Mettapedia.Logic Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelTermReadback HOLKernelJudgmentReadback
universe u
variable {Const : Ty Unit → Type u} {gamma delta : Ctx Unit}

theorem expandEquivalence_varsBelow (references : HOLKernelSyntax.Symbol → Nat)
    (equivalenceReference bound : Nat) (native : Preterm) (bounded : Preterm.VarsBelow bound native) :
    Preterm.VarsBelow bound (expandEquivalence references equivalenceReference native) := by
  induction native using expandEquivalence.induct equivalenceReference <;>
    simp_all [expandEquivalence, Preterm.VarsBelow, HOLKernelBooleanEquality.expanded, applySymbol, Preterm.applyArgs]

variable {terms : TermSignature} {definitions : Definition.Signature}
variable {references : HOLKernelSyntax.Symbol → Nat} {ids : SortIds}
open HOLKernelRuleInstances

def TypingArguments.rename (rho : Rename Unit gamma delta) (arguments : TypingArguments Const gamma) :
    TypingArguments Const delta :=
  ⟨arguments.premises.map (HOL.rename rho), arguments.antecedent.rename rho,
    arguments.type, HOL.rename rho arguments.term⟩

def RuleArguments.rename {rule : Rule} (rho : Rename Unit gamma delta) :
    RuleArguments Const gamma rule → RuleArguments Const delta rule
  | .structural arguments => .structural (arguments.rename rho)
  | .inference arguments => .inference (arguments.rename rho)
  | .typing rule arguments => .typing rule (arguments.rename rho)

theorem RuleArguments.rename_premises {rule : Rule} (rho : Rename Unit gamma delta)
    (arguments : RuleArguments Const gamma rule) :
    (arguments.rename rho).premises = arguments.premises.map (HOL.rename rho) := by
  cases arguments with
  | structural arguments => exact arguments.rename_premises rho
  | inference arguments => exact arguments.rename_premises rho
  | typing rule arguments => rfl

theorem RuleArguments.rename_conclusion {rule : Rule} (rho : Rename Unit gamma delta)
    (arguments : RuleArguments Const gamma rule) :
    (arguments.rename rho).conclusion = HOL.rename rho arguments.conclusion := by
  cases arguments with
  | structural arguments => exact arguments.rename_conclusion rho
  | inference arguments => exact arguments.rename_conclusion rho
  | typing rule arguments =>
      simp only [RuleArguments.rename, RuleArguments.conclusion, TypingArguments.rename,
        Judgment.rename_formula, HOL.rename]

theorem readFormulaIn_rename
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids)
    (reader : TermReader Const) (parameters bound : Nat)
    (rho : Rename Unit gamma delta) (source : Names gamma) (target : Names delta)
    (natural : ∀ native : Preterm, Preterm.VarsBelow bound native →
      reader target native = (reader source native).map (Decoded.rename rho))
    (native : Preterm) (bounded : Preterm.VarsBelow bound native) :
    readFormulaIn abbreviation reader parameters target native =
      (readFormulaIn abbreviation reader parameters source native).map (HOL.rename rho) := by
  unfold readFormulaIn
  rw [readJudgmentWith_rename reader references bound rho source target natural _
    (expandEquivalence_varsBelow references abbreviation.reference bound native bounded)]
  simp only [Option.map_map, Function.comp_def, Judgment.rename_formula]

theorem readFormulas_rename
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids)
    (reader : TermReader Const) (parameters bound : Nat)
    (rho : Rename Unit gamma delta) (source : Names gamma) (target : Names delta)
    (natural : ∀ native : Preterm, Preterm.VarsBelow bound native →
      reader target native = (reader source native).map (Decoded.rename rho))
    (natives : List Preterm) (bounded : ∀ native ∈ natives, Preterm.VarsBelow bound native) :
    natives.mapM (readFormulaIn abbreviation reader parameters target) =
      (natives.mapM (readFormulaIn abbreviation reader parameters source)).map (List.map (HOL.rename rho)) := by
  induction natives with
  | nil => rfl
  | cons first rest ih =>
      have head := readFormulaIn_rename abbreviation reader parameters bound rho source target natural
        first (bounded first List.mem_cons_self)
      have tail := ih (fun native member => bounded native (List.mem_cons_of_mem _ member))
      simp only [List.mapM_cons, head, tail, Option.bind_eq_bind, Option.bind_map,
        Option.map_bind, Function.comp_def, Option.pure_def, Option.map_some, List.map_cons]

theorem readTypingArguments_rename
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids)
    (reader : TermReader Const) (parameters bound : Nat)
    (rho : Rename Unit gamma delta) (source : Names gamma) (target : Names delta)
    (natural : ∀ native : Preterm, Preterm.VarsBelow bound native →
      reader target native = (reader source native).map (Decoded.rename rho))
    (native : TheoremInstance)
    (premisesBound : ∀ premise ∈ native.hypotheses, Preterm.VarsBelow bound premise)
    (conclusionBound : Preterm.VarsBelow bound native.conclusion) :
    readTypingArguments abbreviation reader parameters target native =
      (readTypingArguments abbreviation reader parameters source native).map (TypingArguments.rename rho) := by
  have premisesRead := readFormulas_rename abbreviation reader parameters bound rho source target natural
    native.hypotheses premisesBound
  have conclusionRead := readJudgmentWith_rename reader references bound rho source target natural _
    (expandEquivalence_varsBelow references abbreviation.reference bound native.conclusion conclusionBound)
  simp only [readTypingArguments, premisesRead, conclusionRead, Option.bind_eq_bind]
  cases native.hypotheses.mapM (readFormulaIn abbreviation reader parameters source) with
  | none => rfl
  | some premises =>
      cases readJudgmentWith reader references source
          (expandEquivalence references abbreviation.reference native.conclusion) with
      | none => rfl
      | some judgment =>
          cases judgment with
          | typing term => rfl
          | assertion formula => rfl
          | conjunction first second => rfl
          | consequence first second => cases second <;> rfl

theorem readArguments_rename
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids)
    (reader : TermReader Const) (parameters bound : Nat)
    (rho : Rename Unit gamma delta) (source : Names gamma) (target : Names delta)
    (natural : ∀ native : Preterm, Preterm.VarsBelow bound native →
      reader target native = (reader source native).map (Decoded.rename rho))
    (rule : Rule) (arguments : List Preterm) (native : TheoremInstance)
    (argumentsBound : ∀ argument ∈ arguments, Preterm.VarsBelow bound argument)
    (premisesBound : ∀ premise ∈ native.hypotheses, Preterm.VarsBelow bound premise)
    (conclusionBound : Preterm.VarsBelow bound native.conclusion) :
    readArguments abbreviation reader parameters target rule arguments native =
      (readArguments abbreviation reader parameters source rule arguments native).map (RuleArguments.rename rho) := by
  have expandedBound : ∀ argument ∈ arguments.map (expandEquivalence references abbreviation.reference),
      Preterm.VarsBelow bound argument := by
    intro argument member
    obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
    exact expandEquivalence_varsBelow references abbreviation.reference bound old (argumentsBound old oldMember)
  cases rule with
  | typing rule =>
      simp only [readArguments, readTypingArguments_rename abbreviation reader parameters bound rho
        source target natural native premisesBound conclusionBound, Option.map_map, Function.comp_def,
        RuleArguments.rename]
  | structural rule =>
      simp only [readArguments, readStructuralArguments_rename reader references bound rho source target
        natural rule _ expandedBound, Option.map_map, Function.comp_def, RuleArguments.rename]
  | inference rule =>
      simp only [readArguments, readInferenceArguments_rename reader references bound rho source target
        natural rule _ expandedBound, Option.map_map, Function.comp_def, RuleArguments.rename]

/-- A frame change transports a licensed local application with the same native
rule, arguments and instantiated theorem. Only its intrinsic source operands
and formulas are renamed. -/
def AdmittedApplication.rename
    {abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids}
    {theorems : TheoremSignature} {context : Context} {reader : TermReader Const}
    {parameters : Nat} {source : Names gamma} {ruleAt : Nat → Option Rule}
    {index : Nat} {arguments : List Preterm}
    (admitted : AdmittedApplication abbreviation theorems context reader parameters source ruleAt index arguments)
    (bound : Nat) (rho : Rename Unit gamma delta) (target : Names delta)
    (natural : ∀ native : Preterm, Preterm.VarsBelow bound native →
      reader target native = (reader source native).map (Decoded.rename rho))
    (argumentsBound : ∀ argument ∈ arguments, Preterm.VarsBelow bound argument)
    (premisesBound : ∀ premise ∈ admitted.native.hypotheses, Preterm.VarsBelow bound premise)
    (conclusionBound : Preterm.VarsBelow bound admitted.native.conclusion) :
    AdmittedApplication abbreviation theorems context reader parameters target ruleAt index arguments where
  rule := admitted.rule
  selected := admitted.selected
  native := admitted.native
  declared := admitted.declared
  instantiated := admitted.instantiated
  operands := admitted.operands.rename rho
  operands_read := by
    rw [readArguments_rename abbreviation reader parameters bound rho source target natural
      admitted.rule arguments admitted.native argumentsBound premisesBound conclusionBound, admitted.operands_read]
    rfl
  premises_read := by
    rw [RuleArguments.rename_premises,
      readFormulas_rename abbreviation reader parameters bound rho source target natural
        admitted.native.hypotheses premisesBound, admitted.premises_read]
    rfl
  conclusion_read := by
    rw [RuleArguments.rename_conclusion,
      readFormulaIn_rename abbreviation reader parameters bound rho source target natural
        admitted.native.conclusion conclusionBound, admitted.conclusion_read]
    rfl

#print axioms AdmittedApplication.rename
#print axioms readArguments_rename

theorem logical_formula_rename
    {sorts : SortSignature} {terms : TermSignature} {definitions : Definition.Signature}
    {theorems : TheoremSignature} {signature : Signature sorts terms}
    (profile : HOLKernelLogicalOperations.Profile sorts terms definitions theorems signature)
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions signature.symbol signature.ids)
    (constants : Nat → Option (NamedElaboration.SomeConst Const)) (parameters bound : Nat)
    (source : Names gamma) (target : Names delta) (rho : Rename Unit gamma delta)
    (related : NamesRel bound rho source target) (native : Preterm) (bounded : Preterm.VarsBelow bound native) :
    readFormulaIn abbreviation (HOLKernelLogicalFunctionReadback.reader profile constants parameters)
      parameters target native =
      (readFormulaIn abbreviation (HOLKernelLogicalFunctionReadback.reader profile constants parameters)
        parameters source native).map (HOL.rename rho) := by
  exact readFormulaIn_rename abbreviation _ parameters bound rho source target
    (fun term support => logical_reader_rename profile constants parameters bound source target rho related term support)
    native bounded

#print axioms expandEquivalence_varsBelow
#print axioms logical_formula_rename
end Mettapedia.Languages.MM0.HOLKernelRuleReadback

