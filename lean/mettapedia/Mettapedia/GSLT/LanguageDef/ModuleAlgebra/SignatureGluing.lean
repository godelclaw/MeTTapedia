import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.Gluing
import Mettapedia.OSLF.Syntax.SignatureMorphism
import Mettapedia.OSLF.Syntax.BindingCloneAlgebra

/-!
# Gluing independently declared binding operators

Each module has its own operator signature. Result sorts and binding arities
come from the declaration bodies; origins distinguish independent instances.
Interpretations share a semantic substitution algebra, but need agree only
on the operators actually shared by the modules. The union supplies the
unique interpretation extending both branches.

The universal signature maps allow arbitrary common sort maps into a
target signature. Semantic model gluing here retains the source sorts and
a shared substitution algebra; it does not amalgamate independently chosen
carriers or substitution structures along sort identifications.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleAlgebra.SignatureGluing

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FreeBindingTerms

universe u

variable {Origin Label Body : Type}
  [DecidableEq Origin] [DecidableEq Label] [DecidableEq Body]

/-! ## Dependent interpretations of the existing declaration pushout -/

abbrev CompatibleAssignments (F : Entry Origin Label Body → Type u)
    (p q : Presentation Origin Label Body) :=
  {pair : DependentAssignment F p × DependentAssignment F q //
    ∀ entry hp hq, pair.1 ⟨entry, hp⟩ = pair.2 ⟨entry, hq⟩}

/-- The inverse laws preserve the complete dependent payloads. -/
def assignmentJoinEquiv (F : Entry Origin Label Body → Type u)
    {p q r : Presentation Origin Label Body} (joined : join p q = some r) :
    DependentAssignment F r ≃ CompatibleAssignments F p q where
  toFun assignment := ⟨(fun entry => assignment (includeLeft joined entry),
    fun entry => assignment (includeRight joined entry)), fun _ _ _ => rfl⟩
  invFun pair := glueDependent joined pair.val.1 pair.val.2
  left_inv assignment :=
    (glueDependent_unique joined _ _ assignment (fun _ => rfl) (fun _ => rfl)).symm
  right_inv pair := by
    apply Subtype.ext
    apply Prod.ext
    · funext entry
      exact glueDependent_left joined _ _ entry
    · funext entry
      exact glueDependent_right joined _ _ pair.property entry

/-- Disagreeing shared declarations obstruct a mediator, regardless of
whether the declaration union exists. -/
theorem no_glue_of_disagreement {F : Entry Origin Label Body → Type u}
    {p q r : Presentation Origin Label Body} (joined : join p q = some r)
    (left : DependentAssignment F p) (right : DependentAssignment F q)
    (entry : Entry Origin Label Body) (hp : entry ∈ p.val) (hq : entry ∈ q.val)
    (different : left ⟨entry, hp⟩ ≠ right ⟨entry, hq⟩) :
    ¬ ∃ candidate : DependentAssignment F r,
      (∀ e, candidate (includeLeft joined e) = left e) ∧
      (∀ e, candidate (includeRight joined e) = right e) := by
  rintro ⟨candidate, onLeft, onRight⟩
  exact different ((onLeft ⟨entry, hp⟩).symm.trans (onRight ⟨entry, hq⟩))

/-- The common signature contains every shared declaration, not merely a
chosen smaller ancestor. -/
def common (p q : Presentation Origin Label Body) : Presentation Origin Label Body :=
  ⟨p.val ∩ q.val, p.property.mono Finset.inter_subset_left⟩

theorem common_agreement_iff {F : Entry Origin Label Body → Type u}
    (p q : Presentation Origin Label Body) (left : DependentAssignment F p) (right : DependentAssignment F q) :
    restrictDependent (show (common p q).val ⊆ p.val from Finset.inter_subset_left) left =
        restrictDependent (show (common p q).val ⊆ q.val from Finset.inter_subset_right) right ↔
      ∀ entry hp hq, left ⟨entry, hp⟩ = right ⟨entry, hq⟩ := by
  constructor
  · intro equal entry hp hq
    exact congrFun equal ⟨entry, Finset.mem_inter.mpr ⟨hp, hq⟩⟩
  · intro agree
    funext entry
    exact agree entry.val (Finset.mem_inter.mp entry.property).1
      (Finset.mem_inter.mp entry.property).2

open _root_.CategoryTheory _root_.CategoryTheory.Limits

/-- The actual dependent assignment square is a pullback over the complete
common signature. Existence is proved by constructing its mediator. -/
theorem assignmentJoin_isPullback (F : Entry Origin Label Body → Type u)
    {p q r : Presentation Origin Label Body} (joined : join p q = some r) :
    IsPullback
      (↾(restrictDependent (F := F) ((join_eq_some_iff.mp joined) ▸ Finset.subset_union_left)))
      (↾(restrictDependent (F := F) ((join_eq_some_iff.mp joined) ▸ Finset.subset_union_right)))
      (↾(restrictDependent (F := F)
        (show (common p q).val ⊆ p.val from Finset.inter_subset_left)))
      (↾(restrictDependent (F := F)
        (show (common p q).val ⊆ q.val from Finset.inter_subset_right))) := by
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext assignment entry
    rfl
  · intro first second equal
    have left := equal.1
    have right := equal.2
    have firstUnique := glueDependent_unique joined
      (restrictDependent ((join_eq_some_iff.mp joined) ▸ Finset.subset_union_left) first)
      (restrictDependent ((join_eq_some_iff.mp joined) ▸ Finset.subset_union_right) first)
      first (fun _ => rfl) (fun _ => rfl)
    have secondUnique := glueDependent_unique joined
      (restrictDependent ((join_eq_some_iff.mp joined) ▸ Finset.subset_union_left) first)
      (restrictDependent ((join_eq_some_iff.mp joined) ▸ Finset.subset_union_right) first)
      second (fun entry => (congrFun left entry).symm)
      (fun entry => (congrFun right entry).symm)
    exact firstUnique.trans secondUnique.symm
  · intro left right equal
    have agree := (common_agreement_iff p q left right).mp equal
    refine ⟨glueDependent joined left right, ?_, ?_⟩
    · funext entry
      exact glueDependent_left joined left right entry
    · funext entry
      exact glueDependent_right joined left right agree entry

/-! ## Actual varying binding signatures -/

variable {S : Signature}

/-- Operators are the admitted declarations with the requested result sort.
The signature therefore varies with the module, rather than predeclaring
every private operator in every component. -/
def signature (S : Signature) (result : Body → S.Srt)
    (arity : Body → List (List S.Srt × S.Srt))
    (p : Presentation Origin Label Body) : Signature where
  Srt := S.Srt
  Op sort := {entry : Member p // result entry.val.body = sort}
  arity op := arity op.val.val.body

/-- Declaration inclusion is an existing binder-preserving signature map. -/
def inclusion (result : Body → S.Srt) (arity : Body → List (List S.Srt × S.Srt))
    {p q : Presentation Origin Label Body} (included : p.val ⊆ q.val) :
    SigMor (signature S result arity p) (signature S result arity q) where
  sortMap := id
  opMap op := ⟨⟨op.val.val, included op.val.property⟩, op.property⟩
  carriesArity op := (mapArities_id (arity op.val.val.body)).symm

/-! ## Universal signature maps, including a change of sorts -/

variable {T : Signature}

/-- An image operator has the translated result sort and the complete
translated binding arity. Sort identification is permitted by `sortMap`. -/
abbrev OperatorImage (T : Signature) (sortMap : S.Srt → T.Srt)
    (result : Body → S.Srt) (arity : Body → List (List S.Srt × S.Srt))
    (entry : Entry Origin Label Body) :=
  {op : T.Op (sortMap (result entry.body)) //
    T.arity op = mapArities sortMap (arity entry.body)}

/-- The fibre of actual signature morphisms over a chosen map of sorts. -/
abbrev SignatureMap (T : Signature) (sortMap : S.Srt → T.Srt)
    (result : Body → S.Srt) (arity : Body → List (List S.Srt × S.Srt))
    (p : Presentation Origin Label Body) :=
  {map : SigMor (signature S result arity p) T // map.sortMap = sortMap}

def signatureMap (T : Signature) (sortMap : S.Srt → T.Srt)
    (result : Body → S.Srt) (arity : Body → List (List S.Srt × S.Srt))
    (p : Presentation Origin Label Body)
    (assignment : DependentAssignment (OperatorImage T sortMap result arity) p) :
    SignatureMap T sortMap result arity p :=
  ⟨{ sortMap := sortMap
     opMap := fun op => (congrArg sortMap op.property) ▸ (assignment op.val).val
     carriesArity := by
       intro sort op
       rcases op with ⟨entry, same⟩
       cases same
       exact (assignment entry).property }, rfl⟩

def assignmentOfSignatureMap (T : Signature) (sortMap : S.Srt → T.Srt)
    (result : Body → S.Srt) (arity : Body → List (List S.Srt × S.Srt))
    (p : Presentation Origin Label Body) (map : SignatureMap T sortMap result arity p) :
    DependentAssignment (OperatorImage T sortMap result arity) p := by
  rcases map with ⟨⟨sorts, operators, law⟩, same⟩
  dsimp at same
  subst sorts
  exact fun entry => ⟨operators ⟨entry, rfl⟩, law ⟨entry, rfl⟩⟩

theorem assignmentOfSignatureMap_signatureMap (T : Signature) (sortMap : S.Srt → T.Srt)
    (result : Body → S.Srt) (arity : Body → List (List S.Srt × S.Srt))
    (p : Presentation Origin Label Body)
    (assignment : DependentAssignment (OperatorImage T sortMap result arity) p) :
    assignmentOfSignatureMap T sortMap result arity p
      (signatureMap T sortMap result arity p assignment) = assignment := by
  funext entry
  apply Subtype.ext
  rfl

theorem signatureMap_assignmentOfSignatureMap (T : Signature) (sortMap : S.Srt → T.Srt)
    (result : Body → S.Srt) (arity : Body → List (List S.Srt × S.Srt))
    (p : Presentation Origin Label Body) (map : SignatureMap T sortMap result arity p) :
    signatureMap T sortMap result arity p
      (assignmentOfSignatureMap T sortMap result arity p map) = map := by
  rcases map with ⟨⟨sorts, operators, law⟩, same⟩
  dsimp at same
  subst sorts
  apply Subtype.ext
  dsimp only [signatureMap, assignmentOfSignatureMap]
  congr 1
  funext sort op
  rcases op with ⟨entry, same⟩
  cases same
  rfl

def signatureMapEquiv (T : Signature) (sortMap : S.Srt → T.Srt)
    (result : Body → S.Srt) (arity : Body → List (List S.Srt × S.Srt))
    (p : Presentation Origin Label Body) :
    SignatureMap T sortMap result arity p ≃ DependentAssignment (OperatorImage T sortMap result arity) p where
  toFun := assignmentOfSignatureMap T sortMap result arity p
  invFun := signatureMap T sortMap result arity p
  left_inv := signatureMap_assignmentOfSignatureMap T sortMap result arity p
  right_inv := assignmentOfSignatureMap_signatureMap T sortMap result arity p

/-- For every target signature and every common map of sorts, a morphism
from the joined signature is exactly a compatible pair of operator images
from the component signatures. This is the signature universal property;
it does not require the sort map to be injective or surjective. -/
def signatureMapJoinEquiv (T : Signature) (sortMap : S.Srt → T.Srt)
    (result : Body → S.Srt) (arity : Body → List (List S.Srt × S.Srt))
    {p q r : Presentation Origin Label Body} (joined : join p q = some r) :
    SignatureMap T sortMap result arity r ≃
      CompatibleAssignments (OperatorImage T sortMap result arity) p q :=
  (signatureMapEquiv T sortMap result arity r).trans (assignmentJoinEquiv _ joined)

/-- Semantic argument vectors depend on sorts and binder contexts; changing
the operator inventory only repackages the same values. -/
noncomputable def toBaseArgs (result : Body → S.Srt) (arity : Body → List (List S.Srt × S.Srt))
    (p : Presentation Origin Label Body) {F : Ctx S → S.Srt → Type u}
    {args : List (List S.Srt × S.Srt)} {Γ : Ctx S}
    (values : FamilyArgs (signature S result arity p) F args Γ) : FamilyArgs S F args Γ :=
  FamilyArgs.rec (S := signature S result arity p) (F := F)
    (motive := fun args Γ _ => FamilyArgs S F args Γ)
    (fun {_Γ} => .nil) (fun head _tail ih => .cons head ih) values

noncomputable def fromBaseArgs (result : Body → S.Srt) (arity : Body → List (List S.Srt × S.Srt))
    (p : Presentation Origin Label Body) {F : Ctx S → S.Srt → Type u}
    {args : List (List S.Srt × S.Srt)} {Γ : Ctx S}
    (values : FamilyArgs S F args Γ) : FamilyArgs (signature S result arity p) F args Γ :=
  FamilyArgs.rec (S := S) (F := F)
    (motive := fun args Γ _ => FamilyArgs (signature S result arity p) F args Γ)
    (fun {_Γ} => .nil) (fun head _tail ih => .cons head ih) values

theorem toBase_fromBase (result : Body → S.Srt)
    (arity : Body → List (List S.Srt × S.Srt)) (p : Presentation Origin Label Body)
    {F : Ctx S → S.Srt → Type u} :
    ∀ {args : List (List S.Srt × S.Srt)} {Γ : Ctx S} (values : FamilyArgs S F args Γ),
      toBaseArgs result arity p (fromBaseArgs result arity p values) = values
  | _, _, .nil => rfl
  | _, _, .cons head tail => congrArg (FamilyArgs.cons head) (toBase_fromBase _ _ _ tail)

theorem fromBase_toBase (result : Body → S.Srt)
    (arity : Body → List (List S.Srt × S.Srt)) (p : Presentation Origin Label Body)
    {F : Ctx S → S.Srt → Type u} :
    ∀ {args : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (values : FamilyArgs (signature S result arity p) F args Γ),
      fromBaseArgs result arity p (toBaseArgs result arity p values) = values
  | _, _, .nil => rfl
  | _, _, .cons head tail => congrArg (FamilyArgs.cons head) (fromBase_toBase _ _ _ tail)

/-- Only the operator inventory changes. The whole shared substitution
algebra is retained, including its action in arbitrary binder contexts. -/
def substitution (A : BindingSubstitutionAlgebra.Algebra.{u} S)
    (result : Body → S.Srt) (arity : Body → List (List S.Srt × S.Srt))
    (p : Presentation Origin Label Body) :
    BindingSubstitutionAlgebra.Algebra.{u} (signature S result arity p) where
  Carrier := A.Carrier
  injectVar := A.injectVar
  substitute := A.substitute
  substitute_var := A.substitute_var
  substitute_identity := A.substitute_identity
  substitute_comp := A.substitute_comp

theorem liftEnvironment_substitution (A : BindingSubstitutionAlgebra.Algebra.{u} S)
    (result : Body → S.Srt) (arity : Body → List (List S.Srt × S.Srt))
    (p : Presentation Origin Label Body) {Γ Δ : Ctx S}
    (env : BindingSubstitutionAlgebra.Environment S A.Carrier Γ Δ) (binders : List S.Srt) :
    (substitution A result arity p).liftEnvironment env binders =
      A.liftEnvironment env binders := by
  induction binders with
  | nil => rfl
  | cons fresh binders ih =>
      funext sort index
      cases index with
      | zero => rfl
      | succ old =>
          exact congrArg (A.substitute (fun _ v => A.injectVar (.succ v)))
            (congrFun (congrFun ih sort) old)

theorem toBase_substituteArgs (A : BindingSubstitutionAlgebra.Algebra.{u} S)
    (result : Body → S.Srt) (arity : Body → List (List S.Srt × S.Srt))
    (p : Presentation Origin Label Body) {Γ Δ : Ctx S}
    (env : BindingSubstitutionAlgebra.Environment S A.Carrier Γ Δ) :
    ∀ {args : List (List S.Srt × S.Srt)}
      (values : FamilyArgs (signature S result arity p) A.Carrier args Γ),
      toBaseArgs result arity p ((substitution A result arity p).substituteArgs env values) =
        A.substituteArgs env (toBaseArgs result arity p values)
  | _, .nil => rfl
  | _, .cons (bs := binders) head tail => by
      exact congrArg₂ FamilyArgs.cons
        (congrArg (fun lifted => A.substitute lifted head)
          (liftEnvironment_substitution A result arity p env binders))
        (toBase_substituteArgs A result arity p env tail)

/-- One declaration's operation and its binder-aware substitution law,
extracted from the existing binding-clone algebra interface. -/
abbrev Operation (A : BindingSubstitutionAlgebra.Algebra.{u} S)
    (result : Body → S.Srt) (arity : Body → List (List S.Srt × S.Srt))
    (entry : Entry Origin Label Body) :=
  {operation : {Γ : Ctx S} → FamilyArgs S A.Carrier (arity entry.body) Γ →
      A.Carrier Γ (result entry.body) //
    ∀ {Γ Δ : Ctx S} (env : BindingSubstitutionAlgebra.Environment S A.Carrier Γ Δ)
      (args : FamilyArgs S A.Carrier (arity entry.body) Γ),
      A.substitute env (operation args) = operation (A.substituteArgs env args)}

/-- The glued assignments realize the established full binding-clone
algebra, not just a collection of untyped operator values. -/
noncomputable def algebra (A : BindingSubstitutionAlgebra.Algebra.{u} S)
    (result : Body → S.Srt) (arity : Body → List (List S.Srt × S.Srt))
    (p : Presentation Origin Label Body) (assignment : DependentAssignment (Operation A result arity) p) :
    BindingCloneAlgebra.Algebra.{u} (signature S result arity p) where
  substitution := substitution A result arity p
  operation op args := op.property ▸ (assignment op.val).val (toBaseArgs result arity p args)
  operation_substitute := by
    intro Γ Δ sort env op args
    rcases op with ⟨entry, equal⟩
    cases equal
    exact ((assignment entry).property env (toBaseArgs result arity p args)).trans
      (congrArg (fun values => (assignment entry).val values)
        (toBase_substituteArgs A result arity p env args).symm)

theorem algebra_operation (A : BindingSubstitutionAlgebra.Algebra.{u} S)
    (result : Body → S.Srt) (arity : Body → List (List S.Srt × S.Srt))
    (p : Presentation Origin Label Body) (assignment : DependentAssignment (Operation A result arity) p)
    (entry : Member p) {Γ : Ctx S}
    (args : FamilyArgs S A.Carrier (arity entry.val.body) Γ) :
    (algebra A result arity p assignment).operation ⟨entry, rfl⟩
      (fromBaseArgs result arity p args) = (assignment entry).val args := by
  change (assignment entry).val (toBaseArgs result arity p (fromBaseArgs result arity p args)) = _
  rw [toBase_fromBase]

theorem toBaseArgs_injective (result : Body → S.Srt)
    (arity : Body → List (List S.Srt × S.Srt)) (p : Presentation Origin Label Body)
    {F : Ctx S → S.Srt → Type u} {args : List (List S.Srt × S.Srt)} {Γ : Ctx S} :
    Function.Injective (@toBaseArgs _ _ _ _ _ _ S result arity p F args Γ) := by
  intro first second equal
  exact (fromBase_toBase result arity p first).symm.trans
    ((congrArg (fromBaseArgs result arity p) equal).trans (fromBase_toBase result arity p second))

theorem fromBase_substituteArgs (A : BindingSubstitutionAlgebra.Algebra.{u} S)
    (result : Body → S.Srt) (arity : Body → List (List S.Srt × S.Srt))
    (p : Presentation Origin Label Body) {Γ Δ : Ctx S}
    (env : BindingSubstitutionAlgebra.Environment S A.Carrier Γ Δ)
    {args : List (List S.Srt × S.Srt)} (values : FamilyArgs S A.Carrier args Γ) :
    fromBaseArgs result arity p (A.substituteArgs env values) =
      (substitution A result arity p).substituteArgs env (fromBaseArgs result arity p values) := by
  apply toBaseArgs_injective result arity p
  exact (toBase_fromBase result arity p _).trans
    ((congrArg (A.substituteArgs env) (toBase_fromBase result arity p values).symm).trans
      (toBase_substituteArgs A result arity p env _).symm)

/-- The fibre consists of existing binding-clone algebras whose full
substitution structure is the chosen shared parameter. -/
abbrev Model (A : BindingSubstitutionAlgebra.Algebra.{u} S)
    (result : Body → S.Srt) (arity : Body → List (List S.Srt × S.Srt))
    (p : Presentation Origin Label Body) :=
  {model : BindingCloneAlgebra.Algebra.{u} (signature S result arity p) //
    model.substitution = substitution A result arity p}

noncomputable def assignmentOfModel (A : BindingSubstitutionAlgebra.Algebra.{u} S)
    (result : Body → S.Srt) (arity : Body → List (List S.Srt × S.Srt))
    (p : Presentation Origin Label Body) (model : Model A result arity p) :
    DependentAssignment (Operation A result arity) p := by
  rcases model with ⟨⟨shared, operation, law⟩, same⟩
  dsimp at same
  subst shared
  exact fun entry => ⟨fun args => operation ⟨entry, rfl⟩ (fromBaseArgs result arity p args),
    fun env args => (law env ⟨entry, rfl⟩ (fromBaseArgs result arity p args)).trans
      (congrArg (operation ⟨entry, rfl⟩) (fromBase_substituteArgs A result arity p env args).symm)⟩

theorem assignmentOfModel_algebra (A : BindingSubstitutionAlgebra.Algebra.{u} S)
    (result : Body → S.Srt) (arity : Body → List (List S.Srt × S.Srt))
    (p : Presentation Origin Label Body) (assignment : DependentAssignment (Operation A result arity) p) :
    assignmentOfModel A result arity p ⟨algebra A result arity p assignment, rfl⟩ = assignment := by
  funext entry
  apply Subtype.ext
  funext Γ args
  exact algebra_operation A result arity p assignment entry args

theorem algebra_assignmentOfModel (A : BindingSubstitutionAlgebra.Algebra.{u} S)
    (result : Body → S.Srt) (arity : Body → List (List S.Srt × S.Srt))
    (p : Presentation Origin Label Body) (model : Model A result arity p) :
    algebra A result arity p (assignmentOfModel A result arity p model) = model.val := by
  rcases model with ⟨⟨shared, operation, law⟩, same⟩
  dsimp at same
  subst shared
  dsimp only [algebra, assignmentOfModel]
  congr 1
  funext Γ sort op args
  rcases op with ⟨entry, equal⟩
  cases equal
  exact congrArg (operation ⟨entry, rfl⟩) (fromBase_toBase result arity p args)

/-- Every algebra in the semantic fibre is represented by its actual
operations. Both inverse laws recover all operations, not a readout of them. -/
noncomputable def modelEquiv (A : BindingSubstitutionAlgebra.Algebra.{u} S)
    (result : Body → S.Srt) (arity : Body → List (List S.Srt × S.Srt))
    (p : Presentation Origin Label Body) :
    Model A result arity p ≃ DependentAssignment (Operation A result arity) p where
  toFun := assignmentOfModel A result arity p
  invFun assignment := ⟨algebra A result arity p assignment, rfl⟩
  left_inv model := Subtype.ext (algebra_assignmentOfModel A result arity p model)
  right_inv := assignmentOfModel_algebra A result arity p

/-- Models of the variable operator signature are exactly the compatible
dependent operation assignments from its two components. -/
noncomputable def modelJoinEquiv (A : BindingSubstitutionAlgebra.Algebra.{u} S)
    (result : Body → S.Srt) (arity : Body → List (List S.Srt × S.Srt))
    {p q r : Presentation Origin Label Body} (joined : join p q = some r) :
    Model A result arity r ≃ CompatibleAssignments (Operation A result arity) p q :=
  (modelEquiv A result arity r).trans (assignmentJoinEquiv _ joined)

/-- Signature inclusion carries substitution using the established general
signature-morphism theorem, including all lifts beneath binders. -/
theorem inclusion_bind (result : Body → S.Srt)
    (arity : Body → List (List S.Srt × S.Srt))
    {p q : Presentation Origin Label Body} (included : p.val ⊆ q.val)
    {Γ Δ : Ctx S} (env : Sub (signature S result arity p) Γ Δ)
    {sort : S.Srt} (term : Term (signature S result arity p) Γ sort) :
    mapTerm (inclusion result arity included) (fun _ v => v) (bind env term) =
      bind (fun s v => mapTerm (inclusion result arity included) (fun _ w => w) (env s v))
        (mapTerm (inclusion result arity included) (fun _ v => v) term) :=
  mapTerm_bind (inclusion result arity included) _ _ _ _ (fun _ _ => rfl) term

end Mettapedia.GSLT.LanguageDef.ModuleAlgebra.SignatureGluing
