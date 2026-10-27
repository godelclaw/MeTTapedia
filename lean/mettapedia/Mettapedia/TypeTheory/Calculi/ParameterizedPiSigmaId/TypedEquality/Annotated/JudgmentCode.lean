import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Judgment

/-!
# Finite local codes for the annotated declarative judgment

The codes retain the original annotated syntax, contexts, displayed types and
ordered rule premises. Only primitive universe/declaration policies and an
explicit root decoder are consulted. Child derivations are separate replay
inputs; no typing or equality proof is stored in a code.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality.Annotated.Checking

variable {Head : Type} {R : Rules Head}

deriving instance DecidableEq for CCtx, CPremise, CStatement

structure RootResult (Head : Type) (n : Nat) where
  left : CTm Head n
  right : CTm Head n
  premises : List (CPremise Head n)
  deriving DecidableEq

/-- The primitive root provider exposes endpoints and the required premises.
Completeness concerns that local root relation, not arbitrary typechecking. -/
structure RootDecoder (computation : CRootComputation Head) where
  Code : Nat → Type
  decode : {n : Nat} → Code n → Option (RootResult Head n)
  sound : ∀ {n : Nat} {code : Code n} {result}, decode code = some result →
    computation.step result.left result.right ∧
    computation.requires result.left result.right result.premises
  complete : ∀ {n : Nat} {left right : CTm Head n} {premises},
    computation.step left right → computation.requires left right premises →
    ∃ code : Code n, decode code = some ⟨left, right, premises⟩

inductive Code (Head : Type) (RootCode : Nat → Type) : CStatement Head → Type where
  | headType {n : Nat} {Γ : CCtx Head n} {h u : Head} :
      Code Head RootCode (.typing Γ (.head h) (.head u))
  | var {n : Nat} {Γ : CCtx Head n} (i : Fin n) :
      Code Head RootCode (.typing Γ (.var i) (Γ.lookup i))
  | const {n : Nat} {Γ : CCtx Head n} {name : DeclName} {type : CTm Head 0} {u : Head} :
      Code Head RootCode (.typing Γ (.const name) type.liftClosed)
  | piForm {n : Nat} {Γ : CCtx Head n} {A : CTm Head n} {B : CTm Head (n + 1)}
      {u v w : Head} :
      Code Head RootCode (.typing Γ (.pi A B) (.head w))
  | sigmaForm {n : Nat} {Γ : CCtx Head n} {A : CTm Head n} {B : CTm Head (n + 1)}
      {u v w : Head} :
      Code Head RootCode (.typing Γ (.sigma A B) (.head w))
  | lamIntro {n : Nat} {Γ : CCtx Head n} {A : CTm Head n} {body B : CTm Head (n + 1)}
      {u w : Head} :
      Code Head RootCode (.typing Γ (.lam A body) (.pi A B))
  | appElim {n : Nat} {Γ : CCtx Head n} {g a A : CTm Head n} {B : CTm Head (n + 1)} :
      Code Head RootCode (.typing Γ (.app g a) (CTm.inst0 a B))
  | pairIntro {n : Nat} {Γ : CCtx Head n} {a b A : CTm Head n} {B : CTm Head (n + 1)}
      {u : Head} :
      Code Head RootCode (.typing Γ (.pair a b) (.sigma A B))
  | fstElim {n : Nat} {Γ : CCtx Head n} {p A : CTm Head n} {B : CTm Head (n + 1)} :
      Code Head RootCode (.typing Γ (.fst p) A)
  | sndElim {n : Nat} {Γ : CCtx Head n} {p A : CTm Head n} {B : CTm Head (n + 1)} :
      Code Head RootCode (.typing Γ (.snd p) (CTm.inst0 (.fst p) B))
  | idForm {n : Nat} {Γ : CCtx Head n} {A a b : CTm Head n} {u : Head} :
      Code Head RootCode (.typing Γ (.id A a b) (.head u))
  | reflIntro {n : Nat} {Γ : CCtx Head n} {a A : CTm Head n} :
      Code Head RootCode (.typing Γ (.refl a) (.id A a a))
  | sub {n : Nat} {Γ : CCtx Head n} {t A B : CTm Head n} :
      Code Head RootCode (.typing Γ t B)
  | conv {n : Nat} {Γ : CCtx Head n} {t A B : CTm Head n} {u : Head} :
      Code Head RootCode (.typing Γ t B)
  | refl {n : Nat} {Γ : CCtx Head n} {a A : CTm Head n} :
      Code Head RootCode (.equality Γ a a A)
  | symm {n : Nat} {Γ : CCtx Head n} {a b A : CTm Head n} :
      Code Head RootCode (.equality Γ b a A)
  | trans {n : Nat} {Γ : CCtx Head n} {a b c A : CTm Head n} :
      Code Head RootCode (.equality Γ a c A)
  | convEq {n : Nat} {Γ : CCtx Head n} {a b A B : CTm Head n} {u : Head} :
      Code Head RootCode (.equality Γ a b B)
  | subEq {n : Nat} {Γ : CCtx Head n} {a b A B : CTm Head n} :
      Code Head RootCode (.equality Γ a b B)
  | headEq {n : Nat} {Γ : CCtx Head n} {h h' : Head} {A : CTm Head n} :
      Code Head RootCode (.equality Γ (.head h) (.head h') A)
  | piCong {n : Nat} {Γ : CCtx Head n} {A A' : CTm Head n} {B B' : CTm Head (n + 1)}
      {u v w : Head} :
      Code Head RootCode (.equality Γ (.pi A B) (.pi A' B') (.head w))
  | sigmaCong {n : Nat} {Γ : CCtx Head n} {A A' : CTm Head n} {B B' : CTm Head (n + 1)}
      {u v w : Head} :
      Code Head RootCode (.equality Γ (.sigma A B) (.sigma A' B') (.head w))
  | idCong {n : Nat} {Γ : CCtx Head n} {A A' a a' b b' : CTm Head n} {u : Head} :
      Code Head RootCode (.equality Γ (.id A a b) (.id A' a' b') (.head u))
  | lamCong {n : Nat} {Γ : CCtx Head n} {A A' : CTm Head n} {body body' B : CTm Head (n + 1)}
      {u w : Head} :
      Code Head RootCode (.equality Γ (.lam A body) (.lam A' body') (.pi A B))
  | appCong {n : Nat} {Γ : CCtx Head n} {f g a b A : CTm Head n} {B : CTm Head (n + 1)} :
      Code Head RootCode (.equality Γ (.app f a) (.app g b) (CTm.inst0 a B))
  | pairCong {n : Nat} {Γ : CCtx Head n} {a a' b b' A : CTm Head n} {B : CTm Head (n + 1)}
      {u : Head} :
      Code Head RootCode (.equality Γ (.pair a b) (.pair a' b') (.sigma A B))
  | fstCong {n : Nat} {Γ : CCtx Head n} {p q A : CTm Head n} {B : CTm Head (n + 1)} :
      Code Head RootCode (.equality Γ (.fst p) (.fst q) A)
  | sndCong {n : Nat} {Γ : CCtx Head n} {p q A : CTm Head n} {B : CTm Head (n + 1)} :
      Code Head RootCode (.equality Γ (.snd p) (.snd q) (CTm.inst0 (.fst p) B))
  | reflCong {n : Nat} {Γ : CCtx Head n} {a b A : CTm Head n} :
      Code Head RootCode (.equality Γ (.refl a) (.refl b) (.id A a a))
  | betaPi {n : Nat} {Γ : CCtx Head n} {A a : CTm Head n} {body B : CTm Head (n + 1)}
      {u : Head} :
      Code Head RootCode (.equality Γ (.app (.lam A body) a) (CTm.inst0 a body) (CTm.inst0 a B))
  | betaFst {n : Nat} {Γ : CCtx Head n} {A a b : CTm Head n} {B : CTm Head (n + 1)}
      {u : Head} :
      Code Head RootCode (.equality Γ (.fst (.pair a b)) a A)
  | betaSnd {n : Nat} {Γ : CCtx Head n} {A a b : CTm Head n} {B : CTm Head (n + 1)}
      {u : Head} :
      Code Head RootCode (.equality Γ (.snd (.pair a b)) b (CTm.inst0 a B))
  | root {n : Nat} {Γ : CCtx Head n} {left right A : CTm Head n} (root : RootCode n) :
      Code Head RootCode (.equality Γ left right A)
  | etaPi {n : Nat} {Γ : CCtx Head n} {f g A : CTm Head n} {B : CTm Head (n + 1)} :
      Code Head RootCode (.equality Γ f g (.pi A B))
  | etaSigma {n : Nat} {Γ : CCtx Head n} {p q A : CTm Head n} {B : CTm Head (n + 1)} :
      Code Head RootCode (.equality Γ p q (.sigma A B))
  | subEqual {n : Nat} {Γ : CCtx Head n} {A B : CTm Head n} {u : Head} :
      Code Head RootCode (.sub Γ A B)
  | subUniv {n : Nat} {Γ : CCtx Head n} {u v : Head} :
      Code Head RootCode (.sub Γ (.head u) (.head v))
  | subPi {n : Nat} {Γ : CCtx Head n} {A A' : CTm Head n} {B B' : CTm Head (n + 1)}
      {u u' w : Head} :
      Code Head RootCode (.sub Γ (.pi A B) (.pi A' B'))
  | subSigma {n : Nat} {Γ : CCtx Head n} {A A' : CTm Head n} {B B' : CTm Head (n + 1)}
      {u u' : Head} :
      Code Head RootCode (.sub Γ (.sigma A B) (.sigma A' B'))
  | subTrans {n : Nat} {Γ : CCtx Head n} {A B C : CTm Head n} :
      Code Head RootCode (.sub Γ A C)

variable (P : ChurchRules R) [DecidableEq Head]
    [DecidableRel R.headTyping] [DecidablePred R.isUniverse]
    [∀ u v w, Decidable (R.join u v w)] [DecidableRel R.cumulative]
    [DecidableRel R.headEq]

/-- Check local side conditions and return every original child obligation. -/
def decode (decoder : RootDecoder P.computation) {statement : CStatement Head} :
    Code Head decoder.Code statement → Option (List (CStatement Head))
  | @Code.headType _ _ _n _Γ h u =>
      if R.headTyping h u then some [] else none
  | @Code.var _ _ _n _Γ _i =>
      some []
  | @Code.const _ _ _n _Γ name type u =>
      if P.constantType name = some type then if R.isUniverse u then some [(.typing .nil type (.head u))] else none else none
  | @Code.piForm _ _ _n Γ A B u v w =>
      if R.isUniverse u then if R.isUniverse v then if R.join u v w then some [(.typing Γ A (.head u)), (.typing (.snoc Γ A) B (.head v))] else none else none else none
  | @Code.sigmaForm _ _ _n Γ A B u v w =>
      if R.isUniverse u then if R.isUniverse v then if R.join u v w then some [(.typing Γ A (.head u)), (.typing (.snoc Γ A) B (.head v))] else none else none else none
  | @Code.lamIntro _ _ _n Γ A body B u w =>
      if R.isUniverse w then if R.isUniverse u then some [(.typing Γ A (.head w)), (.typing Γ (.pi A B) (.head u)), (.typing (.snoc Γ A) body B)] else none else none
  | @Code.appElim _ _ _n Γ g a A B =>
      some [(.typing Γ g (.pi A B)), (.typing Γ a A)]
  | @Code.pairIntro _ _ _n Γ a b A B u =>
      if R.isUniverse u then some [(.typing Γ (.sigma A B) (.head u)), (.typing Γ a A), (.typing Γ b (CTm.inst0 a B))] else none
  | @Code.fstElim _ _ _n Γ p A B =>
      some [(.typing Γ p (.sigma A B))]
  | @Code.sndElim _ _ _n Γ p A B =>
      some [(.typing Γ p (.sigma A B))]
  | @Code.idForm _ _ _n Γ A a b u =>
      if R.isUniverse u then some [(.typing Γ A (.head u)), (.typing Γ a A), (.typing Γ b A)] else none
  | @Code.reflIntro _ _ _n Γ a A =>
      some [(.typing Γ a A)]
  | @Code.sub _ _ _n Γ t A B =>
      some [(.typing Γ t A), (.sub Γ A B)]
  | @Code.conv _ _ _n Γ t A B u =>
      if R.isUniverse u then some [(.typing Γ t A), (.equality Γ A B (.head u))] else none
  | @Code.refl _ _ _n Γ a A =>
      some [(.typing Γ a A)]
  | @Code.symm _ _ _n Γ a b A =>
      some [(.equality Γ a b A)]
  | @Code.trans _ _ _n Γ a b c A =>
      some [(.equality Γ a b A), (.equality Γ b c A)]
  | @Code.convEq _ _ _n Γ a b A B u =>
      if R.isUniverse u then some [(.equality Γ a b A), (.equality Γ A B (.head u))] else none
  | @Code.subEq _ _ _n Γ a b A B =>
      some [(.equality Γ a b A), (.sub Γ A B)]
  | @Code.headEq _ _ _n Γ h h' A =>
      if R.headEq h h' then some [(.typing Γ (.head h) A), (.typing Γ (.head h') A)] else none
  | @Code.piCong _ _ _n Γ A A' B B' u v w =>
      if R.isUniverse u then if R.isUniverse v then if R.join u v w then some [(.equality Γ A A' (.head u)), (.equality (.snoc Γ A) B B' (.head v))] else none else none else none
  | @Code.sigmaCong _ _ _n Γ A A' B B' u v w =>
      if R.isUniverse u then if R.isUniverse v then if R.join u v w then some [(.equality Γ A A' (.head u)), (.equality (.snoc Γ A) B B' (.head v))] else none else none else none
  | @Code.idCong _ _ _n Γ A A' a a' b b' u =>
      if R.isUniverse u then some [(.equality Γ A A' (.head u)), (.equality Γ a a' A), (.equality Γ b b' A)] else none
  | @Code.lamCong _ _ _n Γ A A' body body' B u w =>
      if R.isUniverse w then if R.isUniverse u then some [(.equality Γ A A' (.head w)), (.typing Γ (.pi A B) (.head u)), (.equality (.snoc Γ A) body body' B)] else none else none
  | @Code.appCong _ _ _n Γ f g a b A B =>
      some [(.equality Γ f g (.pi A B)), (.equality Γ a b A)]
  | @Code.pairCong _ _ _n Γ a a' b b' A B u =>
      if R.isUniverse u then some [(.typing Γ (.sigma A B) (.head u)), (.equality Γ a a' A), (.equality Γ b b' (CTm.inst0 a B))] else none
  | @Code.fstCong _ _ _n Γ p q A B =>
      some [(.equality Γ p q (.sigma A B))]
  | @Code.sndCong _ _ _n Γ p q A B =>
      some [(.equality Γ p q (.sigma A B))]
  | @Code.reflCong _ _ _n Γ a b A =>
      some [(.equality Γ a b A)]
  | @Code.betaPi _ _ _n Γ A a body B u =>
      if R.isUniverse u then some [(.typing Γ (.pi A B) (.head u)), (.typing (.snoc Γ A) body B), (.typing Γ a A)] else none
  | @Code.betaFst _ _ _n Γ A a b B u =>
      if R.isUniverse u then some [(.typing Γ (.sigma A B) (.head u)), (.typing Γ a A), (.typing Γ b (CTm.inst0 a B))] else none
  | @Code.betaSnd _ _ _n Γ A a b B u =>
      if R.isUniverse u then some [(.typing Γ (.sigma A B) (.head u)), (.typing Γ a A), (.typing Γ b (CTm.inst0 a B))] else none
  | @Code.root _ _ _n Γ left right A code =>
      match decoder.decode code with
      | none => none
      | some result => if result.left = left ∧ result.right = right then
          some ([.typing Γ left A, .typing Γ right A] ++ result.premises.map (CPremise.statement Γ))
        else none
  | @Code.etaPi _ _ _n Γ f g A B =>
      some [(.typing Γ f (.pi A B)), (.typing Γ g (.pi A B)), (.equality (.snoc Γ A)
        (.app (f.rename wk) (.var 0)) (.app (g.rename wk) (.var 0)) B)]
  | @Code.etaSigma _ _ _n Γ p q A B =>
      some [(.typing Γ p (.sigma A B)), (.typing Γ q (.sigma A B)), (.equality Γ (.fst p) (.fst q) A), (.equality Γ (.snd p) (.snd q) (CTm.inst0 (.fst p) B))]
  | @Code.subEqual _ _ _n Γ A B u =>
      if R.isUniverse u then some [(.equality Γ A B (.head u))] else none
  | @Code.subUniv _ _ _n _Γ u v =>
      if R.cumulative u v then some [] else none
  | @Code.subPi _ _ _n Γ A A' B B' u u' w =>
      if R.isUniverse u then if R.isUniverse u' then if R.isUniverse w then some [(.typing Γ (.pi A B) (.head u)), (.typing Γ (.pi A' B') (.head u')), (.equality Γ A A' (.head w)), (.sub (.snoc Γ A) B B')] else none else none else none
  | @Code.subSigma _ _ _n Γ A A' B B' u u' =>
      if R.isUniverse u then if R.isUniverse u' then some [(.typing Γ (.sigma A B) (.head u)), (.typing Γ (.sigma A' B') (.head u')), (.sub Γ A A'), (.sub (.snoc Γ A) B B')] else none else none
  | @Code.subTrans _ _ _n Γ A B C =>
      some [(.sub Γ A B), (.sub Γ B C)]

end TypedEquality.Annotated.Checking
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
