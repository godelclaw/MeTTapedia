import Mettapedia.Languages.MM0.NaturalInduction

/-!
# Typed statements for the selected infinite HOL carrier

The definitions select an injective, non-surjective map and an omitted point
using the supplied HOL presentation's choice and infinity rules. Intrinsic
syntax supplies the five definition bodies and the six public statements.
The native proof producer must separately check against this specification.

This is a pointed infinite carrier, not yet its natural subtype or a recursion
theorem. No claim of full HOL-presentation adequacy follows from printing it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.NaturalCarrier

open Mettapedia.Logic.HOL
open HOLSyntaxWire NaturalClosure

universe w

inductive Base where
  | individual
  | parameter
  deriving DecidableEq, Repr

abbrev individual : Ty Base := .base .individual
abbrev parameter : Ty Base := .base .parameter

inductive Const : Ty Base → Type where
  | choose (type : Ty Base) : Const ((type ⇒ .prop) ⇒ type)
  | oneOne : Const ((individual ⇒ individual) ⇒ .prop)
  | onto : Const ((individual ⇒ individual) ⇒ .prop)
  | injection : Const ((individual ⇒ individual) ⇒ .prop)
  | successor : Const (individual ⇒ individual)
  | zero : Const individual
  | outside : Const (individual ⇒ .prop)

def encodeBase : Base → Wire
  | .individual => node "ind" []
  | .parameter => symbol "A"

def encodeConst {type : Ty Base} : Const type → Wire
  | .choose type => node "sel" [encodeType encodeBase type]
  | .oneOne => node "one_one" [node "ind" [], node "ind" []]
  | .onto => node "onto" [node "ind" [], node "ind" []]
  | .injection => node "infiniteInjection" []
  | .successor => node "infiniteSuccessor" []
  | .zero => node "infiniteZero" []
  | .outside => node "negativePredicate" [node "ind" [],
      node "rangePredicate" [node "ind" [], node "infiniteSuccessor" []]]

def noNames : Names ([] : Ctx Base)
  | _, index => nomatch index

def encodeClosed {type : Ty Base} (fresh : Nat → String)
    (term : Term Const [] type) : Wire :=
  encodeTerm encodeBase encodeConst fresh noNames 0 term

def injection : Term Const [] ((individual ⇒ individual) ⇒ .prop) :=
  .lam (.and (.app (.const .oneOne) (.var .vz))
    (.not (.app (.const .onto) (.var .vz))))

def successor : Term Const [] (individual ⇒ individual) :=
  .app (.const (.choose (individual ⇒ individual))) (.const .injection)

def negative : Term Const [parameter ⇒ .prop] (parameter ⇒ .prop) :=
  .lam (.not (.app (.var (.vs .vz)) (.var .vz)))

def range : Term Const [parameter ⇒ parameter] (parameter ⇒ .prop) :=
  .lam (.ex (.eq (.var (.vs .vz))
    (.app (.var (.vs (.vs .vz))) (.var .vz))))

def zero : Term Const [] individual :=
  .app (.const (.choose individual)) (.const .outside)

def injectionBody : Wire := encodeClosed (fun _ => "f") injection
def successorBody : Wire := encodeClosed (fun _ => "unused") successor
def negativeBody : Wire :=
  encodeTerm encodeBase encodeConst (fun _ => "x")
    (Names.lift "P" noNames) 0 negative
def rangeBody : Wire :=
  encodeTerm encodeBase encodeConst (fun n => if n = 0 then "y" else "x")
    (Names.lift "s" noNames) 0 range
def zeroBody : Wire := encodeClosed (fun _ => "unused") zero

def successorTyped : String :=
  statement "infiniteSuccessorT" "((var G wff ()))" []
    (typed (node "infiniteSuccessor" []) (arrow (node "ind" []) (node "ind" [])))

def successorInjective : String :=
  statement "infiniteSuccessorInjective" "((var G wff ()))" []
    (asserts (application (encodeConst .oneOne) (encodeConst .successor)))

def successorNotOnto : String :=
  statement "infiniteSuccessorNotOnto" "((var G wff ()))" []
    (asserts (node "notc" [application (encodeConst .onto) (encodeConst .successor)]))

def zeroTyped : String :=
  statement "infiniteZeroT" "((var G wff ()))" []
    (typed (encodeConst .zero) (node "ind" []))

def noPreimage : ClosedFormula Const :=
  .not (.ex (σ := individual) (.eq (.const .zero)
    (.app (.const .successor) (.var .vz))))

/-- The public negative existential means that the selected point is omitted,
including in general models; the individual domain is already fully admitted. -/
theorem noPreimage_meaning (model : HenkinModel.{0, 0, w} Base Const) :
    model.models noPreimage ↔
      ∀ number : model.Carrier .individual,
        model.constDen .successor number ≠ model.constDen .zero := by
  constructor
  · intro valid number same
    exact valid ⟨number, model.base_mem _ number, same.symm⟩
  · intro omitted ⟨number, _, same⟩
    exact omitted number same.symm

def noPreimageStatement : String :=
  statement "infiniteZeroNoPreimage" "((var G wff ()) (bound x term))" []
    (asserts (encodeClosed (fun _ => "x") noPreimage))

def notSuccessor : Term Const [individual] .prop :=
  .not (.eq (.const .zero) (.app (.const .successor) (.var .vz)))

def notSuccessorBody : Wire :=
  encodeTerm encodeBase encodeConst (fun _ => "unused")
    (Names.lift "n" noNames) 0 notSuccessor

def notSuccessorStatement : String :=
  statement "infiniteZeroNotSuccessor" "((var G wff ()) (var n term ()))"
    [typed (symbol "n") (node "ind" [])] (asserts notSuccessorBody)

def definitions : List (String × Wire) := [
  ("infiniteInjection", injectionBody), ("infiniteSuccessor", successorBody),
  ("negativePredicate", negativeBody), ("rangePredicate", rangeBody), ("infiniteZero", zeroBody)]

def statements : List (String × String) := [
  ("infiniteSuccessorT", successorTyped), ("infiniteSuccessorInjective", successorInjective),
  ("infiniteSuccessorNotOnto", successorNotOnto), ("infiniteZeroT", zeroTyped),
  ("infiniteZeroNoPreimage", noPreimageStatement), ("infiniteZeroNotSuccessor", notSuccessorStatement)]

def specification : String := NaturalInduction.specification ++
  "def infiniteInjection {.f: term}: term = $ " ++ injectionBody.render ++ " $;\n" ++
  "def infiniteSuccessor: term = $ " ++ successorBody.render ++ " $;\n" ++
  "theorem infiniteSuccessorT (G: wff): $ G |- infiniteSuccessor: ind -> ind $;\n" ++
  "theorem infiniteSuccessorInjective (G: wff): $ G |- one_one ind ind @ infiniteSuccessor $;\n" ++
  "theorem infiniteSuccessorNotOnto (G: wff): $ G |- ~(onto ind ind @ infiniteSuccessor) $;\n" ++
  "def negativePredicate (A: type) (P: term) {.x: term}: term = $ " ++ negativeBody.render ++ " $;\n" ++
  "def rangePredicate (A: type) (s: term) {.y .x: term}: term = $ " ++ rangeBody.render ++ " $;\n" ++
  "def infiniteZero: term = $ " ++ zeroBody.render ++ " $;\n" ++
  "theorem infiniteZeroT (G: wff): $ G |- infiniteZero: ind $;\n" ++
  "theorem infiniteZeroNoPreimage (G: wff) {x: term}:\n" ++
  " $ G |- ~(?x: ind. =[ind] infiniteZero = infiniteSuccessor @ x) $;\n" ++
  "theorem infiniteZeroNotSuccessor (G: wff) (n: term):\n" ++
  " $ G |- n: ind $ > $ G |- ~(=[ind] infiniteZero = infiniteSuccessor @ n) $;\n"

/-- Shared inherited definition/statement fields for proof-extension emitters.
The complete selected specification and core type-definition boundary stay
explicit arguments of each executable entry point. -/
def referenceFields : List (String × String) := [
    ("definition_body", NaturalClosure.definitionBody.render),
    ("strengthening_body", NaturalInduction.strengtheningBody.render),
    ("naturalClosureZero", NaturalClosure.zeroStatement),
    ("naturalClosureSuccessor", NaturalClosure.successorStatement),
    ("naturalClosureElimination", NaturalClosure.eliminationStatement),
    ("naturalClosureInduction", NaturalInduction.inductionStatement)] ++
  definitions.map (fun entry => (entry.1 ++ "_body", entry.2.render)) ++ statements

def verdicts : List (String × Bool) := [
  ("MM0 selected carrier keeps zero and successor distinct", zeroTyped != successorTyped),
  ("MM0 selected zero retains the outside-range predicate",
    zeroBody.render != successorBody.render),
  ("MM0 no-confusion retains its object-typing premise",
    notSuccessorStatement != statement "infiniteZeroNotSuccessor"
      "((var G wff ()) (var n term ()))" [] (asserts notSuccessorBody)),
  ("MM0 selected carrier definitions have distinct names", decide ((definitions.map Prod.fst).Nodup)),
  ("MM0 selected carrier statements have distinct names", decide ((statements.map Prod.fst).Nodup))]

theorem all_verdicts : verdicts.all Prod.snd = true := by decide +kernel

end Mettapedia.Languages.MM0.NaturalCarrier
