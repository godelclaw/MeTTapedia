import Mettapedia.GSLT.LanguageDef.IndexedInductiveGuestMeaning
import Mettapedia.GSLT.LanguageDef.IndexedInductiveGuestPackageControls

/-!
# Generated vector elimination and length-checked list values

The actual admitted vector family is indexed by the admitted natural family.
Its generated guest eliminator reduces to the independently length-checked list
interpretation. All payloads, their order and the actual guest type parameter
are retained. The local methods are proved by forward beta reduction.

This is raw execution correctness in the selected generated-root calculus.
Guest typing of the list readout motive and backend implementation remain
separate obligations; no new conversion authority is inferred from this model.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.VectorMeaning

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Declaration.IndexedFamily NativeNaturalVectorFamilies
open IndexedInductiveNatVec Meaning

def numeral {n : Nat} : Nat → Tower.Tm n
  | 0 => zeroTm
  | k + 1 => succApp (numeral k)

noncomputable def quoteIndex (length : Natural.Carrier) : Tower.Tm 0 := numeral (Natural.toNat length)

@[simp] theorem quoteIndex_zero : quoteIndex Natural.zero = zeroTm := rfl
@[simp] theorem quoteIndex_succ (length : Natural.Carrier) :
    quoteIndex (Natural.succ length) = succApp (quoteIndex length) := rfl

noncomputable def quoteData {A : Type} (payload : A → Tower.Tm 0) :
    ∀ sort, Vectors.value A sort → Tower.Tm 0
  | .length, value => quoteIndex value
  | .payload, value => payload value

/-- Only the constructor indices are quoted literally. The broader index
language also contains addition, which is not licensed by this certificate. -/
theorem constructors_quoted {A : Type} (payload : A → Tower.Tm 0)
    (occurrence : Fin (Vectors.admitted A).constructors.length) :
    QuotedCode (TypedControls.indexSyntax A) (quoteData payload) quoteIndex
      ((Vectors.admitted A).constructors.get occurrence).body := by
  refine Fin.cases ?_ (fun occurrence => ?_) occurrence
  · intro environment
    rfl
  · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) occurrence
    constructor
    · intro environment; rfl
    · intro environment; rfl

noncomputable def types (A : Type) (parameter : Tower.Tm 0) :=
  ((DeclarationControls.vectorParameters A).types DeclarationControls.vectorNames).map
    (subst (fun _ => parameter))

noncomputable def encodeVector {A : Type} (parameter : Tower.Tm 0) (payload : A → Tower.Tm 0)
    {length : Natural.Carrier} (value : Vectors.Vector A length) : Tower.Tm 0 :=
  Meaning.encode (Vectors.admitted A) (quoteData payload) (types A parameter).constructor
    PUnit.unit length value

@[simp] theorem encode_nil {A : Type} (parameter : Tower.Tm 0) (payload : A → Tower.Tm 0) :
    encodeVector parameter payload Vectors.nil = vnilApp parameter := rfl

@[simp] theorem encode_cons {A : Type} (parameter : Tower.Tm 0) (payload : A → Tower.Tm 0)
    {length : Natural.Carrier} (head : A) (tail : Vectors.Vector A length) :
    encodeVector parameter payload (Vectors.cons head tail) =
      vconsApp parameter (quoteIndex length) (payload head) (encodeVector parameter payload tail) := rfl

/-- Lists use the existing pair syntax and a distinguished empty value. -/
def quoteList {A : Type} (payload : A → Tower.Tm 0) : List A → Tower.Tm 0
  | [] => .const `List.Empty
  | head :: tail => .pair (payload head) (quoteList payload tail)

def consMethod : Tower.Tm 0 := .lam (.lam (.lam (.lam (.pair (.var 2) (.var 0)))))

/-- This method receives length, payload, original tail and recursive result.
Only the recursive result is used as the new list tail. -/
theorem consMethod_reduces (root : RootComputation Tower.Head) (length head tail result : Tower.Tm 0) :
    Steps root (applyArgs consMethod [length, head, tail, result]) (.pair head result) := by
  change Steps root (.app (.app (.app (.app consMethod length) head) tail) result) _
  refine Relation.ReflTransGen.head
    (.congAppFun (.congAppFun (.congAppFun (.betaPi _ _)))) ?_
  change Steps root (.app (.app (.app
    (.lam (.lam (.lam (.pair (.var 2) (.var 0))))) head) tail) result) _
  refine Relation.ReflTransGen.head (.congAppFun (.congAppFun (.betaPi _ _))) ?_
  change Steps root (.app (.app (.lam (.lam
    (.pair (rename wk (rename wk head)) (.var 0)))) tail) result) _
  refine Relation.ReflTransGen.head (.congAppFun (.betaPi _ _)) ?_
  simp only [inst0, subst, subst_rename]
  have shifted : subst (fun i => liftSub (subst0 tail) (wk (wk i))) head = rename wk head := by
    change subst (fun i => rename wk (ids i)) head = _
    rw [← rename_subst, subst_ids]
  rw [shifted]
  change Steps root (.app (.lam (.pair (rename wk head) (.var 0))) result) _
  convert Relation.ReflTransGen.single
    (StepCore.betaPi (root := root) (headEq := fun _ _ => False)
      (.pair (rename wk head) (.var 0)) result) using 1
  simp only [inst0, subst, subst_rename]
  change Tm.pair head result = Tm.pair (subst ids head) result
  rw [subst_ids]


def methods (A : Type) : Fin (Vectors.admitted A).constructors.length → Tower.Tm 0 :=
  Fin.cases (.const `List.Empty) (fun _ => consMethod)

noncomputable def root (A : Type) :=
  (Package.computation (TypedControls.indexSyntax A) (DeclarationControls.vectorParameters A)
    DeclarationControls.vectorNames (Vectors.admitted A)).support

/-- Both local methods implement the existing genuinely indexed displayed
algebra: its result contains a list and its length equality. -/
theorem methods_realize {A : Type} (parameter : Tower.Tm 0) (payload : A → Tower.Tm 0) :
    MethodsRealize (Vectors.admitted A) (types A parameter) (methods A) (quoteData payload)
      (root A) (Vectors.listMethods A) (fun _ _ _ result => quoteList payload result.val) := by
  intro environment length shape children hypotheses
  cases environment
  rcases shape with ⟨occurrence, shape⟩
  revert shape children hypotheses
  refine Fin.cases ?_ (fun occurrence => ?_) occurrence
  · intro shape children hypotheses
    exact Relation.ReflTransGen.refl
  · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) occurrence
    intro shape children hypotheses
    rcases shape with ⟨tailLength, head, equation⟩
    exact consMethod_reduces (root A) (quoteIndex tailLength) (payload head)
      (encodeVector parameter payload (children none)) (quoteList payload (hypotheses none).val)

/-- The emitted constructor equations and beta reduction compute every
payload, in order, of the independent length-checked interpretation. -/
theorem readout_reduces {A : Type} (parameter motive : Tower.Tm 0) (payload : A → Tower.Tm 0)
    {length : Natural.Carrier} (value : Vectors.Vector A length) :
    Steps (root A)
      (vecEliminateApp parameter motive (.const `List.Empty) consMethod (quoteIndex length)
        (encodeVector parameter payload value))
      (quoteList payload (Vectors.toList value).val) := by
  exact package_reduces (Vectors.admitted A) (TypedControls.indexSyntax A) motive (methods A)
    (quoteData payload) quoteIndex (root A) (DeclarationControls.vectorParameters A)
    DeclarationControls.vectorNames (fun _ => parameter) (fun step => step)
    (constructors_quoted payload) (Vectors.listMethods A)
    (fun _ _ _ result => quoteList payload result.val) (methods_realize parameter payload)
    PUnit.unit length value

/-- Appending a fixed suffix is a dependent method family over the same
source polynomial. Its result is checked at the authored sum of lengths. -/
noncomputable def appendMethods {A : Type} {m : Natural.Carrier}
    (right : Vectors.Vector A m) :
    Algebra.Displayed (Algebra.initial (Vectors.polynomial A))
      (fun _ length _ => Vectors.ListVector A (Natural.add length m)) where
  act := by
    intro _ length shape children hypotheses
    rcases shape with ⟨occurrence, shape⟩
    revert shape children hypotheses
    refine Fin.cases ?_ (fun occurrence => ?_) occurrence
    · intro shape _children _hypotheses
      exact ⟨(Vectors.toList right).val, (Vectors.toList right).property.trans
        (congrArg (fun length => Natural.toNat (Natural.add length m)) shape.down.down)⟩
    · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) occurrence
      intro shape _children hypotheses
      rcases shape with ⟨tailLength, head, equation⟩
      exact ⟨head :: (hypotheses none).val,
        (congrArg Nat.succ (hypotheses none).property).trans
          (congrArg (fun length => Natural.toNat (Natural.add length m)) equation.down.down)⟩

/-- The new result is compared with ordinary list append, independently of
the guest program or its constructor rules. -/
theorem appendMethods_payload {A : Type} {n m : Natural.Carrier}
    (left : Vectors.Vector A n) (right : Vectors.Vector A m) :
    ((appendMethods right).initialSection.toFun PUnit.unit n left).val =
      (Vectors.toList left).val ++ (Vectors.toList right).val := by
  refine Fix.eliminate (Vectors.polynomial A) (fun environment length value =>
    ((appendMethods right).initialSection.toFun environment length value).val =
      ((Vectors.listMethods A).initialSection.toFun environment length value).val ++
        (Vectors.toList right).val) ?_ PUnit.unit n left
  intro environment length shape children hypotheses
  rcases shape with ⟨occurrence, shape⟩
  revert shape children hypotheses
  refine Fin.cases ?_ (fun occurrence => ?_) occurrence
  · intro shape _children _hypotheses; rfl
  · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) occurrence
    intro shape children hypotheses
    exact congrArg (List.cons shape.2.1) (hypotheses none)

theorem appendMethods_meaning {A : Type} {n m : Natural.Carrier}
    (left : Vectors.Vector A n) (right : Vectors.Vector A m) :
    (appendMethods right).initialSection.toFun PUnit.unit n left =
      Vectors.toList (Vectors.append left right) := by
  apply Subtype.ext
  exact (appendMethods_payload left right).trans (Vectors.append_payload left right).symm

noncomputable def appendGuestMethods {A : Type} {m : Natural.Carrier} (payload : A → Tower.Tm 0)
    (right : Vectors.Vector A m) : Fin (Vectors.admitted A).constructors.length → Tower.Tm 0 :=
  Fin.cases (quoteList payload (Vectors.toList right).val) (fun _ => consMethod)

theorem appendMethods_realize {A : Type} {m : Natural.Carrier}
    (parameter : Tower.Tm 0) (payload : A → Tower.Tm 0) (right : Vectors.Vector A m) :
    MethodsRealize (Vectors.admitted A) (types A parameter) (appendGuestMethods payload right)
      (quoteData payload) (root A) (appendMethods right)
      (fun _ _ _ result => quoteList payload result.val) := by
  intro environment length shape children hypotheses
  cases environment
  rcases shape with ⟨occurrence, shape⟩
  revert shape children hypotheses
  refine Fin.cases ?_ (fun occurrence => ?_) occurrence
  · intro shape children hypotheses
    exact Relation.ReflTransGen.refl
  · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) occurrence
    intro shape children hypotheses
    rcases shape with ⟨tailLength, head, equation⟩
    exact consMethod_reduces (root A) (quoteIndex tailLength) (payload head)
      (encodeVector parameter payload (children none)) (quoteList payload (hypotheses none).val)

/-- Generated elimination implements append's list realization, including
the complete ordered payload and the dependent source length. This does not
identify this realization with a separately elaborated guest append term. -/
theorem append_reduces {A : Type} (parameter motive : Tower.Tm 0) (payload : A → Tower.Tm 0)
    {n m : Natural.Carrier} (left : Vectors.Vector A n) (right : Vectors.Vector A m) :
    Steps (root A)
      (vecEliminateApp parameter motive (quoteList payload (Vectors.toList right).val)
        consMethod (quoteIndex n) (encodeVector parameter payload left))
      (quoteList payload (Vectors.toList (Vectors.append left right)).val) := by
  have computed := package_reduces (Vectors.admitted A) (TypedControls.indexSyntax A) motive
    (appendGuestMethods payload right) (quoteData payload) quoteIndex (root A)
    (DeclarationControls.vectorParameters A) DeclarationControls.vectorNames (fun _ => parameter)
    (fun step => step) (constructors_quoted payload) (appendMethods right)
    (fun _ _ _ result => quoteList payload result.val)
    (appendMethods_realize parameter payload right) PUnit.unit n left
  rw [appendMethods_meaning] at computed
  exact computed

/-- With an injective payload representation, the complete output packet
retains the list value. A mere length check would not give this conclusion. -/
theorem quoteList_injective {A : Type} {payload : A → Tower.Tm 0}
    (faithful : Function.Injective payload) : Function.Injective (quoteList payload) := by
  intro first second equal
  induction first generalizing second with
  | nil => cases second with
    | nil => rfl
    | cons head tail => cases equal
  | cons head tail ih => cases second with
    | nil => cases equal
    | cons head' tail' =>
        have paired := Tm.pair.inj equal
        exact congrArg₂ List.cons (faithful paired.1) (ih paired.2)

#print axioms readout_reduces
#print axioms append_reduces
#print axioms quoteList_injective

end Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.VectorMeaning
