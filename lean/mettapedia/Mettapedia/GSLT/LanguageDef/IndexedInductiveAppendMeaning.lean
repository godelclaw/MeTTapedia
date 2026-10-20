import Mettapedia.GSLT.LanguageDef.IndexedInductiveVectorMeaning
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorProgramChecking

/-!
# Forward execution of the existing dependent append core

The selected program is the independently authored natural/vector program.
Natural addition and its vector-producing constructor method execute with
the existing iota and beta rules. Their result is compared with the original
source vector append, retaining the actual element representation and index.
This operational comparison grants no new computation or typing authority.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.AppendMeaning

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeNaturalVectorFamilies Declaration.IndexedFamily
open TypedEquality.Normalization
open IndexedInductiveNatVec Meaning VectorMeaning

abbrev Executes {n : Nat} (left right : Tower.Tm n) := Steps iotaComputation left right

private theorem liftBeta {n : Nat} {left right : Tower.Tm n}
    (steps : TelescopeAbstraction.BetaSteps left right) : Executes left right := by
  apply Relation.ReflTransGen.mono (fun _ _ step => ?_) _ _ steps
  simpa only [Step, Tm.mapHead_id] using StepCore.mapHead (sourceRoot := RootComputation.empty) (sourceEq := fun _ _ => False) (targetRoot := iotaComputation)
    (targetEq := fun _ _ => False) (fun h => h) (fun impossible => impossible.elim)
    (fun impossible => impossible.elim) step

/-- The actual natural recursor computes addition on numeral representations. -/
theorem add_numerals {n : Nat} (first second : Nat) :
    Executes (n := n) (Programs.add (numeral first) (numeral second)) (numeral (first + second)) := by
  induction first with
  | zero =>
      simpa only [Nat.zero_add, Programs.add, numeral, Executes, Steps] using Relation.ReflTransGen.single
        (StepCore.root (root := iotaComputation) (headEq := fun _ _ => False)
          ⟨IotaEvidence.natZero (.lam natTm) (numeral (n := n) second) (.lam (.lam (succApp (.var 0))))⟩)
  | succ first ih =>
      refine Relation.ReflTransGen.head (.root ⟨IotaEvidence.natSucc _ _ _ _⟩) ?_
      refine Relation.ReflTransGen.head (.congAppFun (.betaPi _ _)) ?_
      change Executes (.app (.lam (succApp (.var 0)))
        (Programs.add (numeral first) (numeral second))) _
      refine Relation.ReflTransGen.head (.betaPi _ _) ?_
      change Executes (succApp (Programs.add (numeral first) (numeral second))) (numeral (first.succ + second))
      rw [Nat.succ_add]
      exact steps_app Relation.ReflTransGen.refl ih

theorem add_reduces (first second : Natural.Carrier) :
    Executes (Programs.add (quoteIndex first) (quoteIndex second))
      (quoteIndex (Natural.add first second)) := by
  unfold quoteIndex
  rw [Natural.toNat_add]
  exact add_numerals _ _

/-- The genuine four argument context of the append constructor method. -/
def methodContext (element secondLength : Tower.Tm 0) : Tower.Ctx 4 :=
  .snoc (.snoc (.snoc (.snoc .nil natTm) (rename (wkN 1) element))
    (vecApp (rename (wkN 2) element) (.var 1)))
    (vecApp (rename (wkN 3) element) (Programs.add (.var 2) (rename (wkN 3) secondLength)))

def methodBody (element secondLength : Tower.Tm 0) : Tower.Tm 4 :=
  vconsApp (rename (wkN 4) element) (Programs.add (.var 3) (rename (wkN 4) secondLength))
    (.var 2) (.var 0)

private theorem instantiate_closed_shift {k : Nat} (sigma : Sub Tower.Head (0 + k) 0) (term : Tower.Tm 0) :
    subst sigma (rename (wkN (n := 0) k) term) = term := by
  rw [subst_rename, TelescopeAbstraction.subst_empty, TelescopeAbstraction.liftClosed_zero]

/-- Four forward beta steps recover the original constructor expression;
the recursive result is retained and the new length still contains addition. -/
theorem method_beta (element secondLength length head tail result : Tower.Tm 0) :
    Executes (applyArgs (Programs.appendCons element secondLength) [length, head, tail, result])
      (vconsApp element (Programs.add length secondLength) head result) := by
  let assignment : Sub Tower.Head 4 0 :=
    Fin.cases result (Fin.cases tail (Fin.cases head (fun _ => length)))
  have beta := TelescopeAbstraction.applyClosed_beta (methodContext element secondLength)
    assignment (methodBody element secondLength)
  rw [TelescopeAbstraction.liftClosed_zero] at beta
  have target : subst assignment (methodBody element secondLength) =
      vconsApp element (Programs.add length secondLength) head result := by
    simp only [methodBody, vconsApp, subst, Programs.Computation.add_substitute]
    rw [instantiate_closed_shift (k := 4) assignment element, instantiate_closed_shift (k := 4) assignment secondLength]
    rfl
  rw [target] at beta
  exact liftBeta beta

theorem method_reduces {A : Type} (element : Tower.Tm 0) (payload : A → Tower.Tm 0)
    (first second : Natural.Carrier) (head : A) (tail result : Tower.Tm 0) :
    Executes (applyArgs (Programs.appendCons element (quoteIndex second))
      [quoteIndex first, payload head, tail, result])
      (vconsApp element (quoteIndex (Natural.add first second)) (payload head) result) := by
  apply (method_beta element (quoteIndex second) (quoteIndex first) (payload head) tail result).trans
  exact steps_app (steps_app (steps_app Relation.ReflTransGen.refl
    (add_reduces first second)) Relation.ReflTransGen.refl) Relation.ReflTransGen.refl

/-- Dependent vector-valued methods over the admitted source polynomial. -/
noncomputable def vectorMethods {A : Type} {m : Natural.Carrier}
    (right : Vectors.Vector A m) :
    Algebra.Displayed (Algebra.initial (Vectors.polynomial A))
      (fun _ length _ => Vectors.Vector A (Natural.add length m)) where
  act := by
    intro _ length shape children hypotheses
    rcases shape with ⟨occurrence, shape⟩
    revert shape children hypotheses
    refine Fin.cases ?_ (fun occurrence => ?_) occurrence
    · intro shape _children _hypotheses
      rcases shape with ⟨⟨same⟩⟩
      cases same
      exact right
    · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) occurrence
      intro shape _children hypotheses
      rcases shape with ⟨tailLength, head, ⟨⟨same⟩⟩⟩
      cases same
      exact Vectors.cons head (hypotheses none)

theorem vectorMethods_payload {A : Type} {n m : Natural.Carrier}
    (left : Vectors.Vector A n) (right : Vectors.Vector A m) :
    (Vectors.toList ((vectorMethods right).initialSection.toFun PUnit.unit n left)).val =
      (Vectors.toList left).val ++ (Vectors.toList right).val := by
  refine Fix.eliminate (Vectors.polynomial A) (fun environment length value =>
    (Vectors.toList ((vectorMethods right).initialSection.toFun environment length value)).val =
      ((Vectors.listMethods A).initialSection.toFun environment length value).val ++
        (Vectors.toList right).val) ?_ PUnit.unit n left
  intro environment length shape children hypotheses
  cases environment
  rcases shape with ⟨occurrence, shape⟩
  revert shape children hypotheses
  refine Fin.cases ?_ (fun occurrence => ?_) occurrence
  · intro shape _children _hypotheses
    rcases shape with ⟨⟨same⟩⟩
    cases same
    rfl
  · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) occurrence
    intro shape children hypotheses
    rcases shape with ⟨tailLength, head, ⟨⟨same⟩⟩⟩
    cases same
    exact congrArg (List.cons head) (hypotheses none)

/-- The displayed section is the independently defined source append. -/
theorem vectorMethods_meaning {A : Type} {n m : Natural.Carrier}
    (left : Vectors.Vector A n) (right : Vectors.Vector A m) :
    (vectorMethods right).initialSection.toFun PUnit.unit n left = Vectors.append left right := by
  apply (Vectors.listEquiv A (Natural.add n m)).injective
  apply Subtype.ext
  exact (vectorMethods_payload left right).trans (Vectors.append_payload left right).symm

noncomputable def guestMethods {A : Type} {m : Natural.Carrier}
    (element : Tower.Tm 0) (payload : A → Tower.Tm 0) (right : Vectors.Vector A m) :
    Fin (Vectors.admitted A).constructors.length → Tower.Tm 0 :=
  Fin.cases (encodeVector element payload right) (fun _ => Programs.appendCons element (quoteIndex m))

theorem methods_realize {A : Type} {m : Natural.Carrier}
    (element : Tower.Tm 0) (payload : A → Tower.Tm 0) (right : Vectors.Vector A m) :
    MethodsRealize (Vectors.admitted A) (types A element) (guestMethods element payload right)
      (quoteData payload) iotaComputation (vectorMethods right)
      (fun _ _ _ result => encodeVector element payload result) := by
  intro environment length shape children hypotheses
  cases environment
  rcases shape with ⟨occurrence, shape⟩
  revert shape children hypotheses
  refine Fin.cases ?_ (fun occurrence => ?_) occurrence
  · intro shape _children _hypotheses
    rcases shape with ⟨⟨same⟩⟩
    cases same
    exact Relation.ReflTransGen.refl
  · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) occurrence
    intro shape children hypotheses
    rcases shape with ⟨tailLength, head, ⟨⟨same⟩⟩⟩
    cases same
    exact method_reduces element payload tailLength m head
      (encodeVector element payload (children none)) (encodeVector element payload (hypotheses none))

/-- The independently authored vector roots implement the generated source
endpoints at arbitrary complete argument assignments. -/
theorem generated_roots (A : Type) (element motive : Tower.Tm 0)
    (method : Fin (Vectors.admitted A).constructors.length → Tower.Tm 0)
    (occurrence : Fin (Vectors.admitted A).constructors.length)
    (arguments : Fin (fieldCount ((Vectors.admitted A).constructors.get occurrence).body) → Tower.Tm 0) :
    iotaComputation.step
      (Types.endpoints (TypedControls.indexSyntax A) (Vectors.admitted A) occurrence (types A element)
        (.app (.const vecEliminateName) element) motive method arguments).1
      (Types.endpoints (TypedControls.indexSyntax A) (Vectors.admitted A) occurrence (types A element)
        (.app (.const vecEliminateName) element) motive method arguments).2 := by
  change Fin 2 → Tower.Tm 0 at method
  revert arguments
  refine Fin.cases ?_ (fun occurrence => ?_) occurrence
  · intro arguments
    exact ⟨IotaEvidence.vecNil element motive (method 0) (method 1)⟩
  · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) occurrence
    intro arguments
    change Fin 3 → Tower.Tm 0 at arguments
    exact ⟨IotaEvidence.vecCons element motive (method 0) (method 1)
      (arguments 0) (arguments 1) (arguments 2)⟩

/-- The existing vector-producing append core has a forward computation to
the represented source append, including canonical output length arithmetic.
This uses the generic dependent-meaning theorem, not a second append recursion. -/
theorem append_reduces {A : Type} (element : Tower.Tm 0) (payload : A → Tower.Tm 0)
    {n m : Natural.Carrier} (left : Vectors.Vector A n) (right : Vectors.Vector A m) :
    Executes (Programs.append element (quoteIndex n) (quoteIndex m)
      (encodeVector element payload left) (encodeVector element payload right))
      (encodeVector element payload (Vectors.append left right)) := by
  have computes := recursor_reduces (Vectors.admitted A) (TypedControls.indexSyntax A)
    (types A element) (.app (.const vecEliminateName) element)
    (Programs.appendMotive element (quoteIndex m)) (guestMethods element payload right)
    (quoteData payload) quoteIndex iotaComputation (constructors_quoted payload)
    (generated_roots A element _ _) (vectorMethods right)
    (fun _ _ _ result => encodeVector element payload result) (methods_realize element payload right)
    PUnit.unit n left
  rw [vectorMethods_meaning] at computes
  exact computes

/-- Applying the existing closed function performs its actual five beta
steps before entering the independently authored append body. -/
theorem appendTerm_beta (element firstLength secondLength left right : Tower.Tm 0) :
    Executes (applyArgs Programs.appendTerm [element, firstLength, secondLength, left, right])
      (Programs.append element firstLength secondLength left right) := by
  let assignment : Sub Tower.Head 5 0 :=
    Fin.cases right (Fin.cases left (Fin.cases secondLength (Fin.cases firstLength (fun _ => element))))
  have beta := TelescopeAbstraction.applyClosed_beta Programs.appendContext assignment Programs.appendBody
  rw [TelescopeAbstraction.liftClosed_zero] at beta
  have target : subst assignment Programs.appendBody =
      Programs.append element firstLength secondLength left right := by
    rw [Programs.appendBody, Programs.Computation.append_substitute]
    rfl
  rw [target] at beta
  exact liftBeta beta

/-- Closed-function execution preserves the full source append representation. -/
theorem appendTerm_reduces {A : Type} (element : Tower.Tm 0) (payload : A → Tower.Tm 0)
    {n m : Natural.Carrier} (left : Vectors.Vector A n) (right : Vectors.Vector A m) :
    Executes (applyArgs Programs.appendTerm [element, quoteIndex n, quoteIndex m,
      encodeVector element payload left, encodeVector element payload right])
      (encodeVector element payload (Vectors.append left right)) :=
  (appendTerm_beta _ _ _ _ _).trans (append_reduces element payload left right)

/-- The selected declared calculus includes the independently authored iota
roots. Its head equality and other permitted reductions are retained. -/
abbrev ProgramExecutes {n : Nat} (left right : Tower.Tm n) :=
  Relation.ReflTransGen (fun left right =>
    Step Programs.rules.headEq left right Programs.rules.computation) left right

theorem in_program {n : Nat} {left right : Tower.Tm n} (steps : Executes left right) :
    ProgramExecutes left right := by
  apply Relation.ReflTransGen.mono (fun _ _ step => ?_) _ _ steps
  simpa only [Step, Tm.mapHead_id] using StepCore.mapHead
    (sourceRoot := iotaComputation) (sourceEq := fun _ _ => False)
    (targetRoot := Programs.rules.computation) (targetEq := Programs.rules.headEq)
    (fun h => h) (fun impossible => impossible.elim)
    (fun evidence => by
      apply Declaration.RootStep.declared
      change iotaComputation.step _ _
      simpa only [Tm.mapHead_id] using evidence) step

theorem appendTerm_program {A : Type} (element : Tower.Tm 0) (payload : A → Tower.Tm 0)
    {n m : Natural.Carrier} (left : Vectors.Vector A n) (right : Vectors.Vector A m) :
    ProgramExecutes (applyArgs Programs.appendTerm [element, quoteIndex n, quoteIndex m,
      encodeVector element payload left, encodeVector element payload right])
      (encodeVector element payload (Vectors.append left right)) :=
  in_program (appendTerm_reduces element payload left right)

#print axioms add_reduces
#print axioms method_reduces
#print axioms append_reduces
#print axioms appendTerm_program

end Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.AppendMeaning
