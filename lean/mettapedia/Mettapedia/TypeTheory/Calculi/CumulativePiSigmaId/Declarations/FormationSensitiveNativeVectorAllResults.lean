import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAll

import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.RecursorDerivation

/-!
# Constant-motive results from the actual native Vector All bundle

The object program projects one result per source position. Its raw canonical
computation and substitution laws are proved here. Independent typing replay
is in the checking companion; source-fold adaptation and arbitrary open-term
semantic decoding remain separate obligations.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.ResultView
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Declaration
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeNaturalVectorFamilies
open Mettapedia.TypeTheory.IndexedContainer

universe uWitness

private def weaken5 {n : Nat} (term : Tower.Tm n) : Tower.Tm (n + 5) :=
  rename wk (NativeVectorAll.weaken4 term)

def predicate {n : Nat} (result : Tower.Tm n) : Tower.Tm n :=
  .lam (rename wk result)

def motive {n : Nat} (element result : Tower.Tm n) : Tower.Tm n :=
  .lam (.lam (.pi
    (allType (weaken2 element) (predicate (weaken2 result)) (.var 1) (.var 0))
    (vecApp (rename wk (weaken2 result)) (.var 2))))

def nilCase {n : Nat} (result : Tower.Tm n) : Tower.Tm n :=
  .lam (vnilApp (rename wk result))

def consCase {n : Nat} (result : Tower.Tm n) : Tower.Tm n :=
  .lam (.lam (.lam (.lam (.lam
    (vconsApp (weaken5 result) (.var 4) (.fst (.var 0)) (.app (.var 1) (.snd (.var 0))))))))

def project {n : Nat} (element result length vector bundle : Tower.Tm n) : Tower.Tm n :=
  .app (vecEliminateApp element (motive element result) (nilCase result) (consCase result)
    length vector) bundle

def programType : Tower.Tm 0 :=
  .pi (sortTm NativeVectorAll.elementLevel)
    (.pi (sortTm NativeVectorAll.elementLevel)
      (.pi natTm
        (.pi (vecApp (.var 2) (.var 0))
          (.pi (allType (.var 3) (predicate (.var 2)) (.var 1) (.var 0))
            (vecApp (.var 3) (.var 2))))))

def program : Tower.Tm 0 :=
  .lam (.lam (.lam (.lam (.lam
    (project (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))))))

theorem subst_predicate {n m : Nat} (sigma : Sub Tower.Head n m) (result : Tower.Tm n) :
    subst sigma (predicate result) = predicate (subst sigma result) := by
  simp [predicate, subst]

theorem subst_motive {n m : Nat} (sigma : Sub Tower.Head n m) (element result : Tower.Tm n) :
    subst sigma (motive element result) = motive (subst sigma element) (subst sigma result) := by
  simp [motive, subst, subst_predicate]
  rfl

theorem subst_consCase {n m : Nat} (sigma : Sub Tower.Head n m) (result : Tower.Tm n) :
    subst sigma (consCase result) = consCase (subst sigma result) := by
  simp [consCase, vconsApp, subst, weaken5]
  rfl

theorem subst_project {n m : Nat} (sigma : Sub Tower.Head n m)
    (element result length vector bundle : Tower.Tm n) :
    subst sigma (project element result length vector bundle) =
      project (subst sigma element) (subst sigma result) (subst sigma length)
        (subst sigma vector) (subst sigma bundle) := by
  simp [project, nilCase, vecEliminateApp, vnilApp, subst, subst_motive, subst_consCase]


open CanonicalAdequacy
open TypedEquality.Normalization

/-! ## Vector elimination into an explicitly supplied result representation

The two case computations and actual iota roots imply the complete ordered
readout. The output constructor prefix is separate from its term arguments.
-/

namespace EvidenceElimination

def encode {n : Nat} (empty constructor : Tower.Tm n) : List (Tower.Tm n) → Tower.Tm n
  | [] => empty
  | head :: tail => appSpine constructor [numeral tail.length, head, encode empty constructor tail]

theorem encode_reduces {n : Nat} (R : Rules Tower.Head)
    (empty constructor : Tower.Tm n) {left right : List (Tower.Tm n)}
    (paths : List.Forall₂ (TypedEquality.Reduces R) left right) :
    TypedEquality.Reduces R (encode empty constructor left) (encode empty constructor right) := by
  induction paths with
  | nil => exact .refl
  | @cons first second left right headPath tailPaths ih =>
      have lengths := tailPaths.length_eq
      have firstPath := Relation.ReflTransGen.lift
        (fun value => appSpine constructor [numeral left.length, value,
          encode empty constructor left])
        (fun _ _ step => StepCore.congAppFun (StepCore.congAppArg step)) _ _ headPath
      have restPath := Relation.ReflTransGen.lift
        (fun value => appSpine constructor [numeral left.length, second, value])
        (fun _ _ step => StepCore.congAppArg step) _ _ ih
      simpa only [encode, lengths] using firstPath.trans restPath

theorem fold_reads {n : Nat} (R : Rules Tower.Head)
    (roots : ∀ {k : Nat} {left right : Tower.Tm k}, IotaEvidence k left right →
      R.computation.step left right)
    (element motive onNil onCons empty constructor : Tower.Tm n)
    (nil_beta : ∀ bundle : Tower.Tm n,
      TypedEquality.Reduces R (.app onNil bundle) empty)
    (cons_beta : ∀ length head tail recursive bundle : Tower.Tm n,
      TypedEquality.Reduces R
        (appSpine onCons [length, head, tail, recursive, bundle])
        (appSpine constructor [length, .fst bundle, .app recursive (.snd bundle)])) :
    ∀ (values : List (Tower.Tm n)) (bundle : Tower.Tm n),
      TypedEquality.Reduces R
        (.app (vecEliminateApp element motive onNil onCons
          (numeral values.length) (encodeVector element values)) bundle)
        (encode empty constructor (PairSpine.reads values.length bundle))
  | [], bundle => by
      apply Relation.ReflTransGen.head
      · exact .congAppFun (.root (roots (.vecNil element motive onNil onCons)))
      · exact nil_beta bundle
  | head :: tail, bundle => by
      have first : TypedEquality.Reduces R
          (.app (vecEliminateApp element motive onNil onCons
            (numeral (head :: tail).length) (encodeVector element (head :: tail))) bundle)
          (appSpine constructor [numeral tail.length, .fst bundle,
            .app (vecEliminateApp element motive onNil onCons
              (numeral tail.length) (encodeVector element tail)) (.snd bundle)]) := by
        apply Relation.ReflTransGen.head
        · exact .congAppFun (.root (roots (.vecCons element motive onNil onCons
            (numeral tail.length) head (encodeVector element tail))))
        · exact cons_beta (numeral tail.length) head (encodeVector element tail)
            (vecEliminateApp element motive onNil onCons
              (numeral tail.length) (encodeVector element tail)) bundle
      have rest := Relation.ReflTransGen.lift
        (fun value => appSpine constructor [numeral tail.length, .fst bundle, value])
        (fun _ _ step => StepCore.congAppArg step) _ _
        (fold_reads R roots element motive onNil onCons empty constructor nil_beta cons_beta
          tail (.snd bundle))
      simpa only [List.length_cons, PairSpine.reads, encode, PairSpine.reads_length]
        using first.trans rest

#print axioms fold_reads

theorem encode_vector {n : Nat} (result : Tower.Tm n) (values : List (Tower.Tm n)) :
    encode (vnilApp result) (.app (.const vconsName) result) values =
      encodeVector result values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      change vconsApp result (numeral tail.length) head
        (encode (vnilApp result) (.app (.const vconsName) result) tail) = _
      rw [ih]
      rfl

end EvidenceElimination

private theorem inst0_weaken {n : Nat} (value term : Tower.Tm n) :
    inst0 value (rename wk term) = term := by
  unfold inst0
  rw [subst_rename]
  change subst ids term = term
  exact subst_ids term

theorem nil_steps {n : Nat} (element result bundle : Tower.Tm n) :
    Steps (project element result zeroTm (vnilApp element) bundle) (vnilApp result) := by
  apply Relation.ReflTransGen.head
  · apply StepCore.congAppFun
    apply StepCore.root
    exact RootStep.declared ⟨IotaEvidence.vecNil element (motive element result) (nilCase result) (consCase result)⟩
  · change Steps (.app (.lam (rename wk (vnilApp result))) bundle) (vnilApp result)
    have beta := Relation.ReflTransGen.single
      (StepCore.betaPi (root := rules.computation) (headEq := rules.headEq)
        (rename wk (vnilApp result)) bundle)
    simpa only [inst0_weaken] using beta

theorem consCase_beta {n : Nat} (result length head tail recursive bundle : Tower.Tm n) :
    Steps (.app (.app (.app (.app (.app (consCase result) length) head) tail) recursive) bundle)
      (vconsApp result length (.fst bundle) (.app recursive (.snd bundle))) := by
  let body : Tower.Tm (n + 5) :=
    vconsApp (weaken5 result) (.var 4) (.fst (.var 0)) (.app (.var 1) (.snd (.var 0)))
  let sigma : Sub Tower.Head (n + 5) n :=
    consSub bundle (consSub recursive (consSub tail (consSub head (consSub length ids))))
  have beta := TypedEquality.Normalization.lams_beta (R := rules)
    5 body [length, head, tail, recursive, bundle] rfl
  have assignment : extendSub ids (fun j => [length, head, tail, recursive, bundle].getD j defaultTm) 5 = sigma := rfl
  rw [assignment] at beta
  have outer : subst sigma (weaken5 result) = result := by
    unfold weaken5 NativeVectorAll.weaken4
    rw [subst_rename, subst_rename]
    change subst ids result = result
    exact subst_ids result
  have target : subst sigma body =
      vconsApp result length (.fst bundle) (.app recursive (.snd bundle)) := by
    change vconsApp (subst sigma (weaken5 result)) length (.fst bundle) (.app recursive (.snd bundle)) = _
    rw [outer]
  rw [target] at beta
  exact beta

theorem cons_unfolds {n : Nat} (element result length head tail bundle : Tower.Tm n) :
    Steps (project element result (succApp length) (vconsApp element length head tail) bundle)
      (vconsApp result length (.fst bundle) (project element result length tail (.snd bundle))) := by
  apply Relation.ReflTransGen.head
  · apply StepCore.congAppFun
    apply StepCore.root
    exact RootStep.declared ⟨IotaEvidence.vecCons element (motive element result)
      (nilCase result) (consCase result) length head tail⟩
  · exact consCase_beta result length head tail
      (vecEliminateApp element (motive element result) (nilCase result) (consCase result) length tail) bundle


theorem cons_steps {n : Nat} (element result length head tail value rest : Tower.Tm n) :
    Steps (project element result (succApp length) (vconsApp element length head tail) (.pair value rest))
      (vconsApp result length value (project element result length tail rest)) := by
  refine (cons_unfolds element result length head tail (.pair value rest)).trans ?_
  apply Relation.ReflTransGen.head
  · exact .congAppFun (.congAppArg (.betaSigmaFst value rest))
  · exact Relation.ReflTransGen.single (.congAppArg (.congAppArg (.betaSigmaSnd value rest)))

/-! ## Arbitrary position witnesses and actual registered bundles

The canonical computation accepts any supplied evidence term. It reads one
projection at every source position. Quoted independent witnesses and actual
registered-container bundles specialize this law. The semantic quotation is
supplied explicitly; open source-term decoding remains separate.
-/

theorem canonical_steps_observe {n : Nat} (element result : Tower.Tm n) :
    ∀ (values : List (Tower.Tm n)) (bundle : Tower.Tm n),
      Steps (project element result (numeral values.length) (encodeVector element values) bundle)
        (encodeVector result (PairSpine.reads values.length bundle)) := by
  intro values bundle
  have computed := EvidenceElimination.fold_reads NativeVectorAll.rules
    (fun evidence => RootStep.declared ⟨evidence⟩)
    element (motive element result) (nilCase result) (consCase result)
    (vnilApp result) (.app (.const vconsName) result)
    (fun evidence => by
      change TypedEquality.Reduces NativeVectorAll.rules
        (.app (.lam (rename wk (vnilApp result))) evidence) (vnilApp result)
      have beta := Relation.ReflTransGen.single
        (StepCore.betaPi (root := NativeVectorAll.rules.computation)
          (headEq := NativeVectorAll.rules.headEq)
          (rename wk (vnilApp result)) evidence)
      simpa only [inst0_weaken] using beta)
    (consCase_beta result) values bundle
  simpa only [EvidenceElimination.encode_vector, project, Steps, TypedEquality.Reduces] using computed

/-- Reading the head positions does not require a canonical proof in the final tail. -/
theorem canonical_steps_assembled {n : Nat} (element result : Tower.Tm n)
    (values witnesses : List (Tower.Tm n)) (last : Tower.Tm n)
    (lengths : values.length = witnesses.length) :
    Steps (project element result (numeral values.length) (encodeVector element values)
      (PairSpine.assemble witnesses last)) (encodeVector result witnesses) := by
  refine (canonical_steps_observe element result values (PairSpine.assemble witnesses last)).trans ?_
  rw [lengths]
  exact encodeVector_reduces rules result
    (PairSpine.reads_of_reduces_to_assemble rules witnesses last (PairSpine.assemble witnesses last) .refl)

theorem canonical_steps_witnesses {n : Nat} (element result : Tower.Tm n)
    (values witnesses : List (Tower.Tm n)) (lengths : values.length = witnesses.length) :
    Steps (project element result (numeral values.length) (encodeVector element values)
      (quoteWitnesses witnesses)) (encodeVector result witnesses) :=
  canonical_steps_assembled element result values witnesses unitEvidence lengths

theorem semanticBundle_steps {n : Nat} (element result : Tower.Tm n)
    {P : Tower.Tm n → Type uWitness} (read : ∀ value, P value → Tower.Tm n)
    (values : List (Tower.Tm n))
    (bundle : (vectorInductionBundle P).Bundle (semanticValue values)) :
    let witnesses := List.ofFn fun position : Fin values.length =>
      read (values.get position) ((vectorInductionBundle P).exact (semanticValue values) bundle position)
    Steps (project element result (numeral values.length) (encodeVector element values)
      (quoteWitnesses witnesses)) (encodeVector result witnesses) := by
  dsimp only
  apply canonical_steps_witnesses
  exact List.length_ofFn.symm


theorem canonical_steps {n : Nat} (element result witness : Tower.Tm n)
    (values : List (Tower.Tm n)) :
    Steps (project element result (numeral values.length) (encodeVector element values)
      (quoteBundle (pointwiseBundle witness values)))
      (encodeVector result (values.map (fun value => .app witness value))) := by
  rw [quoteBundle_pointwise_eq_quoteWitnesses]
  exact canonical_steps_witnesses element result values
    (values.map (fun value => .app witness value)) (by simp only [List.length_map])

theorem program_beta (R : Rules Tower.Head) {n : Nat}
    (element result arity children bundle : Tower.Tm n) :
    TypedEquality.Reduces R
      (appSpine (liftClosed program) [element, result, arity, children, bundle])
      (project element result arity children bundle) := by
  let body : Tower.Tm (n + 5) := project (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)
  let sigma : Sub Tower.Head (n + 5) n :=
    consSub bundle (consSub children (consSub arity (consSub result (consSub element ids))))
  have beta := lams_beta (R := R) 5 body [element, result, arity, children, bundle] rfl
  have assigned : extendSub ids
      (fun j => [element, result, arity, children, bundle].getD j defaultTm) 5 = sigma := rfl
  rw [assigned] at beta
  have target : subst sigma body = project element result arity children bundle := by
    rw [show body = project (.var 4) (.var 3) (.var 2) (.var 1) (.var 0) from rfl, subst_project]
    rfl
  rw [target] at beta
  exact beta


#print axioms canonical_steps

#print axioms nil_steps
#print axioms consCase_beta
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.ResultView
