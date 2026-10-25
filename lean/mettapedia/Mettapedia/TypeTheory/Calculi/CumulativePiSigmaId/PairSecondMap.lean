import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.Tower
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Structural
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.HeadMorphism
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.DeclarationSignature
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.RecursorDerivation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.BetaApplication

/-!
# Mapping the second component of a product

The first component is retained, while a supplied function maps the second.
The three carrier universes are independent. The derivation uses only the
ordinary formation, introduction and elimination rules, and may be installed
in a declaration extension by a typed substitution. No normalization or
computation facts about that extension are needed. The application equation
uses the shared primitive typed-beta construction under that substitution.
-/

set_option autoImplicit false
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation TypedEquality

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.PairSecondMap

def context (first source target : LevelExpr Nat) : Tower.Ctx 3 :=
  .snoc (.snoc (.snoc .nil (sortTm first)) (sortTm source)) (sortTm target)

def subject {n : Nat} : Tower.Tm n :=
  .lam (.lam (.pair (.fst (.var 0)) (.app (.var 1) (.snd (.var 0)))))

def displayed : Tower.Tm 3 :=
  .pi (.pi (.var 1) (.var 1))
    (.pi (.sigma (.var 3) (.var 3)) (.sigma (.var 4) (.var 3)))

theorem displayed_typed (first source target : LevelExpr Nat) :
    Typed Tower.rules (context first source target) displayed
      (sortTm (.max (.max source target) (.max (.max first source) (.max first target)))) := by
  refine Derivable.piForm (R := Tower.rules) ?_ (.sort _) ?_ (.sort _) (.sorts _ _)
  · exact .piForm (.var 1) (.sort source) (.var 1) (.sort target) (.sorts _ _)
  · refine Derivable.piForm ?_ (.sort _) ?_ (.sort _) (.sorts _ _)
    · exact .sigmaForm (.var 3) (.sort first) (.var 3) (.sort source) (.sorts _ _)
    · exact .sigmaForm (.var 4) (.sort first) (.var 3) (.sort target) (.sorts _ _)

def functionContext (first source target : LevelExpr Nat) : Tower.Ctx 4 :=
  .snoc (context first source target) (.pi (.var 1) (.var 1))

def bundleContext (first source target : LevelExpr Nat) : Tower.Ctx 5 :=
  .snoc (functionContext first source target) (.sigma (.var 3) (.var 3))

def innerType : Tower.Tm 4 := .pi (.sigma (.var 3) (.var 3)) (.sigma (.var 4) (.var 3))
def body : Tower.Tm 5 := .pair (.fst (.var 0)) (.app (.var 1) (.snd (.var 0)))
def resultType : Tower.Tm 5 := .sigma (.var 4) (.var 3)

theorem inner_formed (first source target : LevelExpr Nat) :
    Typed Tower.rules (functionContext first source target) innerType
      (sortTm (.max (.max first source) (.max first target))) :=
  .piForm (.sigmaForm (.var 3) (.sort first) (.var 3) (.sort source) (.sorts _ _))
    (.sort _) (.sigmaForm (.var 4) (.sort first) (.var 3) (.sort target) (.sorts _ _))
    (.sort _) (.sorts _ _)

theorem body_typed (first source target : LevelExpr Nat) :
    Typed Tower.rules (bundleContext first source target) body resultType := by
  refine Derivable.pairIntro (u := .sort (.max first target)) ?_ (.sort _) ?_ ?_
  · exact .sigmaForm (.var 4) (.sort first) (.var 3) (.sort target) (.sorts _ _)
  · exact .fstElim (.var 0)
  · exact .appElim (A := .var 3) (B := .var 3) (.var 1)
      (.sndElim (A := .var 4) (B := .var 4) (.var 0))

theorem typed (first source target : LevelExpr Nat) :
    Typed Tower.rules (context first source target) subject displayed :=
  .lamIntro (displayed_typed first source target) (.sort _)
    (.lamIntro (inner_formed first source target) (.sort _) (body_typed first source target))

def arguments {n : Nat} (first source target : Tower.Tm n) : Sub Tower.Head 3 n :=
  consSub target (consSub source (consSub first Fin.elim0))

def typeAt {n : Nat} (first source target : Tower.Tm n) : Tower.Tm n :=
  .pi (.pi source (rename wk target))
    (.pi (.sigma (rename wk first) (rename wk (rename wk source)))
      (.sigma (rename wk (rename wk first)) (rename wk (rename wk (rename wk target)))))

theorem typeAt_expanded {n : Nat} (first source target : Tower.Tm n) :
    typeAt first source target =
      .pi (.pi source (rename wk target))
        (rename wk (.pi (.sigma first (rename wk source))
          (rename wk (.sigma first (rename wk target))))) := by
  simp only [typeAt, rename, rename_liftRen_wk]

theorem substitute_typeAt {n m : Nat} (sigma : Sub Tower.Head n m)
    (first source target : Tower.Tm n) :
    subst sigma (typeAt first source target) =
      typeAt (subst sigma first) (subst sigma source) (subst sigma target) := by
  simp only [typeAt, subst, subst_liftSub_wk]

theorem type_readback {n : Nat} (first source target : Tower.Tm n) :
    subst (arguments first source target) displayed = typeAt first source target := rfl

theorem subject_readback {n : Nat} (first source target : Tower.Tm n) :
    subst (arguments first source target) subject = (subject : Tower.Tm n) := rfl

theorem substitute_subject {n m : Nat} (sigma : Sub Tower.Head n m) :
    subst sigma (subject : Tower.Tm n) = (subject : Tower.Tm m) := rfl

theorem assignment (signature : Declaration.Signature Tower.Head)
    {n : Nat} {ambient : Tower.Ctx n} {a s t : LevelExpr Nat}
    {first source target : Tower.Tm n}
    (firstTyped : Typed (Declaration.extendRules Tower.rules signature) ambient first (sortTm a))
    (sourceTyped : Typed (Declaration.extendRules Tower.rules signature) ambient source (sortTm s))
    (targetTyped : Typed (Declaration.extendRules Tower.rules signature) ambient target (sortTm t)) :
    SubstMor (Declaration.extendRules Tower.rules signature) (context a s t) ambient
      (arguments first source target) := by
  intro index
  fin_cases index
  · exact targetTyped
  · exact sourceTyped
  · exact firstTyped

theorem instantiate_typed (signature : Declaration.Signature Tower.Head)
    {n : Nat} {ambient : Tower.Ctx n} {a s t : LevelExpr Nat}
    {first source target : Tower.Tm n}
    (firstTyped : Typed (Declaration.extendRules Tower.rules signature) ambient first (sortTm a))
    (sourceTyped : Typed (Declaration.extendRules Tower.rules signature) ambient source (sortTm s))
    (targetTyped : Typed (Declaration.extendRules Tower.rules signature) ambient target (sortTm t)) :
    Typed (Declaration.extendRules Tower.rules signature) ambient subject (typeAt first source target) := by
  have linked := ((typed a s t).of_morphism
    (Declaration.includeMorphism Tower.rules signature)).substitute
      (assignment signature firstTyped sourceTyped targetTyped)
  simpa only [type_readback, subject_readback] using linked

theorem instantiate_type_typed (signature : Declaration.Signature Tower.Head)
    {n : Nat} {ambient : Tower.Ctx n} {a s t : LevelExpr Nat}
    {first source target : Tower.Tm n}
    (firstTyped : Typed (Declaration.extendRules Tower.rules signature) ambient first (sortTm a))
    (sourceTyped : Typed (Declaration.extendRules Tower.rules signature) ambient source (sortTm s))
    (targetTyped : Typed (Declaration.extendRules Tower.rules signature) ambient target (sortTm t)) :
    Typed (Declaration.extendRules Tower.rules signature) ambient (typeAt first source target)
      (sortTm (.max (.max s t) (.max (.max a s) (.max a t)))) := by
  have linked := ((displayed_typed a s t).of_morphism
    (Declaration.includeMorphism Tower.rules signature)).substitute
      (assignment signature firstTyped sourceTyped targetTyped)
  simpa only [type_readback, sortTm, subst] using linked

theorem beta_at (signature : Declaration.Signature Tower.Head)
    {n : Nat} {ambient : Tower.Ctx n} {a s t : LevelExpr Nat}
    {first source target function bundle : Tower.Tm n}
    (firstTyped : Typed (Declaration.extendRules Tower.rules signature) ambient first (sortTm a))
    (sourceTyped : Typed (Declaration.extendRules Tower.rules signature) ambient source (sortTm s))
    (targetTyped : Typed (Declaration.extendRules Tower.rules signature) ambient target (sortTm t))
    (functionTyped : Typed (Declaration.extendRules Tower.rules signature) ambient function
      (.pi source (rename wk target)))
    (bundleTyped : Typed (Declaration.extendRules Tower.rules signature) ambient bundle
      (.sigma first (rename wk source))) :
    Equal (Declaration.extendRules Tower.rules signature) ambient
      (.app (.app subject function) bundle) (.pair (.fst bundle) (.app function (.snd bundle)))
      (.sigma first (rename wk target)) := by
  let sigma := arguments first source target
  have firstAt : Typed (Declaration.extendRules Tower.rules signature) ambient function
      (subst sigma (.pi (.var 1) (.var 1))) := by
    exact functionTyped
  have secondAt : Typed (Declaration.extendRules Tower.rules signature) ambient bundle
      (subst (consSub function sigma) (.sigma (.var 3) (.var 3))) := by
    exact bundleTyped
  have equation := betaPi_two_substitute
    ((displayed_typed a s t).of_morphism (Declaration.includeMorphism Tower.rules signature)) (.sort _)
    ((inner_formed a s t).of_morphism (Declaration.includeMorphism Tower.rules signature)) (.sort _)
    ((body_typed a s t).of_morphism (Declaration.includeMorphism Tower.rules signature))
    (assignment signature firstTyped sourceTyped targetTyped) firstAt secondAt
  exact equation

def run {n : Nat} (function bundle : Tower.Tm n) : Tower.Tm n :=
  .app (.app subject function) bundle

theorem computes (R : Rules Tower.Head) {n : Nat} (function bundle : Tower.Tm n) :
    Reduces R (run function bundle) (.pair (.fst bundle) (.app function (.snd bundle))) := by
  have beta := Normalization.lams_beta (R := R) 2
    (.pair (.fst (.var 0)) (.app (.var 1) (.snd (.var 0))) : Tower.Tm (n + 2))
    [function, bundle] rfl
  exact beta

theorem computes_pair (R : Rules Tower.Head) {n : Nat}
    (function first second : Tower.Tm n) :
    Reduces R (run function (.pair first second)) (.pair first (.app function second)) := by
  refine (computes R function (.pair first second)).trans ?_
  refine Relation.ReflTransGen.head (.congPairFst (.betaSigmaFst first second)) ?_
  exact .single (.congPairSnd (.congAppArg (.betaSigmaSnd first second)))

theorem reads_first (R : Rules Tower.Head) {n : Nat}
    (function first second : Tower.Tm n) :
    Reduces R (.fst (run function (.pair first second))) first :=
  (Relation.ReflTransGen.lift Tm.fst (fun _ _ step => .congFst step) _ _
    (computes_pair R function first second)).tail (.betaSigmaFst first (.app function second))

theorem distinct_pairs : (Tm.pair (.var 0) (.var 0) : Tower.Tm 2) ≠ .pair (.var 1) (.var 0) := by
  intro same
  have components := Tm.pair.inj same
  cases components.1

/-- Equal second components do not identify the retained first components. -/
theorem distinct_first_control :
    ((Tm.pair (.var 0) (.var 0) : Tower.Tm 2) ≠ .pair (.var 1) (.var 0)) ∧
    Reduces Tower.rules (.snd (.pair (.var 0) (.var 0) : Tower.Tm 2)) (.var 0) ∧
    Reduces Tower.rules (.snd (.pair (.var 1) (.var 0) : Tower.Tm 2)) (.var 0) := by
  exact ⟨distinct_pairs, .single (.betaSigmaSnd _ _), .single (.betaSigmaSnd _ _)⟩

#print axioms typed
#print axioms instantiate_typed
#print axioms beta_at
#print axioms reads_first
#print axioms distinct_first_control

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.PairSecondMap
