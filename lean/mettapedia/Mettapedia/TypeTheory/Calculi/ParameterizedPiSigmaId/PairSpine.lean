import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Algorithm
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.HeadMorphism
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Structural
import Mathlib.Data.List.Forall2

/-!
# Raw pair spines and finite projection readouts

A pair expansion retains each head projection and its final tail under the
ordinary contextual pair reductions. The operations quantify over the actual
scoped syntax and any supplied rule package. They leave that package unchanged.
The final tail is retained as data. Computation and readout laws use ordinary
contextual reduction; reconstruction uses the separately stated typed pair eta
rule and the formation of each dependent projection fibre.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.PairSpine

variable {Head : Type} {n : Nat}

def tail : Nat → Tm Head n → Tm Head n
  | 0, term => term
  | count + 1, term => tail count (.snd term)

def head (position : Nat) (term : Tm Head n) : Tm Head n := .fst (tail position term)

def reads : Nat → Tm Head n → List (Tm Head n)
  | 0, _ => []
  | count + 1, term => .fst term :: reads count (.snd term)

def expand : Nat → Tm Head n → Tm Head n
  | 0, term => term
  | count + 1, term => .pair (.fst term) (expand count (.snd term))

def assemble (heads : List (Tm Head n)) (last : Tm Head n) : Tm Head n :=
  heads.foldr Tm.pair last

@[simp] theorem reads_length (count : Nat) (term : Tm Head n) :
    (reads count term).length = count := by
  induction count generalizing term with
  | zero => rfl
  | succ count ih => exact congrArg Nat.succ (ih (.snd term))

theorem reads_getElem? (count position : Nat) (term : Tm Head n)
    (inside : position < count) :
    (reads count term)[position]? = some (head position term) := by
  induction count generalizing position term with
  | zero => exact (Nat.not_lt_zero position inside).elim
  | succ count ih =>
      cases position with
      | zero => rfl
      | succ position => exact ih position (.snd term) (Nat.lt_of_succ_lt_succ inside)

theorem tail_reduces (R : Rules Head) (count : Nat) {left right : Tm Head n}
    (path : TypedEquality.Reduces R left right) :
    TypedEquality.Reduces R (tail count left) (tail count right) := by
  induction count generalizing left right with
  | zero => exact path
  | succ count ih =>
      exact ih (Relation.ReflTransGen.lift Tm.snd (fun _ _ step => StepCore.congSnd step) _ _ path)

theorem head_reduces (R : Rules Head) (position : Nat) {left right : Tm Head n}
    (path : TypedEquality.Reduces R left right) :
    TypedEquality.Reduces R (head position left) (head position right) :=
  Relation.ReflTransGen.lift Tm.fst (fun _ _ step => StepCore.congFst step)
    _ _ (tail_reduces R position path)

theorem head_expand (R : Rules Head) (count position : Nat) (term : Tm Head n)
    (inside : position < count) :
    TypedEquality.Reduces R (head position (expand count term)) (head position term) := by
  induction count generalizing position term with
  | zero => exact (Nat.not_lt_zero position inside).elim
  | succ count ih =>
      cases position with
      | zero => exact Relation.ReflTransGen.single (.betaSigmaFst _ _)
      | succ position =>
          exact (head_reduces R position
            (Relation.ReflTransGen.single (.betaSigmaSnd _ _))).trans
              (ih position (.snd term) (Nat.lt_of_succ_lt_succ inside))

theorem tail_expand (R : Rules Head) (count : Nat) (term : Tm Head n) :
    TypedEquality.Reduces R (tail count (expand count term)) (tail count term) := by
  induction count generalizing term with
  | zero => exact .refl
  | succ count ih =>
      exact (tail_reduces R count
        (Relation.ReflTransGen.single (.betaSigmaSnd _ _))).trans (ih (.snd term))

/-- A supplied reduction can be replayed at every copied projection in an
expansion; a step may therefore become several contextual steps. -/
theorem expand_reduces (R : Rules Head) (count : Nat) {left right : Tm Head n}
    (path : TypedEquality.Reduces R left right) :
    TypedEquality.Reduces R (expand count left) (expand count right) := by
  induction count generalizing left right with
  | zero => exact path
  | succ count ih =>
      have first := Relation.ReflTransGen.lift Tm.fst
        (fun _ _ step => StepCore.congFst step) _ _ path
      have rest := ih (Relation.ReflTransGen.lift Tm.snd
        (fun _ _ step => StepCore.congSnd step) _ _ path)
      exact (Relation.ReflTransGen.lift
        (fun value => Tm.pair value (expand count (.snd left)))
        (fun _ _ step => StepCore.congPairFst step) _ _ first).trans
          (Relation.ReflTransGen.lift (Tm.pair (.fst right))
            (fun _ _ step => StepCore.congPairSnd step) _ _ rest)

/-- Repeating the same expansion adds no retained data. Projection beta
contracts the second expansion without identifying the terminal inhabitant. -/
theorem expand_idempotent (R : Rules Head) (count : Nat) (term : Tm Head n) :
    TypedEquality.Reduces R (expand count (expand count term)) (expand count term) := by
  induction count generalizing term with
  | zero => exact .refl
  | succ count ih =>
      have first := Relation.ReflTransGen.lift
        (fun value => Tm.pair value (expand count (.snd (expand (count + 1) term))))
        (fun _ _ step => StepCore.congPairFst step) _ _
          (Relation.ReflTransGen.single (StepCore.betaSigmaFst
            (root := R.computation) (headEq := R.headEq)
            (.fst term) (expand count (.snd term))))
      have rest := expand_reduces R count
        (Relation.ReflTransGen.single (.betaSigmaSnd (.fst term) (expand count (.snd term))))
      exact first.trans ((Relation.ReflTransGen.lift (Tm.pair (.fst term))
        (fun _ _ step => StepCore.congPairSnd step) _ _ rest).trans
          (Relation.ReflTransGen.lift (Tm.pair (.fst term))
            (fun _ _ step => StepCore.congPairSnd step) _ _ (ih (.snd term))))

theorem reads_of_reduces_to_assemble (R : Rules Head) (heads : List (Tm Head n))
    (last term : Tm Head n) (path : TypedEquality.Reduces R term (assemble heads last)) :
    List.Forall₂ (TypedEquality.Reduces R) (reads heads.length term) heads := by
  induction heads generalizing term with
  | nil => exact .nil
  | cons first rest ih =>
      refine .cons ?_ ?_
      · exact (Relation.ReflTransGen.lift Tm.fst (fun _ _ step => StepCore.congFst step) _ _ path).tail
          (.betaSigmaFst _ _)
      · exact ih (.snd term)
          ((Relation.ReflTransGen.lift Tm.snd (fun _ _ step => StepCore.congSnd step) _ _ path).tail
            (.betaSigmaSnd _ _))

theorem expand_of_reduces_to_assemble (R : Rules Head) (heads : List (Tm Head n))
    (last term : Tm Head n) (path : TypedEquality.Reduces R term (assemble heads last)) :
    TypedEquality.Reduces R (expand heads.length term) (assemble heads last) := by
  induction heads generalizing term with
  | nil => exact path
  | cons first rest ih =>
      have firstPath := (Relation.ReflTransGen.lift Tm.fst
        (fun _ _ step => StepCore.congFst step) _ _ path).tail (.betaSigmaFst _ _)
      have restPath := ih (.snd term)
        ((Relation.ReflTransGen.lift Tm.snd
          (fun _ _ step => StepCore.congSnd step) _ _ path).tail (.betaSigmaSnd _ _))
      exact (Relation.ReflTransGen.lift
        (fun value => Tm.pair value (expand rest.length (.snd term)))
        (fun _ _ step => StepCore.congPairFst step) _ _ firstPath).trans
          (Relation.ReflTransGen.lift (Tm.pair first)
            (fun _ _ step => StepCore.congPairSnd step) _ _ restPath)

/-- The retained readout contains exactly the data used by expansion. -/
theorem expand_eq_assemble_reads_tail (count : Nat) (term : Tm Head n) :
    expand count term = assemble (reads count term) (tail count term) := by
  induction count generalizing term with
  | zero => rfl
  | succ count ih =>
      change Tm.pair (.fst term) (expand count (.snd term)) =
        Tm.pair (.fst term) (assemble (reads count (.snd term)) (tail count (.snd term)))
      rw [ih]

@[simp] theorem subst_expand {m : Nat} (sigma : Sub Head n m)
    (count : Nat) (term : Tm Head n) :
    subst sigma (expand count term) = expand count (subst sigma term) := by
  induction count generalizing term with
  | zero => rfl
  | succ count ih => simp only [expand, subst, ih]

@[simp] theorem mapHead_expand {Other : Type} (map : Head → Other)
    (count : Nat) (term : Tm Head n) :
    (expand count term).mapHead map = expand count (term.mapHead map) := by
  induction count generalizing term with
  | zero => rfl
  | succ count ih => simp only [expand, Tm.mapHead, ih]

/-! ## Reconstruction at typed dependent pair spines -/

open TypedEquality

/-- Formation data for the successive dependent pair types of a supplied term.
The terminal fibre is arbitrary: in particular it need not be a unit type and
its inhabitants are never identified. No equality or reduction is assumed. -/
inductive TypedSpine (R : Rules Head) (context : Ctx Head n) :
    Nat → Tm Head n → Tm Head n → Prop where
  | zero {term type : Tm Head n} (typing : Typed R context term type) :
      TypedSpine R context 0 term type
  | succ {count : Nat} {term domain : Tm Head n} {codomain : Tm Head (n + 1)}
      {sort : Head}
      (formed : Typed R context (.sigma domain codomain) (.head sort))
      (isUniverse : R.isUniverse sort)
      (typing : Typed R context term (.sigma domain codomain))
      (rest : TypedSpine R context count (.snd term) (inst0 (.fst term) codomain)) :
      TypedSpine R context (count + 1) term (.sigma domain codomain)

/-- Typed substitution transports the successive dependent projection fibres. -/
theorem TypedSpine.substitute {R : Rules Head} {context : Ctx Head n}
    {count : Nat} {term type : Tm Head n}
    (spine : TypedSpine R context count term type)
    {m : Nat} {target : Ctx Head m} {sigma : Sub Head n m}
    (images : SubstMor R context target sigma) :
    TypedSpine R target count (subst sigma term) (subst sigma type) := by
  induction spine with
  | zero typing => exact .zero (typing.substitute images)
  | succ formed isUniverse typing rest ih =>
      simp only [subst, subst_inst0] at ih ⊢
      exact .succ (formed.substitute images) isUniverse (typing.substitute images) ih

/-- A rule-package morphism transports the whole typed spine, including its
terminal type. The morphism must preserve the actual declared computations. -/
theorem TypedSpine.mapHead {Other : Type} {source : Rules Head} {target : Rules Other}
    {map : Head → Other} (morphism : source.Morphism target map)
    {context : Ctx Head n} {count : Nat} {term type : Tm Head n}
    (spine : TypedSpine source context count term type) :
    TypedSpine target (context.mapHead map) count (term.mapHead map) (type.mapHead map) := by
  induction spine with
  | zero typing => exact .zero (typing.mapHead morphism)
  | succ formed isUniverse typing rest ih =>
      simp only [Tm.mapHead, Tm.mapHead_inst0] at ih ⊢
      exact .succ (formed.mapHead morphism) (morphism.isUniverse isUniverse)
        (typing.mapHead morphism) ih

/-- Pair eta reconstructs every finite, well-formed dependent spine, including
an arbitrary neutral supplied bundle and its unchanged terminal inhabitant.
The judgment is typed eta equality, rather than raw beta/iota conversion. -/
theorem TypedSpine.expand_typed_and_equal {R : Rules Head} {context : Ctx Head n}
    {count : Nat} {term type : Tm Head n}
    (spine : TypedSpine R context count term type) :
    Typed R context (expand count term) type ∧
      Equal R context (expand count term) term type := by
  induction spine with
  | zero typing => exact ⟨typing, .refl typing⟩
  | @succ count term domain codomain sort formed isUniverse typing rest ih =>
      have first : Typed R _ (.fst term) domain := .fstElim typing
      have last : Typed R _ (.snd term) (inst0 (.fst term) codomain) := .sndElim typing
      have pairTyped : Typed R _ (.pair (.fst term) (.snd term)) (.sigma domain codomain) :=
        .pairIntro formed isUniverse first last
      have eta : Equal R _ term (.pair (.fst term) (.snd term)) (.sigma domain codomain) :=
        .etaSigma typing pairTyped (.symm (.betaFst formed isUniverse first last))
          (.symm (.betaSnd formed isUniverse first last))
      exact ⟨.pairIntro formed isUniverse first ih.1,
        .trans (.pairCong formed isUniverse (.refl first) ih.2) (.symm eta)⟩

/-- Typed comparison of the ordered heads and retained final tail. Each tail
comparison uses its dependent fibre at the left head; equal heads can require
transport into that fibre. Literal equality of projection syntax is not
required. At depth zero the remaining tail itself must be compared. -/
def ReadoutEqual (R : Rules Head) (context : Ctx Head n) :
    Nat → Tm Head n → Tm Head n → Tm Head n → Prop
  | 0, left, right, type => Equal R context left right type
  | count + 1, left, right, type =>
      ∃ (domain : Tm Head n) (codomain : Tm Head (n + 1)),
        type = .sigma domain codomain ∧
        Typed R context left type ∧ Typed R context right type ∧
        Equal R context (.fst left) (.fst right) domain ∧
        ReadoutEqual R context count (.snd left) (.snd right) (inst0 (.fst left) codomain)

/-- Comparing every retained projection reconstructs a whole-bundle typed
equality by dependent pair eta. The terminal comparison is indispensable. -/
theorem equal_of_readout {R : Rules Head} {context : Ctx Head n}
    {count : Nat} {left right type : Tm Head n}
    (comparison : ReadoutEqual R context count left right type) :
    Equal R context left right type := by
  induction count generalizing left right type with
  | zero => exact comparison
  | succ count ih =>
      obtain ⟨domain, codomain, rfl, leftTyped, rightTyped, first, rest⟩ := comparison
      exact .etaSigma leftTyped rightTyped first (ih rest)

/-- Reconstruction also produces an object identity witness. The witness is
reflexivity checked through typed pair eta; identity reflection, K and unit
eta are not used. -/
theorem TypedSpine.expand_identity {R : Rules Head} {context : Ctx Head n}
    {count : Nat} {term type : Tm Head n} {sort : Head}
    (spine : TypedSpine R context count term type)
    (formed : Typed R context type (.head sort)) (isUniverse : R.isUniverse sort) :
    Typed R context (.refl (expand count term)) (.id type (expand count term) term) := by
  obtain ⟨expanded, eta⟩ := spine.expand_typed_and_equal
  exact .conv (.reflIntro expanded)
    (.idCong (.refl formed) isUniverse (.refl expanded) eta) isUniverse

#print axioms head_expand
#print axioms tail_expand
#print axioms reads_of_reduces_to_assemble
#print axioms expand_idempotent
#print axioms TypedSpine.substitute
#print axioms TypedSpine.mapHead
#print axioms TypedSpine.expand_typed_and_equal
#print axioms equal_of_readout
#print axioms TypedSpine.expand_identity

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.PairSpine
