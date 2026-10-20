import Mettapedia.GSLT.LanguageDef.KernelAuthority
import Mettapedia.TypeTheory.FreeConversion
import Mathlib.Logic.Relation

/-!
# Composable recipes over a checked equality comparison

A comparison algorithm need not be transitive. Its successful comparisons
can nevertheless be leaves of explicit reflexivity, symmetry and transitivity
proofs. This checker computes endpoints and checks the intermediate join;
the independent meaning is the equivalence closure of the leaf relation.

Coverage of that closure does not imply completeness for a larger ideal
equality. A leaf translator gives a recipe translator only after its endpoint
and acceptance laws have been proved. No algorithmic time bound is inferred.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.EqualityRecipe

open Mettapedia.GSLT.LanguageDef.KernelAuthority

universe u v w x

inductive Recipe (Term : Type u) (Evidence : Type v) where
  | leaf (source target : Term) (evidence : Evidence)
  | refl (term : Term)
  | symm (proof : Recipe Term Evidence)
  | trans (first second : Recipe Term Evidence)

def Recipe.nodes {Term : Type u} {Evidence : Type v} : Recipe Term Evidence → Nat
  | .leaf _ _ _ | .refl _ => 1
  | .symm proof => proof.nodes + 1
  | .trans first second => first.nodes + second.nodes + 1

def Recipe.leaves {Term : Type u} {Evidence : Type v} : Recipe Term Evidence → Nat
  | .leaf _ _ _ => 1
  | .refl _ => 0
  | .symm proof => proof.leaves
  | .trans first second => first.leaves + second.leaves

variable {Term : Type u} {Evidence : Type v} [DecidableEq Term]

/-- Endpoints are recomputed from checked leaves. In particular, transitivity
refuses when the computed middle endpoints differ. -/
def evaluate (comparison : Checker (Term × Term) Evidence) :
    Recipe Term Evidence → Option (Term × Term)
  | .leaf source target evidence =>
      if comparison.check (source, target) evidence then some (source, target) else none
  | .refl term => some (term, term)
  | .symm proof => (evaluate comparison proof).map Prod.swap
  | .trans first second => do
      let (source, middle) ← evaluate comparison first
      let (middle', target) ← evaluate comparison second
      if middle = middle' then some (source, target) else none

def checker (comparison : Checker (Term × Term) Evidence) :
    Checker (Term × Term) (Recipe Term Evidence) where
  check claim proof := decide (evaluate comparison proof = some claim)

theorem check_iff (comparison : Checker (Term × Term) Evidence)
    (claim : Term × Term) (proof : Recipe Term Evidence) :
    (checker comparison).check claim proof = true ↔ evaluate comparison proof = some claim := by
  simp [checker]

theorem evaluate_sound (comparison : Checker (Term × Term) Evidence)
    {Rel : Term → Term → Prop}
    (sound : comparison.Sound (fun claim => Rel claim.1 claim.2))
    (proof : Recipe Term Evidence) (source target : Term)
    (accepted : evaluate comparison proof = some (source, target)) :
    Relation.EqvGen Rel source target := by
  induction proof generalizing source target with
  | leaf left right evidence =>
      cases checked : comparison.check (left, right) evidence with
      | false => simp [evaluate, checked] at accepted
      | true =>
          have same : (left, right) = (source, target) := by
            simpa [evaluate, checked] using accepted
          cases same
          exact .rel _ _ (sound _ _ checked)
  | refl term =>
      have same : (term, term) = (source, target) := by simpa [evaluate] using accepted
      cases same
      exact .refl _
  | symm proof ih =>
      cases computed : evaluate comparison proof with
      | none => simp [evaluate, computed] at accepted
      | some pair =>
          obtain ⟨left, right⟩ := pair
          have same : (right, left) = (source, target) := by
            simpa [evaluate, computed, Prod.swap] using accepted
          cases same
          exact .symm _ _ (ih _ _ computed)
  | trans first second ihFirst ihSecond =>
      cases computedFirst : evaluate comparison first with
      | none => simp [evaluate, computedFirst] at accepted
      | some pair =>
          obtain ⟨left, middle⟩ := pair
          cases computedSecond : evaluate comparison second with
          | none => simp [evaluate, computedFirst, computedSecond] at accepted
          | some pair =>
              obtain ⟨middle', right⟩ := pair
              by_cases sameMiddle : middle = middle'
              · subst middle'
                have same : (left, right) = (source, target) := by
                  simpa [evaluate, computedFirst, computedSecond] using accepted
                cases same
                exact .trans _ _ _ (ihFirst _ _ computedFirst) (ihSecond _ _ computedSecond)
              · simp [evaluate, computedFirst, computedSecond, sameMiddle] at accepted

theorem evaluate_complete (comparison : Checker (Term × Term) Evidence)
    {Rel : Term → Term → Prop}
    (complete : comparison.CertificateComplete (fun claim => Rel claim.1 claim.2))
    {source target : Term} (valid : Relation.EqvGen Rel source target) :
    ∃ proof, evaluate comparison proof = some (source, target) := by
  induction valid with
  | rel source target valid =>
      obtain ⟨evidence, accepted⟩ := complete (source, target) valid
      exact ⟨.leaf source target evidence, by simp [evaluate, accepted]⟩
  | refl term => exact ⟨.refl term, rfl⟩
  | symm source target _ ih =>
      obtain ⟨proof, accepted⟩ := ih
      exact ⟨.symm proof, by simp [evaluate, accepted, Prod.swap]⟩
  | trans source middle target _ _ ihFirst ihSecond =>
      obtain ⟨first, acceptedFirst⟩ := ihFirst
      obtain ⟨second, acceptedSecond⟩ := ihSecond
      exact ⟨.trans first second, by simp [evaluate, acceptedFirst, acceptedSecond]⟩

/-- The compositional checker has exact authority for the independently
generated equality, even if a single leaf comparison is nontransitive. -/
theorem authority (comparison : Checker (Term × Term) Evidence)
    {Rel : Term → Term → Prop}
    (exactLeaf : comparison.Authority (fun claim => Rel claim.1 claim.2)) :
    (checker comparison).Authority (fun claim => Relation.EqvGen Rel claim.1 claim.2) where
  sound claim proof accepted := evaluate_sound comparison exactLeaf.sound proof _ _
    ((check_iff comparison claim proof).mp accepted)
  complete claim valid := by
    obtain ⟨proof, accepted⟩ := evaluate_complete comparison exactLeaf.complete valid
    exact ⟨proof, (check_iff comparison claim proof).mpr accepted⟩

/-- Sound comparison leaves compose into ideal equality proofs. This does
not claim that every ideal equality is generated by those leaves. -/
theorem sound_for_ideal (comparison : Checker (Term × Term) Evidence)
    {Ideal : Term → Term → Prop} (ideal : Equivalence Ideal)
    (sound : comparison.Sound (fun claim => Ideal claim.1 claim.2)) :
    (checker comparison).Sound (fun claim => Ideal claim.1 claim.2) := by
  intro claim proof accepted
  have generated := evaluate_sound comparison sound proof _ _
    ((check_iff comparison claim proof).mp accepted)
  exact ideal.eqvGen_iff.mp generated

theorem trans_checked (comparison : Checker (Term × Term) Evidence)
    (first second : Recipe Term Evidence) (source middle target : Term)
    (firstAccepted : (checker comparison).check (source, middle) first = true)
    (secondAccepted : (checker comparison).check (middle, target) second = true) :
    (checker comparison).check (source, target) (.trans first second) = true := by
  apply (check_iff comparison _ _).mpr
  simp [evaluate, (check_iff comparison _ _).mp firstAccepted,
    (check_iff comparison _ _).mp secondAccepted]

theorem symm_checked (comparison : Checker (Term × Term) Evidence)
    (proof : Recipe Term Evidence) (source target : Term)
    (accepted : (checker comparison).check (source, target) proof = true) :
    (checker comparison).check (target, source) (.symm proof) = true := by
  apply (check_iff comparison _ _).mpr
  simp [evaluate, (check_iff comparison _ _).mp accepted, Prod.swap]

/-! ## Recovering retained evidence from successful replay -/

/-- The primitive evidence of the generated conversion is an actual accepted
leaf, including its submitted witness. -/
abbrev AcceptedLeaf (comparison : Checker (Term × Term) Evidence)
    (source target : Term) :=
  { evidence : Evidence // comparison.check (source, target) evidence = true }

/-- The maintained free conversion carrier retains every checked leaf and
composition node. The single index here fixes the recipe's term domain;
typed clients instantiate that domain at their context and type. -/
abbrev CheckedPath (comparison : Checker (Term × Term) Evidence)
    (source target : Term) :=
  Mettapedia.TypeTheory.FreeConversion.Path (fun _ : Unit => Term)
    (fun {_index : Unit} (left right : Term) => AcceptedLeaf comparison left right)
    (index := ()) source target

private def replayAlgebra (comparison : Checker (Term × Term) Evidence) :
    Mettapedia.TypeTheory.FreeConversion.Algebra (fun _ : Unit => Term)
      (fun {_index : Unit} (left right : Term) => AcceptedLeaf comparison left right)
      (fun {_index : Unit} (left right : Term) =>
        { recipe : Recipe Term Evidence // evaluate comparison recipe = some (left, right) }) where
  onStep {_index} {source target} evidence :=
    ⟨.leaf source target evidence.1, by simp [evaluate, evidence.2]⟩
  onRefl term := ⟨.refl term, rfl⟩
  onSymm recipe := ⟨.symm recipe.1, by simp [evaluate, recipe.2, Prod.swap]⟩
  onTrans first second := ⟨.trans first.1 second.1, by simp [evaluate, first.2, second.2]⟩

/-- Rebuild the submitted syntax using the common free-conversion fold. Its
receipt records successful replay at exactly the original endpoints. -/
def forgetPath (comparison : Checker (Term × Term) Evidence)
    {source target : Term} (path : CheckedPath comparison source target) : Recipe Term Evidence :=
  ((replayAlgebra comparison).fold path).1

@[simp] theorem forgetPath_step (comparison : Checker (Term × Term) Evidence)
    {source target : Term} (evidence : AcceptedLeaf comparison source target) :
    forgetPath comparison (.step evidence) = .leaf source target evidence.1 := by
  simp only [forgetPath, Mettapedia.TypeTheory.FreeConversion.Algebra.fold, replayAlgebra]

@[simp] theorem forgetPath_refl (comparison : Checker (Term × Term) Evidence) (term : Term) :
    forgetPath comparison (.refl term) = .refl term := by
  simp only [forgetPath, Mettapedia.TypeTheory.FreeConversion.Algebra.fold, replayAlgebra]

@[simp] theorem forgetPath_symm (comparison : Checker (Term × Term) Evidence)
    {source target : Term} (path : CheckedPath comparison source target) :
    forgetPath comparison (.symm path) = .symm (forgetPath comparison path) := by
  simp only [forgetPath, Mettapedia.TypeTheory.FreeConversion.Algebra.fold, replayAlgebra]

@[simp] theorem forgetPath_trans (comparison : Checker (Term × Term) Evidence)
    {source middle target : Term} (first : CheckedPath comparison source middle)
    (second : CheckedPath comparison middle target) :
    forgetPath comparison (.trans first second) =
      .trans (forgetPath comparison first) (forgetPath comparison second) := by
  simp only [forgetPath, Mettapedia.TypeTheory.FreeConversion.Algebra.fold, replayAlgebra]

/-- Replay of retained evidence reconstructs its endpoints. -/
theorem evaluate_forgetPath (comparison : Checker (Term × Term) Evidence)
    {source target : Term} (path : CheckedPath comparison source target) :
    evaluate comparison (forgetPath comparison path) = some (source, target) :=
  ((replayAlgebra comparison).fold path).2

/-- Reconstruct a conversion tree and its exact syntax-recovery receipt from
successful replay. Every branch builds the tree itself; no proof search or
classical witness selection is used. -/
def checkedPathWithRecovery (comparison : Checker (Term × Term) Evidence) :
    (recipe : Recipe Term Evidence) → (source target : Term) →
    evaluate comparison recipe = some (source, target) →
      { path : CheckedPath comparison source target // forgetPath comparison path = recipe }
  | .leaf left right evidence, source, target, accepted => by
      cases checked : comparison.check (left, right) evidence with
      | false => simp [evaluate, checked] at accepted
      | true =>
          have same : (left, right) = (source, target) := by
            simpa [evaluate, checked] using accepted
          cases same
          exact ⟨.step ⟨evidence, checked⟩, by simp⟩
  | .refl term, source, target, accepted => by
      have same : (term, term) = (source, target) := by
        simpa [evaluate] using accepted
      cases same
      exact ⟨.refl _, by simp⟩
  | .symm recipe, source, target, accepted => by
      cases computed : evaluate comparison recipe with
      | none => simp [evaluate, computed] at accepted
      | some pair =>
          obtain ⟨left, right⟩ := pair
          have same : (right, left) = (source, target) := by
            simpa [evaluate, computed, Prod.swap] using accepted
          cases same
          let inner := checkedPathWithRecovery comparison recipe target source computed
          exact ⟨.symm inner.1, by simp only [forgetPath_symm, inner.2]⟩
  | .trans first second, source, target, accepted => by
      cases computedFirst : evaluate comparison first with
      | none => simp [evaluate, computedFirst] at accepted
      | some pair =>
          obtain ⟨left, middle⟩ := pair
          cases computedSecond : evaluate comparison second with
          | none => simp [evaluate, computedFirst, computedSecond] at accepted
          | some pair =>
              obtain ⟨middle', right⟩ := pair
              by_cases sameMiddle : middle = middle'
              · subst middle'
                have same : (left, right) = (source, target) := by
                  simpa [evaluate, computedFirst, computedSecond] using accepted
                cases same
                let firstPath := checkedPathWithRecovery comparison first source middle computedFirst
                let secondPath := checkedPathWithRecovery comparison second middle target computedSecond
                exact ⟨.trans firstPath.1 secondPath.1, by
                  simp only [forgetPath_trans, firstPath.2, secondPath.2]⟩
              · simp [evaluate, computedFirst, computedSecond, sameMiddle] at accepted

/-- The retained conversion reconstructed from the submitted recipe. -/
def checkedPath (comparison : Checker (Term × Term) Evidence)
    (recipe : Recipe Term Evidence) (source target : Term)
    (accepted : evaluate comparison recipe = some (source, target)) :
    CheckedPath comparison source target :=
  (checkedPathWithRecovery comparison recipe source target accepted).1

/-- The decoder preserves the submitted evidence tree, not only its claim. -/
theorem forget_checkedPath (comparison : Checker (Term × Term) Evidence)
    (recipe : Recipe Term Evidence) (source target : Term)
    (accepted : evaluate comparison recipe = some (source, target)) :
    forgetPath comparison (checkedPath comparison recipe source target accepted) = recipe :=
  (checkedPathWithRecovery comparison recipe source target accepted).2

variable {OtherTerm : Type w} {OtherEvidence : Type x} [DecidableEq OtherTerm]

/-- Translate leaves and syntax without erasing any composition node. -/
def Recipe.map (termMap : Term → OtherTerm)
    (evidenceMap : Term → Term → Evidence → OtherEvidence) :
    Recipe Term Evidence → Recipe OtherTerm OtherEvidence
  | .leaf source target evidence => .leaf (termMap source) (termMap target)
      (evidenceMap source target evidence)
  | .refl term => .refl (termMap term)
  | .symm proof => .symm (proof.map termMap evidenceMap)
  | .trans first second => .trans (first.map termMap evidenceMap) (second.map termMap evidenceMap)

omit [DecidableEq Term] [DecidableEq OtherTerm] in
theorem Recipe.map_nodes (termMap : Term → OtherTerm)
    (evidenceMap : Term → Term → Evidence → OtherEvidence) (proof : Recipe Term Evidence) :
    (proof.map termMap evidenceMap).nodes = proof.nodes := by
  induction proof <;> simp_all [map, nodes]

omit [DecidableEq Term] [DecidableEq OtherTerm] in
theorem Recipe.map_leaves (termMap : Term → OtherTerm)
    (evidenceMap : Term → Term → Evidence → OtherEvidence) (proof : Recipe Term Evidence) :
    (proof.map termMap evidenceMap).leaves = proof.leaves := by
  induction proof <;> simp_all [map, leaves]

/-- A checked leaf translation extends to all recipes. The map need not be
injective, and this forward law supplies no reflection or cost bound. -/
theorem map_checked
    (sourceChecker : Checker (Term × Term) Evidence)
    (targetChecker : Checker (OtherTerm × OtherTerm) OtherEvidence)
    (termMap : Term → OtherTerm)
    (evidenceMap : Term → Term → Evidence → OtherEvidence)
    (preserves : ∀ source target evidence,
      sourceChecker.check (source, target) evidence = true →
      targetChecker.check (termMap source, termMap target)
        (evidenceMap source target evidence) = true)
    (proof : Recipe Term Evidence) (source target : Term)
    (accepted : evaluate sourceChecker proof = some (source, target)) :
    evaluate targetChecker (proof.map termMap evidenceMap) = some (termMap source, termMap target) := by
  induction proof generalizing source target with
  | leaf left right evidence =>
      cases checked : sourceChecker.check (left, right) evidence with
      | false => simp [evaluate, checked] at accepted
      | true =>
          have same : (left, right) = (source, target) := by simpa [evaluate, checked] using accepted
          cases same
          simp [Recipe.map, evaluate, preserves _ _ _ checked]
  | refl term =>
      have same : (term, term) = (source, target) := by simpa [evaluate] using accepted
      cases same
      rfl
  | symm proof ih =>
      cases computed : evaluate sourceChecker proof with
      | none => simp [evaluate, computed] at accepted
      | some pair =>
          obtain ⟨left, right⟩ := pair
          have same : (right, left) = (source, target) := by
            simpa [evaluate, computed, Prod.swap] using accepted
          cases same
          simp [Recipe.map, evaluate, ih _ _ computed, Prod.swap]
  | trans first second ihFirst ihSecond =>
      cases computedFirst : evaluate sourceChecker first with
      | none => simp [evaluate, computedFirst] at accepted
      | some pair =>
          obtain ⟨left, middle⟩ := pair
          cases computedSecond : evaluate sourceChecker second with
          | none => simp [evaluate, computedFirst, computedSecond] at accepted
          | some pair =>
              obtain ⟨middle', right⟩ := pair
              by_cases sameMiddle : middle = middle'
              · subst middle'
                have same : (left, right) = (source, target) := by
                  simpa [evaluate, computedFirst, computedSecond] using accepted
                cases same
                simp [Recipe.map, evaluate, ihFirst _ _ computedFirst, ihSecond _ _ computedSecond]
              · simp [evaluate, computedFirst, computedSecond, sameMiddle] at accepted

namespace Controls

/-- A finite, nontransitive comparison. It models the boundary, not Lean's
actual conversion algorithm. -/
def adjacent : Checker (Nat × Nat) Unit where
  check pair _ := decide (pair.1 ≤ pair.2 + 1 ∧ pair.2 ≤ pair.1 + 1)

def composed : Recipe Nat Unit := .trans (.leaf 0 1 ()) (.leaf 1 2 ())

example : adjacent.check (0, 1) () = true ∧ adjacent.check (1, 2) () = true := by decide
example : adjacent.check (0, 2) () = false := by decide
example : (checker adjacent).check (0, 2) composed = true := by decide
example : (checker adjacent).check (0, 2) (.trans (.leaf 0 1 ()) (.leaf 2 3 ())) = false := by decide
example : (checker adjacent).check (2, 0) (.symm composed) = true := by decide

end Controls

end Mettapedia.Logic.EqualityRecipe
