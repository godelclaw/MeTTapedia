import Mettapedia.Logic.InferenceBasis

/-!
# Executable expansion of derived inference rules

A semantic generation proof says that a derivation exists. A rule compiler
also supplies executable proof templates. Template holes reference original
premises by position; filling them substitutes the already compiled child
certificates. The compiler below constructs target certificates and proves
their original replay accepts them. It does not run proof search or use
classical choice to select a derivation. The compiler interface states
functional correctness; computability and executed resource bounds require
realization of the supplied template function. The concrete controls provide
an executable instance.

This tree compiler can duplicate a child when a template uses its hole more
than once. Neither a linear output bound nor an executed polynomial clock is
claimed. Those require additional bounds and, for sharing, a graph compiler.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.InferenceBasisCompiler

universe u v w
variable {J : Type u} [DecidableEq J]
variable {sourceRules targetRules : List J → J → Prop}

/-- An explicit premise reference or an original target-rule witness. -/
def openRules (targetRules : List J → J → Prop) {n : Nat} (premises : Fin n → J)
    (children : List J) (result : J) : Prop :=
  (∃ i, children = [] ∧ result = premises i) ∨ targetRules children result

def openWitness (target : RuleWitness.{u, w} targetRules) {n : Nat}
    (premises : Fin n → J) : RuleWitness (openRules targetRules premises) where
  W := Fin n ⊕ target.W
  isInstance witness children result := match witness with
    | .inl i => decide (children = [] ∧ result = premises i)
    | .inr witness => target.isInstance witness children result
  sound witness children result accepted := by
    cases witness with
    | inl i => exact .inl ⟨i, by simpa using accepted⟩
    | inr witness => exact .inr (target.sound witness children result accepted)
  complete children result rule := by
    rcases rule with ⟨i, empty, same⟩ | targetRule
    · exact ⟨.inl i, by simp [empty, same]⟩
    · obtain ⟨witness, accepted⟩ := target.complete children result targetRule
      exact ⟨.inr witness, accepted⟩

/-- Fill a template using supplied target certificates. Malformed templates
are still finite data; preservation is proved for independently replayed ones. -/
def fill {W : Type w} {n : Nat} (arguments : Fin n → Derivation J W) :
    Derivation J (Fin n ⊕ W) → Derivation J W
  | .node _ (.inl i) _ _ => arguments i
  | .node result (.inr witness) m children =>
      .node result witness m (fun i => fill arguments (children i))

/-- Structural node count, separate from bytes and original-machine work. -/
def nodes {W : Type w} : Derivation J W → Nat
  | .node _ _ _ children => 1 + (List.ofFn fun i => nodes (children i)).sum

/-- Each occurrence of a premise hole is charged its supplied child size.
Thus repeated use of a hole is not silently treated as graph sharing. -/
def filledNodes {W : Type w} {n : Nat} (argumentSizes : Fin n → Nat) :
    Derivation J (Fin n ⊕ W) → Nat
  | .node _ (.inl i) _ _ => argumentSizes i
  | .node _ (.inr _) _ children =>
      1 + (List.ofFn fun i => filledNodes argumentSizes (children i)).sum

omit [DecidableEq J] in
theorem fill_nodes {W : Type w} {n : Nat} (arguments : Fin n → Derivation J W)
    (template : Derivation J (Fin n ⊕ W)) :
    nodes (fill arguments template) = filledNodes (fun i => nodes (arguments i)) template := by
  induction template with
  | node result witness m children ih =>
      cases witness with
      | inl i => rfl
      | inr witness =>
          simp only [fill, nodes, filledNodes]
          exact congrArg (fun f : Fin m → Nat => 1 + (List.ofFn f).sum) (funext ih)

theorem fill_concl (target : RuleWitness.{u, w} targetRules) {n : Nat}
    (premises : Fin n → J) (arguments : Fin n → Derivation J target.W)
    (conclusions : ∀ i, (arguments i).concl = premises i)
    (template : Derivation J (Fin n ⊕ target.W))
    (valid : template.valid (openWitness target premises) = true) :
    (fill arguments template).concl = template.concl := by
  cases template with
  | node result witness m children =>
      cases witness with
      | inl i =>
          have same : result = premises i := (of_decide_eq_true (Bool.and_eq_true_iff.mp valid).1).2
          exact (conclusions i).trans same.symm
      | inr witness => rfl

theorem fill_valid (target : RuleWitness.{u, w} targetRules) {n : Nat}
    (premises : Fin n → J) (arguments : Fin n → Derivation J target.W)
    (conclusions : ∀ i, (arguments i).concl = premises i)
    (accepted : ∀ i, (arguments i).valid target = true)
    (template : Derivation J (Fin n ⊕ target.W))
    (valid : template.valid (openWitness target premises) = true) :
    (fill arguments template).valid target = true := by
  induction template with
  | node result witness m children ih =>
      cases witness with
      | inl i => exact accepted i
      | inr witness =>
          have components := Bool.and_eq_true_iff.mp valid
          have childrenValid : ∀ i, (children i).valid (openWitness target premises) = true := by
            simpa only [List.all_eq_true, List.forall_mem_ofFn_iff, id] using components.2
          have same : (fun i => (fill arguments (children i)).concl) =
              (fun i => (children i).concl) :=
            funext fun i => fill_concl target premises arguments conclusions _ (childrenValid i)
          simp only [fill, Derivation.valid, Bool.and_eq_true, List.all_eq_true,
            List.forall_mem_ofFn_iff, id]
          refine ⟨?_, fun i => ih i (childrenValid i)⟩
          rw [same]
          exact components.1

/-- Local compiler data and its independently replayed target templates.
These obligations concern one source node, not the completed compiler. -/
structure Compiler (source : RuleWitness.{u, v} sourceRules)
    (target : RuleWitness.{u, w} targetRules) where
  template : ∀ n, source.W → (Fin n → J) → J → Derivation J (Fin n ⊕ target.W)
  template_valid : ∀ n witness premises result,
    source.isInstance witness (List.ofFn premises) result = true →
      (template n witness premises result).valid (openWitness target premises) = true
  template_concl : ∀ n witness premises result,
    source.isInstance witness (List.ofFn premises) result = true →
      (template n witness premises result).concl = result

namespace Compiler

variable {source : RuleWitness.{u, v} sourceRules} {target : RuleWitness.{u, w} targetRules}

def compile (compiler : Compiler source target) :
    Derivation J source.W → Derivation J target.W
  | .node result witness n children =>
      fill (fun i => compile compiler (children i))
        (compiler.template n witness (fun i => (children i).concl) result)

theorem compile_correct (compiler : Compiler source target)
    (certificate : Derivation J source.W) (accepted : certificate.valid source = true) :
    (compiler.compile certificate).valid target = true ∧
      (compiler.compile certificate).concl = certificate.concl := by
  induction certificate with
  | node result witness n children ih =>
      have components := Bool.and_eq_true_iff.mp accepted
      have childrenValid : ∀ i, (children i).valid source = true := by
        simpa only [List.all_eq_true, List.forall_mem_ofFn_iff, id] using components.2
      have compiled := fun i => ih i (childrenValid i)
      have localValid := compiler.template_valid n witness _ result components.1
      refine ⟨fill_valid target _ _ (fun i => (compiled i).2)
        (fun i => (compiled i).1) _ localValid, ?_⟩
      exact (fill_concl target _ _ (fun i => (compiled i).2) _ localValid).trans
        (compiler.template_concl n witness _ result components.1)

/-- An executable rule compiler implies semantic generation. The converse
requires computational data and does not follow from existence alone. -/
theorem consequences (compiler : Compiler source target) {judgment : J}
    (derived : Derives sourceRules judgment) : Derives targetRules judgment := by
  obtain ⟨certificate, checked, same⟩ := derived.exists_derivation source
  obtain ⟨compiled, conclusion⟩ := compiler.compile_correct certificate checked
  have result := Derivation.valid_sound target _ compiled
  simpa only [conclusion, same] using result

end Compiler

end Mettapedia.Logic.InferenceBasisCompiler
