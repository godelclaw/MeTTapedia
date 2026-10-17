import Mettapedia.Logic.Derivation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Nat.Find

/-!
# Generating and irredundant bases of finitary inference rules

An operation inventory records which names an interface exposes. A generating
basis answers a different question: can the omitted rules be derived using the
retained rules, with the original premises available as hypotheses?

This module uses the existing least rule closure. Rule generation is equivalent
to preservation of every consequence relation, including open hypotheses.
Every finite candidate basis has an inclusion-minimal generating subset.
Minimal subsets need not be unique, and a least generating subset need not
exist. These are semantic statements; they supply no effective minimizer,
certificate compiler, or execution bound.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.InferenceBasis

universe u v

variable {Operation : Type u} {Judgment : Type v}

abbrev RuleFamily (Operation : Type u) (Judgment : Type v) :=
  Operation → List Judgment → Judgment → Prop

/-- Original rules selected by a basis, with explicitly supplied hypotheses. -/
def Rules (family : RuleFamily Operation Judgment) (basis : Finset Operation)
    (context : List Judgment) (premises : List Judgment) (conclusion : Judgment) : Prop :=
  (premises = [] ∧ conclusion ∈ context) ∨
    ∃ operation ∈ basis, family operation premises conclusion

abbrev From (family : RuleFamily Operation Judgment) (basis : Finset Operation)
    (context : List Judgment) : Judgment → Prop :=
  Derives (Rules family basis context)

variable {family : RuleFamily Operation Judgment}

theorem hypothesis (basis : Finset Operation) {context : List Judgment}
    {judgment : Judgment} (member : judgment ∈ context) :
    From family basis context judgment :=
  .node [] judgment (.inl ⟨rfl, member⟩) (by simp)

theorem apply_rule {basis : Finset Operation} {context premises : List Judgment}
    {operation : Operation} {conclusion : Judgment}
    (member : operation ∈ basis) (rule : family operation premises conclusion)
    (children : ∀ premise ∈ premises, From family basis context premise) :
    From family basis context conclusion :=
  .node premises conclusion (.inr ⟨operation, member, rule⟩) children

theorem from_mono {small large : Finset Operation} (included : small ⊆ large)
    {context : List Judgment} {judgment : Judgment}
    (derived : From family small context judgment) :
    From family large context judgment := by
  apply derived.mono
  intro premises conclusion rule
  rcases rule with assumed | ⟨operation, member, ruleInstance⟩
  · exact .inl assumed
  · exact .inr ⟨operation, included member, ruleInstance⟩

/-- Substitute derivations for every open hypothesis. -/
theorem cut {basis : Finset Operation} {source target : List Judgment}
    {judgment : Judgment} (derived : From family basis source judgment)
    (arguments : ∀ premise ∈ source, From family basis target premise) :
    From family basis target judgment := by
  apply derived.least (From family basis target)
  intro premises conclusion rule children
  rcases rule with ⟨rfl, member⟩ | ⟨operation, member, ruleInstance⟩
  · exact arguments conclusion member
  · exact apply_rule member ruleInstance children

/-- Every instance of an operation has a derivation from its own premises. -/
def Implements (family : RuleFamily Operation Judgment) (basis : Finset Operation)
    (operation : Operation) : Prop :=
  ∀ premises conclusion, family operation premises conclusion →
    From family basis premises conclusion

/-- `target` can derive every rule instance exposed by `source`. -/
def Generates (family : RuleFamily Operation Judgment)
    (target source : Finset Operation) : Prop :=
  ∀ operation ∈ source, Implements family target operation

theorem generates_of_subset {source target : Finset Operation}
    (included : source ⊆ target) : Generates family target source := by
  intro operation member premises conclusion ruleInstance
  exact apply_rule (included member) ruleInstance (fun _ used => hypothesis target used)

theorem generates_refl (basis : Finset Operation) : Generates family basis basis :=
  generates_of_subset (Finset.Subset.refl basis)

/-- Derived rules preserve complete consequence relations, not only closed
theorem existence. The substitution of premises is essential here. -/
theorem Generates.consequences {source target : Finset Operation}
    (generated : Generates family target source)
    {context : List Judgment} {judgment : Judgment}
    (derived : From family source context judgment) :
    From family target context judgment := by
  apply derived.least (From family target context)
  intro premises conclusion rule children
  rcases rule with ⟨rfl, member⟩ | ⟨operation, member, ruleInstance⟩
  · exact hypothesis target member
  · exact cut (generated operation member premises conclusion ruleInstance) children

theorem generates_iff_consequences (source target : Finset Operation) :
    Generates family target source ↔
      ∀ context judgment, From family source context judgment →
        From family target context judgment := by
  constructor
  · exact fun generated _ _ derived => generated.consequences derived
  · intro transport operation member premises conclusion ruleInstance
    exact transport premises conclusion
      (apply_rule member ruleInstance (fun _ used => hypothesis source used))

theorem Generates.trans {first middle last : Finset Operation}
    (firstMiddle : Generates family middle first)
    (middleLast : Generates family last middle) : Generates family last first := by
  intro operation member premises conclusion ruleInstance
  exact middleLast.consequences (firstMiddle operation member premises conclusion ruleInstance)

theorem consequence_equivalence {first second : Finset Operation}
    (forward : Generates family second first) (backward : Generates family first second)
    (context : List Judgment) (judgment : Judgment) :
    From family first context judgment ↔ From family second context judgment :=
  ⟨forward.consequences, backward.consequences⟩

/-- A separating invariant rules out an implementation of a missing rule. -/
theorem not_implements_of_invariant {basis : Finset Operation} {operation : Operation}
    (invariant : Judgment → Prop)
    (closed : ∀ op ∈ basis, ∀ premises conclusion,
      family op premises conclusion →
        (∀ premise ∈ premises, invariant premise) → invariant conclusion)
    (premises : List Judgment) (conclusion : Judgment)
    (ruleInstance : family operation premises conclusion)
    (inputs : ∀ premise ∈ premises, invariant premise)
    (separated : ¬ invariant conclusion) : ¬ Implements family basis operation := by
  intro implementation
  apply separated
  apply (implementation premises conclusion ruleInstance).least invariant
  intro children result rule ih
  rcases rule with ⟨rfl, member⟩ | ⟨op, member, step⟩
  · exact inputs result member
  · exact closed op member children result step ih

section Finite

variable [DecidableEq Operation]

/-- No retained operation is derivable after removing it. -/
def Irredundant (family : RuleFamily Operation Judgment) (basis : Finset Operation) : Prop :=
  ∀ operation ∈ basis, ¬ Implements family (basis.erase operation) operation

/-- Inclusion-minimality concerns generating power, not the number of names
reported by an observer. -/
def MinimalGenerating (family : RuleFamily Operation Judgment)
    (available basis : Finset Operation) : Prop :=
  basis ⊆ available ∧ Generates family basis available ∧
    ∀ smaller, smaller ⊆ basis → Generates family smaller available → basis ⊆ smaller

theorem irredundant_iff_minimal (basis : Finset Operation) :
    Irredundant family basis ↔ MinimalGenerating family basis basis := by
  constructor
  · intro independent
    refine ⟨Finset.Subset.refl basis, generates_refl basis, ?_⟩
    intro smaller included generates operation member
    by_contra absent
    have subsetErase : smaller ⊆ basis.erase operation := by
      intro other used
      exact Finset.mem_erase.mpr ⟨by intro same; subst other; exact absent used,
        included used⟩
    exact independent operation member
      (generates.trans (generates_of_subset subsetErase) operation member)
  · rintro ⟨_, _, minimal⟩ operation member implementation
    have generates : Generates family (basis.erase operation) basis := by
      intro other used
      by_cases same : other = operation
      · simpa only [same] using implementation
      · exact generates_of_subset (source := {other})
          (by simpa using Finset.mem_erase.mpr ⟨same, used⟩)
          other (by simp)
    have impossible := minimal _ (Finset.erase_subset _ _) generates member
    exact (Finset.mem_erase.mp impossible).1 rfl

/-- An irredundant sufficient subset is minimal among the subsets of the
original candidate basis, even when that candidate contains derived rules. -/
theorem Irredundant.minimal_of_generates {available basis : Finset Operation}
    (independent : Irredundant family basis) (included : basis ⊆ available)
    (generated : Generates family basis available) :
    MinimalGenerating family available basis := by
  refine ⟨included, generated, ?_⟩
  intro smaller subset generatesSmaller
  apply ((irredundant_iff_minimal basis).mp independent).2.2 smaller subset
  exact (generates_of_subset included).trans generatesSmaller

end Finite

/-- Finite minimization proves existence, without a decision procedure for
rule derivability or an algorithm finding the minimal subset. -/
theorem exists_minimal_generating (available : Finset Operation) :
    ∃ basis, MinimalGenerating family available basis := by
  classical
  let property : Nat → Prop := fun n => ∃ basis : Finset Operation,
    basis ⊆ available ∧ Generates family basis available ∧ basis.card = n
  have inhabited : ∃ n, property n :=
    ⟨available.card, available, Finset.Subset.refl available, generates_refl available, rfl⟩
  obtain ⟨basis, included, generates, cardinality⟩ := Nat.find_spec inhabited
  refine ⟨basis, included, generates, ?_⟩
  intro smaller subset generatesSmaller
  have bound : basis.card ≤ smaller.card := by
    rw [cardinality]
    exact Nat.find_min' inhabited ⟨smaller, subset.trans included, generatesSmaller, rfl⟩
  exact (Finset.eq_of_subset_of_card_le subset bound).symm.subset

end Mettapedia.Logic.InferenceBasis
