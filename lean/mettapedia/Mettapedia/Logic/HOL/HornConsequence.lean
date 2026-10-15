import Mettapedia.Logic.Derivation
import Mettapedia.Logic.HOL.CanonicalTheory
import Mettapedia.Logic.HOL.Soundness
import Mettapedia.Logic.HOL.Semantics.ModelProperties
import Mettapedia.Logic.HOL.PublishedFacts

/-!
# Finitary inference as Horn consequence in higher-order logic

A rule instance with ordered premises becomes an implication chain between
propositional constants. The resulting HOL theory has exactly the original
atomic consequences. Preservation replays the premises by modus ponens;
reflection uses a standard model whose atoms denote the least rule closure.

This is a theorem about instantiated Horn theories. A finite schematic source
still needs its term encoding, quantification and substitution correspondence;
enumerating the instances here does not supply that finite presentation.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.HornConsequence

universe u

variable {Judgment : Type u}

/-- One proposition symbol per source judgment. -/
inductive Atom (Judgment : Type u) : Ty Empty → Type u where
  | judgment (value : Judgment) : Atom Judgment .prop

def encode (judgment : Judgment) : ClosedFormula (Atom Judgment) :=
  .const (.judgment judgment)

/-- Each physical premise slot becomes one implication, including duplicates. -/
def clause (premises : List Judgment) (conclusion : Judgment) :
    ClosedFormula (Atom Judgment) :=
  hypChain (premises.map encode) (encode conclusion)

/-- Ground rule instances, without adding their already-derived conclusions. -/
def theory (rules : List Judgment → Judgment → Prop) : ClosedTheorySet (Atom Judgment) :=
  {formula | ∃ premises conclusion, rules premises conclusion ∧ formula = clause premises conclusion}

theorem clause_nil (conclusion : Judgment) : clause [] conclusion = encode conclusion := rfl

theorem clause_cons (premise : Judgment) (premises : List Judgment) (conclusion : Judgment) :
    clause (premise :: premises) conclusion = .imp (encode premise) (clause premises conclusion) := rfl

theorem clause_mem {rules : List Judgment → Judgment → Prop}
    {premises : List Judgment} {conclusion : Judgment} (rule : rules premises conclusion) :
    clause premises conclusion ∈ theory rules := ⟨premises, conclusion, rule, rfl⟩

/-- Replay every ordered premise of an instantiated rule. -/
theorem eliminate_clause {background : ClosedTheorySet (Atom Judgment)} :
    ∀ {premises : List Judgment} {conclusion : Judgment},
      background.Provable (clause premises conclusion) →
      (∀ premise ∈ premises, background.Provable (encode premise)) →
      background.Provable (encode conclusion)
  | [], _, proof, _ => proof
  | premise :: _premises, _, proof, children =>
      eliminate_clause
        (ClosedTheorySet.provable_mp proof (children premise List.mem_cons_self))
        (fun other member => children other (List.mem_cons_of_mem _ member))

theorem preserves {rules : List Judgment → Judgment → Prop} {judgment : Judgment}
    (derived : Mettapedia.Logic.Derives rules judgment) :
    (theory rules).Provable (encode judgment) := by
  apply Mettapedia.Logic.Derives.least (fun value => (theory rules).Provable (encode value))
    _ derived
  intro premises conclusion rule children
  exact eliminate_clause (ClosedTheorySet.provable_of_mem (clause_mem rule)) children

/-- The least source closure supplies a concrete standard HOL interpretation. -/
def closureModel (rules : List Judgment → Judgment → Prop) :
    HenkinModel.{0, u, u + 1} Empty (Atom Judgment) :=
  HenkinModel.standard (fun empty => nomatch empty)
    (fun {type} symbol => match symbol with
      | .judgment value => ULift.up (Mettapedia.Logic.Derives rules value))

theorem models_encode_iff (rules : List Judgment → Judgment → Prop) (judgment : Judgment) :
    (closureModel rules).models (encode judgment) ↔ Mettapedia.Logic.Derives rules judgment :=
  Iff.rfl

theorem models_clause_iff (rules : List Judgment → Judgment → Prop) :
    ∀ (premises : List Judgment) (conclusion : Judgment),
      (closureModel rules).models (clause premises conclusion) ↔
        ((∀ premise ∈ premises, Mettapedia.Logic.Derives rules premise) →
          Mettapedia.Logic.Derives rules conclusion)
  | [], conclusion => by
      simp only [clause_nil, models_encode_iff, List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, true_implies]
  | premise :: premises, conclusion => by
      rw [clause_cons, HenkinModel.models_imp, models_encode_iff, models_clause_iff]
      constructor
      · intro holds children
        exact holds (children premise List.mem_cons_self)
          (fun other member => children other (List.mem_cons_of_mem _ member))
      · intro closed first rest
        apply closed
        intro other member
        rcases List.mem_cons.mp member with rfl | member
        · exact first
        · exact rest other member

theorem closureModel_models_theory (rules : List Judgment → Judgment → Prop)
    {formula : ClosedFormula (Atom Judgment)} (member : formula ∈ theory rules) :
    (closureModel rules).models formula := by
  obtain ⟨premises, conclusion, rule, rfl⟩ := member
  exact (models_clause_iff rules premises conclusion).mpr
    (Mettapedia.Logic.Derives.node premises conclusion rule)

/-- Reflection follows from HOL soundness in an independently built model. -/
theorem reflects {rules : List Judgment → Judgment → Prop} {judgment : Judgment}
    (proof : (theory rules).Provable (encode judgment)) :
    Mettapedia.Logic.Derives rules judgment := by
  obtain ⟨premises, members, derivation⟩ := proof
  have holds := Soundness.extDerivation_sound derivation
    (M := closureModel rules)
    (HenkinModel.functionsRespectEqv_of_fullDomains _
      (HenkinModel.fullDomains_standard _ _))
    (fun index => nomatch index)
    (fun formula member => closureModel_models_theory rules (members formula member))
  exact (models_encode_iff rules judgment).mp holds

theorem provable_iff {rules : List Judgment → Judgment → Prop} (judgment : Judgment) :
    (theory rules).Provable (encode judgment) ↔ Mettapedia.Logic.Derives rules judgment :=
  ⟨reflects, preserves⟩

theorem not_provable_of_not_derivable {rules : List Judgment → Judgment → Prop}
    {judgment : Judgment} (underivable : ¬ Mettapedia.Logic.Derives rules judgment) :
    ¬ (theory rules).Provable (encode judgment) :=
  fun proof => underivable (reflects proof)

namespace Controls

/-- A fact and a rule whose two equal premises remain separate slots. -/
def rules (premises : List Bool) (conclusion : Bool) : Prop :=
  (premises = [] ∧ conclusion = true) ∨
    (premises = [true, true] ∧ conclusion = true)

theorem seed_derives : Mettapedia.Logic.Derives rules true :=
  .node [] true (Or.inl ⟨rfl, rfl⟩) (fun _ impossible => nomatch impossible)

theorem repeated_premise_derives : Mettapedia.Logic.Derives rules true :=
  .node [true, true] true (Or.inr ⟨rfl, rfl⟩) (by
    intro premise member
    have same : premise = true := by simpa using member
    exact same ▸ seed_derives)

theorem positive : (theory rules).Provable (encode true) := preserves repeated_premise_derives

theorem underivable : ¬ Mettapedia.Logic.Derives rules false := by
  intro derived
  have result : (false : Bool) = true := by
    apply Mettapedia.Logic.Derives.least (fun value : Bool => value = true) _ derived
    intro premises conclusion rule _
    rcases rule with ⟨_, same⟩ | ⟨_, same⟩ <;> exact same
  contradiction

theorem negative : ¬ (theory rules).Provable (encode false) :=
  not_provable_of_not_derivable underivable

/-- Forward preservation survives an unauthorized extra atom. -/
theorem extra_behavior :
    (theory rules ∪ {encode false}).Provable (encode false) ∧
      ¬ Mettapedia.Logic.Derives rules false :=
  ⟨ClosedTheorySet.provable_of_mem (Or.inr rfl), underivable⟩

end Controls

end Mettapedia.Logic.HOL.HornConsequence
