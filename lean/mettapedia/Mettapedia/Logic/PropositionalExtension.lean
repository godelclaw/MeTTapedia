import Mettapedia.Logic.PropositionalHilbertChecking
import Foundation.Propositional.ClassicalSemantics.Hilbert

/-!
# Fresh definitions in classical propositional proof checking

Extension declarations are literal hypotheses, never schematic axioms.
Freshness excludes the final claim, earlier declarations, and the new
definition's own right-hand side. Every valuation of the old vocabulary
extends to one satisfying all declarations, without changing that claim.
The native Hilbert rules therefore remain conservative.

The checker validates declarations and an explicit derivation. Semantic
conservativity is not a polynomial compiler eliminating those declarations.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.PropositionalExtension

open PropositionalHilbertChecking
open LO.Propositional

def atoms : Formula → List Nat
  | .atom name => [name]
  | .falsum => []
  | .imp left right | .and left right | .or left right => atoms left ++ atoms right

def holds (valuation : Nat → Prop) : Formula → Prop
  | .atom name => valuation name
  | .falsum => False
  | .imp left right => holds valuation left → holds valuation right
  | .and left right => holds valuation left ∧ holds valuation right
  | .or left right => holds valuation left ∨ holds valuation right

theorem holds_agree (left right : Nat → Prop) (formula : Formula)
    (agree : ∀ name ∈ atoms formula, left name ↔ right name) :
    holds left formula ↔ holds right formula := by
  induction formula with
  | atom name => exact agree name (by simp [atoms])
  | falsum => rfl
  | _ => simp_all [atoms, holds, List.mem_append]

theorem holds_iff_models (valuation : Nat → Prop) (formula : Formula) :
    holds valuation formula ↔ LO.Semantics.Models valuation formula := by
  rw [LO.Propositional.Formula.ClassicalSemantics.models_iff_val]
  induction formula <;> simp_all [holds, LO.Propositional.Formula.ClassicalSemantics.val]

structure Definition where
  name : Nat
  body : Formula
  deriving DecidableEq

def Definition.formula (definition : Definition) : Formula :=
  .and (.imp (.atom definition.name) definition.body)
    (.imp definition.body (.atom definition.name))

def declarations (definitions : List Definition) : List Formula := definitions.map Definition.formula

/-- `used` contains all old symbols whose interpretation must remain fixed.
Each subsequent definition must also avoid every preceding body. -/
def validate (used : List Nat) : List Definition → Bool
  | [] => true
  | definition :: rest =>
      decide (definition.name ∉ used ∧ definition.name ∉ atoms definition.body) &&
        validate (definition.name :: atoms definition.body ++ used) rest

inductive Admitted : List Nat → List Definition → Prop where
  | nil (used : List Nat) : Admitted used []
  | cons {used : List Nat} {definition : Definition} {rest : List Definition}
      (fresh : definition.name ∉ used) (nonrecursive : definition.name ∉ atoms definition.body)
      (tail : Admitted (definition.name :: atoms definition.body ++ used) rest) :
      Admitted used (definition :: rest)

theorem validate_exact (used : List Nat) (definitions : List Definition) :
    validate used definitions = true ↔ Admitted used definitions := by
  induction definitions generalizing used with
  | nil => exact ⟨fun _ => .nil used, fun _ => rfl⟩
  | cons definition rest ih =>
      simp only [validate, Bool.and_eq_true, decide_eq_true_eq, ih]
      constructor
      · rintro ⟨⟨fresh, nonrecursive⟩, tail⟩
        exact .cons fresh nonrecursive tail
      · intro admitted
        cases admitted with
        | cons fresh nonrecursive tail => exact ⟨⟨fresh, nonrecursive⟩, tail⟩

def extend (valuation : Nat → Prop) : List Definition → Nat → Prop
  | [] => valuation
  | definition :: rest => extend
      (Function.update valuation definition.name (holds valuation definition.body)) rest

/-- The final valuation preserves the old vocabulary and satisfies every
literal extension hypothesis. It is constructed in declaration order. -/
theorem extend_correct (definitions : List Definition) (used : List Nat)
    (valuation : Nat → Prop) (valid : validate used definitions = true) :
    (∀ name ∈ used, extend valuation definitions name ↔ valuation name) ∧
      ∀ formula ∈ declarations definitions, holds (extend valuation definitions) formula := by
  induction definitions generalizing used valuation with
  | nil => simp [extend, declarations]
  | cons definition rest ih =>
      simp only [validate, Bool.and_eq_true, decide_eq_true_eq] at valid
      obtain ⟨fresh, tailValid⟩ := valid
      let next := Function.update valuation definition.name (holds valuation definition.body)
      obtain ⟨preserved, satisfied⟩ := ih
        (definition.name :: atoms definition.body ++ used) next tailValid
      have preservedBody : holds (extend next rest) definition.body ↔ holds next definition.body :=
        holds_agree _ _ _ (fun name member => preserved name (by simp [member]))
      have unchangedBody : holds next definition.body ↔ holds valuation definition.body := by
        apply holds_agree
        intro name member
        have different : name ≠ definition.name := by
          intro same
          exact fresh.2 (same ▸ member)
        simp [next, Function.update_of_ne different]
      constructor
      · intro name member
        have different : name ≠ definition.name := by
          intro same
          exact fresh.1 (same ▸ member)
        simpa [extend, next, Function.update_of_ne different] using
          preserved name (by simp [member])
      · intro formula member
        simp only [declarations, List.map_cons, List.mem_cons] at member
        rcases member with rfl | member
        · have named := preserved definition.name (by simp)
          have same : extend next rest definition.name ↔ holds (extend next rest) definition.body :=
            named.trans ((by simp [next] : next definition.name ↔ holds valuation definition.body).trans
              (preservedBody.trans unchangedBody).symm)
          exact ⟨same.mp, same.mpr⟩
        · exact satisfied formula member

inductive ExtensionRule (hypotheses : List Formula) : List Formula → Formula → Prop where
  | core {premises conclusion} : Rule .classical premises conclusion →
      ExtensionRule hypotheses premises conclusion
  | hypothesis {formula} : formula ∈ hypotheses → ExtensionRule hypotheses [] formula

inductive ExtensionCode where
  | core (code : Code)
  | hypothesis (index : Nat)
  deriving DecidableEq

def checkRule (hypotheses : List Formula) (code : ExtensionCode)
    (premises : List Formula) (conclusion : Formula) : Bool :=
  match code with
  | .core code => PropositionalHilbertChecking.checkRule .classical code premises conclusion
  | .hypothesis index => decide (premises = [] ∧ hypotheses[index]? = some conclusion)

theorem checkRule_sound (hypotheses : List Formula) (code : ExtensionCode)
    (premises : List Formula) (conclusion : Formula)
    (accepted : checkRule hypotheses code premises conclusion = true) :
    ExtensionRule hypotheses premises conclusion := by
  cases code with
  | core code => exact .core (PropositionalHilbertChecking.checkRule_sound _ _ _ _ accepted)
  | hypothesis index =>
      have valid : premises = [] ∧ hypotheses[index]? = some conclusion := of_decide_eq_true accepted
      rcases valid with ⟨rfl, found⟩
      exact .hypothesis (List.mem_of_getElem? found)

theorem checkRule_complete (hypotheses : List Formula) (premises : List Formula) (conclusion : Formula)
    (rule : ExtensionRule hypotheses premises conclusion) :
    ∃ code, checkRule hypotheses code premises conclusion = true := by
  cases rule with
  | core rule =>
      obtain ⟨code, accepted⟩ := PropositionalHilbertChecking.checkRule_complete _ _ _ rule
      exact ⟨.core code, accepted⟩
  | hypothesis member =>
      obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
      exact ⟨.hypothesis index, by simp [checkRule, found]⟩

def interface (hypotheses : List Formula) : RuleWitness (ExtensionRule hypotheses) where
  W := ExtensionCode
  isInstance := checkRule hypotheses
  sound := checkRule_sound hypotheses
  complete := checkRule_complete hypotheses

theorem core_rule_sound (valuation : Nat → Prop) {premises : List Formula} {conclusion : Formula}
    (rule : Rule .classical premises conclusion)
    (earlier : ∀ premise ∈ premises, holds valuation premise) : holds valuation conclusion := by
  classical
  cases rule <;> simp_all [holds]
  all_goals tauto

theorem derives_sound (hypotheses : List Formula) (valuation : Nat → Prop)
    (assumed : ∀ formula ∈ hypotheses, holds valuation formula) {claim : Formula}
    (proved : Derives (ExtensionRule hypotheses) claim) : holds valuation claim := by
  apply Derives.least (holds valuation) ?_ proved
  intro premises conclusion rule earlier
  cases rule with
  | core rule => exact core_rule_sound valuation rule earlier
  | hypothesis member => exact assumed conclusion member

abbrev Proof := Derivation Formula ExtensionCode

structure Certificate where
  definitions : List Definition
  proof : Proof

def check (claim : Formula) (certificate : Certificate) : Bool :=
  validate (atoms claim) certificate.definitions &&
    decide (certificate.proof.concl = claim) &&
    certificate.proof.valid (interface (declarations certificate.definitions))

/-- The independent proof judgment fixes both declaration freshness and the
native extended Hilbert derivation, without mentioning the checker. -/
def Valid (claim : Formula) (definitions : List Definition) : Prop :=
  Admitted (atoms claim) definitions ∧
    Derives (ExtensionRule (declarations definitions)) claim

theorem check_valid (claim : Formula) (certificate : Certificate)
    (accepted : check claim certificate = true) : Valid claim certificate.definitions := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at accepted
  refine ⟨(validate_exact _ _).mp accepted.1.1, ?_⟩
  exact accepted.1.2 ▸ Derivation.valid_sound (interface _) certificate.proof accepted.2

theorem coverage (claim : Formula) (definitions : List Definition) :
    Valid claim definitions ↔
      ∃ proof, check claim ⟨definitions, proof⟩ = true := by
  constructor
  · rintro ⟨valid, derivation⟩
    obtain ⟨proof, checked, conclusion⟩ := Derives.exists_derivation (interface _) derivation
    refine ⟨proof, ?_⟩
    simp only [check, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨(validate_exact _ _).mpr valid, conclusion⟩, checked⟩
  · rintro ⟨proof, accepted⟩
    exact check_valid claim ⟨definitions, proof⟩ accepted

theorem conservative (claim : Formula) (definitions : List Definition)
    (valid : Valid claim definitions) : ∀ valuation, holds valuation claim := by
  intro valuation
  obtain ⟨preserved, satisfied⟩ := extend_correct definitions (atoms claim) valuation
    ((validate_exact _ _).mpr valid.1)
  have trueExtended := derives_sound (declarations definitions) (extend valuation definitions) satisfied valid.2
  exact (holds_agree _ _ claim preserved).mp trueExtended

/-- Every accepted extension proof is an ordinary classical theorem.
This completeness-based implication does not construct a short Frege proof. -/
theorem valid_source (claim : Formula) (definitions : List Definition)
    (valid : Valid claim definitions) : Source .classical claim := by
  have tautology : claim.Tautology := by
    intro valuation
    exact (holds_iff_models valuation claim).mp
      (conservative claim definitions valid valuation)
  exact LO.Propositional.Logic.iff_provable.mp (LO.Propositional.Cl.completeness tautology)

theorem check_sound (claim : Formula) (certificate : Certificate)
    (accepted : check claim certificate = true) : Source .classical claim :=
  valid_source claim certificate.definitions (check_valid claim certificate accepted)

structure DAGCertificate where
  definitions : List Definition
  nodes : List (DerivationGraph.Node Formula ExtensionCode Unit)
  root : Nat

def checkDAG (claim : Formula) (certificate : DAGCertificate) : Bool :=
  validate (atoms claim) certificate.definitions &&
    decide ((DerivationGraph.replay (interface (declarations certificate.definitions))
      certificate.nodes).bind (fun cache => cache[certificate.root]?) = some claim)

theorem checkDAG_valid (claim : Formula) (certificate : DAGCertificate)
    (accepted : checkDAG claim certificate = true) : Valid claim certificate.definitions := by
  have both := Bool.and_eq_true_iff.mp accepted
  refine ⟨(validate_exact _ _).mp both.1, ?_⟩
  have result := of_decide_eq_true both.2
  cases replayed : DerivationGraph.replay (interface (declarations certificate.definitions)) certificate.nodes with
  | none => simp [replayed] at result
  | some cache =>
      exact DerivationGraph.root_sound (interface _) replayed (by simpa [replayed] using result)

theorem dag_coverage (claim : Formula) (definitions : List Definition) :
    Valid claim definitions ↔ ∃ nodes root, checkDAG claim ⟨definitions, nodes, root⟩ = true := by
  constructor
  · rintro ⟨admitted, derivation⟩
    obtain ⟨nodes, cache, root, replayed, found⟩ :=
      DerivationGraph.exists_replay_of_derives (interface _) () derivation
    exact ⟨nodes, root, by simp [checkDAG, (validate_exact _ _).mpr admitted, replayed, found]⟩
  · rintro ⟨nodes, root, accepted⟩
    exact checkDAG_valid claim ⟨definitions, nodes, root⟩ accepted

def checker : Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker Formula DAGCertificate where
  check := checkDAG

theorem checkDAG_sound (claim : Formula) (certificate : DAGCertificate)
    (accepted : checkDAG claim certificate = true) : Source .classical claim :=
  valid_source claim certificate.definitions (checkDAG_valid claim certificate accepted)

theorem authority : checker.Authority (Source .classical) where
  sound := checkDAG_sound
  complete claim proved := by
    have extended := Derives.mono
      (fun _ _ rule => ExtensionRule.core (hypotheses := []) rule)
      (source_derives .classical proved)
    obtain ⟨nodes, root, accepted⟩ := (dag_coverage claim []).mp ⟨.nil _, extended⟩
    exact ⟨⟨[], nodes, root⟩, accepted⟩

/-- Frege DAGs enter the extension checker without adding definitions or
changing their formulas, reference lists, or source occurrence metadata. -/
def embedDAG (nodes : List (DerivationGraph.Node Formula Code Unit)) (root : Nat) : DAGCertificate :=
  ⟨[], nodes.map (DerivationGraph.Node.map id ExtensionCode.core id), root⟩

theorem embedDAG_exact (nodes : List (DerivationGraph.Node Formula Code Unit)) (root : Nat) (claim : Formula) :
    checkDAG claim (embedDAG nodes root) =
      decide ((DerivationGraph.replay (PropositionalHilbertChecking.interface .classical) nodes).bind
        (fun cache => cache[root]?) = some claim) := by
  simp only [checkDAG, embedDAG, validate, Bool.true_and]
  have mapped := DerivationGraph.replay_mapWitness
    (PropositionalHilbertChecking.interface .classical) (interface (declarations []))
    ExtensionCode.core (by intros; rfl) nodes
  exact congrArg (fun result : Option (Array Formula) =>
    decide ((result.bind (fun cache => cache[root]?)) = some claim)) mapped

theorem embedDAG_nodes (nodes : List (DerivationGraph.Node Formula Code Unit)) (root : Nat) :
    (embedDAG nodes root).nodes.length = nodes.length := by simp [embedDAG]

def object {Origin : Type} (definitions : List Definition)
    (store : DerivationGraph.BorrowedCursor.Store Formula ExtensionCode Origin) :=
  Mettapedia.GSLT.Distinction.ProductiveBlocks.ObservedMachine.of
    (Mettapedia.Machines.Cursor.ProofChecking.machine (interface (declarations definitions)) store)

/-! ## The cost of literal definition expansion -/

def replace (definition : Definition) (formula : Formula) : Formula :=
  formula.subst (fun name => if name = definition.name then definition.body else .atom name)

/-- Expand the last definition first, then its dependencies. The source
list remains shared; the returned formula is a literal tree. -/
def unfold (definitions : List Definition) (formula : Formula) : Formula :=
  definitions.foldr (fun definition current => replace definition current) formula

theorem unfold_append (first second : List Definition) (formula : Formula) :
    unfold (first ++ second) formula = unfold first (unfold second formula) := by
  simp [unfold, List.foldr_append]

theorem unfold_and (definitions : List Definition) (left right : Formula) :
    unfold definitions (.and left right) = .and (unfold definitions left) (unfold definitions right) := by
  induction definitions with
  | nil => rfl
  | cons definition rest ih =>
      change replace definition (unfold rest (.and left right)) =
        .and (replace definition (unfold rest left)) (replace definition (unfold rest right))
      rw [ih]
      rfl

def doubling : Nat → Formula
  | 0 => .atom 0
  | n + 1 => .and (doubling n) (doubling n)

def chainFrom (start : Nat) : Nat → List Definition
  | 0 => []
  | n + 1 => ⟨start + 1, .and (.atom start) (.atom start)⟩ :: chainFrom (start + 1) n

theorem chainFrom_append (start depth : Nat) :
    chainFrom start (depth + 1) = chainFrom start depth ++
      [⟨start + depth + 1, .and (.atom (start + depth)) (.atom (start + depth))⟩] := by
  induction depth generalizing start with
  | zero => rfl
  | succ depth ih =>
      change _ :: chainFrom (start + 1) (depth + 1) = _ ::
        (chainFrom (start + 1) depth ++ [_])
      rw [ih]
      simp only [Nat.add_left_comm, Nat.add_comm]

theorem chainFrom_admitted (start depth : Nat) (used : List Nat)
    (bounded : ∀ name ∈ used, name ≤ start) : Admitted used (chainFrom start depth) := by
  induction depth generalizing start used with
  | zero => exact .nil used
  | succ depth ih =>
      refine .cons ?_ ?_ (ih (start + 1) _ ?_)
      · change start + 1 ∉ used
        intro member
        have := bounded _ member
        omega
      · change start + 1 ∉ atoms (.and (.atom start) (.atom start))
        simp [atoms]
      · intro name member
        change name ∈ (start + 1) :: start :: start :: used at member
        simp only [List.mem_cons] at member
        rcases member with rfl | rfl | rfl | member
        all_goals first | omega | exact (bounded _ member).trans (by omega)

theorem unfold_chain_zero (start depth : Nat) (name : Nat) (old : name ≤ start) :
    unfold (chainFrom start depth) (.atom name) = .atom name := by
  induction depth generalizing start with
  | zero => rfl
  | succ depth ih =>
      have previous := ih (start + 1) (by omega)
      have different : name ≠ start + 1 := by omega
      change replace ⟨start + 1, .and (.atom start) (.atom start)⟩
        (unfold (chainFrom (start + 1) depth) (.atom name)) = .atom name
      rw [previous]
      simp [replace, different]

/-- This is an exact statement about this specific literal unfolding
algorithm, not a lower bound on all equivalent formulas or Frege proofs. -/
theorem unfold_chain (depth : Nat) :
    unfold (chainFrom 0 depth) (.atom depth) = doubling depth := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      rw [chainFrom_append, unfold_append]
      simp only [Nat.zero_add]
      change unfold (chainFrom 0 depth)
        (replace ⟨depth + 1, .and (.atom depth) (.atom depth)⟩ (.atom (depth + 1))) = _
      have replaced : replace ⟨depth + 1, .and (.atom depth) (.atom depth)⟩ (.atom (depth + 1)) =
          .and (.atom depth) (.atom depth) := by simp [replace]
      rw [replaced]
      rw [unfold_and, ih]
      rfl

def formulaNodes : Formula → Nat
  | .atom _ | .falsum => 1
  | .imp left right | .and left right | .or left right => formulaNodes left + formulaNodes right + 1

def formulaCodeSize : Formula → Nat
  | .atom name => name + 2
  | .falsum => 1
  | .imp left right | .and left right | .or left right => formulaCodeSize left + formulaCodeSize right + 1

/-- Names are charged in unary here. They are not constant-size naturals. -/
def definitionCodeSize (definition : Definition) : Nat :=
  definition.name + 2 + formulaCodeSize definition.body

theorem chain_code_bound (start depth : Nat) :
    ((chainFrom start depth).map definitionCodeSize).sum ≤ 4 * depth * (start + depth + 2) := by
  induction depth generalizing start with
  | zero => simp [chainFrom]
  | succ depth ih =>
      have bound := ih (start + 1)
      simp only [chainFrom, List.map_cons, List.sum_cons, definitionCodeSize, formulaCodeSize]
      nlinarith

theorem doubling_nodes (depth : Nat) : formulaNodes (doubling depth) + 1 = 2 ^ (depth + 1) := by
  induction depth with
  | zero => rfl
  | succ depth ih => simp only [doubling, formulaNodes, pow_succ]; omega

theorem literal_expansion_gap (depth : Nat) :
    Admitted [0] (chainFrom 0 depth) ∧
    ((chainFrom 0 depth).map definitionCodeSize).sum + formulaCodeSize (.atom depth) ≤
      5 * (depth + 1) * (depth + 2) ∧
    formulaNodes (unfold (chainFrom 0 depth) (.atom depth)) + 1 = 2 ^ (depth + 1) := by
  refine ⟨chainFrom_admitted 0 depth [0] (by simp), ?_, by rw [unfold_chain, doubling_nodes]⟩
  have bound := chain_code_bound 0 depth
  simp only [Nat.zero_add] at bound
  simp only [formulaCodeSize]
  nlinarith

namespace Controls

def oldClaim : Formula := .imp (.atom 0) (.atom 0)
def fresh : Definition := ⟨1, .atom 0⟩
def cyclic : Definition := ⟨1, .atom 1⟩

/-- Both directions of a genuine fresh definition are used to derive an old
claim. The root contains none of the newly introduced symbols. -/
def worked : DAGCertificate :=
  let a : Formula := .atom 0
  let p : Formula := .atom 1
  let forward : Formula := .imp p a
  let backward : Formula := .imp a p
  let definition := fresh.formula
  let node := fun claim code parents =>
    (⟨claim, code, parents, ()⟩ : DerivationGraph.Node Formula ExtensionCode Unit)
  ⟨[fresh], [
    node definition (.hypothesis 0) [],
    node (.imp definition forward) (.core (.andLeft forward backward)) [],
    node forward (.core (.mp definition forward)) [1, 0],
    node (.imp definition backward) (.core (.andRight forward backward)) [],
    node backward (.core (.mp definition backward)) [3, 0],
    node (.imp forward (.imp a forward)) (.core (.k forward a)) [],
    node (.imp a forward) (.core (.mp forward (.imp a forward))) [5, 2],
    node (.imp (.imp a forward) (.imp backward oldClaim)) (.core (.s a p a)) [],
    node (.imp backward oldClaim) (.core (.mp (.imp a forward) (.imp backward oldClaim))) [7, 6],
    node oldClaim (.core (.mp backward oldClaim)) [8, 4]], 9⟩

example : validate (atoms oldClaim) [fresh] = true := by decide
example : validate (atoms oldClaim) [⟨0, .falsum⟩] = false := by decide
example : validate (atoms oldClaim) [cyclic] = false := by decide
example : validate (atoms oldClaim) [⟨1, .atom 2⟩, ⟨2, .atom 0⟩] = false := by decide
example : validate (atoms oldClaim) [fresh, fresh] = false := by decide
example : checkDAG oldClaim worked = true := by decide
example : checkDAG .falsum worked = false := by decide
example : checkDAG oldClaim { worked with definitions := [] } = false := by decide

end Controls

end Mettapedia.Logic.PropositionalExtension
