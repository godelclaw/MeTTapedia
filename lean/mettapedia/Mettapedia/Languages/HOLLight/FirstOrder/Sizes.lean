import Mettapedia.Languages.HOLLight.FirstOrder.Completeness
import Mettapedia.Languages.MM0.Translation.DerivationWeight

/-!
# The sizes of the certificates the builders produce

Every rule of the calculus covers its formals, and none has more than seventeen
(`holCalculus_covering`). So a derivation's certificate weighs at most thirty-five times the
summed weights of its judgments (`proofWeight_erase_le`), and the bounds below are bounds on
judgments: how many each builder writes, and how heavy they are.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.FirstOrder

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.LabeledTreeOrder
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.MM0.Translation.CalculusSimulation
  (weight weights proofWeight proofWeights RuleCovers ruleCoversB ruleCoversB_iff CoveringCalculus
    judgmentWeight judgmentWeights proofWeight_erase_le substSchema substSchemas)
open Mettapedia.GSLT.LanguageDef (ValidatedCalculusLanguageDef)

/-! ## Every rule covers its formals -/

theorem holRules_eq (axioms : List Sequent) : holRules axioms = holRules [] ++ axiomRules axioms := by
  simp [holRules, axiomRules]

theorem fixedRules_covering :
    (holRules []).all (fun rule => ruleCoversB rule && decide (rule.metavariables.length ≤ 17)) = true := by
  decide +kernel

theorem holRules_covering (axioms : List Sequent) :
    ∀ rule ∈ holRules axioms, RuleCovers rule ∧ rule.metavariables.length ≤ 17 := by
  intro rule member
  rw [holRules_eq, List.mem_append] at member
  rcases member with fixed | axiomRule
  · have checked := List.all_eq_true.mp fixedRules_covering rule fixed
    simp only [Bool.and_eq_true, decide_eq_true_eq] at checked
    exact ⟨(ruleCoversB_iff rule).mp checked.1, checked.2⟩
  · simp only [axiomRules, List.mem_map] at axiomRule
    obtain ⟨⟨sequent, index⟩, -, rfl⟩ := axiomRule
    exact ⟨⟨by simp [rule], by simp [rule]⟩, by simp [rule]⟩

theorem holCalculus_covering {axioms : List Sequent} {definition : ValidatedCalculusLanguageDef}
    (calculus : definition.1 = holCalculus axioms) : CoveringCalculus definition 17 := by
  intro rule member
  rw [calculus] at member
  exact holRules_covering axioms rule member

/-- **A certificate weighs at most thirty-five times its judgments.** -/
theorem holCertificate_weight_le {axioms : List Sequent} {definition : ValidatedCalculusLanguageDef}
    (calculus : definition.1 = holCalculus axioms) {goal : Pattern} (derivation : Derivation definition goal) :
    proofWeight derivation.erase ≤ 35 * judgmentWeight derivation := by
  have bound := proofWeight_erase_le (holCalculus_covering calculus) derivation
  omega

/-! ## Counting judgments and bounding them -/

mutual
  /-- The number of judgments of a derivation. -/
  def nodeCount {definition : ValidatedCalculusLanguageDef} {goal : Pattern} : Derivation definition goal → ℕ
    | .byRule _ _ children => 1 + nodeCounts children

  def nodeCounts {definition : ValidatedCalculusLanguageDef} {premises : List Pattern} :
      DerivationList definition premises → ℕ
    | .nil => 0
    | .cons head tail => nodeCount head + nodeCounts tail
end

mutual
  /-- The weight of the heaviest judgment of a derivation. -/
  def maxJudgment {definition : ValidatedCalculusLanguageDef} {goal : Pattern} : Derivation definition goal → ℕ
    | .byRule _ _ children => max (weight goal) (maxJudgments children)

  def maxJudgments {definition : ValidatedCalculusLanguageDef} {premises : List Pattern} :
      DerivationList definition premises → ℕ
    | .nil => 0
    | .cons head tail => max (maxJudgment head) (maxJudgments tail)
end

mutual
  /-- Judgments, counted, weigh at most their number times the heaviest. -/
  theorem judgmentWeight_le {definition : ValidatedCalculusLanguageDef} :
      ∀ {goal : Pattern} (derivation : Derivation definition goal),
        judgmentWeight derivation ≤ nodeCount derivation * (maxJudgment derivation + 1)
    | goal, .byRule _ _ children => by
        have inner := judgmentWeights_le children
        rw [judgmentWeight, nodeCount, maxJudgment, Nat.add_mul, Nat.one_mul]
        have rootBound := le_max_left (weight goal) (maxJudgments children)
        have childBound : nodeCounts children * (maxJudgments children + 1) ≤
            nodeCounts children * (max (weight goal) (maxJudgments children) + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        omega

  theorem judgmentWeights_le {definition : ValidatedCalculusLanguageDef} :
      ∀ {premises : List Pattern} (derivations : DerivationList definition premises),
        judgmentWeights derivations ≤ nodeCounts derivations * (maxJudgments derivations + 1)
    | _, .nil => by simp [judgmentWeights, nodeCounts]
    | _, .cons head tail => by
        have first := judgmentWeight_le head
        have rest := judgmentWeights_le tail
        rw [judgmentWeights, nodeCounts, maxJudgments, Nat.add_mul]
        have firstBound : nodeCount head * (maxJudgment head + 1) ≤
            nodeCount head * (max (maxJudgment head) (maxJudgments tail) + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        have restBound : nodeCounts tail * (maxJudgments tail + 1) ≤
            nodeCounts tail * (max (maxJudgment head) (maxJudgments tail) + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        omega
end

/-! ## Counting and bounding through the rule firings -/

section Firing

variable {definition : ValidatedCalculusLanguageDef}

theorem nodeCount_recast {first second : Pattern} (same : first = second) (derivation : Derivation definition first) :
    nodeCount (recast same derivation) = nodeCount derivation := by
  subst same
  rfl

theorem maxJudgment_recast {first second : Pattern} (same : first = second) (derivation : Derivation definition first) :
    maxJudgment (recast same derivation) = maxJudgment derivation := by
  subst same
  rfl

theorem nodeCount_fire {r : RuleSchema} (member : r ∈ definition.1.rules) (shape : RuleShape r)
    (arguments : List Pattern) (arity : arguments.length = r.metavariables.length)
    (valid : ∀ argument ∈ arguments, Valid argument)
    (children : DerivationList definition (substSchemas (ruleValues r arguments) r.premises)) :
    nodeCount (fire member shape arguments arity valid children) = 1 + nodeCounts children := by
  rw [fire, nodeCount]

theorem maxJudgment_fire {r : RuleSchema} (member : r ∈ definition.1.rules) (shape : RuleShape r)
    (arguments : List Pattern) (arity : arguments.length = r.metavariables.length)
    (valid : ∀ argument ∈ arguments, Valid argument)
    (children : DerivationList definition (substSchemas (ruleValues r arguments) r.premises)) :
    maxJudgment (fire member shape arguments arity valid children) =
      max (weight (substSchema (ruleValues r arguments) r.conclusion)) (maxJudgments children) := by
  rw [fire, maxJudgment]

theorem nodeCount_fireAt {r : RuleSchema} (member : r ∈ definition.1.rules) (shape : RuleShape r)
    (arguments : List Pattern) (arity : arguments.length = r.metavariables.length)
    (valid : ∀ argument ∈ arguments, Valid argument) {premises : List Pattern} {conclusion : Pattern}
    (premisesEq : substSchemas (ruleValues r arguments) r.premises = premises)
    (conclusionEq : substSchema (ruleValues r arguments) r.conclusion = conclusion)
    (children : DerivationList definition premises) :
    nodeCount (fireAt member shape arguments arity valid premisesEq conclusionEq children) = 1 + nodeCounts children := by
  subst premisesEq conclusionEq
  rw [fireAt, nodeCount_recast, nodeCount_fire]

theorem maxJudgment_fireAt {r : RuleSchema} (member : r ∈ definition.1.rules) (shape : RuleShape r)
    (arguments : List Pattern) (arity : arguments.length = r.metavariables.length)
    (valid : ∀ argument ∈ arguments, Valid argument) {premises : List Pattern} {conclusion : Pattern}
    (premisesEq : substSchemas (ruleValues r arguments) r.premises = premises)
    (conclusionEq : substSchema (ruleValues r arguments) r.conclusion = conclusion)
    (children : DerivationList definition premises) :
    maxJudgment (fireAt member shape arguments arity valid premisesEq conclusionEq children) =
      max (weight conclusion) (maxJudgments children) := by
  subst premisesEq conclusionEq
  rw [fireAt, maxJudgment_recast, maxJudgment_fire]

theorem nodeCounts_nil : nodeCounts (DerivationList.nil : DerivationList definition []) = 0 := by
  rw [nodeCounts]

theorem nodeCounts_cons {premise : Pattern} {premises : List Pattern} (head : Derivation definition premise)
    (tail : DerivationList definition premises) :
    nodeCounts (DerivationList.cons head tail) = nodeCount head + nodeCounts tail := by
  rw [nodeCounts]

theorem maxJudgments_nil : maxJudgments (DerivationList.nil : DerivationList definition []) = 0 := by
  rw [maxJudgments]

theorem maxJudgments_cons {premise : Pattern} {premises : List Pattern} (head : Derivation definition premise)
    (tail : DerivationList definition premises) :
    maxJudgments (DerivationList.cons head tail) = max (maxJudgment head) (maxJudgments tail) := by
  rw [maxJudgments]

end Firing

/-! ## Weights of the patterns -/

@[simp] theorem weight_apply (name : String) (arguments : List Pattern) :
    weight (.apply name arguments) = 1 + name.length + weights arguments := by
  rw [weight]

@[simp] theorem weights_nil : weights [] = 0 := by rw [weights]

@[simp] theorem weights_cons (pattern : Pattern) (patterns : List Pattern) :
    weights (pattern :: patterns) = 1 + weight pattern + weights patterns := by
  rw [weights]

theorem weight_numeralP : ∀ count, weight (numeralP count) = 10 + 11 * count
  | 0 => rfl
  | count + 1 => by
      simp only [numeralP, succP, weight_apply, weights_cons, weights_nil, weight_numeralP count]
      rw [show "tree.succ".length = 9 from rfl]
      omega

theorem weight_nilP : weight nilP = 9 := rfl

theorem weight_consP (head tail : Pattern) : weight (consP head tail) = 12 + weight head + weight tail := by
  simp only [consP, weight_apply, weights_cons, weights_nil]
  rw [show "tree.cons".length = 9 from rfl]
  omega

theorem weight_nodeP (label children : Pattern) : weight (nodeP label children) = 12 + weight label + weight children := by
  simp only [nodeP, weight_apply, weights_cons, weights_nil]
  rw [show "tree.node".length = 9 from rfl]
  omega

theorem weight_toPattern_node (label : Nat) (children : List LabeledTree) :
    weight (LabeledTree.node label children).toPattern = 22 + 11 * label + weight (LabeledTree.toPatternList children) := by
  rw [LabeledTree.toPattern, weight_nodeP, weight_numeralP]
  omega

theorem weight_toPatternList_nil : weight (LabeledTree.toPatternList []) = 9 := by
  rw [LabeledTree.toPatternList, weight_nilP]

theorem weight_toPatternList_cons (tree : LabeledTree) (trees : List LabeledTree) :
    weight (LabeledTree.toPatternList (tree :: trees)) = 12 + weight tree.toPattern + weight (LabeledTree.toPatternList trees) := by
  rw [LabeledTree.toPatternList, weight_consP]

theorem weight_belowJudgment (first second : Pattern) :
    weight (belowJudgment first second) = 13 + weight first + weight second := by
  simp only [belowJudgment, weight_apply, weights_cons, weights_nil]
  rw [show "tree.Below".length = 10 from rfl]
  omega

theorem weight_ltJudgment (first second : Pattern) :
    weight (ltJudgment first second) = 10 + weight first + weight second := by
  simp only [ltJudgment, weight_apply, weights_cons, weights_nil]
  rw [show "tree.Lt".length = 7 from rfl]
  omega

theorem weight_ltListJudgment (first second : Pattern) :
    weight (ltListJudgment first second) = 14 + weight first + weight second := by
  simp only [ltListJudgment, weight_apply, weights_cons, weights_nil]
  rw [show "tree.LtList".length = 11 from rfl]
  omega

theorem weight_neqJ (first second : Pattern) : weight (neqJ first second) = 10 + weight first + weight second := by
  simp only [neqJ, weight_apply, weights_cons, weights_nil]
  rw [show "hol.Neq".length = 7 from rfl]
  omega

theorem weight_toPattern_pos (tree : LabeledTree) : 22 ≤ weight tree.toPattern := by
  cases tree with
  | node label children =>
      rw [weight_toPattern_node]
      omega

theorem weight_listP : ∀ items : List Pattern, weight (listP items) = 9 + (items.map fun item => 12 + weight item).sum
  | [] => by rw [listP, weight_nilP]; rfl
  | item :: rest => by
      rw [listP, weight_consP, weight_listP rest, List.map_cons, List.sum_cons]
      omega

theorem weight_listP_ge (items : List Pattern) : 9 ≤ weight (listP items) := by
  rw [weight_listP]
  omega

theorem weight_treeP (label : Nat) (children : List Pattern) :
    weight (treeP label children) = 22 + 11 * label + weight (listP children) := by
  rw [treeP, weight_nodeP, weight_numeralP]
  omega

theorem weight_le_listP {item : Pattern} : ∀ {items : List Pattern}, item ∈ items →
    weight item + 21 ≤ weight (listP items)
  | [], member => absurd member List.not_mem_nil
  | first :: rest, member => by
      rw [listP, weight_consP]
      rcases List.mem_cons.mp member with rfl | member
      · have := weight_nilP
        have : 9 ≤ weight (listP rest) := by
          cases rest with
          | nil => rw [listP, weight_nilP]
          | cons _ _ => rw [listP, weight_consP]; omega
        omega
      · have := weight_le_listP member
        omega

theorem weight_le_treeP {label : Nat} {child : Pattern} {children : List Pattern} (member : child ∈ children) :
    weight child + 43 ≤ weight (treeP label children) := by
  have := weight_le_listP member
  rw [weight_treeP]
  omega

theorem weight_wfJ (kind : String) (datum : Pattern) : weight (wfJ kind datum) = 8 + kind.length + weight datum := by
  simp only [wfJ, weight_apply, weights_cons, weights_nil, String.length_append]
  rw [show "hol.Wf".length = 6 from rfl]
  omega

theorem weight_treeP_sum (label : Nat) (children : List Pattern) :
    weight (treeP label children) = 31 + 11 * label + (children.map fun child => 12 + weight child).sum := by
  rw [weight_treeP, weight_listP]
  omega

theorem weight_groundP_node (label : Nat) (children : List LabeledTree) :
    weight (groundP (.node label children)) = 31 + 11 * label + (children.map fun child => 12 + weight (groundP child)).sum := by
  rw [groundP_node, weight_treeP_sum, List.map_map]
  rfl

theorem weight_bitP (bit : Nat) : weight (bitP bit) = 31 + 11 * bit := by
  rw [bitP, weight_treeP, show listP [] = nilP from rfl, weight_nilP]
  omega

/-! ## The order and disequality -/

/-! ## Weights of terms, types and contexts -/

theorem weight_typeMapletsP_cons (replacement key : Ty) (rest : List (Ty × Ty)) :
    weight (typeMapletsP ((replacement, key) :: rest)) =
      386 + weight (groundP (encodeTy replacement)) + weight (groundP (encodeTy key)) + weight (typeMapletsP rest) := by
  rw [show typeMapletsP ((replacement, key) :: rest) =
      consP (typeMapletP (groundP (encodeTy replacement)) (groundP (encodeTy key))) (typeMapletsP rest) from rfl,
    weight_consP, typeMapletP, weight_treeP_sum, show typeMapletLabel = 29 from rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

theorem weight_contextP_cons (type : Ty) (rest : List Ty) :
    weight (contextP (type :: rest)) = 12 + weight (groundP (encodeTy type)) + weight (contextP rest) := by
  rw [show contextP (type :: rest) = consP (groundP (encodeTy type)) (contextP rest) from rfl, weight_consP]

theorem weight_contextP_nil : weight (contextP []) = 9 := by
  rw [show contextP [] = nilP from rfl, weight_nilP]

theorem weight_le_contextP : ∀ {context : List Ty} {index : Nat} {type : Ty}, context[index]? = some type →
    weight (groundP (encodeTy type)) + 21 ≤ weight (contextP context)
  | first :: rest, 0, type, found => by
      obtain rfl : first = type := Option.some.inj found
      rw [weight_contextP_cons]
      have : 9 ≤ weight (contextP rest) := by
        cases rest with
        | nil => rw [weight_contextP_nil]
        | cons _ _ => rw [weight_contextP_cons]; omega
      omega
  | first :: rest, index + 1, type, found => by
      have := weight_le_contextP (context := rest) (index := index) (by simpa using found)
      rw [weight_contextP_cons]
      omega
  | [], _, _, found => absurd found (by simp)

theorem weight_encodeUnary : ∀ count, weight (groundP (encodeUnary count)) = 306 + 329 * count
  | 0 => by rw [encodeUnary, weight_groundP_node, show unaryZeroLabel = 25 from rfl]; simp
  | count + 1 => by
      rw [encodeUnary, weight_groundP_node]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, weight_encodeUnary count,
        show unarySuccLabel = 26 from rfl]
      omega

theorem weight_encodeTerm_const (constant : Const) (type : Ty) :
    weight (groundP (encodeTerm (.const constant type))) =
      275 + weight (groundP (encodeConst constant)) + weight (groundP (encodeTy type)) := by
  rw [encodeTerm, weight_groundP_node]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, show termConstLabel = 20 from rfl]
  omega

theorem weight_encodeTerm_free (sourceVar : SourceVar) :
    weight (groundP (encodeTerm (.free sourceVar))) =
      286 + weight (groundP (encodeName sourceVar.name)) + weight (groundP (encodeTy sourceVar.ty)) := by
  rw [encodeTerm, weight_groundP_node]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, show termFreeLabel = 21 from rfl]
  omega

theorem weight_encodeTerm_bound (index : Nat) :
    weight (groundP (encodeTerm (.bound index))) = 285 + weight (groundP (encodeUnary index)) := by
  rw [encodeTerm, weight_groundP_node]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, show termBoundLabel = 22 from rfl]
  omega

theorem weight_encodeTerm_app (function argument : DBTerm) :
    weight (groundP (encodeTerm (.app function argument))) =
      308 + weight (groundP (encodeTerm function)) + weight (groundP (encodeTerm argument)) := by
  rw [encodeTerm, weight_groundP_node]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, show termAppLabel = 23 from rfl]
  omega

theorem weight_encodeTerm_abs (domain : Ty) (body : DBTerm) :
    weight (groundP (encodeTerm (.abs domain body))) =
      319 + weight (groundP (encodeTy domain)) + weight (groundP (encodeTerm body)) := by
  rw [encodeTerm, weight_groundP_node]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, show termAbsLabel = 24 from rfl]
  omega

theorem weight_functionOp : weight (groundP (encodeTypeOp TypeOp.function)) = 3379 := by decide +kernel

theorem weight_encodeTy_function (domain codomain : Ty) :
    weight (groundP (encodeTy (Ty.function domain codomain))) =
      3621 + weight (groundP (encodeTy domain)) + weight (groundP (encodeTy codomain)) := by
  rw [Ty.function, encodeTy, weight_groundP_node]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, encodeTys, weight_groundP_node,
    weight_functionOp, show tyOpLabel = 7 from rfl, show listLabel = 5 from rfl]
  omega

/-- **An inferred type weighs at most twenty times its term, plus its context.** -/
theorem weight_inferType : ∀ (context : List Ty) (term : DBTerm) (type : Ty), term.inferType context = some type →
    weight (groundP (encodeTy type)) ≤ 20 * weight (groundP (encodeTerm term)) + weight (contextP context)
  | context, .const constant annotation, type, typed => by
      obtain rfl : annotation = type := Option.some.inj (by simpa [DBTerm.inferType] using typed)
      rw [weight_encodeTerm_const]
      omega
  | context, .free sourceVar, type, typed => by
      obtain rfl : sourceVar.ty = type := Option.some.inj (by simpa [DBTerm.inferType] using typed)
      rw [weight_encodeTerm_free]
      omega
  | context, .bound index, type, typed => by
      have found : context[index]? = some type := by simpa [DBTerm.inferType] using typed
      have := weight_le_contextP found
      omega
  | context, .app function argument, type, typed => by
      obtain ⟨domain, functionTyped, -⟩ := DBTerm.inferType_app_eq_some_iff.mp typed
      have inner := weight_inferType context function _ functionTyped
      rw [weight_encodeTy_function] at inner
      rw [weight_encodeTerm_app]
      omega
  | context, .abs domain body, type, typed => by
      obtain ⟨codomain, bodyTyped, rfl⟩ := DBTerm.inferType_abs_eq_some_iff.mp typed
      have inner := weight_inferType (domain :: context) body codomain bodyTyped
      rw [weight_contextP_cons] at inner
      rw [weight_encodeTy_function, weight_encodeTerm_abs]
      omega

theorem weight_freeVarP (sourceVar : SourceVar) :
    weight (freeVarP sourceVar) = 286 + weight (groundP (encodeName sourceVar.name)) + weight (groundP (encodeTy sourceVar.ty)) :=
  weight_encodeTerm_free sourceVar

theorem weight_bindersP_cons (binder : SourceVar) (rest : List SourceVar) :
    weight (bindersP (binder :: rest)) = 12 + weight (freeVarP binder) + weight (bindersP rest) := by
  rw [show bindersP (binder :: rest) = consP (freeVarP binder) (bindersP rest) from rfl, weight_consP]

theorem weight_bindersP_nil : weight (bindersP []) = 9 := by
  rw [show bindersP [] = nilP from rfl, weight_nilP]

theorem bindersP_length_le : ∀ binders : List SourceVar, 298 * binders.length ≤ weight (bindersP binders)
  | [] => by simp
  | binder :: rest => by
      have := bindersP_length_le rest
      rw [weight_bindersP_cons, weight_freeVarP, List.length_cons]
      omega

theorem boundIndex_lt : ∀ {needle : SourceVar} {binders : List SourceVar} {index : Nat},
    boundIndex needle binders = some index → index < binders.length
  | _, [], _, found => by simp [boundIndex] at found
  | needle, binder :: rest, index, found => by
      by_cases same : sourceVarSame needle binder = true
      · simp [boundIndex, same] at found
        subst found
        simp
      · cases restFound : boundIndex needle rest with
        | none => simp [boundIndex, same, restFound] at found
        | some position =>
            simp [boundIndex, same, restFound] at found
            subst found
            have := boundIndex_lt restFound
            simp
            omega

theorem weight_sourceVar (name : Name) (type : Ty) :
    weight (groundP (encodeSourceTerm (.var name type))) = 242 + weight (groundP (encodeName name)) + weight (groundP (encodeTy type)) := by
  rw [encodeSourceTerm, weight_groundP_node]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, show sourceVarLabel = 17 from rfl]
  omega

theorem weight_sourceConst (constant : Const) (type : Ty) :
    weight (groundP (encodeSourceTerm (.const constant type))) =
      231 + weight (groundP (encodeConst constant)) + weight (groundP (encodeTy type)) := by
  rw [encodeSourceTerm, weight_groundP_node]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, show sourceConstLabel = 16 from rfl]
  omega

theorem weight_sourceApp (function argument : SourceTerm) :
    weight (groundP (encodeSourceTerm (.app function argument))) =
      253 + weight (groundP (encodeSourceTerm function)) + weight (groundP (encodeSourceTerm argument)) := by
  rw [encodeSourceTerm, weight_groundP_node]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, show sourceAppLabel = 18 from rfl]
  omega

theorem weight_sourceAbs (name : Name) (type : Ty) (body : SourceTerm) :
    weight (groundP (encodeSourceTerm (.abs name type body))) =
      276 + weight (groundP (encodeName name)) + weight (groundP (encodeTy type)) +
        weight (groundP (encodeSourceTerm body)) := by
  rw [encodeSourceTerm, weight_groundP_node]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, show sourceAbsLabel = 19 from rfl]
  omega

/-- **The de Bruijn form weighs at most the source times its binders and itself.** -/
theorem weight_toDB : ∀ (binders : List SourceVar) (source : SourceTerm),
    weight (groundP (encodeTerm (source.toDB binders))) ≤
      (weight (bindersP binders) + 2 * weight (groundP (encodeSourceTerm source)) + 2) *
        weight (groundP (encodeSourceTerm source))
  | binders, .const constant type => by
      simp only [SourceTerm.toDB]
      rw [weight_encodeTerm_const, weight_sourceConst]
      nlinarith
  | binders, .var name type => by
      simp only [SourceTerm.toDB]
      have count := bindersP_length_le binders
      rw [weight_sourceVar]
      split
      · rename_i index found
        have small := boundIndex_lt found
        rw [weight_encodeTerm_bound, weight_encodeUnary]
        nlinarith
      · rw [weight_encodeTerm_free]
        nlinarith
  | binders, .app function argument => by
      simp only [SourceTerm.toDB]
      have first := weight_toDB binders function
      have second := weight_toDB binders argument
      rw [weight_encodeTerm_app, weight_sourceApp]
      nlinarith
  | binders, .abs name type body => by
      simp only [SourceTerm.toDB]
      have inner := weight_toDB (⟨name, type⟩ :: binders) body
      rw [weight_bindersP_cons, weight_freeVarP] at inner
      rw [weight_encodeTerm_abs, weight_sourceAbs]
      nlinarith

theorem weight_boundIndexJ (binders needle index : Pattern) :
    weight (boundIndexJ binders needle index) = 18 + weight binders + weight needle + weight index := by
  simp only [boundIndexJ, weight_apply, weights_cons, weights_nil]
  rw [show "hol.BoundIndex".length = 14 from rfl]
  omega

theorem weight_notBoundJ (binders needle : Pattern) :
    weight (notBoundJ binders needle) = 15 + weight binders + weight needle := by
  simp only [notBoundJ, weight_apply, weights_cons, weights_nil]
  rw [show "hol.NotBound".length = 12 from rfl]
  omega

theorem weight_toDBJ (binders source term : Pattern) :
    weight (toDBJ binders source term) = 12 + weight binders + weight source + weight term := by
  simp only [toDBJ, weight_apply, weights_cons, weights_nil]
  rw [show "hol.ToDB".length = 8 from rfl]
  omega

theorem weight_termsP_cons (term : DBTerm) (rest : List DBTerm) :
    weight (termsP (term :: rest)) = 12 + weight (groundP (encodeTerm term)) + weight (termsP rest) := by
  rw [show termsP (term :: rest) = consP (groundP (encodeTerm term)) (termsP rest) from rfl, weight_consP]

theorem weight_termsP_nil : weight (termsP []) = 9 := by
  rw [show termsP [] = nilP from rfl, weight_nilP]

theorem weight_encodeTerm_ge (term : DBTerm) : 275 ≤ weight (groundP (encodeTerm term)) := by
  cases term with
  | const constant type => rw [weight_encodeTerm_const]; omega
  | free sourceVar => rw [weight_encodeTerm_free]; omega
  | bound index => rw [weight_encodeTerm_bound]; omega
  | app function argument => rw [weight_encodeTerm_app]; omega
  | abs domain body => rw [weight_encodeTerm_abs]; omega

/-- **Closing a variable multiplies a term's weight by at most its depth and itself.** -/
theorem weight_closeFreeAt (needle : SourceVar) : ∀ (level : Nat) (term : DBTerm),
    weight (groundP (encodeTerm (DBTerm.closeFreeAt needle level term))) ≤
      weight (groundP (encodeTerm term)) * (2 * level + 3 + weight (groundP (encodeTerm term)))
  | level, .const constant type => by
      simp only [DBTerm.closeFreeAt]
      nlinarith [weight_encodeTerm_ge (.const constant type)]
  | level, .free sourceVar => by
      simp only [DBTerm.closeFreeAt]
      split
      · rw [weight_encodeTerm_bound, weight_encodeUnary, weight_encodeTerm_free]
        nlinarith
      · nlinarith [weight_encodeTerm_ge (.free sourceVar)]
  | level, .bound index => by
      simp only [DBTerm.closeFreeAt]
      nlinarith [weight_encodeTerm_ge (.bound index)]
  | level, .app function argument => by
      simp only [DBTerm.closeFreeAt]
      have first := weight_closeFreeAt needle level function
      have second := weight_closeFreeAt needle level argument
      rw [weight_encodeTerm_app, weight_encodeTerm_app]
      nlinarith
  | level, .abs domain body => by
      simp only [DBTerm.closeFreeAt]
      have inner := weight_closeFreeAt needle (level + 1) body
      rw [weight_encodeTerm_abs, weight_encodeTerm_abs]
      nlinarith

/-- **Instantiation multiplies a term's weight by at most the replacement's.** -/
theorem weight_instantiateAt (replacement : DBTerm) : ∀ (level : Nat) (term : DBTerm),
    weight (groundP (encodeTerm (DBTerm.instantiateAt replacement level term))) ≤
      weight (groundP (encodeTerm term)) * (weight (groundP (encodeTerm replacement)) + 1)
  | level, .const constant type => by
      simp only [DBTerm.instantiateAt]
      nlinarith
  | level, .free sourceVar => by
      simp only [DBTerm.instantiateAt]
      nlinarith
  | level, .bound index => by
      simp only [DBTerm.instantiateAt]
      split
      · nlinarith [weight_encodeTerm_ge (.bound index)]
      · nlinarith
  | level, .app function argument => by
      simp only [DBTerm.instantiateAt]
      have first := weight_instantiateAt replacement level function
      have second := weight_instantiateAt replacement level argument
      rw [weight_encodeTerm_app, weight_encodeTerm_app]
      nlinarith
  | level, .abs domain body => by
      simp only [DBTerm.instantiateAt]
      have inner := weight_instantiateAt replacement (level + 1) body
      rw [weight_encodeTerm_abs, weight_encodeTerm_abs]
      nlinarith

theorem weight_notFreeJ (needle term : Pattern) : weight (notFreeJ needle term) = 14 + weight needle + weight term := by
  simp only [notFreeJ, weight_apply, weights_cons, weights_nil]
  rw [show "hol.NotFree".length = 11 from rfl]
  omega

theorem weight_notFreeAllJ (needle terms : Pattern) :
    weight (notFreeAllJ needle terms) = 17 + weight needle + weight terms := by
  simp only [notFreeAllJ, weight_apply, weights_cons, weights_nil]
  rw [show "hol.NotFreeAll".length = 14 from rfl]
  omega

theorem weight_closeJ (needle depth term result : Pattern) :
    weight (closeJ needle depth term result) = 14 + weight needle + weight depth + weight term + weight result := by
  simp only [closeJ, weight_apply, weights_cons, weights_nil]
  rw [show "hol.Close".length = 9 from rfl]
  omega

theorem weight_instantiateJ (replacement depth term result : Pattern) :
    weight (instantiateJ replacement depth term result) =
      20 + weight replacement + weight depth + weight term + weight result := by
  simp only [instantiateJ, weight_apply, weights_cons, weights_nil]
  rw [show "hol.Instantiate".length = 15 from rfl]
  omega

theorem weight_typeOfJ (context term type : Pattern) :
    weight (typeOfJ context term type) = 14 + weight context + weight term + weight type := by
  simp only [typeOfJ, weight_apply, weights_cons, weights_nil]
  rw [show "hol.TypeOf".length = 10 from rfl]
  omega

theorem weight_nthJ (list index value : Pattern) :
    weight (nthJ list index value) = 11 + weight list + weight index + weight value := by
  simp only [nthJ, weight_apply, weights_cons, weights_nil]
  rw [show "hol.Nth".length = 7 from rfl]
  omega

/-! ## Weights of increasing tree lists -/

theorem weight_treesP_nil : weight (treesP []) = 9 := by
  rw [show treesP [] = nilP from rfl, weight_nilP]

theorem weight_treesP_cons (tree : LabeledTree) (trees : List LabeledTree) :
    weight (treesP (tree :: trees)) = 12 + weight (groundP tree) + weight (treesP trees) := by
  rw [show treesP (tree :: trees) = consP (groundP tree) (treesP trees) from rfl, weight_consP]

theorem weight_unionJ (first second result : Pattern) :
    weight (unionJ first second result) = 13 + weight first + weight second + weight result := by
  simp only [unionJ, weight_apply, weights_cons, weights_nil]
  rw [show "hol.Union".length = 9 from rfl]
  omega

theorem weight_eraseJ (term terms result : Pattern) :
    weight (eraseJ term terms result) = 13 + weight term + weight terms + weight result := by
  simp only [eraseJ, weight_apply, weights_cons, weights_nil]
  rw [show "hol.Erase".length = 9 from rfl]
  omega

theorem weight_insertJ (term terms result : Pattern) :
    weight (insertJ term terms result) = 14 + weight term + weight terms + weight result := by
  simp only [insertJ, weight_apply, weights_cons, weights_nil]
  rw [show "hol.Insert".length = 10 from rfl]
  omega

theorem weight_sortJ (terms result : Pattern) : weight (sortJ terms result) = 11 + weight terms + weight result := by
  simp only [sortJ, weight_apply, weights_cons, weights_nil]
  rw [show "hol.Sort".length = 8 from rfl]
  omega

/-- **A union weighs no more than its two sides.** -/
theorem weight_treeUnion : ∀ firsts seconds : List LabeledTree,
    weight (treesP (treeUnion firsts seconds)) + 9 ≤ weight (treesP firsts) + weight (treesP seconds)
  | [], seconds => by
      rw [treeUnion, weight_treesP_nil]
      omega
  | first :: firsts, [] => by
      rw [treeUnion, weight_treesP_nil]
  | first :: firsts, second :: seconds => by
      have firstsWeight := weight_treesP_cons first firsts
      have secondsWeight := weight_treesP_cons second seconds
      unfold treeUnion
      split_ifs with lower upper
      · have rest := weight_treeUnion firsts (second :: seconds)
        have result := weight_treesP_cons first (treeUnion firsts (second :: seconds))
        omega
      · have rest := weight_treeUnion (first :: firsts) seconds
        have result := weight_treesP_cons second (treeUnion (first :: firsts) seconds)
        omega
      · have rest := weight_treeUnion firsts seconds
        have result := weight_treesP_cons first (treeUnion firsts seconds)
        omega
termination_by firsts seconds => firsts.length + seconds.length

theorem weight_treeErase (tree : LabeledTree) : ∀ trees : List LabeledTree,
    weight (treesP (treeErase tree trees)) ≤ weight (treesP trees)
  | [] => by rw [treeErase]
  | first :: rest => by
      have restBound := weight_treeErase tree rest
      have before := weight_treesP_cons first rest
      have after := weight_treesP_cons first (treeErase tree rest)
      unfold treeErase
      split_ifs
      · omega
      · omega

theorem weight_treeInsert (tree : LabeledTree) : ∀ trees : List LabeledTree,
    weight (treesP (treeInsert tree trees)) ≤ 12 + weight (groundP tree) + weight (treesP trees)
  | [] => by
      have single := weight_treesP_cons tree []
      rw [treeInsert]
      omega
  | first :: rest => by
      have restBound := weight_treeInsert tree rest
      have before := weight_treesP_cons first rest
      have inserted := weight_treesP_cons tree (first :: rest)
      have after := weight_treesP_cons first (treeInsert tree rest)
      unfold treeInsert
      split_ifs
      · omega
      · omega
      · omega

theorem weight_le_treeInsert (tree : LabeledTree) : ∀ trees : List LabeledTree,
    weight (treesP trees) ≤ weight (treesP (treeInsert tree trees))
  | [] => by
      have single := weight_treesP_cons tree []
      rw [treeInsert]
      omega
  | first :: rest => by
      have restBound := weight_le_treeInsert tree rest
      have before := weight_treesP_cons first rest
      have inserted := weight_treesP_cons tree (first :: rest)
      have after := weight_treesP_cons first (treeInsert tree rest)
      unfold treeInsert
      split_ifs
      · omega
      · omega
      · omega

/-- **Sorting never adds weight.** -/
theorem weight_treeSort : ∀ trees : List LabeledTree, weight (treesP (treeSort trees)) ≤ weight (treesP trees)
  | [] => by rw [treeSort]
  | first :: rest => by
      have restBound := weight_treeSort rest
      have inserted := weight_treeInsert first (treeSort rest)
      have before := weight_treesP_cons first rest
      rw [treeSort]
      omega

section Calculus

variable {axioms : List Sequent} {definition : ValidatedCalculusLanguageDef}
  (calculus : definition.1 = holCalculus axioms)

include calculus in
theorem deriveBelow_count : ∀ (first second : Nat) (lower : first < second),
    nodeCount (deriveBelow calculus first second lower) = first + 1
  | 0, second + 1, _ => rfl
  | first + 1, second + 1, lower => by
      have step : nodeCount (deriveBelow calculus (first + 1) (second + 1) lower) =
          1 + (nodeCount (deriveBelow calculus first second (by omega)) + 0) := rfl
      rw [step, deriveBelow_count first second]
      omega
  | _, 0, lower => absurd lower (Nat.not_lt_zero _)

include calculus in
theorem deriveBelow_max : ∀ (first second : Nat) (lower : first < second),
    maxJudgment (deriveBelow calculus first second lower) = weight (belowJudgment (numeralP first) (numeralP second))
  | 0, second + 1, _ => by
      have step : maxJudgment (deriveBelow calculus 0 (second + 1) (by omega)) =
          max (weight (belowJudgment (numeralP 0) (numeralP (second + 1)))) 0 := rfl
      rw [step, Nat.max_zero]
  | first + 1, second + 1, lower => by
      have step : maxJudgment (deriveBelow calculus (first + 1) (second + 1) lower) =
          max (weight (belowJudgment (numeralP (first + 1)) (numeralP (second + 1))))
            (max (maxJudgment (deriveBelow calculus first second (by omega))) 0) := rfl
      rw [step, deriveBelow_max first second, Nat.max_zero]
      have inner : weight (belowJudgment (numeralP first) (numeralP second)) ≤
          weight (belowJudgment (numeralP (first + 1)) (numeralP (second + 1))) := by
        simp only [weight_belowJudgment, weight_numeralP]
        omega
      omega
  | _, 0, lower => absurd lower (Nat.not_lt_zero _)

mutual
  theorem deriveLt_count : ∀ (first second : LabeledTree) (lower : first < second),
      nodeCount (deriveLt calculus first second lower) ≤ weight first.toPattern + weight second.toPattern
    | .node label children, .node label' children', lower => by
        rw [deriveLt]
        split
        · rename_i labels
          have step : nodeCount (recast rfl (fire (r := ltLabelRule) (member_of_orderRules calculus (by simp [orderRules]))
              (orderRules_shape _ (by simp [orderRules]))
              [numeralP label, numeralP label', LabeledTree.toPatternList children,
                LabeledTree.toPatternList children'] rfl
              (by simp [valid_numeralP, valid_toPatternList])
              (.cons (deriveBelow calculus label label' labels) .nil)) :
                Derivation definition (ltJudgment (LabeledTree.node label children).toPattern
                  (LabeledTree.node label' children').toPattern)) =
              1 + (nodeCount (deriveBelow calculus label label' labels) + 0) := rfl
          rw [step, deriveBelow_count, weight_toPattern_node, weight_toPattern_node]
          omega
        · rename_i labels
          rw [nodeCount_recast]
          simp only [fire, nodeCount, nodeCounts]
          refine le_trans (Nat.add_le_add_left (Nat.add_le_add_right (deriveLtList_count children children' _) 0) 1) ?_
          rw [weight_toPattern_node, weight_toPattern_node]
          omega

  theorem deriveLtList_count : ∀ (firsts seconds : List LabeledTree) (lower : LabeledTree.ListLt firsts seconds),
      nodeCount (deriveLtList calculus firsts seconds lower) ≤
        weight (LabeledTree.toPatternList firsts) + weight (LabeledTree.toPatternList seconds)
    | [], second :: seconds, _ => by
        rw [deriveLtList]
        have step : nodeCount (deriveLtList calculus [] (second :: seconds) LabeledTree.ListLt.nil) = 1 := rfl
        rw [deriveLtList] at step
        rw [step, weight_toPatternList_nil, weight_toPatternList_cons]
        omega
    | first :: firsts, second :: seconds, lower => by
        rw [deriveLtList]
        split
        · rename_i heads
          have inner := deriveLt_count first second heads
          have step : nodeCount (recast rfl (fire (r := ltListHeadRule) (member_of_orderRules calculus (by simp [orderRules]))
              (orderRules_shape _ (by simp [orderRules]))
              [first.toPattern, second.toPattern, LabeledTree.toPatternList firsts, LabeledTree.toPatternList seconds]
              rfl (by simp [valid_toPattern, valid_toPatternList])
              (.cons (deriveLt calculus first second heads) .nil)) :
                Derivation definition (ltListJudgment (LabeledTree.toPatternList (first :: firsts))
                  (LabeledTree.toPatternList (second :: seconds)))) =
              1 + (nodeCount (deriveLt calculus first second heads) + 0) := rfl
          rw [step, weight_toPatternList_cons, weight_toPatternList_cons]
          omega
        · rename_i heads
          rw [nodeCount_recast]
          simp only [fire, nodeCount, nodeCounts]
          refine le_trans (Nat.add_le_add_left (Nat.add_le_add_right (deriveLtList_count firsts seconds _) 0) 1) ?_
          rw [weight_toPatternList_cons, weight_toPatternList_cons]
          have := weight_toPattern_pos first
          have := weight_toPattern_pos second
          omega
    | _, [], lower => absurd lower listLt_nil_right
end

/-! ## Well-formed characters -/

theorem weight_char_plane (character : Char) :
    weight (groundP (encodeUnary (character.toNat / 65536))) + 43 ≤ weight (groundP (encodeChar character)) := by
  rw [groundP_encodeChar, charP]
  exact weight_le_treeP (List.mem_cons.mpr (Or.inl rfl))

theorem weight_char_large (character : Char) : 360 ≤ weight (groundP (encodeChar character)) := by
  rw [groundP_encodeChar, charP, weight_treeP, show charLabel = 30 from rfl]
  have := weight_listP_ge (groundP (encodeUnary (character.toNat / 65536)) :: (bitsDown character.toNat 16).map bitP)
  omega

include calculus in
theorem deriveBit_count : ∀ (bit : Nat) (small : bit < 2), nodeCount (deriveBit calculus bit small) = 1
  | 0, _ => by rw [deriveBit]; erw [nodeCount_fireAt, nodeCounts_nil]
  | 1, _ => by rw [deriveBit]; erw [nodeCount_fireAt, nodeCounts_nil]
  | _ + 2, small => absurd small (by omega)

include calculus in
theorem deriveBit_max : ∀ (bit : Nat) (small : bit < 2), maxJudgment (deriveBit calculus bit small) ≤ 53
  | 0, _ => by
      rw [deriveBit]
      erw [maxJudgment_fireAt, maxJudgments_nil, Nat.max_zero, weight_wfJ, weight_bitP]
      decide
  | 1, _ => by
      rw [deriveBit]
      erw [maxJudgment_fireAt, maxJudgments_nil, Nat.max_zero, weight_wfJ, weight_bitP]
      decide
  | _ + 2, small => absurd small (by omega)

include calculus in
theorem deriveBits_count : ∀ (bits : List Nat) (binary : ∀ bit ∈ bits, bit < 2),
    nodeCounts (deriveBits calculus bits binary) = bits.length
  | [], _ => by rw [deriveBits, nodeCounts_nil]; rfl
  | bit :: rest, binary => by
      rw [deriveBits, nodeCounts_cons, deriveBit_count, deriveBits_count rest, List.length_cons]
      omega

include calculus in
theorem deriveBits_max : ∀ (bits : List Nat) (binary : ∀ bit ∈ bits, bit < 2),
    maxJudgments (deriveBits calculus bits binary) ≤ 53
  | [], _ => by rw [deriveBits, maxJudgments_nil]; omega
  | bit :: rest, binary => by
      rw [deriveBits, maxJudgments_cons]
      exact max_le (deriveBit_max calculus _ _) (deriveBits_max rest _)

include calculus in
theorem derivePlane_count (plane : Nat) (low : 1 ≤ plane) (high : plane ≤ 16) :
    nodeCount (derivePlane calculus plane low high) = 1 := by
  rw [derivePlane]
  erw [nodeCount_fireAt, nodeCounts_nil]

include calculus in
theorem derivePlane_max (plane : Nat) (low : 1 ≤ plane) (high : plane ≤ 16) :
    maxJudgment (derivePlane calculus plane low high) = weight (wfJ "Plane" (groundP (encodeUnary plane))) := by
  rw [derivePlane]
  erw [maxJudgment_fireAt, maxJudgments_nil, Nat.max_zero]

include calculus in
theorem deriveCharPlane_count (character : Char) (nonzero : character.toNat / 65536 ≠ 0) :
    nodeCount (deriveCharPlane calculus character nonzero) = 18 := by
  rw [deriveCharPlane]
  erw [nodeCount_fireAt, nodeCounts_cons, derivePlane_count, deriveBits_count, bitsDown_length]

include calculus in
theorem deriveCharPlane_max (character : Char) (nonzero : character.toNat / 65536 ≠ 0) :
    maxJudgment (deriveCharPlane calculus character nonzero) = weight (wfJ "Char" (groundP (encodeChar character))) := by
  rw [deriveCharPlane]
  erw [maxJudgment_fireAt, maxJudgments_cons, derivePlane_max]
  have bits := deriveBits_max calculus (bitsDown character.toNat 16) (bitsDown_binary _ _)
  have plane := weight_char_plane character
  have large := weight_char_large character
  simp only [weight_wfJ] at *
  rw [show "Plane".length = 5 from rfl, show "Char".length = 4 from rfl]
  omega

include calculus in
theorem deriveCharFixed_count (character : Char) (index : Nat) (bound : index < charRules.length) (others : List Nat)
    (arity : (others.map fun position => bitP (charBit character position)).length = charRules[index].metavariables.length)
    (premisesEq : substSchemas (ruleValues charRules[index] (others.map fun position => bitP (charBit character position)))
      charRules[index].premises = (others.map (charBit character)).map fun bit => wfJ "Bit" (bitP bit))
    (conclusionEq : substSchema (ruleValues charRules[index] (others.map fun position => bitP (charBit character position)))
      charRules[index].conclusion = wfJ "Char" (groundP (encodeChar character))) :
    nodeCount (deriveCharFixed calculus character index bound others arity premisesEq conclusionEq) = 1 + others.length := by
  rw [deriveCharFixed]
  erw [nodeCount_fireAt, deriveBits_count, List.length_map]

include calculus in
theorem deriveCharFixed_max (character : Char) (index : Nat) (bound : index < charRules.length) (others : List Nat)
    (arity : (others.map fun position => bitP (charBit character position)).length = charRules[index].metavariables.length)
    (premisesEq : substSchemas (ruleValues charRules[index] (others.map fun position => bitP (charBit character position)))
      charRules[index].premises = (others.map (charBit character)).map fun bit => wfJ "Bit" (bitP bit))
    (conclusionEq : substSchema (ruleValues charRules[index] (others.map fun position => bitP (charBit character position)))
      charRules[index].conclusion = wfJ "Char" (groundP (encodeChar character))) :
    maxJudgment (deriveCharFixed calculus character index bound others arity premisesEq conclusionEq) =
      weight (wfJ "Char" (groundP (encodeChar character))) := by
  rw [deriveCharFixed]
  erw [maxJudgment_fireAt]
  have bits := deriveBits_max calculus (others.map (charBit character)) (fun bit member => by
    obtain ⟨position, -, rfl⟩ := List.mem_map.mp member
    exact charBit_lt _ _)
  have large := weight_char_large character
  apply max_eq_left
  rw [weight_wfJ]
  omega

include calculus in
theorem deriveCharZero_count (character : Char) (zero : character.toNat / 65536 = 0) :
    nodeCount (deriveCharZero calculus character zero) = 16 := by
  rw [deriveCharZero]
  split_ifs <;> (try simp only []) <;> erw [deriveCharFixed_count] <;> rfl

include calculus in
theorem deriveCharZero_max (character : Char) (zero : character.toNat / 65536 = 0) :
    maxJudgment (deriveCharZero calculus character zero) = weight (wfJ "Char" (groundP (encodeChar character))) := by
  rw [deriveCharZero]
  split_ifs <;> (try simp only []) <;> erw [deriveCharFixed_max]

include calculus in
theorem deriveChar_count (character : Char) : nodeCount (deriveChar calculus character) ≤ weight (groundP (encodeChar character)) := by
  have large := weight_char_large character
  rw [deriveChar]
  split
  · rw [deriveCharZero_count]
    omega
  · rw [deriveCharPlane_count]
    omega

include calculus in
theorem deriveChar_max (character : Char) :
    maxJudgment (deriveChar calculus character) = weight (wfJ "Char" (groundP (encodeChar character))) := by
  rw [deriveChar]
  split
  · rw [deriveCharZero_max]
  · rw [deriveCharPlane_max]

/-! ## Well-formed strings and names -/

theorem weight_charsP_cons (character : Char) (rest : List Char) :
    weight (charsP (character :: rest)) = 12 + weight (groundP (encodeChar character)) + weight (charsP rest) := by
  rw [show charsP (character :: rest) = consP (groundP (encodeChar character)) (charsP rest) from rfl, weight_consP]

theorem weight_stringsP_cons (text : String) (rest : List String) :
    weight (stringsP (text :: rest)) = 12 + weight (groundP (encodeString text)) + weight (stringsP rest) := by
  rw [show stringsP (text :: rest) = consP (groundP (encodeString text)) (stringsP rest) from rfl, weight_consP]

theorem weight_namesP_cons (name : Name) (rest : List Name) :
    weight (namesP (name :: rest)) = 12 + weight (groundP (encodeName name)) + weight (namesP rest) := by
  rw [show namesP (name :: rest) = consP (groundP (encodeName name)) (namesP rest) from rfl, weight_consP]

theorem weight_encodeString (text : String) : weight (groundP (encodeString text)) = 55 + weight (charsP text.toList) := by
  rw [groundP_encodeString, weight_nodeP, weight_numeralP, show stringLabel = 3 from rfl]

theorem weight_encodeName (name : Name) :
    weight (groundP (encodeName name)) =
      176 + weight (stringsP name.namespaceComponents) + weight (groundP (encodeString name.component)) := by
  rw [groundP_encodeName, weight_treeP, weight_listP, show nameLabel = 4 from rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, listNodeP, weight_nodeP, weight_numeralP,
    show listLabel = 5 from rfl]
  omega

include calculus in
theorem deriveChars_count : ∀ characters : List Char,
    nodeCount (deriveChars calculus characters) ≤ weight (charsP characters)
  | [] => by
      rw [deriveChars]
      erw [nodeCount_fireAt, nodeCounts_nil]
      rw [show charsP [] = nilP from rfl, weight_nilP]
      omega
  | character :: rest => by
      rw [deriveChars]
      erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
      refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveChar_count calculus character)
        (Nat.add_le_add_right (deriveChars_count rest) 0)) 1) ?_
      rw [weight_charsP_cons]
      omega

include calculus in
theorem deriveChars_max : ∀ characters : List Char,
    maxJudgment (deriveChars calculus characters) = weight (wfJ "Chars" (charsP characters))
  | [] => by
      rw [deriveChars]
      erw [maxJudgment_fireAt, maxJudgments_nil, Nat.max_zero]
  | character :: rest => by
      rw [deriveChars]
      erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero,
        deriveChar_max, deriveChars_max rest]
      apply max_eq_left
      simp only [weight_wfJ, weight_charsP_cons]
      rw [show "Chars".length = 5 from rfl, show "Char".length = 4 from rfl]
      omega

include calculus in
theorem deriveString_count (text : String) :
    nodeCount (deriveString calculus text) ≤ weight (groundP (encodeString text)) := by
  rw [deriveString]
  erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_nil]
  refine le_trans (Nat.add_le_add_left (Nat.add_le_add_right (deriveChars_count calculus text.toList) 0) 1) ?_
  rw [weight_encodeString]
  omega

include calculus in
theorem deriveString_max (text : String) :
    maxJudgment (deriveString calculus text) = weight (wfJ "String" (groundP (encodeString text))) := by
  rw [deriveString]
  erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_nil, Nat.max_zero, deriveChars_max]
  apply max_eq_left
  simp only [weight_wfJ, weight_encodeString]
  rw [show "Chars".length = 5 from rfl, show "String".length = 6 from rfl]
  omega

include calculus in
theorem deriveStrings_count : ∀ texts : List String,
    nodeCount (deriveStrings calculus texts) ≤ weight (stringsP texts)
  | [] => by
      rw [deriveStrings]
      erw [nodeCount_fireAt, nodeCounts_nil]
      rw [show stringsP [] = nilP from rfl, weight_nilP]
      omega
  | text :: rest => by
      rw [deriveStrings]
      erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
      refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveString_count calculus text)
        (Nat.add_le_add_right (deriveStrings_count rest) 0)) 1) ?_
      rw [weight_stringsP_cons]
      omega

include calculus in
theorem deriveStrings_max : ∀ texts : List String,
    maxJudgment (deriveStrings calculus texts) = weight (wfJ "Strings" (stringsP texts))
  | [] => by
      rw [deriveStrings]
      erw [maxJudgment_fireAt, maxJudgments_nil, Nat.max_zero]
  | text :: rest => by
      rw [deriveStrings]
      erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero,
        deriveString_max, deriveStrings_max rest]
      apply max_eq_left
      simp only [weight_wfJ, weight_stringsP_cons]
      rw [show "Strings".length = 7 from rfl, show "String".length = 6 from rfl]
      omega

include calculus in
theorem deriveName_count (name : Name) : nodeCount (deriveName calculus name) ≤ weight (groundP (encodeName name)) := by
  rw [deriveName]
  erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
  refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveStrings_count calculus name.namespaceComponents)
    (Nat.add_le_add_right (deriveString_count calculus name.component) 0)) 1) ?_
  rw [weight_encodeName]
  omega

include calculus in
theorem deriveName_max (name : Name) :
    maxJudgment (deriveName calculus name) = weight (wfJ "Name" (groundP (encodeName name))) := by
  rw [deriveName]
  erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero,
    deriveStrings_max, deriveString_max]
  apply max_eq_left
  simp only [weight_wfJ, weight_encodeName]
  rw [show "Strings".length = 7 from rfl, show "String".length = 6 from rfl, show "Name".length = 4 from rfl]
  omega

include calculus in
theorem deriveNames_count : ∀ names : List Name, nodeCount (deriveNames calculus names) ≤ weight (namesP names)
  | [] => by
      rw [deriveNames]
      erw [nodeCount_fireAt, nodeCounts_nil]
      rw [show namesP [] = nilP from rfl, weight_nilP]
      omega
  | name :: rest => by
      rw [deriveNames]
      erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
      refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveName_count calculus name)
        (Nat.add_le_add_right (deriveNames_count rest) 0)) 1) ?_
      rw [weight_namesP_cons]
      omega

include calculus in
theorem deriveNames_max : ∀ names : List Name,
    maxJudgment (deriveNames calculus names) = weight (wfJ "Names" (namesP names))
  | [] => by
      rw [deriveNames]
      erw [maxJudgment_fireAt, maxJudgments_nil, Nat.max_zero]
  | name :: rest => by
      rw [deriveNames]
      erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero,
        deriveName_max, deriveNames_max rest]
      apply max_eq_left
      simp only [weight_wfJ, weight_namesP_cons]
      rw [show "Names".length = 5 from rfl, show "Name".length = 4 from rfl]
      omega

/-! ## Well-formed syntax -/

theorem weight_tysP_cons (type : Ty) (rest : List Ty) :
    weight (tysP (type :: rest)) = 12 + weight (groundP (encodeTy type)) + weight (tysP rest) := by
  rw [show tysP (type :: rest) = consP (groundP (encodeTy type)) (tysP rest) from rfl, weight_consP]

theorem weight_listNode_tys (types : List Ty) :
    weight (groundP (.node listLabel (encodeTys types))) = 77 + weight (tysP types) := by
  rw [groundP_node, weight_treeP, show listLabel = 5 from rfl]
  rfl

theorem weight_listNode_names (names : List Name) :
    weight (groundP (.node listLabel (names.map encodeName))) = 77 + weight (namesP names) := by
  rw [groundP_node, weight_treeP, show listLabel = 5 from rfl, List.map_map]
  rfl

include calculus in
theorem fireSyntax_count (index : Nat) (bound : index < syntaxRules.length) (arguments : List Pattern)
    (arity : arguments.length = syntaxRules[index].metavariables.length)
    (valid : ∀ argument ∈ arguments, Valid argument) {premises : List Pattern} {conclusion : Pattern}
    (premisesEq : substSchemas (ruleValues syntaxRules[index] arguments) syntaxRules[index].premises = premises)
    (conclusionEq : substSchema (ruleValues syntaxRules[index] arguments) syntaxRules[index].conclusion = conclusion)
    (children : DerivationList definition premises) :
    nodeCount (fireSyntax calculus index bound arguments arity valid premisesEq conclusionEq children) =
      1 + nodeCounts children := by
  rw [fireSyntax, nodeCount_fireAt]

include calculus in
theorem fireSyntax_max (index : Nat) (bound : index < syntaxRules.length) (arguments : List Pattern)
    (arity : arguments.length = syntaxRules[index].metavariables.length)
    (valid : ∀ argument ∈ arguments, Valid argument) {premises : List Pattern} {conclusion : Pattern}
    (premisesEq : substSchemas (ruleValues syntaxRules[index] arguments) syntaxRules[index].premises = premises)
    (conclusionEq : substSchema (ruleValues syntaxRules[index] arguments) syntaxRules[index].conclusion = conclusion)
    (children : DerivationList definition premises) :
    maxJudgment (fireSyntax calculus index bound arguments arity valid premisesEq conclusionEq children) =
      max (weight conclusion) (maxJudgments children) := by
  rw [fireSyntax, maxJudgment_fireAt]

mutual
  theorem deriveTy_count : ∀ type : Ty, nodeCount (deriveTy calculus type) ≤ weight (groundP (encodeTy type))
    | .var name => by
        rw [deriveTy]
        erw [fireSyntax_count, nodeCounts_cons, nodeCounts_nil]
        refine le_trans (Nat.add_le_add_left (Nat.add_le_add_right (deriveName_count calculus name) 0) 1) ?_
        rw [encodeTy, weight_groundP_node]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        omega
    | .op operator arguments => by
        rw [deriveTy]
        erw [fireSyntax_count, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
        refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveTypeOp_count operator)
          (Nat.add_le_add_right (deriveTys_count arguments) 0)) 1) ?_
        rw [encodeTy, weight_groundP_node]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, weight_listNode_tys]
        omega

  theorem deriveTys_count : ∀ types : List Ty, nodeCount (deriveTys calculus types) ≤ weight (tysP types)
    | [] => by
        rw [deriveTys]
        erw [fireSyntax_count, nodeCounts_nil]
        rw [show tysP [] = nilP from rfl, weight_nilP]
        omega
    | type :: rest => by
        rw [deriveTys]
        erw [fireSyntax_count, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
        refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveTy_count type)
          (Nat.add_le_add_right (deriveTys_count rest) 0)) 1) ?_
        rw [weight_tysP_cons]
        omega

  theorem deriveTypeOp_count : ∀ operator : TypeOp,
      nodeCount (deriveTypeOp calculus operator) ≤ weight (groundP (encodeTypeOp operator))
    | .mk name provenance => by
        rw [deriveTypeOp]
        erw [fireSyntax_count, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
        refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveName_count calculus name)
          (Nat.add_le_add_right (deriveTypeOpProvenance_count provenance) 0)) 1) ?_
        rw [encodeTypeOp, weight_groundP_node]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        omega

  theorem deriveTypeOpProvenance_count : ∀ provenance : TypeOpProvenance,
      nodeCount (deriveTypeOpProvenance calculus provenance) ≤ weight (groundP (encodeTypeOpProvenance provenance))
    | .undefined => by
        rw [deriveTypeOpProvenance]
        erw [fireSyntax_count, nodeCounts_nil]
        rw [encodeTypeOpProvenance, weight_groundP_node]
        simp only [List.map_nil, List.sum_nil]
        omega
    | .defined predicate parameters => by
        rw [deriveTypeOpProvenance]
        erw [fireSyntax_count, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
        refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveSource_count predicate)
          (Nat.add_le_add_right (deriveNames_count calculus parameters) 0)) 1) ?_
        rw [encodeTypeOpProvenance, weight_groundP_node]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, weight_listNode_names]
        omega

  theorem deriveConst_count : ∀ constant : Const,
      nodeCount (deriveConst calculus constant) ≤ weight (groundP (encodeConst constant))
    | .mk name provenance => by
        rw [deriveConst]
        erw [fireSyntax_count, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
        refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveName_count calculus name)
          (Nat.add_le_add_right (deriveConstProvenance_count provenance) 0)) 1) ?_
        rw [encodeConst, weight_groundP_node]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        omega

  theorem deriveConstProvenance_count : ∀ provenance : ConstProvenance,
      nodeCount (deriveConstProvenance calculus provenance) ≤ weight (groundP (encodeConstProvenance provenance))
    | .undefined => by
        rw [deriveConstProvenance]
        erw [fireSyntax_count, nodeCounts_nil]
        rw [encodeConstProvenance, weight_groundP_node]
        simp only [List.map_nil, List.sum_nil]
        omega
    | .defined definition' => by
        rw [deriveConstProvenance]
        erw [fireSyntax_count, nodeCounts_cons, nodeCounts_nil]
        refine le_trans (Nat.add_le_add_left (Nat.add_le_add_right (deriveSource_count definition') 0) 1) ?_
        rw [encodeConstProvenance, weight_groundP_node]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        omega
    | .abstraction operator => by
        rw [deriveConstProvenance]
        erw [fireSyntax_count, nodeCounts_cons, nodeCounts_nil]
        refine le_trans (Nat.add_le_add_left (Nat.add_le_add_right (deriveTypeOp_count operator) 0) 1) ?_
        rw [encodeConstProvenance, weight_groundP_node]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        omega
    | .representation operator => by
        rw [deriveConstProvenance]
        erw [fireSyntax_count, nodeCounts_cons, nodeCounts_nil]
        refine le_trans (Nat.add_le_add_left (Nat.add_le_add_right (deriveTypeOp_count operator) 0) 1) ?_
        rw [encodeConstProvenance, weight_groundP_node]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        omega

  theorem deriveSource_count : ∀ source : SourceTerm,
      nodeCount (deriveSource calculus source) ≤ weight (groundP (encodeSourceTerm source))
    | .const constant type => by
        rw [deriveSource]
        erw [fireSyntax_count, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
        refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveConst_count constant)
          (Nat.add_le_add_right (deriveTy_count type) 0)) 1) ?_
        rw [encodeSourceTerm, weight_groundP_node]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        omega
    | .var name type => by
        rw [deriveSource]
        erw [fireSyntax_count, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
        refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveName_count calculus name)
          (Nat.add_le_add_right (deriveTy_count type) 0)) 1) ?_
        rw [encodeSourceTerm, weight_groundP_node]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        omega
    | .app function argument => by
        rw [deriveSource]
        erw [fireSyntax_count, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
        refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveSource_count function)
          (Nat.add_le_add_right (deriveSource_count argument) 0)) 1) ?_
        rw [encodeSourceTerm, weight_groundP_node]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        omega
    | .abs name type body => by
        rw [deriveSource]
        erw [fireSyntax_count, nodeCounts_cons, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
        refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveName_count calculus name)
          (Nat.add_le_add (deriveTy_count type) (Nat.add_le_add_right (deriveSource_count body) 0))) 1) ?_
        rw [encodeSourceTerm, weight_groundP_node]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        omega
end

mutual
  theorem deriveTy_max : ∀ type : Ty,
      maxJudgment (deriveTy calculus type) = weight (wfJ "Ty" (groundP (encodeTy type)))
    | .var name => by
        rw [deriveTy]
        erw [fireSyntax_max, maxJudgments_cons, maxJudgments_nil, Nat.max_zero, deriveName_max]
        apply max_eq_left
        rw [encodeTy, weight_wfJ, weight_wfJ, weight_groundP_node]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        rw [show "Ty".length = 2 from rfl, show "Name".length = 4 from rfl]
        omega
    | .op operator arguments => by
        rw [deriveTy]
        erw [fireSyntax_max, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero,
          deriveTypeOp_max operator, deriveTys_max arguments]
        apply max_eq_left
        rw [encodeTy, weight_wfJ, weight_wfJ, weight_wfJ, weight_groundP_node]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, weight_listNode_tys]
        rw [show "Ty".length = 2 from rfl, show "TypeOp".length = 6 from rfl, show "Tys".length = 3 from rfl]
        omega

  theorem deriveTys_max : ∀ types : List Ty,
      maxJudgment (deriveTys calculus types) = weight (wfJ "Tys" (tysP types))
    | [] => by
        rw [deriveTys]
        erw [fireSyntax_max, maxJudgments_nil, Nat.max_zero]
    | type :: rest => by
        rw [deriveTys]
        erw [fireSyntax_max, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero,
          deriveTy_max type, deriveTys_max rest]
        apply max_eq_left
        rw [weight_wfJ, weight_wfJ, weight_wfJ, weight_tysP_cons]
        rw [show "Ty".length = 2 from rfl, show "Tys".length = 3 from rfl]
        omega

  theorem deriveTypeOp_max : ∀ operator : TypeOp,
      maxJudgment (deriveTypeOp calculus operator) = weight (wfJ "TypeOp" (groundP (encodeTypeOp operator)))
    | .mk name provenance => by
        rw [deriveTypeOp]
        erw [fireSyntax_max, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero,
          deriveName_max, deriveTypeOpProvenance_max provenance]
        apply max_eq_left
        rw [encodeTypeOp, weight_wfJ, weight_wfJ, weight_wfJ, weight_groundP_node]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        rw [show "TypeOp".length = 6 from rfl, show "Name".length = 4 from rfl,
          show "TypeOpProv".length = 10 from rfl]
        omega

  theorem deriveTypeOpProvenance_max : ∀ provenance : TypeOpProvenance,
      maxJudgment (deriveTypeOpProvenance calculus provenance) =
        weight (wfJ "TypeOpProv" (groundP (encodeTypeOpProvenance provenance)))
    | .undefined => by
        rw [deriveTypeOpProvenance]
        erw [fireSyntax_max, maxJudgments_nil, Nat.max_zero]
    | .defined predicate parameters => by
        rw [deriveTypeOpProvenance]
        erw [fireSyntax_max, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero,
          deriveSource_max predicate, deriveNames_max]
        apply max_eq_left
        rw [encodeTypeOpProvenance, weight_wfJ, weight_wfJ, weight_wfJ, weight_groundP_node]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, weight_listNode_names]
        rw [show "TypeOpProv".length = 10 from rfl, show "Source".length = 6 from rfl,
          show "Names".length = 5 from rfl]
        omega

  theorem deriveConst_max : ∀ constant : Const,
      maxJudgment (deriveConst calculus constant) = weight (wfJ "Const" (groundP (encodeConst constant)))
    | .mk name provenance => by
        rw [deriveConst]
        erw [fireSyntax_max, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero,
          deriveName_max, deriveConstProvenance_max provenance]
        apply max_eq_left
        rw [encodeConst, weight_wfJ, weight_wfJ, weight_wfJ, weight_groundP_node]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        rw [show "Const".length = 5 from rfl, show "Name".length = 4 from rfl,
          show "ConstProv".length = 9 from rfl]
        omega

  theorem deriveConstProvenance_max : ∀ provenance : ConstProvenance,
      maxJudgment (deriveConstProvenance calculus provenance) =
        weight (wfJ "ConstProv" (groundP (encodeConstProvenance provenance)))
    | .undefined => by
        rw [deriveConstProvenance]
        erw [fireSyntax_max, maxJudgments_nil, Nat.max_zero]
    | .defined definition' => by
        rw [deriveConstProvenance]
        erw [fireSyntax_max, maxJudgments_cons, maxJudgments_nil, Nat.max_zero, deriveSource_max definition']
        apply max_eq_left
        rw [encodeConstProvenance, weight_wfJ, weight_wfJ, weight_groundP_node]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        rw [show "ConstProv".length = 9 from rfl, show "Source".length = 6 from rfl]
        omega
    | .abstraction operator => by
        rw [deriveConstProvenance]
        erw [fireSyntax_max, maxJudgments_cons, maxJudgments_nil, Nat.max_zero, deriveTypeOp_max operator]
        apply max_eq_left
        rw [encodeConstProvenance, weight_wfJ, weight_wfJ, weight_groundP_node]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        rw [show "ConstProv".length = 9 from rfl, show "TypeOp".length = 6 from rfl]
        omega
    | .representation operator => by
        rw [deriveConstProvenance]
        erw [fireSyntax_max, maxJudgments_cons, maxJudgments_nil, Nat.max_zero, deriveTypeOp_max operator]
        apply max_eq_left
        rw [encodeConstProvenance, weight_wfJ, weight_wfJ, weight_groundP_node]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        rw [show "ConstProv".length = 9 from rfl, show "TypeOp".length = 6 from rfl]
        omega

  theorem deriveSource_max : ∀ source : SourceTerm,
      maxJudgment (deriveSource calculus source) = weight (wfJ "Source" (groundP (encodeSourceTerm source)))
    | .const constant type => by
        rw [deriveSource]
        erw [fireSyntax_max, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero,
          deriveConst_max constant, deriveTy_max type]
        apply max_eq_left
        rw [encodeSourceTerm, weight_wfJ, weight_wfJ, weight_wfJ, weight_groundP_node]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        rw [show "Source".length = 6 from rfl, show "Const".length = 5 from rfl, show "Ty".length = 2 from rfl]
        omega
    | .var name type => by
        rw [deriveSource]
        erw [fireSyntax_max, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero,
          deriveName_max, deriveTy_max type]
        apply max_eq_left
        rw [encodeSourceTerm, weight_wfJ, weight_wfJ, weight_wfJ, weight_groundP_node]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        rw [show "Source".length = 6 from rfl, show "Name".length = 4 from rfl, show "Ty".length = 2 from rfl]
        omega
    | .app function argument => by
        rw [deriveSource]
        erw [fireSyntax_max, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero,
          deriveSource_max function, deriveSource_max argument]
        apply max_eq_left
        rw [encodeSourceTerm, weight_wfJ, weight_wfJ, weight_wfJ, weight_groundP_node]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        omega
    | .abs name type body => by
        rw [deriveSource]
        erw [fireSyntax_max, maxJudgments_cons, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero,
          deriveName_max, deriveTy_max type, deriveSource_max body]
        apply max_eq_left
        rw [encodeSourceTerm, weight_wfJ, weight_wfJ, weight_wfJ, weight_wfJ, weight_groundP_node]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        rw [show "Source".length = 6 from rfl, show "Name".length = 4 from rfl, show "Ty".length = 2 from rfl]
        omega
end

/-! ## The order, disequality and type maplets: the heaviest judgments -/

mutual
  theorem deriveLt_max : ∀ (first second : LabeledTree) (lower : first < second),
      maxJudgment (deriveLt calculus first second lower) ≤ weight (ltJudgment first.toPattern second.toPattern)
    | .node label children, .node label' children', lower => by
        rw [deriveLt]
        split
        · rename_i labels
          have step : maxJudgment (recast rfl (fire (r := ltLabelRule) (member_of_orderRules calculus (by simp [orderRules]))
              (orderRules_shape _ (by simp [orderRules]))
              [numeralP label, numeralP label', LabeledTree.toPatternList children,
                LabeledTree.toPatternList children'] rfl
              (by simp [valid_numeralP, valid_toPatternList])
              (.cons (deriveBelow calculus label label' labels) .nil)) :
                Derivation definition (ltJudgment (LabeledTree.node label children).toPattern
                  (LabeledTree.node label' children').toPattern)) =
              max (weight (ltJudgment (LabeledTree.node label children).toPattern
                (LabeledTree.node label' children').toPattern))
                (max (maxJudgment (deriveBelow calculus label label' labels)) 0) := rfl
          rw [step, deriveBelow_max, Nat.max_zero]
          apply max_le (le_refl _)
          rw [weight_belowJudgment, weight_ltJudgment, weight_numeralP, weight_numeralP, weight_toPattern_node,
            weight_toPattern_node]
          omega
        · rename_i labels
          rw [maxJudgment_recast]
          simp only [fire, maxJudgment, maxJudgments]
          apply max_le
          · have same := ((treeLt_node_inv lower).resolve_left labels).1
            subst same
            exact le_refl _
          · refine max_le (le_trans (deriveLtList_max children children' _) ?_) (Nat.zero_le _)
            rw [weight_ltListJudgment, weight_ltJudgment, weight_toPattern_node, weight_toPattern_node]
            omega

  theorem deriveLtList_max : ∀ (firsts seconds : List LabeledTree) (lower : LabeledTree.ListLt firsts seconds),
      maxJudgment (deriveLtList calculus firsts seconds lower) ≤
        weight (ltListJudgment (LabeledTree.toPatternList firsts) (LabeledTree.toPatternList seconds))
    | [], second :: seconds, _ => by
        have step : maxJudgment (deriveLtList calculus [] (second :: seconds) LabeledTree.ListLt.nil) =
            max (weight (ltListJudgment (LabeledTree.toPatternList []) (LabeledTree.toPatternList (second :: seconds))))
              0 := rfl
        rw [step, Nat.max_zero]
    | first :: firsts, second :: seconds, lower => by
        rw [deriveLtList]
        split
        · rename_i heads
          have step : maxJudgment (recast rfl (fire (r := ltListHeadRule) (member_of_orderRules calculus (by simp [orderRules]))
              (orderRules_shape _ (by simp [orderRules]))
              [first.toPattern, second.toPattern, LabeledTree.toPatternList firsts, LabeledTree.toPatternList seconds]
              rfl (by simp [valid_toPattern, valid_toPatternList])
              (.cons (deriveLt calculus first second heads) .nil)) :
                Derivation definition (ltListJudgment (LabeledTree.toPatternList (first :: firsts))
                  (LabeledTree.toPatternList (second :: seconds)))) =
              max (weight (ltListJudgment (LabeledTree.toPatternList (first :: firsts))
                (LabeledTree.toPatternList (second :: seconds))))
                (max (maxJudgment (deriveLt calculus first second heads)) 0) := rfl
          rw [step, Nat.max_zero]
          refine max_le (le_refl _) (le_trans (deriveLt_max first second heads) ?_)
          rw [weight_ltJudgment, weight_ltListJudgment, weight_toPatternList_cons, weight_toPatternList_cons]
          omega
        · rename_i heads
          rw [maxJudgment_recast]
          simp only [fire, maxJudgment, maxJudgments]
          apply max_le
          · have same := ((listLt_cons_inv lower).resolve_left heads).1
            subst same
            exact le_refl _
          · refine max_le (le_trans (deriveLtList_max firsts seconds _) ?_) (Nat.zero_le _)
            rw [weight_ltListJudgment, weight_ltListJudgment, weight_toPatternList_cons, weight_toPatternList_cons]
            omega
    | _, [], lower => absurd lower listLt_nil_right
end

theorem deriveNeq_count (first second : LabeledTree) (different : first ≠ second) :
    nodeCount (deriveNeq calculus first second different) ≤ 1 + weight first.toPattern + weight second.toPattern := by
  rw [deriveNeq]
  split
  · erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_nil]
    refine le_trans (Nat.add_le_add_left (Nat.add_le_add_right (deriveLt_count calculus first second _) 0) 1) ?_
    omega
  · erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_nil]
    refine le_trans (Nat.add_le_add_left (Nat.add_le_add_right (deriveLt_count calculus second first _) 0) 1) ?_
    omega

theorem deriveNeq_max (first second : LabeledTree) (different : first ≠ second) :
    maxJudgment (deriveNeq calculus first second different) = weight (neqJ first.toPattern second.toPattern) := by
  rw [deriveNeq]
  split
  · erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_nil, Nat.max_zero]
    apply max_eq_left
    refine le_trans (deriveLt_max calculus first second _) ?_
    rw [weight_ltJudgment, weight_neqJ]
  · erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_nil, Nat.max_zero]
    apply max_eq_left
    refine le_trans (deriveLt_max calculus second first _) ?_
    rw [weight_ltJudgment, weight_neqJ]
    omega

/-! ## Type maplets, context lookup and type inference -/

theorem deriveTypeMaplets_count : ∀ entries : List (Ty × Ty),
    nodeCount (deriveTypeMaplets calculus entries) ≤ weight (typeMapletsP entries)
  | [] => by
      rw [deriveTypeMaplets]
      erw [fireSyntax_count, nodeCounts_nil]
      rw [show typeMapletsP [] = nilP from rfl, weight_nilP]
      omega
  | (replacement, key) :: rest => by
      rw [deriveTypeMaplets]
      erw [fireSyntax_count, nodeCounts_cons, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
      refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveTy_count calculus replacement)
        (Nat.add_le_add (deriveTy_count calculus key) (Nat.add_le_add_right (deriveTypeMaplets_count rest) 0))) 1) ?_
      rw [weight_typeMapletsP_cons]
      omega

theorem deriveTypeMaplets_max : ∀ entries : List (Ty × Ty),
    maxJudgment (deriveTypeMaplets calculus entries) = weight (wfJ "TypeMaplets" (typeMapletsP entries))
  | [] => by
      rw [deriveTypeMaplets]
      erw [fireSyntax_max, maxJudgments_nil, Nat.max_zero]
  | (replacement, key) :: rest => by
      rw [deriveTypeMaplets]
      erw [fireSyntax_max, maxJudgments_cons, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero,
        deriveTy_max, deriveTy_max, deriveTypeMaplets_max rest]
      apply max_eq_left
      rw [weight_wfJ, weight_wfJ, weight_wfJ, weight_wfJ, weight_typeMapletsP_cons]
      rw [show "TypeMaplets".length = 11 from rfl, show "Ty".length = 2 from rfl]
      omega

theorem deriveNth_count : ∀ (context : List Ty) (index : Nat) (type : Ty) (found : context[index]? = some type),
    nodeCount (deriveNth calculus context index type found) = index + 1
  | first :: rest, 0, type, found => by
      rw [deriveNth]
      erw [nodeCount_fireAt, nodeCounts_nil]
  | first :: rest, index + 1, type, found => by
      rw [deriveNth]
      erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_nil, deriveNth_count rest index type]
      omega
  | [], _, _, found => absurd found (by simp)

theorem deriveNth_max : ∀ (context : List Ty) (index : Nat) (type : Ty) (found : context[index]? = some type),
    maxJudgment (deriveNth calculus context index type found) =
      weight (nthJ (contextP context) (groundP (encodeUnary index)) (groundP (encodeTy type)))
  | first :: rest, 0, type, found => by
      rw [deriveNth]
      erw [maxJudgment_fireAt, maxJudgments_nil, Nat.max_zero]
  | first :: rest, index + 1, type, found => by
      rw [deriveNth]
      erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_nil, Nat.max_zero, deriveNth_max rest index type]
      apply max_eq_left
      rw [weight_nthJ, weight_nthJ, weight_contextP_cons, weight_encodeUnary, weight_encodeUnary]
      omega
  | [], _, _, found => absurd found (by simp)

theorem deriveTypeOf_count (context : List Ty) : ∀ (term : DBTerm) (type : Ty) (typed : term.inferType context = some type),
    nodeCount (deriveTypeOf calculus context term type typed) ≤
      (weight (groundP (encodeTerm term)) + 1) * (weight (contextP context) + weight (groundP (encodeTerm term)) + 1)
  | .const constant annotation, type, typed => by
      rw [deriveTypeOf]
      erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
      refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveConst_count calculus constant)
        (Nat.add_le_add_right (deriveTy_count calculus annotation) 0)) 1) ?_
      rw [weight_encodeTerm_const]
      nlinarith
  | .free sourceVar, type, typed => by
      rw [deriveTypeOf]
      erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
      refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveName_count calculus sourceVar.name)
        (Nat.add_le_add_right (deriveTy_count calculus sourceVar.ty) 0)) 1) ?_
      rw [weight_encodeTerm_free]
      nlinarith
  | .bound index, type, typed => by
      rw [deriveTypeOf]
      erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_nil, deriveNth_count]
      rw [weight_encodeTerm_bound, weight_encodeUnary]
      nlinarith
  | .app function argument, type, typed => by
      rw [deriveTypeOf]
      split
      · rename_i domain argumentTyped
        erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
        refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveTypeOf_count context function _ _)
          (Nat.add_le_add_right (deriveTypeOf_count context argument domain argumentTyped) 0)) 1) ?_
        rw [weight_encodeTerm_app]
        nlinarith
      · rename_i argumentTyped
        exact absurd typed (by
          intro typed'
          obtain ⟨_, _, argumentTyped'⟩ := DBTerm.inferType_app_eq_some_iff.mp typed'
          rw [argumentTyped] at argumentTyped'
          cases argumentTyped')
  | .abs domain body, type, typed => by
      rw [deriveTypeOf]
      split
      · rename_i codomain bodyTyped
        erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
        refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveTy_count calculus domain)
          (Nat.add_le_add_right (deriveTypeOf_count (domain :: context) body codomain bodyTyped) 0)) 1) ?_
        rw [weight_encodeTerm_abs, weight_contextP_cons]
        nlinarith
      · rename_i bodyTyped
        exact absurd typed (by
          intro typed'
          obtain ⟨_, bodyTyped', _⟩ := DBTerm.inferType_abs_eq_some_iff.mp typed'
          rw [bodyTyped] at bodyTyped'
          cases bodyTyped')

theorem deriveTypeOf_max (context : List Ty) : ∀ (term : DBTerm) (type : Ty) (typed : term.inferType context = some type),
    maxJudgment (deriveTypeOf calculus context term type typed) ≤
      400 + 40 * weight (contextP context) + 40 * weight (groundP (encodeTerm term))
  | .const constant annotation, type, typed => by
      have root := weight_inferType context _ type typed
      rw [deriveTypeOf]
      erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero,
        deriveConst_max, deriveTy_max]
      rw [weight_typeOfJ, weight_wfJ, weight_wfJ, weight_encodeTerm_const] at *
      rw [show "Const".length = 5 from rfl, show "Ty".length = 2 from rfl]
      refine max_le (by omega) (max_le (by omega) (by omega))
  | .free sourceVar, type, typed => by
      have root := weight_inferType context _ type typed
      rw [deriveTypeOf]
      erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero,
        deriveName_max, deriveTy_max]
      rw [weight_typeOfJ, weight_wfJ, weight_wfJ, weight_encodeTerm_free] at *
      rw [show "Name".length = 4 from rfl, show "Ty".length = 2 from rfl]
      refine max_le (by omega) (max_le (by omega) (by omega))
  | .bound index, type, typed => by
      have root := weight_inferType context _ type typed
      rw [deriveTypeOf]
      erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_nil, Nat.max_zero, deriveNth_max]
      rw [weight_typeOfJ, weight_nthJ, weight_encodeTerm_bound] at *
      refine max_le (by omega) (by omega)
  | .app function argument, type, typed => by
      have root := weight_inferType context _ type typed
      rw [deriveTypeOf]
      split
      · rename_i domain argumentTyped
        erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero]
        have functionBound := deriveTypeOf_max context function (Ty.function domain type) (by
          obtain ⟨domain', functionTyped', argumentTyped'⟩ := DBTerm.inferType_app_eq_some_iff.mp typed
          obtain rfl : domain' = domain := Option.some.inj (argumentTyped'.symm.trans argumentTyped)
          exact functionTyped')
        have argumentBound := deriveTypeOf_max context argument domain argumentTyped
        rw [weight_typeOfJ, weight_encodeTerm_app] at *
        refine max_le (by omega) (max_le (le_trans functionBound (by omega)) (le_trans argumentBound (by omega)))
      · rename_i argumentTyped
        exact absurd typed (by
          intro typed'
          obtain ⟨_, _, argumentTyped'⟩ := DBTerm.inferType_app_eq_some_iff.mp typed'
          rw [argumentTyped] at argumentTyped'
          cases argumentTyped')
  | .abs domain body, type, typed => by
      have root := weight_inferType context _ type typed
      rw [deriveTypeOf]
      split
      · rename_i codomain bodyTyped
        erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero, deriveTy_max]
        have bodyBound := deriveTypeOf_max (domain :: context) body codomain bodyTyped
        rw [weight_typeOfJ, weight_wfJ, weight_encodeTerm_abs, weight_contextP_cons] at *
        rw [show "Ty".length = 2 from rfl]
        refine max_le (by omega) (max_le (by omega) (le_trans bodyBound (by omega)))
      · rename_i bodyTyped
        exact absurd typed (by
          intro typed'
          obtain ⟨_, bodyTyped', _⟩ := DBTerm.inferType_abs_eq_some_iff.mp typed'
          rw [bodyTyped] at bodyTyped'
          cases bodyTyped')

/-! ## Binders and the conversion to de Bruijn form -/

theorem deriveBoundIndex_count (needle : SourceVar) : ∀ (binders : List SourceVar) (index : Nat)
    (found : boundIndex needle binders = some index),
    nodeCount (deriveBoundIndex calculus needle binders index found) ≤
      weight (bindersP binders) * (weight (freeVarP needle) + 2)
  | binder :: rest, index, found => by
      rw [deriveBoundIndex]
      split
      · erw [nodeCount_fireAt, nodeCounts_nil]
        rw [weight_bindersP_cons]
        nlinarith
      · split
        · rename_i position restFound
          erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
          refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveNeq_count calculus _ _ _)
            (Nat.add_le_add_right (deriveBoundIndex_count needle rest position restFound) 0)) 1) ?_
          rw [weight_bindersP_cons]
          show 1 + (1 + weight (freeVarP needle) + weight (freeVarP binder) + _) ≤ _
          nlinarith
        · rename_i restMissing
          exact absurd found (by simp [boundIndex, *])
  | [], _, found => absurd found (by simp [boundIndex])

theorem deriveBoundIndex_max (needle : SourceVar) : ∀ (binders : List SourceVar) (index : Nat)
    (found : boundIndex needle binders = some index),
    maxJudgment (deriveBoundIndex calculus needle binders index found) ≤
      weight (boundIndexJ (bindersP binders) (freeVarP needle) (groundP (encodeUnary index)))
  | binder :: rest, index, found => by
      rw [deriveBoundIndex]
      split
      · erw [maxJudgment_fireAt, maxJudgments_nil, Nat.max_zero]
      · split
        · rename_i position restFound
          have indexEq : index = position + 1 := by
            simp [boundIndex, *] at found
            omega
          subst indexEq
          erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero,
            deriveNeq_max]
          refine max_le (le_refl _) (max_le ?_ (le_trans (deriveBoundIndex_max needle rest position restFound) ?_))
          · show weight (neqJ (freeVarP needle) (freeVarP binder)) ≤ _
            rw [weight_neqJ, weight_boundIndexJ, weight_bindersP_cons]
            omega
          · rw [weight_boundIndexJ, weight_boundIndexJ, weight_bindersP_cons, weight_encodeUnary, weight_encodeUnary]
            omega
        · rename_i restMissing
          exact absurd found (by simp [boundIndex, *])
  | [], _, found => absurd found (by simp [boundIndex])

theorem deriveNotBound_count (needle : SourceVar) : ∀ (binders : List SourceVar) (missing : boundIndex needle binders = none),
    nodeCount (deriveNotBound calculus needle binders missing) ≤ weight (bindersP binders) * (weight (freeVarP needle) + 2)
  | [], _ => by
      rw [deriveNotBound]
      erw [nodeCount_fireAt, nodeCounts_nil]
      rw [weight_bindersP_nil]
      nlinarith
  | binder :: rest, missing => by
      rw [deriveNotBound]
      erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
      refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveNeq_count calculus _ _ _)
        (Nat.add_le_add_right (deriveNotBound_count needle rest _) 0)) 1) ?_
      rw [weight_bindersP_cons]
      show 1 + (1 + weight (freeVarP needle) + weight (freeVarP binder) + _) ≤ _
      nlinarith

theorem deriveNotBound_max (needle : SourceVar) : ∀ (binders : List SourceVar) (missing : boundIndex needle binders = none),
    maxJudgment (deriveNotBound calculus needle binders missing) ≤ weight (notBoundJ (bindersP binders) (freeVarP needle))
  | [], _ => by
      rw [deriveNotBound]
      erw [maxJudgment_fireAt, maxJudgments_nil, Nat.max_zero]
  | binder :: rest, missing => by
      rw [deriveNotBound]
      erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero, deriveNeq_max]
      refine max_le (le_refl _) (max_le ?_ (le_trans (deriveNotBound_max needle rest _) ?_))
      · show weight (neqJ (freeVarP needle) (freeVarP binder)) ≤ _
        rw [weight_neqJ, weight_notBoundJ, weight_bindersP_cons]
        omega
      · rw [weight_notBoundJ, weight_notBoundJ, weight_bindersP_cons]
        omega

theorem deriveToDB_count (binders : List SourceVar) : ∀ source : SourceTerm,
    nodeCount (deriveToDB calculus binders source) ≤
      2 * (weight (groundP (encodeSourceTerm source)) + 1) *
        (weight (bindersP binders) + 2 * weight (groundP (encodeSourceTerm source)) + 2)
  | .const constant type => by
      rw [deriveToDB]
      erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
      refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveConst_count calculus constant)
        (Nat.add_le_add_right (deriveTy_count calculus type) 0)) 1) ?_
      rw [weight_sourceConst]
      nlinarith
  | .var name type => by
      rw [deriveToDB]
      split
      · rename_i index found
        erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
        refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveName_count calculus name)
          (Nat.add_le_add (deriveTy_count calculus type)
            (Nat.add_le_add_right (deriveBoundIndex_count calculus ⟨name, type⟩ binders index found) 0))) 1) ?_
        rw [weight_sourceVar, weight_freeVarP]
        nlinarith
      · rename_i found
        erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
        refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveName_count calculus name)
          (Nat.add_le_add (deriveTy_count calculus type)
            (Nat.add_le_add_right (deriveNotBound_count calculus ⟨name, type⟩ binders found) 0))) 1) ?_
        rw [weight_sourceVar, weight_freeVarP]
        nlinarith
  | .app function argument => by
      rw [deriveToDB]
      erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
      refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveToDB_count binders function)
        (Nat.add_le_add_right (deriveToDB_count binders argument) 0)) 1) ?_
      rw [weight_sourceApp]
      nlinarith
  | .abs name type body => by
      rw [deriveToDB]
      erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
      refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveName_count calculus name)
        (Nat.add_le_add (deriveTy_count calculus type)
          (Nat.add_le_add_right (deriveToDB_count (⟨name, type⟩ :: binders) body) 0))) 1) ?_
      rw [weight_sourceAbs, weight_bindersP_cons, weight_freeVarP]
      nlinarith

theorem deriveToDB_max (binders : List SourceVar) : ∀ source : SourceTerm,
    maxJudgment (deriveToDB calculus binders source) ≤
      4 * (weight (bindersP binders) + 2 * weight (groundP (encodeSourceTerm source)) + 2) ^ 2
  | .const constant type => by
      have converted := weight_toDB binders (.const constant type)
      rw [deriveToDB]
      erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero,
        deriveConst_max, deriveTy_max]
      rw [weight_toDBJ, weight_wfJ, weight_wfJ]
      rw [weight_sourceConst] at *
      rw [show "Const".length = 5 from rfl, show "Ty".length = 2 from rfl]
      refine max_le (by nlinarith) (max_le (by nlinarith) (by nlinarith))
  | .var name type => by
      have converted := weight_toDB binders (.var name type)
      rw [deriveToDB]
      split
      · rename_i index found
        have small := boundIndex_lt found
        have count := bindersP_length_le binders
        erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil,
          Nat.max_zero, deriveName_max, deriveTy_max]
        have lookup := deriveBoundIndex_max calculus ⟨name, type⟩ binders index found
        rw [weight_boundIndexJ, weight_freeVarP, weight_encodeUnary] at lookup
        rw [weight_toDBJ, weight_wfJ, weight_wfJ]
        rw [weight_sourceVar] at *
        rw [show "Name".length = 4 from rfl, show "Ty".length = 2 from rfl]
        refine max_le (by nlinarith) (max_le (by nlinarith) (max_le (by nlinarith) (le_trans lookup (by nlinarith))))
      · rename_i found
        erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil,
          Nat.max_zero, deriveName_max, deriveTy_max]
        have lookup := deriveNotBound_max calculus ⟨name, type⟩ binders found
        rw [weight_notBoundJ, weight_freeVarP] at lookup
        rw [weight_toDBJ, weight_wfJ, weight_wfJ]
        rw [weight_sourceVar] at *
        rw [show "Name".length = 4 from rfl, show "Ty".length = 2 from rfl]
        refine max_le (by nlinarith) (max_le (by nlinarith) (max_le (by nlinarith) (le_trans lookup (by nlinarith))))
  | .app function argument => by
      have converted := weight_toDB binders (.app function argument)
      rw [deriveToDB]
      erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero]
      have first := deriveToDB_max binders function
      have second := deriveToDB_max binders argument
      rw [weight_toDBJ]
      rw [weight_sourceApp] at *
      refine max_le (by nlinarith) (max_le (le_trans first (by nlinarith)) (le_trans second (by nlinarith)))
  | .abs name type body => by
      have converted := weight_toDB binders (.abs name type body)
      rw [deriveToDB]
      erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil,
        Nat.max_zero, deriveName_max, deriveTy_max]
      have inner := deriveToDB_max (⟨name, type⟩ :: binders) body
      rw [weight_bindersP_cons, weight_freeVarP] at inner
      rw [weight_toDBJ, weight_wfJ, weight_wfJ]
      rw [weight_sourceAbs] at *
      rw [show "Name".length = 4 from rfl, show "Ty".length = 2 from rfl]
      refine max_le (by nlinarith) (max_le (by nlinarith) (max_le (by nlinarith) (le_trans inner (by nlinarith))))

/-! ## Free variables, closing a variable, instantiation -/

theorem deriveNotFree_count (needle : SourceVar) : ∀ (term : DBTerm) (absent : DBTerm.hasFree needle term = false),
    nodeCount (deriveNotFree calculus needle term absent) ≤
      weight (groundP (encodeTerm term)) * (weight (freeVarP needle) + 2)
  | .const constant type, absent => by
      rw [deriveNotFree]
      erw [nodeCount_fireAt, nodeCounts_nil]
      rw [weight_encodeTerm_const]
      nlinarith
  | .free sourceVar, absent => by
      rw [deriveNotFree]
      erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_nil]
      refine le_trans (Nat.add_le_add_left (Nat.add_le_add_right (deriveNeq_count calculus _ _ _) 0) 1) ?_
      show 1 + (1 + weight (freeVarP needle) + weight (groundP (encodeTerm (.free sourceVar))) + 0) ≤ _
      rw [weight_encodeTerm_free]
      nlinarith
  | .bound index, absent => by
      rw [deriveNotFree]
      erw [nodeCount_fireAt, nodeCounts_nil]
      rw [weight_encodeTerm_bound]
      nlinarith
  | .app function argument, absent => by
      rw [deriveNotFree]
      erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
      refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveNotFree_count needle function _)
        (Nat.add_le_add_right (deriveNotFree_count needle argument _) 0)) 1) ?_
      rw [weight_encodeTerm_app]
      nlinarith
  | .abs domain body, absent => by
      rw [deriveNotFree]
      erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_nil]
      refine le_trans (Nat.add_le_add_left (Nat.add_le_add_right (deriveNotFree_count needle body _) 0) 1) ?_
      rw [weight_encodeTerm_abs]
      nlinarith

theorem deriveNotFree_max (needle : SourceVar) : ∀ (term : DBTerm) (absent : DBTerm.hasFree needle term = false),
    maxJudgment (deriveNotFree calculus needle term absent) ≤ weight (notFreeJ (freeVarP needle) (groundP (encodeTerm term)))
  | .const constant type, absent => by
      rw [deriveNotFree]
      erw [maxJudgment_fireAt, maxJudgments_nil, Nat.max_zero]
  | .free sourceVar, absent => by
      rw [deriveNotFree]
      erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_nil, Nat.max_zero, deriveNeq_max]
      refine max_le (le_refl _) ?_
      show weight (neqJ (freeVarP needle) (groundP (encodeTerm (.free sourceVar)))) ≤ _
      rw [weight_neqJ, weight_notFreeJ]
      omega
  | .bound index, absent => by
      rw [deriveNotFree]
      erw [maxJudgment_fireAt, maxJudgments_nil, Nat.max_zero]
  | .app function argument, absent => by
      rw [deriveNotFree]
      erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero]
      refine max_le (le_refl _) (max_le (le_trans (deriveNotFree_max needle function _) ?_)
        (le_trans (deriveNotFree_max needle argument _) ?_))
      · rw [weight_notFreeJ, weight_notFreeJ, weight_encodeTerm_app]
        omega
      · rw [weight_notFreeJ, weight_notFreeJ, weight_encodeTerm_app]
        omega
  | .abs domain body, absent => by
      rw [deriveNotFree]
      erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_nil, Nat.max_zero]
      refine max_le (le_refl _) (le_trans (deriveNotFree_max needle body _) ?_)
      rw [weight_notFreeJ, weight_notFreeJ, weight_encodeTerm_abs]
      omega

theorem deriveNotFreeAll_count (needle : SourceVar) : ∀ (terms : List DBTerm)
    (absent : ∀ term ∈ terms, DBTerm.hasFree needle term = false),
    nodeCount (deriveNotFreeAll calculus needle terms absent) ≤ weight (termsP terms) * (weight (freeVarP needle) + 2)
  | [], _ => by
      rw [deriveNotFreeAll]
      erw [nodeCount_fireAt, nodeCounts_nil]
      rw [weight_termsP_nil]
      nlinarith
  | term :: rest, absent => by
      rw [deriveNotFreeAll]
      erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
      refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveNotFree_count calculus needle term _)
        (Nat.add_le_add_right (deriveNotFreeAll_count needle rest _) 0)) 1) ?_
      rw [weight_termsP_cons]
      nlinarith

theorem deriveNotFreeAll_max (needle : SourceVar) : ∀ (terms : List DBTerm)
    (absent : ∀ term ∈ terms, DBTerm.hasFree needle term = false),
    maxJudgment (deriveNotFreeAll calculus needle terms absent) ≤ weight (notFreeAllJ (freeVarP needle) (termsP terms))
  | [], _ => by
      rw [deriveNotFreeAll]
      erw [maxJudgment_fireAt, maxJudgments_nil, Nat.max_zero]
  | term :: rest, absent => by
      rw [deriveNotFreeAll]
      erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero]
      refine max_le (le_refl _) (max_le (le_trans (deriveNotFree_max calculus needle term _) ?_)
        (le_trans (deriveNotFreeAll_max needle rest _) ?_))
      · rw [weight_notFreeJ, weight_notFreeAllJ, weight_termsP_cons]
        omega
      · rw [weight_notFreeAllJ, weight_notFreeAllJ, weight_termsP_cons]
        omega

theorem deriveClose_count (needle : SourceVar) : ∀ (level : Nat) (term : DBTerm),
    nodeCount (deriveClose calculus needle level term) ≤
      weight (groundP (encodeTerm term)) * (weight (freeVarP needle) + 2)
  | level, .const constant type => by
      rw [deriveClose]
      erw [nodeCount_fireAt, nodeCounts_nil]
      rw [weight_encodeTerm_const]
      nlinarith
  | level, .free sourceVar => by
      rw [deriveClose]
      split
      · erw [nodeCount_fireAt, nodeCounts_nil]
        rw [weight_encodeTerm_free]
        nlinarith
      · erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_nil]
        refine le_trans (Nat.add_le_add_left (Nat.add_le_add_right (deriveNeq_count calculus _ _ _) 0) 1) ?_
        show 1 + (1 + weight (freeVarP needle) + weight (groundP (encodeTerm (.free sourceVar))) + 0) ≤ _
        rw [weight_encodeTerm_free]
        nlinarith
  | level, .bound index => by
      rw [deriveClose]
      erw [nodeCount_fireAt, nodeCounts_nil]
      rw [weight_encodeTerm_bound]
      nlinarith
  | level, .app function argument => by
      rw [deriveClose]
      erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
      refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveClose_count needle level function)
        (Nat.add_le_add_right (deriveClose_count needle level argument) 0)) 1) ?_
      rw [weight_encodeTerm_app]
      nlinarith
  | level, .abs domain body => by
      rw [deriveClose]
      erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_nil]
      refine le_trans (Nat.add_le_add_left (Nat.add_le_add_right (deriveClose_count needle (level + 1) body) 0) 1) ?_
      rw [weight_encodeTerm_abs]
      nlinarith

theorem deriveClose_max (needle : SourceVar) : ∀ (level : Nat) (term : DBTerm),
    maxJudgment (deriveClose calculus needle level term) ≤
      weight (closeJ (freeVarP needle) (groundP (encodeUnary level)) (groundP (encodeTerm term))
        (groundP (encodeTerm (DBTerm.closeFreeAt needle level term))))
  | level, .const constant type => by
      rw [deriveClose]
      erw [maxJudgment_fireAt, maxJudgments_nil, Nat.max_zero]
  | level, .free sourceVar => by
      rw [deriveClose]
      split
      · erw [maxJudgment_fireAt, maxJudgments_nil, Nat.max_zero]
      · erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_nil, Nat.max_zero, deriveNeq_max]
        refine max_le (le_refl _) ?_
        show weight (neqJ (freeVarP needle) (groundP (encodeTerm (.free sourceVar)))) ≤ _
        rw [weight_neqJ, weight_closeJ]
        omega
  | level, .bound index => by
      rw [deriveClose]
      erw [maxJudgment_fireAt, maxJudgments_nil, Nat.max_zero]
  | level, .app function argument => by
      rw [deriveClose]
      erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero]
      refine max_le (le_refl _) (max_le (le_trans (deriveClose_max needle level function) ?_)
        (le_trans (deriveClose_max needle level argument) ?_))
      · simp only [DBTerm.closeFreeAt]
        rw [weight_closeJ, weight_closeJ, weight_encodeTerm_app, weight_encodeTerm_app]
        omega
      · simp only [DBTerm.closeFreeAt]
        rw [weight_closeJ, weight_closeJ, weight_encodeTerm_app, weight_encodeTerm_app]
        omega
  | level, .abs domain body => by
      rw [deriveClose]
      erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_nil, Nat.max_zero]
      refine max_le (le_refl _) (le_trans (deriveClose_max needle (level + 1) body) ?_)
      simp only [DBTerm.closeFreeAt]
      rw [weight_closeJ, weight_closeJ, weight_encodeTerm_abs, weight_encodeTerm_abs, weight_encodeUnary,
        weight_encodeUnary]
      omega

theorem deriveInstantiate_count (replacement : DBTerm) : ∀ (level : Nat) (term : DBTerm),
    nodeCount (deriveInstantiate calculus replacement level term) ≤
      weight (groundP (encodeTerm term)) *
        (weight (groundP (encodeUnary level)) + weight (groundP (encodeTerm term)) + 2)
  | level, .const constant type => by
      rw [deriveInstantiate]
      erw [nodeCount_fireAt, nodeCounts_nil]
      rw [weight_encodeTerm_const]
      nlinarith
  | level, .free sourceVar => by
      rw [deriveInstantiate]
      erw [nodeCount_fireAt, nodeCounts_nil]
      rw [weight_encodeTerm_free]
      nlinarith
  | level, .bound index => by
      rw [deriveInstantiate]
      split
      · erw [nodeCount_fireAt, nodeCounts_nil]
        rw [weight_encodeTerm_bound]
        nlinarith
      · erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_nil]
        refine le_trans (Nat.add_le_add_left (Nat.add_le_add_right (deriveNeq_count calculus _ _ _) 0) 1) ?_
        show 1 + (1 + weight (groundP (encodeUnary index)) + weight (groundP (encodeUnary level)) + 0) ≤ _
        rw [weight_encodeTerm_bound]
        nlinarith
  | level, .app function argument => by
      rw [deriveInstantiate]
      erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
      refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveInstantiate_count replacement level function)
        (Nat.add_le_add_right (deriveInstantiate_count replacement level argument) 0)) 1) ?_
      rw [weight_encodeTerm_app]
      nlinarith
  | level, .abs domain body => by
      rw [deriveInstantiate]
      erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_nil]
      refine le_trans (Nat.add_le_add_left (Nat.add_le_add_right (deriveInstantiate_count replacement (level + 1) body) 0) 1) ?_
      rw [weight_encodeTerm_abs, weight_encodeUnary, weight_encodeUnary]
      nlinarith

theorem deriveInstantiate_max (replacement : DBTerm) : ∀ (level : Nat) (term : DBTerm),
    maxJudgment (deriveInstantiate calculus replacement level term) ≤
      weight (instantiateJ (groundP (encodeTerm replacement)) (groundP (encodeUnary level))
        (groundP (encodeTerm term)) (groundP (encodeTerm (DBTerm.instantiateAt replacement level term))))
  | level, .const constant type => by
      rw [deriveInstantiate]
      erw [maxJudgment_fireAt, maxJudgments_nil, Nat.max_zero]
  | level, .free sourceVar => by
      rw [deriveInstantiate]
      erw [maxJudgment_fireAt, maxJudgments_nil, Nat.max_zero]
  | level, .bound index => by
      rw [deriveInstantiate]
      split
      · erw [maxJudgment_fireAt, maxJudgments_nil, Nat.max_zero]
      · erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_nil, Nat.max_zero, deriveNeq_max]
        refine max_le (le_refl _) ?_
        show weight (neqJ (groundP (encodeUnary index)) (groundP (encodeUnary level))) ≤ _
        rw [weight_neqJ, weight_instantiateJ, weight_encodeTerm_bound]
        omega
  | level, .app function argument => by
      rw [deriveInstantiate]
      erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero]
      refine max_le (le_refl _) (max_le (le_trans (deriveInstantiate_max replacement level function) ?_)
        (le_trans (deriveInstantiate_max replacement level argument) ?_))
      · simp only [DBTerm.instantiateAt]
        rw [weight_instantiateJ, weight_instantiateJ, weight_encodeTerm_app, weight_encodeTerm_app]
        omega
      · simp only [DBTerm.instantiateAt]
        rw [weight_instantiateJ, weight_instantiateJ, weight_encodeTerm_app, weight_encodeTerm_app]
        omega
  | level, .abs domain body => by
      rw [deriveInstantiate]
      erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_nil, Nat.max_zero]
      refine max_le (le_refl _) (le_trans (deriveInstantiate_max replacement (level + 1) body) ?_)
      simp only [DBTerm.instantiateAt]
      rw [weight_instantiateJ, weight_instantiateJ, weight_encodeTerm_abs, weight_encodeTerm_abs, weight_encodeUnary,
        weight_encodeUnary]
      omega

/-! ## Union, erase, insertion and sorting -/

theorem deriveLt_count_ground (first second : LabeledTree) (lower : first < second) :
    nodeCount (deriveLt calculus first second lower) ≤ weight (groundP first) + weight (groundP second) :=
  deriveLt_count calculus first second lower

theorem deriveLt_max_ground (first second : LabeledTree) (lower : first < second) :
    maxJudgment (deriveLt calculus first second lower) ≤ weight (ltJudgment (groundP first) (groundP second)) :=
  deriveLt_max calculus first second lower

theorem deriveNeq_count_ground (first second : LabeledTree) (different : first ≠ second) :
    nodeCount (deriveNeq calculus first second different) ≤ 1 + weight (groundP first) + weight (groundP second) :=
  deriveNeq_count calculus first second different

theorem deriveNeq_max_ground (first second : LabeledTree) (different : first ≠ second) :
    maxJudgment (deriveNeq calculus first second different) ≤ weight (neqJ (groundP first) (groundP second)) :=
  le_of_eq (deriveNeq_max calculus first second different)

theorem deriveUnion_count : ∀ firsts seconds : List LabeledTree,
    nodeCount (deriveUnion calculus firsts seconds) ≤
      (weight (treesP firsts) + weight (treesP seconds)) * (weight (treesP firsts) + weight (treesP seconds))
  | [], seconds => by
      rw [deriveUnion]
      erw [nodeCount_fireAt, nodeCounts_nil]
      rw [weight_treesP_nil]
      nlinarith
  | first :: firsts, [] => by
      rw [deriveUnion]
      erw [nodeCount_fireAt, nodeCounts_nil]
      rw [weight_treesP_nil]
      nlinarith
  | first :: firsts, second :: seconds => by
      have secondsWeight := weight_treesP_cons second seconds
      rw [deriveUnion]
      split
      · erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
        refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveLt_count_ground calculus _ _ _)
          (Nat.add_le_add_right (deriveUnion_count firsts (second :: seconds)) 0)) 1) ?_
        rw [weight_treesP_cons first firsts]
        nlinarith
      · split
        · erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
          refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveLt_count_ground calculus _ _ _)
            (Nat.add_le_add_right (deriveUnion_count (first :: firsts) seconds) 0)) 1) ?_
          have firstsWeight := weight_treesP_cons first firsts
          rw [secondsWeight]
          nlinarith
        · erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_nil]
          refine le_trans (Nat.add_le_add_left (Nat.add_le_add_right (deriveUnion_count firsts seconds) 0) 1) ?_
          rw [weight_treesP_cons first firsts, secondsWeight]
          nlinarith
termination_by firsts seconds => firsts.length + seconds.length

theorem deriveUnion_max : ∀ firsts seconds : List LabeledTree,
    maxJudgment (deriveUnion calculus firsts seconds) ≤
      weight (unionJ (treesP firsts) (treesP seconds) (treesP (treeUnion firsts seconds)))
  | [], seconds => by
      rw [deriveUnion]
      erw [maxJudgment_fireAt, maxJudgments_nil, Nat.max_zero]
  | first :: firsts, [] => by
      rw [deriveUnion]
      erw [maxJudgment_fireAt, maxJudgments_nil, Nat.max_zero]
  | first :: firsts, second :: seconds => by
      have firstsWeight := weight_treesP_cons first firsts
      have secondsWeight := weight_treesP_cons second seconds
      rw [deriveUnion]
      split
      · rename_i lower
        have rest := deriveUnion_max firsts (second :: seconds)
        have result := weight_treesP_cons first (treeUnion firsts (second :: seconds))
        have unfolded : treeUnion (first :: firsts) (second :: seconds) =
            first :: treeUnion firsts (second :: seconds) := by
          rw [treeUnion, if_pos lower]
        erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero]
        refine max_le (le_refl _) (max_le (le_trans (deriveLt_max_ground calculus _ _ _) ?_) (le_trans rest ?_))
        · rw [weight_ltJudgment, weight_unionJ]
          omega
        · rw [weight_unionJ, weight_unionJ, unfolded]
          omega
      · split
        · rename_i lower upper
          have rest := deriveUnion_max (first :: firsts) seconds
          have result := weight_treesP_cons second (treeUnion (first :: firsts) seconds)
          have unfolded : treeUnion (first :: firsts) (second :: seconds) =
              second :: treeUnion (first :: firsts) seconds := by
            rw [treeUnion, if_neg lower, if_pos upper]
          erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero]
          refine max_le (le_refl _) (max_le (le_trans (deriveLt_max_ground calculus _ _ _) ?_) (le_trans rest ?_))
          · rw [weight_ltJudgment, weight_unionJ]
            omega
          · rw [weight_unionJ, weight_unionJ, unfolded]
            omega
        · rename_i lower upper
          have rest := deriveUnion_max firsts seconds
          have result := weight_treesP_cons first (treeUnion firsts seconds)
          have unfolded : treeUnion (first :: firsts) (second :: seconds) = first :: treeUnion firsts seconds := by
            rw [treeUnion, if_neg lower, if_neg upper]
          erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_nil, Nat.max_zero]
          refine max_le (le_refl _) (le_trans rest ?_)
          rw [weight_unionJ, weight_unionJ, unfolded]
          omega
termination_by firsts seconds => firsts.length + seconds.length

theorem deriveErase_count (tree : LabeledTree) : ∀ trees : List LabeledTree,
    nodeCount (deriveErase calculus tree trees) ≤ weight (treesP trees) * (weight (groundP tree) + 2)
  | [] => by
      rw [deriveErase]
      erw [nodeCount_fireAt, nodeCounts_nil]
      rw [weight_treesP_nil]
      omega
  | first :: rest => by
      rw [deriveErase]
      split
      · erw [nodeCount_fireAt, nodeCounts_nil]
        rw [weight_treesP_cons]
        nlinarith
      · erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
        refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveNeq_count_ground calculus _ _ _)
          (Nat.add_le_add_right (deriveErase_count tree rest) 0)) 1) ?_
        rw [weight_treesP_cons]
        nlinarith

theorem deriveErase_max (tree : LabeledTree) : ∀ trees : List LabeledTree,
    maxJudgment (deriveErase calculus tree trees) ≤
      weight (eraseJ (groundP tree) (treesP trees) (treesP (treeErase tree trees)))
  | [] => by
      rw [deriveErase]
      erw [maxJudgment_fireAt, maxJudgments_nil, Nat.max_zero]
  | first :: rest => by
      have before := weight_treesP_cons first rest
      have after := weight_treesP_cons first (treeErase tree rest)
      rw [deriveErase]
      split
      · erw [maxJudgment_fireAt, maxJudgments_nil, Nat.max_zero]
      · rename_i different
        have unfolded : treeErase tree (first :: rest) = first :: treeErase tree rest := by
          rw [treeErase, if_neg different]
        erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero]
        refine max_le (le_refl _) (max_le (le_trans (deriveNeq_max_ground calculus _ _ _) ?_)
          (le_trans (deriveErase_max tree rest) ?_))
        · rw [weight_neqJ, weight_eraseJ]
          omega
        · rw [weight_eraseJ, weight_eraseJ, unfolded]
          omega

theorem deriveInsert_count (tree : LabeledTree) : ∀ trees : List LabeledTree,
    nodeCount (deriveInsert calculus tree trees) ≤ weight (treesP trees) * (weight (groundP tree) + 2)
  | [] => by
      rw [deriveInsert]
      erw [nodeCount_fireAt, nodeCounts_nil]
      rw [weight_treesP_nil]
      omega
  | first :: rest => by
      rw [deriveInsert]
      split
      · erw [nodeCount_fireAt, nodeCounts_nil]
        rw [weight_treesP_cons]
        nlinarith
      · split
        · erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_nil]
          refine le_trans (Nat.add_le_add_left (Nat.add_le_add_right (deriveLt_count_ground calculus _ _ _) 0) 1) ?_
          rw [weight_treesP_cons]
          nlinarith
        · erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
          refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveLt_count_ground calculus _ _ _)
            (Nat.add_le_add_right (deriveInsert_count tree rest) 0)) 1) ?_
          rw [weight_treesP_cons]
          nlinarith

theorem deriveInsert_max (tree : LabeledTree) : ∀ trees : List LabeledTree,
    maxJudgment (deriveInsert calculus tree trees) ≤
      weight (insertJ (groundP tree) (treesP trees) (treesP (treeInsert tree trees)))
  | [] => by
      rw [deriveInsert]
      erw [maxJudgment_fireAt, maxJudgments_nil, Nat.max_zero]
  | first :: rest => by
      have before := weight_treesP_cons first rest
      have after := weight_treesP_cons first (treeInsert tree rest)
      rw [deriveInsert]
      split
      · erw [maxJudgment_fireAt, maxJudgments_nil, Nat.max_zero]
      · split
        · erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_nil, Nat.max_zero]
          refine max_le (le_refl _) (le_trans (deriveLt_max_ground calculus _ _ _) ?_)
          rw [weight_ltJudgment, weight_insertJ]
          omega
        · rename_i same lower
          have unfolded : treeInsert tree (first :: rest) = first :: treeInsert tree rest := by
            rw [treeInsert, if_neg same, if_neg lower]
          erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero]
          refine max_le (le_refl _) (max_le (le_trans (deriveLt_max_ground calculus _ _ _) ?_)
            (le_trans (deriveInsert_max tree rest) ?_))
          · rw [weight_ltJudgment, weight_insertJ]
            omega
          · rw [weight_insertJ, weight_insertJ, unfolded]
            omega

theorem deriveSort_count : ∀ trees : List LabeledTree,
    nodeCount (deriveSort calculus trees) ≤ weight (treesP trees) * weight (treesP trees)
  | [] => by
      rw [deriveSort]
      erw [nodeCount_fireAt, nodeCounts_nil]
      rw [weight_treesP_nil]
      norm_num
  | first :: rest => by
      have sorted := weight_treeSort rest
      rw [deriveSort]
      erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
      refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveSort_count rest)
        (Nat.add_le_add_right (deriveInsert_count calculus first (treeSort rest)) 0)) 1) ?_
      rw [weight_treesP_cons]
      nlinarith [Nat.mul_le_mul_right (weight (groundP first) + 2) sorted]

theorem deriveSort_max : ∀ trees : List LabeledTree,
    maxJudgment (deriveSort calculus trees) ≤ weight (sortJ (treesP trees) (treesP (treeSort trees)))
  | [] => by
      rw [deriveSort]
      erw [maxJudgment_fireAt, maxJudgments_nil, Nat.max_zero]
  | first :: rest => by
      have sorted := weight_treeSort rest
      have grows := weight_le_treeInsert first (treeSort rest)
      have before := weight_treesP_cons first rest
      have unfolded : treeSort (first :: rest) = treeInsert first (treeSort rest) := by rw [treeSort]
      rw [deriveSort]
      erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero]
      refine max_le (le_refl _) (max_le (le_trans (deriveSort_max rest) ?_)
        (le_trans (deriveInsert_max calculus first (treeSort rest)) ?_))
      · rw [weight_sortJ, weight_sortJ, unfolded]
        omega
      · rw [weight_insertJ, weight_sortJ, unfolded]
        omega

/-! ## Type instantiation -/

theorem weight_encodeTy_var (name : Name) :
    weight (groundP (encodeTy (.var name))) = 109 + weight (groundP (encodeName name)) := by
  rw [encodeTy, weight_groundP_node]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, show tyVarLabel = 6 from rfl]
  omega

theorem weight_encodeTy_op (operator : TypeOp) (arguments : List Ty) :
    weight (groundP (encodeTy (.op operator arguments))) =
      209 + weight (groundP (encodeTypeOp operator)) + weight (tysP arguments) := by
  rw [encodeTy, weight_groundP_node]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, weight_listNode_tys,
    show tyOpLabel = 7 from rfl]
  omega

theorem typeAction_var (entries : List (Ty × Ty)) (name : Name) :
    SourceSubstitution.typeAction entries (.var name) = SourceSubstitution.variableType entries name := by
  rw [SourceSubstitution.typeAction]

theorem typeAction_op (entries : List (Ty × Ty)) (operator : TypeOp) (arguments : List Ty) :
    SourceSubstitution.typeAction entries (.op operator arguments) =
      .op operator (arguments.map (SourceSubstitution.typeAction entries)) := by
  rw [SourceSubstitution.typeAction]

/-- **A name's type under the maplets is its variable or one of the replacements.** -/
theorem weight_variableType (name : Name) : ∀ entries : List (Ty × Ty),
    weight (groundP (encodeTy (SourceSubstitution.variableType entries name))) ≤
      weight (groundP (encodeTy (.var name))) + weight (typeMapletsP entries)
  | [] => by
      rw [SourceSubstitution.variableType]
      omega
  | (replacement, .var key) :: rest => by
      have restBound := weight_variableType name rest
      have entry := weight_typeMapletsP_cons replacement (.var key) rest
      rw [SourceSubstitution.variableType]
      split
      · omega
      · omega
  | (replacement, .op operator arguments) :: rest => by
      have restBound := weight_variableType name rest
      have entry := weight_typeMapletsP_cons replacement (.op operator arguments) rest
      rw [SourceSubstitution.variableType]
      omega

mutual
  /-- **Type instantiation multiplies a type's weight by at most the maplets' weight.** -/
  theorem weight_typeAction (entries : List (Ty × Ty)) : ∀ type : Ty,
      weight (groundP (encodeTy (SourceSubstitution.typeAction entries type))) ≤
        weight (groundP (encodeTy type)) * (weight (typeMapletsP entries) + 1)
    | .var name => by
        have found := weight_variableType name entries
        have positive := weight_encodeTy_var name
        rw [typeAction_var]
        nlinarith [Nat.mul_le_mul_right (weight (typeMapletsP entries))
          (show 1 ≤ weight (groundP (encodeTy (.var name))) by omega)]
    | .op operator arguments => by
        have inner := weight_typeActionList entries arguments
        rw [typeAction_op, weight_encodeTy_op, weight_encodeTy_op]
        nlinarith

  theorem weight_typeActionList (entries : List (Ty × Ty)) : ∀ types : List Ty,
      weight (tysP (types.map (SourceSubstitution.typeAction entries))) ≤
        weight (tysP types) * (weight (typeMapletsP entries) + 1)
    | [] => by
        rw [List.map_nil, show tysP [] = nilP from rfl, weight_nilP]
        omega
    | type :: rest => by
        have first := weight_typeAction entries type
        have second := weight_typeActionList entries rest
        rw [List.map_cons, weight_tysP_cons, weight_tysP_cons]
        nlinarith
end

theorem weight_termTypeAction (entries : List (Ty × Ty)) : ∀ term : DBTerm,
    weight (groundP (encodeTerm (termTypeAction entries term))) ≤
      weight (groundP (encodeTerm term)) * (weight (typeMapletsP entries) + 1)
  | .const constant type => by
      have acted := weight_typeAction entries type
      simp only [termTypeAction, weight_encodeTerm_const]
      nlinarith
  | .free sourceVar => by
      have acted := weight_typeAction entries sourceVar.ty
      simp only [termTypeAction, weight_encodeTerm_free]
      nlinarith
  | .bound index => by
      simp only [termTypeAction]
      nlinarith [Nat.zero_le (weight (groundP (encodeTerm (.bound index))) * weight (typeMapletsP entries))]
  | .app function argument => by
      have first := weight_termTypeAction entries function
      have second := weight_termTypeAction entries argument
      simp only [termTypeAction, weight_encodeTerm_app]
      nlinarith
  | .abs domain body => by
      have acted := weight_typeAction entries domain
      have inner := weight_termTypeAction entries body
      simp only [termTypeAction, weight_encodeTerm_abs]
      nlinarith

theorem weight_termTypeActionList (entries : List (Ty × Ty)) : ∀ terms : List DBTerm,
    weight (termsP (terms.map (termTypeAction entries))) ≤ weight (termsP terms) * (weight (typeMapletsP entries) + 1)
  | [] => by
      rw [List.map_nil, weight_termsP_nil]
      omega
  | term :: rest => by
      have first := weight_termTypeAction entries term
      have second := weight_termTypeActionList entries rest
      rw [List.map_cons, weight_termsP_cons, weight_termsP_cons]
      nlinarith

theorem weight_varTypeJ (entries name type : Pattern) :
    weight (varTypeJ entries name type) = 15 + weight entries + weight name + weight type := by
  simp only [varTypeJ, weight_apply, weights_cons, weights_nil]
  rw [show "hol.VarType".length = 11 from rfl]
  omega

theorem weight_tyActJ (entries type result : Pattern) :
    weight (tyActJ entries type result) = 13 + weight entries + weight type + weight result := by
  simp only [tyActJ, weight_apply, weights_cons, weights_nil]
  rw [show "hol.TyAct".length = 9 from rfl]
  omega

theorem weight_tyActListJ (entries types results : Pattern) :
    weight (tyActListJ entries types results) = 17 + weight entries + weight types + weight results := by
  simp only [tyActListJ, weight_apply, weights_cons, weights_nil]
  rw [show "hol.TyActList".length = 13 from rfl]
  omega

theorem weight_termTyActJ (entries term result : Pattern) :
    weight (termTyActJ entries term result) = 17 + weight entries + weight term + weight result := by
  simp only [termTyActJ, weight_apply, weights_cons, weights_nil]
  rw [show "hol.TermTyAct".length = 13 from rfl]
  omega

theorem weight_termTyActListJ (entries terms results : Pattern) :
    weight (termTyActListJ entries terms results) = 21 + weight entries + weight terms + weight results := by
  simp only [termTyActListJ, weight_apply, weights_cons, weights_nil]
  rw [show "hol.TermTyActList".length = 17 from rfl]
  omega

theorem deriveVarType_count : ∀ (entries : List (Ty × Ty)) (name : Name),
    nodeCount (deriveVarType calculus entries name) ≤
      weight (typeMapletsP entries) * (weight (groundP (encodeName name)) + 2)
  | [], name => by
      rw [deriveVarType]
      erw [nodeCount_fireAt, nodeCounts_nil]
      rw [show typeMapletsP [] = nilP from rfl, weight_nilP]
      omega
  | (replacement, .var key) :: rest, name => by
      have entry := weight_typeMapletsP_cons replacement (.var key) rest
      have keyWeight := weight_encodeTy_var key
      rw [deriveVarType]
      split
      · erw [nodeCount_fireAt, nodeCounts_nil]
        rw [entry]
        nlinarith
      · erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
        refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveNeq_count_ground calculus _ _ _)
          (Nat.add_le_add_right (deriveVarType_count rest name) 0)) 1) ?_
        rw [entry, keyWeight]
        nlinarith
  | (replacement, .op operator arguments) :: rest, name => by
      have entry := weight_typeMapletsP_cons replacement (.op operator arguments) rest
      rw [deriveVarType]
      erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_nil]
      refine le_trans (Nat.add_le_add_left (Nat.add_le_add_right (deriveVarType_count rest name) 0) 1) ?_
      rw [entry]
      nlinarith

theorem deriveVarType_max : ∀ (entries : List (Ty × Ty)) (name : Name),
    maxJudgment (deriveVarType calculus entries name) ≤
      weight (varTypeJ (typeMapletsP entries) (groundP (encodeName name))
        (groundP (encodeTy (SourceSubstitution.variableType entries name))))
  | [], name => by
      rw [deriveVarType]
      erw [maxJudgment_fireAt, maxJudgments_nil, Nat.max_zero]
  | (replacement, .var key) :: rest, name => by
      have entry := weight_typeMapletsP_cons replacement (.var key) rest
      have keyWeight := weight_encodeTy_var key
      rw [deriveVarType]
      split
      · erw [maxJudgment_fireAt, maxJudgments_nil, Nat.max_zero]
      · rename_i different
        have unfolded : SourceSubstitution.variableType ((replacement, .var key) :: rest) name =
            SourceSubstitution.variableType rest name := by
          rw [SourceSubstitution.variableType, if_neg different]
        erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero]
        refine max_le (le_refl _) (max_le (le_trans (deriveNeq_max_ground calculus _ _ _) ?_)
          (le_trans (deriveVarType_max rest name) ?_))
        · rw [weight_neqJ, weight_varTypeJ]
          omega
        · rw [weight_varTypeJ, weight_varTypeJ, unfolded]
          omega
  | (replacement, .op operator arguments) :: rest, name => by
      have entry := weight_typeMapletsP_cons replacement (.op operator arguments) rest
      have unfolded : SourceSubstitution.variableType ((replacement, .op operator arguments) :: rest) name =
          SourceSubstitution.variableType rest name := by
        rw [SourceSubstitution.variableType]
      rw [deriveVarType]
      erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_nil, Nat.max_zero]
      refine max_le (le_refl _) (le_trans (deriveVarType_max rest name) ?_)
      rw [weight_varTypeJ, weight_varTypeJ, unfolded]
      omega

mutual
  theorem deriveTyAct_count (entries : List (Ty × Ty)) : ∀ type : Ty,
      nodeCount (deriveTyAct calculus entries type) ≤
        weight (groundP (encodeTy type)) * (weight (typeMapletsP entries) + 2)
    | .var name => by
        rw [deriveTyAct]
        erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_nil]
        refine le_trans (Nat.add_le_add_left (Nat.add_le_add_right (deriveVarType_count calculus entries name) 0) 1) ?_
        rw [weight_encodeTy_var]
        nlinarith
    | .op operator arguments => by
        rw [deriveTyAct]
        erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_nil]
        refine le_trans (Nat.add_le_add_left (Nat.add_le_add_right (deriveTyActList_count entries arguments) 0) 1) ?_
        rw [weight_encodeTy_op]
        nlinarith

  theorem deriveTyActList_count (entries : List (Ty × Ty)) : ∀ types : List Ty,
      nodeCount (deriveTyActList calculus entries types) ≤ weight (tysP types) * (weight (typeMapletsP entries) + 2)
    | [] => by
        rw [deriveTyActList]
        erw [nodeCount_fireAt, nodeCounts_nil]
        rw [show tysP [] = nilP from rfl, weight_nilP]
        omega
    | type :: rest => by
        rw [deriveTyActList]
        erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
        refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveTyAct_count entries type)
          (Nat.add_le_add_right (deriveTyActList_count entries rest) 0)) 1) ?_
        rw [weight_tysP_cons]
        nlinarith
end

mutual
  theorem deriveTyAct_max (entries : List (Ty × Ty)) : ∀ type : Ty,
      maxJudgment (deriveTyAct calculus entries type) ≤
        weight (tyActJ (typeMapletsP entries) (groundP (encodeTy type))
          (groundP (encodeTy (SourceSubstitution.typeAction entries type))))
    | .var name => by
        rw [deriveTyAct]
        erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_nil, Nat.max_zero]
        refine max_le (le_refl _) (le_trans (deriveVarType_max calculus entries name) ?_)
        rw [weight_varTypeJ, weight_tyActJ, typeAction_var, weight_encodeTy_var]
        omega
    | .op operator arguments => by
        rw [deriveTyAct]
        erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_nil, Nat.max_zero]
        refine max_le (le_refl _) (le_trans (deriveTyActList_max entries arguments) ?_)
        rw [weight_tyActListJ, weight_tyActJ, typeAction_op, weight_encodeTy_op, weight_encodeTy_op]
        omega

  theorem deriveTyActList_max (entries : List (Ty × Ty)) : ∀ types : List Ty,
      maxJudgment (deriveTyActList calculus entries types) ≤
        weight (tyActListJ (typeMapletsP entries) (tysP types)
          (tysP (types.map (SourceSubstitution.typeAction entries))))
    | [] => by
        rw [deriveTyActList]
        erw [maxJudgment_fireAt, maxJudgments_nil, Nat.max_zero]
    | type :: rest => by
        rw [deriveTyActList]
        erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero]
        refine max_le (le_refl _) (max_le (le_trans (deriveTyAct_max entries type) ?_)
          (le_trans (deriveTyActList_max entries rest) ?_))
        · rw [weight_tyActJ, weight_tyActListJ, List.map_cons, weight_tysP_cons, weight_tysP_cons]
          omega
        · rw [weight_tyActListJ, weight_tyActListJ, List.map_cons, weight_tysP_cons, weight_tysP_cons]
          omega
end

theorem deriveTermTyAct_count (entries : List (Ty × Ty)) : ∀ term : DBTerm,
    nodeCount (deriveTermTyAct calculus entries term) ≤
      weight (groundP (encodeTerm term)) * (weight (typeMapletsP entries) + 2)
  | .const constant type => by
      rw [deriveTermTyAct]
      erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_nil]
      refine le_trans (Nat.add_le_add_left (Nat.add_le_add_right (deriveTyAct_count calculus entries type) 0) 1) ?_
      rw [weight_encodeTerm_const]
      nlinarith
  | .free sourceVar => by
      rw [deriveTermTyAct]
      erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_nil]
      refine le_trans (Nat.add_le_add_left (Nat.add_le_add_right
        (deriveTyAct_count calculus entries sourceVar.ty) 0) 1) ?_
      rw [weight_encodeTerm_free]
      nlinarith
  | .bound index => by
      rw [deriveTermTyAct]
      erw [nodeCount_fireAt, nodeCounts_nil]
      rw [weight_encodeTerm_bound]
      nlinarith
  | .app function argument => by
      rw [deriveTermTyAct]
      erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
      refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveTermTyAct_count entries function)
        (Nat.add_le_add_right (deriveTermTyAct_count entries argument) 0)) 1) ?_
      rw [weight_encodeTerm_app]
      nlinarith
  | .abs domain body => by
      rw [deriveTermTyAct]
      erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
      refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveTyAct_count calculus entries domain)
        (Nat.add_le_add_right (deriveTermTyAct_count entries body) 0)) 1) ?_
      rw [weight_encodeTerm_abs]
      nlinarith

theorem deriveTermTyAct_max (entries : List (Ty × Ty)) : ∀ term : DBTerm,
    maxJudgment (deriveTermTyAct calculus entries term) ≤
      weight (termTyActJ (typeMapletsP entries) (groundP (encodeTerm term))
        (groundP (encodeTerm (termTypeAction entries term))))
  | .const constant type => by
      rw [deriveTermTyAct]
      erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_nil, Nat.max_zero]
      refine max_le (le_refl _) (le_trans (deriveTyAct_max calculus entries type) ?_)
      simp only [termTypeAction, weight_tyActJ, weight_termTyActJ, weight_encodeTerm_const]
      omega
  | .free sourceVar => by
      rw [deriveTermTyAct]
      erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_nil, Nat.max_zero]
      refine max_le (le_refl _) (le_trans (deriveTyAct_max calculus entries sourceVar.ty) ?_)
      simp only [termTypeAction, weight_tyActJ, weight_termTyActJ, weight_encodeTerm_free]
      omega
  | .bound index => by
      rw [deriveTermTyAct]
      erw [maxJudgment_fireAt, maxJudgments_nil, Nat.max_zero]
  | .app function argument => by
      rw [deriveTermTyAct]
      erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero]
      refine max_le (le_refl _) (max_le (le_trans (deriveTermTyAct_max entries function) ?_)
        (le_trans (deriveTermTyAct_max entries argument) ?_))
      · simp only [termTypeAction, weight_termTyActJ, weight_encodeTerm_app]
        omega
      · simp only [termTypeAction, weight_termTyActJ, weight_encodeTerm_app]
        omega
  | .abs domain body => by
      rw [deriveTermTyAct]
      erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero]
      refine max_le (le_refl _) (max_le (le_trans (deriveTyAct_max calculus entries domain) ?_)
        (le_trans (deriveTermTyAct_max entries body) ?_))
      · simp only [termTypeAction, weight_tyActJ, weight_termTyActJ, weight_encodeTerm_abs]
        omega
      · simp only [termTypeAction, weight_termTyActJ, weight_encodeTerm_abs]
        omega

theorem deriveTermTyActList_count (entries : List (Ty × Ty)) : ∀ terms : List DBTerm,
    nodeCount (deriveTermTyActList calculus entries terms) ≤
      weight (termsP terms) * (weight (typeMapletsP entries) + 2)
  | [] => by
      rw [deriveTermTyActList]
      erw [nodeCount_fireAt, nodeCounts_nil]
      rw [weight_termsP_nil]
      omega
  | term :: rest => by
      rw [deriveTermTyActList]
      erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
      refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveTermTyAct_count calculus entries term)
        (Nat.add_le_add_right (deriveTermTyActList_count entries rest) 0)) 1) ?_
      rw [weight_termsP_cons]
      nlinarith

theorem deriveTermTyActList_max (entries : List (Ty × Ty)) : ∀ terms : List DBTerm,
    maxJudgment (deriveTermTyActList calculus entries terms) ≤
      weight (termTyActListJ (typeMapletsP entries) (termsP terms) (termsP (terms.map (termTypeAction entries))))
  | [] => by
      rw [deriveTermTyActList]
      erw [maxJudgment_fireAt, maxJudgments_nil, Nat.max_zero]
  | term :: rest => by
      rw [deriveTermTyActList]
      erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero]
      refine max_le (le_refl _) (max_le (le_trans (deriveTermTyAct_max calculus entries term) ?_)
        (le_trans (deriveTermTyActList_max entries rest) ?_))
      · rw [weight_termTyActJ, weight_termTyActListJ, List.map_cons, weight_termsP_cons, weight_termsP_cons]
        omega
      · rw [weight_termTyActListJ, weight_termTyActListJ, List.map_cons, weight_termsP_cons, weight_termsP_cons]
        omega

/-! ## Term instantiation -/

theorem weight_tableP_nil : weight (tableP []) = 9 := by
  rw [show tableP [] = nilP from rfl, weight_nilP]

theorem weight_tableP_cons (key : SourceVar) (replacement : CheckedSourceTerm)
    (rest : List (SourceVar × CheckedSourceTerm)) :
    weight (tableP ((key, replacement) :: rest)) =
      375 + weight (freeVarP key) + weight (groundP (encodeTerm replacement.canonical.term)) + weight (tableP rest) := by
  rw [show tableP ((key, replacement) :: rest) =
      consP (pairP (freeVarP key) (groundP (encodeTerm replacement.canonical.term))) (tableP rest) from rfl,
    weight_consP, pairP, weight_treeP_sum]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, show pairLabel = 28 from rfl]
  omega

theorem weight_termMapletsP_cons (replacement : CheckedSourceTerm) (key : SourceTerm)
    (rest : List SourceSubstitution.TermMaplet) :
    weight (termMapletsP ((replacement, key) :: rest)) =
      364 + weight (groundP (encodeSourceTerm replacement.source)) + weight (groundP (encodeSourceTerm key)) +
        weight (termMapletsP rest) := by
  rw [show termMapletsP ((replacement, key) :: rest) =
      consP (termMapletP (groundP (encodeSourceTerm replacement.source)) (groundP (encodeSourceTerm key)))
        (termMapletsP rest) from rfl, weight_consP, termMapletP, weight_treeP_sum]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, show termMapletLabel = 27 from rfl]
  omega

theorem weight_admitTmJ (maplets table : Pattern) :
    weight (admitTmJ maplets table) = 14 + weight maplets + weight table := by
  simp only [admitTmJ, weight_apply, weights_cons, weights_nil]
  rw [show "hol.AdmitTm".length = 11 from rfl]
  omega

theorem weight_tmLookupJ (table needle value : Pattern) :
    weight (tmLookupJ table needle value) = 16 + weight table + weight needle + weight value := by
  simp only [tmLookupJ, weight_apply, weights_cons, weights_nil]
  rw [show "hol.TmLookup".length = 12 from rfl]
  omega

theorem weight_tmNoKeyJ (table needle : Pattern) : weight (tmNoKeyJ table needle) = 14 + weight table + weight needle := by
  simp only [tmNoKeyJ, weight_apply, weights_cons, weights_nil]
  rw [show "hol.TmNoKey".length = 11 from rfl]
  omega

theorem weight_tmApplyJ (table term result : Pattern) :
    weight (tmApplyJ table term result) = 15 + weight table + weight term + weight result := by
  simp only [tmApplyJ, weight_apply, weights_cons, weights_nil]
  rw [show "hol.TmApply".length = 11 from rfl]
  omega

theorem weight_tmApplyListJ (table terms results : Pattern) :
    weight (tmApplyListJ table terms results) = 19 + weight table + weight terms + weight results := by
  simp only [tmApplyListJ, weight_apply, weights_cons, weights_nil]
  rw [show "hol.TmApplyList".length = 15 from rfl]
  omega

theorem tableAction_const (entries : List (SourceVar × CheckedSourceTerm)) (constant : Const) (type : Ty) :
    tableAction entries (.const constant type) = .const constant type := by
  simp only [tableAction, TermSubst.applyDB_const, TypeSubst.apply_empty]

theorem tableAction_bound (entries : List (SourceVar × CheckedSourceTerm)) (index : Nat) :
    tableAction entries (.bound index) = .bound index := by
  simp only [tableAction, TermSubst.applyDB_bound]

theorem tableAction_app (entries : List (SourceVar × CheckedSourceTerm)) (function argument : DBTerm) :
    tableAction entries (.app function argument) =
      .app (tableAction entries function) (tableAction entries argument) := by
  simp only [tableAction, TermSubst.applyDB_app]

theorem tableAction_abs (entries : List (SourceVar × CheckedSourceTerm)) (domain : Ty) (body : DBTerm) :
    tableAction entries (.abs domain body) = .abs domain (tableAction entries body) := by
  simp only [tableAction, TermSubst.applyDB_abs, TypeSubst.apply_empty]

/-- **A looked-up replacement is part of the table.** -/
theorem weight_lookup_le : ∀ {entries : List (SourceVar × CheckedSourceTerm)} {needle : SourceVar}
    {replacement : CheckedSourceTerm}, TermSubst.lookup ⟨TypeSubst.empty, entries⟩ needle = some replacement →
    weight (groundP (encodeTerm replacement.canonical.term)) ≤ weight (tableP entries)
  | [], _, _, found => absurd found (by simp [TermSubst.lookup])
  | (key, value) :: rest, needle, replacement, found => by
      have entry := weight_tableP_cons key value rest
      by_cases same : key = needle
      · subst same
        rw [lookup_cons_same] at found
        obtain rfl := Option.some.inj found
        omega
      · rw [lookup_cons_other same] at found
        have := weight_lookup_le found
        omega

/-- **Term instantiation multiplies a term's weight by at most the table's.** -/
theorem weight_tableAction (entries : List (SourceVar × CheckedSourceTerm)) : ∀ term : DBTerm,
    weight (groundP (encodeTerm (tableAction entries term))) ≤
      weight (groundP (encodeTerm term)) * (weight (tableP entries) + 1)
  | .const constant type => by
      rw [tableAction_const]
      nlinarith [Nat.zero_le (weight (groundP (encodeTerm (.const constant type))) * weight (tableP entries))]
  | .free sourceVar => by
      have positive := weight_encodeTerm_ge (.free sourceVar)
      have scaled := Nat.mul_le_mul_right (weight (tableP entries)) positive
      cases found : TermSubst.lookup ⟨TypeSubst.empty, entries⟩ sourceVar with
      | some replacement =>
          rw [tableAction_free_of_lookup_some found]
          have := weight_lookup_le found
          nlinarith
      | none =>
          rw [tableAction_free_of_lookup_none found]
          nlinarith
  | .bound index => by
      rw [tableAction_bound]
      nlinarith [Nat.zero_le (weight (groundP (encodeTerm (.bound index))) * weight (tableP entries))]
  | .app function argument => by
      have first := weight_tableAction entries function
      have second := weight_tableAction entries argument
      rw [tableAction_app, weight_encodeTerm_app, weight_encodeTerm_app]
      nlinarith
  | .abs domain body => by
      have inner := weight_tableAction entries body
      rw [tableAction_abs, weight_encodeTerm_abs, weight_encodeTerm_abs]
      nlinarith

theorem weight_tableActionList (entries : List (SourceVar × CheckedSourceTerm)) : ∀ terms : List DBTerm,
    weight (termsP (terms.map (tableAction entries))) ≤ weight (termsP terms) * (weight (tableP entries) + 1)
  | [] => by
      rw [List.map_nil, weight_termsP_nil]
      omega
  | term :: rest => by
      have first := weight_tableAction entries term
      have second := weight_tableActionList entries rest
      rw [List.map_cons, weight_termsP_cons, weight_termsP_cons]
      nlinarith

/-- **The table of admitted maplets is at most quadratic in the maplets.** -/
theorem weight_tableP_termEntries : ∀ maplets : List SourceSubstitution.TermMaplet,
    weight (tableP (SourceSubstitution.termEntries maplets)) ≤
      weight (termMapletsP maplets) * (2 * weight (termMapletsP maplets) + 12)
  | [] => by
      rw [show SourceSubstitution.termEntries [] = [] from rfl, weight_tableP_nil,
        show termMapletsP [] = nilP from rfl, weight_nilP]
      omega
  | (replacement, .var name type) :: rest => by
      have restBound := weight_tableP_termEntries rest
      have converted := weight_toDB [] replacement.source
      rw [weight_bindersP_nil] at converted
      have canonicalEq : replacement.canonical.term = replacement.source.toDB [] := rfl
      rw [show SourceSubstitution.termEntries ((replacement, .var name type) :: rest) =
          (⟨name, type⟩, replacement) :: SourceSubstitution.termEntries rest from rfl,
        weight_tableP_cons, weight_termMapletsP_cons, weight_sourceVar, weight_freeVarP, canonicalEq]
      nlinarith
  | (replacement, .const constant type) :: rest => by
      have restBound := weight_tableP_termEntries rest
      rw [show SourceSubstitution.termEntries ((replacement, .const constant type) :: rest) =
          SourceSubstitution.termEntries rest from rfl, weight_termMapletsP_cons]
      nlinarith
  | (replacement, .app function argument) :: rest => by
      have restBound := weight_tableP_termEntries rest
      rw [show SourceSubstitution.termEntries ((replacement, .app function argument) :: rest) =
          SourceSubstitution.termEntries rest from rfl, weight_termMapletsP_cons]
      nlinarith
  | (replacement, .abs name type body) :: rest => by
      have restBound := weight_tableP_termEntries rest
      rw [show SourceSubstitution.termEntries ((replacement, .abs name type body) :: rest) =
          SourceSubstitution.termEntries rest from rfl, weight_termMapletsP_cons]
      nlinarith

theorem deriveLookup_count (needle : SourceVar) (replacement : CheckedSourceTerm) :
    ∀ (entries : List (SourceVar × CheckedSourceTerm))
      (found : TermSubst.lookup ⟨TypeSubst.empty, entries⟩ needle = some replacement),
      nodeCount (deriveLookup calculus needle replacement entries found) ≤
        weight (tableP entries) * (weight (freeVarP needle) + 2)
  | (key, value) :: rest, found => by
      have entry := weight_tableP_cons key value rest
      rw [deriveLookup]
      split
      · erw [nodeCount_fireAt, nodeCounts_nil]
        rw [entry]
        nlinarith
      · erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
        refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveNeq_count calculus _ _ _)
          (Nat.add_le_add_right (deriveLookup_count needle replacement rest _) 0)) 1) ?_
        show 1 + (1 + weight (freeVarP needle) + weight (freeVarP key) + _) ≤ _
        rw [entry]
        nlinarith
  | [], found => absurd found (by simp [TermSubst.lookup])

theorem deriveLookup_max (needle : SourceVar) (replacement : CheckedSourceTerm) :
    ∀ (entries : List (SourceVar × CheckedSourceTerm))
      (found : TermSubst.lookup ⟨TypeSubst.empty, entries⟩ needle = some replacement),
      maxJudgment (deriveLookup calculus needle replacement entries found) ≤
        weight (tmLookupJ (tableP entries) (freeVarP needle) (groundP (encodeTerm replacement.canonical.term)))
  | (key, value) :: rest, found => by
      have entry := weight_tableP_cons key value rest
      rw [deriveLookup]
      split
      · erw [maxJudgment_fireAt, maxJudgments_nil, Nat.max_zero]
      · erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero,
          deriveNeq_max]
        refine max_le (le_refl _) (max_le ?_ (le_trans (deriveLookup_max needle replacement rest _) ?_))
        · show weight (neqJ (freeVarP needle) (freeVarP key)) ≤ _
          rw [weight_neqJ, weight_tmLookupJ]
          omega
        · rw [weight_tmLookupJ, weight_tmLookupJ]
          omega
  | [], found => absurd found (by simp [TermSubst.lookup])

theorem deriveNoKey_count (needle : SourceVar) : ∀ (entries : List (SourceVar × CheckedSourceTerm))
    (missing : TermSubst.lookup ⟨TypeSubst.empty, entries⟩ needle = none),
    nodeCount (deriveNoKey calculus needle entries missing) ≤ weight (tableP entries) * (weight (freeVarP needle) + 2)
  | [], _ => by
      rw [deriveNoKey]
      erw [nodeCount_fireAt, nodeCounts_nil]
      rw [weight_tableP_nil]
      omega
  | (key, value) :: rest, missing => by
      have entry := weight_tableP_cons key value rest
      rw [deriveNoKey]
      erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
      refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveNeq_count calculus _ _ _)
        (Nat.add_le_add_right (deriveNoKey_count needle rest _) 0)) 1) ?_
      show 1 + (1 + weight (freeVarP needle) + weight (freeVarP key) + _) ≤ _
      rw [entry]
      nlinarith

theorem deriveNoKey_max (needle : SourceVar) : ∀ (entries : List (SourceVar × CheckedSourceTerm))
    (missing : TermSubst.lookup ⟨TypeSubst.empty, entries⟩ needle = none),
    maxJudgment (deriveNoKey calculus needle entries missing) ≤ weight (tmNoKeyJ (tableP entries) (freeVarP needle))
  | [], _ => by
      rw [deriveNoKey]
      erw [maxJudgment_fireAt, maxJudgments_nil, Nat.max_zero]
  | (key, value) :: rest, missing => by
      have entry := weight_tableP_cons key value rest
      rw [deriveNoKey]
      erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero, deriveNeq_max]
      refine max_le (le_refl _) (max_le ?_ (le_trans (deriveNoKey_max needle rest _) ?_))
      · show weight (neqJ (freeVarP needle) (freeVarP key)) ≤ _
        rw [weight_neqJ, weight_tmNoKeyJ]
        omega
      · rw [weight_tmNoKeyJ, weight_tmNoKeyJ]
        omega

theorem deriveTmApply_count (entries : List (SourceVar × CheckedSourceTerm)) : ∀ term : DBTerm,
    nodeCount (deriveTmApply calculus entries term) ≤
      weight (groundP (encodeTerm term)) * (2 * weight (tableP entries) + 2)
  | .const constant type => by
      rw [deriveTmApply]
      erw [nodeCount_fireAt, nodeCounts_nil]
      rw [weight_encodeTerm_const]
      nlinarith
  | .free sourceVar => by
      have positive := weight_encodeTerm_ge (.free sourceVar)
      have scaled := Nat.mul_le_mul_left (weight (tableP entries)) positive
      rw [deriveTmApply]
      split
      · erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_nil]
        refine le_trans (Nat.add_le_add_left (Nat.add_le_add_right (deriveLookup_count calculus _ _ _ _) 0) 1) ?_
        simp only [freeVarP]
        nlinarith
      · erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_nil]
        refine le_trans (Nat.add_le_add_left (Nat.add_le_add_right (deriveNoKey_count calculus _ _ _) 0) 1) ?_
        simp only [freeVarP]
        nlinarith
  | .bound index => by
      rw [deriveTmApply]
      erw [nodeCount_fireAt, nodeCounts_nil]
      rw [weight_encodeTerm_bound]
      nlinarith
  | .app function argument => by
      rw [deriveTmApply]
      erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
      refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveTmApply_count entries function)
        (Nat.add_le_add_right (deriveTmApply_count entries argument) 0)) 1) ?_
      rw [weight_encodeTerm_app]
      nlinarith
  | .abs domain body => by
      rw [deriveTmApply]
      erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_nil]
      refine le_trans (Nat.add_le_add_left (Nat.add_le_add_right (deriveTmApply_count entries body) 0) 1) ?_
      rw [weight_encodeTerm_abs]
      nlinarith

theorem deriveTmApply_max (entries : List (SourceVar × CheckedSourceTerm)) : ∀ term : DBTerm,
    maxJudgment (deriveTmApply calculus entries term) ≤
      weight (tmApplyJ (tableP entries) (groundP (encodeTerm term)) (groundP (encodeTerm (tableAction entries term)))) + 1
  | .const constant type => by
      rw [deriveTmApply]
      erw [maxJudgment_fireAt, maxJudgments_nil, Nat.max_zero]
      omega
  | .free sourceVar => by
      rw [deriveTmApply]
      split
      · rename_i replacement found
        erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_nil, Nat.max_zero]
        refine max_le (by omega) (le_trans (deriveLookup_max calculus _ _ _ _) ?_)
        rw [weight_tmLookupJ, weight_tmApplyJ, tableAction_free_of_lookup_some found]
        simp only [freeVarP]
        omega
      · rename_i found
        erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_nil, Nat.max_zero]
        refine max_le (by omega) (le_trans (deriveNoKey_max calculus _ _ _) ?_)
        rw [weight_tmNoKeyJ, weight_tmApplyJ]
        simp only [freeVarP]
        omega
  | .bound index => by
      rw [deriveTmApply]
      erw [maxJudgment_fireAt, maxJudgments_nil, Nat.max_zero]
      omega
  | .app function argument => by
      rw [deriveTmApply]
      erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero]
      refine max_le (by omega) (max_le (le_trans (deriveTmApply_max entries function) ?_)
        (le_trans (deriveTmApply_max entries argument) ?_))
      · rw [weight_tmApplyJ, weight_tmApplyJ, tableAction_app, weight_encodeTerm_app, weight_encodeTerm_app]
        omega
      · rw [weight_tmApplyJ, weight_tmApplyJ, tableAction_app, weight_encodeTerm_app, weight_encodeTerm_app]
        omega
  | .abs domain body => by
      rw [deriveTmApply]
      erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_nil, Nat.max_zero]
      refine max_le (by omega) (le_trans (deriveTmApply_max entries body) ?_)
      rw [weight_tmApplyJ, weight_tmApplyJ, tableAction_abs, weight_encodeTerm_abs, weight_encodeTerm_abs]
      omega

theorem deriveTmApplyList_count (entries : List (SourceVar × CheckedSourceTerm)) : ∀ terms : List DBTerm,
    nodeCount (deriveTmApplyList calculus entries terms) ≤ weight (termsP terms) * (2 * weight (tableP entries) + 2)
  | [] => by
      rw [deriveTmApplyList]
      erw [nodeCount_fireAt, nodeCounts_nil]
      rw [weight_termsP_nil]
      omega
  | term :: rest => by
      rw [deriveTmApplyList]
      erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
      refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveTmApply_count calculus entries term)
        (Nat.add_le_add_right (deriveTmApplyList_count entries rest) 0)) 1) ?_
      rw [weight_termsP_cons]
      nlinarith

theorem deriveTmApplyList_max (entries : List (SourceVar × CheckedSourceTerm)) : ∀ terms : List DBTerm,
    maxJudgment (deriveTmApplyList calculus entries terms) ≤
      weight (tmApplyListJ (tableP entries) (termsP terms) (termsP (terms.map (tableAction entries))))
  | [] => by
      rw [deriveTmApplyList]
      erw [maxJudgment_fireAt, maxJudgments_nil, Nat.max_zero]
  | term :: rest => by
      rw [deriveTmApplyList]
      erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_cons, maxJudgments_nil, Nat.max_zero]
      refine max_le (le_refl _) (max_le (le_trans (deriveTmApply_max calculus entries term) ?_)
        (le_trans (deriveTmApplyList_max entries rest) ?_))
      · rw [weight_tmApplyJ, weight_tmApplyListJ, List.map_cons, weight_termsP_cons, weight_termsP_cons]
        omega
      · rw [weight_tmApplyListJ, weight_tmApplyListJ, List.map_cons, weight_termsP_cons, weight_termsP_cons]
        omega

/-- The judgments one admitted maplet writes, given a bound on the maplets' weight. -/
def admitCost (bound : ℕ) : ℕ :=
  1 + bound + 2 * (bound + 1) * (9 + 2 * bound + 2) +
    ((9 + 2 * bound + 2) * bound + 1) * (9 + (9 + 2 * bound + 2) * bound + 1)

theorem admitCost_mono {small large : ℕ} (le : small ≤ large) : admitCost small ≤ admitCost large := by
  unfold admitCost
  gcongr

/-- The heaviest judgment one admitted maplet writes, given a bound on the maplets' weight. -/
def admitMax (bound : ℕ) : ℕ := 800 + bound + 4 * (9 + 2 * bound + 2) ^ 2 + 40 * ((9 + 2 * bound + 2) * bound)

theorem admitMax_mono {small large : ℕ} (le : small ≤ large) : admitMax small ≤ admitMax large := by
  unfold admitMax
  gcongr

theorem deriveAdmit_count : ∀ (maplets : List SourceSubstitution.TermMaplet)
    (admissible : SourceSubstitution.TermMapletsAdmissible maplets),
    nodeCount (deriveAdmit calculus maplets admissible) ≤
      weight (termMapletsP maplets) * admitCost (weight (termMapletsP maplets))
  | [], _ => by
      rw [deriveAdmit]
      erw [nodeCount_fireAt, nodeCounts_nil]
      rw [show termMapletsP [] = nilP from rfl, weight_nilP]
      norm_num [admitCost]
  | (replacement, .var name type) :: rest, admissible => by
      have entry := weight_termMapletsP_cons replacement (.var name type) rest
      have keyWeight := weight_sourceVar name type
      have converted := weight_toDB [] replacement.source
      rw [weight_bindersP_nil] at converted
      have restMono : weight (termMapletsP rest) * admitCost (weight (termMapletsP rest)) ≤
          weight (termMapletsP rest) * admitCost (weight (termMapletsP ((replacement, .var name type) :: rest))) :=
        Nat.mul_le_mul_left _ (admitCost_mono (by omega))
      have total : (1 + weight (termMapletsP rest)) *
            admitCost (weight (termMapletsP ((replacement, .var name type) :: rest))) ≤
          weight (termMapletsP ((replacement, .var name type) :: rest)) *
            admitCost (weight (termMapletsP ((replacement, .var name type) :: rest))) :=
        Nat.mul_le_mul_right _ (by omega)
      have perMaplet : 1 + weight (groundP (encodeName name)) +
          2 * (weight (groundP (encodeSourceTerm replacement.source)) + 1) *
            (9 + 2 * weight (groundP (encodeSourceTerm replacement.source)) + 2) +
          (weight (groundP (encodeTerm (replacement.source.toDB []))) + 1) *
            (9 + weight (groundP (encodeTerm (replacement.source.toDB []))) + 1) ≤
          admitCost (weight (termMapletsP ((replacement, .var name type) :: rest))) := by
        have sourceLe : weight (groundP (encodeSourceTerm replacement.source)) ≤
            weight (termMapletsP ((replacement, .var name type) :: rest)) := by omega
        have nameLe : weight (groundP (encodeName name)) ≤
            weight (termMapletsP ((replacement, .var name type) :: rest)) := by omega
        have convertedLe : weight (groundP (encodeTerm (replacement.source.toDB []))) ≤
            (9 + 2 * weight (termMapletsP ((replacement, .var name type) :: rest)) + 2) *
              weight (termMapletsP ((replacement, .var name type) :: rest)) :=
          le_trans converted (by gcongr)
        unfold admitCost
        gcongr
      rw [deriveAdmit]
      erw [nodeCount_fireAt, nodeCounts_cons, nodeCounts_cons, nodeCounts_cons, nodeCounts_cons, nodeCounts_nil]
      refine le_trans (Nat.add_le_add_left (Nat.add_le_add (deriveName_count calculus name)
        (Nat.add_le_add (deriveToDB_count calculus [] replacement.source)
          (Nat.add_le_add (deriveTypeOf_count calculus [] _ type _)
            (Nat.add_le_add_right (deriveAdmit_count rest _) 0)))) 1) ?_
      rw [weight_bindersP_nil, weight_contextP_nil]
      nlinarith
  | (_, .const _ _) :: _, admissible => absurd (admissible _ (List.mem_cons.mpr (Or.inl rfl))) id
  | (_, .app _ _) :: _, admissible => absurd (admissible _ (List.mem_cons.mpr (Or.inl rfl))) id
  | (_, .abs _ _ _) :: _, admissible => absurd (admissible _ (List.mem_cons.mpr (Or.inl rfl))) id

theorem deriveAdmit_max : ∀ (maplets : List SourceSubstitution.TermMaplet)
    (admissible : SourceSubstitution.TermMapletsAdmissible maplets),
    maxJudgment (deriveAdmit calculus maplets admissible) ≤
      weight (admitTmJ (termMapletsP maplets) (tableP (SourceSubstitution.termEntries maplets))) +
        admitMax (weight (termMapletsP maplets))
  | [], _ => by
      rw [deriveAdmit]
      erw [maxJudgment_fireAt, maxJudgments_nil, Nat.max_zero]
      exact Nat.le_add_right _ _
  | (replacement, .var name type) :: rest, admissible => by
      have entry := weight_termMapletsP_cons replacement (.var name type) rest
      have keyWeight := weight_sourceVar name type
      have converted := weight_toDB [] replacement.source
      rw [weight_bindersP_nil] at converted
      have entries : SourceSubstitution.termEntries ((replacement, .var name type) :: rest) =
          (⟨name, type⟩, replacement) :: SourceSubstitution.termEntries rest := rfl
      have table := weight_tableP_cons ⟨name, type⟩ replacement (SourceSubstitution.termEntries rest)
      have sourceLe : weight (groundP (encodeSourceTerm replacement.source)) ≤
          weight (termMapletsP ((replacement, .var name type) :: rest)) := by omega
      have restLe : weight (termMapletsP rest) ≤ weight (termMapletsP ((replacement, .var name type) :: rest)) := by
        omega
      have bigger := admitMax_mono restLe
      have toDBLe : 4 * (9 + 2 * weight (groundP (encodeSourceTerm replacement.source)) + 2) ^ 2 ≤
          4 * (9 + 2 * weight (termMapletsP ((replacement, .var name type) :: rest)) + 2) ^ 2 := by
        gcongr
      have typeLe : weight (groundP (encodeTerm (replacement.source.toDB []))) ≤
          (9 + 2 * weight (termMapletsP ((replacement, .var name type) :: rest)) + 2) *
            weight (termMapletsP ((replacement, .var name type) :: rest)) :=
        le_trans converted (by gcongr)
      rw [deriveAdmit]
      erw [maxJudgment_fireAt, maxJudgments_cons, maxJudgments_cons, maxJudgments_cons, maxJudgments_cons,
        maxJudgments_nil, Nat.max_zero, deriveName_max]
      refine max_le (Nat.le_add_right _ _) (max_le ?_ (max_le (le_trans (deriveToDB_max calculus [] replacement.source) ?_)
        (max_le (le_trans (deriveTypeOf_max calculus [] _ type _) ?_) (le_trans (deriveAdmit_max rest _) ?_))))
      · rw [weight_wfJ, show "Name".length = 4 from rfl]
        unfold admitMax
        omega
      · rw [weight_bindersP_nil]
        unfold admitMax
        omega
      · rw [weight_contextP_nil]
        unfold admitMax
        omega
      · rw [weight_admitTmJ, weight_admitTmJ, entries, table]
        omega
  | (_, .const _ _) :: _, admissible => absurd (admissible _ (List.mem_cons.mpr (Or.inl rfl))) id
  | (_, .app _ _) :: _, admissible => absurd (admissible _ (List.mem_cons.mpr (Or.inl rfl))) id
  | (_, .abs _ _ _) :: _, admissible => absurd (admissible _ (List.mem_cons.mpr (Or.inl rfl))) id

end Calculus

end Mettapedia.Languages.HOLLight.FirstOrder
