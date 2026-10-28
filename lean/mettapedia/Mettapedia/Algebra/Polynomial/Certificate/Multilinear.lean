import Mathlib

/-!
Kernel-checked semantics for the exact multilinear case-split engine.

A search engine is only a trace finder.  Its four combinatorial moves are
proved sound here over characteristic-zero fields.  A separate finite-DAG
checker can therefore replay large memoized traces without trusting Python or
the search strategy.
-/

namespace Mettapedia.Algebra.Polynomial.Certificate.Multilinear

/-- One multilinear monomial with an integer coefficient. -/
structure Term where
  coefficient : ℤ
  support : Finset Nat
deriving DecidableEq

/-- Sparse multilinear polynomials.  The trace format keeps terms canonical,
but the semantic layer does not rely on ordering or absence of duplicates. -/
abbrev Poly := List Term

namespace Term

/-- Evaluate the coefficient times the product of the supported variables. -/
def eval {R : Type*} [CommRing R] (term : Term) (values : Nat → R) : R :=
  (term.coefficient : R) * term.support.prod values

/-- Remove a variable from a monomial's support, retaining its coefficient. -/
def eraseVariable (term : Term) (index : Nat) : Term :=
  { term with support := term.support.erase index }

/-- A monomial vanishes if its support meets a set of zero-valued variables. -/
theorem eval_eq_zero_of_not_disjoint
    {R : Type*} [CommRing R] (term : Term) (values : Nat → R)
    (zero : Finset Nat) (zeroValues : ∀ index ∈ zero, values index = 0)
    (overlap : ¬ Disjoint term.support zero) : term.eval values = 0 := by
  obtain ⟨index, inTerm, inZero⟩ := Finset.not_disjoint_iff.mp overlap
  simp [eval, Finset.prod_eq_zero inTerm (zeroValues index inZero)]

/-- An occurring variable factors out of a multilinear monomial. -/
theorem eval_eq_value_mul_eraseVariable
    {R : Type*} [CommRing R] (term : Term) (values : Nat → R)
    {index : Nat} (present : index ∈ term.support) :
    term.eval values = values index * (term.eraseVariable index).eval values := by
  simp only [eval, eraseVariable]
  rw [← Finset.mul_prod_erase term.support values present]
  ring

end Term

namespace Poly

/-- Evaluate a sparse polynomial by summing its monomial values. -/
def eval {R : Type*} [CommRing R] (polynomial : Poly) (values : Nat → R) : R :=
  (polynomial.map fun term => term.eval values).sum

/-- Substitute zero for all variables in `zero`.  Since the representation is
multilinear, this simply removes every term meeting the zero set. -/
def reduce (polynomial : Poly) (zero : Finset Nat) : Poly :=
  polynomial.filter fun term => Disjoint term.support zero

/-- Remove a variable from every monomial's support. -/
def eraseVariable (polynomial : Poly) (index : Nat) : Poly :=
  polynomial.map fun term => term.eraseVariable index

/-- Removing monomials killed by known zero coordinates preserves evaluation. -/
theorem eval_reduce
    {R : Type*} [CommRing R] (polynomial : Poly) (values : Nat → R)
    (zero : Finset Nat) (zeroValues : ∀ index ∈ zero, values index = 0) :
    (polynomial.reduce zero).eval values = polynomial.eval values := by
  induction polynomial with
  | nil => simp [eval, reduce]
  | cons term tail inductionHypothesis =>
      by_cases survives : Disjoint term.support zero
      · simpa [eval, reduce, survives] using
          congrArg (fun result => term.eval values + result) inductionHypothesis
      · have termZero := term.eval_eq_zero_of_not_disjoint values zero zeroValues survives
        simpa [eval, reduce, survives, termZero] using inductionHypothesis

/-- A variable occurring in every monomial factors out of the polynomial. -/
theorem eval_eq_value_mul_eraseVariable
    {R : Type*} [CommRing R] (polynomial : Poly) (values : Nat → R)
    (index : Nat) (present : ∀ term ∈ polynomial, index ∈ term.support) :
    polynomial.eval values = values index * (polynomial.eraseVariable index).eval values := by
  induction polynomial with
  | nil => simp [eval, eraseVariable]
  | cons term tail inductionHypothesis =>
      have termPresent : index ∈ term.support := present term (by simp)
      have tailPresent : ∀ item ∈ tail, index ∈ item.support := by
        intro item inTail
        exact present item (by simp [inTail])
      change term.eval values + Poly.eval tail values =
        values index * ((term.eraseVariable index).eval values +
          Poly.eval (Poly.eraseVariable tail index) values)
      rw [term.eval_eq_value_mul_eraseVariable values termPresent,
        inductionHypothesis tailPresent]
      ring

end Poly

/-- A point satisfies a trace state when all active polynomials and all
recorded zero coordinates vanish. -/
def satisfies {R : Type*} [CommRing R]
    (active : List Poly) (zero : Finset Nat) (values : Nat → R) : Prop :=
  (∀ polynomial ∈ active, polynomial.eval values = 0) ∧
    ∀ index ∈ zero, values index = 0

/-- No assignment satisfies the active equations and recorded zero coordinates. -/
def closed {R : Type*} [CommRing R] (active : List Poly) (zero : Finset Nat) : Prop :=
  ∀ values : Nat → R, ¬ satisfies active zero values

/-- An active equation remains zero after reduction by known zero coordinates. -/
theorem reduced_source_zero
    {R : Type*} [CommRing R] {active : List Poly} {zero : Finset Nat}
    {values : Nat → R} (state : satisfies active zero values)
    {source : Poly} (sourceActive : source ∈ active) :
    (source.reduce zero).eval values = 0 := by
  rw [source.eval_reduce values zero state.2]
  exact state.1 source sourceActive

/-- A nonzero constant among the reduced active equations closes a state. -/
theorem contradiction_sound
    {R : Type*} [Field R] [CharZero R]
    {active : List Poly} {zero : Finset Nat} {source : Poly} {coefficient : ℤ}
    (sourceActive : source ∈ active)
    (reduced : source.reduce zero = [{ coefficient := coefficient, support := ∅ }])
    (coefficientNonzero : coefficient ≠ 0) : closed (R := R) active zero := by
  intro values state
  have sourceZero := reduced_source_zero state sourceActive
  rw [reduced] at sourceZero
  simp [Poly.eval, Term.eval, coefficientNonzero] at sourceZero

/-- Unit-monomial equations justify adding all their variables to the known
zero set.  The child may combine several forced coordinates in one step. -/
theorem forced_sound
    {R : Type*} [Field R] [CharZero R]
    {active : List Poly} {zero forced : Finset Nat}
    (witness : ∀ index ∈ forced, ∃ source ∈ active, ∃ coefficient : ℤ,
      coefficient ≠ 0 ∧
        source.reduce zero = [{ coefficient := coefficient, support := {index} }])
    (childClosed : closed (R := R) active (zero ∪ forced)) :
    closed (R := R) active zero := by
  intro values state
  apply childClosed values
  refine ⟨state.1, ?_⟩
  intro index inUnion
  rcases Finset.mem_union.mp inUnion with inZero | inForced
  · exact state.2 index inZero
  · obtain ⟨source, sourceActive, coefficient, coefficientNonzero, reduced⟩ :=
      witness index inForced
    have sourceZero := reduced_source_zero state sourceActive
    rw [reduced] at sourceZero
    simpa [Poly.eval, Term.eval, coefficientNonzero] using sourceZero

/-- A pure monomial equation closes a state when every coordinate-zero branch
is closed. -/
theorem pure_sound
    {R : Type*} [Field R] [CharZero R]
    {active : List Poly} {zero support : Finset Nat}
    {source : Poly} {coefficient : ℤ}
    (sourceActive : source ∈ active)
    (reduced : source.reduce zero = [{ coefficient := coefficient, support := support }])
    (coefficientNonzero : coefficient ≠ 0)
    (childrenClosed : ∀ index ∈ support, closed (R := R) active (insert index zero)) :
    closed (R := R) active zero := by
  intro values state
  have sourceZero := reduced_source_zero state sourceActive
  rw [reduced] at sourceZero
  have productZero : ∏ index ∈ support, values index = 0 := by
    simpa [Poly.eval, Term.eval, coefficientNonzero] using sourceZero
  obtain ⟨index, inSupport, indexZero⟩ := Finset.prod_eq_zero_iff.mp productZero
  apply childrenClosed index inSupport values
  refine ⟨state.1, ?_⟩
  intro item inInsert
  rcases Finset.mem_insert.mp inInsert with rfl | inZero
  · exact indexZero
  · exact state.2 item inZero

/-- If a reduced equation is `variable * quotient`, the two exhaustive
branches are `variable = 0` and `quotient = 0`. -/
theorem factor_sound
    {R : Type*} [Field R] [CharZero R]
    {active : List Poly} {zero : Finset Nat} {pivot : Nat}
    {source quotient reducedSource : Poly}
    (sourceActive : source ∈ active)
    (reduced : source.reduce zero = reducedSource)
    (present : ∀ term ∈ reducedSource, pivot ∈ term.support)
    (quotientDefinition : reducedSource.eraseVariable pivot = quotient)
    (zeroChildClosed : closed (R := R) active (insert pivot zero))
    (quotientChildClosed : closed (R := R) (quotient :: active) zero) :
    closed (R := R) active zero := by
  intro values state
  have sourceZero := reduced_source_zero state sourceActive
  rw [reduced, reducedSource.eval_eq_value_mul_eraseVariable values pivot present,
    quotientDefinition] at sourceZero
  rcases mul_eq_zero.mp sourceZero with pivotZero | quotientZero
  · apply zeroChildClosed values
    refine ⟨state.1, ?_⟩
    intro item inInsert
    rcases Finset.mem_insert.mp inInsert with rfl | inZero
    · exact pivotZero
    · exact state.2 item inZero
  · apply quotientChildClosed values
    refine ⟨?_, state.2⟩
    ·
      intro polynomial inActive
      simp only [List.mem_cons] at inActive
      rcases inActive with rfl | inParent
      · exact quotientZero
      · exact state.1 polynomial inParent

/-! ## Finite postorder proof DAGs -/

/-- A trace state records zero coordinates and IDs of additional equations. -/
structure State where
  zero : List Nat
  extras : List Nat
deriving DecidableEq

namespace State

/-- Canonical insertion used by trace states.  Exact list equality makes the
kernel checker cheap; semantics below use membership only. -/
def insertSorted (index : Nat) : List Nat → List Nat
  | [] => [index]
  | head :: tail =>
      if index = head then head :: tail
      else if index < head then index :: head :: tail
      else head :: insertSorted index tail

/-- Sorted insertion adds the selected element and preserves all prior members. -/
theorem mem_insertSorted {item index : Nat} {items : List Nat} :
    item ∈ insertSorted index items ↔ item = index ∨ item ∈ items := by
  induction items with
  | nil => simp [insertSorted]
  | cons head tail ih =>
      simp only [insertSorted]
      split <;> rename_i equality
      · subst index
        simp
      · split <;> simp [ih, or_left_comm]

/-- Insert a list of coordinates using canonical single-coordinate insertion. -/
def insertMany : List Nat → List Nat → List Nat
  | [], zero => zero
  | index :: indices, zero => insertMany indices (insertSorted index zero)

/-- Multiple insertion has exactly the union of the two input memberships. -/
theorem mem_insertMany {item : Nat} {indices zero : List Nat} :
    item ∈ insertMany indices zero ↔ item ∈ zero ∨ item ∈ indices := by
  induction indices generalizing zero with
  | nil => simp [insertMany]
  | cons head tail ih =>
      rw [insertMany, ih, mem_insertSorted]
      simp [or_assoc, or_left_comm]

/-- Record one more coordinate as zero. -/
def addZero (state : State) (index : Nat) : State :=
  { state with zero := insertSorted index state.zero }

/-- Record a list of coordinates as zero. -/
def addZeros (state : State) (indices : List Nat) : State :=
  { state with zero := insertMany indices state.zero }

/-- Activate an additional equation by its polynomial ID. -/
def addExtra (state : State) (index : Nat) : State :=
  { state with extras := insertSorted index state.extras }

end State

/-- Refutation rules: constant contradiction, forced zeros, monomial split or factor split. -/
inductive Rule where
  | contradiction (source : Nat)
  | forced (sources : List (Nat × Nat)) (child : Nat)
  | pure (source : Nat) (children : List (Nat × Nat))
  | factor (source quotient pivot zeroChild quotientChild : Nat)
deriving DecidableEq

/-- One refutation step together with the state it refutes. -/
structure Node where
  state : State
  rule : Rule
deriving DecidableEq

/-- A finite polynomial pool and postorder refutation DAG with a designated root. -/
structure Trace where
  baseCount : Nat
  polynomials : Array Poly
  nodes : Array Node
  root : Nat
deriving DecidableEq

namespace Trace

/-- A source is a base equation or an equation activated by the current state. -/
def sourceActive (certificate : Trace) (state : State) (source : Nat) : Prop :=
  source < certificate.baseCount ∨ source ∈ state.extras

/-- A child exists earlier in the DAG and carries exactly the expected state. -/
def childStateAt (certificate : Trace) (position child : Nat) (expected : State) : Prop :=
  child < position ∧ match certificate.nodes[child]? with
    | some node => node.state = expected
    | none => False

/-- An active, resolved source reduces to a nonzero constant. -/
def contradictionSource (certificate : Trace) (state : State) (source : Nat) : Prop :=
  certificate.sourceActive state source ∧ match certificate.polynomials[source]? with
    | some polynomial => match polynomial.reduce state.zero.toFinset with
      | [term] => term.support = ∅ ∧ term.coefficient ≠ 0
      | _ => False
    | none => False

/-- An active, resolved source forces one coordinate to zero. -/
def forcedSource (certificate : Trace) (state : State) (index source : Nat) : Prop :=
  certificate.sourceActive state source ∧ match certificate.polynomials[source]? with
    | some polynomial => match polynomial.reduce state.zero.toFinset with
      | [term] => term.support = {index} ∧ term.coefficient ≠ 0
      | _ => False
    | none => False

/-- Local validity of a rule, including its source IDs and earlier child edges. -/
def validRule (certificate : Trace) (position : Nat) (state : State) : Rule → Prop
  | .contradiction source =>
      certificate.contradictionSource state source
  | .forced sources child =>
      certificate.childStateAt position child
        (state.addZeros (sources.map Prod.fst)) ∧
      ∀ entry ∈ sources, certificate.forcedSource state entry.1 entry.2
  | .pure source children =>
      certificate.sourceActive state source ∧ match certificate.polynomials[source]? with
        | some polynomial => match polynomial.reduce state.zero.toFinset with
          | [term] =>
              term.coefficient ≠ 0 ∧
              (children.map Prod.fst).toFinset = term.support ∧
              ∀ entry ∈ children, certificate.childStateAt position entry.2
                (state.addZero entry.1)
          | _ => False
        | none => False
  | .factor source quotient pivot zeroChild quotientChild =>
      certificate.sourceActive state source ∧
        match certificate.polynomials[source]?, certificate.polynomials[quotient]? with
        | some polynomial, some quotientPolynomial =>
            let reducedPolynomial := polynomial.reduce state.zero.toFinset
            (∀ term ∈ reducedPolynomial, pivot ∈ term.support) ∧
            reducedPolynomial.eraseVariable pivot = quotientPolynomial ∧
            certificate.childStateAt position zeroChild
              (state.addZero pivot) ∧
            certificate.childStateAt position quotientChild
              (state.addExtra quotient)
        | _, _ => False

/-- A node exists at this position and its rule is valid in its recorded state. -/
def validNodeAt (certificate : Trace) (position : Nat) : Prop :=
  match certificate.nodes[position]? with
  | some node => certificate.validRule position node.state node.rule
  | none => False

/-- The designated root starts with no extra equations or known zero coordinates. -/
def validRoot (certificate : Trace) : Prop :=
  match certificate.nodes[certificate.root]? with
  | some node => node.state = { zero := [], extras := [] }
  | none => False

/-- The base and root are in bounds, the root is initial, and every node is valid. -/
def valid (certificate : Trace) : Prop :=
  certificate.baseCount ≤ certificate.polynomials.size ∧
    certificate.root < certificate.nodes.size ∧
    certificate.validRoot ∧
    ∀ position ∈ List.range certificate.nodes.size, certificate.validNodeAt position

/-- Executable test for source activity. -/
def sourceActiveB (certificate : Trace) (state : State) (source : Nat) : Bool :=
  decide (source < certificate.baseCount) || decide (source ∈ state.extras)

/-- Executable test for an earlier child with the expected state. -/
def childStateAtB
    (certificate : Trace) (position child : Nat) (expected : State) : Bool :=
  decide (child < position) && match certificate.nodes[child]? with
    | some node => decide (node.state = expected)
    | none => false

/-- Executable test for a resolved nonzero-constant contradiction. -/
def contradictionSourceB
    (certificate : Trace) (state : State) (source : Nat) : Bool :=
  certificate.sourceActiveB state source && match certificate.polynomials[source]? with
    | some polynomial => match polynomial.reduce state.zero.toFinset with
      | [term] => decide (term.support = ∅) && decide (term.coefficient ≠ 0)
      | _ => false
    | none => false

/-- Executable test for a resolved equation forcing one coordinate to zero. -/
def forcedSourceB
    (certificate : Trace) (state : State) (index source : Nat) : Bool :=
  certificate.sourceActiveB state source && match certificate.polynomials[source]? with
    | some polynomial => match polynomial.reduce state.zero.toFinset with
      | [term] => decide (term.support = {index}) && decide (term.coefficient ≠ 0)
      | _ => false
    | none => false

/-- Executable local rule validator. -/
def validRuleB (certificate : Trace) (position : Nat) (state : State) : Rule → Bool
  | .contradiction source => certificate.contradictionSourceB state source
  | .forced sources child =>
      certificate.childStateAtB position child
        (state.addZeros (sources.map Prod.fst)) &&
      sources.all fun entry => certificate.forcedSourceB state entry.1 entry.2
  | .pure source children =>
      certificate.sourceActiveB state source && match certificate.polynomials[source]? with
        | some polynomial => match polynomial.reduce state.zero.toFinset with
          | [term] =>
              decide (term.coefficient ≠ 0) &&
              decide ((children.map Prod.fst).toFinset = term.support) &&
              children.all fun entry => certificate.childStateAtB position entry.2
                (state.addZero entry.1)
          | _ => false
        | none => false
  | .factor source quotient pivot zeroChild quotientChild =>
      certificate.sourceActiveB state source &&
        match certificate.polynomials[source]?, certificate.polynomials[quotient]? with
        | some polynomial, some quotientPolynomial =>
            let reducedPolynomial := polynomial.reduce state.zero.toFinset
            reducedPolynomial.all (fun term => decide (pivot ∈ term.support)) &&
            decide (reducedPolynomial.eraseVariable pivot = quotientPolynomial) &&
            certificate.childStateAtB position zeroChild
              (state.addZero pivot) &&
            certificate.childStateAtB position quotientChild
              (state.addExtra quotient)
        | _, _ => false

/-- Executable validator for the node at a given position. -/
def validNodeAtB (certificate : Trace) (position : Nat) : Bool :=
  match certificate.nodes[position]? with
  | some node => certificate.validRuleB position node.state node.rule
  | none => false

/-- Executable test that the designated root has the initial state. -/
def validRootB (certificate : Trace) : Bool :=
  match certificate.nodes[certificate.root]? with
  | some node => decide (node.state = { zero := [], extras := [] })
  | none => false

/-- The executable kernel checker for a whole postorder trace. -/
def check (certificate : Trace) : Bool :=
  decide (certificate.baseCount ≤ certificate.polynomials.size) &&
    decide (certificate.root < certificate.nodes.size) &&
    certificate.validRootB &&
    (List.range certificate.nodes.size).all certificate.validNodeAtB

theorem sourceActiveB_eq_true {certificate : Trace} {state : State} {source : Nat} :
    certificate.sourceActiveB state source = true ↔ certificate.sourceActive state source := by
  simp [sourceActiveB, sourceActive]

theorem childStateAtB_eq_true
    {certificate : Trace} {position child : Nat} {expected : State} :
    certificate.childStateAtB position child expected = true ↔
      certificate.childStateAt position child expected := by
  simp only [childStateAtB, childStateAt, Bool.and_eq_true, decide_eq_true_eq]
  cases lookup : certificate.nodes[child]? <;> simp []

theorem contradictionSourceB_eq_true
    {certificate : Trace} {state : State} {source : Nat} :
    certificate.contradictionSourceB state source = true ↔
      certificate.contradictionSource state source := by
  cases lookup : certificate.polynomials[source]? with
  | none => simp [contradictionSourceB, contradictionSource, lookup,
      ]
  | some polynomial =>
      cases reduced : polynomial.reduce state.zero.toFinset with
      | nil => simp [contradictionSourceB, contradictionSource, lookup, reduced,
          ]
      | cons term tail =>
          cases tail with
          | nil => simp [contradictionSourceB, contradictionSource, lookup, reduced,
              sourceActiveB_eq_true]
          | cons next rest => simp [contradictionSourceB, contradictionSource, lookup,
              reduced]

theorem forcedSourceB_eq_true
    {certificate : Trace} {state : State} {index source : Nat} :
    certificate.forcedSourceB state index source = true ↔
      certificate.forcedSource state index source := by
  cases lookup : certificate.polynomials[source]? with
  | none => simp [forcedSourceB, forcedSource, lookup]
  | some polynomial =>
      cases reduced : polynomial.reduce state.zero.toFinset with
      | nil => simp [forcedSourceB, forcedSource, lookup, reduced]
      | cons term tail =>
          cases tail with
          | nil => simp [forcedSourceB, forcedSource, lookup, reduced,
              sourceActiveB_eq_true]
          | cons next rest => simp [forcedSourceB, forcedSource, lookup, reduced,
              ]

theorem validRuleB_eq_true
    {certificate : Trace} {position : Nat} {state : State} {rule : Rule} :
    certificate.validRuleB position state rule = true ↔
      certificate.validRule position state rule := by
  cases rule with
  | contradiction source =>
      exact contradictionSourceB_eq_true
  | forced sources child =>
      simp [validRuleB, validRule, childStateAtB_eq_true, forcedSourceB_eq_true,
        List.all_eq_true]
  | pure source children =>
      cases lookup : certificate.polynomials[source]? with
      | none => simp [validRuleB, validRule, lookup]
      | some polynomial =>
          cases reduced : polynomial.reduce state.zero.toFinset with
          | nil => simp [validRuleB, validRule, lookup, reduced]
          | cons term tail =>
              cases tail with
              | nil => simp [validRuleB, validRule, lookup, reduced,
                  sourceActiveB_eq_true, childStateAtB_eq_true, List.all_eq_true,
                  and_assoc]
              | cons next rest => simp [validRuleB, validRule, lookup, reduced,
                  ]
  | factor source quotient pivot zeroChild quotientChild =>
      cases sourceLookup : certificate.polynomials[source]? with
      | none => simp [validRuleB, validRule, sourceLookup]
      | some polynomial =>
          cases quotientLookup : certificate.polynomials[quotient]? with
          | none => simp [validRuleB, validRule, sourceLookup, quotientLookup,
              ]
          | some quotientPolynomial =>
              simp [validRuleB, validRule, sourceLookup, quotientLookup,
                sourceActiveB_eq_true, childStateAtB_eq_true, List.all_eq_true,
                and_assoc]

theorem validNodeAtB_eq_true {certificate : Trace} {position : Nat} :
    certificate.validNodeAtB position = true ↔ certificate.validNodeAt position := by
  cases lookup : certificate.nodes[position]? <;>
    simp [validNodeAtB, validNodeAt, lookup, validRuleB_eq_true]

theorem validRootB_eq_true {certificate : Trace} :
    certificate.validRootB = true ↔ certificate.validRoot := by
  cases lookup : certificate.nodes[certificate.root]? <;>
    simp [validRootB, validRoot, lookup]

theorem check_eq_true_iff {certificate : Trace} :
    certificate.check = true ↔ certificate.valid := by
  simp [check, valid, validRootB_eq_true, validNodeAtB_eq_true, List.all_eq_true,
    and_assoc]

/-- A bounded checker used to replay large traces compositionally.  Chunking
changes only elaboration cost: every node is still checked by `validNodeAtB`. -/
def checkNodes (certificate : Trace) (start count : Nat) : Bool :=
  (List.range count).all fun offset => certificate.validNodeAtB (start + offset)

/-- Every node in the indicated interval satisfies the propositional validator. -/
def nodeChunkValid (certificate : Trace) (start count : Nat) : Prop :=
  ∀ position, start ≤ position → position < start + count →
    certificate.validNodeAt position

theorem nodeChunkValid_of_checkNodes
    {certificate : Trace} {start count : Nat}
    (checked : certificate.checkNodes start count = true) :
    certificate.nodeChunkValid start count := by
  have checkedOffsets : ∀ offset ∈ List.range count,
      certificate.validNodeAt (start + offset) := by
    simpa [checkNodes, List.all_eq_true, validNodeAtB_eq_true] using checked
  intro position lower upper
  have offsetBound : position - start < count := by omega
  have offsetInRange : position - start ∈ List.range count := by
    simp [offsetBound]
  have identity : start + (position - start) = position := by omega
  simpa [identity] using checkedOffsets (position - start) offsetInRange

/-- Semantic interpretation of an ID-based trace state.  Missing polynomial
IDs cannot help a trace: every source used by a valid rule is separately
required to resolve in `validRule`. -/
def satisfiesState {R : Type*} [CommRing R]
    (certificate : Trace) (state : State) (values : Nat → R) : Prop :=
  (∀ index polynomial, index < certificate.baseCount →
      certificate.polynomials[index]? = some polynomial →
      polynomial.eval values = 0) ∧
    (∀ index ∈ state.extras, ∀ polynomial,
      certificate.polynomials[index]? = some polynomial →
      polynomial.eval values = 0) ∧
    ∀ index ∈ state.zero, values index = 0

/-- No assignment satisfies the equations and zeros recorded by this trace state. -/
def closedState {R : Type*} [CommRing R]
    (certificate : Trace) (state : State) : Prop :=
  ∀ values : Nat → R, ¬ certificate.satisfiesState state values

theorem source_zero
    {R : Type*} [CommRing R] {certificate : Trace} {state : State}
    {values : Nat → R} (satisfies : certificate.satisfiesState state values)
    {source : Nat} (active : certificate.sourceActive state source)
    {polynomial : Poly} (resolves : certificate.polynomials[source]? = some polynomial) :
    polynomial.eval values = 0 := by
  rcases active with inBase | inExtras
  · exact satisfies.1 source polynomial inBase resolves
  · exact satisfies.2.1 source inExtras polynomial resolves

theorem reduced_source_zero_state
    {R : Type*} [CommRing R] {certificate : Trace} {state : State}
    {values : Nat → R} (satisfies : certificate.satisfiesState state values)
    {source : Nat} (active : certificate.sourceActive state source)
    {polynomial : Poly} (resolves : certificate.polynomials[source]? = some polynomial) :
    (polynomial.reduce state.zero.toFinset).eval values = 0 := by
  rw [polynomial.eval_reduce values state.zero.toFinset]
  · exact source_zero satisfies active resolves
  · intro index inZero
    exact satisfies.2.2 index (List.mem_toFinset.mp inZero)

/-- Earlier-node closure transported through an explicitly checked child
edge. -/
theorem child_closed_of
    {R : Type*} [CommRing R] {certificate : Trace} {position child : Nat}
    {expected : State}
    (earlier : ∀ index, index < position → ∀ inBounds : index < certificate.nodes.size,
      certificate.closedState (R := R) certificate.nodes[index].state)
    (edge : certificate.childStateAt position child expected) :
    certificate.closedState (R := R) expected := by
  rcases edge with ⟨childEarlier, edgeState⟩
  cases lookup : certificate.nodes[child]? with
  | none => simp [lookup] at edgeState
  | some childNode =>
      simp [lookup] at edgeState
      have childInBounds : child < certificate.nodes.size :=
        (Array.getElem?_eq_some_iff.mp lookup).1
      have childValue : certificate.nodes[child] = childNode :=
        (Array.getElem?_eq_some_iff.mp lookup).2
      have closed := earlier child childEarlier childInBounds
      rw [childValue] at closed
      exact edgeState ▸ closed

theorem closed_of_contradictionSource
    {R : Type*} [Field R] [CharZero R]
    {certificate : Trace} {state : State} {source : Nat}
    (validSource : certificate.contradictionSource state source) :
    certificate.closedState (R := R) state := by
  rcases validSource with ⟨active, sourceData⟩
  cases lookup : certificate.polynomials[source]? with
  | none => simp [lookup] at sourceData
  | some polynomial =>
      cases reduced : polynomial.reduce state.zero.toFinset with
      | nil => simp [lookup, reduced] at sourceData
      | cons term tail =>
          cases tail with
          | cons next rest => simp [lookup, reduced] at sourceData
          | nil =>
              simp [lookup, reduced] at sourceData
              rcases sourceData with ⟨emptySupport, coefficientNonzero⟩
              intro values satisfies
              have reducedZero := reduced_source_zero_state satisfies active lookup
              rw [reduced] at reducedZero
              simp [Poly.eval, Term.eval, emptySupport, coefficientNonzero] at reducedZero

theorem zero_of_forcedSource
    {R : Type*} [Field R] [CharZero R]
    {certificate : Trace} {state : State} {index source : Nat}
    {values : Nat → R} (satisfies : certificate.satisfiesState state values)
    (validSource : certificate.forcedSource state index source) : values index = 0 := by
  rcases validSource with ⟨active, sourceData⟩
  cases lookup : certificate.polynomials[source]? with
  | none => simp [lookup] at sourceData
  | some polynomial =>
      cases reduced : polynomial.reduce state.zero.toFinset with
      | nil => simp [lookup, reduced] at sourceData
      | cons term tail =>
          cases tail with
          | cons next rest => simp [lookup, reduced] at sourceData
          | nil =>
              simp [lookup, reduced] at sourceData
              rcases sourceData with ⟨singletonSupport, coefficientNonzero⟩
              have reducedZero := reduced_source_zero_state satisfies active lookup
              rw [reduced] at reducedZero
              simpa [Poly.eval, Term.eval, singletonSupport, coefficientNonzero] using reducedZero

theorem closed_of_forced
    {R : Type*} [Field R] [CharZero R]
    {certificate : Trace} {state : State} {sources : List (Nat × Nat)}
    (validSources : ∀ entry ∈ sources,
      certificate.forcedSource state entry.1 entry.2)
    (childClosed : certificate.closedState (R := R)
      (state.addZeros (sources.map Prod.fst))) :
    certificate.closedState (R := R) state := by
  intro values satisfies
  apply childClosed values
  refine ⟨satisfies.1, satisfies.2.1, ?_⟩
  intro index inUnion
  rcases State.mem_insertMany.mp inUnion with inZero | inForced
  · exact satisfies.2.2 index inZero
  · have inMapped : index ∈ sources.map Prod.fst := inForced
    obtain ⟨entry, entryInSources, entryIndex⟩ := List.mem_map.mp inMapped
    subst index
    exact zero_of_forcedSource satisfies (validSources entry entryInSources)

theorem closed_of_pure
    {R : Type*} [Field R] [CharZero R]
    {certificate : Trace} {state : State} {source : Nat}
    {polynomial : Poly} {term : Term} {children : List (Nat × Nat)}
    (active : certificate.sourceActive state source)
    (lookup : certificate.polynomials[source]? = some polynomial)
    (reduced : polynomial.reduce state.zero.toFinset = [term])
    (coefficientNonzero : term.coefficient ≠ 0)
    (covers : (children.map Prod.fst).toFinset = term.support)
    (childrenClosed : ∀ entry ∈ children,
      certificate.closedState (R := R)
        (state.addZero entry.1)) :
    certificate.closedState (R := R) state := by
  intro values satisfies
  have reducedZero := reduced_source_zero_state satisfies active lookup
  rw [reduced] at reducedZero
  have productZero : term.support.prod values = 0 := by
    simpa [Poly.eval, Term.eval, coefficientNonzero] using reducedZero
  obtain ⟨index, inSupport, indexZero⟩ := Finset.prod_eq_zero_iff.mp productZero
  have inMappedFinset : index ∈ (children.map Prod.fst).toFinset := by
    rw [covers]
    exact inSupport
  have inMapped : index ∈ children.map Prod.fst := List.mem_toFinset.mp inMappedFinset
  obtain ⟨entry, entryInChildren, entryIndex⟩ := List.mem_map.mp inMapped
  subst index
  apply childrenClosed entry entryInChildren values
  refine ⟨satisfies.1, satisfies.2.1, ?_⟩
  intro item inInsert
  rcases State.mem_insertSorted.mp inInsert with rfl | inZero
  · exact indexZero
  · exact satisfies.2.2 item inZero

theorem closed_of_factor
    {R : Type*} [Field R] [CharZero R]
    {certificate : Trace} {state : State} {source quotient pivot : Nat}
    {polynomial quotientPolynomial : Poly}
    (active : certificate.sourceActive state source)
    (sourceLookup : certificate.polynomials[source]? = some polynomial)
    (quotientLookup : certificate.polynomials[quotient]? = some quotientPolynomial)
    (present : ∀ term ∈ polynomial.reduce state.zero.toFinset, pivot ∈ term.support)
    (quotientDefinition :
      (polynomial.reduce state.zero.toFinset).eraseVariable pivot = quotientPolynomial)
    (zeroChildClosed : certificate.closedState (R := R)
      (state.addZero pivot))
    (quotientChildClosed : certificate.closedState (R := R)
      (state.addExtra quotient)) :
    certificate.closedState (R := R) state := by
  intro values satisfies
  have reducedZero := reduced_source_zero_state satisfies active sourceLookup
  rw [(polynomial.reduce state.zero.toFinset).eval_eq_value_mul_eraseVariable values pivot present,
    quotientDefinition] at reducedZero
  rcases mul_eq_zero.mp reducedZero with pivotZero | quotientZero
  · apply zeroChildClosed values
    refine ⟨satisfies.1, satisfies.2.1, ?_⟩
    intro index inInsert
    rcases State.mem_insertSorted.mp inInsert with rfl | inZero
    · exact pivotZero
    · exact satisfies.2.2 index inZero
  · apply quotientChildClosed values
    refine ⟨satisfies.1, ?_, satisfies.2.2⟩
    intro index inExtras candidate candidateLookup
    rcases State.mem_insertSorted.mp inExtras with rfl | inParent
    · rw [quotientLookup] at candidateLookup
      cases candidateLookup
      exact quotientZero
    · exact satisfies.2.1 index inParent candidate candidateLookup

theorem validRule_sound
    {R : Type*} [Field R] [CharZero R]
    {certificate : Trace} {position : Nat} {state : State} {rule : Rule}
    (earlier : ∀ index, index < position → ∀ inBounds : index < certificate.nodes.size,
      certificate.closedState (R := R) certificate.nodes[index].state)
    (validRule : certificate.validRule position state rule) :
    certificate.closedState (R := R) state := by
  cases rule with
  | contradiction source =>
      exact closed_of_contradictionSource validRule
  | forced sources child =>
      rcases validRule with ⟨childEdge, validSources⟩
      exact closed_of_forced validSources (child_closed_of earlier childEdge)
  | pure source children =>
      rcases validRule with ⟨active, sourceData⟩
      cases lookup : certificate.polynomials[source]? with
      | none => simp [lookup] at sourceData
      | some polynomial =>
          cases reduced : polynomial.reduce state.zero.toFinset with
          | nil => simp [lookup, reduced] at sourceData
          | cons term tail =>
              cases tail with
              | cons next rest => simp [lookup, reduced] at sourceData
              | nil =>
                  simp [lookup, reduced] at sourceData
                  rcases sourceData with ⟨coefficientNonzero, covers, childEdges⟩
                  apply closed_of_pure active lookup reduced coefficientNonzero covers
                  intro entry entryInChildren
                  exact child_closed_of earlier
                    (childEdges entry.1 entry.2 entryInChildren)
  | factor source quotient pivot zeroChild quotientChild =>
      rcases validRule with ⟨active, sourceData⟩
      cases sourceLookup : certificate.polynomials[source]? with
      | none => simp [sourceLookup] at sourceData
      | some polynomial =>
          cases quotientLookup : certificate.polynomials[quotient]? with
          | none => simp [sourceLookup, quotientLookup] at sourceData
          | some quotientPolynomial =>
              simp [sourceLookup, quotientLookup] at sourceData
              rcases sourceData with
                ⟨present, quotientDefinition, zeroEdge, quotientEdge⟩
              exact closed_of_factor active sourceLookup quotientLookup present
                quotientDefinition (child_closed_of earlier zeroEdge)
                (child_closed_of earlier quotientEdge)

/-- Every node in a valid postorder certificate is semantically closed. -/
theorem valid_node_closed
    {R : Type*} [Field R] [CharZero R]
    {certificate : Trace} (valid : certificate.valid) :
    ∀ position (inBounds : position < certificate.nodes.size),
      certificate.closedState (R := R) certificate.nodes[position].state := by
  intro position
  induction position using Nat.strong_induction_on with
  | h position earlier =>
      intro inBounds
      have positionInRange : position ∈ List.range certificate.nodes.size := by
        simp [inBounds]
      have validAt := valid.2.2.2 position positionInRange
      have lookup : certificate.nodes[position]? = some certificate.nodes[position] :=
        Array.getElem?_eq_getElem inBounds
      simp [validNodeAt, lookup] at validAt
      exact validRule_sound earlier validAt

/-- The semantic reflection theorem from an explicitly assembled validity
proof.  Large generated traces use this after kernel-checking bounded chunks. -/
theorem closed_root_of_valid
    {R : Type*} [Field R] [CharZero R]
    {certificate : Trace} (valid : certificate.valid) :
    certificate.closedState (R := R) { zero := [], extras := [] } := by
  have rootClosed := valid_node_closed (R := R) valid certificate.root valid.2.1
  cases lookup : certificate.nodes[certificate.root]? with
  | none =>
      exfalso
      exact (not_lt_of_ge (Array.getElem?_eq_none_iff.mp lookup)) valid.2.1
  | some rootNode =>
      have rootValue : certificate.nodes[certificate.root]'valid.2.1 = rootNode :=
        (Array.getElem?_eq_some_iff.mp lookup).2
      have rootState : rootNode.state = { zero := [], extras := [] } := by
        simpa [validRoot, lookup] using valid.2.2.1
      rw [rootValue] at rootClosed
      exact rootState ▸ rootClosed

/-- The public one-shot reflection theorem for small traces. -/
theorem closed_root_of_check
    {R : Type*} [Field R] [CharZero R]
    {certificate : Trace} (checked : certificate.check = true) :
    certificate.closedState (R := R) { zero := [], extras := [] } :=
  closed_root_of_valid (check_eq_true_iff.mp checked)

section Sanity

/-- A four-node certificate exercising the factor and forced rules:
`x*(y+1)=0`, `x-1=0`, and `y=0`. -/
def factorSanity : Trace :=
  { baseCount := 3
    polynomials :=
      #[[{ coefficient := 1, support := {0} },
          { coefficient := 1, support := {0, 1} }],
        [{ coefficient := -1, support := ∅ },
          { coefficient := 1, support := {0} }],
        [{ coefficient := 1, support := {1} }],
        [{ coefficient := 1, support := ∅ },
          { coefficient := 1, support := {1} }] ]
    nodes :=
      #[{ state := { zero := [0], extras := [] }, rule := .contradiction 1 },
        { state := { zero := [1], extras := [3] }, rule := .contradiction 3 },
        { state := { zero := [], extras := [3] }, rule := .forced [(1, 2)] 1 },
        { state := { zero := [], extras := [] }, rule := .factor 0 3 0 0 2 } ]
    root := 3 }

example : factorSanity.check = true := by decide

/-- A child edge pointing to the wrong semantic state must fail closed. -/
def factorSanityBadChild : Trace :=
  { factorSanity with
    nodes := factorSanity.nodes.set! 3
      { state := { zero := [], extras := [] }, rule := .factor 0 3 0 1 2 } }

/-- A rule may use only a base equation or a quotient explicitly activated in
the current state. -/
def factorSanityInactiveSource : Trace :=
  { factorSanity with
    nodes := factorSanity.nodes.set! 0
      { state := { zero := [0], extras := [] }, rule := .contradiction 3 } }

/-- Postorder edges may never point forward or to the current node. -/
def factorSanityForwardEdge : Trace :=
  { factorSanity with
    nodes := factorSanity.nodes.set! 2
      { state := { zero := [], extras := [3] }, rule := .forced [(1, 2)] 3 } }

example : factorSanityBadChild.check = false := by decide
example : factorSanityInactiveSource.check = false := by decide
example : factorSanityForwardEdge.check = false := by decide

theorem factorSanity_closed
    {R : Type*} [Field R] [CharZero R] :
    factorSanity.closedState (R := R) { zero := [], extras := [] } :=
  closed_root_of_check (by decide)

end Sanity

end Trace

end Mettapedia.Algebra.Polynomial.Certificate.Multilinear

#print axioms Mettapedia.Algebra.Polynomial.Certificate.Multilinear.Trace.closed_root_of_check
#print axioms Mettapedia.Algebra.Polynomial.Certificate.Multilinear.Trace.factorSanity_closed
