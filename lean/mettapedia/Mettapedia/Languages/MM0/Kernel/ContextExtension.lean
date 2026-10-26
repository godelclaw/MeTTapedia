import Mettapedia.Languages.MM0.Kernel.ProofChecking

/-!
# MM0 proof checking under context extension

Appending declarations preserves typing, complete occurrence support,
admissible substitution, definition conversion and the exact supplied proof
witness. The conclusion and ordered hypotheses are unchanged.

Restriction to a context prefix preserves the same receipt exactly when every
native variable stored in its arguments and conversion evidence belongs to
that prefix (`ProofWitness.proof_in_prefix_iff`). The bound includes definition
dummy images and recursively retained child proofs, not just the conclusion.

An admitted context can allocate new bound variables at its end. Their sorts
must be declared and non-strict. Formation ensures that existing regular
variables depend only on already declared bound names, so every appended
index is independent of every previously typed expression. A malformed
forward dependency separates allocation from merely appending a list.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.Kernel

private theorem lookup_append {context : Context} {index : Nat} {binder : Binder}
    (known : context[index]? = some binder) (extra : Context) :
    (context ++ extra)[index]? = some binder := by
  obtain ⟨smaller, _⟩ := List.getElem?_eq_some_iff.mp known
  rw [List.getElem?_append_left smaller]
  exact known

theorem Preterm.Supports.weakenContext {context : Context} {expression : Preterm} {support : Finset Nat}
    (supported : Preterm.Supports context expression support) (extra : Context) :
    Preterm.Supports (context ++ extra) expression support := by
  induction supported with
  | bound known => exact .bound (lookup_append known extra)
  | regular known => exact .regular (lookup_append known extra)
  | term index => exact .term index
  | app _ _ ihFunction ihArgument => exact .app ihFunction ihArgument

theorem Preterm.Supports.hasVar_append_iff {context : Context} {expression : Preterm} {support : Finset Nat}
    (supported : Preterm.Supports context expression support) (extra : Context) (index : Nat) :
    Preterm.HasVar (context ++ extra) index expression ↔ Preterm.HasVar context index expression :=
  ((supported.weakenContext extra).mem_iff_hasVar index).symm.trans (supported.mem_iff_hasVar index)

theorem Preterm.HasType.weakenContext {signature : TermSignature} {context remaining : Context}
    {expression : Preterm} {sort : Nat}
    (typed : Preterm.HasType signature context expression remaining sort) (extra : Context) :
    Preterm.HasType signature (context ++ extra) expression remaining sort := by
  induction typed with
  | var known => exact .var (lookup_append known extra)
  | term known => exact .term known
  | bound _ known ih => exact .bound ih (lookup_append known extra)
  | regular _ _ ihFunction ihArgument => exact .regular ihFunction ihArgument

theorem Preterm.FitsBinder.weakenContext {signature : TermSignature} {context : Context}
    {expression : Preterm} {binder : Binder}
    (fitted : Preterm.FitsBinder signature context expression binder) (extra : Context) :
    Preterm.FitsBinder signature (context ++ extra) expression binder := by
  cases fitted with
  | bound known => exact .bound (lookup_append known extra)
  | regular typed => exact .regular (typed.weakenContext extra)

theorem Substitution.arguments_weakenContext {signature : TermSignature} {context formal : Context}
    {expressions : List Preterm}
    (fitted : List.Forall₂ (Preterm.FitsBinder signature context) expressions formal) (extra : Context) :
    List.Forall₂ (Preterm.FitsBinder signature (context ++ extra)) expressions formal := by
  induction fitted with
  | nil => exact .nil
  | cons head _ ih => exact .cons (head.weakenContext extra) ih

theorem Substitution.Admissible.weakenContext {signature : TermSignature} {formal context : Context}
    {expressions : List Preterm}
    (admitted : Substitution.Admissible signature formal context expressions) (extra : Context) :
    Substitution.Admissible signature formal (context ++ extra) expressions := by
  refine ⟨?_, ?_⟩
  · exact Substitution.arguments_weakenContext admitted.typed extra
  · intro entry member sort image bound other otherMember independent occurrence
    obtain ⟨support, supported⟩ := Substitution.typed_entry_support admitted.typed other otherMember
    exact admitted.independent entry member sort image bound other otherMember independent
      ((supported.hasVar_append_iff extra image).mp occurrence)

theorem Preterm.FreshFor.weakenContext {context : Context} {index : Nat} {expression : Preterm}
    (fresh : Preterm.FreshFor context index expression) (extra : Context) :
    Preterm.FreshFor (context ++ extra) index expression := by
  obtain ⟨⟨support, supported⟩, independent⟩ := fresh
  exact ⟨⟨support, supported.weakenContext extra⟩,
    fun occurrence => independent ((supported.hasVar_append_iff extra index).mp occurrence)⟩

theorem Definition.FreshDummies.weakenContext {context : Context} {arguments : List Preterm}
    {sorts images : List Nat} (fresh : Definition.FreshDummies context arguments sorts images)
    (extra : Context) : Definition.FreshDummies (context ++ extra) arguments sorts images := by
  induction fresh with
  | nil arguments => exact .nil arguments
  | cons known independent _ ih =>
      exact .cons (lookup_append known extra)
        (fun expression member => (independent expression member).weakenContext extra) ih

theorem Definition.Unfolds.weakenContext {signature : TermSignature} {definitions : Definition.Signature}
    {context : Context} {symbol : Nat} {arguments : List Preterm} {images : List Nat} {result : Preterm}
    (unfolded : Definition.Unfolds signature definitions context symbol arguments images result)
    (extra : Context) : Definition.Unfolds signature definitions (context ++ extra) symbol arguments images result := by
  cases unfolded with
  | intro known body fitted fresh substituted =>
      exact .intro known body (Substitution.arguments_weakenContext fitted extra)
        (fresh.weakenContext extra) substituted

theorem TheoremDecl.Instantiates.weakenContext {signature : TermSignature} {context : Context}
    {declaration : TheoremDecl} {arguments : List Preterm} {instantiation : TheoremInstance}
    (instantiated : TheoremDecl.Instantiates signature context declaration arguments instantiation)
    (extra : Context) : TheoremDecl.Instantiates signature (context ++ extra) declaration arguments instantiation :=
  ⟨instantiated.admissible.weakenContext extra, instantiated.hypotheses, instantiated.conclusion⟩

theorem ConvWitness.Checks.weakenContext {signature : TermSignature} {definitions : Definition.Signature}
    {context : Context} {witness : ConvWitness} {left right : Preterm} {sort : Nat}
    (checked : ConvWitness.Checks signature definitions context witness left right sort) (extra : Context) :
    ConvWitness.Checks signature definitions (context ++ extra) witness left right sort := by
  induction checked using ConvWitness.Checks.rec
      (motive_2 := fun children left right binders _ =>
        ConvWitness.ChecksArgs signature definitions (context ++ extra) children left right binders) with
  | refl typed => exact .refl (typed.weakenContext extra)
  | symm _ ih => exact .symm ih
  | trans _ _ ihFirst ihSecond => exact .trans ihFirst ihSecond
  | congruence known _ ih => exact .congruence known ih
  | unfold known unfolded typed => exact .unfold known (unfolded.weakenContext extra) (typed.weakenContext extra)
  | nil => exact .nil
  | cons leftFits rightFits _ _ ihChild ihTail =>
      exact .cons (leftFits.weakenContext extra) (rightFits.weakenContext extra) ihChild ihTail

theorem ProofWitness.Checks.weakenContext {signature : TermSignature} {definitions : Definition.Signature}
    {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}
    {witness : ProofWitness} {conclusion : Preterm}
    (checked : ProofWitness.Checks signature definitions theorems context hypotheses witness conclusion)
    (extra : Context) :
    ProofWitness.Checks signature definitions theorems (context ++ extra) hypotheses witness conclusion := by
  induction checked using ProofWitness.Checks.rec
      (motive_2 := fun children conclusions _ =>
        ProofWitness.ChecksList signature definitions theorems (context ++ extra) hypotheses children conclusions) with
  | hyp known => exact .hyp known
  | theoremApp known instantiated _ ih => exact .theoremApp known (instantiated.weakenContext extra) ih
  | conversion converted _ ih => exact .conversion (converted.weakenContext extra) ih
  | nil => exact .nil
  | cons _ _ ihChild ihTail => exact .cons ihChild ihTail

theorem ProofWitness.accepted_weakenContext {signature : TermSignature} {definitions : Definition.Signature}
    {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}
    {witness : ProofWitness} {conclusion : Preterm}
    (accepted : witness.proof? signature definitions theorems context hypotheses = some conclusion)
    (extra : Context) :
    witness.proof? signature definitions theorems (context ++ extra) hypotheses = some conclusion :=
  ((ProofWitness.proof_eq_some_iff _ _ _ _ _ _ _).mp accepted |>.weakenContext extra).eval

#print axioms Preterm.Supports.weakenContext
#print axioms Substitution.Admissible.weakenContext
#print axioms ConvWitness.Checks.weakenContext
#print axioms ProofWitness.Checks.weakenContext
#print axioms ProofWitness.accepted_weakenContext



private theorem dependencies_append {sorts : SortSignature} {initial : Context} {binder : Binder}
    (admitted : Context.AdmitsBinder sorts initial binder)
    (prior : ∀ sort dependencies, Binder.regular sort dependencies ∈ initial →
      ∀ index ∈ dependencies, ∃ boundSort, initial[index]? = some (.bound boundSort)) :
    ∀ sort dependencies, Binder.regular sort dependencies ∈ initial ++ [binder] →
      ∀ index ∈ dependencies, ∃ boundSort, (initial ++ [binder])[index]? = some (.bound boundSort) := by
  intro sort dependencies member index depends
  rcases List.mem_append.mp member with earlier | latest
  · obtain ⟨boundSort, known⟩ := prior sort dependencies earlier index depends
    exact ⟨boundSort, lookup_append known [binder]⟩
  · have same : Binder.regular sort dependencies = binder := List.mem_singleton.mp latest
    rw [← same] at admitted
    cases admitted with
    | regular _ declared =>
        obtain ⟨boundSort, known⟩ := declared index depends
        exact ⟨boundSort, lookup_append known [binder]⟩

private theorem dependencies_extension {sorts : SortSignature} {initial remaining : Context}
    (extension : Context.Extension sorts initial remaining) :
    (∀ sort dependencies, Binder.regular sort dependencies ∈ initial →
      ∀ index ∈ dependencies, ∃ boundSort, initial[index]? = some (.bound boundSort)) →
    ∀ sort dependencies, Binder.regular sort dependencies ∈ initial ++ remaining →
      ∀ index ∈ dependencies, ∃ boundSort, (initial ++ remaining)[index]? = some (.bound boundSort) := by
  induction extension with
  | nil initial => intro prior; simpa using prior
  | cons admitted _ ih =>
      intro prior
      simpa only [List.append_assoc, List.singleton_append] using ih (dependencies_append admitted prior)

theorem Context.WellFormed.regular_dependency_declared {sorts : SortSignature} {context : Context}
    (formed : Context.WellFormed sorts context) {sort index : Nat} {dependencies : Finset Nat}
    (member : Binder.regular sort dependencies ∈ context) (depends : index ∈ dependencies) :
    ∃ boundSort, context[index]? = some (.bound boundSort) := by
  exact dependencies_extension formed (by simp) sort dependencies member index depends

theorem Preterm.Supports.bound_lookup {sorts : SortSignature} {context : Context}
    {expression : Preterm} {support : Finset Nat} (supported : Preterm.Supports context expression support)
    (formed : Context.WellFormed sorts context) {index : Nat} (member : index ∈ support) :
    ∃ sort, context[index]? = some (.bound sort) := by
  induction supported with
  | bound known =>
      have same := Finset.mem_singleton.mp member
      subst index
      exact ⟨_, known⟩
  | regular known =>
      exact formed.regular_dependency_declared (List.mem_of_getElem? known) member
  | term => simp at member
  | app _ _ ihFunction ihArgument =>
      rcases Finset.mem_union.mp member with left | right
      · exact ihFunction left
      · exact ihArgument right

def Context.appendBounds (context : Context) (sort count : Nat) : Context :=
  context ++ List.replicate count (.bound sort)

@[simp] theorem Context.appendBounds_length (context : Context) (sort count : Nat) :
    (context.appendBounds sort count).length = context.length + count := by
  simp [Context.appendBounds]

theorem Context.appendBounds_lookup (context : Context) (sort count offset : Nat) (smaller : offset < count) :
    (context.appendBounds sort count)[context.length + offset]? = some (.bound sort) := by
  change (context ++ List.replicate count (.bound sort))[context.length + offset]? = some (.bound sort)
  rw [List.getElem?_append_right (Nat.le_add_right context.length offset)]
  simp [smaller]

/-- Independence from a suffix of allocated bound names gives a syntactic
variable bound for a typed expression. -/
theorem Preterm.HasType.varsBelow_of_tail_independent
    {signature : TermSignature} {initial remaining : Context} {expression : Preterm}
    {object count result lower : Nat}
    (typed : Preterm.HasType signature (initial.appendBounds object count) expression remaining result)
    (independent : ∀ offset, lower ≤ offset →
      ¬ Preterm.HasVar (initial.appendBounds object count) (initial.length + offset) expression) :
    Preterm.VarsBelow (initial.length + lower) expression := by
  apply (Preterm.varsBelow_iff_occurs _ _).mpr
  intro index occurs
  by_contra outside
  have upper := typed.varsBelow.occurs_lt occurs
  rw [Context.appendBounds_length] at upper
  have initialBefore : initial.length ≤ index := by omega
  have offsetBound : index - initial.length < count := by omega
  have declared := initial.appendBounds_lookup object count (index - initial.length) offsetBound
  have atIndex : (initial.appendBounds object count)[index]? = some (.bound object) := by
    simpa only [Nat.add_sub_of_le initialBefore] using declared
  have used := occurs.hasVar_of_bound atIndex
  have excluded := independent (index - initial.length) (by omega)
  rw [Nat.add_sub_of_le initialBefore] at excluded
  exact excluded used

private theorem bound_extension {sorts : SortSignature} {sort : Nat} {info : SortInfo}
    (known : sorts sort = some info) (notStrict : info.strict = false) (count : Nat) (initial : Context) :
    Context.Extension sorts initial (List.replicate count (.bound sort)) := by
  induction count generalizing initial with
  | zero => exact .nil initial
  | succ count ih => exact .cons (.bound known notStrict) (ih _)

theorem Context.appendBounds_wellFormed {sorts : SortSignature} {context : Context} {sort : Nat} {info : SortInfo}
    (formed : Context.WellFormed sorts context) (known : sorts sort = some info) (notStrict : info.strict = false)
    (count : Nat) : Context.WellFormed sorts (context.appendBounds sort count) := by
  apply (Context.extension_append_iff sorts [] context (List.replicate count (.bound sort))).mpr
  exact ⟨formed, bound_extension known notStrict count context⟩

theorem Preterm.HasType.independent_appendedBound {sorts : SortSignature} {signature : TermSignature}
    {context remaining : Context} {expression : Preterm} {result : Nat}
    (typed : Preterm.HasType signature context expression remaining result)
    (formed : Context.WellFormed sorts context) (sort count offset : Nat) :
    ¬ Preterm.HasVar (context.appendBounds sort count) (context.length + offset) expression := by
  obtain ⟨support, supported⟩ := typed.support_exists
  intro occurrence
  have earlier := (supported.hasVar_append_iff (List.replicate count (.bound sort)) _).mp occurrence
  have member := (supported.mem_iff_hasVar _).mpr earlier
  obtain ⟨boundSort, known⟩ := supported.bound_lookup formed member
  obtain ⟨smaller, _⟩ := List.getElem?_eq_some_iff.mp known
  omega

namespace ContextExtensionControls
def sorts : SortSignature := fun _ => some {}
def original : Context := [.bound 2, .regular 2 {0}]
theorem original_formed : Context.WellFormed sorts original := by
  apply (Context.check_iff _ _).mp
  decide

theorem two_fresh_slots : (original.appendBounds 2 2)[2]? = some (.bound 2) ∧
    (original.appendBounds 2 2)[3]? = some (.bound 2) := by decide

theorem retained_regular_support :
    Preterm.support? (original.appendBounds 2 2) (.var 1) = some {0} := by decide

theorem appended_slots_independent :
    ¬ Preterm.HasVar (original.appendBounds 2 2) 2 (.var 1) ∧
    ¬ Preterm.HasVar (original.appendBounds 2 2) 3 (.var 1) := by
  constructor
  · exact Preterm.HasType.independent_appendedBound
      (Preterm.HasType.var (signature := fun _ => none) (context := original) (index := 1) rfl)
      original_formed 2 2 0
  · exact Preterm.HasType.independent_appendedBound
      (Preterm.HasType.var (signature := fun _ => none) (context := original) (index := 1) rfl)
      original_formed 2 2 1

theorem collapsed_new_names_refused :
    Substitution.checkAdmissible (fun _ => none) [.bound 2, .bound 2]
      (original.appendBounds 2 2) [.var 2, .var 2] = false := by decide

def malformed : Context := [.regular 2 {1}]
theorem malformed_not_formed : ¬ Context.WellFormed sorts malformed := by
  intro formed
  have checked := (Context.check_iff _ _).mpr formed
  contradiction

theorem append_alone_does_not_give_freshness :
    Preterm.HasVar (malformed.appendBounds 2 1) 1 (.var 0) :=
  .regular rfl (by decide)

theorem fresh_variable_refuses_in_original : Preterm.infer (fun _ => none) original (.var 2) = none := by decide
theorem fresh_variable_types_in_extension :
    Preterm.HasType (fun _ => none) (original.appendBounds 2 2) (.var 2) [] 2 := .var (binder := .bound 2) rfl
end ContextExtensionControls

#print axioms Context.WellFormed.regular_dependency_declared
#print axioms Preterm.Supports.bound_lookup
#print axioms Context.appendBounds_wellFormed
#print axioms Preterm.HasType.independent_appendedBound
#print axioms ContextExtensionControls.append_alone_does_not_give_freshness
private theorem lookup_prefix {context extra : Context} {index : Nat} {binder : Binder}
    (known : (context ++ extra)[index]? = some binder) (before : index < context.length) :
    context[index]? = some binder := by
  rwa [List.getElem?_append_left before] at known


theorem Preterm.Supports.restrictContext {context extra : Context} {expression : Preterm} {support : Finset Nat}
    (supported : Supports (context ++ extra) expression support) (bounded : VarsBelow context.length expression) :
    Supports context expression support := by
  induction supported with
  | bound known => exact .bound (lookup_prefix known bounded)
  | regular known => exact .regular (lookup_prefix known bounded)
  | term index => exact .term index
  | app first second ihFirst ihSecond => exact .app (ihFirst bounded.1) (ihSecond bounded.2)


theorem Preterm.HasType.restrictContext {signature : TermSignature} {context extra remaining : Context}
    {expression : Preterm} {sort : Nat}
    (typed : HasType signature (context ++ extra) expression remaining sort)
    (bounded : VarsBelow context.length expression) : HasType signature context expression remaining sort := by
  induction typed with
  | var known => exact .var (lookup_prefix known bounded)
  | term known => exact .term known
  | bound first known ih => exact .bound (ih bounded.1) (lookup_prefix known bounded.2)
  | regular first second ihFirst ihSecond => exact .regular (ihFirst bounded.1) (ihSecond bounded.2)


theorem Preterm.FitsBinder.restrictContext {signature : TermSignature} {context extra : Context}
    {expression : Preterm} {binder : Binder}
    (fits : FitsBinder signature (context ++ extra) expression binder)
    (bounded : VarsBelow context.length expression) : FitsBinder signature context expression binder := by
  cases fits with
  | bound known => exact .bound (lookup_prefix known bounded)
  | regular typed => exact .regular (typed.restrictContext bounded)


theorem Substitution.arguments_restrictContext {signature : TermSignature} {context extra formal : Context}
    {expressions : List Preterm}
    (fits : List.Forall₂ (Preterm.FitsBinder signature (context ++ extra)) expressions formal)
    (bounded : ∀ expression ∈ expressions, Preterm.VarsBelow context.length expression) :
    List.Forall₂ (Preterm.FitsBinder signature context) expressions formal := by
  induction fits with
  | nil => exact .nil
  | cons first rest ih =>
      exact .cons (first.restrictContext (bounded _ List.mem_cons_self))
        (ih (fun expression member => bounded expression (List.mem_cons_of_mem _ member)))


theorem Substitution.Admissible.restrictContext {signature : TermSignature} {formal context extra : Context}
    {expressions : List Preterm}
    (admitted : Admissible signature formal (context ++ extra) expressions)
    (bounded : ∀ expression ∈ expressions, Preterm.VarsBelow context.length expression) :
    Admissible signature formal context expressions := by
  refine ⟨arguments_restrictContext admitted.typed bounded, ?_⟩
  intro entry member sort image bound other otherMember independent occurrence
  obtain ⟨support, restricted⟩ := typed_entry_support
    (arguments_restrictContext admitted.typed bounded) other otherMember
  exact admitted.independent entry member sort image bound other otherMember independent
    ((restricted.hasVar_append_iff extra image).mpr occurrence)


theorem Preterm.FreshFor.restrictContext {context extra : Context} {index : Nat} {expression : Preterm}
    (fresh : FreshFor (context ++ extra) index expression) (bounded : VarsBelow context.length expression) :
    FreshFor context index expression := by
  obtain ⟨⟨support, supported⟩, independent⟩ := fresh
  have restricted := supported.restrictContext bounded
  exact ⟨⟨support, restricted⟩, fun occurrence => independent ((restricted.hasVar_append_iff extra index).mpr occurrence)⟩


theorem Definition.FreshDummies.restrictContext {context extra : Context} {arguments : List Preterm}
    {sorts images : List Nat} (fresh : FreshDummies (context ++ extra) arguments sorts images)
    (argumentsBound : ∀ expression ∈ arguments, Preterm.VarsBelow context.length expression)
    (imagesBound : ∀ image ∈ images, image < context.length) :
    FreshDummies context arguments sorts images := by
  induction fresh with
  | nil arguments => exact .nil arguments
  | @cons arguments sort image sorts images known independent tail ih =>
      refine .cons (lookup_prefix known (imagesBound _ List.mem_cons_self))
        (fun expression member => (independent expression member).restrictContext (argumentsBound expression member))
        (ih ?_ (fun name member => imagesBound name (List.mem_cons_of_mem _ member)))
      intro expression member
      rcases List.mem_append.mp member with old | last
      · exact argumentsBound expression old
      · have same : expression = .var image := by simpa using last
        subst expression
        exact imagesBound _ List.mem_cons_self


theorem Definition.Unfolds.restrictContext {signature : TermSignature} {definitions : Definition.Signature}
    {context extra : Context} {symbol : Nat} {arguments : List Preterm} {images : List Nat} {result : Preterm}
    (unfolded : Unfolds signature definitions (context ++ extra) symbol arguments images result)
    (argumentsBound : ∀ argument ∈ arguments, Preterm.VarsBelow context.length argument)
    (imagesBound : ∀ image ∈ images, image < context.length) :
    Unfolds signature definitions context symbol arguments images result := by
  cases unfolded with
  | intro known body fits fresh substituted =>
      exact .intro known body (Substitution.arguments_restrictContext fits argumentsBound)
        (fresh.restrictContext argumentsBound imagesBound) substituted


theorem ConvWitness.Checks.restrictContext {signature : TermSignature} {definitions : Definition.Signature}
    {context extra : Context} {witness : ConvWitness} {left right : Preterm} {sort : Nat}
    (checked : Checks signature definitions (context ++ extra) witness left right sort)
    (bounded : witness.VarsBelow context.length) :
    Checks signature definitions context witness left right sort := by
  induction checked using Checks.rec
      (motive_2 := fun children left right binders _ =>
        (∀ child ∈ children, child.VarsBelow context.length) →
          ChecksArgs signature definitions context children left right binders) with
  | refl typed =>
      simp only [ConvWitness.VarsBelow] at bounded
      exact .refl (typed.restrictContext bounded)
  | symm child ih =>
      simp only [ConvWitness.VarsBelow] at bounded
      exact .symm (ih bounded)
  | trans first second ihFirst ihSecond =>
      simp only [ConvWitness.VarsBelow] at bounded
      exact .trans (ihFirst bounded.1) (ihSecond bounded.2)
  | congruence known children ih =>
      simp only [ConvWitness.VarsBelow] at bounded
      exact .congruence known (ih bounded)
  | unfold known unfolded typed =>
      simp only [ConvWitness.VarsBelow] at bounded
      exact .unfold known (unfolded.restrictContext bounded.1 bounded.2)
        (typed.restrictContext (unfolded.varsBelow _ bounded.1 bounded.2))
  | nil => exact .nil
  | cons leftFits rightFits child tail ihChild ihTail =>
      rename_i allBound
      have headBound := allBound _ List.mem_cons_self
      have ends := child.endpoint_varsBelow _ headBound
      exact .cons (leftFits.restrictContext ends.1) (rightFits.restrictContext ends.2)
        (ihChild headBound) (ihTail (fun child member => allBound child (List.mem_cons_of_mem _ member)))


theorem TheoremDecl.Instantiates.restrictContext {signature : TermSignature} {context extra : Context}
    {declaration : TheoremDecl} {arguments : List Preterm} {instantiation : TheoremInstance}
    (instantiated : Instantiates signature (context ++ extra) declaration arguments instantiation)
    (bounded : ∀ argument ∈ arguments, Preterm.VarsBelow context.length argument) :
    Instantiates signature context declaration arguments instantiation :=
  ⟨instantiated.admissible.restrictContext bounded, instantiated.hypotheses, instantiated.conclusion⟩


theorem ProofWitness.Checks.restrictContext {signature : TermSignature} {definitions : Definition.Signature}
    {theorems : TheoremSignature} {context extra : Context} {hypotheses : List Preterm}
    {witness : ProofWitness} {conclusion : Preterm}
    (checked : Checks signature definitions theorems (context ++ extra) hypotheses witness conclusion)
    (bounded : witness.VarsBelow context.length) :
    Checks signature definitions theorems context hypotheses witness conclusion := by
  induction checked using Checks.rec
      (motive_2 := fun children conclusions _ =>
        (∀ child ∈ children, child.VarsBelow context.length) →
          ChecksList signature definitions theorems context hypotheses children conclusions) with
  | hyp known => exact .hyp known
  | theoremApp known instantiated children ih =>
      simp only [ProofWitness.VarsBelow] at bounded
      exact .theoremApp known (instantiated.restrictContext bounded.1) (ih bounded.2)
  | conversion converted child ih =>
      simp only [ProofWitness.VarsBelow] at bounded
      exact .conversion (converted.restrictContext bounded.1) (ih bounded.2)
  | nil => exact .nil
  | cons head tail ihHead ihTail =>
      rename_i allBound
      exact .cons (ihHead (allBound _ List.mem_cons_self))
        (ihTail (fun child member => allBound child (List.mem_cons_of_mem _ member)))


theorem ProofWitness.proof_in_prefix_iff (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (context extra : Context) (hypotheses : List Preterm)
    (witness : ProofWitness) (conclusion : Preterm) :
    witness.proof? signature definitions theorems context hypotheses = some conclusion ↔
      witness.proof? signature definitions theorems (context ++ extra) hypotheses = some conclusion ∧
      witness.VarsBelow context.length := by
  rw [proof_eq_some_iff, proof_eq_some_iff]
  exact ⟨fun checked => ⟨checked.weakenContext extra, checked.payload_varsBelow⟩,
    fun ⟨checked, bounded⟩ => checked.restrictContext bounded⟩


end Mettapedia.Languages.MM0.Kernel
