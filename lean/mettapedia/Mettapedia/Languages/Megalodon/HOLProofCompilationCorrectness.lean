import Mettapedia.Languages.Megalodon.ProofCompilation
import Mettapedia.Languages.Megalodon.HOLExistentialProofInference
import Mettapedia.Languages.Megalodon.HOLExtensionalityProofInference
import Mettapedia.Languages.Megalodon.HOLTypeSubstitutionEncoding
import Mettapedia.Logic.HOL.ProofSyntaxTypeSubstitution

/-!
# All-constructor HOL proof compilation under explicit native policies

The translation retains the supplied proof tree, ordered assumptions and
exact encoded conclusion. Its type interpretation must form every source
simple type. The declaration table is opaque; the extensionality names used
by the proof must resolve to the precise guest schemas. These are sufficient
policies for this route, not requirements on every Megalodon environment or
on the ambient logic of Prime.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace Mettapedia.Languages.Megalodon.HOLProofCompilationCorrectness

open Mettapedia.Logic.HOL
open MathdataKernel HenkinTermInterpretation HOLTermEncoding HOLProofInference

universe u v
variable {SourceBase : Type u} {SourceConst : Ty SourceBase → Type v}
variable {environment : Environment}

/-- Only the function-type pairs whose extensionality proofs are actually
used by the compiler. Lambda congruence uses the same guest schema. -/
def functionalTypes : {gamma : Ctx SourceBase} →
    {assumptions : List (Formula SourceConst gamma)} → {conclusion : Formula SourceConst gamma} →
    ProofSyntax SourceConst assumptions conclusion → List (Ty SourceBase × Ty SourceBase)
  | _, _, _, .hyp _ | _, _, _, .topI | _, _, _, .eqRefl _
  | _, _, _, .beta _ _ | _, _, _, .eta _ => []
  | _, _, _, .botE inner | _, _, _, .andEL inner | _, _, _, .andER inner
  | _, _, _, .orIL inner | _, _, _, .orIR inner | _, _, _, .impI inner
  | _, _, _, .notI inner | _, _, _, .allI inner | _, _, _, .allE _ inner
  | _, _, _, .exI _ inner | _, _, _, .eqSymm inner | _, _, _, .eqPropEL inner
  | _, _, _, .eqPropER inner | _, _, _, .eqApp _ inner | _, _, _, .eqAppArg _ inner =>
      functionalTypes inner
  | _, _, _, .andI one two | _, _, _, .impE one two | _, _, _, .notE one two
  | _, _, _, .exE one two | _, _, _, .eqTrans one two | _, _, _, .eqPropI one two =>
      functionalTypes one ++ functionalTypes two
  | _, _, _, .orE cases left right =>
      functionalTypes cases ++ functionalTypes left ++ functionalTypes right
  | _, _, _, @ProofSyntax.eqLam _ _ _ _ domain result _ _ inner
  | _, _, _, @ProofSyntax.funExt _ _ _ _ domain result _ _ inner =>
      (domain, result) :: functionalTypes inner

theorem compile_castIndices (functional : Tp → Tp → Pf) (propositional : Pf)
    {gamma : Ctx Base} {assumptions other : List (Formula (Constant environment) gamma)}
    {conclusion target : Formula (Constant environment) gamma}
    (contexts : assumptions = other) (goals : conclusion = target)
    (source : ProofSyntax (Constant environment) assumptions conclusion) :
    ProofCompilation.compile functional propositional (ProofSyntax.castIndices contexts goals source) =
      ProofCompilation.compile functional propositional source := by
  cases contexts
  cases goals
  rfl

variable (types : SourceBase → Ty Base)
variable (constants : ∀ {type}, SourceConst type → Constant environment (type.substitute types))
variable (depth : Nat)
variable (formed : ∀ type : Ty SourceBase,
  (reifyType (type.substitute types)).plainWellFormed depth = true)
variable (unfoldingAbsent : ∀ name entry,
  environment.lookupTerm? name = some entry → entry.definition = none)
variable (functional : Tp → Tp → Name) (propositional : Name)
variable (propositionalDeclared :
  environment.lookupKnown? propositional = some ExtensionalityAxioms.Native.propositional)

include formed unfoldingAbsent propositionalDeclared in
/-- Every constructor of the supplied source proof produces an inferred
native proof, with a constructed sufficient budget. Functional declarations
are required only for the finite pairs used by this particular proof. -/
theorem inferred {gamma : Ctx SourceBase}
    {assumptions : List (Formula SourceConst gamma)} {conclusion : Formula SourceConst gamma}
    (source : ProofSyntax SourceConst assumptions conclusion) :
    (∀ domain result, (domain, result) ∈ functionalTypes source →
      environment.lookupKnown? (functional (reifyType (domain.substitute types))
        (reifyType (result.substitute types))) = some
          (ExtensionalityAxioms.Native.functional (reifyType (domain.substitute types))
            (reifyType (result.substitute types)))) →
    Infers depth (assumptions.map (mapTypes types constants))
      (ProofCompilation.compile (fun domain result => .known (functional domain result))
        (.known propositional) (ProofSyntax.mapTypes types constants source))
      (mapTypes types constants conclusion) := by
  have annotations {gamma : Ctx SourceBase} {type : Ty SourceBase}
      (term : Term SourceConst gamma type) :=
    HOLTypeSubstitutionEncoding.native_annotations types constants depth formed term
  have normal {gamma : Ctx Base} {type : Ty Base} (term : Term (Constant environment) gamma type) :
      DeltaNormalInvariant.Normal environment (native term) :=
    fun name entry _ found => unfoldingAbsent name entry found
  have contexts {gamma : Ctx Base} (assumptions : List (Formula (Constant environment) gamma)) :
      DeltaNormalInvariant.ContextNormal environment (context depth assumptions) :=
    fun _ _ name entry _ found => unfoldingAbsent name entry found
  induction source with
  | @hyp ctx hyps occurrence =>
      intro _
      simpa [ProofSyntax.mapTypes, compile_castIndices, ProofCompilation.compile] using
        (HOLProofInference.hyp depth (hyps.map (mapTypes types constants))
          ⟨occurrence.val, by simpa only [List.length_map] using occurrence.isLt⟩)
  | topI => intro _; exact HOLProofInference.topI depth _
  | @botE ctx hyps conclusion inner ih =>
      intro declared
      have child := fun domain result (member : (domain, result) ∈ functionalTypes inner) => declared domain result
        (by simpa only [functionalTypes] using member)
      simpa only [ProofSyntax.mapTypes, compile_castIndices, ProofCompilation.compile,
        LogicalProofCompilation.applyTerms, LogicalProofCompilation.applyProofs, List.foldl_cons, List.foldl_nil,
        mapTypes, mapTypes_instantiate, ExtDerivation.mapTypes_weakenHyps, mapTypes_weaken, Ty.substitute] using
        (HOLLogicalProofInference.botE (mapTypes types constants conclusion) (annotations conclusion) (normal _) (contexts _) (ih child))
  | @andEL ctx hyps left right inner ih =>
      intro declared
      have child := fun domain result (member : (domain, result) ∈ functionalTypes inner) => declared domain result
        (by simpa only [functionalTypes] using member)
      simpa only [ProofSyntax.mapTypes, compile_castIndices, ProofCompilation.compile,
        LogicalProofCompilation.applyTerms, LogicalProofCompilation.applyProofs, List.foldl_cons, List.foldl_nil,
        mapTypes, mapTypes_instantiate, ExtDerivation.mapTypes_weakenHyps, mapTypes_weaken, Ty.substitute] using
        (HOLLogicalProofInference.andEL (annotations left) (annotations right) (normal _) (normal _) (contexts _) (ih child))
  | @andER ctx hyps left right inner ih =>
      intro declared
      have child := fun domain result (member : (domain, result) ∈ functionalTypes inner) => declared domain result
        (by simpa only [functionalTypes] using member)
      simpa only [ProofSyntax.mapTypes, compile_castIndices, ProofCompilation.compile,
        LogicalProofCompilation.applyTerms, LogicalProofCompilation.applyProofs, List.foldl_cons, List.foldl_nil,
        mapTypes, mapTypes_instantiate, ExtDerivation.mapTypes_weakenHyps, mapTypes_weaken, Ty.substitute] using
        (HOLLogicalProofInference.andER (annotations left) (annotations right) (normal _) (normal _) (contexts _) (ih child))
  | @orIL ctx hyps left right inner ih =>
      intro declared
      have child := fun domain result (member : (domain, result) ∈ functionalTypes inner) => declared domain result
        (by simpa only [functionalTypes] using member)
      simpa only [ProofSyntax.mapTypes, compile_castIndices, ProofCompilation.compile,
        LogicalProofCompilation.applyTerms, LogicalProofCompilation.applyProofs, List.foldl_cons, List.foldl_nil,
        mapTypes, mapTypes_instantiate, ExtDerivation.mapTypes_weakenHyps, mapTypes_weaken, Ty.substitute] using
        (HOLLogicalProofInference.orIL (annotations left) (annotations right) (normal _) (normal _) (contexts _) (ih child))
  | @orIR ctx hyps left right inner ih =>
      intro declared
      have child := fun domain result (member : (domain, result) ∈ functionalTypes inner) => declared domain result
        (by simpa only [functionalTypes] using member)
      simpa only [ProofSyntax.mapTypes, compile_castIndices, ProofCompilation.compile,
        LogicalProofCompilation.applyTerms, LogicalProofCompilation.applyProofs, List.foldl_cons, List.foldl_nil,
        mapTypes, mapTypes_instantiate, ExtDerivation.mapTypes_weakenHyps, mapTypes_weaken, Ty.substitute] using
        (HOLLogicalProofInference.orIR (annotations left) (annotations right) (normal _) (normal _) (contexts _) (ih child))
  | @impI ctx hyps premise conclusion inner ih =>
      intro declared
      have child := fun domain result (member : (domain, result) ∈ functionalTypes inner) => declared domain result
        (by simpa only [functionalTypes] using member)
      simpa only [ProofSyntax.mapTypes, compile_castIndices, ProofCompilation.compile,
        LogicalProofCompilation.applyTerms, LogicalProofCompilation.applyProofs, List.foldl_cons, List.foldl_nil,
        mapTypes, mapTypes_instantiate, ExtDerivation.mapTypes_weakenHyps, mapTypes_weaken, Ty.substitute] using
        (HOLProofInference.impI (annotations premise) (normal _) (ih child))
  | @notI ctx hyps premise inner ih =>
      intro declared
      have child := fun domain result (member : (domain, result) ∈ functionalTypes inner) => declared domain result
        (by simpa only [functionalTypes] using member)
      simpa only [ProofSyntax.mapTypes, compile_castIndices, ProofCompilation.compile,
        LogicalProofCompilation.applyTerms, LogicalProofCompilation.applyProofs, List.foldl_cons, List.foldl_nil,
        mapTypes, mapTypes_instantiate, ExtDerivation.mapTypes_weakenHyps, mapTypes_weaken, Ty.substitute] using
        (HOLLogicalProofInference.notI (annotations premise) (normal _) (ih child))
  | @allI ctx hyps domain body inner ih =>
      intro declared
      have child := fun domain result (member : (domain, result) ∈ functionalTypes inner) => declared domain result
        (by simpa only [functionalTypes] using member)
      have bodyInferred := HOLProofInference.of_assumptions_eq
        (ExtDerivation.mapTypes_weakenHyps types constants hyps) (ih child)
      simpa only [ProofSyntax.mapTypes, compile_castIndices, ProofCompilation.compile,
        LogicalProofCompilation.applyTerms, LogicalProofCompilation.applyProofs, List.foldl_cons, List.foldl_nil,
        mapTypes, mapTypes_instantiate, ExtDerivation.mapTypes_weakenHyps, mapTypes_weaken, Ty.substitute] using
        (HOLProofInference.allI (formed domain) bodyInferred)
  | @allE ctx hyps domain body argument inner ih =>
      intro declared
      have child := fun domain result (member : (domain, result) ∈ functionalTypes inner) => declared domain result
        (by simpa only [functionalTypes] using member)
      simpa only [ProofSyntax.mapTypes, compile_castIndices, ProofCompilation.compile,
        LogicalProofCompilation.applyTerms, LogicalProofCompilation.applyProofs, List.foldl_cons, List.foldl_nil,
        mapTypes, mapTypes_instantiate, ExtDerivation.mapTypes_weakenHyps, mapTypes_weaken, Ty.substitute] using
        (HOLProofInference.allE (mapTypes types constants argument) (annotations argument) (normal _) (contexts _) (ih child))
  | @exI ctx hyps domain predicate argument inner ih =>
      intro declared
      have child := fun domain result (member : (domain, result) ∈ functionalTypes inner) => declared domain result
        (by simpa only [functionalTypes] using member)
      have bodyInferred := HOLProofInference.of_conclusion_eq
        (mapTypes_instantiate types constants argument predicate) (ih child)
      simpa only [ProofSyntax.mapTypes, compile_castIndices, ProofCompilation.compile,
        LogicalProofCompilation.applyTerms, LogicalProofCompilation.applyProofs, List.foldl_cons, List.foldl_nil,
        mapTypes, mapTypes_instantiate, ExtDerivation.mapTypes_weakenHyps, mapTypes_weaken, Ty.substitute] using
        (HOLExistentialProofInference.exI (mapTypes types constants argument) (formed domain) (annotations (.lam predicate)) (annotations argument) (normal _) (normal _) (contexts _) bodyInferred)
  | @eqSymm ctx hyps type left right inner ih =>
      intro declared
      have child := fun domain result (member : (domain, result) ∈ functionalTypes inner) => declared domain result
        (by simpa only [functionalTypes] using member)
      simpa only [ProofSyntax.mapTypes, compile_castIndices, ProofCompilation.compile,
        LogicalProofCompilation.applyTerms, LogicalProofCompilation.applyProofs, List.foldl_cons, List.foldl_nil,
        mapTypes, mapTypes_instantiate, ExtDerivation.mapTypes_weakenHyps, mapTypes_weaken, Ty.substitute] using
        (HOLEqualityProofInference.eqSymm (formed type) (annotations left) (annotations right) (normal _) (normal _) (contexts _) (ih child))
  | @eqPropEL ctx hyps left right inner ih =>
      intro declared
      have child := fun domain result (member : (domain, result) ∈ functionalTypes inner) => declared domain result
        (by simpa only [functionalTypes] using member)
      simpa only [ProofSyntax.mapTypes, compile_castIndices, ProofCompilation.compile,
        LogicalProofCompilation.applyTerms, LogicalProofCompilation.applyProofs, List.foldl_cons, List.foldl_nil,
        mapTypes, mapTypes_instantiate, ExtDerivation.mapTypes_weakenHyps, mapTypes_weaken, Ty.substitute] using
        (HOLEqualityProofInference.eqPropEL (annotations left) (annotations right) (normal _) (normal _) (contexts _) (ih child))
  | @eqPropER ctx hyps left right inner ih =>
      intro declared
      have child := fun domain result (member : (domain, result) ∈ functionalTypes inner) => declared domain result
        (by simpa only [functionalTypes] using member)
      simpa only [ProofSyntax.mapTypes, compile_castIndices, ProofCompilation.compile,
        LogicalProofCompilation.applyTerms, LogicalProofCompilation.applyProofs, List.foldl_cons, List.foldl_nil,
        mapTypes, mapTypes_instantiate, ExtDerivation.mapTypes_weakenHyps, mapTypes_weaken, Ty.substitute] using
        (HOLEqualityProofInference.eqPropER (annotations left) (annotations right) (normal _) (normal _) (contexts _) (ih child))
  | @eqApp ctx hyps domain result left right argument inner ih =>
      intro declared
      have child := fun domain result (member : (domain, result) ∈ functionalTypes inner) => declared domain result
        (by simpa only [functionalTypes] using member)
      simpa only [ProofSyntax.mapTypes, compile_castIndices, ProofCompilation.compile,
        LogicalProofCompilation.applyTerms, LogicalProofCompilation.applyProofs, List.foldl_cons, List.foldl_nil,
        mapTypes, mapTypes_instantiate, ExtDerivation.mapTypes_weakenHyps, mapTypes_weaken, Ty.substitute] using
        (HOLEqualityProofInference.eqApp (mapTypes types constants argument) (formed domain) (formed result) (annotations left) (annotations right) (annotations argument) (normal _) (normal _) (normal _) (contexts _) (ih child))
  | @eqAppArg ctx hyps domain result function left right inner ih =>
      intro declared
      have child := fun domain result (member : (domain, result) ∈ functionalTypes inner) => declared domain result
        (by simpa only [functionalTypes] using member)
      simpa only [ProofSyntax.mapTypes, compile_castIndices, ProofCompilation.compile,
        LogicalProofCompilation.applyTerms, LogicalProofCompilation.applyProofs, List.foldl_cons, List.foldl_nil,
        mapTypes, mapTypes_instantiate, ExtDerivation.mapTypes_weakenHyps, mapTypes_weaken, Ty.substitute] using
        (HOLEqualityProofInference.eqAppArg (mapTypes types constants function) (formed domain) (formed result) (annotations function) (annotations left) (annotations right) (normal _) (normal _) (normal _) (contexts _) (ih child))
  | @andI ctx hyps left right one two ihOne ihTwo =>
      intro declared
      have first := ihOne (fun domain result member => declared domain result
        (List.mem_append_left _ member))
      have second := ihTwo (fun domain result member => declared domain result
        (List.mem_append_right _ member))
      simpa only [ProofSyntax.mapTypes, ProofCompilation.compile,
        LogicalProofCompilation.applyTerms, LogicalProofCompilation.applyProofs, List.foldl_cons, List.foldl_nil, mapTypes] using
        (HOLLogicalProofInference.andI (annotations left) (annotations right)
          (normal _) (normal _) (contexts _) first second)
  | @impE ctx hyps premise conclusion one two ihOne ihTwo =>
      intro declared
      have first := ihOne (fun domain result member => declared domain result
        (List.mem_append_left _ member))
      have second := ihTwo (fun domain result member => declared domain result
        (List.mem_append_right _ member))
      exact HOLProofInference.impE first second
  | @notE ctx hyps premise one two ihOne ihTwo =>
      intro declared
      have first := ihOne (fun domain result member => declared domain result
        (List.mem_append_left _ member))
      have second := ihTwo (fun domain result member => declared domain result
        (List.mem_append_right _ member))
      exact HOLLogicalProofInference.notE first second
  | @exE ctx hyps domain predicate conclusion one two ihOne ihTwo =>
      intro declared
      have first := ihOne (fun domain result member => declared domain result
        (List.mem_append_left _ member))
      have second := ihTwo (fun domain result member => declared domain result
        (List.mem_append_right _ member))
      have sameContext : (predicate :: weakenHyps hyps).map (mapTypes types constants) =
          mapTypes types constants predicate ::
            weakenHyps (hyps.map (mapTypes types constants)) := by
        exact congrArg (List.cons (mapTypes types constants predicate))
          (ExtDerivation.mapTypes_weakenHyps types constants hyps)
      have branch := HOLProofInference.of_conclusion_eq (mapTypes_weaken types constants conclusion)
        (HOLProofInference.of_assumptions_eq sameContext second)
      simpa only [ProofSyntax.mapTypes, compile_castIndices, ProofCompilation.compile,
        LogicalProofCompilation.applyTerms, LogicalProofCompilation.applyProofs, List.foldl_cons, List.foldl_nil,
        mapTypes, ExtDerivation.mapTypes_weakenHyps, mapTypes_weaken, Ty.substitute] using
        (HOLExistentialProofInference.exE (formed domain) (annotations (.lam predicate))
          (annotations predicate) (annotations conclusion) (normal _) (normal _) (normal _)
          (contexts _) first branch)
  | @eqTrans ctx hyps type first second third one two ihOne ihTwo =>
      intro declared
      have left := ihOne (fun domain result member => declared domain result
        (List.mem_append_left _ member))
      have right := ihTwo (fun domain result member => declared domain result
        (List.mem_append_right _ member))
      simpa only [ProofSyntax.mapTypes, ProofCompilation.compile,
        LogicalProofCompilation.applyTerms, LogicalProofCompilation.applyProofs, List.foldl_cons, List.foldl_nil, mapTypes] using
        (HOLEqualityProofInference.eqTrans (formed type) (annotations first) (annotations second)
          (annotations third) (normal _) (normal _) (normal _) (contexts _) left right)
  | @eqPropI ctx hyps left right one two ihOne ihTwo =>
      intro declared
      have first := ihOne (fun domain result member => declared domain result
        (List.mem_append_left _ member))
      have second := ihTwo (fun domain result member => declared domain result
        (List.mem_append_right _ member))
      simpa only [ProofSyntax.mapTypes, ProofCompilation.compile,
        LogicalProofCompilation.applyTerms, LogicalProofCompilation.applyProofs, List.foldl_cons, List.foldl_nil, mapTypes] using
        (HOLExtensionalityProofInference.eqPropI (annotations left) (annotations right)
          (normal _) (normal _) (contexts _)
          (HOLExtensionalityProofInference.known_propositional propositionalDeclared) first second)
  | @orE ctx hyps left right conclusion cases leftBranch rightBranch ihCases ihLeft ihRight =>
      intro declared
      have first := ihCases (fun domain result member => declared domain result
        (List.mem_append_left _ (List.mem_append_left _ member)))
      have second := ihLeft (fun domain result member => declared domain result
        (List.mem_append_left _ (List.mem_append_right _ member)))
      have third := ihRight (fun domain result member => declared domain result
        (List.mem_append_right _ member))
      simpa only [ProofSyntax.mapTypes, ProofCompilation.compile,
        LogicalProofCompilation.applyTerms, LogicalProofCompilation.applyProofs, List.foldl_cons, List.foldl_nil, mapTypes] using
        (HOLLogicalProofInference.orE (annotations left) (annotations right) (annotations conclusion)
          (normal _) (normal _) (normal _) (contexts _) first second third)
  | @eqRefl ctx hyps type value =>
      intro _
      exact HOLEqualityProofInference.eqRefl _ (formed type) (annotations value) (normal _) (contexts _)
  | @beta ctx hyps domain result argument body =>
      intro _
      have argumentFormed := annotations (instantiate argument body)
      rw [mapTypes_instantiate] at argumentFormed
      simpa only [ProofSyntax.mapTypes, compile_castIndices, ProofCompilation.compile,
        mapTypes, mapTypes_instantiate] using
        (HOLEqualityProofInference.beta (mapTypes types constants body) (mapTypes types constants argument)
          (formed result) argumentFormed (normal _) (contexts _))
  | @eta ctx hyps domain result function =>
      intro _
      simpa only [ProofSyntax.mapTypes, compile_castIndices, ProofCompilation.compile,
        mapTypes, mapTypes_weaken, Var.mapTypes] using
        (HOLEqualityProofInference.eta (mapTypes types constants function)
          (formed (domain ⇒ result)) (annotations function) (normal _) (contexts _))
  | @eqLam ctx hyps domain result left right inner ih =>
      intro declared
      have child := ih (fun first second member => declared first second (List.mem_cons_of_mem _ member))
      have license := HOLExtensionalityProofInference.known_functional
        (depth := depth) (assumptions := hyps.map (mapTypes types constants))
        (declared domain result (List.mem_cons_self))
      have branch := HOLProofInference.of_assumptions_eq
        (ExtDerivation.mapTypes_weakenHyps types constants hyps) child
      simpa only [ProofSyntax.mapTypes, compile_castIndices, ProofCompilation.compile,
        LogicalProofCompilation.applyTerms, List.foldl_cons, List.foldl_nil, mapTypes, ExtDerivation.mapTypes_weakenHyps, Ty.substitute] using
        (HOLExtensionalityProofInference.eqLam (formed domain) (annotations (.lam left))
          (annotations (.lam right)) (normal _) (normal _) (contexts _) license branch)
  | @funExt ctx hyps domain result left right inner ih =>
      intro declared
      have child := ih (fun first second member => declared first second (List.mem_cons_of_mem _ member))
      have license := HOLExtensionalityProofInference.known_functional
        (depth := depth) (assumptions := hyps.map (mapTypes types constants))
        (declared domain result (List.mem_cons_self))
      have sameConclusion : mapTypes types constants
          (.all (.eq (.app (weaken left) (.var .vz)) (.app (weaken right) (.var .vz)))) =
          Term.all (.eq (.app (weaken (mapTypes types constants left)) (.var .vz))
            (.app (weaken (mapTypes types constants right)) (.var .vz))) := by
        simp only [mapTypes, mapTypes_weaken, Var.mapTypes]
      have pointwise := HOLProofInference.of_conclusion_eq sameConclusion child
      simpa only [ProofSyntax.mapTypes, compile_castIndices, ProofCompilation.compile,
        LogicalProofCompilation.applyTerms, List.foldl_cons, List.foldl_nil, mapTypes, mapTypes_weaken, Var.mapTypes, Ty.substitute] using
        (HOLExtensionalityProofInference.funExt (annotations left) (annotations right)
          (normal _) (normal _) (contexts _) license pointwise)

#print axioms compile_castIndices
#print axioms inferred

end Mettapedia.Languages.Megalodon.HOLProofCompilationCorrectness
