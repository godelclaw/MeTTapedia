import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalEqualityReading
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateRoots
import Mettapedia.Logic.HOL.PredicateProductsNaturality
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalAssignmentReading
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorJudgmentReplay

/-!
# Reading primitive annotated equality instructions

Beta instructions check their annotated domain, body and argument carriers.
Natural instructions check a finite simultaneous assignment at the original
row's parameter carriers. Each successful instruction constructs a retained
HOL proof with exact source readings and no function-extensionality rule.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
namespace AnnotatedConversion.EqualityCode

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated NativeNaturalVectorFamilies

universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v} [DecidableEq Base]

def beta? (operations : Operations Base Const) (Γ : HOL.Ctx Base)
    (domain : CTm Tower.Head Γ.length) (body : CTm Tower.Head (Γ.length + 1))
    (argument : CTm Tower.Head Γ.length) :
    Option (EqualityReading operations Γ (.app (.lam domain body) argument) (CTm.inst0 argument body)) :=
  AnnotatedPredicateReading.Interpreter.beta? (evidenceOps operations) Γ domain body argument

def row? (operations : Operations Base Const) (Γ : HOL.Ctx Base) (row : Row)
    (raw : CSub Tower.Head (row.parameters operations).length Γ.length) :
    Option (EqualityReading operations Γ ((row.left operations).subst raw) ((row.right operations).subst raw)) :=
  (AnnotatedReading.readAssignment? operations (row.parameters operations) Γ raw).map
    fun assignment => ⟨operations.result, EqualityAt.row row raw assignment.val assignment.property⟩

def castEndpoints {operations : Operations Base Const} {Γ : HOL.Ctx Base}
    {source target source' target' : CTm Tower.Head Γ.length}
    (left : source = source') (right : target = target')
    (reading : EqualityReading operations Γ source target) : EqualityReading operations Γ source' target' :=
  left ▸ right ▸ reading

/-- Exact annotated endpoints are checked even if their raw erasures agree. -/
def at? {operations : Operations Base Const} {Γ : HOL.Ctx Base}
    {source target : CTm Tower.Head Γ.length}
    (left right : CTm Tower.Head Γ.length) (reading : EqualityReading operations Γ source target) :
    Option (EqualityReading operations Γ left right) :=
  if sameLeft : source = left then
    if sameRight : target = right then some (castEndpoints sameLeft sameRight reading) else none
  else none

namespace RootTable

variable (operations : Operations Base Const) (profile : Programs.ComputationProfiles.Selection)

def rawLeft : (row : Row) → Tower.Tm (row.parameters operations).length
  | .zero => natZeroIotaLeft
  | .successor => natSuccIotaLeft

def rawRight : (row : Row) → Tower.Tm (row.parameters operations).length
  | .zero => natZeroIotaRight
  | .successor => natSuccIotaRight

omit [DecidableEq Base] in
theorem left_annotated (row : Row) :
    elabLeft (Programs.Annotated.church profile).constantType (rawLeft operations row) = row.left operations := by
  cases row <;> apply elab_lamFree <;> rfl

omit [DecidableEq Base] in
theorem right_annotated (row : Row) :
    elabRight (Programs.Annotated.church profile).constantType (rawLeft operations row) (rawRight operations row) =
      row.right operations := by
  cases row <;> apply elab_lamFree <;> rfl

def template (row : Row) : AnnotatedPredicateReading.Roots.Template (lexicalReading operations)
    (closedAssumptions operations) (Programs.Annotated.church profile).constantType where
  parameters := row.parameters operations
  carrier := operations.result
  rawLeft := rawLeft operations row
  rawRight := rawRight operations row
  leftCode := row.leftCode operations
  rightCode := row.rightCode operations
  leftRead := by rw [left_annotated]; exact (row.left_reads operations).toGeneric
  rightRead := by rw [right_annotated]; exact (row.right_reads operations).toGeneric
  proof := HOL.ProofSyntax.castIndices (assumptions_eq_closed operations _) rfl (row.proof operations)

omit [DecidableEq Base] in
theorem template_free (row : Row) : (template operations profile row).proof.FunctionExtensionalityFree := by
  simpa only [template, HOL.ProofSyntax.functionExtensionalityFree_castIndices] using row.proof_free operations

/-- The actual four-row source table supplies addresses. Only its two natural
rows have retained HOL proofs in this instance. -/
def entries : AnnotatedPredicateReading.Roots.Table (lexicalReading operations)
    (closedAssumptions operations) (Programs.Annotated.church profile).constantType Checking.table
  | ⟨0, _⟩ => some ⟨template operations profile .zero, rfl⟩
  | ⟨1, _⟩ => some ⟨template operations profile .successor, rfl⟩
  | _ => none

omit [DecidableEq Base] in
theorem entries_free (address : Fin Checking.table.length) (entry)
    (known : entries operations profile address = some entry) : entry.template.proof.FunctionExtensionalityFree := by
  have count : Checking.table.length = 4 := rfl
  fin_cases address <;> simp only [entries] at known
  · cases known
    exact template_free operations profile .zero
  · cases known
    exact template_free operations profile .successor
  · cases known
  · cases known

def receipt (row : Row) (permitted : profile row.address = true) (Γ : HOL.Ctx Base)
    (raw : CSub Tower.Head (row.parameters operations).length Γ.length)
    (assignment : HOL.Subst Const (row.parameters operations) Γ)
    (represented : ∀ {type} (index : HOL.Var (row.parameters operations) type),
      AnnotatedReads operations (Γ := Γ) (raw (FormationSensitiveHOLInterface.variableIndex index)) (assignment index)) :
    AnnotatedPredicateReading.Roots.Receipt (entries operations profile) profile Γ ⟨row.address.val, List.ofFn raw⟩ := by
  cases row
  case zero =>
    refine ⟨⟨⟨0, by decide⟩, permitted, raw⟩, ?_, ⟨template operations profile .zero, rfl⟩, rfl,
      ⟨assignment, ?_⟩⟩
    · exact AnnotatedPredicateReading.Roots.decodeInstance_encode Checking.table profile ⟨0, by decide⟩ permitted raw
    · intro type index
      simpa only [AnnotatedPredicateReading.Roots.reindex, variableIndex_eq_toFin, Fin.cast_eq_self] using (represented index).toGeneric
  case successor =>
    refine ⟨⟨⟨1, by decide⟩, permitted, raw⟩, ?_, ⟨template operations profile .successor, rfl⟩, rfl,
      ⟨assignment, ?_⟩⟩
    · exact AnnotatedPredicateReading.Roots.decodeInstance_encode Checking.table profile ⟨1, by decide⟩ permitted raw
    · intro type index
      simpa only [AnnotatedPredicateReading.Roots.reindex, variableIndex_eq_toFin, Fin.cast_eq_self] using (represented index).toGeneric

def result (row : Row) (permitted : profile row.address = true) (Γ : HOL.Ctx Base)
    (raw : CSub Tower.Head (row.parameters operations).length Γ.length)
    (assignment : HOL.Subst Const (row.parameters operations) Γ)
    (represented : ∀ {type} (index : HOL.Var (row.parameters operations) type),
      AnnotatedReads operations (Γ := Γ) (raw (FormationSensitiveHOLInterface.variableIndex index)) (assignment index)) :
    AnnotatedPredicateReading.Roots.Result (entries operations profile) profile Γ
      ((row.left operations).subst raw) ((row.right operations).subst raw) ⟨row.address.val, List.ofFn raw⟩ where
  receipt := receipt operations profile row permitted Γ raw assignment represented
  leftExact := by
    cases row with
    | zero => exact congrArg (CTm.subst raw) (left_annotated operations profile .zero)
    | successor => exact congrArg (CTm.subst raw) (left_annotated operations profile .successor)
  rightExact := by
    cases row with
    | zero => exact congrArg (CTm.subst raw) (right_annotated operations profile .zero)
    | successor => exact congrArg (CTm.subst raw) (right_annotated operations profile .successor)

theorem result_read (row : Row) (permitted : profile row.address = true) (Γ : HOL.Ctx Base)
    (raw : CSub Tower.Head (row.parameters operations).length Γ.length)
    (assignment : HOL.Subst Const (row.parameters operations) Γ)
    (represented : ∀ {type} (index : HOL.Var (row.parameters operations) type),
      AnnotatedReads operations (Γ := Γ) (raw (FormationSensitiveHOLInterface.variableIndex index)) (assignment index)) :
    AnnotatedPredicateReading.Roots.read? (entries operations profile) profile Γ
      ((row.left operations).subst raw) ((row.right operations).subst raw) ⟨row.address.val, List.ofFn raw⟩ =
      some (result operations profile row permitted Γ raw assignment represented) := by
  apply AnnotatedPredicateReading.Roots.read?_complete
  exact AnnotatedPredicateReading.Roots.readReceipt?_complete _ _ _ _ _
    (receipt operations profile row permitted Γ raw assignment represented).decoded _
    (receipt operations profile row permitted Γ raw assignment represented).known _

end RootTable

def fromShared {operations : Operations Base Const} {Γ : HOL.Ctx Base} {source target : CTm Tower.Head Γ.length}
    (reading : AnnotatedPredicateReading.EqualityReading (lexicalReading operations) (closedAssumptions operations)
      Γ source target) (free : reading.2.proof.FunctionExtensionalityFree) : EqualityReading operations Γ source target :=
  ⟨reading.1, reading.2.left, reading.2.right,
    AnnotatedReads.ofGeneric reading.2.leftRead, AnnotatedReads.ofGeneric reading.2.rightRead,
    HOL.ProofSyntax.castIndices (assumptions_eq_closed operations Γ).symm rfl reading.2.proof,
    by simpa only [HOL.ProofSyntax.functionExtensionalityFree_castIndices] using free⟩

omit [DecidableEq Base] in
private theorem reading_ext {operations : Operations Base Const} {Γ : HOL.Ctx Base}
    {source target : CTm Tower.Head Γ.length} {carrier : HOL.Ty Base}
    (first second : EqualityAt operations Γ source target carrier)
    (left : first.left = second.left) (right : first.right = second.right)
    (proof : HEq first.proof second.proof) : first = second := by
  cases first
  cases second
  cases left
  cases right
  cases eq_of_heq proof
  rfl

omit [DecidableEq Base] in
theorem generic_result_agrees (operations : Operations Base Const) (profile : Programs.ComputationProfiles.Selection)
    (row : Row) (permitted : profile row.address = true) (Γ : HOL.Ctx Base)
    (raw : CSub Tower.Head (row.parameters operations).length Γ.length)
    (assignment : HOL.Subst Const (row.parameters operations) Γ)
    (represented : ∀ {type} (index : HOL.Var (row.parameters operations) type),
      AnnotatedReads operations (Γ := Γ) (raw (FormationSensitiveHOLInterface.variableIndex index)) (assignment index)) :
    fromShared (RootTable.result operations profile row permitted Γ raw assignment represented).equality
      ((RootTable.result operations profile row permitted Γ raw assignment represented).equality_free
        (RootTable.entries_free operations profile)) =
      ⟨operations.result, EqualityAt.row row raw assignment represented⟩ := by
  cases row
  all_goals
    dsimp only [fromShared, AnnotatedPredicateReading.Roots.Result.equality, RootTable.result,
      RootTable.receipt, AnnotatedPredicateReading.Roots.Receipt.equality, RootTable.template]
    apply congrArg (Sigma.mk operations.result)
    apply reading_ext
  all_goals first
    | solve | simp only [AnnotatedPredicateReading.EqualityAt.castEndpoints_left,
        AnnotatedPredicateReading.EqualityAt.castEndpoints_right, AnnotatedPredicateReading.EqualityAt.substitute,
        AnnotatedPredicateReading.Roots.Template.equality, EqualityAt.row]
    | skip
  all_goals
    dsimp only [EqualityAt.row]
    refine (HOL.ProofSyntax.castIndices_heq _ _ _).trans ?_
    refine (AnnotatedPredicateReading.EqualityAt.castEndpoints_proof _ _ _).trans ?_
    refine (AnnotatedPredicateReading.EqualityAt.castEndpoints_proof _ _ _).trans ?_
    dsimp only [AnnotatedPredicateReading.EqualityAt.substitute, AnnotatedPredicateReading.Roots.Template.equality]
    refine (HOL.ProofSyntax.castIndices_heq _ _ _).trans ?_
    refine (HOL.ProofSyntax.subst_castIndices_heq _ _ _ _).trans ?_
    exact (HOL.ProofSyntax.castIndices_heq _ _ _).symm

/-- Nat supplies table entries to the shared dispatcher. Source decoding,
permission, argument reading and endpoint checks are signature-independent. -/
def natural? (operations : Operations Base Const) (profile : Programs.ComputationProfiles.Selection)
    (Γ : HOL.Ctx Base) (source target : CTm Tower.Head Γ.length) (code : SchemaJudgmentCode.Code Tower.Head Γ.length) :
    Option (EqualityReading operations Γ source target) :=
  (AnnotatedPredicateReading.Roots.read? (RootTable.entries operations profile) profile Γ source target code).map
    (fun result => fromShared result.equality (result.equality_free (RootTable.entries_free operations profile)))

#print axioms RootTable.entries_free
#print axioms generic_result_agrees

theorem beta?_complete {operations : Operations Base Const} {Γ : HOL.Ctx Base}
    {A : CTm Tower.Head Γ.length} {body : CTm Tower.Head (Γ.length + 1)} {argument : CTm Tower.Head Γ.length}
    {domain codomain : HOL.Ty Base} {domainCode : HOL.Term Const Γ (.arr domain .prop)}
    {bodyCode : HOL.Term Const (domain :: Γ) codomain} {argumentCode : HOL.Term Const Γ domain}
    (domainRead : AnnotatedReads operations (Γ := Γ) A domainCode)
    (bodyRead : AnnotatedReads operations (Γ := domain :: Γ) body bodyCode)
    (argumentRead : AnnotatedReads operations (Γ := Γ) argument argumentCode) :
    beta? operations Γ A body argument =
      some ⟨codomain, EqualityAt.beta domainRead bodyRead argumentRead⟩ := by
  exact AnnotatedPredicateReading.Interpreter.beta?_complete (evidenceOps operations)
    domainRead.toGeneric bodyRead.toGeneric argumentRead.toGeneric

theorem row?_complete {operations : Operations Base Const} {Γ : HOL.Ctx Base} (row : Row)
    (raw : CSub Tower.Head (row.parameters operations).length Γ.length)
    (assignment : HOL.Subst Const (row.parameters operations) Γ)
    (represented : ∀ {type} (index : HOL.Var (row.parameters operations) type),
      AnnotatedReads operations (Γ := Γ) (raw (FormationSensitiveHOLInterface.variableIndex index))
        (assignment index)) :
    row? operations Γ row raw = some ⟨operations.result, EqualityAt.row row raw assignment represented⟩ := by
  simp only [row?, AnnotatedReading.readAssignment?_complete operations _ _ raw assignment represented,
    Option.map_some]

theorem natural?_complete {operations : Operations Base Const} {Γ : HOL.Ctx Base}
    (profile : Programs.ComputationProfiles.Selection) (row : Row)
    (permitted : profile row.address = true)
    (raw : CSub Tower.Head (row.parameters operations).length Γ.length)
    (assignment : HOL.Subst Const (row.parameters operations) Γ)
    (represented : ∀ {type} (index : HOL.Var (row.parameters operations) type),
      AnnotatedReads operations (Γ := Γ) (raw (FormationSensitiveHOLInterface.variableIndex index))
        (assignment index)) :
    natural? operations profile Γ ((row.left operations).subst raw) ((row.right operations).subst raw)
      ⟨row.address.val, List.ofFn raw⟩ =
      some ⟨operations.result, EqualityAt.row row raw assignment represented⟩ := by
  rw [natural?, RootTable.result_read operations profile row permitted Γ raw assignment represented, Option.map_some]
  exact congrArg some (generic_result_agrees operations profile row permitted Γ raw assignment represented)

#print axioms beta?
#print axioms row?
#print axioms natural?
#print axioms natural?_complete

end AnnotatedConversion.EqualityCode
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
