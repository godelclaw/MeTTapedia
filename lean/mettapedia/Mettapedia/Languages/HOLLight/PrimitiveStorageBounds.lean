import Mettapedia.Languages.HOLLight.PrimitiveTransport
import Mettapedia.Languages.OpenTheory.StorageSize
import Mettapedia.Languages.HOLLight.StorageSize

/-!
# Storage growth of computed HOL Light primitive expansions

The bounds use full UTF-8 and binary storage measures. Named representatives
are produced by the actual fresh-namespace algorithm; instantiation uses the
existing capture-avoiding operation. These are payload bounds, independently
of a running-time account.
-/
set_option autoImplicit false
namespace Mettapedia.Languages.HOLLight.PrimitiveStorageBounds
open Mettapedia.Languages.OpenTheory PrimitiveTransport

/-- Every displayed term carries a constructor delimiter. -/
theorem term_positive (value : DBTerm) : 0 < OpenTheory.StorageSize.term value := by
  cases value <;> simp only [OpenTheory.StorageSize.term] <;> omega

/-- Binder namespaces retain their delimiters even when components are empty. -/
theorem freshName_size (avoid : List Name) :
    OpenTheory.StorageSize.name (ReverseTranslation.freshName avoid) = ReverseTranslation.maxNamespaceLength avoid + 5 := by
  have xBytes : "x".utf8ByteSize = 1 := rfl
  simp [OpenTheory.StorageSize.name, OpenTheory.StorageSize.list, OpenTheory.StorageSize.string,
    ReverseTranslation.freshName, List.map_replicate, List.sum_replicate, xBytes]
  omega

private theorem maxNamespaceLength_le (bound : Nat) (avoid : List Name)
    (bounded : ∀ value ∈ avoid, OpenTheory.StorageSize.name value ≤ bound) :
    ReverseTranslation.maxNamespaceLength avoid ≤ bound := by
  induction avoid with
  | nil => simp [ReverseTranslation.maxNamespaceLength]
  | cons first rest ih =>
      have firstBound := (Nat.le_of_lt (OpenTheory.StorageSize.name_namespace_le first)).trans (bounded first (by simp))
      have restBound := ih (fun value member => bounded value (by simp [member]))
      simpa only [ReverseTranslation.maxNamespaceLength] using max_le firstBound restBound

/-- Fresh naming depends on the stored avoided namespaces, rather than a
numeric code for an entire term. -/
theorem freshName_size_le (bound : Nat) (avoid : List Name)
    (bounded : ∀ value ∈ avoid, OpenTheory.StorageSize.name value ≤ bound) :
    OpenTheory.StorageSize.name (ReverseTranslation.freshName avoid) ≤ bound + 5 := by
  rw [freshName_size]
  exact Nat.add_le_add_right (maxNamespaceLength_le bound avoid bounded) 5

/-- A free name's complete namespace and component occur in the input term. -/
theorem freeName_size (value : DBTerm) :
    ∀ name ∈ freeNames value, OpenTheory.StorageSize.name name ≤ OpenTheory.StorageSize.term value := by
  induction value with
  | const _ _ => simp [freeNames]
  | bound _ => simp [freeNames]
  | free sourceVar =>
      intro name member
      have same : name = sourceVar.name := by simpa [freeNames] using member
      subst name
      simp only [OpenTheory.StorageSize.term, OpenTheory.StorageSize.sourceVar]
      omega
  | app function argument first second =>
      intro name member
      rcases List.mem_append.mp member with inFunction | inArgument
      · have small := first name inFunction
        simp only [OpenTheory.StorageSize.term]
        omega
      · have small := second name inArgument
        simp only [OpenTheory.StorageSize.term]
        omega
  | abs domain body inner =>
      intro name member
      have small := inner name member
      simp only [OpenTheory.StorageSize.term]
      omega

/-- Every replaced occurrence is charged its complete copied payload; opaque
symbol provenance and type annotations stay in the account. -/
theorem instantiateAt_size (replacement : DBTerm) : ∀ (depth : Nat) (body : DBTerm),
    OpenTheory.StorageSize.term (DBTerm.instantiateAt replacement depth body) ≤
      OpenTheory.StorageSize.term body * (OpenTheory.StorageSize.term replacement + 1)
  | depth, .const symbol annotation => by
      simp only [DBTerm.instantiateAt, OpenTheory.StorageSize.term]
      nlinarith
  | depth, .free sourceVar => by
      simp only [DBTerm.instantiateAt, OpenTheory.StorageSize.term]
      nlinarith
  | depth, .bound index => by
      simp only [DBTerm.instantiateAt]
      split
      · have positive := term_positive (.bound index)
        nlinarith
      · nlinarith
  | depth, .app function argument => by
      have first := instantiateAt_size replacement depth function
      have second := instantiateAt_size replacement depth argument
      simp only [DBTerm.instantiateAt, OpenTheory.StorageSize.term] at *
      nlinarith
  | depth, .abs domain body => by
      have inner := instantiateAt_size replacement (depth + 1) body
      simp only [DBTerm.instantiateAt, OpenTheory.StorageSize.term] at *
      nlinarith

private theorem named?_size_of_names (value : DBTerm) (binders : List SourceVar)
    (source : SourceTerm) (computed : named? value binders = some source)
    (bound : Nat)
    (binderBound : ∀ binder ∈ binders, OpenTheory.StorageSize.sourceVar binder ≤ bound)
    (nameBound : ∀ name ∈ freeNames value, OpenTheory.StorageSize.name name ≤ bound) :
    OpenTheory.StorageSize.sourceTerm source ≤ OpenTheory.StorageSize.term value * (bound + 6 * OpenTheory.StorageSize.term value) := by
  induction value generalizing binders source bound with
  | const symbol annotation =>
      have same : SourceTerm.const symbol annotation = source := by simpa [named?] using computed
      subst source
      have positive := term_positive (.const symbol annotation)
      simp only [OpenTheory.StorageSize.sourceTerm, OpenTheory.StorageSize.term] at *
      nlinarith
  | free sourceVar =>
      have same : SourceTerm.var sourceVar.name sourceVar.ty = source := by simpa [named?] using computed
      subst source
      have positive := term_positive (.free sourceVar)
      simp only [OpenTheory.StorageSize.sourceTerm, OpenTheory.StorageSize.term, OpenTheory.StorageSize.sourceVar] at *
      nlinarith
  | bound index =>
      cases found : binders[index]? with
      | none => simp [named?, found] at computed
      | some binderValue =>
          have same : SourceTerm.var binderValue.name binderValue.ty = source := by simpa [named?, found] using computed
          subst source
          have small := binderBound binderValue (List.mem_of_getElem? found)
          have positive := term_positive (.bound index)
          simp only [OpenTheory.StorageSize.sourceTerm, OpenTheory.StorageSize.sourceVar] at small ⊢
          nlinarith
  | app function argument first second =>
      cases functionComputed : named? function binders with
      | none => simp [named?, functionComputed] at computed
      | some functionSource =>
          cases argumentComputed : named? argument binders with
          | none => simp [named?, functionComputed, argumentComputed] at computed
          | some argumentSource =>
              have same : SourceTerm.app functionSource argumentSource = source := by
                simpa [named?, functionComputed, argumentComputed] using computed
              subst source
              have functionBound := first binders functionSource functionComputed bound binderBound
                (fun name member => nameBound name (List.mem_append_left _ member))
              have argumentBound := second binders argumentSource argumentComputed bound binderBound
                (fun name member => nameBound name (List.mem_append_right _ member))
              simp only [OpenTheory.StorageSize.sourceTerm, OpenTheory.StorageSize.term]
              nlinarith
  | abs domain body inner =>
      let fresh := ReverseTranslation.freshName (binders.map Var.name ++ freeNames body)
      change ((named? body (⟨fresh, domain⟩ :: binders)).bind
        (fun bodySource => some (.abs fresh domain bodySource))) = some source at computed
      have freshBound : OpenTheory.StorageSize.name fresh ≤ bound + 5 := by
        apply freshName_size_le
        intro name member
        rcases List.mem_append.mp member with old | bodyName
        · obtain ⟨binder, inBinders, rfl⟩ := List.mem_map.mp old
          have small := binderBound binder inBinders
          unfold OpenTheory.StorageSize.sourceVar at small
          omega
        · exact nameBound name bodyName
      cases bodyComputed : named? body (⟨fresh, domain⟩ :: binders) with
      | none => simp only [bodyComputed, Option.bind_none, reduceCtorEq] at computed
      | some bodySource =>
          have same : SourceTerm.abs fresh domain bodySource = source := by
            simpa only [bodyComputed, Option.bind_some, Option.some.injEq] using computed
          subst source
          have bodyBound := inner (⟨fresh, domain⟩ :: binders) bodySource bodyComputed
            (bound + OpenTheory.StorageSize.ty domain + 6) (by
              intro binder member
              rcases List.mem_cons.mp member with rfl | earlier
              · simp only [OpenTheory.StorageSize.sourceVar]
                nlinarith
              · have small := binderBound binder earlier
                omega) (by
              intro name member
              have small := nameBound name member
              omega)
          simp only [OpenTheory.StorageSize.sourceTerm, OpenTheory.StorageSize.term]
          have positive := term_positive body
          nlinarith

/-- Every successful representative has quadratic growth in the full nameless
input plus its supplied binder payloads, with no typing or freshness shortcut. -/
theorem named?_size (value : DBTerm) (binders : List SourceVar)
    (source : SourceTerm) (computed : named? value binders = some source) :
    OpenTheory.StorageSize.sourceTerm source ≤
      OpenTheory.StorageSize.term value * (7 * OpenTheory.StorageSize.term value + (binders.map OpenTheory.StorageSize.sourceVar).sum) := by
  have binderBound : ∀ binder ∈ binders,
      OpenTheory.StorageSize.sourceVar binder ≤ OpenTheory.StorageSize.term value + (binders.map OpenTheory.StorageSize.sourceVar).sum := by
    intro binder member
    have small := List.single_le_sum (fun _ _ => Nat.zero_le _) (OpenTheory.StorageSize.sourceVar binder) (List.mem_map.mpr ⟨binder, member, rfl⟩)
    omega
  have nameBound : ∀ name ∈ freeNames value,
      OpenTheory.StorageSize.name name ≤ OpenTheory.StorageSize.term value + (binders.map OpenTheory.StorageSize.sourceVar).sum := by
    intro name member
    exact (freeName_size value name member).trans (Nat.le_add_right _ _)
  have bounded := named?_size_of_names value binders source computed
    (OpenTheory.StorageSize.term value + (binders.map OpenTheory.StorageSize.sourceVar).sum) binderBound nameBound
  nlinarith

/-- Total named reconstruction has the same storage bound as its successful scanner. -/
theorem named_size (value : DBTerm) (binders : List SourceVar)
    (scope : DBTerm.LooseBelow binders.length value)
    (unique : (binders.map Var.name).Nodup)
    (fresh : ∀ name ∈ freeNames value, name ∉ binders.map Var.name) :
    OpenTheory.StorageSize.sourceTerm (named value binders scope unique fresh) ≤
      OpenTheory.StorageSize.term value *
        (7 * OpenTheory.StorageSize.term value + (binders.map OpenTheory.StorageSize.sourceVar).sum) := by
  obtain ⟨source, computed, _⟩ := named?_complete value binders scope unique fresh
  have same : named value binders scope unique fresh = source := by
    unfold named
    simp only [computed, Option.get_some]
  rw [same]
  exact named?_size value binders source computed

/-- Successful source reconstruction charges the retained annotation as well as its named term. -/
theorem checkedSource?_size (value : CanonicalTerm) {source : CheckedSourceTerm}
    (computed : PrimitiveTransport.checkedSource? value = some source) :
    OpenTheory.StorageSize.checkedSource source ≤ 8 * OpenTheory.StorageSize.canonical value ^ 2 := by
  cases scanned : named? value.term [] with
  | none => simp [PrimitiveTransport.checkedSource?, scanned] at computed
  | some representative =>
      have namedBound := named?_size value.term [] representative scanned
      have original := computed
      simp only [PrimitiveTransport.checkedSource?, scanned] at computed
      change (match checked : representative.inferType with
        | some type => some (⟨representative, type, checked⟩ : CheckedSourceTerm)
        | none => none) = some source at computed
      split at computed
      · rename_i annotation typed
        have same : (⟨representative, annotation, typed⟩ : CheckedSourceTerm) = source := Option.some.inj computed
        subst source
        have exactImage := checkedSource?_exact value original
        have sameType : annotation = value.ty := congrArg CanonicalTerm.ty exactImage
        simp only [OpenTheory.StorageSize.checkedSource, OpenTheory.StorageSize.canonical,
          sameType, List.map_nil, List.sum_nil, Nat.add_zero] at namedBound ⊢
        nlinarith
      · contradiction

/-- The total checked-source algorithm retains its scanner's full payload bound. -/
theorem checkedSource_size (value : CanonicalTerm) :
    OpenTheory.StorageSize.checkedSource (PrimitiveTransport.checkedSource value) ≤
      8 * OpenTheory.StorageSize.canonical value ^ 2 := by
  obtain ⟨source, computed, _⟩ := checkedSource?_complete value
  have same : PrimitiveTransport.checkedSource value = source := by
    unfold PrimitiveTransport.checkedSource
    simp only [computed, Option.get_some]
  rw [same]
  exact checkedSource?_size value computed

/-- The fresh beta binder is bounded by the complete body and domain payloads. -/
theorem betaNeedle_size (domain : Ty) (body : DBTerm) :
    OpenTheory.StorageSize.sourceVar (betaNeedle domain body) ≤
      OpenTheory.StorageSize.term body + OpenTheory.StorageSize.ty domain + 6 := by
  have fresh := freshName_size_le (OpenTheory.StorageSize.term body) (freeNames body)
    (freeName_size body)
  simp only [betaNeedle, OpenTheory.StorageSize.sourceVar]
  omega

/-- Named primitive BETA input has quadratic storage growth. -/
theorem betaSource_size (domain : Ty) (body : DBTerm) (codomain : Ty)
    (checkedBody : body.inferType [domain] = some codomain) :
    OpenTheory.StorageSize.checkedSource (betaSource domain body codomain checkedBody) ≤
      20 * (OpenTheory.StorageSize.term body + OpenTheory.StorageSize.ty domain +
        OpenTheory.StorageSize.ty codomain + 1) ^ 2 := by
  have namedBound := named_size body [betaNeedle domain body]
    (by simpa only [List.length_singleton] using DBTerm.looseBelow_of_inferType checkedBody)
    (by simp) (by
      intro other member
      change other ∉ [(betaNeedle domain body).name]
      simp only [List.mem_singleton]
      exact fun same => betaNeedle_fresh domain body (same ▸ member))
  have needleBound := betaNeedle_size domain body
  simp only [List.map_singleton, List.sum_singleton] at namedBound
  unfold betaSource OpenTheory.StorageSize.checkedSource
  simp only [OpenTheory.StorageSize.sourceTerm]
  change 1 + (1 + (1 + OpenTheory.StorageSize.name (betaNeedle domain body).name +
    OpenTheory.StorageSize.ty domain + OpenTheory.StorageSize.sourceTerm (named body [betaNeedle domain body] _ _ _)) +
    (1 + OpenTheory.StorageSize.name (betaNeedle domain body).name + OpenTheory.StorageSize.ty domain)) +
    OpenTheory.StorageSize.ty codomain ≤ _
  simp only [OpenTheory.StorageSize.sourceVar, betaNeedle] at needleBound namedBound ⊢
  nlinarith

/-- Complete annotated beta application size. -/
theorem betaRedex_size (domain : Ty) (body : DBTerm) (codomain : Ty)
    (checkedBody : body.inferType [domain] = some codomain)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain) :
    OpenTheory.StorageSize.canonical (betaRedex domain body codomain checkedBody argument argumentType) =
      3 + OpenTheory.StorageSize.ty domain + OpenTheory.StorageSize.term body +
        OpenTheory.StorageSize.term argument.term + OpenTheory.StorageSize.ty codomain := by
  simp only [betaRedex, OpenTheory.StorageSize.canonical, OpenTheory.StorageSize.term]
  omega

/-- Substitution copies only payload already charged by the body and argument. -/
theorem betaReduced_size (domain : Ty) (body : DBTerm) (codomain : Ty)
    (checkedBody : body.inferType [domain] = some codomain)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain) :
    OpenTheory.StorageSize.canonical (betaReduced domain body codomain checkedBody argument argumentType) ≤
      1 + OpenTheory.StorageSize.term body * (OpenTheory.StorageSize.term argument.term + 1) +
        OpenTheory.StorageSize.ty codomain := by
  exact Nat.add_le_add_right (Nat.add_le_add_left (instantiateAt_size argument.term 0 body) 1) _

/-- Raw equality formation charges both open operands and their shared annotation. -/
theorem equalityDB_size (operand : Ty) (left right : DBTerm) :
    OpenTheory.StorageSize.term (CanonicalTerm.equalityDB operand left right) =
      38 + 2 * OpenTheory.StorageSize.ty operand + OpenTheory.StorageSize.term left + OpenTheory.StorageSize.term right := by
  have arrowBytes : "->".utf8ByteSize = 2 := rfl
  have boolBytes : "bool".utf8ByteSize = 4 := rfl
  have equalityBytes : "=".utf8ByteSize = 1 := rfl
  simp only [CanonicalTerm.equalityDB, OpenTheory.StorageSize.term,
    OpenTheory.StorageSize.ty, OpenTheory.StorageSize.types, OpenTheory.StorageSize.constant,
    OpenTheory.StorageSize.constantProvenance, OpenTheory.StorageSize.typeOp,
    OpenTheory.StorageSize.typeOpProvenance, OpenTheory.StorageSize.name,
    OpenTheory.StorageSize.list, OpenTheory.StorageSize.string, Ty.equality, Ty.function,
    Ty.bool, TypeOp.bool, TypeOp.function, Const.equality, Name.global,
    List.map_nil, List.sum_nil, arrowBytes, boolBytes, equalityBytes]
  omega

/-- Equality formation charges its actual constant and type annotations. -/
theorem equalityOfSameType_size (left right : CanonicalTerm) (sameType : left.ty = right.ty) :
    OpenTheory.StorageSize.canonical (CanonicalTerm.equalityOfSameType left right sameType) =
      48 + OpenTheory.StorageSize.canonical left + OpenTheory.StorageSize.canonical right := by
  have arrowBytes : "->".utf8ByteSize = 2 := rfl
  have boolBytes : "bool".utf8ByteSize = 4 := rfl
  have equalityBytes : "=".utf8ByteSize = 1 := rfl
  simp only [CanonicalTerm.equalityOfSameType, CanonicalTerm.equalityDB, OpenTheory.StorageSize.canonical,
    OpenTheory.StorageSize.term, OpenTheory.StorageSize.ty, OpenTheory.StorageSize.types,
    OpenTheory.StorageSize.constant, OpenTheory.StorageSize.constantProvenance,
    OpenTheory.StorageSize.typeOp, OpenTheory.StorageSize.typeOpProvenance,
    OpenTheory.StorageSize.name, OpenTheory.StorageSize.list, OpenTheory.StorageSize.string,
    Ty.equality, Ty.function, Ty.bool, TypeOp.bool, TypeOp.function, Const.equality, Name.global,
    List.map_nil, List.sum_nil, arrowBytes, boolBytes, equalityBytes]
  rw [sameType]
  omega

/-- The full input payload for one computed beta expansion. -/
def betaInputSize (domain : Ty) (body : DBTerm) (codomain : Ty) (argument : CanonicalTerm) : Nat :=
  OpenTheory.StorageSize.ty domain + OpenTheory.StorageSize.term body +
    OpenTheory.StorageSize.ty codomain + OpenTheory.StorageSize.canonical argument + 1

/-- Primitive BETA's intermediate redex retains the exact fresh-variable payload. -/
theorem betaSource_canonical_size (domain : Ty) (body : DBTerm) (codomain : Ty)
    (checkedBody : body.inferType [domain] = some codomain) :
    OpenTheory.StorageSize.canonical (betaSource domain body codomain checkedBody).canonical =
      4 + OpenTheory.StorageSize.ty domain + OpenTheory.StorageSize.term body +
        OpenTheory.StorageSize.sourceVar (betaNeedle domain body) + OpenTheory.StorageSize.ty codomain := by
  unfold OpenTheory.StorageSize.canonical
  rw [betaSource_term]
  simp only [OpenTheory.StorageSize.term]
  change 1 + (1 + (1 + OpenTheory.StorageSize.ty domain + OpenTheory.StorageSize.term body) +
    (1 + OpenTheory.StorageSize.sourceVar (betaNeedle domain body))) + OpenTheory.StorageSize.ty codomain = _
  omega

/-- Both beta requests retain a quadratic-size named-source payload. -/
theorem betaExpansion_source_size (domain : Ty) (body : DBTerm) (codomain : Ty)
    (checkedBody : body.inferType [domain] = some codomain)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain) :
    OpenTheory.StorageSize.checkedSource (betaExpansion domain body codomain checkedBody argument argumentType).source ≤
      20 * betaInputSize domain body codomain argument ^ 2 := by
  have bound := betaSource_size domain body codomain checkedBody
  change OpenTheory.StorageSize.checkedSource (betaSource domain body codomain checkedBody) ≤ _
  apply bound.trans
  gcongr
  unfold betaInputSize
  omega

/-- INST retains its actual singleton substitution, including both named terms. -/
theorem betaExpansion_entries_size (domain : Ty) (body : DBTerm) (codomain : Ty)
    (checkedBody : body.inferType [domain] = some codomain)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain) :
    OpenTheory.StorageSize.list StorageSize.termMaplet
      (betaExpansion domain body codomain checkedBody argument argumentType).entries ≤
      20 * betaInputSize domain body codomain argument ^ 2 := by
  have sourceBound := checkedSource_size argument
  have needleBound := betaNeedle_size domain body
  change OpenTheory.StorageSize.list StorageSize.termMaplet
    [(PrimitiveTransport.checkedSource argument,
      SourceTerm.var (betaNeedle domain body).name (betaNeedle domain body).ty)] ≤ _
  simp only [OpenTheory.StorageSize.list, List.map_singleton, List.sum_singleton,
    StorageSize.termMaplet, OpenTheory.StorageSize.sourceTerm]
  unfold OpenTheory.StorageSize.sourceVar at needleBound
  have argumentInside : OpenTheory.StorageSize.canonical argument ≤ betaInputSize domain body codomain argument := by
    unfold betaInputSize; omega
  have argumentSquared := Nat.pow_le_pow_left argumentInside 2
  have needleInside : OpenTheory.StorageSize.term body + OpenTheory.StorageSize.ty domain + 1 ≤
      betaInputSize domain body codomain argument := by unfold betaInputSize; omega
  have positive : 1 ≤ betaInputSize domain body codomain argument := by unfold betaInputSize; omega
  nlinarith

/-- The intermediate equation carries no hidden axiom or hypothesis payload. -/
theorem betaExpansion_intermediate_size (domain : Ty) (body : DBTerm) (codomain : Ty)
    (checkedBody : body.inferType [domain] = some codomain)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain) :
    OpenTheory.StorageSize.theoremData
      (betaExpansion domain body codomain checkedBody argument argumentType).intermediate ≤
      100 * betaInputSize domain body codomain argument ^ 2 := by
  let freeArgument := (CheckedSourceTerm.ofVariable (betaNeedle domain body)).canonical
  have sourceBound := betaSource_canonical_size domain body codomain checkedBody
  have needleBound := betaNeedle_size domain body
  have reducedBound := betaReduced_size domain body codomain checkedBody freeArgument rfl
  have argumentSize : OpenTheory.StorageSize.term freeArgument.term =
      1 + OpenTheory.StorageSize.sourceVar (betaNeedle domain body) := by
    simp [freeArgument, CheckedSourceTerm.ofVariable, CheckedSourceTerm.canonical,
      SourceTerm.toDB, boundIndex, OpenTheory.StorageSize.term]
  change OpenTheory.StorageSize.theoremData (Theorem.emptyResult ∅
    (CanonicalTerm.equalityOfSameType (betaSource domain body codomain checkedBody).canonical
      (betaReduced domain body codomain checkedBody freeArgument rfl) rfl)) ≤ _
  rw [OpenTheory.StorageSize.emptyResult_size, OpenTheory.StorageSize.finset_empty]
  erw [equalityOfSameType_size]
  rw [argumentSize] at reducedBound
  have bodyInside : OpenTheory.StorageSize.term body ≤ betaInputSize domain body codomain argument := by
    unfold betaInputSize; omega
  have needleInside : 1 + OpenTheory.StorageSize.sourceVar (betaNeedle domain body) + 1 ≤
      betaInputSize domain body codomain argument + 8 := by unfold betaInputSize; omega
  have codomainInside : OpenTheory.StorageSize.ty codomain ≤ betaInputSize domain body codomain argument := by
    unfold betaInputSize; omega
  have reducedLarge : OpenTheory.StorageSize.canonical (betaReduced domain body codomain checkedBody freeArgument rfl) ≤
      1 + betaInputSize domain body codomain argument * (betaInputSize domain body codomain argument + 8) +
        betaInputSize domain body codomain argument := by
    apply reducedBound.trans
    gcongr
  have sourceLarge : OpenTheory.StorageSize.canonical (betaSource domain body codomain checkedBody).canonical ≤
      2 * betaInputSize domain body codomain argument + 10 := by
    rw [sourceBound]
    unfold betaInputSize
    omega
  have positive : 1 ≤ betaInputSize domain body codomain argument := by unfold betaInputSize; omega
  nlinarith

/-- The final equation uses the original argument and capture-avoiding instantiation. -/
theorem betaExpansion_conclusion_size (domain : Ty) (body : DBTerm) (codomain : Ty)
    (checkedBody : body.inferType [domain] = some codomain)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain) :
    OpenTheory.StorageSize.theoremData
      (betaExpansion domain body codomain checkedBody argument argumentType).conclusion ≤
      80 * betaInputSize domain body codomain argument ^ 2 := by
  have redexBound := betaRedex_size domain body codomain checkedBody argument argumentType
  have reducedBound := betaReduced_size domain body codomain checkedBody argument argumentType
  have argumentBound := OpenTheory.StorageSize.canonical_term_le argument
  rw [betaExpansion_conclusion, OpenTheory.StorageSize.emptyResult_size,
    OpenTheory.StorageSize.finset_empty]
  have equalitySize := equalityOfSameType_size
    (betaRedex domain body codomain checkedBody argument argumentType)
    (betaReduced domain body codomain checkedBody argument argumentType) (by rfl)
  simp only [betaRedex, betaReduced] at equalitySize ⊢
  rw [equalitySize]
  change 3 + 1 + (48 + OpenTheory.StorageSize.canonical (betaRedex domain body codomain checkedBody argument argumentType) +
    OpenTheory.StorageSize.canonical (betaReduced domain body codomain checkedBody argument argumentType)) ≤ _
  rw [redexBound]
  unfold betaInputSize
  nlinarith

/-- The actual two-node BETA/INST certificate has a polynomial full-payload
bound, including copied intermediate theorems and the supplied origin. -/
theorem betaBlock_payload (domain : Ty) (body : DBTerm) (codomain : Ty)
    (checkedBody : body.inferType [domain] = some codomain)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain)
    (origin : ProofExecution.Origin) :
    GraphExpansion.graphWeight StorageSize.receiptPayload
      (betaBlock (betaExpansion domain body codomain checkedBody argument argumentType) origin).1 ≤
      500 * (betaInputSize domain body codomain argument + StorageSize.origin origin) ^ 2 := by
  have sourceBound := betaExpansion_source_size domain body codomain checkedBody argument argumentType
  have entriesBound := betaExpansion_entries_size domain body codomain checkedBody argument argumentType
  have intermediateBound := betaExpansion_intermediate_size domain body codomain checkedBody argument argumentType
  have conclusionBound := betaExpansion_conclusion_size domain body codomain checkedBody argument argumentType
  simp only [betaBlock, GraphExpansion.graphWeight, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, GraphExpansion.receiptWeight, StorageSize.receiptPayload,
    StorageSize.request, StorageSize.inferenceRequest, List.length_nil, List.length_cons]
  have positive : 1 ≤ betaInputSize domain body codomain argument := by unfold betaInputSize; omega
  nlinarith

/-- The local beta graph has the single parent address zero and selected root one. -/
theorem betaBlock_certificateUnits (expansion : BetaExpansion) (origin : ProofExecution.Origin) :
    StorageSize.certificateUnits (betaBlock expansion origin) =
      GraphExpansion.graphWeight StorageSize.receiptPayload (betaBlock expansion origin).1 + 3 := by
  simp only [StorageSize.certificateUnits, GraphExpansion.binaryGraphWeight,
    GraphExpansion.parentAddressBits, betaBlock, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.size_zero, Nat.add_zero]
  have rootSize : OpenTheory.StorageSize.nat 1 = 2 := rfl
  rw [rootSize]
  omega

/-- Complete local graph storage includes its selected root and binary parent address. -/
theorem betaBlock_certificateBits (domain : Ty) (body : DBTerm) (codomain : Ty)
    (checkedBody : body.inferType [domain] = some codomain)
    (argument : CanonicalTerm) (argumentType : argument.ty = domain)
    (origin : ProofExecution.Origin) :
    StorageSize.certificateBits
      (betaBlock (betaExpansion domain body codomain checkedBody argument argumentType) origin) ≤
      4032 * (betaInputSize domain body codomain argument + StorageSize.origin origin) ^ 2 := by
  have payloadBound := betaBlock_payload domain body codomain checkedBody argument argumentType origin
  rw [StorageSize.certificateBits, betaBlock_certificateUnits]
  have positive : 1 ≤ betaInputSize domain body codomain argument + StorageSize.origin origin := by
    unfold betaInputSize; omega
  nlinarith

end Mettapedia.Languages.HOLLight.PrimitiveStorageBounds
