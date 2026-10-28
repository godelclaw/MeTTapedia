import Mettapedia.Logic.HOL.ProofSyntaxAppend
import Mettapedia.Logic.HOL.Syntax.SubstitutionExtension
import Mettapedia.Logic.HOL.ProofSyntaxSharedRenaming

/-!
# Supplied hypothesis proofs through every retained HOL rule

Each source hypothesis occurrence receives an actual target proof. Logical
assumptions introduced under a rule remain local; object binders rename the
supplied proofs capture-safely. The construction neither selects a proof from
mere derivability nor conflates repeated hypothesis formulas.

Replacing a hypothesis can add nodes or duplicate a supplied proof tree.
The input proofs remain the provenance of that operation; the output tree
alone does not establish that its branches are independent observations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.ProofSyntax

universe u v

variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}

def HypothesisSubstitution (source target : List (Formula Const Γ)) :=
  ∀ occurrence : Fin source.length, ProofSyntax Const target (source.get occurrence)

namespace HypothesisSubstitution

variable {source target : List (Formula Const Γ)}

/-- Stored proofs retain the source occurrence order, including duplicates. -/
inductive Table (Const : Ty Base → Type v) (target : List (Formula Const Γ)) :
    List (Formula Const Γ) → Type (max u v) where
  | nil : Table Const target []
  | cons {head : Formula Const Γ} {tail : List (Formula Const Γ)}
      (proof : ProofSyntax Const target head) (rest : Table Const target tail) : Table Const target (head :: tail)

namespace Table

def get : {source : List (Formula Const Γ)} → Table Const target source → HypothesisSubstitution source target
  | _, .nil, occurrence => Fin.elim0 occurrence
  | _, .cons proof rest, occurrence => Fin.cases proof (fun prior => rest.get prior) occurrence

def ofFn : {source : List (Formula Const Γ)} → HypothesisSubstitution source target → Table Const target source
  | [], _ => .nil
  | _ :: _, substitution => .cons (substitution 0) (ofFn (fun prior => substitution prior.succ))

theorem get_ofFn (substitution : HypothesisSubstitution source target) :
    (ofFn substitution).get = substitution := by
  induction source with
  | nil => funext index; exact Fin.elim0 index
  | cons head tail ih =>
      funext index
      refine Fin.cases rfl (fun prior => ?_) index
      exact congrFun (ih (fun index => substitution index.succ)) prior

end Table

def lift (substitution : HypothesisSubstitution source target) (head : Formula Const Γ) :
    HypothesisSubstitution (head :: source) (head :: target) :=
  Fin.cases (.hyp 0) (fun occurrence => prepend head (substitution occurrence))

def weaken (substitution : HypothesisSubstitution source target) (type : Ty Base) :
    HypothesisSubstitution (weakenHyps (σ := type) source) (weakenHyps (σ := type) target) :=
  fun occurrence =>
    let original : Fin source.length :=
      occurrence.cast (by simp only [weakenHyps, List.length_map])
    castIndices rfl (by
      change HOL.weaken (source.get original) = (source.map HOL.weaken).get occurrence
      change HOL.weaken source[original.val] = (source.map HOL.weaken)[occurrence.val]
      simp only [List.getElem_map, original, Fin.val_cast])
      (ProofSyntax.renameShared Rename.weaken (substitution original))

def identity (source : List (Formula Const Γ)) : HypothesisSubstitution source source :=
  fun occurrence => .hyp occurrence

/-- Supply the two blocks by their own occurrence positions. -/
def append : (left right target : List (Formula Const Γ)) →
    HypothesisSubstitution left target → HypothesisSubstitution right target →
    HypothesisSubstitution (left ++ right) target
  | [], _, _, _, rightProofs => rightProofs
  | _ :: left, right, target, leftProofs, rightProofs =>
      Fin.cases (leftProofs 0)
        (append left right target (fun occurrence => leftProofs occurrence.succ) rightProofs)

theorem lift_free (substitution : HypothesisSubstitution source target) (head : Formula Const Γ)
    (free : ∀ occurrence, (substitution occurrence).FunctionExtensionalityFree) :
    ∀ occurrence, ((substitution.lift head) occurrence).FunctionExtensionalityFree := by
  intro occurrence
  refine Fin.cases ?_ ?_ occurrence
  · trivial
  · intro prior
    exact (functionExtensionalityFree_mono _ _).mpr (free prior)

theorem weaken_free (substitution : HypothesisSubstitution source target) (type : Ty Base)
    (free : ∀ occurrence, (substitution occurrence).FunctionExtensionalityFree) :
    ∀ occurrence, ((substitution.weaken type) occurrence).FunctionExtensionalityFree := by
  intro occurrence
  simpa only [weaken, renameShared_eq, functionExtensionalityFree_castIndices, functionExtensionalityFree_rename] using
    free (occurrence.cast (by simp only [weakenHyps, List.length_map]))

theorem append_free (left right target : List (Formula Const Γ))
    (leftProofs : HypothesisSubstitution left target) (rightProofs : HypothesisSubstitution right target)
    (leftFree : ∀ occurrence, (leftProofs occurrence).FunctionExtensionalityFree)
    (rightFree : ∀ occurrence, (rightProofs occurrence).FunctionExtensionalityFree) :
    ∀ occurrence, (append left right target leftProofs rightProofs occurrence).FunctionExtensionalityFree := by
  induction left with
  | nil => exact rightFree
  | cons head tail ih =>
      intro occurrence
      refine Fin.cases (leftFree 0) ?_ occurrence
      intro prior
      exact ih (fun index => leftProofs index.succ) (fun index => leftFree index.succ) prior

end HypothesisSubstitution

/-- A closed derivation can be used below any sequence of object binders. -/
def weakenContext {formula : ClosedFormula Const} : (context : Ctx Base) →
    ProofSyntax Const [] formula → ProofSyntax Const [] (HOL.weakenCtx context formula)
  | [], proof => proof
  | _ :: context, proof => ProofSyntax.rename Rename.weaken (weakenContext context proof)

theorem weakenContext_nodeCount {formula : ClosedFormula Const}
    (context : Ctx Base) (proof : ProofSyntax Const [] formula) :
    (weakenContext context proof).nodeCount = proof.nodeCount := by
  induction context with
  | nil => rfl
  | cons type context ih =>
      change (ProofSyntax.rename Rename.weaken (weakenContext context proof)).nodeCount = _
      rw [rename_nodeCount, ih]

def emptyOccurrenceMap (target : List (Formula Const Γ)) : OccurrenceMap [] target where
  index occurrence := Fin.elim0 occurrence
  get_eq occurrence := Fin.elim0 occurrence

/-- Materialize the finite assignment before traversing a retained proof. -/
def substCached {Ξ : Ctx Base} {Δ : List (Formula Const Γ)} {formula : Formula Const Γ}
    (substitution : Subst Const Γ Ξ) (proof : ProofSyntax Const Δ formula) :
    ProofSyntax Const (Δ.map (HOL.subst substitution)) (HOL.subst substitution formula) :=
  let table := Subst.Table.ofSubst substitution
  Eq.ndrec (motive := fun (assignment : Subst Const Γ Ξ) =>
    ProofSyntax Const (Δ.map (HOL.subst assignment)) (HOL.subst assignment formula))
    (proof.subst table.lookup) (Subst.Table.lookup_ofSubst substitution)

theorem substCached_eq {Ξ : Ctx Base} {Δ : List (Formula Const Γ)} {formula : Formula Const Γ}
    (substitution : Subst Const Γ Ξ) (proof : ProofSyntax Const Δ formula) :
    substCached substitution proof = proof.subst substitution := by
  have transport : ∀ (assignment : Subst Const Γ Ξ)
      (same : @assignment = @substitution),
      Eq.ndrec (motive := fun (assigned : Subst Const Γ Ξ) =>
        ProofSyntax Const (Δ.map (HOL.subst assigned)) (HOL.subst assigned formula))
        (proof.subst assignment) same = proof.subst substitution := by
    intro assignment same
    cases same
    rfl
  exact transport _ (Subst.Table.lookup_ofSubst substitution)

/-- Actual proof substitution, including all extensional and binder rules. -/
def substituteHypotheses {Γ : Ctx Base} {source target : List (Formula Const Γ)}
    {conclusion : Formula Const Γ} (substitution : HypothesisSubstitution source target)
    (proof : ProofSyntax Const source conclusion) : ProofSyntax Const target conclusion :=
  match proof with
  | .hyp occurrence => substitution occurrence
  | .topI => .topI
  | .botE proof => .botE (substituteHypotheses substitution proof)
  | .andI left right =>
      .andI (substituteHypotheses substitution left) (substituteHypotheses substitution right)
  | .andEL proof => .andEL (substituteHypotheses substitution proof)
  | .andER proof => .andER (substituteHypotheses substitution proof)
  | .orIL proof => .orIL (substituteHypotheses substitution proof)
  | .orIR proof => .orIR (substituteHypotheses substitution proof)
  | .orE cases left right => .orE (substituteHypotheses substitution cases)
      (substituteHypotheses (substitution.lift _) left)
      (substituteHypotheses (substitution.lift _) right)
  | .impI proof => .impI (substituteHypotheses (substitution.lift _) proof)
  | .impE function argument =>
      .impE (substituteHypotheses substitution function) (substituteHypotheses substitution argument)
  | .notI proof => .notI (substituteHypotheses (substitution.lift _) proof)
  | .notE negative positive =>
      .notE (substituteHypotheses substitution negative) (substituteHypotheses substitution positive)
  | .allI proof => .allI (substituteHypotheses (substitution.weaken _) proof)
  | .allE term proof => .allE term (substituteHypotheses substitution proof)
  | .exI term proof => .exI term (substituteHypotheses substitution proof)
  | .exE existsProof body => .exE (substituteHypotheses substitution existsProof)
      (substituteHypotheses ((substitution.weaken _).lift _) body)
  | .eqRefl term => .eqRefl term
  | .eqSymm proof => .eqSymm (substituteHypotheses substitution proof)
  | .eqTrans left right =>
      .eqTrans (substituteHypotheses substitution left) (substituteHypotheses substitution right)
  | .eqPropI forward backward => .eqPropI (substituteHypotheses substitution forward)
      (substituteHypotheses substitution backward)
  | .eqPropEL proof => .eqPropEL (substituteHypotheses substitution proof)
  | .eqPropER proof => .eqPropER (substituteHypotheses substitution proof)
  | .eqApp term proof => .eqApp term (substituteHypotheses substitution proof)
  | .eqAppArg function proof => .eqAppArg function (substituteHypotheses substitution proof)
  | .eqLam proof => .eqLam (substituteHypotheses (substitution.weaken _) proof)
  | .funExt proof => .funExt (substituteHypotheses substitution proof)
  | .beta term body => .beta term body
  | .eta function => .eta function

/-- Binder-local tables share raised supplied proofs across sibling subtrees. -/
def substituteTable {Γ : Ctx Base} {source target : List (Formula Const Γ)}
    {conclusion : Formula Const Γ} (table : HypothesisSubstitution.Table Const target source)
    (proof : ProofSyntax Const source conclusion) : ProofSyntax Const target conclusion :=
  match proof with
  | .hyp occurrence => table.get occurrence
  | .topI => .topI
  | .botE proof => .botE (substituteTable table proof)
  | .andI left right =>
      .andI (substituteTable table left) (substituteTable table right)
  | .andEL proof => .andEL (substituteTable table proof)
  | .andER proof => .andER (substituteTable table proof)
  | .orIL proof => .orIL (substituteTable table proof)
  | .orIR proof => .orIR (substituteTable table proof)
  | .orE cases left right => .orE (substituteTable table cases)
      (substituteTable (HypothesisSubstitution.Table.ofFn (table.get.lift _)) left)
      (substituteTable (HypothesisSubstitution.Table.ofFn (table.get.lift _)) right)
  | .impI proof => .impI (substituteTable (HypothesisSubstitution.Table.ofFn (table.get.lift _)) proof)
  | .impE function argument =>
      .impE (substituteTable table function) (substituteTable table argument)
  | .notI proof => .notI (substituteTable (HypothesisSubstitution.Table.ofFn (table.get.lift _)) proof)
  | .notE negative positive =>
      .notE (substituteTable table negative) (substituteTable table positive)
  | .allI proof => .allI (substituteTable (HypothesisSubstitution.Table.ofFn (table.get.weaken _)) proof)
  | .allE term proof => .allE term (substituteTable table proof)
  | .exI term proof => .exI term (substituteTable table proof)
  | .exE existsProof body => .exE (substituteTable table existsProof)
      (substituteTable (HypothesisSubstitution.Table.ofFn ((table.get.weaken _).lift _)) body)
  | .eqRefl term => .eqRefl term
  | .eqSymm proof => .eqSymm (substituteTable table proof)
  | .eqTrans left right =>
      .eqTrans (substituteTable table left) (substituteTable table right)
  | .eqPropI forward backward => .eqPropI (substituteTable table forward)
      (substituteTable table backward)
  | .eqPropEL proof => .eqPropEL (substituteTable table proof)
  | .eqPropER proof => .eqPropER (substituteTable table proof)
  | .eqApp term proof => .eqApp term (substituteTable table proof)
  | .eqAppArg function proof => .eqAppArg function (substituteTable table proof)
  | .eqLam proof => .eqLam (substituteTable (HypothesisSubstitution.Table.ofFn (table.get.weaken _)) proof)
  | .funExt proof => .funExt (substituteTable table proof)
  | .beta term body => .beta term body
  | .eta function => .eta function

theorem substituteTable_eq {source target : List (Formula Const Γ)} {conclusion : Formula Const Γ}
    (table : HypothesisSubstitution.Table Const target source) (proof : ProofSyntax Const source conclusion) :
    substituteTable table proof = substituteHypotheses table.get proof := by
  induction proof with
  | _ => simp_all only [substituteTable, substituteHypotheses, HypothesisSubstitution.Table.get_ofFn]

/-- Construct each supplied proof once before traversing the source tree. -/
def substituteHypothesesCached {Γ : Ctx Base} {source target : List (Formula Const Γ)}
    {conclusion : Formula Const Γ} (substitution : HypothesisSubstitution source target)
    (proof : ProofSyntax Const source conclusion) : ProofSyntax Const target conclusion :=
  let table := HypothesisSubstitution.Table.ofFn substitution
  substituteTable table proof

theorem substituteHypothesesCached_eq {source target : List (Formula Const Γ)}
    {conclusion : Formula Const Γ} (substitution : HypothesisSubstitution source target)
    (proof : ProofSyntax Const source conclusion) :
    substituteHypothesesCached substitution proof = substituteHypotheses substitution proof := by
  simp only [substituteHypothesesCached, substituteTable_eq, HypothesisSubstitution.Table.get_ofFn]

theorem substituteHypotheses_free {source target : List (Formula Const Γ)} {conclusion : Formula Const Γ}
    (substitution : HypothesisSubstitution source target) (proof : ProofSyntax Const source conclusion)
    (free : proof.FunctionExtensionalityFree)
    (supplied : ∀ occurrence, (substitution occurrence).FunctionExtensionalityFree) :
    (substituteHypotheses substitution proof).FunctionExtensionalityFree := by
  induction proof with
  | hyp occurrence => exact supplied occurrence
  | topI => trivial
  | eqRefl => trivial
  | beta => trivial
  | eta => exact free.elim
  | funExt => exact free.elim
  | botE _ ih => exact ih substitution free supplied
  | andEL _ ih => exact ih substitution free supplied
  | andER _ ih => exact ih substitution free supplied
  | orIL _ ih => exact ih substitution free supplied
  | orIR _ ih => exact ih substitution free supplied
  | eqSymm _ ih => exact ih substitution free supplied
  | eqPropEL _ ih => exact ih substitution free supplied
  | eqPropER _ ih => exact ih substitution free supplied
  | eqApp _ _ ih => exact ih substitution free supplied
  | eqAppArg _ _ ih => exact ih substitution free supplied
  | allE _ _ ih => exact ih substitution free supplied
  | exI _ _ ih => exact ih substitution free supplied
  | andI _ _ first second => exact ⟨first substitution free.1 supplied, second substitution free.2 supplied⟩
  | impE _ _ first second => exact ⟨first substitution free.1 supplied, second substitution free.2 supplied⟩
  | notE _ _ first second => exact ⟨first substitution free.1 supplied, second substitution free.2 supplied⟩
  | eqTrans _ _ first second => exact ⟨first substitution free.1 supplied, second substitution free.2 supplied⟩
  | eqPropI _ _ first second => exact ⟨first substitution free.1 supplied, second substitution free.2 supplied⟩
  | impI _ ih => exact ih (substitution.lift _) free (HypothesisSubstitution.lift_free _ _ supplied)
  | notI _ ih => exact ih (substitution.lift _) free (HypothesisSubstitution.lift_free _ _ supplied)
  | allI _ ih => exact ih (substitution.weaken _) free (HypothesisSubstitution.weaken_free _ _ supplied)
  | eqLam _ ih => exact ih (substitution.weaken _) free (HypothesisSubstitution.weaken_free _ _ supplied)
  | orE _ _ _ cases first second =>
      exact ⟨cases substitution free.1 supplied,
        first (substitution.lift _) free.2.1 (HypothesisSubstitution.lift_free _ _ supplied),
        second (substitution.lift _) free.2.2 (HypothesisSubstitution.lift_free _ _ supplied)⟩
  | exE _ _ first second =>
      exact ⟨first substitution free.1 supplied,
        second ((substitution.weaken _).lift _) free.2
          (HypothesisSubstitution.lift_free _ _ (HypothesisSubstitution.weaken_free _ _ supplied))⟩


theorem substituteHypotheses_erasure {source target : List (Formula Const Γ)}
    {conclusion : Formula Const Γ} (substitution : HypothesisSubstitution source target)
    (proof : ProofSyntax Const source conclusion) : ExtDerivation Const target conclusion :=
  (substituteHypotheses substitution proof).erase

end Mettapedia.Logic.HOL.ProofSyntax
