import Mettapedia.Languages.MM0.HOLSyntaxWire
import Mettapedia.Logic.HOL.ProofSyntax

/-!
# Retained HOL proofs exported to the maintained MM0 HOL presentation

The producer uses the rules and proved lemmas of `examples/hol.mm1`.
Typing premises, ordered source hypotheses and binder names are supplied
explicitly. All retained proof constructors have executable branches.

The output is untrusted MM1 proof text. Acceptance belongs to the existing
MM0 checker, against an independently printed statement; rendering alone
does not establish a checker-refinement theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.HOLProofExport

open Mettapedia.Logic.HOL
open HOLSyntaxWire

universe u v
variable {Base : Type u} {Const : Ty Base → Type v}

/-- An MM1 theorem application, with its premise proofs in source order. -/
def call (rule : String) (proofs : List String := []) : String :=
  "(" ++ String.intercalate " " (rule :: proofs) ++ ")"

def weakenText (proof : String) : String := call "anwl" [proof]

/-- Select the bound name in an existing MM1 rule. -/
def bind (rule name : String) (proofs : List String) : String :=
  "(!! " ++ rule ++ " " ++ name ++ " " ++ String.intercalate " " proofs ++ ")"

/-- The proof text available at one source term context. No typing authority
is inferred from a printed name. -/
structure Context (Const : Ty Base → Type v) (gamma : Ctx Base) where
  names : Names gamma
  varProofs : ∀ {type}, Var gamma type → String
  constants : ∀ {type}, Const type → String
  /-- Projection from the current proof assumptions to its formation context. -/
  projection : String := "id"

def Context.under {gamma : Ctx Base} (context : Context Const gamma) : Context Const gamma where
  names := context.names
  varProofs := context.varProofs
  constants := context.constants
  projection := weakenText context.projection

def Context.extend {gamma : Ctx Base} (context : Context Const gamma)
    (name : String) (type : Ty Base) : Context Const (type :: gamma) where
  names := Names.lift name context.names
  varProofs := fun index => match index with
    | .vz => "anr"
    | .vs index => weakenText (context.varProofs index)
  constants := fun symbol => weakenText (context.constants symbol)
  projection := call "ian" [weakenText context.projection, "anr"]

/-- Formation proofs are constructed before introducing logical assumptions.
This retains MM0's literal binder-independence conditions. -/
def Context.promote {gamma : Ctx Base} (context : Context Const gamma) (proof : String) : String :=
  if context.projection = "id" then proof else call "syl" [context.projection, proof]

def Context.promoteUnder {gamma : Ctx Base} (context : Context Const gamma) (proof : String) : String :=
  if context.projection = "id" then proof else
    call "syl" [call "ian" [weakenText context.projection, "anr"], proof]

/-- Structural source typing exported through the presentation's actual
typing rules, including every logical term constructor. -/
def typing (fresh : Nat → String) : {gamma : Ctx Base} → {type : Ty Base} →
    Context Const gamma → Nat → Term Const gamma type → String
  | _, _, context, _, .var index => context.varProofs index
  | _, _, context, _, .const symbol => context.constants symbol
  | _, _, context, depth, .app function argument =>
      call "appT" [typing fresh context depth function, typing fresh context depth argument]
  | _, _, context, depth, .lam (σ := domain) body =>
      bind "lamT" (fresh depth) [typing fresh (context.extend (fresh depth) domain) (depth + 1) body]
  | _, _, _, _, .top => "TT"
  | _, _, _, _, .bot => "FT"
  | _, _, context, depth, .and first second =>
      call "andcT" [typing fresh context depth first, typing fresh context depth second]
  | _, _, context, depth, .or first second =>
      call "orcT" [typing fresh context depth first, typing fresh context depth second]
  | _, _, context, depth, .imp first second =>
      call "impcT" [typing fresh context depth first, typing fresh context depth second]
  | _, _, context, depth, .not body => call "notcT" [typing fresh context depth body]
  | _, _, context, depth, .eq first second =>
      call "eqcT" [typing fresh context depth first, typing fresh context depth second]
  | _, _, context, depth, .all (σ := domain) body =>
      bind "allcT" (fresh depth) [typing fresh (context.extend (fresh depth) domain) (depth + 1) body]
  | _, _, context, depth, .ex (σ := domain) body =>
      bind "excT" (fresh depth) [typing fresh (context.extend (fresh depth) domain) (depth + 1) body]

def typed (fresh : Nat → String) {gamma : Ctx Base} {type : Ty Base}
    (context : Context Const gamma) (depth : Nat) (term : Term Const gamma type) : String :=
  context.promote (typing fresh context depth term)

/-- Introduce one variable using an explicit typing proof in the new native context. -/
def Context.extendAs {gamma : Ctx Base} (context : Context Const gamma)
    (name : String) (type : Ty Base) (headProof : String) : Context Const (type :: gamma) where
  names := Names.lift name context.names
  varProofs := fun index => match index with
    | .vz => headProof
    | .vs index => weakenText (context.varProofs index)
  constants := fun symbol => weakenText (context.constants symbol)

/-- The two bound names of the maintained change-of-variable lemma. -/
def bindTwo (rule first second : String) (proofs : List String) : String :=
  "(!! " ++ rule ++ " " ++ first ++ " " ++ second ++ " " ++ String.intercalate " " proofs ++ ")"

/-- Binder congruence with a literal common name, or the presentation's proved
change-of-variable rule when the two names differ. -/
def binderCongruence (first second : String) (typedFirst typedSecond same other : String) : String :=
  if first = second then bind "leq" first [same]
  else bindTwo "cbv" first second [typedFirst, typedSecond, other]

/-- Structural congruence for two substitutions and two binder namings.
The supplied variable equations are the leaves; binder changes are proved
using `cbv`, rather than assumed to be native definitional equality. -/
def congruence (leftFresh rightFresh : Nat → String) :
    {gamma : Ctx Base} → {type : Ty Base} →
    Context Const gamma → Context Const gamma →
    (∀ {type}, Var gamma type → String) → Nat → Nat → Term Const gamma type → String
  | _, _, _, _, entries, _, _, .var index => entries index
  | _, _, first, _, _, _, _, .const symbol => call "refl" [first.constants symbol]
  | _, _, first, second, entries, leftDepth, rightDepth, .app function argument =>
      call "aeq" [congruence leftFresh rightFresh first second entries leftDepth rightDepth function,
        congruence leftFresh rightFresh first second entries leftDepth rightDepth argument]
  | _, _, first, second, entries, leftDepth, rightDepth, .lam (σ := domain) body =>
      binderCongruence (leftFresh leftDepth) (rightFresh rightDepth)
        (typing leftFresh (first.extend (leftFresh leftDepth) domain) (leftDepth + 1) body)
        (typing rightFresh (second.extend (rightFresh rightDepth) domain) (rightDepth + 1) body)
        (congruence leftFresh rightFresh (first.extend (leftFresh leftDepth) domain)
          (second.extend (rightFresh rightDepth) domain) (liftEqualities entries)
          (leftDepth + 1) (rightDepth + 1) body)
        (congruence leftFresh rightFresh
          (first.extendAs (leftFresh leftDepth) domain (call "eqR1" ["anr"]))
          (second.extendAs (rightFresh rightDepth) domain (call "eqR2" ["anr"]))
          (liftRelated entries) (leftDepth + 1) (rightDepth + 1) body)
  | _, _, _, _, _, _, _, .top => call "refl" ["TT"]
  | _, _, _, _, _, _, _, .bot => call "refl" ["FT"]
  | _, _, first, second, entries, leftDepth, rightDepth, .and left right =>
      call "bineq" ["andT", congruence leftFresh rightFresh first second entries leftDepth rightDepth left,
        congruence leftFresh rightFresh first second entries leftDepth rightDepth right]
  | _, _, first, second, entries, leftDepth, rightDepth, .or left right =>
      call "bineq" ["orT", congruence leftFresh rightFresh first second entries leftDepth rightDepth left,
        congruence leftFresh rightFresh first second entries leftDepth rightDepth right]
  | _, _, first, second, entries, leftDepth, rightDepth, .imp left right =>
      call "bineq" ["impT", congruence leftFresh rightFresh first second entries leftDepth rightDepth left,
        congruence leftFresh rightFresh first second entries leftDepth rightDepth right]
  | _, _, first, second, entries, leftDepth, rightDepth, .not body =>
      call "aeq2" ["notT", congruence leftFresh rightFresh first second entries leftDepth rightDepth body]
  | _, _, first, second, entries, leftDepth, rightDepth, .eq left right =>
      call "bineq" ["eqT", congruence leftFresh rightFresh first second entries leftDepth rightDepth left,
        congruence leftFresh rightFresh first second entries leftDepth rightDepth right]
  | _, _, first, second, entries, leftDepth, rightDepth, .all (σ := domain) body =>
      call "aeq2" ["allT", binderCongruence (leftFresh leftDepth) (rightFresh rightDepth)
        (typing leftFresh (first.extend (leftFresh leftDepth) domain) (leftDepth + 1) body)
        (typing rightFresh (second.extend (rightFresh rightDepth) domain) (rightDepth + 1) body)
        (congruence leftFresh rightFresh (first.extend (leftFresh leftDepth) domain)
          (second.extend (rightFresh rightDepth) domain) (liftEqualities entries)
          (leftDepth + 1) (rightDepth + 1) body)
        (congruence leftFresh rightFresh
          (first.extendAs (leftFresh leftDepth) domain (call "eqR1" ["anr"]))
          (second.extendAs (rightFresh rightDepth) domain (call "eqR2" ["anr"]))
          (liftRelated entries) (leftDepth + 1) (rightDepth + 1) body)]
  | _, _, first, second, entries, leftDepth, rightDepth, .ex (σ := domain) body =>
      call "aeq2" ["exT", binderCongruence (leftFresh leftDepth) (rightFresh rightDepth)
        (typing leftFresh (first.extend (leftFresh leftDepth) domain) (leftDepth + 1) body)
        (typing rightFresh (second.extend (rightFresh rightDepth) domain) (rightDepth + 1) body)
        (congruence leftFresh rightFresh (first.extend (leftFresh leftDepth) domain)
          (second.extend (rightFresh rightDepth) domain) (liftEqualities entries)
          (leftDepth + 1) (rightDepth + 1) body)
        (congruence leftFresh rightFresh
          (first.extendAs (leftFresh leftDepth) domain (call "eqR1" ["anr"]))
          (second.extendAs (rightFresh rightDepth) domain (call "eqR2" ["anr"]))
          (liftRelated entries) (leftDepth + 1) (rightDepth + 1) body)]
where
  liftEqualities {gamma : Ctx Base} {domain : Ty Base}
      (entries : ∀ {type}, Var gamma type → String) :
      ∀ {type}, Var (domain :: gamma) type → String
    | _, .vz => call "refl" ["anr"]
    | _, .vs index => weakenText (entries index)
  liftRelated {gamma : Ctx Base} {domain : Ty Base}
      (entries : ∀ {type}, Var gamma type → String) :
      ∀ {type}, Var (domain :: gamma) type → String
    | _, .vz => "anr"
    | _, .vs index => weakenText (entries index)

/-- Alpha-renaming is witnessed by a logical equality proof. -/
def alpha (leftFresh rightFresh : Nat → String) {gamma : Ctx Base} {type : Ty Base}
    (context : Context Const gamma) (leftDepth rightDepth : Nat) (term : Term Const gamma type) : String :=
  congruence leftFresh rightFresh context context
    (fun index => call "refl" [context.varProofs index]) leftDepth rightDepth term

/-- A disjoint naming family for temporary instantiation binders. -/
def temporary (depth index : Nat) : String := "inst" ++ toString depth ++ "_" ++ toString index

/-- Move between depths through a disjoint name family. Directly shifting
nested binder names can identify an inner name with an outer one. -/
def rebind (fresh : Nat → String) {gamma : Ctx Base} {type : Ty Base}
    (context : Context Const gamma) (sourceDepth targetDepth : Nat) (term : Term Const gamma type) : String :=
  let middle := fun index => "rename" ++ toString sourceDepth ++ "_" ++ toString index
  call "trans" [alpha fresh middle context sourceDepth sourceDepth term,
    alpha middle fresh context sourceDepth targetDepth term]

def rootName (fresh : Nat → String) (depth : Nat) (name : String) (index : Nat) : String :=
  if index = depth then name else fresh index

/-- Under `x = argument`, prove actual simultaneous instantiation through
all constructors, including the changed names of inner binders. -/
def instantiateEquality (leftFresh rightFresh : Nat → String)
    {gamma : Ctx Base} {domain type : Ty Base}
    (context : Context Const gamma) (depth : Nat) (body : Term Const (domain :: gamma) type) : String :=
  congruence leftFresh rightFresh
    (context.extendAs (leftFresh depth) domain (call "eqR1" ["anr"]))
    (context.extendAs (leftFresh depth) domain (call "eqR2" ["anr"]))
    (congruence.liftRelated.{u, v} (fun index => call "refl" [context.varProofs index]))
    (depth + 1) depth body

def specialize (fresh : Nat → String) {gamma : Ctx Base} {domain : Ty Base}
    (context : Context Const gamma) (depth : Nat) (argument : Term Const gamma domain)
    (body : Formula Const (domain :: gamma)) (proof : String) : String :=
  let temporaryFresh := temporary depth
  bind "SPEC" (temporaryFresh depth)
    [typed fresh context depth argument,
      typed fresh context depth (instantiate argument body),
      context.promoteUnder (instantiateEquality temporaryFresh fresh context depth body),
      call "eqmp" [context.promote (alpha fresh temporaryFresh context depth depth (.all body)), proof]]

/-- General beta conversion with explicit alpha and substitution proofs. -/
def beta (fresh : Nat → String) {gamma : Ctx Base} {domain type : Ty Base}
    (context : Context Const gamma) (depth : Nat) (argument : Term Const gamma domain)
    (body : Term Const (domain :: gamma) type) : String :=
  let temporaryFresh := temporary depth
  call "trans" [call "aeq1" [context.promote (alpha fresh temporaryFresh context depth depth (.lam body)),
      typed fresh context depth argument],
    bind "betac" (temporaryFresh depth)
      [typed temporaryFresh (context.extend (temporaryFresh depth) domain) (depth + 1) body,
        typed fresh context depth argument, typed fresh context depth (instantiate argument body),
        context.promoteUnder (instantiateEquality temporaryFresh fresh context depth body)]]

/-- Eta conversion keeps public binder spelling separate from the fresh
object variable used by the proof rule. -/
def eta (fresh : Nat → String) {gamma : Ctx Base} {domain type : Ty Base}
    (context : Context Const gamma) (depth : Nat) (function : Term Const gamma (domain ⇒ type)) : String :=
  let name := "etaObject" ++ toString depth
  let binderChange := context.promote (alpha fresh (rootName fresh depth name) context depth depth
    (.lam (.app (weaken function) (.var .vz))))
  let functionChange := weakenText (context.promote (rebind fresh context (depth + 1) depth function))
  call "trans" [binderChange,
    call "trans" [bind "leq" name [call "aeq1" [functionChange, "anr"]],
      bind "eta" name [typed fresh context depth function]]]

abbrev Hypotheses {gamma : Ctx Base} (assumptions : List (Formula Const gamma)) :=
  Fin assumptions.length → String

/-- Logical hypotheses keep their source occurrence while their literal
bound names are transported before a new term variable is introduced. -/
def shiftHypotheses (fresh : Nat → String) {gamma : Ctx Base}
    {assumptions : List (Formula Const gamma)} (context : Context Const gamma)
    (depth : Nat) (hypotheses : Hypotheses assumptions) : Hypotheses assumptions :=
  fun index => weakenText (call "eqmp"
    [context.promote (rebind fresh context depth (depth + 1) (assumptions.get index)), hypotheses index])

/-- Compile all 29 constructors. The hypothesis environment retains the
selected ordered source occurrence even when several formulas are equal. -/
def proof (fresh : Nat → String) : {gamma : Ctx Base} →
    {assumptions : List (Formula Const gamma)} → {conclusion : Formula Const gamma} →
    Context Const gamma → Hypotheses assumptions → Nat →
    ProofSyntax Const assumptions conclusion → String
  | _, _, _, _, hypotheses, _, .hyp occurrence => hypotheses occurrence
  | _, _, _, _, _, _, .topI => "TRUTH"
  | _, _, conclusion, context, hypotheses, depth, .botE inner =>
      call "CONTR" [typed fresh context depth conclusion, proof fresh context hypotheses depth inner]
  | _, _, _, context, hypotheses, depth, .andI first second =>
      call "CONJ" [proof fresh context hypotheses depth first, proof fresh context hypotheses depth second]
  | _, _, _, context, hypotheses, depth, .andEL inner => call "CONJUNCT1" [proof fresh context hypotheses depth inner]
  | _, _, _, context, hypotheses, depth, .andER inner => call "CONJUNCT2" [proof fresh context hypotheses depth inner]
  | _, _, _, context, hypotheses, depth, @ProofSyntax.orIL _ _ _ _ _ other inner =>
      call "DISJ1" [proof fresh context hypotheses depth inner, typed fresh context depth other]
  | _, _, _, context, hypotheses, depth, @ProofSyntax.orIR _ _ _ _ other _ inner =>
      call "DISJ2" [typed fresh context depth other, proof fresh context hypotheses depth inner]
  | _, _, conclusion, context, hypotheses, depth, .orE cases first second =>
      call "DISJ_CASES" [proof fresh context hypotheses depth cases, typed fresh context depth conclusion,
        proof fresh context.under (fun index => Fin.cases "anr" (fun index => weakenText (hypotheses index)) index) depth first,
        proof fresh context.under (fun index => Fin.cases "anr" (fun index => weakenText (hypotheses index)) index) depth second]
  | _, _, _, context, hypotheses, depth, @ProofSyntax.impI _ _ _ _ premise result inner =>
      call "DISCH" [typed fresh context depth premise, typed fresh context depth result,
        proof fresh context.under (fun index => Fin.cases "anr" (fun index => weakenText (hypotheses index)) index) depth inner]
  | _, _, _, context, hypotheses, depth, .impE function argument =>
      call "MP" [proof fresh context hypotheses depth function, proof fresh context hypotheses depth argument]
  | _, _, _, context, hypotheses, depth, @ProofSyntax.notI _ _ _ _ premise inner =>
      call "NOT_INTRO" [call "DISCH" [typed fresh context depth premise, "FT",
        proof fresh context.under (fun index => Fin.cases "anr" (fun index => weakenText (hypotheses index)) index) depth inner]]
  | _, _, _, context, hypotheses, depth, .notE negative positive =>
      call "MP" [call "NOT_ELIM" [proof fresh context hypotheses depth negative],
        proof fresh context hypotheses depth positive]
  | _, _, _, context, hypotheses, depth, @ProofSyntax.allI _ _ _ _ domain body inner =>
      let name := "object" ++ toString depth
      call "eqmpr" [context.promote (alpha fresh (rootName fresh depth name) context depth depth (.all body)),
        bind "GEN" name [proof fresh (context.extend name domain)
          (fun index => shiftHypotheses fresh context depth hypotheses (index.cast (by simp only [weakenHyps, List.length_map])))
          (depth + 1) inner]]
  | _, _, _, context, hypotheses, depth, @ProofSyntax.allE _ _ _ _ _ body argument inner =>
      specialize fresh context depth argument body (proof fresh context hypotheses depth inner)
  | _, _, _, context, hypotheses, depth, @ProofSyntax.exI _ _ _ _ domain body argument inner =>
      call "eqmpr" [context.promote (alpha fresh (temporary depth) context depth depth (.ex body)),
        bind "EXISTS" (temporary depth depth)
          [typed (temporary depth) (context.extend (temporary depth depth) domain) (depth + 1) body,
            typed fresh context depth argument, context.promoteUnder (instantiateEquality (temporary depth) fresh context depth body),
            proof fresh context hypotheses depth inner]]
  | _, _, conclusion, context, hypotheses, depth, @ProofSyntax.exE _ _ _ _ domain body _ witness inner =>
      let name := "object" ++ toString depth
      let renamedWitness := call "eqmp"
        [context.promote (alpha fresh (rootName fresh depth name) context depth depth (.ex body)),
          proof fresh context hypotheses depth witness]
      let branch := proof fresh (context.extend name domain).under
        (fun index => Fin.cases "anr"
          (fun prior => weakenText (shiftHypotheses fresh context depth hypotheses
            (prior.cast (by simp only [weakenHyps, List.length_map])))) index) (depth + 1) inner
      let restored := call "eqmpr"
        [weakenText (weakenText (context.promote (rebind fresh context depth (depth + 1) conclusion))), branch]
      bind "CHOOSE" name [typed fresh context depth conclusion, renamedWitness, restored]
  | _, _, _, context, _, depth, .eqRefl term => call "refl" [typed fresh context depth term]
  | _, _, _, context, hypotheses, depth, .eqSymm inner => call "sym" [proof fresh context hypotheses depth inner]
  | _, _, _, context, hypotheses, depth, .eqTrans first second =>
      call "trans" [proof fresh context hypotheses depth first, proof fresh context hypotheses depth second]
  | _, _, _, context, hypotheses, depth, .eqPropI first second =>
      call "IMP_ANTISYM" [proof fresh context hypotheses depth first, proof fresh context hypotheses depth second]
  | _, _, _, context, hypotheses, depth, .eqPropEL inner => call "EQ_IMP1" [proof fresh context hypotheses depth inner]
  | _, _, _, context, hypotheses, depth, .eqPropER inner => call "EQ_IMP2" [proof fresh context hypotheses depth inner]
  | _, _, _, context, hypotheses, depth, .eqApp argument inner =>
      call "aeq1" [proof fresh context hypotheses depth inner, typed fresh context depth argument]
  | _, _, _, context, hypotheses, depth, .eqAppArg function inner =>
      call "aeq2" [typed fresh context depth function, proof fresh context hypotheses depth inner]
  | _, _, _, context, hypotheses, depth, @ProofSyntax.eqLam _ _ _ _ domain _ first second inner =>
      let name := "object" ++ toString depth
      let body := proof fresh (context.extend name domain)
        (fun index => shiftHypotheses fresh context depth hypotheses (index.cast (by simp only [weakenHyps, List.length_map])))
        (depth + 1) inner
      call "trans" [context.promote (alpha fresh (rootName fresh depth name) context depth depth (.lam first)),
        call "trans" [bind "leq" name [body],
          call "sym" [context.promote (alpha fresh (rootName fresh depth name) context depth depth (.lam second))]]]
  | _, _, _, context, hypotheses, depth, @ProofSyntax.funExt _ _ _ _ domain _ first second inner =>
      let name := "point" ++ toString depth
      let extended := context.extend name domain
      let pointwise := specialize fresh extended depth (.var .vz)
        (.eq (.app (weaken (weaken first)) (.var .vz)) (.app (weaken (weaken second)) (.var .vz)))
        (weakenText (proof fresh context hypotheses depth inner))
      call "trans" [call "sym" [bind "eta" name [typed fresh context depth first]],
        call "trans" [bind "leq" name [pointwise], bind "eta" name [typed fresh context depth second]]]
  | _, _, _, context, _, depth, @ProofSyntax.beta _ _ _ _ domain _ argument body =>
      beta fresh context depth argument body
  | _, _, _, context, _, depth, .eta function => eta fresh context depth function


end Mettapedia.Languages.MM0.HOLProofExport
