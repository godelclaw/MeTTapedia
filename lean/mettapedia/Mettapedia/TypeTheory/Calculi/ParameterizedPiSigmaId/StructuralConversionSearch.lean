import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionCodeCongruence

/-!
# Bounded production of structural conversion recipes

The producer reduces beta redexes, traverses the existing term grammar and
asks an untrusted search function for declaration-root codes. Roots are read
through the qualified decoder and must cite the actual source term. Every
returned normalization or comparison recipe is independently replayed.

Fuel exhaustion can return an intermediate term. The API promises a checked
conversion path, not a normal form, complete conversion search, or a typed
execution. Neither normalization nor subject preservation of the rule package
is assumed or established here.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace StructuralConversionSearch

variable {Head : Type} {RootCode : Nat → Type}

open StructuralConversionCode

structure Candidate (Head : Type) (RootCode : Nat → Type) (n : Nat) where
  term : Tm Head n
  recipe : Code Head RootCode n

variable [DecidableEq Head]
variable (decodeRoot : {n : Nat} → RootCode n → Option (Tm Head n × Tm Head n))
variable (searchRoot : {n : Nat} → Tm Head n → Option (RootCode n))

mutual

def produce : Nat → {n : Nat} → Tm Head n → Candidate Head RootCode n
  | 0, _, term => ⟨term, .refl term⟩
  | fuel + 1, _, term =>
      let candidate := match term with
        | .var _ | .head _ | .const _ => ⟨term, .refl term⟩
        | .pi domain body =>
            let first := produce fuel domain
            let second := produce fuel body
            ⟨.pi first.term second.term, .congPi first.term body first.recipe second.recipe⟩
        | .sigma domain body =>
            let first := produce fuel domain
            let second := produce fuel body
            ⟨.sigma first.term second.term, .congSigma first.term body first.recipe second.recipe⟩
        | .lam body =>
            let result := produce fuel body
            ⟨.lam result.term, .congLam result.recipe⟩
        | .app function argument =>
            let first := produce fuel function
            let second := produce fuel argument
            ⟨.app first.term second.term, .congApp first.term argument first.recipe second.recipe⟩
        | .pair first second =>
            let left := produce fuel first
            let right := produce fuel second
            ⟨.pair left.term right.term, .congPair left.term second left.recipe right.recipe⟩
        | .fst pair =>
            let result := produce fuel pair
            ⟨.fst result.term, .congFst result.recipe⟩
        | .snd pair =>
            let result := produce fuel pair
            ⟨.snd result.term, .congSnd result.recipe⟩
        | .refl subject =>
            let result := produce fuel subject
            ⟨.refl result.term, .congRefl result.recipe⟩
        | .id carrier left right =>
            let type := produce fuel carrier
            let first := produce fuel left
            let second := produce fuel right
            ⟨.id type.term first.term second.term,
              .congId type.term left first.term right type.recipe first.recipe second.recipe⟩
      finish fuel candidate

def finish : Nat → {n : Nat} → Candidate Head RootCode n → Candidate Head RootCode n
  | 0, _, candidate => candidate
  | fuel + 1, _, candidate =>
      let next := match candidate.term with
        | .app (.lam body) argument =>
            some (inst0 argument body, Code.single (.betaPi body argument))
        | .fst (.pair first second) => some (first, Code.single (.betaSigmaFst first second))
        | .snd (.pair first second) => some (second, Code.single (.betaSigmaSnd first second))
        | term => do
            let proposed ← searchRoot term
            let (left, right) ← decodeRoot proposed
            if left = term then some (right, Code.single (.root proposed)) else none
      match next with
      | none => candidate
      | some (term, step) =>
          let rest := produce fuel term
          ⟨rest.term, .trans candidate.recipe (.trans step rest.recipe)⟩

end

/-- Compare the syntax left after bounded computation. Head comparisons
remain explicit local certificates, including beneath binders. -/
def compareShape : {n : Nat} → Tm Head n → Tm Head n → Option (Code Head RootCode n)
  | _, .var first, .var second =>
      if first = second then some (.refl (.var first)) else none
  | _, .const first, .const second =>
      if first = second then some (.refl (.const first)) else none
  | _, .head first, .head second => some (.single (.head first second))
  | _, .pi first body, .pi second body' => do
      let left ← compareShape first second
      let right ← compareShape body body'
      return .congPi second body left right
  | _, .sigma first body, .sigma second body' => do
      let left ← compareShape first second
      let right ← compareShape body body'
      return .congSigma second body left right
  | _, .lam first, .lam second => do return .congLam (← compareShape first second)
  | _, .app first argument, .app second argument' => do
      let left ← compareShape first second
      let right ← compareShape argument argument'
      return .congApp second argument left right
  | _, .pair first tail, .pair second tail' => do
      let left ← compareShape first second
      let right ← compareShape tail tail'
      return .congPair second tail left right
  | _, .fst first, .fst second => do return .congFst (← compareShape first second)
  | _, .snd first, .snd second => do return .congSnd (← compareShape first second)
  | _, .refl first, .refl second => do return .congRefl (← compareShape first second)
  | _, .id type first tail, .id type' second tail' => do
      let carrier ← compareShape type type'
      let left ← compareShape first second
      let right ← compareShape tail tail'
      return .congId type' first second tail carrier left right
  | _, _, _ => none

variable {root : RootComputation Head} {headEq : Head → Head → Prop} [DecidableRel headEq]
variable (decoder : StructuralConversionCode.RootDecoder root)
variable (searchRoot : {n : Nat} → Tm Head n → Option (decoder.Code n))

/-- The independent replay gate qualifies the path of the computed result.
The result may still contain reducible terms when its budget is exhausted. -/
def normalize (fuel : Nat) {n : Nat} (term : Tm Head n) :
    Option (Candidate Head decoder.Code n) :=
  let candidate := produce decoder.decode searchRoot fuel term
  if candidate.recipe.check headEq decoder.decode term candidate.term then some candidate else none

theorem normalize_sound (fuel : Nat) {n : Nat} (term : Tm Head n)
    (candidate : Candidate Head decoder.Code n)
    (accepted : normalize decoder searchRoot (headEq := headEq) fuel term = some candidate) :
    Conv headEq term candidate.term root := by
  dsimp only [normalize] at accepted
  split at accepted
  · rename_i checked
    cases Option.some.inj accepted
    exact StructuralConversionCode.Code.check_sound decoder checked
  · cases accepted

def compare (fuel : Nat) {n : Nat} (left right : Tm Head n) :
    Option (Code Head decoder.Code n) := do
  let first := produce decoder.decode searchRoot fuel left
  let second := produce decoder.decode searchRoot fuel right
  let middle ← compareShape first.term second.term
  let recipe := Code.trans first.recipe (.trans middle (.symm second.recipe))
  if recipe.check headEq decoder.decode left right then some recipe else none

theorem compare_sound (fuel : Nat) {n : Nat} (left right : Tm Head n)
    (recipe : Code Head decoder.Code n)
    (accepted : compare decoder searchRoot (headEq := headEq) fuel left right = some recipe) :
    Conv headEq left right root := by
  dsimp only [compare] at accepted
  cases matched : compareShape (RootCode := decoder.Code) (produce decoder.decode searchRoot fuel left).term
      (produce decoder.decode searchRoot fuel right).term with
  | none => simp [matched] at accepted
  | some middle =>
      simp only [matched, Option.bind_eq_bind, Option.bind_some] at accepted
      split at accepted
      · rename_i checked
        cases Option.some.inj accepted
        exact StructuralConversionCode.Code.check_sound decoder checked
      · cases accepted

end StructuralConversionSearch
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
