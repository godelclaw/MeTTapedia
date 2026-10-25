import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionSearch

/-!
# Bounded structural weak-head conversion proposals

The producer retains a finite structural recipe, visits function and projection
positions, and compares matching syntax before further computation. Type views
also descend through product domains and bodies, and through identity carriers;
identity endpoints retain their authored syntax. The public comparison replays
its proposed recipe with the independent conversion checker. Failure is not a
non-convertibility result, and fuel bounds this producer rather than the logic.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.StructuralWeakHeadSearch
open StructuralConversionCode
open StructuralConversionSearch (Candidate compareShape)
variable {Head : Type} {RootCode : Nat → Type} [DecidableEq Head]
variable (decodeRoot : {n : Nat} → RootCode n → Option (Tm Head n × Tm Head n))
variable (searchRoot : {n : Nat} → Tm Head n → Option (RootCode n))

def produce : (fuel : Nat) → {n : Nat} → Tm Head n → Candidate Head RootCode n
  | 0, _, term => ⟨term, .refl term⟩
  | fuel + 1, _, term =>
    let initial : Candidate Head RootCode _ := match term with
      | .app function argument =>
        let first := produce fuel function
        ⟨.app first.term argument, .congApp first.term argument first.recipe (.refl argument)⟩
      | .fst pair =>
        let first := produce fuel pair
        ⟨.fst first.term, .congFst first.recipe⟩
      | .snd pair =>
        let first := produce fuel pair
        ⟨.snd first.term, .congSnd first.recipe⟩
      | _ => ⟨term, .refl term⟩
    let next := match initial.term with
      | .app (.lam body) argument =>
        some (inst0 argument body, Code.single (.betaPi body argument))
      | .fst (.pair first second) => some (first, Code.single (.betaSigmaFst first second))
      | .snd (.pair first second) => some (second, Code.single (.betaSigmaSnd first second))
      | current => do
        let code ← searchRoot current
        let (left, right) ← decodeRoot code
        if left = current then some (right, Code.single (.root code)) else none
    match next with
    | none => initial
    | some (contracted, step) =>
      let rest := produce fuel contracted
      ⟨rest.term, .trans initial.recipe (.trans step rest.recipe)⟩
termination_by structural fuel _ _ => fuel

def typeView : (fuel : Nat) → {n : Nat} → Tm Head n → Candidate Head RootCode n
  | 0, _, term => ⟨term, .refl term⟩
  | fuel + 1, _, term =>
    let viewed := produce decodeRoot searchRoot (fuel + 1) term
    match viewed.term with
    | .pi domain body =>
      let first := typeView fuel domain
      let second := typeView fuel body
      ⟨.pi first.term second.term,
        .trans viewed.recipe (.congPi first.term body first.recipe second.recipe)⟩
    | .sigma domain body =>
      let first := typeView fuel domain
      let second := typeView fuel body
      ⟨.sigma first.term second.term,
        .trans viewed.recipe (.congSigma first.term body first.recipe second.recipe)⟩
    | .id carrier left right =>
      let first := typeView fuel carrier
      ⟨.id first.term left right,
        .trans viewed.recipe (.congId first.term left left right first.recipe (.refl left) (.refl right))⟩
    | _ => viewed
termination_by structural fuel _ _ => fuel

def compareCore : (fuel : Nat) → {n : Nat} → Tm Head n → Tm Head n → Option (Code Head RootCode n)
  | 0, _, left, right => if left = right then some (.refl left) else none
  | fuel + 1, _, left, right =>
    if left = right then some (.refl left)
    else do
      let first := produce decodeRoot searchRoot (fuel + 1) left
      let second := produce decodeRoot searchRoot (fuel + 1) right
      let middle ← if first.term = second.term then some (.refl first.term) else
        match first.term, second.term with
        | .var first, .var second => if first = second then some (.refl (.var first)) else none
        | .const first, .const second => if first = second then some (.refl (.const first)) else none
        | .head first, .head second => some (.single (.head first second))
        | .pi first body, .pi second body' => do
          let left ← compareCore fuel first second
          let right ← compareCore fuel body body'
          pure (Code.congPi second body left right)
        | .sigma first body, .sigma second body' => do
          let left ← compareCore fuel first second
          let right ← compareCore fuel body body'
          pure (Code.congSigma second body left right)
        | .lam first, .lam second => do pure (Code.congLam (← compareCore fuel first second))
        | .app first argument, .app second argument' => do
          let left ← compareCore fuel first second
          let right ← compareCore fuel argument argument'
          pure (Code.congApp second argument left right)
        | .pair first tail, .pair second tail' => do
          let left ← compareCore fuel first second
          let right ← compareCore fuel tail tail'
          pure (Code.congPair second tail left right)
        | .fst first, .fst second => do pure (Code.congFst (← compareCore fuel first second))
        | .snd first, .snd second => do pure (Code.congSnd (← compareCore fuel first second))
        | .refl first, .refl second => do pure (Code.congRefl (← compareCore fuel first second))
        | .id type first tail, .id type' second tail' => do
          let carrier ← compareCore fuel type type'
          let left ← compareCore fuel first second
          let right ← compareCore fuel tail tail'
          pure (Code.congId type' first second tail carrier left right)
        | _, _ => none
      return .trans first.recipe (.trans middle (.symm second.recipe))
termination_by structural fuel _ _ _ => fuel

variable {root : RootComputation Head} {headEq : Head → Head → Prop} [DecidableRel headEq]
variable (decoder : RootDecoder root)
variable (searchRoot : {n : Nat} → Tm Head n → Option (decoder.Code n))

def compare (fuel : Nat) {n : Nat} (left right : Tm Head n) : Option (Code Head decoder.Code n) := do
  let proposed ← compareCore decoder.decode searchRoot fuel left right
  if proposed.check headEq decoder.decode left right then some proposed else none

theorem compare_sound (fuel : Nat) {n : Nat} {left right : Tm Head n}
    {recipe : Code Head decoder.Code n}
    (accepted : compare decoder searchRoot (headEq := headEq) fuel left right = some recipe) :
    Conv headEq left right root := by
  unfold compare at accepted
  cases produced : compareCore decoder.decode searchRoot fuel left right with
  | none => simp [produced] at accepted
  | some candidate =>
    simp only [Option.bind_eq_bind, produced, Option.bind_some] at accepted
    split at accepted
    · rename_i checked
      cases Option.some.inj accepted
      exact Code.check_sound decoder checked
    · cases accepted

#print axioms compare_sound
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.StructuralWeakHeadSearch
