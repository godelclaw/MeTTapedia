import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarBridgeTarget
import Mathlib.Data.List.GetD

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: closed-collar bridge proof support

This module contains the reusable finite-certificate machinery for the
closed-collar section-9.2 bridge.  The generated per-word files only need to
prove small Boolean root-closure checks; the theorems here turn those checks
into the executable Kempe-connectedness target.
-/

namespace GoertzelLemma818ClosedCollarBridgeProof

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget

def addIfFreshDec {α : Type} [DecidableEq α] (xs : List α) (x : α) :
    List α :=
  if x ∈ xs then xs else xs ++ [x]

theorem mem_addIfFreshDec_of_mem {α : Type} [DecidableEq α]
    {xs : List α} {x y : α} (h : x ∈ xs) :
    x ∈ addIfFreshDec xs y := by
  unfold addIfFreshDec
  by_cases hy : y ∈ xs
  · simp [hy, h]
  · simp [hy, h]

theorem mem_addIfFreshDec_self {α : Type} [DecidableEq α]
    (xs : List α) (x : α) :
    x ∈ addIfFreshDec xs x := by
  unfold addIfFreshDec
  by_cases hx : x ∈ xs
  · simp [hx]
  · simp [hx]

theorem mem_addIfFreshDec_source_or_eq {α : Type} [DecidableEq α]
    (xs : List α) (candidate x : α)
    (h : x ∈ addIfFreshDec xs candidate) :
    x ∈ xs ∨ x = candidate := by
  unfold addIfFreshDec at h
  by_cases hc : candidate ∈ xs
  · exact Or.inl (by simpa [hc] using h)
  · have hx : x ∈ xs ∨ x ∈ [candidate] := by
      have h' : x ∈ xs ++ [candidate] := by
        simpa [hc] using h
      exact List.mem_append.mp h'
    rcases hx with hx | hx
    · exact Or.inl hx
    · simp at hx
      exact Or.inr hx

def boolClosureStep {α : Type} [DecidableEq α]
    (step : α → α → Bool) (fiber seen : List α) : List α :=
  fiber.foldl
    (fun acc candidate =>
      if acc.any (fun current => step current candidate) then
        addIfFreshDec acc candidate
      else
        acc)
    seen

def closeBoolFiber {α : Type} [DecidableEq α]
    (step : α → α → Bool) (fiber : List α) :
    Nat → List α → List α
  | 0, seen => seen
  | n + 1, seen =>
      let seen' := boolClosureStep step fiber seen
      if seen'.length == seen.length then seen' else closeBoolFiber step fiber n seen'

def boolFiberRootConnected {α : Type} [DecidableEq α]
    (step : α → α → Bool) (fiber : List α) : Bool :=
  match fiber with
  | [] => true
  | root :: _ =>
      let closure := closeBoolFiber step fiber fiber.length [root]
      fiber.all fun state => closure.contains state

theorem boolClosureStep_mem_of_seen {α : Type} [DecidableEq α]
    (step : α → α → Bool) (fiber seen : List α) (x : α)
    (h : x ∈ seen) :
    x ∈ boolClosureStep step fiber seen := by
  unfold boolClosureStep
  induction fiber generalizing seen with
  | nil =>
      simpa using h
  | cons candidate rest ih =>
      simp only [List.foldl_cons]
      apply ih
      by_cases hc : (seen.any fun current => step current candidate) = true
      · simp [hc, mem_addIfFreshDec_of_mem h]
      · have hfalse :
            (seen.any fun current => step current candidate) = false :=
          bool_false_of_not_true hc
        simp [hfalse, h]

theorem boolClosureStep_lift_property {α : Type} [DecidableEq α]
    (step : α → α → Bool) (fiber seen : List α) (P : α → Prop)
    (hseen : ∀ x, x ∈ seen → P x)
    (hstep : ∀ current target,
      P current →
      target ∈ fiber →
      step current target = true →
      P target) :
    ∀ x, x ∈ boolClosureStep step fiber seen → P x := by
  induction fiber generalizing seen with
  | nil =>
      intro x hx
      simpa [boolClosureStep] using hseen x hx
  | cons candidate rest ih =>
      intro x hx
      unfold boolClosureStep at hx
      simp only [List.foldl_cons] at hx
      let nextSeen :=
        if (seen.any fun current => step current candidate) then
          addIfFreshDec seen candidate
        else
          seen
      have hnextSeen : ∀ w, w ∈ nextSeen → P w := by
        intro w hw
        by_cases hany : (seen.any fun current => step current candidate) = true
        · have hw' : w ∈ addIfFreshDec seen candidate := by
            simpa [nextSeen, hany] using hw
          rcases mem_addIfFreshDec_source_or_eq seen candidate w hw' with
            hwSeen | hwCandidate
          · exact hseen w hwSeen
          · subst hwCandidate
            rw [List.any_eq_true] at hany
            rcases hany with ⟨current, hcurrentSeen, hcurrentStep⟩
            exact hstep current w (hseen current hcurrentSeen) (by simp)
              hcurrentStep
        · have hfalse :
              (seen.any fun current => step current candidate) = false :=
            bool_false_of_not_true hany
          exact hseen w (by simpa [nextSeen, hfalse] using hw)
      exact ih nextSeen hnextSeen (by
        intro current target hcurrent htarget hsingle
        exact hstep current target hcurrent
          (List.mem_cons_of_mem candidate htarget) hsingle)
        x (by simpa [boolClosureStep, nextSeen] using hx)

theorem closeBoolFiber_mem_of_seen {α : Type} [DecidableEq α]
    (step : α → α → Bool) (fiber : List α) (n : Nat)
    (seen : List α) (x : α) (h : x ∈ seen) :
    x ∈ closeBoolFiber step fiber n seen := by
  induction n generalizing seen with
  | zero =>
      simpa [closeBoolFiber] using h
  | succ n ih =>
      simp only [closeBoolFiber]
      let seen' := boolClosureStep step fiber seen
      have hx' : x ∈ seen' := boolClosureStep_mem_of_seen step fiber seen x h
      by_cases hstop : ((seen'.length == seen.length) = true)
      · simp [seen', hstop, hx']
      · have hfalse : (seen'.length == seen.length) = false :=
          bool_false_of_not_true hstop
        simp only [seen', hfalse, Bool.false_eq_true, if_false]
        exact ih seen' hx'

theorem closeBoolFiber_lift_property {α : Type} [DecidableEq α]
    (step : α → α → Bool) (fiber : List α) (n : Nat) (seen : List α)
    (P : α → Prop)
    (hseen : ∀ x, x ∈ seen → P x)
    (hstep : ∀ current target,
      P current →
      target ∈ fiber →
      step current target = true →
      P target) :
    ∀ x, x ∈ closeBoolFiber step fiber n seen → P x := by
  induction n generalizing seen with
  | zero =>
      intro x hx
      simpa [closeBoolFiber] using hseen x hx
  | succ n ih =>
      intro x hx
      simp only [closeBoolFiber] at hx
      let seen' := boolClosureStep step fiber seen
      have hseen' : ∀ y, y ∈ seen' → P y :=
        boolClosureStep_lift_property step fiber seen P hseen hstep
      by_cases hstop : (seen'.length == seen.length) = true
      · simp only [seen', hstop, if_true] at hx
        exact hseen' x hx
      · have hfalse : (seen'.length == seen.length) = false :=
          bool_false_of_not_true hstop
        simp only [seen', hfalse, Bool.false_eq_true, if_false] at hx
        exact ih seen' hseen' x hx

theorem reflTransGen_reverse_of_stepSymmetric {α : Type}
    {R : α → α → Prop}
    (hsym : ∀ {x y}, R x y → R y x) :
    ∀ {x y}, Relation.ReflTransGen R x y →
      Relation.ReflTransGen R y x := by
  intro x y hxy
  induction hxy with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hpre hstep ih =>
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single (hsym hstep)) ih

theorem boolFiberRootConnected_pairwise {α : Type} [DecidableEq α]
    (step : α → α → Bool)
    (hsym : ∀ {x y}, step x y = true → step y x = true)
    (fiber : List α)
    (hconn : boolFiberRootConnected step fiber = true) :
    ∀ x, x ∈ fiber →
      ∀ y, y ∈ fiber →
        Relation.ReflTransGen (fun a b => step a b = true) x y := by
  intro x hx y hy
  cases fiber with
  | nil =>
      cases hx
  | cons root rest =>
      unfold boolFiberRootConnected at hconn
      rw [List.all_eq_true] at hconn
      let closure := closeBoolFiber step (root :: rest) (root :: rest).length [root]
      have hRootReach :
          ∀ state, state ∈ closure →
            Relation.ReflTransGen (fun a b => step a b = true) root state := by
        apply closeBoolFiber_lift_property
        · intro state hstate
          simp at hstate
          subst state
          exact Relation.ReflTransGen.refl
        · intro current target hcurrent _htarget hstep
          exact Relation.ReflTransGen.tail hcurrent hstep
      have hxClosure : x ∈ closure :=
        List.contains_iff_mem.mp (hconn x hx)
      have hyClosure : y ∈ closure :=
        List.contains_iff_mem.mp (hconn y hy)
      exact Relation.ReflTransGen.trans
        (reflTransGen_reverse_of_stepSymmetric
          (R := fun a b => step a b = true) (by
            intro a b hstep
            exact hsym hstep)
          (hRootReach x hxClosure))
        (hRootReach y hyClosure)

def boolReachableCheck {α : Type} [DecidableEq α]
    (step : α → α → Bool) (fiber : List α) (source target : α) : Bool :=
  (closeBoolFiber step fiber fiber.length [source]).contains target

def boolFiberPairwiseConnected {α : Type} [DecidableEq α]
    (step : α → α → Bool) (fiber : List α) : Bool :=
  fiber.all fun source =>
    fiber.all fun target => boolReachableCheck step fiber source target

theorem boolReachableCheck_sound {α : Type} [DecidableEq α]
    (step : α → α → Bool) (fiber : List α) {source target : α}
    (hcheck : boolReachableCheck step fiber source target = true) :
    Relation.ReflTransGen (fun a b => step a b = true) source target := by
  unfold boolReachableCheck at hcheck
  have htarget :
      target ∈ closeBoolFiber step fiber fiber.length [source] :=
    List.contains_iff_mem.mp hcheck
  exact
    closeBoolFiber_lift_property step fiber fiber.length [source]
      (fun state =>
        Relation.ReflTransGen (fun a b => step a b = true) source state)
      (by
        intro state hstate
        simp at hstate
        subst state
        exact Relation.ReflTransGen.refl)
      (by
        intro current target hcurrent _htarget hstep
        exact Relation.ReflTransGen.tail hcurrent hstep)
      target htarget

theorem boolFiberPairwiseConnected_pairwise {α : Type} [DecidableEq α]
    (step : α → α → Bool) (fiber : List α)
    (hconn : boolFiberPairwiseConnected step fiber = true) :
    ∀ x, x ∈ fiber →
      ∀ y, y ∈ fiber →
        Relation.ReflTransGen (fun a b => step a b = true) x y := by
  unfold boolFiberPairwiseConnected at hconn
  rw [List.all_eq_true] at hconn
  intro x hx y hy
  have hxAll := hconn x hx
  rw [List.all_eq_true] at hxAll
  exact boolReachableCheck_sound step fiber (hxAll y hy)

theorem boolReachableCheck_subtype_sound {α : Type} [DecidableEq α]
    (step : α → α → Bool) (fiber : List α) {source target : α}
    (hsource : source ∈ fiber) (htarget : target ∈ fiber)
    (hcheck : boolReachableCheck step fiber source target = true) :
    Relation.ReflTransGen
      (fun a b : {x // x ∈ fiber} => step a.1 b.1 = true)
      ⟨source, hsource⟩ ⟨target, htarget⟩ := by
  unfold boolReachableCheck at hcheck
  have htargetClosure :
      target ∈ closeBoolFiber step fiber fiber.length [source] :=
    List.contains_iff_mem.mp hcheck
  have hreachExists :
      ∃ htarget' : target ∈ fiber,
        Relation.ReflTransGen
          (fun a b : {x // x ∈ fiber} => step a.1 b.1 = true)
          ⟨source, hsource⟩ ⟨target, htarget'⟩ := by
    exact
      closeBoolFiber_lift_property step fiber fiber.length [source]
        (fun state =>
          ∃ hstate : state ∈ fiber,
            Relation.ReflTransGen
              (fun a b : {x // x ∈ fiber} => step a.1 b.1 = true)
              ⟨source, hsource⟩ ⟨state, hstate⟩)
        (by
          intro state hstate
          simp at hstate
          subst state
          exact ⟨hsource, Relation.ReflTransGen.refl⟩)
        (by
          intro current target hcurrent htargetMem hstep
          rcases hcurrent with ⟨hcurrentMem, hreach⟩
          exact
            ⟨htargetMem,
              Relation.ReflTransGen.tail hreach hstep⟩)
        target htargetClosure
  rcases hreachExists with ⟨htarget', hreach⟩
  have hEq :
      (⟨target, htarget'⟩ : {x // x ∈ fiber}) = ⟨target, htarget⟩ :=
    Subtype.ext rfl
  simpa [hEq] using hreach

theorem boolFiberPairwiseConnected_subtypeConnected {α : Type}
    [DecidableEq α] (step : α → α → Bool) (fiber : List α)
    (hconn : boolFiberPairwiseConnected step fiber = true) :
    ∀ x y : {state // state ∈ fiber},
      Relation.ReflTransGen
        (fun a b : {state // state ∈ fiber} => step a.1 b.1 = true)
        x y := by
  unfold boolFiberPairwiseConnected at hconn
  rw [List.all_eq_true] at hconn
  intro x y
  have hxAll := hconn x.1 x.2
  rw [List.all_eq_true] at hxAll
  exact boolReachableCheck_subtype_sound step fiber x.2 y.2
    (hxAll y.1 y.2)

def closedCollarFiberPoints (orients : List TauOrient) (key : List LColor) :
    List (ClosedCollarFiberPoint orients key) :=
  (closedCollarFiber orients key).attach

instance closedCollarFiberPointDecidableEq
    (orients : List TauOrient) (key : List LColor) :
    DecidableEq (ClosedCollarFiberPoint orients key) := by
  intro x y
  by_cases hxy : x.1 = y.1
  · exact isTrue (Subtype.ext hxy)
  · exact isFalse (by
      intro h
      exact hxy (congrArg Subtype.val h))

theorem mem_closedCollarFiberPoints
    (orients : List TauOrient) (key : List LColor)
    (x : ClosedCollarFiberPoint orients key) :
    x ∈ closedCollarFiberPoints orients key := by
  exact List.mem_attach (closedCollarFiber orients key) x

def closedCollarFiberRootConnectedCheck
    (orients : List TauOrient) (key : List LColor) : Bool :=
  boolFiberRootConnected
    (fun x y : ClosedCollarFiberPoint orients key =>
      closedCollarSingleKempeStep orients x.1 y.1)
    (closedCollarFiberPoints orients key)

def closedCollarFiberPairwiseConnectedCheck
    (orients : List TauOrient) (key : List LColor) : Bool :=
  boolFiberPairwiseConnected
    (fun x y : ClosedCollarFiberPoint orients key =>
      closedCollarSingleKempeStep orients x.1 y.1)
    (closedCollarFiberPoints orients key)

def closedCollarStateFiberPairwiseConnectedCheck
    (orients : List TauOrient) (key : List LColor) : Bool :=
  boolFiberPairwiseConnected
    (fun x y : List TauState => closedCollarSingleKempeStep orients x y)
    (closedCollarFiber orients key)

theorem closedCollarAgreesWithSwitch_symm
    {orients : List TauOrient} {s t : List TauState}
    {component : List ChainEdge} {a c : LColor}
    (hagree :
      closedCollarAgreesWithSwitch orients s t component a c = true) :
    closedCollarAgreesWithSwitch orients t s component a c = true := by
  unfold closedCollarAgreesWithSwitch closedCollarSwitchedColor at hagree ⊢
  rw [List.all_eq_true] at hagree ⊢
  intro ge hge
  have hgeAgree := hagree ge hge
  by_cases hcontains : component.contains ge = true
  · rw [hcontains]
    rw [hcontains] at hgeAgree
    exact colorEq_swapColor_swapColor a c _ _ hgeAgree
  · have hcontainsFalse : component.contains ge = false :=
      bool_false_of_not_true hcontains
    rw [hcontainsFalse]
    rw [hcontainsFalse] at hgeAgree
    rw [colorEq_eq_true_iff] at hgeAgree ⊢
    exact hgeAgree.symm

theorem listGetD_eq_getD {α : Type} (xs : List α) (i : Nat)
    (fallback : α) :
    listGetD xs i fallback = xs.getD i fallback := by
  induction xs generalizing i with
  | nil =>
      cases i <;> rfl
  | cons x xs ih =>
      cases i with
      | zero => rfl
      | succ i => exact ih i

theorem listGetD_mem_of_lt {α : Type} (xs : List α) (fallback : α)
    {i : Nat} (hi : i < xs.length) :
    listGetD xs i fallback ∈ xs := by
  rw [listGetD_eq_getD, List.getD_eq_getElem xs fallback hi]
  exact List.getElem_mem hi

theorem listGetD_idxOf_eq_of_mem {α : Type} [BEq α] [LawfulBEq α]
    (xs : List α) (fallback : α) {x : α} (hx : x ∈ xs) :
    listGetD xs (xs.idxOf x) fallback = x := by
  have hlt : xs.idxOf x < xs.length := List.idxOf_lt_length_of_mem hx
  rw [listGetD_eq_getD, List.getD_eq_getElem xs fallback hlt]
  exact List.getElem_idxOf hlt

structure ClosedCollarSpineCertificate where
  key : List LColor
  root : Nat
  maxDepth : Nat
  parents : List Nat
  deriving DecidableEq, BEq, Repr, Inhabited

def closedCollarParentAt (parents : List Nat) (i : Nat) : Nat :=
  listGetD parents i i

def closedCollarParentIter (parents : List Nat) : Nat → Nat → Nat
  | 0, i => i
  | n + 1, i =>
      closedCollarParentIter parents n (closedCollarParentAt parents i)

def closedCollarIndexStepBool (orients : List TauOrient)
    (fiber : List (List TauState)) (i j : Nat) : Bool :=
  closedCollarSingleKempeStep orients
    (listGetD fiber i []) (listGetD fiber j [])

def closedCollarParentIndexValid (orients : List TauOrient)
    (fiber : List (List TauState)) (parents : List Nat) (i : Nat) : Bool :=
  let p := closedCollarParentAt parents i
  decide (p < fiber.length) &&
    (i == p ||
      (closedCollarIndexStepBool orients fiber i p &&
        closedCollarIndexStepBool orients fiber p i))

def closedCollarSpineRowsValid (orients : List TauOrient)
    (fiber : List (List TauState)) (parents : List Nat) : Bool :=
  (List.range fiber.length).all
    (closedCollarParentIndexValid orients fiber parents)

def closedCollarSpineParentsReachRoot (fiber : List (List TauState))
    (cert : ClosedCollarSpineCertificate) : Bool :=
  (List.range fiber.length).all fun i =>
    closedCollarParentIter cert.parents cert.maxDepth i == cert.root

def closedCollarSpineCertificateAuditFrom
    (orients : List TauOrient) (statesList : List (List TauState))
    (cert : ClosedCollarSpineCertificate) : Bool :=
  let fiber := closedCollarFiberFrom orients statesList cert.key
  cert.parents.length == fiber.length &&
    (if fiber.isEmpty then cert.parents == [] else decide (cert.root < fiber.length)) &&
      closedCollarSpineRowsValid orients fiber cert.parents &&
        closedCollarSpineParentsReachRoot fiber cert

def closedCollarSpineCertificateAudit
    (orients : List TauOrient) (cert : ClosedCollarSpineCertificate) : Bool :=
  closedCollarSpineCertificateAuditFrom orients (allClosedCollarStates orients) cert

theorem closedCollarParentIndexValid_parent_lt
    {orients : List TauOrient} {fiber : List (List TauState)}
    {parents : List Nat} {i : Nat}
    (hvalid :
      closedCollarParentIndexValid orients fiber parents i = true) :
    closedCollarParentAt parents i < fiber.length := by
  unfold closedCollarParentIndexValid at hvalid
  simp only [Bool.and_eq_true] at hvalid
  exact of_decide_eq_true hvalid.1

theorem closedCollarParentIndexValid_step_or_self
    {orients : List TauOrient} {fiber : List (List TauState)}
    {parents : List Nat} {i : Nat}
    (hvalid :
      closedCollarParentIndexValid orients fiber parents i = true) :
    i = closedCollarParentAt parents i ∨
      (closedCollarIndexStepBool orients fiber i
          (closedCollarParentAt parents i) = true ∧
        closedCollarIndexStepBool orients fiber
          (closedCollarParentAt parents i) i = true) := by
  unfold closedCollarParentIndexValid at hvalid
  simp only [Bool.and_eq_true] at hvalid
  have hrest := hvalid.2
  rw [Bool.or_eq_true, Bool.and_eq_true] at hrest
  rcases hrest with hself | hsteps
  · exact Or.inl (beq_iff_eq.mp hself)
  · exact Or.inr hsteps

theorem closedCollarSpineRowsValid_index
    {orients : List TauOrient} {fiber : List (List TauState)}
    {parents : List Nat} (hrows :
      closedCollarSpineRowsValid orients fiber parents = true)
    {i : Nat} (hi : i < fiber.length) :
    closedCollarParentIndexValid orients fiber parents i = true := by
  unfold closedCollarSpineRowsValid at hrows
  rw [List.all_eq_true] at hrows
  exact hrows i (List.mem_range.mpr hi)

theorem closedCollarSpineParentsReachRoot_index
    {fiber : List (List TauState)} {cert : ClosedCollarSpineCertificate}
    (hroot : closedCollarSpineParentsReachRoot fiber cert = true)
    {i : Nat} (hi : i < fiber.length) :
    closedCollarParentIter cert.parents cert.maxDepth i = cert.root := by
  unfold closedCollarSpineParentsReachRoot at hroot
  rw [List.all_eq_true] at hroot
  exact beq_iff_eq.mp (hroot i (List.mem_range.mpr hi))

theorem closedCollarSpineReachParentIter
    {orients : List TauOrient} {fiber : List (List TauState)}
    {parents : List Nat}
    (hrows : closedCollarSpineRowsValid orients fiber parents = true) :
    ∀ (n i : Nat) (hi : i < fiber.length),
      ∃ htarget : closedCollarParentIter parents n i < fiber.length,
        Relation.ReflTransGen
          (fun a b : {state // state ∈ fiber} =>
            closedCollarSingleKempeStep orients a.1 b.1 = true)
          ⟨listGetD fiber i [], listGetD_mem_of_lt fiber [] hi⟩
          ⟨listGetD fiber (closedCollarParentIter parents n i) [],
            listGetD_mem_of_lt fiber [] htarget⟩ := by
  intro n
  induction n with
  | zero =>
      intro i hi
      exact ⟨hi, Relation.ReflTransGen.refl⟩
  | succ n ih =>
      intro i hi
      have hvalid := closedCollarSpineRowsValid_index hrows hi
      let p := closedCollarParentAt parents i
      have hp : p < fiber.length := by
        simpa [p] using
          closedCollarParentIndexValid_parent_lt hvalid
      have hfirst :
          Relation.ReflTransGen
            (fun a b : {state // state ∈ fiber} =>
              closedCollarSingleKempeStep orients a.1 b.1 = true)
            ⟨listGetD fiber i [], listGetD_mem_of_lt fiber [] hi⟩
            ⟨listGetD fiber p [], listGetD_mem_of_lt fiber [] hp⟩ := by
        rcases closedCollarParentIndexValid_step_or_self hvalid with
          hself | hsteps
        · have hpEq : p = i := by
            simpa [p] using hself.symm
          have hEq :
              (⟨listGetD fiber i [], listGetD_mem_of_lt fiber [] hi⟩ :
                {state // state ∈ fiber}) =
              ⟨listGetD fiber p [], listGetD_mem_of_lt fiber [] hp⟩ := by
            apply Subtype.ext
            simpa [p] using congrArg (fun k => listGetD fiber k []) hself
          simpa [hEq] using
            (Relation.ReflTransGen.refl :
              Relation.ReflTransGen
                (fun a b : {state // state ∈ fiber} =>
                  closedCollarSingleKempeStep orients a.1 b.1 = true)
                ⟨listGetD fiber i [], listGetD_mem_of_lt fiber [] hi⟩
                ⟨listGetD fiber i [], listGetD_mem_of_lt fiber [] hi⟩)
        · exact Relation.ReflTransGen.single (by
            simpa [closedCollarIndexStepBool, p] using hsteps.1)
      rcases ih p hp with ⟨htarget, htail⟩
      refine ⟨htarget, ?_⟩
      simpa [closedCollarParentIter, p] using
        Relation.ReflTransGen.trans hfirst htail

theorem closedCollarSpineReachParentIter_reverse
    {orients : List TauOrient} {fiber : List (List TauState)}
    {parents : List Nat}
    (hrows : closedCollarSpineRowsValid orients fiber parents = true) :
    ∀ (n i : Nat) (hi : i < fiber.length),
      ∃ htarget : closedCollarParentIter parents n i < fiber.length,
        Relation.ReflTransGen
          (fun a b : {state // state ∈ fiber} =>
            closedCollarSingleKempeStep orients a.1 b.1 = true)
          ⟨listGetD fiber (closedCollarParentIter parents n i) [],
            listGetD_mem_of_lt fiber [] htarget⟩
          ⟨listGetD fiber i [], listGetD_mem_of_lt fiber [] hi⟩ := by
  intro n
  induction n with
  | zero =>
      intro i hi
      exact ⟨hi, Relation.ReflTransGen.refl⟩
  | succ n ih =>
      intro i hi
      have hvalid := closedCollarSpineRowsValid_index hrows hi
      let p := closedCollarParentAt parents i
      have hp : p < fiber.length := by
        simpa [p] using
          closedCollarParentIndexValid_parent_lt hvalid
      rcases ih p hp with ⟨htarget, htail⟩
      have hlast :
          Relation.ReflTransGen
            (fun a b : {state // state ∈ fiber} =>
              closedCollarSingleKempeStep orients a.1 b.1 = true)
            ⟨listGetD fiber p [], listGetD_mem_of_lt fiber [] hp⟩
            ⟨listGetD fiber i [], listGetD_mem_of_lt fiber [] hi⟩ := by
        rcases closedCollarParentIndexValid_step_or_self hvalid with
          hself | hsteps
        · have hpEq : p = i := by
            simpa [p] using hself.symm
          have hEq :
              (⟨listGetD fiber p [], listGetD_mem_of_lt fiber [] hp⟩ :
                {state // state ∈ fiber}) =
              ⟨listGetD fiber i [], listGetD_mem_of_lt fiber [] hi⟩ := by
            apply Subtype.ext
            simpa [p] using congrArg (fun k => listGetD fiber k []) hself.symm
          simpa [hEq] using
            (Relation.ReflTransGen.refl :
              Relation.ReflTransGen
                (fun a b : {state // state ∈ fiber} =>
                  closedCollarSingleKempeStep orients a.1 b.1 = true)
                ⟨listGetD fiber i [], listGetD_mem_of_lt fiber [] hi⟩
                ⟨listGetD fiber i [], listGetD_mem_of_lt fiber [] hi⟩)
        · exact Relation.ReflTransGen.single (by
            simpa [closedCollarIndexStepBool, p] using hsteps.2)
      refine ⟨htarget, ?_⟩
      simpa [closedCollarParentIter, p] using
        Relation.ReflTransGen.trans htail hlast

theorem closedCollarFiberKempeConnected_of_spineCertificateAudit
    {orients : List TauOrient} (cert : ClosedCollarSpineCertificate)
    (haudit : closedCollarSpineCertificateAudit orients cert = true) :
    closedCollarFiberKempeConnected orients cert.key := by
  intro x y
  let fiber := closedCollarFiber orients cert.key
  have hx : x.1 ∈ fiber := x.2
  have hy : y.1 ∈ fiber := y.2
  let i := fiber.idxOf x.1
  let j := fiber.idxOf y.1
  have hi : i < fiber.length := by
    simpa [i] using List.idxOf_lt_length_of_mem hx
  have hj : j < fiber.length := by
    simpa [j] using List.idxOf_lt_length_of_mem hy
  unfold closedCollarSpineCertificateAudit
    closedCollarSpineCertificateAuditFrom at haudit
  simp only [Bool.and_eq_true] at haudit
  rcases haudit with ⟨⟨⟨_hlen, _hrootBound⟩, hrows⟩, hroot⟩
  have hreachI :=
    closedCollarSpineReachParentIter (orients := orients)
      (fiber := fiber) (parents := cert.parents) hrows cert.maxDepth i hi
  have hreachJ :=
    closedCollarSpineReachParentIter_reverse (orients := orients)
      (fiber := fiber) (parents := cert.parents) hrows cert.maxDepth j hj
  rcases hreachI with ⟨hiTarget, hpathI⟩
  rcases hreachJ with ⟨hjTarget, hpathJ⟩
  have hiRoot :
      closedCollarParentIter cert.parents cert.maxDepth i = cert.root :=
    closedCollarSpineParentsReachRoot_index hroot hi
  have hjRoot :
      closedCollarParentIter cert.parents cert.maxDepth j = cert.root :=
    closedCollarSpineParentsReachRoot_index hroot hj
  have hstart :
      (⟨listGetD fiber i [], listGetD_mem_of_lt fiber [] hi⟩ :
        {state // state ∈ fiber}) = x := by
    apply Subtype.ext
    simpa [fiber, i] using listGetD_idxOf_eq_of_mem fiber [] hx
  have hend :
      (⟨listGetD fiber j [], listGetD_mem_of_lt fiber [] hj⟩ :
        {state // state ∈ fiber}) = y := by
    apply Subtype.ext
    simpa [fiber, j] using listGetD_idxOf_eq_of_mem fiber [] hy
  have hmid :
      (⟨listGetD fiber (closedCollarParentIter cert.parents cert.maxDepth i) [],
          listGetD_mem_of_lt fiber [] hiTarget⟩ :
        {state // state ∈ fiber}) =
      ⟨listGetD fiber (closedCollarParentIter cert.parents cert.maxDepth j) [],
          listGetD_mem_of_lt fiber [] hjTarget⟩ := by
    apply Subtype.ext
    simp [hiRoot, hjRoot]
  have hpath := Relation.ReflTransGen.trans hpathI (by
    simpa [hmid] using hpathJ)
  change
    Relation.ReflTransGen
      (fun a b : ClosedCollarFiberPoint orients cert.key =>
        closedCollarSingleKempeStep orients a.1 b.1 = true) x y
  simpa [fiber, ClosedCollarFiberPoint, hstart, hend] using hpath

theorem closedCollarFiberKempeConnected_of_spineCertificateAuditFrom
    {orients : List TauOrient} {statesList : List (List TauState)}
    (cert : ClosedCollarSpineCertificate)
    (hstates : allClosedCollarStates orients = statesList)
    (haudit :
      closedCollarSpineCertificateAuditFrom orients statesList cert = true) :
    closedCollarFiberKempeConnected orients cert.key := by
  apply closedCollarFiberKempeConnected_of_spineCertificateAudit cert
  simpa [closedCollarSpineCertificateAudit, hstates] using haudit

theorem closedCollarFiberKempeConnected_of_pairwiseConnectedCheck
    {orients : List TauOrient} {key : List LColor}
    (hcheck : closedCollarFiberPairwiseConnectedCheck orients key = true) :
    closedCollarFiberKempeConnected orients key := by
  intro x y
  have hpair :=
    boolFiberPairwiseConnected_pairwise
      (fun x y : ClosedCollarFiberPoint orients key =>
        closedCollarSingleKempeStep orients x.1 y.1)
      (fiber := closedCollarFiberPoints orients key)
      (by
        simpa [closedCollarFiberPairwiseConnectedCheck] using hcheck)
      x (mem_closedCollarFiberPoints orients key x)
      y (mem_closedCollarFiberPoints orients key y)
  change
    Relation.ReflTransGen
      (fun a b : ClosedCollarFiberPoint orients key =>
        closedCollarSingleKempeStep orients a.1 b.1 = true) x y
  exact hpair

theorem closedCollarFiberKempeConnected_of_statePairwiseConnectedCheck
    {orients : List TauOrient} {key : List LColor}
    (hcheck : closedCollarStateFiberPairwiseConnectedCheck orients key = true) :
    closedCollarFiberKempeConnected orients key := by
  intro x y
  have hpair :=
    boolFiberPairwiseConnected_subtypeConnected
      (fun x y : List TauState => closedCollarSingleKempeStep orients x y)
      (fiber := closedCollarFiber orients key)
      (by
        simpa [closedCollarStateFiberPairwiseConnectedCheck] using hcheck)
      x y
  change
    Relation.ReflTransGen
      (fun a b : ClosedCollarFiberPoint orients key =>
        closedCollarSingleKempeStep orients a.1 b.1 = true) x y
  exact hpair

end GoertzelLemma818ClosedCollarBridgeProof

end Mettapedia.GraphTheory.FourColor
