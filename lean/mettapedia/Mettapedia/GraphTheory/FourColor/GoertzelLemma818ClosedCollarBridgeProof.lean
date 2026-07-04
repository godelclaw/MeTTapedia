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

def closedCollarSpecifiedKempeStep
    (orients : List TauOrient) (s t : List TauState)
    (move : ChainMove) : Bool :=
  let component := closedCollarComponent orients s move.a move.c move.seed
  !component.isEmpty &&
    closedCollarComponentAvoidsClosingEdges orients component &&
      closedCollarAgreesWithSwitch orients s t component move.a move.c

theorem closedCollarSingleKempeStep_of_specified
    {orients : List TauOrient} {s t : List TauState} {move : ChainMove}
    (hpair : (move.a, move.c) ∈ colorPairs)
    (hseed : move.seed ∈ closedCollarEdges orients)
    (hstep : closedCollarSpecifiedKempeStep orients s t move = true) :
    closedCollarSingleKempeStep orients s t = true := by
  unfold closedCollarSingleKempeStep
  apply list_any_true_of_mem hpair
  exact list_any_true_of_mem hseed (by
    simpa [closedCollarSpecifiedKempeStep] using hstep)

theorem closeClosedCollarComponent_succ_eq
    (orients : List TauOrient) (states : List TauState)
    (a c : LColor) (seen layer : List ChainEdge) (n : Nat)
    (hlayer : closedCollarComponentLayer orients states a c seen = layer) :
    closeClosedCollarComponent orients states a c (n + 1) seen =
      closeClosedCollarComponent orients states a c n (appendFresh seen layer) := by
  simp [closeClosedCollarComponent, hlayer]

theorem closeClosedCollarComponent_eq_self_of_layer_nil
    (orients : List TauOrient) (states : List TauState)
    (a c : LColor) (seen : List ChainEdge)
    (hlayer : closedCollarComponentLayer orients states a c seen = []) :
    ∀ n, closeClosedCollarComponent orients states a c n seen = seen
  | 0 => rfl
  | n + 1 => by
      rw [closeClosedCollarComponent_succ_eq
        orients states a c seen [] n hlayer]
      simpa [appendFresh] using
        closeClosedCollarComponent_eq_self_of_layer_nil
          orients states a c seen hlayer n

theorem closedCollarSingleKempeStep_of_component
    {orients : List TauOrient} {s t : List TauState} {move : ChainMove}
    {component : List ChainEdge}
    (hpair : (move.a, move.c) ∈ colorPairs)
    (hseed : move.seed ∈ closedCollarEdges orients)
    (hcomponent :
      closedCollarComponent orients s move.a move.c move.seed = component)
    (hnonempty : (!component.isEmpty) = true)
    (havoid : closedCollarComponentAvoidsClosingEdges orients component = true)
    (hagree :
      closedCollarAgreesWithSwitch orients s t component move.a move.c = true) :
    closedCollarSingleKempeStep orients s t = true := by
  unfold closedCollarSingleKempeStep
  apply list_any_true_of_mem hpair
  apply list_any_true_of_mem hseed
  simp [hcomponent, hnonempty, havoid, hagree]

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

theorem bindList_eq_flatMap {α β : Type}
    (xs : List α) (f : α → List β) :
    bindList xs f = xs.flatMap f := by
  induction xs with
  | nil =>
      simp [bindList]
  | cons _ _ _ =>
      simp [bindList, List.flatMap]

theorem filter_bindList_bool {α β : Type}
    (xs : List α) (f : α → List β) (p : β → Bool) :
    (bindList xs f).filter p =
      bindList xs (fun x => (f x).filter p) := by
  simp [bindList_eq_flatMap, List.filter_flatMap]

theorem filter_map_bool {α β : Type}
    (xs : List α) (f : α → β) (p : β → Bool) :
    (xs.map f).filter p = (xs.filter fun x => p (f x)).map f := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.filter_cons]
      by_cases hp : p (f x) = true
      · simp [hp, ih]
      · have hf : p (f x) = false := bool_false_of_not_true hp
        simp [hf, ih]

theorem bindList_map {α β γ : Type}
    (xs : List α) (f : α → β) (g : β → List γ) :
    bindList (xs.map f) g = bindList xs (fun x => g (f x)) := by
  simp [bindList_eq_flatMap, List.flatMap_map]

theorem bindList_assoc {α β γ : Type}
    (xs : List α) (f : α → List β) (g : β → List γ) :
    bindList (bindList xs f) g =
      bindList xs (fun x => bindList (f x) g) := by
  simp [bindList_eq_flatMap, List.flatMap_assoc]

theorem bindList_flatten {α β : Type}
    (xss : List (List α)) (f : α → List β) :
    bindList xss.flatten f = bindList xss (fun xs => bindList xs f) := by
  simpa [bindList_eq_flatMap, List.flatMap_assoc]
    using (List.flatMap_assoc (l := xss) (f := id) (g := f))

theorem bindList_eq_flatten_of_getD {α β : Type}
    (xs : List α) (chunks : List (List β)) (f : α → List β)
    (fallback : α)
    (hlen : xs.length = chunks.length)
    (hget :
      ∀ i, i < xs.length →
        f (listGetD xs i fallback) = listGetD chunks i []) :
    bindList xs f = chunks.flatten := by
  induction xs generalizing chunks with
  | nil =>
      cases chunks with
      | nil =>
          rfl
      | cons _ _ =>
          simp at hlen
  | cons x xs ih =>
      cases chunks with
      | nil =>
          simp at hlen
      | cons chunk chunks =>
          have hhead := hget 0 (by simp)
          simp [listGetD] at hhead
          have hlenTail : xs.length = chunks.length :=
            Nat.succ.inj hlen
          have htail :
              bindList xs f = chunks.flatten := by
            apply ih chunks hlenTail
            intro i hi
            have h := hget (i + 1) (by simp [hi])
            simpa [listGetD] using h
          calc
            bindList (x :: xs) f = f x ++ bindList xs f := by
              simp [bindList]
            _ = chunk ++ chunks.flatten := by rw [hhead, htail]
            _ = (chunk :: chunks).flatten := rfl

theorem list_eq_join_chunks_of_drop_take {α : Type}
    (xs : List α) (chunkSize : Nat) (chunks : List (List α))
    (hchunks :
      ∀ i, i < chunks.length →
        (xs.drop (i * chunkSize)).take chunkSize = listGetD chunks i [])
    (hterminal : xs.drop (chunks.length * chunkSize) = []) :
    xs = chunks.flatten := by
  induction chunks generalizing xs with
  | nil =>
      simpa using hterminal
  | cons chunk chunks ih =>
      have hhead : xs.take chunkSize = chunk := by
        have h := hchunks 0 (by simp)
        simpa [listGetD] using h
      have htail : xs.drop chunkSize = chunks.flatten := by
        apply ih (xs.drop chunkSize)
        · intro i hi
          have h := hchunks (i + 1) (by simp [hi])
          simpa [listGetD, List.drop_drop, Nat.succ_mul,
            Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
        · simpa [List.drop_drop, Nat.succ_mul, Nat.add_comm,
            Nat.add_left_comm, Nat.add_assoc] using hterminal
      calc
        xs = xs.take chunkSize ++ xs.drop chunkSize := by
          exact (List.take_append_drop chunkSize xs).symm
        _ = chunk ++ chunks.flatten := by rw [hhead, htail]
        _ = (chunk :: chunks).flatten := rfl

def closedCollarFiber3Prefix
    (orients : List TauOrient) (key : List LColor) :
    List (List TauState) :=
  bindList allTauStates fun s0 =>
  bindList (allTauStates.filter fun s1 =>
      compatibleAdjacent (tauOrientAt orients 0) (tauOrientAt orients 1)
        s0 s1) fun s1 =>
  (allTauStates.filter fun s2 =>
      closedCollarKey orients [s0, s1, s2] == key &&
      (compatibleAdjacent (tauOrientAt orients 2) (tauOrientAt orients 0)
          s2 s0 &&
        compatibleAdjacent (tauOrientAt orients 1) (tauOrientAt orients 2)
          s1 s2)).map fun s2 =>
    [s0, s1, s2]

def closedCollarFiber3Keyed
    (orients : List TauOrient) (key : List LColor) :
    List (List TauState) :=
  let keyedLast := allTauStates.filter fun s2 =>
    closedCollarKey orients [default, default, s2] == key
  bindList allTauStates fun s0 =>
  bindList (allTauStates.filter fun s1 =>
      compatibleAdjacent (tauOrientAt orients 0) (tauOrientAt orients 1)
        s0 s1) fun s1 =>
  (keyedLast.filter fun s2 =>
      compatibleAdjacent (tauOrientAt orients 1) (tauOrientAt orients 2)
        s1 s2 &&
      compatibleAdjacent (tauOrientAt orients 2) (tauOrientAt orients 0)
        s2 s0).map fun s2 =>
    [s0, s1, s2]

def closedCollarFiber3KeyedFromFirsts
    (orients : List TauOrient) (keyedLast firsts : List TauState) :
    List (List TauState) :=
  bindList firsts fun s0 =>
  bindList (allTauStates.filter fun s1 =>
      compatibleAdjacent (tauOrientAt orients 0) (tauOrientAt orients 1)
        s0 s1) fun s1 =>
  (keyedLast.filter fun s2 =>
      compatibleAdjacent (tauOrientAt orients 1) (tauOrientAt orients 2)
        s1 s2 &&
      compatibleAdjacent (tauOrientAt orients 2) (tauOrientAt orients 0)
        s2 s0).map fun s2 =>
    [s0, s1, s2]

def closedCollarFiber3KeyedFrom
    (orients : List TauOrient) (keyedLast : List TauState) :
    List (List TauState) :=
  closedCollarFiber3KeyedFromFirsts orients keyedLast allTauStates

theorem closedCollarFiber3Keyed_eq_from
    (orients : List TauOrient) (key : List LColor)
    {keyedLast : List TauState}
    (hkeyed :
      (allTauStates.filter fun s2 =>
        closedCollarKey orients [default, default, s2] == key) =
        keyedLast) :
    closedCollarFiber3Keyed orients key =
      closedCollarFiber3KeyedFrom orients keyedLast := by
  simp [closedCollarFiber3Keyed, closedCollarFiber3KeyedFrom,
    closedCollarFiber3KeyedFromFirsts, hkeyed]

theorem closedCollarFiber3KeyedFrom_eq_chunks
    (orients : List TauOrient) (keyedLast : List TauState)
    (firstChunks : List (List TauState))
    (fiberChunks : List (List (List TauState)))
    (hfirst : allTauStates = firstChunks.flatten)
    (hlen : firstChunks.length = fiberChunks.length)
    (hchunks :
      ∀ i, i < firstChunks.length →
        closedCollarFiber3KeyedFromFirsts orients keyedLast
            (listGetD firstChunks i []) =
          listGetD fiberChunks i []) :
    closedCollarFiber3KeyedFrom orients keyedLast = fiberChunks.flatten := by
  unfold closedCollarFiber3KeyedFrom
  rw [hfirst]
  unfold closedCollarFiber3KeyedFromFirsts
  rw [bindList_flatten]
  change
    bindList firstChunks
        (fun firsts =>
          closedCollarFiber3KeyedFromFirsts orients keyedLast firsts) =
      fiberChunks.flatten
  exact
    bindList_eq_flatten_of_getD firstChunks fiberChunks
      (fun firsts =>
        closedCollarFiber3KeyedFromFirsts orients keyedLast firsts)
      ([] : List TauState) hlen hchunks

theorem closedCollarFiber3KeyedFrom_nil
    (orients : List TauOrient) :
    closedCollarFiber3KeyedFrom orients [] = [] := by
  simp [closedCollarFiber3KeyedFrom, closedCollarFiber3KeyedFromFirsts,
    bindList_eq_flatMap]

theorem closedCollarFiber_three_eq_prefix
    (o0 o1 o2 : TauOrient) (key : List LColor) :
    closedCollarFiber [o0, o1, o2] key =
      closedCollarFiber3Prefix [o0, o1, o2] key := by
  unfold closedCollarFiber closedCollarFiberFrom allClosedCollarStates
    allChainStates
  simp only [List.length_cons, List.length_nil]
  rw [buildChainStatesFrom.eq_2, buildChainStatesFrom.eq_2,
    buildChainStatesFrom.eq_1]
  unfold extendChainStates closedCollarFiber3Prefix
    closedCollarClosureCompatible
  rw [filter_bindList_bool]
  simp only [filter_map_bool, filter_bindList_bool, bindList_assoc,
    bindList_map]
  simp [List.filter_filter, chainStateAt, listGetD]

theorem closedCollarKey_three_last
    (o0 o1 o2 : TauOrient) (s0 s1 s2 : TauState)
    (key : List LColor) :
    (closedCollarKey [o0, o1, o2] [s0, s1, s2] == key) =
      (closedCollarKey [o0, o1, o2] [default, default, s2] == key) := by
  cases o2 <;>
    simp [closedCollarKey, closedCollarClosingEdges, chainEdgeColor,
      tauStateColorAt, chainStateAt, listGetD, chainOutputOrder,
      tauOrientOutputOrder, tauOrientAt]

theorem closedCollarFiber3Prefix_eq_keyed
    (o0 o1 o2 : TauOrient) (key : List LColor) :
    closedCollarFiber3Prefix [o0, o1, o2] key =
      closedCollarFiber3Keyed [o0, o1, o2] key := by
  unfold closedCollarFiber3Prefix closedCollarFiber3Keyed
  apply congrArg (bindList allTauStates)
  funext s0
  apply congrArg (bindList (List.filter
    (fun s1 => compatibleAdjacent (tauOrientAt [o0, o1, o2] 0)
      (tauOrientAt [o0, o1, o2] 1) s0 s1) allTauStates))
  funext s1
  apply congrArg (List.map fun s2 => [s0, s1, s2])
  rw [List.filter_filter]
  apply List.filter_congr
  intro s2 _hs2
  rw [closedCollarKey_three_last o0 o1 o2 s0 s1 s2 key]
  simp [Bool.and_assoc, Bool.and_comm]

theorem closedCollarFiber_three_eq_keyed
    (o0 o1 o2 : TauOrient) (key : List LColor) :
    closedCollarFiber [o0, o1, o2] key =
      closedCollarFiber3Keyed [o0, o1, o2] key := by
  rw [closedCollarFiber_three_eq_prefix,
    closedCollarFiber3Prefix_eq_keyed]

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

theorem closedCollarIndexStepBool_of_specified
    {orients : List TauOrient} {fiber : List (List TauState)}
    {i j : Nat} {move : ChainMove}
    (hpair : (move.a, move.c) ∈ colorPairs)
    (hseed : move.seed ∈ closedCollarEdges orients)
    (hstep :
      closedCollarSpecifiedKempeStep orients
        (listGetD fiber i []) (listGetD fiber j []) move = true) :
    closedCollarIndexStepBool orients fiber i j = true := by
  unfold closedCollarIndexStepBool
  exact closedCollarSingleKempeStep_of_specified hpair hseed hstep

theorem closedCollarIndexStepBool_of_component
    {orients : List TauOrient} {fiber : List (List TauState)}
    {i j : Nat} {move : ChainMove} {component : List ChainEdge}
    (hpair : (move.a, move.c) ∈ colorPairs)
    (hseed : move.seed ∈ closedCollarEdges orients)
    (hcomponent :
      closedCollarComponent orients (listGetD fiber i [])
        move.a move.c move.seed = component)
    (hnonempty : (!component.isEmpty) = true)
    (havoid : closedCollarComponentAvoidsClosingEdges orients component = true)
    (hagree :
      closedCollarAgreesWithSwitch orients
        (listGetD fiber i []) (listGetD fiber j [])
        component move.a move.c = true) :
    closedCollarIndexStepBool orients fiber i j = true := by
  unfold closedCollarIndexStepBool
  exact closedCollarSingleKempeStep_of_component hpair hseed
    hcomponent hnonempty havoid hagree

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

def closedCollarSpineCertificateAuditForFiber
    (orients : List TauOrient) (fiber : List (List TauState))
    (cert : ClosedCollarSpineCertificate) : Bool :=
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

theorem closedCollarSpineRowsValid_of_index
    {orients : List TauOrient} {fiber : List (List TauState)}
    {parents : List Nat}
    (hindex :
      ∀ i, i < fiber.length →
        closedCollarParentIndexValid orients fiber parents i = true) :
    closedCollarSpineRowsValid orients fiber parents = true := by
  unfold closedCollarSpineRowsValid
  rw [List.all_eq_true]
  intro i hi
  exact hindex i (List.mem_range.mp hi)

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

theorem closedCollarFiberKempeConnected_of_spineRowsForFiber
    {orients : List TauOrient} {statesList fiber : List (List TauState)}
    (cert : ClosedCollarSpineCertificate)
    (hstates : allClosedCollarStates orients = statesList)
    (hfiber : closedCollarFiberFrom orients statesList cert.key = fiber)
    (hrows : closedCollarSpineRowsValid orients fiber cert.parents = true)
    (hroot : closedCollarSpineParentsReachRoot fiber cert = true) :
    closedCollarFiberKempeConnected orients cert.key := by
  have hclosed : closedCollarFiber orients cert.key = fiber := by
    unfold closedCollarFiber
    rw [hstates, hfiber]
  unfold closedCollarFiberKempeConnected closedCollarKempeStep ClosedCollarFiberPoint
  rw [hclosed]
  intro x y
  have hx : x.1 ∈ fiber := x.2
  have hy : y.1 ∈ fiber := y.2
  let i := fiber.idxOf x.1
  let j := fiber.idxOf y.1
  have hi : i < fiber.length := by
    simpa [i] using List.idxOf_lt_length_of_mem hx
  have hj : j < fiber.length := by
    simpa [j] using List.idxOf_lt_length_of_mem hy
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
        {state // state ∈ fiber}) = ⟨x.1, hx⟩ := by
    apply Subtype.ext
    simpa [i] using listGetD_idxOf_eq_of_mem fiber [] hx
  have hend :
      (⟨listGetD fiber j [], listGetD_mem_of_lt fiber [] hj⟩ :
        {state // state ∈ fiber}) = ⟨y.1, hy⟩ := by
    apply Subtype.ext
    simpa [j] using listGetD_idxOf_eq_of_mem fiber [] hy
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
  have hpathXY :
      Relation.ReflTransGen
        (fun a b : {state // state ∈ fiber} =>
          closedCollarSingleKempeStep orients a.1 b.1 = true)
        ⟨x.1, hx⟩ ⟨y.1, hy⟩ := by
    simpa [hstart, hend] using hpath
  simpa [closedCollarKempeStep] using hpathXY

theorem closedCollarFiberKempeConnected_of_spineRowsForClosedFiber
    {orients : List TauOrient} {fiber : List (List TauState)}
    (cert : ClosedCollarSpineCertificate)
    (hfiber : closedCollarFiber orients cert.key = fiber)
    (hrows : closedCollarSpineRowsValid orients fiber cert.parents = true)
    (hroot : closedCollarSpineParentsReachRoot fiber cert = true) :
    closedCollarFiberKempeConnected orients cert.key :=
  closedCollarFiberKempeConnected_of_spineRowsForFiber cert rfl
    (by simpa [closedCollarFiber] using hfiber) hrows hroot

theorem closedCollarFiberKempeConnected_of_spineCertificateAuditForFiber
    {orients : List TauOrient} {statesList fiber : List (List TauState)}
    (cert : ClosedCollarSpineCertificate)
    (hstates : allClosedCollarStates orients = statesList)
    (hfiber : closedCollarFiberFrom orients statesList cert.key = fiber)
    (haudit :
      closedCollarSpineCertificateAuditForFiber orients fiber cert = true) :
    closedCollarFiberKempeConnected orients cert.key := by
  have hclosed : closedCollarFiber orients cert.key = fiber := by
    unfold closedCollarFiber
    rw [hstates, hfiber]
  unfold closedCollarFiberKempeConnected closedCollarKempeStep ClosedCollarFiberPoint
  rw [hclosed]
  intro x y
  have hx : x.1 ∈ fiber := x.2
  have hy : y.1 ∈ fiber := y.2
  let i := fiber.idxOf x.1
  let j := fiber.idxOf y.1
  have hi : i < fiber.length := by
    simpa [i] using List.idxOf_lt_length_of_mem hx
  have hj : j < fiber.length := by
    simpa [j] using List.idxOf_lt_length_of_mem hy
  unfold closedCollarSpineCertificateAuditForFiber at haudit
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
        {state // state ∈ fiber}) = ⟨x.1, hx⟩ := by
    apply Subtype.ext
    simpa [i] using listGetD_idxOf_eq_of_mem fiber [] hx
  have hend :
      (⟨listGetD fiber j [], listGetD_mem_of_lt fiber [] hj⟩ :
        {state // state ∈ fiber}) = ⟨y.1, hy⟩ := by
    apply Subtype.ext
    simpa [j] using listGetD_idxOf_eq_of_mem fiber [] hy
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
  have hpathXY :
      Relation.ReflTransGen
        (fun a b : {state // state ∈ fiber} =>
          closedCollarSingleKempeStep orients a.1 b.1 = true)
        ⟨x.1, hx⟩ ⟨y.1, hy⟩ := by
    simpa [hstart, hend] using hpath
  simpa [closedCollarKempeStep] using hpathXY

theorem closedCollarFiberKempeConnected_of_fiberFrom_eq_nil
    {orients : List TauOrient} {statesList : List (List TauState)}
    {key : List LColor}
    (hstates : allClosedCollarStates orients = statesList)
    (hempty : closedCollarFiberFrom orients statesList key = []) :
    closedCollarFiberKempeConnected orients key := by
  intro x _y
  have hxFiber : x.1 ∈ closedCollarFiberFrom orients statesList key := by
    have hx : x.1 ∈ closedCollarFiber orients key := x.2
    unfold closedCollarFiber at hx
    simpa [hstates] using hx
  have hxEmpty : x.1 ∈ ([] : List (List TauState)) := by
    rw [hempty] at hxFiber
    exact hxFiber
  cases hxEmpty

theorem closedCollarFiberKempeConnected_of_closedFiber_eq_nil
    {orients : List TauOrient} {key : List LColor}
    (hempty : closedCollarFiber orients key = []) :
    closedCollarFiberKempeConnected orients key :=
  closedCollarFiberKempeConnected_of_fiberFrom_eq_nil
    (orients := orients) (statesList := allClosedCollarStates orients)
    (key := key) rfl (by simpa [closedCollarFiber] using hempty)

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
