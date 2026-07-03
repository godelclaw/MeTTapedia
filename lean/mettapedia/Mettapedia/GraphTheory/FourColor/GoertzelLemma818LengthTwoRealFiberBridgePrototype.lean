import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoDirectClosurePrototype
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoDirectClosureMultiPassPrototype
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoLargeFiber8Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoLargeFiber10Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoLargeFiber20Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoLargeFiber30Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoLargeFiber36Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoLargeFiber44Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoLargeFiber50Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoLargeFiber60Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoLargeFiber70Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoLargeFiber72Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoLargeFiber76Bridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoShapeABridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoShapeBBridge

namespace Mettapedia.GraphTheory.FourColor

/-!
# Prototype real-fiber bridge for one generated length-two fiber

This module proves that the first nonempty `tau,tau` real fiber has the same
members as the generated direct-state list.  It avoids the failing global
`chainFiberFrom (allChainStates ...)` reduction by splitting the length-two
state construction into left-state chunks.
-/

namespace GoertzelLemma818LengthTwoRealFiberBridgePrototype

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818LengthTwoDirectClosurePrototype
open GoertzelLemma818LengthTwoDirectClosureMultiPassPrototype
open GoertzelLemma818LengthTwoShapeABridge
open GoertzelLemma818LengthTwoShapeBBridge

theorem bindList_mem {α β : Type} {xs : List α} {f : α → List β} {y : β} :
    y ∈ bindList xs f ↔ ∃ x, x ∈ xs ∧ y ∈ f x := by
  induction xs with
  | nil =>
      simp [bindList]
  | cons x xs ih =>
      simp [bindList, or_and_right, exists_or]

theorem bindList_map {α β γ : Type} (xs : List α) (g : α → β) (f : β → List γ) :
    bindList (xs.map g) f = bindList xs (fun x => f (g x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [bindList, Function.comp_def]

theorem bindList_filter {α β : Type} (xs : List α) (f : α → List β) (p : β → Bool) :
    (bindList xs f).filter p = bindList xs (fun x => (f x).filter p) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [bindList, List.filter_append, Function.comp_def]

theorem bindList_append {α β : Type} (xs ys : List α) (f : α → List β) :
    bindList (xs ++ ys) f = bindList xs f ++ bindList ys f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [bindList, List.append_assoc]

def lengthTwoStatesFromLeft (word : List TauOrient) (left : TauState) :
    List (List TauState) :=
  (allTauStates.filter fun right =>
    compatibleAdjacent (tauOrientAt word 0) (tauOrientAt word 1) left right).map fun right =>
      [left, right]

theorem ttAllChainStates_lengthTwo_eq :
    allChainStates ttWord = bindList allTauStates fun left => lengthTwoStatesFromLeft ttWord left := by
  simp [ttWord, allChainStates, buildChainStatesFrom, extendChainStates,
    lengthTwoStatesFromLeft, chainStateAt, tauOrientAt, listGetD, bindList_map]

def tauStateChunk32 (start : Nat) : List TauState :=
  (allTauStates.drop start).take 32

def tauStateTail192 : List TauState :=
  allTauStates.drop 192

theorem allTauStates_eq_chunks32 :
    allTauStates =
      tauStateChunk32 0 ++ tauStateChunk32 32 ++ tauStateChunk32 64 ++
      tauStateChunk32 96 ++ tauStateChunk32 128 ++ tauStateChunk32 160 ++
      tauStateTail192 := by
  unfold tauStateChunk32 tauStateTail192
  conv_lhs => rw [← List.take_append_drop 32 allTauStates]
  conv_lhs => rw [← List.take_append_drop 32 (allTauStates.drop 32)]
  conv_lhs => rw [← List.take_append_drop 32 ((allTauStates.drop 32).drop 32)]
  conv_lhs => rw [← List.take_append_drop 32 (((allTauStates.drop 32).drop 32).drop 32)]
  conv_lhs => rw [← List.take_append_drop 32 ((((allTauStates.drop 32).drop 32).drop 32).drop 32)]
  conv_lhs => rw [← List.take_append_drop 32 (((((allTauStates.drop 32).drop 32).drop 32).drop 32).drop 32)]
  simp [List.drop_drop]

def lengthTwoFiberCoverLeftState (word : List TauOrient) (key : List LColor)
    (direct : List (List TauState)) (left : TauState) : Bool :=
  (lengthTwoStatesFromLeft word left).all fun states =>
    !(chainInputKey word states == key) || direct.contains states

def lengthTwoFiberCoverLeftStateList (word : List TauOrient) (key : List LColor)
    (direct : List (List TauState)) (lefts : List TauState) : Bool :=
  lefts.all fun left => lengthTwoFiberCoverLeftState word key direct left

def lengthTwoFiberCoverAllLefts (word : List TauOrient) (key : List LColor)
    (direct : List (List TauState)) : Bool :=
  allTauStates.all fun left => lengthTwoFiberCoverLeftState word key direct left

theorem lengthTwoFiberCoverAllLefts_of_chunks
    (word : List TauOrient) (key : List LColor) (direct : List (List TauState))
    (h0 : lengthTwoFiberCoverLeftStateList word key direct (tauStateChunk32 0) = true)
    (h1 : lengthTwoFiberCoverLeftStateList word key direct (tauStateChunk32 32) = true)
    (h2 : lengthTwoFiberCoverLeftStateList word key direct (tauStateChunk32 64) = true)
    (h3 : lengthTwoFiberCoverLeftStateList word key direct (tauStateChunk32 96) = true)
    (h4 : lengthTwoFiberCoverLeftStateList word key direct (tauStateChunk32 128) = true)
    (h5 : lengthTwoFiberCoverLeftStateList word key direct (tauStateChunk32 160) = true)
    (h6 : lengthTwoFiberCoverLeftStateList word key direct tauStateTail192 = true) :
    lengthTwoFiberCoverAllLefts word key direct = true := by
  unfold lengthTwoFiberCoverLeftStateList at h0 h1 h2 h3 h4 h5 h6
  unfold lengthTwoFiberCoverAllLefts
  rw [allTauStates_eq_chunks32]
  simp only [List.all_append]
  simp [h0, h1, h2, h3, h4, h5, h6]

def ttFiber3CoverLeftChunk (start len : Nat) : Bool :=
  lengthTwoFiberCoverLeftStateList ttWord ttFiber3Key ttFiber3DirectStates
    ((allTauStates.drop start).take len)

theorem ttFiber3CoverLeftChunk_0_ok : ttFiber3CoverLeftChunk 0 32 = true := by
  decide

theorem ttFiber3CoverLeftChunk_32_ok : ttFiber3CoverLeftChunk 32 32 = true := by
  decide

theorem ttFiber3CoverLeftChunk_64_ok : ttFiber3CoverLeftChunk 64 32 = true := by
  decide

theorem ttFiber3CoverLeftChunk_96_ok : ttFiber3CoverLeftChunk 96 32 = true := by
  decide

theorem ttFiber3CoverLeftChunk_128_ok : ttFiber3CoverLeftChunk 128 32 = true := by
  decide

theorem ttFiber3CoverLeftChunk_160_ok : ttFiber3CoverLeftChunk 160 32 = true := by
  decide

theorem ttFiber3CoverLeftTail_ok :
    lengthTwoFiberCoverLeftStateList ttWord ttFiber3Key ttFiber3DirectStates
      tauStateTail192 = true := by
  decide

theorem ttFiber3CoverAllLefts_ok :
    lengthTwoFiberCoverAllLefts ttWord ttFiber3Key ttFiber3DirectStates = true := by
  exact lengthTwoFiberCoverAllLefts_of_chunks ttWord ttFiber3Key ttFiber3DirectStates
    ttFiber3CoverLeftChunk_0_ok ttFiber3CoverLeftChunk_32_ok
    ttFiber3CoverLeftChunk_64_ok ttFiber3CoverLeftChunk_96_ok
    ttFiber3CoverLeftChunk_128_ok ttFiber3CoverLeftChunk_160_ok
    ttFiber3CoverLeftTail_ok

theorem tt_direct_contains_of_cover_all
    {states : List TauState} {key : List LColor} {direct : List (List TauState)}
    (hall : lengthTwoFiberCoverAllLefts ttWord key direct = true)
    (hmem : states ∈ allChainStates ttWord)
    (hkey : (chainInputKey ttWord states == key) = true) :
    direct.contains states = true := by
  unfold lengthTwoFiberCoverAllLefts at hall
  rw [List.all_eq_true] at hall
  rw [ttAllChainStates_lengthTwo_eq] at hmem
  rw [bindList_mem] at hmem
  rcases hmem with ⟨left, hleft, hstates⟩
  have hcover := hall left hleft
  unfold lengthTwoFiberCoverLeftState at hcover
  rw [List.all_eq_true] at hcover
  have hrow := hcover states hstates
  simpa [hkey] using hrow

theorem ttFiber3RealFiber_subset_direct {states : List TauState}
    (h : states ∈ chainFiberFrom ttWord (allChainStates ttWord) ttFiber3Key) :
    states ∈ ttFiber3DirectStates := by
  unfold chainFiberFrom at h
  rw [List.mem_filter] at h
  rcases h with ⟨hall, hkey⟩
  exact List.contains_iff_mem.mp
    (tt_direct_contains_of_cover_all ttFiber3CoverAllLefts_ok hall hkey)

theorem ttFiber3State0_mem_allChainStates :
    ttFiber3StateAt 0 ∈ allChainStates ttWord := by
  rw [ttAllChainStates_lengthTwo_eq]
  rw [bindList_mem]
  refine ⟨stateAt 114, by decide, ?_⟩
  unfold lengthTwoStatesFromLeft
  rw [List.mem_map]
  refine ⟨stateAt 52, ?_, ?_⟩
  · rw [List.mem_filter]
    exact ⟨by decide, by decide⟩
  · rfl

theorem ttFiber3State0_mem_realFiber :
    ttFiber3StateAt 0 ∈ chainFiberFrom ttWord (allChainStates ttWord) ttFiber3Key := by
  unfold chainFiberFrom
  rw [List.mem_filter]
  exact ⟨ttFiber3State0_mem_allChainStates, by decide⟩

theorem ttFiber3State1_mem_allChainStates :
    ttFiber3StateAt 1 ∈ allChainStates ttWord := by
  rw [ttAllChainStates_lengthTwo_eq]
  rw [bindList_mem]
  refine ⟨stateAt 114, by decide, ?_⟩
  unfold lengthTwoStatesFromLeft
  rw [List.mem_map]
  refine ⟨stateAt 53, ?_, ?_⟩
  · rw [List.mem_filter]
    exact ⟨by decide, by decide⟩
  · rfl

theorem ttFiber3State1_mem_realFiber :
    ttFiber3StateAt 1 ∈ chainFiberFrom ttWord (allChainStates ttWord) ttFiber3Key := by
  unfold chainFiberFrom
  rw [List.mem_filter]
  exact ⟨ttFiber3State1_mem_allChainStates, by decide⟩

theorem ttFiber3State2_mem_allChainStates :
    ttFiber3StateAt 2 ∈ allChainStates ttWord := by
  rw [ttAllChainStates_lengthTwo_eq]
  rw [bindList_mem]
  refine ⟨stateAt 114, by decide, ?_⟩
  unfold lengthTwoStatesFromLeft
  rw [List.mem_map]
  refine ⟨stateAt 54, ?_, ?_⟩
  · rw [List.mem_filter]
    exact ⟨by decide, by decide⟩
  · rfl

theorem ttFiber3State2_mem_realFiber :
    ttFiber3StateAt 2 ∈ chainFiberFrom ttWord (allChainStates ttWord) ttFiber3Key := by
  unfold chainFiberFrom
  rw [List.mem_filter]
  exact ⟨ttFiber3State2_mem_allChainStates, by decide⟩

theorem ttFiber3State3_mem_allChainStates :
    ttFiber3StateAt 3 ∈ allChainStates ttWord := by
  rw [ttAllChainStates_lengthTwo_eq]
  rw [bindList_mem]
  refine ⟨stateAt 114, by decide, ?_⟩
  unfold lengthTwoStatesFromLeft
  rw [List.mem_map]
  refine ⟨stateAt 55, ?_, ?_⟩
  · rw [List.mem_filter]
    exact ⟨by decide, by decide⟩
  · rfl

theorem ttFiber3State3_mem_realFiber :
    ttFiber3StateAt 3 ∈ chainFiberFrom ttWord (allChainStates ttWord) ttFiber3Key := by
  unfold chainFiberFrom
  rw [List.mem_filter]
  exact ⟨ttFiber3State3_mem_allChainStates, by decide⟩

theorem ttFiber3State4_mem_allChainStates :
    ttFiber3StateAt 4 ∈ allChainStates ttWord := by
  rw [ttAllChainStates_lengthTwo_eq]
  rw [bindList_mem]
  refine ⟨stateAt 115, by decide, ?_⟩
  unfold lengthTwoStatesFromLeft
  rw [List.mem_map]
  refine ⟨stateAt 60, ?_, ?_⟩
  · rw [List.mem_filter]
    exact ⟨by decide, by decide⟩
  · rfl

theorem ttFiber3State4_mem_realFiber :
    ttFiber3StateAt 4 ∈ chainFiberFrom ttWord (allChainStates ttWord) ttFiber3Key := by
  unfold chainFiberFrom
  rw [List.mem_filter]
  exact ⟨ttFiber3State4_mem_allChainStates, by decide⟩

theorem ttFiber3State5_mem_allChainStates :
    ttFiber3StateAt 5 ∈ allChainStates ttWord := by
  rw [ttAllChainStates_lengthTwo_eq]
  rw [bindList_mem]
  refine ⟨stateAt 115, by decide, ?_⟩
  unfold lengthTwoStatesFromLeft
  rw [List.mem_map]
  refine ⟨stateAt 61, ?_, ?_⟩
  · rw [List.mem_filter]
    exact ⟨by decide, by decide⟩
  · rfl

theorem ttFiber3State5_mem_realFiber :
    ttFiber3StateAt 5 ∈ chainFiberFrom ttWord (allChainStates ttWord) ttFiber3Key := by
  unfold chainFiberFrom
  rw [List.mem_filter]
  exact ⟨ttFiber3State5_mem_allChainStates, by decide⟩

theorem ttFiber3State6_mem_allChainStates :
    ttFiber3StateAt 6 ∈ allChainStates ttWord := by
  rw [ttAllChainStates_lengthTwo_eq]
  rw [bindList_mem]
  refine ⟨stateAt 115, by decide, ?_⟩
  unfold lengthTwoStatesFromLeft
  rw [List.mem_map]
  refine ⟨stateAt 62, ?_, ?_⟩
  · rw [List.mem_filter]
    exact ⟨by decide, by decide⟩
  · rfl

theorem ttFiber3State6_mem_realFiber :
    ttFiber3StateAt 6 ∈ chainFiberFrom ttWord (allChainStates ttWord) ttFiber3Key := by
  unfold chainFiberFrom
  rw [List.mem_filter]
  exact ⟨ttFiber3State6_mem_allChainStates, by decide⟩

theorem ttFiber3State7_mem_allChainStates :
    ttFiber3StateAt 7 ∈ allChainStates ttWord := by
  rw [ttAllChainStates_lengthTwo_eq]
  rw [bindList_mem]
  refine ⟨stateAt 115, by decide, ?_⟩
  unfold lengthTwoStatesFromLeft
  rw [List.mem_map]
  refine ⟨stateAt 63, ?_, ?_⟩
  · rw [List.mem_filter]
    exact ⟨by decide, by decide⟩
  · rfl

theorem ttFiber3State7_mem_realFiber :
    ttFiber3StateAt 7 ∈ chainFiberFrom ttWord (allChainStates ttWord) ttFiber3Key := by
  unfold chainFiberFrom
  rw [List.mem_filter]
  exact ⟨ttFiber3State7_mem_allChainStates, by decide⟩

theorem ttFiber3Direct_subset_realFiber {states : List TauState}
    (h : states ∈ ttFiber3DirectStates) :
    states ∈ chainFiberFrom ttWord (allChainStates ttWord) ttFiber3Key := by
  simp only [ttFiber3DirectStates, List.mem_cons, List.not_mem_nil] at h
  rcases h with h | h | h | h | h | h | h | h | h
  · subst states
    exact ttFiber3State0_mem_realFiber
  · subst states
    exact ttFiber3State1_mem_realFiber
  · subst states
    exact ttFiber3State2_mem_realFiber
  · subst states
    exact ttFiber3State3_mem_realFiber
  · subst states
    exact ttFiber3State4_mem_realFiber
  · subst states
    exact ttFiber3State5_mem_realFiber
  · subst states
    exact ttFiber3State6_mem_realFiber
  · subst states
    exact ttFiber3State7_mem_realFiber
  · cases h

theorem ttFiber3RealFiber_same_members (states : List TauState) :
    states ∈ chainFiberFrom ttWord (allChainStates ttWord) ttFiber3Key ↔
      states ∈ ttFiber3DirectStates :=
  ⟨ttFiber3RealFiber_subset_direct, ttFiber3Direct_subset_realFiber⟩

def lengthTwoFiberExtractLeftState (word : List TauOrient) (key : List LColor)
    (left : TauState) : List (List TauState) :=
  (lengthTwoStatesFromLeft word left).filter fun states => chainInputKey word states == key

def lengthTwoFiberExtractLeftStateList (word : List TauOrient) (key : List LColor)
    (lefts : List TauState) : List (List TauState) :=
  bindList lefts fun left => lengthTwoFiberExtractLeftState word key left

theorem lengthTwoFiberExtractLeftStateList_append (word : List TauOrient) (key : List LColor)
    (xs ys : List TauState) :
    lengthTwoFiberExtractLeftStateList word key (xs ++ ys) =
      lengthTwoFiberExtractLeftStateList word key xs ++
        lengthTwoFiberExtractLeftStateList word key ys := by
  unfold lengthTwoFiberExtractLeftStateList
  exact bindList_append xs ys fun left => lengthTwoFiberExtractLeftState word key left

theorem chainFiberFrom_tt_lengthTwo_eq_extracts (key : List LColor) :
    chainFiberFrom ttWord (allChainStates ttWord) key =
      lengthTwoFiberExtractLeftStateList ttWord key allTauStates := by
  unfold chainFiberFrom lengthTwoFiberExtractLeftStateList lengthTwoFiberExtractLeftState
  rw [ttAllChainStates_lengthTwo_eq]
  rw [bindList_filter]

theorem chainFiberFrom_ttFiber3_eq_extracts :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber3Key =
      lengthTwoFiberExtractLeftStateList ttWord ttFiber3Key allTauStates :=
  chainFiberFrom_tt_lengthTwo_eq_extracts ttFiber3Key

theorem ttFiber3ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber3Key (tauStateChunk32 0) = [] := by
  decide

theorem ttFiber3ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber3Key (tauStateChunk32 32) = [] := by
  decide

theorem ttFiber3ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber3Key (tauStateChunk32 64) = [] := by
  decide

theorem ttFiber3ExtractLeftChunk_96_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber3Key (tauStateChunk32 96) =
      ttFiber3DirectStates := by
  decide

theorem ttFiber3ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber3Key (tauStateChunk32 128) = [] := by
  decide

theorem ttFiber3ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber3Key (tauStateChunk32 160) = [] := by
  decide

theorem ttFiber3ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber3Key tauStateTail192 = [] := by
  decide

theorem ttFiber3ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber3Key allTauStates = ttFiber3DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [ttFiber3ExtractLeftChunk_0_eq_nil,
    ttFiber3ExtractLeftChunk_32_eq_nil,
    ttFiber3ExtractLeftChunk_64_eq_nil,
    ttFiber3ExtractLeftChunk_96_eq_direct,
    ttFiber3ExtractLeftChunk_128_eq_nil,
    ttFiber3ExtractLeftChunk_160_eq_nil,
    ttFiber3ExtractLeftTail_eq_nil]
  simp

theorem ttFiber3RealFiber_eq_direct :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber3Key = ttFiber3DirectStates := by
  rw [chainFiberFrom_ttFiber3_eq_extracts]
  exact ttFiber3ExtractAllLefts_eq_direct

theorem ttFiber3RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber3Key) =
      true := by
  rw [ttFiber3RealFiber_eq_direct]
  exact ttFiber3DirectConnected

theorem chainFiberFrom_ttFiber4_eq_extracts :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber4Key =
      lengthTwoFiberExtractLeftStateList ttWord ttFiber4Key allTauStates :=
  chainFiberFrom_tt_lengthTwo_eq_extracts ttFiber4Key

theorem ttFiber4ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber4Key (tauStateChunk32 0) = [] := by
  decide

theorem ttFiber4ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber4Key (tauStateChunk32 32) = [] := by
  decide

theorem ttFiber4ExtractLeftChunk_64_eq_take :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber4Key (tauStateChunk32 64) =
      ttFiber4DirectStates.take 32 := by
  decide

theorem ttFiber4ExtractLeftChunk_96_eq_drop :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber4Key (tauStateChunk32 96) =
      ttFiber4DirectStates.drop 32 := by
  decide

theorem ttFiber4ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber4Key (tauStateChunk32 128) = [] := by
  decide

theorem ttFiber4ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber4Key (tauStateChunk32 160) = [] := by
  decide

theorem ttFiber4ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber4Key tauStateTail192 = [] := by
  decide

theorem ttFiber4ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber4Key allTauStates = ttFiber4DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [ttFiber4ExtractLeftChunk_0_eq_nil,
    ttFiber4ExtractLeftChunk_32_eq_nil,
    ttFiber4ExtractLeftChunk_64_eq_take,
    ttFiber4ExtractLeftChunk_96_eq_drop,
    ttFiber4ExtractLeftChunk_128_eq_nil,
    ttFiber4ExtractLeftChunk_160_eq_nil,
    ttFiber4ExtractLeftTail_eq_nil]
  simp

theorem ttFiber4RealFiber_eq_direct :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber4Key = ttFiber4DirectStates := by
  rw [chainFiberFrom_ttFiber4_eq_extracts]
  exact ttFiber4ExtractAllLefts_eq_direct

theorem ttFiber4RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber4Key) =
      true := by
  rw [ttFiber4RealFiber_eq_direct]
  exact ttFiber4DirectConnected

theorem chainFiberFrom_ttFiber10_eq_extracts :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber10Key =
      lengthTwoFiberExtractLeftStateList ttWord ttFiber10Key allTauStates :=
  chainFiberFrom_tt_lengthTwo_eq_extracts ttFiber10Key

theorem ttFiber10ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber10Key (tauStateChunk32 0) = [] := by
  decide

theorem ttFiber10ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber10Key (tauStateChunk32 32) = [] := by
  decide

theorem ttFiber10ExtractLeftChunk_64_eq_take :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber10Key (tauStateChunk32 64) =
      ttFiber10DirectStates.take 32 := by
  decide

theorem ttFiber10ExtractLeftChunk_96_eq_drop :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber10Key (tauStateChunk32 96) =
      ttFiber10DirectStates.drop 32 := by
  decide

theorem ttFiber10ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber10Key (tauStateChunk32 128) = [] := by
  decide

theorem ttFiber10ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber10Key (tauStateChunk32 160) = [] := by
  decide

theorem ttFiber10ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber10Key tauStateTail192 = [] := by
  decide

theorem ttFiber10ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber10Key allTauStates = ttFiber10DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [ttFiber10ExtractLeftChunk_0_eq_nil,
    ttFiber10ExtractLeftChunk_32_eq_nil,
    ttFiber10ExtractLeftChunk_64_eq_take,
    ttFiber10ExtractLeftChunk_96_eq_drop,
    ttFiber10ExtractLeftChunk_128_eq_nil,
    ttFiber10ExtractLeftChunk_160_eq_nil,
    ttFiber10ExtractLeftTail_eq_nil]
  simp

theorem ttFiber10RealFiber_eq_direct :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber10Key = ttFiber10DirectStates := by
  rw [chainFiberFrom_ttFiber10_eq_extracts]
  exact ttFiber10ExtractAllLefts_eq_direct

theorem ttFiber10RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber10Key) =
      true := by
  rw [ttFiber10RealFiber_eq_direct]
  exact ttFiber10DirectConnected

theorem chainFiberFrom_ttFiber5_eq_extracts :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber5Key =
      lengthTwoFiberExtractLeftStateList ttWord ttFiber5Key allTauStates :=
  chainFiberFrom_tt_lengthTwo_eq_extracts ttFiber5Key

theorem ttFiber5ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber5Key (tauStateChunk32 0) = [] := by
  decide

theorem ttFiber5ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber5Key (tauStateChunk32 32) = [] := by
  decide

theorem ttFiber5ExtractLeftChunk_64_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber5Key (tauStateChunk32 64) =
      ttFiber5DirectStates := by
  decide

theorem ttFiber5ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber5Key (tauStateChunk32 96) = [] := by
  decide

theorem ttFiber5ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber5Key (tauStateChunk32 128) = [] := by
  decide

theorem ttFiber5ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber5Key (tauStateChunk32 160) = [] := by
  decide

theorem ttFiber5ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber5Key tauStateTail192 = [] := by
  decide

theorem ttFiber5ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber5Key allTauStates = ttFiber5DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [ttFiber5ExtractLeftChunk_0_eq_nil,
    ttFiber5ExtractLeftChunk_32_eq_nil,
    ttFiber5ExtractLeftChunk_64_eq_direct,
    ttFiber5ExtractLeftChunk_96_eq_nil,
    ttFiber5ExtractLeftChunk_128_eq_nil,
    ttFiber5ExtractLeftChunk_160_eq_nil,
    ttFiber5ExtractLeftTail_eq_nil]
  simp

theorem ttFiber5RealFiber_eq_direct :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber5Key = ttFiber5DirectStates := by
  rw [chainFiberFrom_ttFiber5_eq_extracts]
  exact ttFiber5ExtractAllLefts_eq_direct

theorem ttFiber5RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber5Key) =
      true := by
  rw [ttFiber5RealFiber_eq_direct]
  exact ttFiber5DirectConnected

theorem chainFiberFrom_ttFiber6_eq_extracts :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber6Key =
      lengthTwoFiberExtractLeftStateList ttWord ttFiber6Key allTauStates :=
  chainFiberFrom_tt_lengthTwo_eq_extracts ttFiber6Key

theorem ttFiber6ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber6Key (tauStateChunk32 0) = [] := by
  decide

theorem ttFiber6ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber6Key (tauStateChunk32 32) = [] := by
  decide

theorem ttFiber6ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber6Key (tauStateChunk32 64) = [] := by
  decide

theorem ttFiber6ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber6Key (tauStateChunk32 96) = [] := by
  decide

theorem ttFiber6ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber6Key (tauStateChunk32 128) = [] := by
  decide

theorem ttFiber6ExtractLeftChunk_160_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber6Key (tauStateChunk32 160) =
      ttFiber6DirectStates := by
  decide

theorem ttFiber6ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber6Key tauStateTail192 = [] := by
  decide

theorem ttFiber6ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber6Key allTauStates = ttFiber6DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [ttFiber6ExtractLeftChunk_0_eq_nil,
    ttFiber6ExtractLeftChunk_32_eq_nil,
    ttFiber6ExtractLeftChunk_64_eq_nil,
    ttFiber6ExtractLeftChunk_96_eq_nil,
    ttFiber6ExtractLeftChunk_128_eq_nil,
    ttFiber6ExtractLeftChunk_160_eq_direct,
    ttFiber6ExtractLeftTail_eq_nil]
  simp

theorem ttFiber6RealFiber_eq_direct :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber6Key = ttFiber6DirectStates := by
  rw [chainFiberFrom_ttFiber6_eq_extracts]
  exact ttFiber6ExtractAllLefts_eq_direct

theorem ttFiber6RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber6Key) =
      true := by
  rw [ttFiber6RealFiber_eq_direct]
  exact ttFiber6DirectConnected

theorem chainFiberFrom_ttFiber7_eq_extracts :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber7Key =
      lengthTwoFiberExtractLeftStateList ttWord ttFiber7Key allTauStates :=
  chainFiberFrom_tt_lengthTwo_eq_extracts ttFiber7Key

theorem ttFiber7ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber7Key (tauStateChunk32 0) = [] := by
  decide

theorem ttFiber7ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber7Key (tauStateChunk32 32) = [] := by
  decide

theorem ttFiber7ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber7Key (tauStateChunk32 64) = [] := by
  decide

theorem ttFiber7ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber7Key (tauStateChunk32 96) = [] := by
  decide

theorem ttFiber7ExtractLeftChunk_128_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber7Key (tauStateChunk32 128) =
      ttFiber7DirectStates := by
  decide

theorem ttFiber7ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber7Key (tauStateChunk32 160) = [] := by
  decide

theorem ttFiber7ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber7Key tauStateTail192 = [] := by
  decide

theorem ttFiber7ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber7Key allTauStates = ttFiber7DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [ttFiber7ExtractLeftChunk_0_eq_nil,
    ttFiber7ExtractLeftChunk_32_eq_nil,
    ttFiber7ExtractLeftChunk_64_eq_nil,
    ttFiber7ExtractLeftChunk_96_eq_nil,
    ttFiber7ExtractLeftChunk_128_eq_direct,
    ttFiber7ExtractLeftChunk_160_eq_nil,
    ttFiber7ExtractLeftTail_eq_nil]
  simp

theorem ttFiber7RealFiber_eq_direct :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber7Key = ttFiber7DirectStates := by
  rw [chainFiberFrom_ttFiber7_eq_extracts]
  exact ttFiber7ExtractAllLefts_eq_direct

theorem ttFiber7RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber7Key) =
      true := by
  rw [ttFiber7RealFiber_eq_direct]
  exact ttFiber7DirectConnected

theorem chainFiberFrom_ttFiber9_eq_extracts :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber9Key =
      lengthTwoFiberExtractLeftStateList ttWord ttFiber9Key allTauStates :=
  chainFiberFrom_tt_lengthTwo_eq_extracts ttFiber9Key

theorem ttFiber9ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber9Key (tauStateChunk32 0) = [] := by
  decide

theorem ttFiber9ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber9Key (tauStateChunk32 32) = [] := by
  decide

theorem ttFiber9ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber9Key (tauStateChunk32 64) = [] := by
  decide

theorem ttFiber9ExtractLeftChunk_96_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber9Key (tauStateChunk32 96) =
      ttFiber9DirectStates := by
  decide

theorem ttFiber9ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber9Key (tauStateChunk32 128) = [] := by
  decide

theorem ttFiber9ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber9Key (tauStateChunk32 160) = [] := by
  decide

theorem ttFiber9ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber9Key tauStateTail192 = [] := by
  decide

theorem ttFiber9ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber9Key allTauStates = ttFiber9DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [ttFiber9ExtractLeftChunk_0_eq_nil,
    ttFiber9ExtractLeftChunk_32_eq_nil,
    ttFiber9ExtractLeftChunk_64_eq_nil,
    ttFiber9ExtractLeftChunk_96_eq_direct,
    ttFiber9ExtractLeftChunk_128_eq_nil,
    ttFiber9ExtractLeftChunk_160_eq_nil,
    ttFiber9ExtractLeftTail_eq_nil]
  simp

theorem ttFiber9RealFiber_eq_direct :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber9Key = ttFiber9DirectStates := by
  rw [chainFiberFrom_ttFiber9_eq_extracts]
  exact ttFiber9ExtractAllLefts_eq_direct

theorem ttFiber9RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber9Key) =
      true := by
  rw [ttFiber9RealFiber_eq_direct]
  exact ttFiber9DirectConnected

theorem chainFiberFrom_ttFiber11_eq_extracts :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber11Key =
      lengthTwoFiberExtractLeftStateList ttWord ttFiber11Key allTauStates :=
  chainFiberFrom_tt_lengthTwo_eq_extracts ttFiber11Key

theorem ttFiber11ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber11Key (tauStateChunk32 0) = [] := by
  decide

theorem ttFiber11ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber11Key (tauStateChunk32 32) = [] := by
  decide

theorem ttFiber11ExtractLeftChunk_64_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber11Key (tauStateChunk32 64) =
      ttFiber11DirectStates := by
  decide

theorem ttFiber11ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber11Key (tauStateChunk32 96) = [] := by
  decide

theorem ttFiber11ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber11Key (tauStateChunk32 128) = [] := by
  decide

theorem ttFiber11ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber11Key (tauStateChunk32 160) = [] := by
  decide

theorem ttFiber11ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber11Key tauStateTail192 = [] := by
  decide

theorem ttFiber11ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber11Key allTauStates = ttFiber11DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [ttFiber11ExtractLeftChunk_0_eq_nil,
    ttFiber11ExtractLeftChunk_32_eq_nil,
    ttFiber11ExtractLeftChunk_64_eq_direct,
    ttFiber11ExtractLeftChunk_96_eq_nil,
    ttFiber11ExtractLeftChunk_128_eq_nil,
    ttFiber11ExtractLeftChunk_160_eq_nil,
    ttFiber11ExtractLeftTail_eq_nil]
  simp

theorem ttFiber11RealFiber_eq_direct :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber11Key = ttFiber11DirectStates := by
  rw [chainFiberFrom_ttFiber11_eq_extracts]
  exact ttFiber11ExtractAllLefts_eq_direct

theorem ttFiber11RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber11Key) =
      true := by
  rw [ttFiber11RealFiber_eq_direct]
  exact ttFiber11DirectConnected

theorem chainFiberFrom_ttFiber18_eq_extracts :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber18Key =
      lengthTwoFiberExtractLeftStateList ttWord ttFiber18Key allTauStates :=
  chainFiberFrom_tt_lengthTwo_eq_extracts ttFiber18Key

theorem ttFiber18ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber18Key (tauStateChunk32 0) = [] := by
  decide

theorem ttFiber18ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber18Key (tauStateChunk32 32) = [] := by
  decide

theorem ttFiber18ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber18Key (tauStateChunk32 64) = [] := by
  decide

theorem ttFiber18ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber18Key (tauStateChunk32 96) = [] := by
  decide

theorem ttFiber18ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber18Key (tauStateChunk32 128) = [] := by
  decide

theorem ttFiber18ExtractLeftChunk_160_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber18Key (tauStateChunk32 160) =
      ttFiber18DirectStates := by
  decide

theorem ttFiber18ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber18Key tauStateTail192 = [] := by
  decide

theorem ttFiber18ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber18Key allTauStates = ttFiber18DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [ttFiber18ExtractLeftChunk_0_eq_nil,
    ttFiber18ExtractLeftChunk_32_eq_nil,
    ttFiber18ExtractLeftChunk_64_eq_nil,
    ttFiber18ExtractLeftChunk_96_eq_nil,
    ttFiber18ExtractLeftChunk_128_eq_nil,
    ttFiber18ExtractLeftChunk_160_eq_direct,
    ttFiber18ExtractLeftTail_eq_nil]
  simp

theorem ttFiber18RealFiber_eq_direct :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber18Key = ttFiber18DirectStates := by
  rw [chainFiberFrom_ttFiber18_eq_extracts]
  exact ttFiber18ExtractAllLefts_eq_direct

theorem ttFiber18RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber18Key) =
      true := by
  rw [ttFiber18RealFiber_eq_direct]
  exact ttFiber18DirectConnected

theorem chainFiberFrom_ttFiber19_eq_extracts :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber19Key =
      lengthTwoFiberExtractLeftStateList ttWord ttFiber19Key allTauStates :=
  chainFiberFrom_tt_lengthTwo_eq_extracts ttFiber19Key

theorem ttFiber19ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber19Key (tauStateChunk32 0) = [] := by
  decide

theorem ttFiber19ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber19Key (tauStateChunk32 32) = [] := by
  decide

theorem ttFiber19ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber19Key (tauStateChunk32 64) = [] := by
  decide

theorem ttFiber19ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber19Key (tauStateChunk32 96) = [] := by
  decide

theorem ttFiber19ExtractLeftChunk_128_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber19Key (tauStateChunk32 128) =
      ttFiber19DirectStates := by
  decide

theorem ttFiber19ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber19Key (tauStateChunk32 160) = [] := by
  decide

theorem ttFiber19ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber19Key tauStateTail192 = [] := by
  decide

theorem ttFiber19ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber19Key allTauStates = ttFiber19DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [ttFiber19ExtractLeftChunk_0_eq_nil,
    ttFiber19ExtractLeftChunk_32_eq_nil,
    ttFiber19ExtractLeftChunk_64_eq_nil,
    ttFiber19ExtractLeftChunk_96_eq_nil,
    ttFiber19ExtractLeftChunk_128_eq_direct,
    ttFiber19ExtractLeftChunk_160_eq_nil,
    ttFiber19ExtractLeftTail_eq_nil]
  simp

theorem ttFiber19RealFiber_eq_direct :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber19Key = ttFiber19DirectStates := by
  rw [chainFiberFrom_ttFiber19_eq_extracts]
  exact ttFiber19ExtractAllLefts_eq_direct

theorem ttFiber19RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber19Key) =
      true := by
  rw [ttFiber19RealFiber_eq_direct]
  exact ttFiber19DirectConnected

theorem chainFiberFrom_ttFiber31_eq_extracts :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber31Key =
      lengthTwoFiberExtractLeftStateList ttWord ttFiber31Key allTauStates :=
  chainFiberFrom_tt_lengthTwo_eq_extracts ttFiber31Key

theorem ttFiber31ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber31Key (tauStateChunk32 0) = [] := by
  decide

theorem ttFiber31ExtractLeftChunk_32_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber31Key (tauStateChunk32 32) =
      ttFiber31DirectStates := by
  decide

theorem ttFiber31ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber31Key (tauStateChunk32 64) = [] := by
  decide

theorem ttFiber31ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber31Key (tauStateChunk32 96) = [] := by
  decide

theorem ttFiber31ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber31Key (tauStateChunk32 128) = [] := by
  decide

theorem ttFiber31ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber31Key (tauStateChunk32 160) = [] := by
  decide

theorem ttFiber31ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber31Key tauStateTail192 = [] := by
  decide

theorem ttFiber31ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber31Key allTauStates = ttFiber31DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [ttFiber31ExtractLeftChunk_0_eq_nil,
    ttFiber31ExtractLeftChunk_32_eq_direct,
    ttFiber31ExtractLeftChunk_64_eq_nil,
    ttFiber31ExtractLeftChunk_96_eq_nil,
    ttFiber31ExtractLeftChunk_128_eq_nil,
    ttFiber31ExtractLeftChunk_160_eq_nil,
    ttFiber31ExtractLeftTail_eq_nil]
  simp

theorem ttFiber31RealFiber_eq_direct :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber31Key = ttFiber31DirectStates := by
  rw [chainFiberFrom_ttFiber31_eq_extracts]
  exact ttFiber31ExtractAllLefts_eq_direct

theorem ttFiber31RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber31Key) =
      true := by
  rw [ttFiber31RealFiber_eq_direct]
  exact ttFiber31DirectConnected

theorem chainFiberFrom_ttFiber32_eq_extracts :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber32Key =
      lengthTwoFiberExtractLeftStateList ttWord ttFiber32Key allTauStates :=
  chainFiberFrom_tt_lengthTwo_eq_extracts ttFiber32Key

theorem ttFiber32ExtractLeftChunk_0_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber32Key (tauStateChunk32 0) =
      ttFiber32DirectStates := by
  decide

theorem ttFiber32ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber32Key (tauStateChunk32 32) = [] := by
  decide

theorem ttFiber32ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber32Key (tauStateChunk32 64) = [] := by
  decide

theorem ttFiber32ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber32Key (tauStateChunk32 96) = [] := by
  decide

theorem ttFiber32ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber32Key (tauStateChunk32 128) = [] := by
  decide

theorem ttFiber32ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber32Key (tauStateChunk32 160) = [] := by
  decide

theorem ttFiber32ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber32Key tauStateTail192 = [] := by
  decide

theorem ttFiber32ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber32Key allTauStates = ttFiber32DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [ttFiber32ExtractLeftChunk_0_eq_direct,
    ttFiber32ExtractLeftChunk_32_eq_nil,
    ttFiber32ExtractLeftChunk_64_eq_nil,
    ttFiber32ExtractLeftChunk_96_eq_nil,
    ttFiber32ExtractLeftChunk_128_eq_nil,
    ttFiber32ExtractLeftChunk_160_eq_nil,
    ttFiber32ExtractLeftTail_eq_nil]
  simp

theorem ttFiber32RealFiber_eq_direct :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber32Key = ttFiber32DirectStates := by
  rw [chainFiberFrom_ttFiber32_eq_extracts]
  exact ttFiber32ExtractAllLefts_eq_direct

theorem ttFiber32RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber32Key) =
      true := by
  rw [ttFiber32RealFiber_eq_direct]
  exact ttFiber32DirectConnected

theorem chainFiberFrom_ttFiber37_eq_extracts :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber37Key =
      lengthTwoFiberExtractLeftStateList ttWord ttFiber37Key allTauStates :=
  chainFiberFrom_tt_lengthTwo_eq_extracts ttFiber37Key

theorem ttFiber37ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber37Key (tauStateChunk32 0) = [] := by
  decide

theorem ttFiber37ExtractLeftChunk_32_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber37Key (tauStateChunk32 32) =
      ttFiber37DirectStates := by
  decide

theorem ttFiber37ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber37Key (tauStateChunk32 64) = [] := by
  decide

theorem ttFiber37ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber37Key (tauStateChunk32 96) = [] := by
  decide

theorem ttFiber37ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber37Key (tauStateChunk32 128) = [] := by
  decide

theorem ttFiber37ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber37Key (tauStateChunk32 160) = [] := by
  decide

theorem ttFiber37ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber37Key tauStateTail192 = [] := by
  decide

theorem ttFiber37ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber37Key allTauStates = ttFiber37DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [ttFiber37ExtractLeftChunk_0_eq_nil,
    ttFiber37ExtractLeftChunk_32_eq_direct,
    ttFiber37ExtractLeftChunk_64_eq_nil,
    ttFiber37ExtractLeftChunk_96_eq_nil,
    ttFiber37ExtractLeftChunk_128_eq_nil,
    ttFiber37ExtractLeftChunk_160_eq_nil,
    ttFiber37ExtractLeftTail_eq_nil]
  simp

theorem ttFiber37RealFiber_eq_direct :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber37Key = ttFiber37DirectStates := by
  rw [chainFiberFrom_ttFiber37_eq_extracts]
  exact ttFiber37ExtractAllLefts_eq_direct

theorem ttFiber37RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber37Key) =
      true := by
  rw [ttFiber37RealFiber_eq_direct]
  exact ttFiber37DirectConnected

theorem chainFiberFrom_ttFiber38_eq_extracts :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber38Key =
      lengthTwoFiberExtractLeftStateList ttWord ttFiber38Key allTauStates :=
  chainFiberFrom_tt_lengthTwo_eq_extracts ttFiber38Key

theorem ttFiber38ExtractLeftChunk_0_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber38Key (tauStateChunk32 0) =
      ttFiber38DirectStates := by
  decide

theorem ttFiber38ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber38Key (tauStateChunk32 32) = [] := by
  decide

theorem ttFiber38ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber38Key (tauStateChunk32 64) = [] := by
  decide

theorem ttFiber38ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber38Key (tauStateChunk32 96) = [] := by
  decide

theorem ttFiber38ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber38Key (tauStateChunk32 128) = [] := by
  decide

theorem ttFiber38ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber38Key (tauStateChunk32 160) = [] := by
  decide

theorem ttFiber38ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber38Key tauStateTail192 = [] := by
  decide

theorem ttFiber38ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber38Key allTauStates = ttFiber38DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [ttFiber38ExtractLeftChunk_0_eq_direct,
    ttFiber38ExtractLeftChunk_32_eq_nil,
    ttFiber38ExtractLeftChunk_64_eq_nil,
    ttFiber38ExtractLeftChunk_96_eq_nil,
    ttFiber38ExtractLeftChunk_128_eq_nil,
    ttFiber38ExtractLeftChunk_160_eq_nil,
    ttFiber38ExtractLeftTail_eq_nil]
  simp

theorem ttFiber38RealFiber_eq_direct :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber38Key = ttFiber38DirectStates := by
  rw [chainFiberFrom_ttFiber38_eq_extracts]
  exact ttFiber38ExtractAllLefts_eq_direct

theorem ttFiber38RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber38Key) =
      true := by
  rw [ttFiber38RealFiber_eq_direct]
  exact ttFiber38DirectConnected

theorem chainFiberFrom_ttFiber42_eq_extracts :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber42Key =
      lengthTwoFiberExtractLeftStateList ttWord ttFiber42Key allTauStates :=
  chainFiberFrom_tt_lengthTwo_eq_extracts ttFiber42Key

theorem ttFiber42ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber42Key (tauStateChunk32 0) = [] := by
  decide

theorem ttFiber42ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber42Key (tauStateChunk32 32) = [] := by
  decide

theorem ttFiber42ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber42Key (tauStateChunk32 64) = [] := by
  decide

theorem ttFiber42ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber42Key (tauStateChunk32 96) = [] := by
  decide

theorem ttFiber42ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber42Key (tauStateChunk32 128) = [] := by
  decide

theorem ttFiber42ExtractLeftChunk_160_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber42Key (tauStateChunk32 160) =
      ttFiber42DirectStates := by
  decide

theorem ttFiber42ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber42Key tauStateTail192 = [] := by
  decide

theorem ttFiber42ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber42Key allTauStates = ttFiber42DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [ttFiber42ExtractLeftChunk_0_eq_nil,
    ttFiber42ExtractLeftChunk_32_eq_nil,
    ttFiber42ExtractLeftChunk_64_eq_nil,
    ttFiber42ExtractLeftChunk_96_eq_nil,
    ttFiber42ExtractLeftChunk_128_eq_nil,
    ttFiber42ExtractLeftChunk_160_eq_direct,
    ttFiber42ExtractLeftTail_eq_nil]
  simp

theorem ttFiber42RealFiber_eq_direct :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber42Key = ttFiber42DirectStates := by
  rw [chainFiberFrom_ttFiber42_eq_extracts]
  exact ttFiber42ExtractAllLefts_eq_direct

theorem ttFiber42RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber42Key) =
      true := by
  rw [ttFiber42RealFiber_eq_direct]
  exact ttFiber42DirectConnected

theorem chainFiberFrom_ttFiber43_eq_extracts :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber43Key =
      lengthTwoFiberExtractLeftStateList ttWord ttFiber43Key allTauStates :=
  chainFiberFrom_tt_lengthTwo_eq_extracts ttFiber43Key

theorem ttFiber43ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber43Key (tauStateChunk32 0) = [] := by
  decide

theorem ttFiber43ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber43Key (tauStateChunk32 32) = [] := by
  decide

theorem ttFiber43ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber43Key (tauStateChunk32 64) = [] := by
  decide

theorem ttFiber43ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber43Key (tauStateChunk32 96) = [] := by
  decide

theorem ttFiber43ExtractLeftChunk_128_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber43Key (tauStateChunk32 128) =
      ttFiber43DirectStates := by
  decide

theorem ttFiber43ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber43Key (tauStateChunk32 160) = [] := by
  decide

theorem ttFiber43ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber43Key tauStateTail192 = [] := by
  decide

theorem ttFiber43ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber43Key allTauStates = ttFiber43DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [ttFiber43ExtractLeftChunk_0_eq_nil,
    ttFiber43ExtractLeftChunk_32_eq_nil,
    ttFiber43ExtractLeftChunk_64_eq_nil,
    ttFiber43ExtractLeftChunk_96_eq_nil,
    ttFiber43ExtractLeftChunk_128_eq_direct,
    ttFiber43ExtractLeftChunk_160_eq_nil,
    ttFiber43ExtractLeftTail_eq_nil]
  simp

theorem ttFiber43RealFiber_eq_direct :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber43Key = ttFiber43DirectStates := by
  rw [chainFiberFrom_ttFiber43_eq_extracts]
  exact ttFiber43ExtractAllLefts_eq_direct

theorem ttFiber43RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber43Key) =
      true := by
  rw [ttFiber43RealFiber_eq_direct]
  exact ttFiber43DirectConnected

theorem chainFiberFrom_ttFiber48_eq_extracts :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber48Key =
      lengthTwoFiberExtractLeftStateList ttWord ttFiber48Key allTauStates :=
  chainFiberFrom_tt_lengthTwo_eq_extracts ttFiber48Key

theorem ttFiber48ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber48Key (tauStateChunk32 0) = [] := by
  decide

theorem ttFiber48ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber48Key (tauStateChunk32 32) = [] := by
  decide

theorem ttFiber48ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber48Key (tauStateChunk32 64) = [] := by
  decide

theorem ttFiber48ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber48Key (tauStateChunk32 96) = [] := by
  decide

theorem ttFiber48ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber48Key (tauStateChunk32 128) = [] := by
  decide

theorem ttFiber48ExtractLeftChunk_160_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber48Key (tauStateChunk32 160) =
      ttFiber48DirectStates := by
  decide

theorem ttFiber48ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber48Key tauStateTail192 = [] := by
  decide

theorem ttFiber48ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber48Key allTauStates = ttFiber48DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [ttFiber48ExtractLeftChunk_0_eq_nil,
    ttFiber48ExtractLeftChunk_32_eq_nil,
    ttFiber48ExtractLeftChunk_64_eq_nil,
    ttFiber48ExtractLeftChunk_96_eq_nil,
    ttFiber48ExtractLeftChunk_128_eq_nil,
    ttFiber48ExtractLeftChunk_160_eq_direct,
    ttFiber48ExtractLeftTail_eq_nil]
  simp

theorem ttFiber48RealFiber_eq_direct :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber48Key = ttFiber48DirectStates := by
  rw [chainFiberFrom_ttFiber48_eq_extracts]
  exact ttFiber48ExtractAllLefts_eq_direct

theorem ttFiber48RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber48Key) =
      true := by
  rw [ttFiber48RealFiber_eq_direct]
  exact ttFiber48DirectConnected

theorem chainFiberFrom_ttFiber49_eq_extracts :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber49Key =
      lengthTwoFiberExtractLeftStateList ttWord ttFiber49Key allTauStates :=
  chainFiberFrom_tt_lengthTwo_eq_extracts ttFiber49Key

theorem ttFiber49ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber49Key (tauStateChunk32 0) = [] := by
  decide

theorem ttFiber49ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber49Key (tauStateChunk32 32) = [] := by
  decide

theorem ttFiber49ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber49Key (tauStateChunk32 64) = [] := by
  decide

theorem ttFiber49ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber49Key (tauStateChunk32 96) = [] := by
  decide

theorem ttFiber49ExtractLeftChunk_128_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber49Key (tauStateChunk32 128) =
      ttFiber49DirectStates := by
  decide

theorem ttFiber49ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber49Key (tauStateChunk32 160) = [] := by
  decide

theorem ttFiber49ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber49Key tauStateTail192 = [] := by
  decide

theorem ttFiber49ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber49Key allTauStates = ttFiber49DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [ttFiber49ExtractLeftChunk_0_eq_nil,
    ttFiber49ExtractLeftChunk_32_eq_nil,
    ttFiber49ExtractLeftChunk_64_eq_nil,
    ttFiber49ExtractLeftChunk_96_eq_nil,
    ttFiber49ExtractLeftChunk_128_eq_direct,
    ttFiber49ExtractLeftChunk_160_eq_nil,
    ttFiber49ExtractLeftTail_eq_nil]
  simp

theorem ttFiber49RealFiber_eq_direct :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber49Key = ttFiber49DirectStates := by
  rw [chainFiberFrom_ttFiber49_eq_extracts]
  exact ttFiber49ExtractAllLefts_eq_direct

theorem ttFiber49RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber49Key) =
      true := by
  rw [ttFiber49RealFiber_eq_direct]
  exact ttFiber49DirectConnected

theorem chainFiberFrom_ttFiber61_eq_extracts :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber61Key =
      lengthTwoFiberExtractLeftStateList ttWord ttFiber61Key allTauStates :=
  chainFiberFrom_tt_lengthTwo_eq_extracts ttFiber61Key

theorem ttFiber61ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber61Key (tauStateChunk32 0) = [] := by
  decide

theorem ttFiber61ExtractLeftChunk_32_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber61Key (tauStateChunk32 32) =
      ttFiber61DirectStates := by
  decide

theorem ttFiber61ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber61Key (tauStateChunk32 64) = [] := by
  decide

theorem ttFiber61ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber61Key (tauStateChunk32 96) = [] := by
  decide

theorem ttFiber61ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber61Key (tauStateChunk32 128) = [] := by
  decide

theorem ttFiber61ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber61Key (tauStateChunk32 160) = [] := by
  decide

theorem ttFiber61ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber61Key tauStateTail192 = [] := by
  decide

theorem ttFiber61ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber61Key allTauStates = ttFiber61DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [ttFiber61ExtractLeftChunk_0_eq_nil,
    ttFiber61ExtractLeftChunk_32_eq_direct,
    ttFiber61ExtractLeftChunk_64_eq_nil,
    ttFiber61ExtractLeftChunk_96_eq_nil,
    ttFiber61ExtractLeftChunk_128_eq_nil,
    ttFiber61ExtractLeftChunk_160_eq_nil,
    ttFiber61ExtractLeftTail_eq_nil]
  simp

theorem ttFiber61RealFiber_eq_direct :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber61Key = ttFiber61DirectStates := by
  rw [chainFiberFrom_ttFiber61_eq_extracts]
  exact ttFiber61ExtractAllLefts_eq_direct

theorem ttFiber61RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber61Key) =
      true := by
  rw [ttFiber61RealFiber_eq_direct]
  exact ttFiber61DirectConnected

theorem chainFiberFrom_ttFiber62_eq_extracts :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber62Key =
      lengthTwoFiberExtractLeftStateList ttWord ttFiber62Key allTauStates :=
  chainFiberFrom_tt_lengthTwo_eq_extracts ttFiber62Key

theorem ttFiber62ExtractLeftChunk_0_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber62Key (tauStateChunk32 0) =
      ttFiber62DirectStates := by
  decide

theorem ttFiber62ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber62Key (tauStateChunk32 32) = [] := by
  decide

theorem ttFiber62ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber62Key (tauStateChunk32 64) = [] := by
  decide

theorem ttFiber62ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber62Key (tauStateChunk32 96) = [] := by
  decide

theorem ttFiber62ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber62Key (tauStateChunk32 128) = [] := by
  decide

theorem ttFiber62ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber62Key (tauStateChunk32 160) = [] := by
  decide

theorem ttFiber62ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber62Key tauStateTail192 = [] := by
  decide

theorem ttFiber62ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber62Key allTauStates = ttFiber62DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [ttFiber62ExtractLeftChunk_0_eq_direct,
    ttFiber62ExtractLeftChunk_32_eq_nil,
    ttFiber62ExtractLeftChunk_64_eq_nil,
    ttFiber62ExtractLeftChunk_96_eq_nil,
    ttFiber62ExtractLeftChunk_128_eq_nil,
    ttFiber62ExtractLeftChunk_160_eq_nil,
    ttFiber62ExtractLeftTail_eq_nil]
  simp

theorem ttFiber62RealFiber_eq_direct :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber62Key = ttFiber62DirectStates := by
  rw [chainFiberFrom_ttFiber62_eq_extracts]
  exact ttFiber62ExtractAllLefts_eq_direct

theorem ttFiber62RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber62Key) =
      true := by
  rw [ttFiber62RealFiber_eq_direct]
  exact ttFiber62DirectConnected

theorem chainFiberFrom_ttFiber73_eq_extracts :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber73Key =
      lengthTwoFiberExtractLeftStateList ttWord ttFiber73Key allTauStates :=
  chainFiberFrom_tt_lengthTwo_eq_extracts ttFiber73Key

theorem ttFiber73ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber73Key (tauStateChunk32 0) = [] := by
  decide

theorem ttFiber73ExtractLeftChunk_32_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber73Key (tauStateChunk32 32) =
      ttFiber73DirectStates := by
  decide

theorem ttFiber73ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber73Key (tauStateChunk32 64) = [] := by
  decide

theorem ttFiber73ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber73Key (tauStateChunk32 96) = [] := by
  decide

theorem ttFiber73ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber73Key (tauStateChunk32 128) = [] := by
  decide

theorem ttFiber73ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber73Key (tauStateChunk32 160) = [] := by
  decide

theorem ttFiber73ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber73Key tauStateTail192 = [] := by
  decide

theorem ttFiber73ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber73Key allTauStates = ttFiber73DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [ttFiber73ExtractLeftChunk_0_eq_nil,
    ttFiber73ExtractLeftChunk_32_eq_direct,
    ttFiber73ExtractLeftChunk_64_eq_nil,
    ttFiber73ExtractLeftChunk_96_eq_nil,
    ttFiber73ExtractLeftChunk_128_eq_nil,
    ttFiber73ExtractLeftChunk_160_eq_nil,
    ttFiber73ExtractLeftTail_eq_nil]
  simp

theorem ttFiber73RealFiber_eq_direct :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber73Key = ttFiber73DirectStates := by
  rw [chainFiberFrom_ttFiber73_eq_extracts]
  exact ttFiber73ExtractAllLefts_eq_direct

theorem ttFiber73RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber73Key) =
      true := by
  rw [ttFiber73RealFiber_eq_direct]
  exact ttFiber73DirectConnected

theorem chainFiberFrom_ttFiber74_eq_extracts :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber74Key =
      lengthTwoFiberExtractLeftStateList ttWord ttFiber74Key allTauStates :=
  chainFiberFrom_tt_lengthTwo_eq_extracts ttFiber74Key

theorem ttFiber74ExtractLeftChunk_0_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber74Key (tauStateChunk32 0) =
      ttFiber74DirectStates := by
  decide

theorem ttFiber74ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber74Key (tauStateChunk32 32) = [] := by
  decide

theorem ttFiber74ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber74Key (tauStateChunk32 64) = [] := by
  decide

theorem ttFiber74ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber74Key (tauStateChunk32 96) = [] := by
  decide

theorem ttFiber74ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber74Key (tauStateChunk32 128) = [] := by
  decide

theorem ttFiber74ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber74Key (tauStateChunk32 160) = [] := by
  decide

theorem ttFiber74ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber74Key tauStateTail192 = [] := by
  decide

theorem ttFiber74ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber74Key allTauStates = ttFiber74DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [ttFiber74ExtractLeftChunk_0_eq_direct,
    ttFiber74ExtractLeftChunk_32_eq_nil,
    ttFiber74ExtractLeftChunk_64_eq_nil,
    ttFiber74ExtractLeftChunk_96_eq_nil,
    ttFiber74ExtractLeftChunk_128_eq_nil,
    ttFiber74ExtractLeftChunk_160_eq_nil,
    ttFiber74ExtractLeftTail_eq_nil]
  simp

theorem ttFiber74RealFiber_eq_direct :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber74Key = ttFiber74DirectStates := by
  rw [chainFiberFrom_ttFiber74_eq_extracts]
  exact ttFiber74ExtractAllLefts_eq_direct

theorem ttFiber74RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber74Key) =
      true := by
  rw [ttFiber74RealFiber_eq_direct]
  exact ttFiber74DirectConnected

theorem chainFiberFrom_ttFiber69_eq_extracts :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber69Key =
      lengthTwoFiberExtractLeftStateList ttWord ttFiber69Key allTauStates :=
  chainFiberFrom_tt_lengthTwo_eq_extracts ttFiber69Key

theorem ttFiber69ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber69Key (tauStateChunk32 0) = [] := by
  decide

theorem ttFiber69ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber69Key (tauStateChunk32 32) = [] := by
  decide

theorem ttFiber69ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber69Key (tauStateChunk32 64) = [] := by
  decide

theorem ttFiber69ExtractLeftChunk_96_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber69Key (tauStateChunk32 96) =
      ttFiber69DirectStates := by
  decide

theorem ttFiber69ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber69Key (tauStateChunk32 128) = [] := by
  decide

theorem ttFiber69ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber69Key (tauStateChunk32 160) = [] := by
  decide

theorem ttFiber69ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber69Key tauStateTail192 = [] := by
  decide

theorem ttFiber69ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber69Key allTauStates = ttFiber69DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [ttFiber69ExtractLeftChunk_0_eq_nil,
    ttFiber69ExtractLeftChunk_32_eq_nil,
    ttFiber69ExtractLeftChunk_64_eq_nil,
    ttFiber69ExtractLeftChunk_96_eq_direct,
    ttFiber69ExtractLeftChunk_128_eq_nil,
    ttFiber69ExtractLeftChunk_160_eq_nil,
    ttFiber69ExtractLeftTail_eq_nil]
  simp

theorem ttFiber69RealFiber_eq_direct :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber69Key = ttFiber69DirectStates := by
  rw [chainFiberFrom_ttFiber69_eq_extracts]
  exact ttFiber69ExtractAllLefts_eq_direct

theorem ttFiber69RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber69Key) =
      true := by
  rw [ttFiber69RealFiber_eq_direct]
  exact ttFiber69DirectConnected

theorem chainFiberFrom_ttFiber71_eq_extracts :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber71Key =
      lengthTwoFiberExtractLeftStateList ttWord ttFiber71Key allTauStates :=
  chainFiberFrom_tt_lengthTwo_eq_extracts ttFiber71Key

theorem ttFiber71ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber71Key (tauStateChunk32 0) = [] := by
  decide

theorem ttFiber71ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber71Key (tauStateChunk32 32) = [] := by
  decide

theorem ttFiber71ExtractLeftChunk_64_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber71Key (tauStateChunk32 64) =
      ttFiber71DirectStates := by
  decide

theorem ttFiber71ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber71Key (tauStateChunk32 96) = [] := by
  decide

theorem ttFiber71ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber71Key (tauStateChunk32 128) = [] := by
  decide

theorem ttFiber71ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber71Key (tauStateChunk32 160) = [] := by
  decide

theorem ttFiber71ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber71Key tauStateTail192 = [] := by
  decide

theorem ttFiber71ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber71Key allTauStates = ttFiber71DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [ttFiber71ExtractLeftChunk_0_eq_nil,
    ttFiber71ExtractLeftChunk_32_eq_nil,
    ttFiber71ExtractLeftChunk_64_eq_direct,
    ttFiber71ExtractLeftChunk_96_eq_nil,
    ttFiber71ExtractLeftChunk_128_eq_nil,
    ttFiber71ExtractLeftChunk_160_eq_nil,
    ttFiber71ExtractLeftTail_eq_nil]
  simp

theorem ttFiber71RealFiber_eq_direct :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber71Key = ttFiber71DirectStates := by
  rw [chainFiberFrom_ttFiber71_eq_extracts]
  exact ttFiber71ExtractAllLefts_eq_direct

theorem ttFiber71RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber71Key) =
      true := by
  rw [ttFiber71RealFiber_eq_direct]
  exact ttFiber71DirectConnected

theorem chainFiberFrom_ttFiber75_eq_extracts :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber75Key =
      lengthTwoFiberExtractLeftStateList ttWord ttFiber75Key allTauStates :=
  chainFiberFrom_tt_lengthTwo_eq_extracts ttFiber75Key

theorem ttFiber75ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber75Key (tauStateChunk32 0) = [] := by
  decide

theorem ttFiber75ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber75Key (tauStateChunk32 32) = [] := by
  decide

theorem ttFiber75ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber75Key (tauStateChunk32 64) = [] := by
  decide

theorem ttFiber75ExtractLeftChunk_96_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber75Key (tauStateChunk32 96) =
      ttFiber75DirectStates := by
  decide

theorem ttFiber75ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber75Key (tauStateChunk32 128) = [] := by
  decide

theorem ttFiber75ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber75Key (tauStateChunk32 160) = [] := by
  decide

theorem ttFiber75ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber75Key tauStateTail192 = [] := by
  decide

theorem ttFiber75ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber75Key allTauStates = ttFiber75DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [ttFiber75ExtractLeftChunk_0_eq_nil,
    ttFiber75ExtractLeftChunk_32_eq_nil,
    ttFiber75ExtractLeftChunk_64_eq_nil,
    ttFiber75ExtractLeftChunk_96_eq_direct,
    ttFiber75ExtractLeftChunk_128_eq_nil,
    ttFiber75ExtractLeftChunk_160_eq_nil,
    ttFiber75ExtractLeftTail_eq_nil]
  simp

theorem ttFiber75RealFiber_eq_direct :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber75Key = ttFiber75DirectStates := by
  rw [chainFiberFrom_ttFiber75_eq_extracts]
  exact ttFiber75ExtractAllLefts_eq_direct

theorem ttFiber75RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber75Key) =
      true := by
  rw [ttFiber75RealFiber_eq_direct]
  exact ttFiber75DirectConnected

theorem chainFiberFrom_ttFiber77_eq_extracts :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber77Key =
      lengthTwoFiberExtractLeftStateList ttWord ttFiber77Key allTauStates :=
  chainFiberFrom_tt_lengthTwo_eq_extracts ttFiber77Key

theorem ttFiber77ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber77Key (tauStateChunk32 0) = [] := by
  decide

theorem ttFiber77ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber77Key (tauStateChunk32 32) = [] := by
  decide

theorem ttFiber77ExtractLeftChunk_64_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber77Key (tauStateChunk32 64) =
      ttFiber77DirectStates := by
  decide

theorem ttFiber77ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber77Key (tauStateChunk32 96) = [] := by
  decide

theorem ttFiber77ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber77Key (tauStateChunk32 128) = [] := by
  decide

theorem ttFiber77ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber77Key (tauStateChunk32 160) = [] := by
  decide

theorem ttFiber77ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber77Key tauStateTail192 = [] := by
  decide

theorem ttFiber77ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber77Key allTauStates = ttFiber77DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [ttFiber77ExtractLeftChunk_0_eq_nil,
    ttFiber77ExtractLeftChunk_32_eq_nil,
    ttFiber77ExtractLeftChunk_64_eq_direct,
    ttFiber77ExtractLeftChunk_96_eq_nil,
    ttFiber77ExtractLeftChunk_128_eq_nil,
    ttFiber77ExtractLeftChunk_160_eq_nil,
    ttFiber77ExtractLeftTail_eq_nil]
  simp

theorem ttFiber77RealFiber_eq_direct :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber77Key = ttFiber77DirectStates := by
  rw [chainFiberFrom_ttFiber77_eq_extracts]
  exact ttFiber77ExtractAllLefts_eq_direct

theorem ttFiber77RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber77Key) =
      true := by
  rw [ttFiber77RealFiber_eq_direct]
  exact ttFiber77DirectConnected

theorem chainFiberFrom_ttFiber70_eq_extracts :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber70Key =
      lengthTwoFiberExtractLeftStateList ttWord ttFiber70Key allTauStates :=
  chainFiberFrom_tt_lengthTwo_eq_extracts ttFiber70Key

theorem ttFiber70ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber70Key (tauStateChunk32 0) = [] := by
  decide

theorem ttFiber70ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber70Key (tauStateChunk32 32) = [] := by
  decide

theorem ttFiber70ExtractLeftChunk_64_eq_take :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber70Key (tauStateChunk32 64) =
      ttFiber70DirectStates.take 32 := by
  decide

theorem ttFiber70ExtractLeftChunk_96_eq_drop :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber70Key (tauStateChunk32 96) =
      ttFiber70DirectStates.drop 32 := by
  decide

theorem ttFiber70ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber70Key (tauStateChunk32 128) = [] := by
  decide

theorem ttFiber70ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber70Key (tauStateChunk32 160) = [] := by
  decide

theorem ttFiber70ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber70Key tauStateTail192 = [] := by
  decide

theorem ttFiber70ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber70Key allTauStates = ttFiber70DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [ttFiber70ExtractLeftChunk_0_eq_nil,
    ttFiber70ExtractLeftChunk_32_eq_nil,
    ttFiber70ExtractLeftChunk_64_eq_take,
    ttFiber70ExtractLeftChunk_96_eq_drop,
    ttFiber70ExtractLeftChunk_128_eq_nil,
    ttFiber70ExtractLeftChunk_160_eq_nil,
    ttFiber70ExtractLeftTail_eq_nil]
  simp

theorem ttFiber70RealFiber_eq_direct :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber70Key = ttFiber70DirectStates := by
  rw [chainFiberFrom_ttFiber70_eq_extracts]
  exact ttFiber70ExtractAllLefts_eq_direct

theorem ttFiber70RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber70Key) =
      true := by
  rw [ttFiber70RealFiber_eq_direct]
  exact ttFiber70DirectConnected

theorem chainFiberFrom_ttFiber76_eq_extracts :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber76Key =
      lengthTwoFiberExtractLeftStateList ttWord ttFiber76Key allTauStates :=
  chainFiberFrom_tt_lengthTwo_eq_extracts ttFiber76Key

theorem ttFiber76ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber76Key (tauStateChunk32 0) = [] := by
  decide

theorem ttFiber76ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber76Key (tauStateChunk32 32) = [] := by
  decide

theorem ttFiber76ExtractLeftChunk_64_eq_take :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber76Key (tauStateChunk32 64) =
      ttFiber76DirectStates.take 32 := by
  decide

theorem ttFiber76ExtractLeftChunk_96_eq_drop :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber76Key (tauStateChunk32 96) =
      ttFiber76DirectStates.drop 32 := by
  decide

theorem ttFiber76ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber76Key (tauStateChunk32 128) = [] := by
  decide

theorem ttFiber76ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber76Key (tauStateChunk32 160) = [] := by
  decide

theorem ttFiber76ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber76Key tauStateTail192 = [] := by
  decide

theorem ttFiber76ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber76Key allTauStates = ttFiber76DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [ttFiber76ExtractLeftChunk_0_eq_nil,
    ttFiber76ExtractLeftChunk_32_eq_nil,
    ttFiber76ExtractLeftChunk_64_eq_take,
    ttFiber76ExtractLeftChunk_96_eq_drop,
    ttFiber76ExtractLeftChunk_128_eq_nil,
    ttFiber76ExtractLeftChunk_160_eq_nil,
    ttFiber76ExtractLeftTail_eq_nil]
  simp

theorem ttFiber76RealFiber_eq_direct :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber76Key = ttFiber76DirectStates := by
  rw [chainFiberFrom_ttFiber76_eq_extracts]
  exact ttFiber76ExtractAllLefts_eq_direct

theorem ttFiber76RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber76Key) =
      true := by
  rw [ttFiber76RealFiber_eq_direct]
  exact ttFiber76DirectConnected

theorem chainFiberFrom_ttFiber8_eq_extracts :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber8Key =
      lengthTwoFiberExtractLeftStateList ttWord ttFiber8Key allTauStates :=
  chainFiberFrom_tt_lengthTwo_eq_extracts ttFiber8Key

theorem ttFiber8ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber8Key (tauStateChunk32 0) = [] := by
  decide

theorem ttFiber8ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber8Key (tauStateChunk32 32) = [] := by
  decide

theorem ttFiber8ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber8Key (tauStateChunk32 64) = [] := by
  decide

theorem ttFiber8ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber8Key (tauStateChunk32 96) = [] := by
  decide

theorem ttFiber8ExtractLeftChunk_128_eq_take :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber8Key (tauStateChunk32 128) =
      ttFiber8DirectStates.take 32 := by
  decide

theorem ttFiber8ExtractLeftChunk_160_eq_drop :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber8Key (tauStateChunk32 160) =
      ttFiber8DirectStates.drop 32 := by
  decide

theorem ttFiber8ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber8Key tauStateTail192 = [] := by
  decide

theorem ttFiber8ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber8Key allTauStates = ttFiber8DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [ttFiber8ExtractLeftChunk_0_eq_nil,
    ttFiber8ExtractLeftChunk_32_eq_nil,
    ttFiber8ExtractLeftChunk_64_eq_nil,
    ttFiber8ExtractLeftChunk_96_eq_nil,
    ttFiber8ExtractLeftChunk_128_eq_take,
    ttFiber8ExtractLeftChunk_160_eq_drop,
    ttFiber8ExtractLeftTail_eq_nil]
  simp

theorem ttFiber8RealFiber_eq_direct :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber8Key = ttFiber8DirectStates := by
  rw [chainFiberFrom_ttFiber8_eq_extracts]
  exact ttFiber8ExtractAllLefts_eq_direct

theorem ttFiber8RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber8Key) =
      true := by
  rw [ttFiber8RealFiber_eq_direct]
  exact ttFiber8DirectConnected

theorem chainFiberFrom_ttFiber20_eq_extracts :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber20Key =
      lengthTwoFiberExtractLeftStateList ttWord ttFiber20Key allTauStates :=
  chainFiberFrom_tt_lengthTwo_eq_extracts ttFiber20Key

theorem ttFiber20ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber20Key (tauStateChunk32 0) = [] := by
  decide

theorem ttFiber20ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber20Key (tauStateChunk32 32) = [] := by
  decide

theorem ttFiber20ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber20Key (tauStateChunk32 64) = [] := by
  decide

theorem ttFiber20ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber20Key (tauStateChunk32 96) = [] := by
  decide

theorem ttFiber20ExtractLeftChunk_128_eq_take :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber20Key (tauStateChunk32 128) =
      ttFiber20DirectStates.take 32 := by
  decide

theorem ttFiber20ExtractLeftChunk_160_eq_drop :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber20Key (tauStateChunk32 160) =
      ttFiber20DirectStates.drop 32 := by
  decide

theorem ttFiber20ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber20Key tauStateTail192 = [] := by
  decide

theorem ttFiber20ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber20Key allTauStates = ttFiber20DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [ttFiber20ExtractLeftChunk_0_eq_nil,
    ttFiber20ExtractLeftChunk_32_eq_nil,
    ttFiber20ExtractLeftChunk_64_eq_nil,
    ttFiber20ExtractLeftChunk_96_eq_nil,
    ttFiber20ExtractLeftChunk_128_eq_take,
    ttFiber20ExtractLeftChunk_160_eq_drop,
    ttFiber20ExtractLeftTail_eq_nil]
  simp

theorem ttFiber20RealFiber_eq_direct :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber20Key = ttFiber20DirectStates := by
  rw [chainFiberFrom_ttFiber20_eq_extracts]
  exact ttFiber20ExtractAllLefts_eq_direct

theorem ttFiber20RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber20Key) =
      true := by
  rw [ttFiber20RealFiber_eq_direct]
  exact ttFiber20DirectConnected

theorem chainFiberFrom_ttFiber44_eq_extracts :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber44Key =
      lengthTwoFiberExtractLeftStateList ttWord ttFiber44Key allTauStates :=
  chainFiberFrom_tt_lengthTwo_eq_extracts ttFiber44Key

theorem ttFiber44ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber44Key (tauStateChunk32 0) = [] := by
  decide

theorem ttFiber44ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber44Key (tauStateChunk32 32) = [] := by
  decide

theorem ttFiber44ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber44Key (tauStateChunk32 64) = [] := by
  decide

theorem ttFiber44ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber44Key (tauStateChunk32 96) = [] := by
  decide

theorem ttFiber44ExtractLeftChunk_128_eq_take :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber44Key (tauStateChunk32 128) =
      ttFiber44DirectStates.take 32 := by
  decide

theorem ttFiber44ExtractLeftChunk_160_eq_drop :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber44Key (tauStateChunk32 160) =
      ttFiber44DirectStates.drop 32 := by
  decide

theorem ttFiber44ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber44Key tauStateTail192 = [] := by
  decide

theorem ttFiber44ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber44Key allTauStates = ttFiber44DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [ttFiber44ExtractLeftChunk_0_eq_nil,
    ttFiber44ExtractLeftChunk_32_eq_nil,
    ttFiber44ExtractLeftChunk_64_eq_nil,
    ttFiber44ExtractLeftChunk_96_eq_nil,
    ttFiber44ExtractLeftChunk_128_eq_take,
    ttFiber44ExtractLeftChunk_160_eq_drop,
    ttFiber44ExtractLeftTail_eq_nil]
  simp

theorem ttFiber44RealFiber_eq_direct :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber44Key = ttFiber44DirectStates := by
  rw [chainFiberFrom_ttFiber44_eq_extracts]
  exact ttFiber44ExtractAllLefts_eq_direct

theorem ttFiber44RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber44Key) =
      true := by
  rw [ttFiber44RealFiber_eq_direct]
  exact ttFiber44DirectConnected

theorem chainFiberFrom_ttFiber50_eq_extracts :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber50Key =
      lengthTwoFiberExtractLeftStateList ttWord ttFiber50Key allTauStates :=
  chainFiberFrom_tt_lengthTwo_eq_extracts ttFiber50Key

theorem ttFiber50ExtractLeftChunk_0_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber50Key (tauStateChunk32 0) = [] := by
  decide

theorem ttFiber50ExtractLeftChunk_32_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber50Key (tauStateChunk32 32) = [] := by
  decide

theorem ttFiber50ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber50Key (tauStateChunk32 64) = [] := by
  decide

theorem ttFiber50ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber50Key (tauStateChunk32 96) = [] := by
  decide

theorem ttFiber50ExtractLeftChunk_128_eq_take :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber50Key (tauStateChunk32 128) =
      ttFiber50DirectStates.take 32 := by
  decide

theorem ttFiber50ExtractLeftChunk_160_eq_drop :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber50Key (tauStateChunk32 160) =
      ttFiber50DirectStates.drop 32 := by
  decide

theorem ttFiber50ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber50Key tauStateTail192 = [] := by
  decide

theorem ttFiber50ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber50Key allTauStates = ttFiber50DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [ttFiber50ExtractLeftChunk_0_eq_nil,
    ttFiber50ExtractLeftChunk_32_eq_nil,
    ttFiber50ExtractLeftChunk_64_eq_nil,
    ttFiber50ExtractLeftChunk_96_eq_nil,
    ttFiber50ExtractLeftChunk_128_eq_take,
    ttFiber50ExtractLeftChunk_160_eq_drop,
    ttFiber50ExtractLeftTail_eq_nil]
  simp

theorem ttFiber50RealFiber_eq_direct :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber50Key = ttFiber50DirectStates := by
  rw [chainFiberFrom_ttFiber50_eq_extracts]
  exact ttFiber50ExtractAllLefts_eq_direct

theorem ttFiber50RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber50Key) =
      true := by
  rw [ttFiber50RealFiber_eq_direct]
  exact ttFiber50DirectConnected

theorem chainFiberFrom_ttFiber30_eq_extracts :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber30Key =
      lengthTwoFiberExtractLeftStateList ttWord ttFiber30Key allTauStates :=
  chainFiberFrom_tt_lengthTwo_eq_extracts ttFiber30Key

theorem ttFiber30ExtractLeftChunk_0_eq_take :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber30Key (tauStateChunk32 0) =
      ttFiber30DirectStates.take 32 := by
  decide

theorem ttFiber30ExtractLeftChunk_32_eq_drop :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber30Key (tauStateChunk32 32) =
      ttFiber30DirectStates.drop 32 := by
  decide

theorem ttFiber30ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber30Key (tauStateChunk32 64) = [] := by
  decide

theorem ttFiber30ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber30Key (tauStateChunk32 96) = [] := by
  decide

theorem ttFiber30ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber30Key (tauStateChunk32 128) = [] := by
  decide

theorem ttFiber30ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber30Key (tauStateChunk32 160) = [] := by
  decide

theorem ttFiber30ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber30Key tauStateTail192 = [] := by
  decide

theorem ttFiber30ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber30Key allTauStates = ttFiber30DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [ttFiber30ExtractLeftChunk_0_eq_take,
    ttFiber30ExtractLeftChunk_32_eq_drop,
    ttFiber30ExtractLeftChunk_64_eq_nil,
    ttFiber30ExtractLeftChunk_96_eq_nil,
    ttFiber30ExtractLeftChunk_128_eq_nil,
    ttFiber30ExtractLeftChunk_160_eq_nil,
    ttFiber30ExtractLeftTail_eq_nil]
  simp

theorem ttFiber30RealFiber_eq_direct :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber30Key = ttFiber30DirectStates := by
  rw [chainFiberFrom_ttFiber30_eq_extracts]
  exact ttFiber30ExtractAllLefts_eq_direct

theorem ttFiber30RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber30Key) =
      true := by
  rw [ttFiber30RealFiber_eq_direct]
  exact ttFiber30DirectConnected

theorem chainFiberFrom_ttFiber36_eq_extracts :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber36Key =
      lengthTwoFiberExtractLeftStateList ttWord ttFiber36Key allTauStates :=
  chainFiberFrom_tt_lengthTwo_eq_extracts ttFiber36Key

theorem ttFiber36ExtractLeftChunk_0_eq_take :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber36Key (tauStateChunk32 0) =
      ttFiber36DirectStates.take 32 := by
  decide

theorem ttFiber36ExtractLeftChunk_32_eq_drop :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber36Key (tauStateChunk32 32) =
      ttFiber36DirectStates.drop 32 := by
  decide

theorem ttFiber36ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber36Key (tauStateChunk32 64) = [] := by
  decide

theorem ttFiber36ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber36Key (tauStateChunk32 96) = [] := by
  decide

theorem ttFiber36ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber36Key (tauStateChunk32 128) = [] := by
  decide

theorem ttFiber36ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber36Key (tauStateChunk32 160) = [] := by
  decide

theorem ttFiber36ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber36Key tauStateTail192 = [] := by
  decide

theorem ttFiber36ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber36Key allTauStates = ttFiber36DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [ttFiber36ExtractLeftChunk_0_eq_take,
    ttFiber36ExtractLeftChunk_32_eq_drop,
    ttFiber36ExtractLeftChunk_64_eq_nil,
    ttFiber36ExtractLeftChunk_96_eq_nil,
    ttFiber36ExtractLeftChunk_128_eq_nil,
    ttFiber36ExtractLeftChunk_160_eq_nil,
    ttFiber36ExtractLeftTail_eq_nil]
  simp

theorem ttFiber36RealFiber_eq_direct :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber36Key = ttFiber36DirectStates := by
  rw [chainFiberFrom_ttFiber36_eq_extracts]
  exact ttFiber36ExtractAllLefts_eq_direct

theorem ttFiber36RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber36Key) =
      true := by
  rw [ttFiber36RealFiber_eq_direct]
  exact ttFiber36DirectConnected

theorem chainFiberFrom_ttFiber60_eq_extracts :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber60Key =
      lengthTwoFiberExtractLeftStateList ttWord ttFiber60Key allTauStates :=
  chainFiberFrom_tt_lengthTwo_eq_extracts ttFiber60Key

theorem ttFiber60ExtractLeftChunk_0_eq_take :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber60Key (tauStateChunk32 0) =
      ttFiber60DirectStates.take 32 := by
  decide

theorem ttFiber60ExtractLeftChunk_32_eq_drop :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber60Key (tauStateChunk32 32) =
      ttFiber60DirectStates.drop 32 := by
  decide

theorem ttFiber60ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber60Key (tauStateChunk32 64) = [] := by
  decide

theorem ttFiber60ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber60Key (tauStateChunk32 96) = [] := by
  decide

theorem ttFiber60ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber60Key (tauStateChunk32 128) = [] := by
  decide

theorem ttFiber60ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber60Key (tauStateChunk32 160) = [] := by
  decide

theorem ttFiber60ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber60Key tauStateTail192 = [] := by
  decide

theorem ttFiber60ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber60Key allTauStates = ttFiber60DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [ttFiber60ExtractLeftChunk_0_eq_take,
    ttFiber60ExtractLeftChunk_32_eq_drop,
    ttFiber60ExtractLeftChunk_64_eq_nil,
    ttFiber60ExtractLeftChunk_96_eq_nil,
    ttFiber60ExtractLeftChunk_128_eq_nil,
    ttFiber60ExtractLeftChunk_160_eq_nil,
    ttFiber60ExtractLeftTail_eq_nil]
  simp

theorem ttFiber60RealFiber_eq_direct :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber60Key = ttFiber60DirectStates := by
  rw [chainFiberFrom_ttFiber60_eq_extracts]
  exact ttFiber60ExtractAllLefts_eq_direct

theorem ttFiber60RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber60Key) =
      true := by
  rw [ttFiber60RealFiber_eq_direct]
  exact ttFiber60DirectConnected

theorem chainFiberFrom_ttFiber72_eq_extracts :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber72Key =
      lengthTwoFiberExtractLeftStateList ttWord ttFiber72Key allTauStates :=
  chainFiberFrom_tt_lengthTwo_eq_extracts ttFiber72Key

theorem ttFiber72ExtractLeftChunk_0_eq_take :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber72Key (tauStateChunk32 0) =
      ttFiber72DirectStates.take 32 := by
  decide

theorem ttFiber72ExtractLeftChunk_32_eq_drop :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber72Key (tauStateChunk32 32) =
      ttFiber72DirectStates.drop 32 := by
  decide

theorem ttFiber72ExtractLeftChunk_64_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber72Key (tauStateChunk32 64) = [] := by
  decide

theorem ttFiber72ExtractLeftChunk_96_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber72Key (tauStateChunk32 96) = [] := by
  decide

theorem ttFiber72ExtractLeftChunk_128_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber72Key (tauStateChunk32 128) = [] := by
  decide

theorem ttFiber72ExtractLeftChunk_160_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber72Key (tauStateChunk32 160) = [] := by
  decide

theorem ttFiber72ExtractLeftTail_eq_nil :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber72Key tauStateTail192 = [] := by
  decide

theorem ttFiber72ExtractAllLefts_eq_direct :
    lengthTwoFiberExtractLeftStateList ttWord ttFiber72Key allTauStates = ttFiber72DirectStates := by
  rw [allTauStates_eq_chunks32]
  repeat rw [lengthTwoFiberExtractLeftStateList_append]
  rw [ttFiber72ExtractLeftChunk_0_eq_take,
    ttFiber72ExtractLeftChunk_32_eq_drop,
    ttFiber72ExtractLeftChunk_64_eq_nil,
    ttFiber72ExtractLeftChunk_96_eq_nil,
    ttFiber72ExtractLeftChunk_128_eq_nil,
    ttFiber72ExtractLeftChunk_160_eq_nil,
    ttFiber72ExtractLeftTail_eq_nil]
  simp

theorem ttFiber72RealFiber_eq_direct :
    chainFiberFrom ttWord (allChainStates ttWord) ttFiber72Key = ttFiber72DirectStates := by
  rw [chainFiberFrom_ttFiber72_eq_extracts]
  exact ttFiber72ExtractAllLefts_eq_direct

theorem ttFiber72RealFiberConnected :
    chainFiberConnected ttWord (chainFiberFrom ttWord (allChainStates ttWord) ttFiber72Key) =
      true := by
  rw [ttFiber72RealFiber_eq_direct]
  exact ttFiber72DirectConnected

end GoertzelLemma818LengthTwoRealFiberBridgePrototype

end Mettapedia.GraphTheory.FourColor
