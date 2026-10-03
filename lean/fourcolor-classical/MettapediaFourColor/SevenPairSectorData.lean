import MettapediaFourColor.RuleTraversalData

/-! A facial sector of two adjacent seven-valent centres.
The first centre has cyclic neighbour degrees 7,5,6,6,5,6,6.
The fixed continuation gives the second centre degrees 7,5,6,5,6,6,6.
Only three additional outer degrees are bounded. All source-rule paths and
maps below are checked against these actual shared facial observations.
Rule data and attribution are retained in NearLinearRuleData. -/

namespace FourColor.SevenPairSectorData

open NearLinearRuleData RuleTraversal

set_option maxRecDepth 65536
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option maxHeartbeats 0

abbrev Point := Fin 24
abbrev State := Point × Point

def numbers (s : String) : List Nat :=
  (NearLinearDiamondData.rows s).headD []

def faceBytes : ByteArray := "ABCCBIACDDCJADEEDKAEFFELAFGGFMAGHHGNAHBBHOBOPBPQBQICIJDJRDRKEKSESLFLMGMTGTNHNUHUOQPVPOWPWXPXV".toUTF8
def face (i : Fin 31) : Point × Point × Point :=
  let xs := faceBytes.data
  (⟨((xs.getD (3*i.val) 0).toNat - 65) % 24, Nat.mod_lt _ (by decide)⟩,
   ⟨((xs.getD (3*i.val+1) 0).toNat - 65) % 24, Nat.mod_lt _ (by decide)⟩,
   ⟨((xs.getD (3*i.val+2) 0).toNat - 65) % 24, Nat.mod_lt _ (by decide)⟩)

def tipBytes : ByteArray := "ADEFGHICAAAAAAAAAAAAAAAAIABAAAAPDAAAAAQRJAAAAAAACJABAAAAKEAAAAAAAAAAAAAADAKABAAAASFAAAAAALAAAAAAEAALABAAAATGAAAAAAMAAAAAFAAAMABAAAANHAAAAAAAAAAAGAAAANABAAAAUIAAAAAOAAAAHBAAAAOAAAAAAVCAAAAAPAAAARCAAAAAADAAAAAAAAAAAAAAAAJDAAAAAAAAAAAAAEAAAAAAAAASEAAAAAAAAAAAAAFAAAAAAAAATFAAAAAAGAAAAAAAAAAAAAAAAMGAAAAAAAAAAAAHAAAAAAAAAAUHAAAAAAAAAAAAIAAAAIAAAAAVAAAAAAACAAAAAAQAAPAAAAAAAAAAAAXACAAAARYWAQAAAAAACAAAAAAWAAAAAAAAAAAKAAAAAAEAAAAAAAAAAAAAAAAALAAAAAAFAAAAAAAAAAAAAAAAAANAAAAAAHAAAAAAAAAAAAAAAAAOAAAAAAIAAAAAAAAAAAAAAAAAAAAAAAAYQAAAAAAAAAAAAAAAAAAAAAAPAAAAAAAQAAAAAAAAAAAAAAAXAAAAAQAA".toUTF8
def witnessBytes : ByteArray := "AACEGIKMAAAAAAAAAAAAAAAAMAAAAAANBAAAAAOPQAAAAAAAABACAAAARDAAAAAAAAAAAAAACADAEAAAASFAAAAAATAAAAAAEAAFAGAAAAUHAAAAAAVAAAAAGAAAHAIAAAAWJAAAAAAAAAAAIAAAAJAKAAAAXLAAAAAYAAAAKMAAAALAAAAAAZNAAAAA[AAAAQBAAAAAARAAAAAAAAAAAAAAAARDAAAAAAAAAAAAASAAAAAAAAATFAAAAAAAAAAAAAUAAAAAAAAAVHAAAAAAWAAAAAAAAAAAAAAAAWJAAAAAAAAAAAAXAAAAAAAAAAYLAAAAAAAAAAAAZAAAANAAAAA[AAAAAAAOAAAAAA]AAOAAAAAAAAAAAA]APAAAA\\^_APAAAAAAQAAAAAA\\AAAAAAAAAAASAAAAAATAAAAAAAAAAAAAAAAAUAAAAAAVAAAAAAAAAAAAAAAAAAXAAAAAAYAAAAAAAAAAAAAAAAAZAAAAAA[AAAAAAAAAAAAAAAAAAAAAAAA_\\AAAAAAAAAAAAAAAAAAAAAA]AAAAAAA^AAAAAAAAAAAAAAA^AAAAA_AA".toUTF8
def tipCode (a b : Point) := (tipBytes.data.getD (24*a.val+b.val) 0).toNat - 65
def tip (a b : Point) : Point := ⟨(tipCode a b - 1)%24,Nat.mod_lt _ (by decide)⟩
def witness (a b : Point) : Fin 31 :=
  ⟨((witnessBytes.data.getD (24*a.val+b.val) 0).toNat - 65)%31,Nat.mod_lt _ (by decide)⟩
def Turn (a b c : Point) : Prop := tipCode a b = c.val + 1
instance (a b c : Point) : Decidable (Turn a b c) := by unfold Turn; infer_instance

theorem witness_sound : ∀ a b : Point, tipCode a b ≠ 0 →
    face (witness a b) = (a,b,tip a b) ∨
    face (witness a b) = (b,tip a b,a) ∨
    face (witness a b) = (tip a b,a,b) := by decide +kernel

theorem turn_faces {a b c : Point} (h : Turn a b c) : ∃ i,
    face i = (a,b,c) ∨ face i = (b,c,a) ∨ face i = (c,a,b) := by
  have hc : tipCode a b = c.val + 1 := h
  have eq : tip a b = c := by
    apply Fin.ext
    simp only [tip,hc,Nat.add_sub_cancel,Nat.mod_eq_of_lt c.isLt]
  have hh := witness_sound a b (by omega)
  rw [eq] at hh
  exact ⟨witness a b,hh⟩

def Edge (a b : Point) : Prop := tipCode a b ≠ 0 ∨ tipCode b a ≠ 0
instance (a b : Point) : Decidable (Edge a b) := by unfold Edge; infer_instance

def Step (op : Move) (p q : State) : Prop :=
  match op with
  | .flip => q.1 = p.2 ∧ q.2 = p.1
  | .next => q.1 = p.1 ∧ Turn p.1 p.2 q.2
  | .previous => q.1 = p.1 ∧ Turn p.1 q.2 p.2
instance (op : Move) (p q : State) : Decidable (Step op p q) := by
  cases op <;> unfold Step <;> infer_instance

def Valid {r : Fin 84} (p : State) : Trace r → List State → Prop
  | [], [] => True
  | (op,_) :: ts, q :: qs => Edge q.1 q.2 ∧ Step op p q ∧ Valid q ts qs
  | _, _ => False
instance {r : Fin 84} (p : State) (ts : Trace r) (qs : List State) :
    Decidable (Valid p ts qs) := by
  induction ts generalizing p qs with
  | nil => cases qs <;> unfold Valid <;> infer_instance
  | cons h t ih =>
      cases qs with
      | nil => unfold Valid; infer_instance
      | cons q qs => letI := ih q qs; unfold Valid; infer_instance

def finish (p : State) : List State → State
  | [] => p
  | q :: qs => finish q qs

def degreeBytes : ByteArray := "HHFGGFGGGGGGHFGGFGGFG".toUTF8
def degree (i : Point) : Nat := (degreeBytes.data.getD i.val 0).toNat - 65

def blockedWords (r : Fin 84) : String :=
  match r.val with
  | 0 => "0 1 0"
  | 1 => "0 1 0"
  | 2 => "0 1 0"
  | 3 => "0 1 0"
  | 4 => "0 1 0"
  | 5 => "0 1 0"
  | 6 => "0 1 0"
  | 7 => "0 1 0"
  | 8 => "0 1 0"
  | 9 => "0 1 0"
  | 10 => "0 1 0"
  | 11 => "0 1 0"
  | 12 => "0 1 0"
  | 13 => "3 8 1 1 2 1 8 8 1"
  | 14 => "3 14 1 1 7 1 14 14 1"
  | 15 => "0 1 0"
  | 16 => "4 15 1 1 7 1 14 1 15 15 1"
  | 17 => "2 7 1 1 7 7 1"
  | 18 => "5 20 7 1 7 7 1 7 14 7 20 20 7"
  | 19 => "2 2 1 1 2 2 1"
  | 20 => "2 7 1 1 7 7 1"
  | 21 => "1 0 1 0 1"
  | 22 => "1 0 1 0 1"
  | 23 => "1 0 1 0 1"
  | 24 => "1 0 1 0 1"
  | 25 => "2 2 1 1 2 2 1"
  | 26 => "4 15 1 1 7 1 14 1 15 15 1"
  | 27 => "5 9 2 1 2 2 1 2 8 2 9 9 2"
  | 28 => "2 7 1 1 7 7 1"
  | 29 => "2 2 1 1 2 2 1"
  | 30 => "3 14 1 1 7 1 14 14 1"
  | 31 => "4 8 1 1 2 1 8 8 1"
  | 32 => "2 2 1 1 2 2 1"
  | 33 => "1 0 1 0 1"
  | 34 => "1 0 1 0 1"
  | 35 => "2 2 1 1 2 2 1"
  | 36 => "3 14 1 1 7 1 14 14 1"
  | 37 => "2 2 1 1 2 2 1"
  | 38 => "6 8 1 1 7 1 14 1 15 1 16 1 8 8 1"
  | 39 => "2 2 1 1 2 2 1"
  | 40 => "5 14 1 1 7 1 14 14 1"
  | 41 => "2 2 1 1 2 2 1"
  | 42 => "3 14 1 1 7 1 14 14 1"
  | 43 => "3 8 1 1 2 1 8 8 1"
  | 44 => "2 7 1 1 7 7 1"
  | 45 => "4 16 1 1 2 1 8 1 16 16 1"
  | 46 => "2 7 1 1 7 7 1"
  | 47 => "2 2 1 1 2 2 1"
  | 48 => "3 6 0 0 1 0 7 0 6 6 0"
  | 49 => "5 15 1 1 2 1 8 1 16 1 15 15 1"
  | 50 => "2 7 1 1 7 7 1"
  | 51 => "2 2 1 1 2 2 1"
  | 52 => "2 7 1 1 7 7 1"
  | 53 => "1 0 1 0 1"
  | 54 => "1 0 1 0 1"
  | 55 => "2 2 1 1 2 2 1"
  | 56 => "3 6 0 0 1 0 7 0 6 6 0"
  | 57 => "1 0 1 0 1"
  | 58 => "1 0 1 0 1"
  | 59 => "2 2 1 1 2 2 1"
  | 60 => "2 7 1 1 7 7 1"
  | 61 => "3 8 1 1 2 1 8 8 1"
  | 62 => "2 7 1 1 7 7 1"
  | 63 => "2 2 1 1 2 2 1"
  | 64 => "2 7 1 1 7 7 1"
  | 65 => "2 2 1 1 2 2 1"
  | 66 => "2 7 1 1 7 7 1"
  | 67 => "2 2 1 1 2 2 1"
  | 68 => "2 7 1 1 7 7 1"
  | 69 => "2 2 1 1 2 2 1"
  | 70 => "4 15 1 1 7 1 14 1 15 15 1"
  | 71 => "2 2 1 1 2 2 1"
  | 72 => "2 2 1 1 2 2 1"
  | 73 => "3 7 1 1 7 7 1"
  | 74 => "2 7 1 1 7 7 1"
  | 75 => "2 2 1 1 2 2 1"
  | 76 => "3 14 1 1 7 1 14 14 1"
  | 77 => "0 1 0"
  | 78 => "0 1 0"
  | 79 => "0 1 0"
  | 80 => "0 1 0"
  | 81 => "0 1 0"
  | 82 => "0 1 0"
  | 83 => "0 1 0"
  | _ => ""

local instance (r : Fin 84) : NeZero (size r) :=
  ⟨by have := (headers r).1; omega⟩

def blockedVertex (r : Fin 84) : Vertex r :=
  ⟨(numbers (blockedWords r)).getD 0 0 % size r,
    Nat.mod_lt _ (NeZero.pos _)⟩
def blockedEnd (r : Fin 84) : State :=
  let xs := numbers (blockedWords r)
  (⟨xs.getD 1 0 % 24, Nat.mod_lt _ (by decide)⟩,
   ⟨xs.getD 2 0 % 24, Nat.mod_lt _ (by decide)⟩)
def pairs : List Nat → List State
  | a :: b :: xs => (⟨a%24,Nat.mod_lt _ (by decide)⟩,
    ⟨b%24,Nat.mod_lt _ (by decide)⟩) :: pairs xs
  | _ => []
def blockedPath (r : Fin 84) := pairs ((numbers (blockedWords r)).drop 3)

theorem blocked_valid : ∀ r : Fin 84, r ≠ 15 →
    Valid (1,0) (RuleTraversalData.trace r (blockedVertex r)) (blockedPath r) ∧
    finish (1,0) (blockedPath r) = blockedEnd r ∧
    (blockedEnd r).1.val < 21 ∧
    ¬ (lower r (blockedVertex r) ≤ degree (blockedEnd r).1 ∧
      (upper r (blockedVertex r) = 0 ∨
       degree (blockedEnd r).1 ≤ upper r (blockedVertex r))) := by
  intro r
  fin_cases r <;> decide +kernel

def RuleMap (r : Fin 84) (m : Vertex r → Point) : Prop :=
  (∀ i j, (graph r).Adj i j → Edge (m i) (m j)) ∧
  (∀ i j k, NearLinearRuleData.Turn r i j k → Turn (m i) (m j) (m k))
instance (r : Fin 84) (m : Vertex r → Point) : Decidable (RuleMap r m) := by
  unfold RuleMap; infer_instance

def map0 : Vertex 15 → Point := ![0,1,7,6,5]
theorem map0_valid : RuleMap 15 map0 := by
  decide +kernel

def map1 : Vertex 17 → Point := ![0,1,2,7,6,13]
theorem map1_valid : RuleMap 17 map1 := by
  decide +kernel

def map2 : Vertex 46 → Point := ![0,1,2,3,4,5]
theorem map2_valid : RuleMap 46 map2 := by
  decide +kernel

def map3 : Vertex 0 → Point := ![2,1]
theorem map3_valid : RuleMap 0 map3 := by
  decide +kernel

def map4 : Vertex 1 → Point := ![8,1,16]
theorem map4_valid : RuleMap 1 map4 := by
  decide +kernel

def map5 : Vertex 2 → Point := ![8,1,2]
theorem map5_valid : RuleMap 2 map5 := by
  decide +kernel

def map6 : Vertex 0 → Point := ![16,1]
theorem map6_valid : RuleMap 0 map6 := by
  decide +kernel

def map7 : Vertex 2 → Point := ![15,1,16]
theorem map7_valid : RuleMap 2 map7 := by
  decide +kernel

def map8 : Vertex 6 → Point := ![14,1,7,20,13]
theorem map8_valid : RuleMap 6 map8 := by
  decide +kernel

def map9 : Vertex 3 → Point := ![14,1,15,22]
theorem map9_valid : RuleMap 3 map9 := by
  decide +kernel

def map10 : Vertex 11 → Point := ![14,1,15,22,23,21,16]
theorem map10_valid : RuleMap 11 map10 := by
  decide +kernel

end FourColor.SevenPairSectorData
