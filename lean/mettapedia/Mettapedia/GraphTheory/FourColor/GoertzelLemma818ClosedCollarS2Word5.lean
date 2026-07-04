import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Base
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Cert3
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Cert4
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Cert5
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Cert6
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Cert7
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Cert8
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Cert9
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Cert10
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Cert11
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Cert18
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Cert19
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Cert20
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Cert30
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Cert31
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Cert32
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Cert36
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Cert37
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Cert38
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Cert42
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Cert43
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Cert44
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Cert48
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Cert49
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Cert50
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Cert60
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Cert61
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Cert62
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Cert69
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Cert70
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Cert71
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Cert72
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Cert73
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Cert74
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Cert75
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Cert76
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5Cert77

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word5

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def keyedLast0 : List TauState :=
  []

theorem keyedLast0_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.r, LColor.r, LColor.r, LColor.r]) =
      keyedLast0 := by
  decide

theorem cert0_keyed_empty :
    closedCollarFiber3Keyed word [LColor.r, LColor.r, LColor.r, LColor.r] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.r, LColor.r, LColor.r, LColor.r] keyedLast0_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast0 = [] := by
    simpa [keyedLast0] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert0_empty :
    closedCollarFiber word [LColor.r, LColor.r, LColor.r, LColor.r] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.r, LColor.r, LColor.r, LColor.r]
  exact hfast.trans cert0_keyed_empty

theorem cert0_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.r, LColor.r, LColor.r] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert0_empty

def keyedLast1 : List TauState :=
  []

theorem keyedLast1_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.r, LColor.r, LColor.r, LColor.b]) =
      keyedLast1 := by
  decide

theorem cert1_keyed_empty :
    closedCollarFiber3Keyed word [LColor.r, LColor.r, LColor.r, LColor.b] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.r, LColor.r, LColor.r, LColor.b] keyedLast1_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast1 = [] := by
    simpa [keyedLast1] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert1_empty :
    closedCollarFiber word [LColor.r, LColor.r, LColor.r, LColor.b] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.r, LColor.r, LColor.r, LColor.b]
  exact hfast.trans cert1_keyed_empty

theorem cert1_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.r, LColor.r, LColor.b] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert1_empty

def keyedLast2 : List TauState :=
  []

theorem keyedLast2_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.r, LColor.r, LColor.r, LColor.p]) =
      keyedLast2 := by
  decide

theorem cert2_keyed_empty :
    closedCollarFiber3Keyed word [LColor.r, LColor.r, LColor.r, LColor.p] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.r, LColor.r, LColor.r, LColor.p] keyedLast2_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast2 = [] := by
    simpa [keyedLast2] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert2_empty :
    closedCollarFiber word [LColor.r, LColor.r, LColor.r, LColor.p] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.r, LColor.r, LColor.r, LColor.p]
  exact hfast.trans cert2_keyed_empty

theorem cert2_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.r, LColor.r, LColor.p] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert2_empty

def keyedLast12 : List TauState :=
  []

theorem keyedLast12_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.r, LColor.b, LColor.b, LColor.r]) =
      keyedLast12 := by
  decide

theorem cert12_keyed_empty :
    closedCollarFiber3Keyed word [LColor.r, LColor.b, LColor.b, LColor.r] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.r, LColor.b, LColor.b, LColor.r] keyedLast12_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast12 = [] := by
    simpa [keyedLast12] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert12_empty :
    closedCollarFiber word [LColor.r, LColor.b, LColor.b, LColor.r] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.r, LColor.b, LColor.b, LColor.r]
  exact hfast.trans cert12_keyed_empty

theorem cert12_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.b, LColor.b, LColor.r] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert12_empty

def keyedLast13 : List TauState :=
  []

theorem keyedLast13_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.r, LColor.b, LColor.b, LColor.b]) =
      keyedLast13 := by
  decide

theorem cert13_keyed_empty :
    closedCollarFiber3Keyed word [LColor.r, LColor.b, LColor.b, LColor.b] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.r, LColor.b, LColor.b, LColor.b] keyedLast13_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast13 = [] := by
    simpa [keyedLast13] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert13_empty :
    closedCollarFiber word [LColor.r, LColor.b, LColor.b, LColor.b] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.r, LColor.b, LColor.b, LColor.b]
  exact hfast.trans cert13_keyed_empty

theorem cert13_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.b, LColor.b, LColor.b] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert13_empty

def keyedLast14 : List TauState :=
  []

theorem keyedLast14_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.r, LColor.b, LColor.b, LColor.p]) =
      keyedLast14 := by
  decide

theorem cert14_keyed_empty :
    closedCollarFiber3Keyed word [LColor.r, LColor.b, LColor.b, LColor.p] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.r, LColor.b, LColor.b, LColor.p] keyedLast14_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast14 = [] := by
    simpa [keyedLast14] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert14_empty :
    closedCollarFiber word [LColor.r, LColor.b, LColor.b, LColor.p] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.r, LColor.b, LColor.b, LColor.p]
  exact hfast.trans cert14_keyed_empty

theorem cert14_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.b, LColor.b, LColor.p] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert14_empty

def keyedLast15 : List TauState :=
  []

theorem keyedLast15_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.r, LColor.b, LColor.p, LColor.r]) =
      keyedLast15 := by
  decide

theorem cert15_keyed_empty :
    closedCollarFiber3Keyed word [LColor.r, LColor.b, LColor.p, LColor.r] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.r, LColor.b, LColor.p, LColor.r] keyedLast15_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast15 = [] := by
    simpa [keyedLast15] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert15_empty :
    closedCollarFiber word [LColor.r, LColor.b, LColor.p, LColor.r] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.r, LColor.b, LColor.p, LColor.r]
  exact hfast.trans cert15_keyed_empty

theorem cert15_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.b, LColor.p, LColor.r] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert15_empty

def keyedLast16 : List TauState :=
  []

theorem keyedLast16_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.r, LColor.b, LColor.p, LColor.b]) =
      keyedLast16 := by
  decide

theorem cert16_keyed_empty :
    closedCollarFiber3Keyed word [LColor.r, LColor.b, LColor.p, LColor.b] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.r, LColor.b, LColor.p, LColor.b] keyedLast16_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast16 = [] := by
    simpa [keyedLast16] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert16_empty :
    closedCollarFiber word [LColor.r, LColor.b, LColor.p, LColor.b] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.r, LColor.b, LColor.p, LColor.b]
  exact hfast.trans cert16_keyed_empty

theorem cert16_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.b, LColor.p, LColor.b] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert16_empty

def keyedLast17 : List TauState :=
  []

theorem keyedLast17_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.r, LColor.b, LColor.p, LColor.p]) =
      keyedLast17 := by
  decide

theorem cert17_keyed_empty :
    closedCollarFiber3Keyed word [LColor.r, LColor.b, LColor.p, LColor.p] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.r, LColor.b, LColor.p, LColor.p] keyedLast17_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast17 = [] := by
    simpa [keyedLast17] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert17_empty :
    closedCollarFiber word [LColor.r, LColor.b, LColor.p, LColor.p] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.r, LColor.b, LColor.p, LColor.p]
  exact hfast.trans cert17_keyed_empty

theorem cert17_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.b, LColor.p, LColor.p] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert17_empty

def keyedLast21 : List TauState :=
  []

theorem keyedLast21_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.r, LColor.p, LColor.b, LColor.r]) =
      keyedLast21 := by
  decide

theorem cert21_keyed_empty :
    closedCollarFiber3Keyed word [LColor.r, LColor.p, LColor.b, LColor.r] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.r, LColor.p, LColor.b, LColor.r] keyedLast21_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast21 = [] := by
    simpa [keyedLast21] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert21_empty :
    closedCollarFiber word [LColor.r, LColor.p, LColor.b, LColor.r] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.r, LColor.p, LColor.b, LColor.r]
  exact hfast.trans cert21_keyed_empty

theorem cert21_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.p, LColor.b, LColor.r] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert21_empty

def keyedLast22 : List TauState :=
  []

theorem keyedLast22_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.r, LColor.p, LColor.b, LColor.b]) =
      keyedLast22 := by
  decide

theorem cert22_keyed_empty :
    closedCollarFiber3Keyed word [LColor.r, LColor.p, LColor.b, LColor.b] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.r, LColor.p, LColor.b, LColor.b] keyedLast22_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast22 = [] := by
    simpa [keyedLast22] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert22_empty :
    closedCollarFiber word [LColor.r, LColor.p, LColor.b, LColor.b] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.r, LColor.p, LColor.b, LColor.b]
  exact hfast.trans cert22_keyed_empty

theorem cert22_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.p, LColor.b, LColor.b] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert22_empty

def keyedLast23 : List TauState :=
  []

theorem keyedLast23_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.r, LColor.p, LColor.b, LColor.p]) =
      keyedLast23 := by
  decide

theorem cert23_keyed_empty :
    closedCollarFiber3Keyed word [LColor.r, LColor.p, LColor.b, LColor.p] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.r, LColor.p, LColor.b, LColor.p] keyedLast23_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast23 = [] := by
    simpa [keyedLast23] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert23_empty :
    closedCollarFiber word [LColor.r, LColor.p, LColor.b, LColor.p] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.r, LColor.p, LColor.b, LColor.p]
  exact hfast.trans cert23_keyed_empty

theorem cert23_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.p, LColor.b, LColor.p] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert23_empty

def keyedLast24 : List TauState :=
  []

theorem keyedLast24_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.r, LColor.p, LColor.p, LColor.r]) =
      keyedLast24 := by
  decide

theorem cert24_keyed_empty :
    closedCollarFiber3Keyed word [LColor.r, LColor.p, LColor.p, LColor.r] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.r, LColor.p, LColor.p, LColor.r] keyedLast24_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast24 = [] := by
    simpa [keyedLast24] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert24_empty :
    closedCollarFiber word [LColor.r, LColor.p, LColor.p, LColor.r] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.r, LColor.p, LColor.p, LColor.r]
  exact hfast.trans cert24_keyed_empty

theorem cert24_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.p, LColor.p, LColor.r] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert24_empty

def keyedLast25 : List TauState :=
  []

theorem keyedLast25_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.r, LColor.p, LColor.p, LColor.b]) =
      keyedLast25 := by
  decide

theorem cert25_keyed_empty :
    closedCollarFiber3Keyed word [LColor.r, LColor.p, LColor.p, LColor.b] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.r, LColor.p, LColor.p, LColor.b] keyedLast25_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast25 = [] := by
    simpa [keyedLast25] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert25_empty :
    closedCollarFiber word [LColor.r, LColor.p, LColor.p, LColor.b] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.r, LColor.p, LColor.p, LColor.b]
  exact hfast.trans cert25_keyed_empty

theorem cert25_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.p, LColor.p, LColor.b] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert25_empty

def keyedLast26 : List TauState :=
  []

theorem keyedLast26_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.r, LColor.p, LColor.p, LColor.p]) =
      keyedLast26 := by
  decide

theorem cert26_keyed_empty :
    closedCollarFiber3Keyed word [LColor.r, LColor.p, LColor.p, LColor.p] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.r, LColor.p, LColor.p, LColor.p] keyedLast26_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast26 = [] := by
    simpa [keyedLast26] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert26_empty :
    closedCollarFiber word [LColor.r, LColor.p, LColor.p, LColor.p] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.r, LColor.p, LColor.p, LColor.p]
  exact hfast.trans cert26_keyed_empty

theorem cert26_connected :
    closedCollarFiberKempeConnected word [LColor.r, LColor.p, LColor.p, LColor.p] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert26_empty

def keyedLast27 : List TauState :=
  []

theorem keyedLast27_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.b, LColor.r, LColor.r, LColor.r]) =
      keyedLast27 := by
  decide

theorem cert27_keyed_empty :
    closedCollarFiber3Keyed word [LColor.b, LColor.r, LColor.r, LColor.r] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.b, LColor.r, LColor.r, LColor.r] keyedLast27_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast27 = [] := by
    simpa [keyedLast27] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert27_empty :
    closedCollarFiber word [LColor.b, LColor.r, LColor.r, LColor.r] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.b, LColor.r, LColor.r, LColor.r]
  exact hfast.trans cert27_keyed_empty

theorem cert27_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.r, LColor.r, LColor.r] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert27_empty

def keyedLast28 : List TauState :=
  []

theorem keyedLast28_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.b, LColor.r, LColor.r, LColor.b]) =
      keyedLast28 := by
  decide

theorem cert28_keyed_empty :
    closedCollarFiber3Keyed word [LColor.b, LColor.r, LColor.r, LColor.b] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.b, LColor.r, LColor.r, LColor.b] keyedLast28_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast28 = [] := by
    simpa [keyedLast28] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert28_empty :
    closedCollarFiber word [LColor.b, LColor.r, LColor.r, LColor.b] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.b, LColor.r, LColor.r, LColor.b]
  exact hfast.trans cert28_keyed_empty

theorem cert28_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.r, LColor.r, LColor.b] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert28_empty

def keyedLast29 : List TauState :=
  []

theorem keyedLast29_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.b, LColor.r, LColor.r, LColor.p]) =
      keyedLast29 := by
  decide

theorem cert29_keyed_empty :
    closedCollarFiber3Keyed word [LColor.b, LColor.r, LColor.r, LColor.p] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.b, LColor.r, LColor.r, LColor.p] keyedLast29_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast29 = [] := by
    simpa [keyedLast29] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert29_empty :
    closedCollarFiber word [LColor.b, LColor.r, LColor.r, LColor.p] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.b, LColor.r, LColor.r, LColor.p]
  exact hfast.trans cert29_keyed_empty

theorem cert29_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.r, LColor.r, LColor.p] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert29_empty

def keyedLast33 : List TauState :=
  []

theorem keyedLast33_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.b, LColor.r, LColor.p, LColor.r]) =
      keyedLast33 := by
  decide

theorem cert33_keyed_empty :
    closedCollarFiber3Keyed word [LColor.b, LColor.r, LColor.p, LColor.r] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.b, LColor.r, LColor.p, LColor.r] keyedLast33_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast33 = [] := by
    simpa [keyedLast33] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert33_empty :
    closedCollarFiber word [LColor.b, LColor.r, LColor.p, LColor.r] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.b, LColor.r, LColor.p, LColor.r]
  exact hfast.trans cert33_keyed_empty

theorem cert33_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.r, LColor.p, LColor.r] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert33_empty

def keyedLast34 : List TauState :=
  []

theorem keyedLast34_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.b, LColor.r, LColor.p, LColor.b]) =
      keyedLast34 := by
  decide

theorem cert34_keyed_empty :
    closedCollarFiber3Keyed word [LColor.b, LColor.r, LColor.p, LColor.b] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.b, LColor.r, LColor.p, LColor.b] keyedLast34_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast34 = [] := by
    simpa [keyedLast34] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert34_empty :
    closedCollarFiber word [LColor.b, LColor.r, LColor.p, LColor.b] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.b, LColor.r, LColor.p, LColor.b]
  exact hfast.trans cert34_keyed_empty

theorem cert34_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.r, LColor.p, LColor.b] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert34_empty

def keyedLast35 : List TauState :=
  []

theorem keyedLast35_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.b, LColor.r, LColor.p, LColor.p]) =
      keyedLast35 := by
  decide

theorem cert35_keyed_empty :
    closedCollarFiber3Keyed word [LColor.b, LColor.r, LColor.p, LColor.p] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.b, LColor.r, LColor.p, LColor.p] keyedLast35_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast35 = [] := by
    simpa [keyedLast35] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert35_empty :
    closedCollarFiber word [LColor.b, LColor.r, LColor.p, LColor.p] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.b, LColor.r, LColor.p, LColor.p]
  exact hfast.trans cert35_keyed_empty

theorem cert35_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.r, LColor.p, LColor.p] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert35_empty

def keyedLast39 : List TauState :=
  []

theorem keyedLast39_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.b, LColor.b, LColor.b, LColor.r]) =
      keyedLast39 := by
  decide

theorem cert39_keyed_empty :
    closedCollarFiber3Keyed word [LColor.b, LColor.b, LColor.b, LColor.r] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.b, LColor.b, LColor.b, LColor.r] keyedLast39_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast39 = [] := by
    simpa [keyedLast39] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert39_empty :
    closedCollarFiber word [LColor.b, LColor.b, LColor.b, LColor.r] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.b, LColor.b, LColor.b, LColor.r]
  exact hfast.trans cert39_keyed_empty

theorem cert39_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.b, LColor.b, LColor.r] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert39_empty

def keyedLast40 : List TauState :=
  []

theorem keyedLast40_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.b, LColor.b, LColor.b, LColor.b]) =
      keyedLast40 := by
  decide

theorem cert40_keyed_empty :
    closedCollarFiber3Keyed word [LColor.b, LColor.b, LColor.b, LColor.b] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.b, LColor.b, LColor.b, LColor.b] keyedLast40_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast40 = [] := by
    simpa [keyedLast40] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert40_empty :
    closedCollarFiber word [LColor.b, LColor.b, LColor.b, LColor.b] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.b, LColor.b, LColor.b, LColor.b]
  exact hfast.trans cert40_keyed_empty

theorem cert40_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.b, LColor.b, LColor.b] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert40_empty

def keyedLast41 : List TauState :=
  []

theorem keyedLast41_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.b, LColor.b, LColor.b, LColor.p]) =
      keyedLast41 := by
  decide

theorem cert41_keyed_empty :
    closedCollarFiber3Keyed word [LColor.b, LColor.b, LColor.b, LColor.p] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.b, LColor.b, LColor.b, LColor.p] keyedLast41_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast41 = [] := by
    simpa [keyedLast41] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert41_empty :
    closedCollarFiber word [LColor.b, LColor.b, LColor.b, LColor.p] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.b, LColor.b, LColor.b, LColor.p]
  exact hfast.trans cert41_keyed_empty

theorem cert41_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.b, LColor.b, LColor.p] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert41_empty

def keyedLast45 : List TauState :=
  []

theorem keyedLast45_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.b, LColor.p, LColor.r, LColor.r]) =
      keyedLast45 := by
  decide

theorem cert45_keyed_empty :
    closedCollarFiber3Keyed word [LColor.b, LColor.p, LColor.r, LColor.r] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.b, LColor.p, LColor.r, LColor.r] keyedLast45_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast45 = [] := by
    simpa [keyedLast45] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert45_empty :
    closedCollarFiber word [LColor.b, LColor.p, LColor.r, LColor.r] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.b, LColor.p, LColor.r, LColor.r]
  exact hfast.trans cert45_keyed_empty

theorem cert45_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.p, LColor.r, LColor.r] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert45_empty

def keyedLast46 : List TauState :=
  []

theorem keyedLast46_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.b, LColor.p, LColor.r, LColor.b]) =
      keyedLast46 := by
  decide

theorem cert46_keyed_empty :
    closedCollarFiber3Keyed word [LColor.b, LColor.p, LColor.r, LColor.b] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.b, LColor.p, LColor.r, LColor.b] keyedLast46_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast46 = [] := by
    simpa [keyedLast46] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert46_empty :
    closedCollarFiber word [LColor.b, LColor.p, LColor.r, LColor.b] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.b, LColor.p, LColor.r, LColor.b]
  exact hfast.trans cert46_keyed_empty

theorem cert46_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.p, LColor.r, LColor.b] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert46_empty

def keyedLast47 : List TauState :=
  []

theorem keyedLast47_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.b, LColor.p, LColor.r, LColor.p]) =
      keyedLast47 := by
  decide

theorem cert47_keyed_empty :
    closedCollarFiber3Keyed word [LColor.b, LColor.p, LColor.r, LColor.p] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.b, LColor.p, LColor.r, LColor.p] keyedLast47_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast47 = [] := by
    simpa [keyedLast47] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert47_empty :
    closedCollarFiber word [LColor.b, LColor.p, LColor.r, LColor.p] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.b, LColor.p, LColor.r, LColor.p]
  exact hfast.trans cert47_keyed_empty

theorem cert47_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.p, LColor.r, LColor.p] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert47_empty

def keyedLast51 : List TauState :=
  []

theorem keyedLast51_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.b, LColor.p, LColor.p, LColor.r]) =
      keyedLast51 := by
  decide

theorem cert51_keyed_empty :
    closedCollarFiber3Keyed word [LColor.b, LColor.p, LColor.p, LColor.r] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.b, LColor.p, LColor.p, LColor.r] keyedLast51_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast51 = [] := by
    simpa [keyedLast51] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert51_empty :
    closedCollarFiber word [LColor.b, LColor.p, LColor.p, LColor.r] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.b, LColor.p, LColor.p, LColor.r]
  exact hfast.trans cert51_keyed_empty

theorem cert51_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.p, LColor.p, LColor.r] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert51_empty

def keyedLast52 : List TauState :=
  []

theorem keyedLast52_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.b, LColor.p, LColor.p, LColor.b]) =
      keyedLast52 := by
  decide

theorem cert52_keyed_empty :
    closedCollarFiber3Keyed word [LColor.b, LColor.p, LColor.p, LColor.b] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.b, LColor.p, LColor.p, LColor.b] keyedLast52_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast52 = [] := by
    simpa [keyedLast52] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert52_empty :
    closedCollarFiber word [LColor.b, LColor.p, LColor.p, LColor.b] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.b, LColor.p, LColor.p, LColor.b]
  exact hfast.trans cert52_keyed_empty

theorem cert52_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.p, LColor.p, LColor.b] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert52_empty

def keyedLast53 : List TauState :=
  []

theorem keyedLast53_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.b, LColor.p, LColor.p, LColor.p]) =
      keyedLast53 := by
  decide

theorem cert53_keyed_empty :
    closedCollarFiber3Keyed word [LColor.b, LColor.p, LColor.p, LColor.p] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.b, LColor.p, LColor.p, LColor.p] keyedLast53_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast53 = [] := by
    simpa [keyedLast53] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert53_empty :
    closedCollarFiber word [LColor.b, LColor.p, LColor.p, LColor.p] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.b, LColor.p, LColor.p, LColor.p]
  exact hfast.trans cert53_keyed_empty

theorem cert53_connected :
    closedCollarFiberKempeConnected word [LColor.b, LColor.p, LColor.p, LColor.p] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert53_empty

def keyedLast54 : List TauState :=
  []

theorem keyedLast54_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.p, LColor.r, LColor.r, LColor.r]) =
      keyedLast54 := by
  decide

theorem cert54_keyed_empty :
    closedCollarFiber3Keyed word [LColor.p, LColor.r, LColor.r, LColor.r] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.p, LColor.r, LColor.r, LColor.r] keyedLast54_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast54 = [] := by
    simpa [keyedLast54] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert54_empty :
    closedCollarFiber word [LColor.p, LColor.r, LColor.r, LColor.r] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.p, LColor.r, LColor.r, LColor.r]
  exact hfast.trans cert54_keyed_empty

theorem cert54_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.r, LColor.r, LColor.r] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert54_empty

def keyedLast55 : List TauState :=
  []

theorem keyedLast55_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.p, LColor.r, LColor.r, LColor.b]) =
      keyedLast55 := by
  decide

theorem cert55_keyed_empty :
    closedCollarFiber3Keyed word [LColor.p, LColor.r, LColor.r, LColor.b] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.p, LColor.r, LColor.r, LColor.b] keyedLast55_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast55 = [] := by
    simpa [keyedLast55] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert55_empty :
    closedCollarFiber word [LColor.p, LColor.r, LColor.r, LColor.b] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.p, LColor.r, LColor.r, LColor.b]
  exact hfast.trans cert55_keyed_empty

theorem cert55_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.r, LColor.r, LColor.b] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert55_empty

def keyedLast56 : List TauState :=
  []

theorem keyedLast56_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.p, LColor.r, LColor.r, LColor.p]) =
      keyedLast56 := by
  decide

theorem cert56_keyed_empty :
    closedCollarFiber3Keyed word [LColor.p, LColor.r, LColor.r, LColor.p] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.p, LColor.r, LColor.r, LColor.p] keyedLast56_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast56 = [] := by
    simpa [keyedLast56] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert56_empty :
    closedCollarFiber word [LColor.p, LColor.r, LColor.r, LColor.p] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.p, LColor.r, LColor.r, LColor.p]
  exact hfast.trans cert56_keyed_empty

theorem cert56_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.r, LColor.r, LColor.p] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert56_empty

def keyedLast57 : List TauState :=
  []

theorem keyedLast57_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.p, LColor.r, LColor.b, LColor.r]) =
      keyedLast57 := by
  decide

theorem cert57_keyed_empty :
    closedCollarFiber3Keyed word [LColor.p, LColor.r, LColor.b, LColor.r] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.p, LColor.r, LColor.b, LColor.r] keyedLast57_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast57 = [] := by
    simpa [keyedLast57] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert57_empty :
    closedCollarFiber word [LColor.p, LColor.r, LColor.b, LColor.r] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.p, LColor.r, LColor.b, LColor.r]
  exact hfast.trans cert57_keyed_empty

theorem cert57_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.r, LColor.b, LColor.r] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert57_empty

def keyedLast58 : List TauState :=
  []

theorem keyedLast58_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.p, LColor.r, LColor.b, LColor.b]) =
      keyedLast58 := by
  decide

theorem cert58_keyed_empty :
    closedCollarFiber3Keyed word [LColor.p, LColor.r, LColor.b, LColor.b] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.p, LColor.r, LColor.b, LColor.b] keyedLast58_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast58 = [] := by
    simpa [keyedLast58] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert58_empty :
    closedCollarFiber word [LColor.p, LColor.r, LColor.b, LColor.b] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.p, LColor.r, LColor.b, LColor.b]
  exact hfast.trans cert58_keyed_empty

theorem cert58_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.r, LColor.b, LColor.b] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert58_empty

def keyedLast59 : List TauState :=
  []

theorem keyedLast59_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.p, LColor.r, LColor.b, LColor.p]) =
      keyedLast59 := by
  decide

theorem cert59_keyed_empty :
    closedCollarFiber3Keyed word [LColor.p, LColor.r, LColor.b, LColor.p] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.p, LColor.r, LColor.b, LColor.p] keyedLast59_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast59 = [] := by
    simpa [keyedLast59] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert59_empty :
    closedCollarFiber word [LColor.p, LColor.r, LColor.b, LColor.p] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.p, LColor.r, LColor.b, LColor.p]
  exact hfast.trans cert59_keyed_empty

theorem cert59_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.r, LColor.b, LColor.p] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert59_empty

def keyedLast63 : List TauState :=
  []

theorem keyedLast63_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.p, LColor.b, LColor.r, LColor.r]) =
      keyedLast63 := by
  decide

theorem cert63_keyed_empty :
    closedCollarFiber3Keyed word [LColor.p, LColor.b, LColor.r, LColor.r] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.p, LColor.b, LColor.r, LColor.r] keyedLast63_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast63 = [] := by
    simpa [keyedLast63] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert63_empty :
    closedCollarFiber word [LColor.p, LColor.b, LColor.r, LColor.r] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.p, LColor.b, LColor.r, LColor.r]
  exact hfast.trans cert63_keyed_empty

theorem cert63_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.b, LColor.r, LColor.r] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert63_empty

def keyedLast64 : List TauState :=
  []

theorem keyedLast64_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.p, LColor.b, LColor.r, LColor.b]) =
      keyedLast64 := by
  decide

theorem cert64_keyed_empty :
    closedCollarFiber3Keyed word [LColor.p, LColor.b, LColor.r, LColor.b] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.p, LColor.b, LColor.r, LColor.b] keyedLast64_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast64 = [] := by
    simpa [keyedLast64] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert64_empty :
    closedCollarFiber word [LColor.p, LColor.b, LColor.r, LColor.b] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.p, LColor.b, LColor.r, LColor.b]
  exact hfast.trans cert64_keyed_empty

theorem cert64_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.b, LColor.r, LColor.b] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert64_empty

def keyedLast65 : List TauState :=
  []

theorem keyedLast65_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.p, LColor.b, LColor.r, LColor.p]) =
      keyedLast65 := by
  decide

theorem cert65_keyed_empty :
    closedCollarFiber3Keyed word [LColor.p, LColor.b, LColor.r, LColor.p] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.p, LColor.b, LColor.r, LColor.p] keyedLast65_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast65 = [] := by
    simpa [keyedLast65] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert65_empty :
    closedCollarFiber word [LColor.p, LColor.b, LColor.r, LColor.p] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.p, LColor.b, LColor.r, LColor.p]
  exact hfast.trans cert65_keyed_empty

theorem cert65_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.b, LColor.r, LColor.p] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert65_empty

def keyedLast66 : List TauState :=
  []

theorem keyedLast66_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.p, LColor.b, LColor.b, LColor.r]) =
      keyedLast66 := by
  decide

theorem cert66_keyed_empty :
    closedCollarFiber3Keyed word [LColor.p, LColor.b, LColor.b, LColor.r] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.p, LColor.b, LColor.b, LColor.r] keyedLast66_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast66 = [] := by
    simpa [keyedLast66] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert66_empty :
    closedCollarFiber word [LColor.p, LColor.b, LColor.b, LColor.r] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.p, LColor.b, LColor.b, LColor.r]
  exact hfast.trans cert66_keyed_empty

theorem cert66_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.b, LColor.b, LColor.r] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert66_empty

def keyedLast67 : List TauState :=
  []

theorem keyedLast67_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.p, LColor.b, LColor.b, LColor.b]) =
      keyedLast67 := by
  decide

theorem cert67_keyed_empty :
    closedCollarFiber3Keyed word [LColor.p, LColor.b, LColor.b, LColor.b] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.p, LColor.b, LColor.b, LColor.b] keyedLast67_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast67 = [] := by
    simpa [keyedLast67] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert67_empty :
    closedCollarFiber word [LColor.p, LColor.b, LColor.b, LColor.b] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.p, LColor.b, LColor.b, LColor.b]
  exact hfast.trans cert67_keyed_empty

theorem cert67_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.b, LColor.b, LColor.b] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert67_empty

def keyedLast68 : List TauState :=
  []

theorem keyedLast68_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.p, LColor.b, LColor.b, LColor.p]) =
      keyedLast68 := by
  decide

theorem cert68_keyed_empty :
    closedCollarFiber3Keyed word [LColor.p, LColor.b, LColor.b, LColor.p] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.p, LColor.b, LColor.b, LColor.p] keyedLast68_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast68 = [] := by
    simpa [keyedLast68] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert68_empty :
    closedCollarFiber word [LColor.p, LColor.b, LColor.b, LColor.p] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.p, LColor.b, LColor.b, LColor.p]
  exact hfast.trans cert68_keyed_empty

theorem cert68_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.b, LColor.b, LColor.p] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert68_empty

def keyedLast78 : List TauState :=
  []

theorem keyedLast78_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.p, LColor.p, LColor.p, LColor.r]) =
      keyedLast78 := by
  decide

theorem cert78_keyed_empty :
    closedCollarFiber3Keyed word [LColor.p, LColor.p, LColor.p, LColor.r] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.p, LColor.p, LColor.p, LColor.r] keyedLast78_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast78 = [] := by
    simpa [keyedLast78] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert78_empty :
    closedCollarFiber word [LColor.p, LColor.p, LColor.p, LColor.r] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.p, LColor.p, LColor.p, LColor.r]
  exact hfast.trans cert78_keyed_empty

theorem cert78_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.p, LColor.p, LColor.r] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert78_empty

def keyedLast79 : List TauState :=
  []

theorem keyedLast79_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.p, LColor.p, LColor.p, LColor.b]) =
      keyedLast79 := by
  decide

theorem cert79_keyed_empty :
    closedCollarFiber3Keyed word [LColor.p, LColor.p, LColor.p, LColor.b] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.p, LColor.p, LColor.p, LColor.b] keyedLast79_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast79 = [] := by
    simpa [keyedLast79] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert79_empty :
    closedCollarFiber word [LColor.p, LColor.p, LColor.p, LColor.b] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.p, LColor.p, LColor.p, LColor.b]
  exact hfast.trans cert79_keyed_empty

theorem cert79_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.p, LColor.p, LColor.b] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert79_empty

def keyedLast80 : List TauState :=
  []

theorem keyedLast80_eq :
    (allTauStates.filter fun s2 =>
      closedCollarKey word [default, default, s2] == [LColor.p, LColor.p, LColor.p, LColor.p]) =
      keyedLast80 := by
  decide

theorem cert80_keyed_empty :
    closedCollarFiber3Keyed word [LColor.p, LColor.p, LColor.p, LColor.p] = [] := by
  have hfrom := closedCollarFiber3Keyed_eq_from
    word [LColor.p, LColor.p, LColor.p, LColor.p] keyedLast80_eq
  have hnil : closedCollarFiber3KeyedFrom word keyedLast80 = [] := by
    simpa [keyedLast80] using closedCollarFiber3KeyedFrom_nil word
  exact hfrom.trans hnil

theorem cert80_empty :
    closedCollarFiber word [LColor.p, LColor.p, LColor.p, LColor.p] = [] := by
  have hfast := closedCollarFiber_three_eq_keyed TauOrient.normal TauOrient.normal TauOrient.mirror [LColor.p, LColor.p, LColor.p, LColor.p]
  exact hfast.trans cert80_keyed_empty

theorem cert80_connected :
    closedCollarFiberKempeConnected word [LColor.p, LColor.p, LColor.p, LColor.p] :=
  closedCollarFiberKempeConnected_of_closedFiber_eq_nil cert80_empty

theorem targetForWord : closedCollarS2BridgeTargetForWord word := by
  intro key hkey
  have hcases :
      key = [LColor.r, LColor.r, LColor.r, LColor.r] ∨
        key = [LColor.r, LColor.r, LColor.r, LColor.b] ∨
          key = [LColor.r, LColor.r, LColor.r, LColor.p] ∨
            key = [LColor.r, LColor.r, LColor.b, LColor.r] ∨
            key = [LColor.r, LColor.r, LColor.b, LColor.b] ∨
            key = [LColor.r, LColor.r, LColor.b, LColor.p] ∨
            key = [LColor.r, LColor.r, LColor.p, LColor.r] ∨
            key = [LColor.r, LColor.r, LColor.p, LColor.b] ∨
            key = [LColor.r, LColor.r, LColor.p, LColor.p] ∨
            key = [LColor.r, LColor.b, LColor.r, LColor.r] ∨
            key = [LColor.r, LColor.b, LColor.r, LColor.b] ∨
            key = [LColor.r, LColor.b, LColor.r, LColor.p] ∨
            key = [LColor.r, LColor.b, LColor.b, LColor.r] ∨
            key = [LColor.r, LColor.b, LColor.b, LColor.b] ∨
            key = [LColor.r, LColor.b, LColor.b, LColor.p] ∨
            key = [LColor.r, LColor.b, LColor.p, LColor.r] ∨
            key = [LColor.r, LColor.b, LColor.p, LColor.b] ∨
            key = [LColor.r, LColor.b, LColor.p, LColor.p] ∨
            key = [LColor.r, LColor.p, LColor.r, LColor.r] ∨
            key = [LColor.r, LColor.p, LColor.r, LColor.b] ∨
            key = [LColor.r, LColor.p, LColor.r, LColor.p] ∨
            key = [LColor.r, LColor.p, LColor.b, LColor.r] ∨
            key = [LColor.r, LColor.p, LColor.b, LColor.b] ∨
            key = [LColor.r, LColor.p, LColor.b, LColor.p] ∨
            key = [LColor.r, LColor.p, LColor.p, LColor.r] ∨
            key = [LColor.r, LColor.p, LColor.p, LColor.b] ∨
            key = [LColor.r, LColor.p, LColor.p, LColor.p] ∨
            key = [LColor.b, LColor.r, LColor.r, LColor.r] ∨
            key = [LColor.b, LColor.r, LColor.r, LColor.b] ∨
            key = [LColor.b, LColor.r, LColor.r, LColor.p] ∨
            key = [LColor.b, LColor.r, LColor.b, LColor.r] ∨
            key = [LColor.b, LColor.r, LColor.b, LColor.b] ∨
            key = [LColor.b, LColor.r, LColor.b, LColor.p] ∨
            key = [LColor.b, LColor.r, LColor.p, LColor.r] ∨
            key = [LColor.b, LColor.r, LColor.p, LColor.b] ∨
            key = [LColor.b, LColor.r, LColor.p, LColor.p] ∨
            key = [LColor.b, LColor.b, LColor.r, LColor.r] ∨
            key = [LColor.b, LColor.b, LColor.r, LColor.b] ∨
            key = [LColor.b, LColor.b, LColor.r, LColor.p] ∨
            key = [LColor.b, LColor.b, LColor.b, LColor.r] ∨
            key = [LColor.b, LColor.b, LColor.b, LColor.b] ∨
            key = [LColor.b, LColor.b, LColor.b, LColor.p] ∨
            key = [LColor.b, LColor.b, LColor.p, LColor.r] ∨
            key = [LColor.b, LColor.b, LColor.p, LColor.b] ∨
            key = [LColor.b, LColor.b, LColor.p, LColor.p] ∨
            key = [LColor.b, LColor.p, LColor.r, LColor.r] ∨
            key = [LColor.b, LColor.p, LColor.r, LColor.b] ∨
            key = [LColor.b, LColor.p, LColor.r, LColor.p] ∨
            key = [LColor.b, LColor.p, LColor.b, LColor.r] ∨
            key = [LColor.b, LColor.p, LColor.b, LColor.b] ∨
            key = [LColor.b, LColor.p, LColor.b, LColor.p] ∨
            key = [LColor.b, LColor.p, LColor.p, LColor.r] ∨
            key = [LColor.b, LColor.p, LColor.p, LColor.b] ∨
            key = [LColor.b, LColor.p, LColor.p, LColor.p] ∨
            key = [LColor.p, LColor.r, LColor.r, LColor.r] ∨
            key = [LColor.p, LColor.r, LColor.r, LColor.b] ∨
            key = [LColor.p, LColor.r, LColor.r, LColor.p] ∨
            key = [LColor.p, LColor.r, LColor.b, LColor.r] ∨
            key = [LColor.p, LColor.r, LColor.b, LColor.b] ∨
            key = [LColor.p, LColor.r, LColor.b, LColor.p] ∨
            key = [LColor.p, LColor.r, LColor.p, LColor.r] ∨
            key = [LColor.p, LColor.r, LColor.p, LColor.b] ∨
            key = [LColor.p, LColor.r, LColor.p, LColor.p] ∨
            key = [LColor.p, LColor.b, LColor.r, LColor.r] ∨
            key = [LColor.p, LColor.b, LColor.r, LColor.b] ∨
            key = [LColor.p, LColor.b, LColor.r, LColor.p] ∨
            key = [LColor.p, LColor.b, LColor.b, LColor.r] ∨
            key = [LColor.p, LColor.b, LColor.b, LColor.b] ∨
            key = [LColor.p, LColor.b, LColor.b, LColor.p] ∨
            key = [LColor.p, LColor.b, LColor.p, LColor.r] ∨
            key = [LColor.p, LColor.b, LColor.p, LColor.b] ∨
            key = [LColor.p, LColor.b, LColor.p, LColor.p] ∨
            key = [LColor.p, LColor.p, LColor.r, LColor.r] ∨
            key = [LColor.p, LColor.p, LColor.r, LColor.b] ∨
            key = [LColor.p, LColor.p, LColor.r, LColor.p] ∨
            key = [LColor.p, LColor.p, LColor.b, LColor.r] ∨
            key = [LColor.p, LColor.p, LColor.b, LColor.b] ∨
            key = [LColor.p, LColor.p, LColor.b, LColor.p] ∨
            key = [LColor.p, LColor.p, LColor.p, LColor.r] ∨
            key = [LColor.p, LColor.p, LColor.p, LColor.b] ∨
            key = [LColor.p, LColor.p, LColor.p, LColor.p] := by
    simpa [colorAssignments4, bindList, colors] using hkey
  rcases hcases with h0 | hcases
  · simpa [h0] using cert0_connected
  rcases hcases with h1 | hcases
  · simpa [h1] using cert1_connected
  rcases hcases with h2 | hcases
  · simpa [h2] using cert2_connected
  rcases hcases with h3 | hcases
  · simpa [h3] using cert3_connected
  rcases hcases with h4 | hcases
  · simpa [h4] using cert4_connected
  rcases hcases with h5 | hcases
  · simpa [h5] using cert5_connected
  rcases hcases with h6 | hcases
  · simpa [h6] using cert6_connected
  rcases hcases with h7 | hcases
  · simpa [h7] using cert7_connected
  rcases hcases with h8 | hcases
  · simpa [h8] using cert8_connected
  rcases hcases with h9 | hcases
  · simpa [h9] using cert9_connected
  rcases hcases with h10 | hcases
  · simpa [h10] using cert10_connected
  rcases hcases with h11 | hcases
  · simpa [h11] using cert11_connected
  rcases hcases with h12 | hcases
  · simpa [h12] using cert12_connected
  rcases hcases with h13 | hcases
  · simpa [h13] using cert13_connected
  rcases hcases with h14 | hcases
  · simpa [h14] using cert14_connected
  rcases hcases with h15 | hcases
  · simpa [h15] using cert15_connected
  rcases hcases with h16 | hcases
  · simpa [h16] using cert16_connected
  rcases hcases with h17 | hcases
  · simpa [h17] using cert17_connected
  rcases hcases with h18 | hcases
  · simpa [h18] using cert18_connected
  rcases hcases with h19 | hcases
  · simpa [h19] using cert19_connected
  rcases hcases with h20 | hcases
  · simpa [h20] using cert20_connected
  rcases hcases with h21 | hcases
  · simpa [h21] using cert21_connected
  rcases hcases with h22 | hcases
  · simpa [h22] using cert22_connected
  rcases hcases with h23 | hcases
  · simpa [h23] using cert23_connected
  rcases hcases with h24 | hcases
  · simpa [h24] using cert24_connected
  rcases hcases with h25 | hcases
  · simpa [h25] using cert25_connected
  rcases hcases with h26 | hcases
  · simpa [h26] using cert26_connected
  rcases hcases with h27 | hcases
  · simpa [h27] using cert27_connected
  rcases hcases with h28 | hcases
  · simpa [h28] using cert28_connected
  rcases hcases with h29 | hcases
  · simpa [h29] using cert29_connected
  rcases hcases with h30 | hcases
  · simpa [h30] using cert30_connected
  rcases hcases with h31 | hcases
  · simpa [h31] using cert31_connected
  rcases hcases with h32 | hcases
  · simpa [h32] using cert32_connected
  rcases hcases with h33 | hcases
  · simpa [h33] using cert33_connected
  rcases hcases with h34 | hcases
  · simpa [h34] using cert34_connected
  rcases hcases with h35 | hcases
  · simpa [h35] using cert35_connected
  rcases hcases with h36 | hcases
  · simpa [h36] using cert36_connected
  rcases hcases with h37 | hcases
  · simpa [h37] using cert37_connected
  rcases hcases with h38 | hcases
  · simpa [h38] using cert38_connected
  rcases hcases with h39 | hcases
  · simpa [h39] using cert39_connected
  rcases hcases with h40 | hcases
  · simpa [h40] using cert40_connected
  rcases hcases with h41 | hcases
  · simpa [h41] using cert41_connected
  rcases hcases with h42 | hcases
  · simpa [h42] using cert42_connected
  rcases hcases with h43 | hcases
  · simpa [h43] using cert43_connected
  rcases hcases with h44 | hcases
  · simpa [h44] using cert44_connected
  rcases hcases with h45 | hcases
  · simpa [h45] using cert45_connected
  rcases hcases with h46 | hcases
  · simpa [h46] using cert46_connected
  rcases hcases with h47 | hcases
  · simpa [h47] using cert47_connected
  rcases hcases with h48 | hcases
  · simpa [h48] using cert48_connected
  rcases hcases with h49 | hcases
  · simpa [h49] using cert49_connected
  rcases hcases with h50 | hcases
  · simpa [h50] using cert50_connected
  rcases hcases with h51 | hcases
  · simpa [h51] using cert51_connected
  rcases hcases with h52 | hcases
  · simpa [h52] using cert52_connected
  rcases hcases with h53 | hcases
  · simpa [h53] using cert53_connected
  rcases hcases with h54 | hcases
  · simpa [h54] using cert54_connected
  rcases hcases with h55 | hcases
  · simpa [h55] using cert55_connected
  rcases hcases with h56 | hcases
  · simpa [h56] using cert56_connected
  rcases hcases with h57 | hcases
  · simpa [h57] using cert57_connected
  rcases hcases with h58 | hcases
  · simpa [h58] using cert58_connected
  rcases hcases with h59 | hcases
  · simpa [h59] using cert59_connected
  rcases hcases with h60 | hcases
  · simpa [h60] using cert60_connected
  rcases hcases with h61 | hcases
  · simpa [h61] using cert61_connected
  rcases hcases with h62 | hcases
  · simpa [h62] using cert62_connected
  rcases hcases with h63 | hcases
  · simpa [h63] using cert63_connected
  rcases hcases with h64 | hcases
  · simpa [h64] using cert64_connected
  rcases hcases with h65 | hcases
  · simpa [h65] using cert65_connected
  rcases hcases with h66 | hcases
  · simpa [h66] using cert66_connected
  rcases hcases with h67 | hcases
  · simpa [h67] using cert67_connected
  rcases hcases with h68 | hcases
  · simpa [h68] using cert68_connected
  rcases hcases with h69 | hcases
  · simpa [h69] using cert69_connected
  rcases hcases with h70 | hcases
  · simpa [h70] using cert70_connected
  rcases hcases with h71 | hcases
  · simpa [h71] using cert71_connected
  rcases hcases with h72 | hcases
  · simpa [h72] using cert72_connected
  rcases hcases with h73 | hcases
  · simpa [h73] using cert73_connected
  rcases hcases with h74 | hcases
  · simpa [h74] using cert74_connected
  rcases hcases with h75 | hcases
  · simpa [h75] using cert75_connected
  rcases hcases with h76 | hcases
  · simpa [h76] using cert76_connected
  rcases hcases with h77 | hcases
  · simpa [h77] using cert77_connected
  rcases hcases with h78 | hcases
  · simpa [h78] using cert78_connected
  rcases hcases with h79 | hcases
  · simpa [h79] using cert79_connected
  simpa [hcases] using cert80_connected

end GoertzelLemma818ClosedCollarS2Word5
end Mettapedia.GraphTheory.FourColor
