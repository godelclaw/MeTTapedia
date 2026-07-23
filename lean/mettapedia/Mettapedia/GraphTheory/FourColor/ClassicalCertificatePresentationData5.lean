import Mettapedia.GraphTheory.FourColor.ClassicalCertificatePresentationCertificate

/-! Generated finite unavoidability presentation certificate. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificatePresentationData5

open ClassicalCertificatePresentationPattern
open ClassicalCertificatePresentationCertificate

def sourceSha256 : String := "46965e354a4377316daff9f0e47ab5ea06921eceaf1b9cefd4f140c561da9da4"
def arity : Nat := 5
def splitCount : Nat := 24
def leafCount : Nat := 25

def code : Code :=
  (.split true ⟨.spoke, 0, 5, true⟩
    (.split true ⟨.spoke, 1, 5, true⟩
      (.split true ⟨.spoke, 2, 6, true⟩
        (.split false ⟨.spoke, 2, 5, true⟩
          (.terminal .reducible)
          (.split false ⟨.spoke, 3, 5, true⟩
            (.terminal .reducible)
            (.split false ⟨.spoke, 4, 6, false⟩
              (.terminal (.hubcap [⟨0, some 1, 0⟩, ⟨2, some 3, -6⟩, ⟨4, none, -4⟩]))
              (.split false ⟨.spoke, 4, 5, false⟩
                (.terminal (.hubcap [⟨0, some 1, 0⟩, ⟨2, some 3, -7⟩, ⟨4, none, -3⟩]))
                (.terminal .reducible)))))
        (.split false ⟨.spoke, 4, 6, true⟩
          (.similar 0 ⟨true, 3⟩)
          (.split false ⟨.spoke, 3, 5, false⟩
            (.terminal (.hubcap [⟨0, some 1, 0⟩, ⟨2, some 3, -6⟩, ⟨4, none, -4⟩]))
            (.terminal (.hubcap [⟨0, some 1, 0⟩, ⟨2, some 3, -5⟩, ⟨4, none, -5⟩])))))
      (.split false ⟨.spoke, 4, 5, true⟩
        (.similar 0 ⟨false, 4⟩)
        (.split true ⟨.spoke, 2, 5, true⟩
          (.split false ⟨.spoke, 1, 6, true⟩
            (.terminal .reducible)
            (.split false ⟨.spoke, 3, 5, true⟩
              (.similar 0 ⟨false, 2⟩)
              (.split true ⟨.spoke, 3, 6, true⟩
                (.split false ⟨.spoke, 4, 6, true⟩
                  (.terminal .reducible)
                  (.terminal (.hubcap [⟨0, some 1, -4⟩, ⟨2, some 3, -2⟩, ⟨4, none, -4⟩])))
                (.split false ⟨.spoke, 4, 6, true⟩
                  (.similar 0 ⟨true, 2⟩)
                  (.terminal (.hubcap [⟨0, some 1, -4⟩, ⟨2, some 3, -3⟩, ⟨4, none, -3⟩]))))))
          (.split false ⟨.spoke, 3, 5, true⟩
            (.similar 0 ⟨true, 4⟩)
            (.split true ⟨.spoke, 1, 6, false⟩
              (.split false ⟨.spoke, 4, 6, false⟩
                (.terminal (.hubcap [⟨0, some 1, -3⟩, ⟨2, some 3, -4⟩, ⟨4, none, -3⟩]))
                (.terminal (.hubcap [⟨0, some 1, -3⟩, ⟨2, some 3, -5⟩, ⟨4, none, -2⟩])))
              (.split false ⟨.spoke, 4, 6, false⟩
                (.similar 0 ⟨true, 4⟩)
                (.terminal (.hubcap [⟨0, some 1, -2⟩, ⟨2, some 3, -6⟩, ⟨4, none, -2⟩]))))))))
    (.split false ⟨.spoke, 1, 5, true⟩
      (.similar 0 ⟨false, 1⟩)
      (.split false ⟨.spoke, 2, 5, true⟩
        (.similar 0 ⟨false, 2⟩)
        (.split false ⟨.spoke, 3, 5, true⟩
          (.similar 0 ⟨false, 3⟩)
          (.split false ⟨.spoke, 4, 5, true⟩
            (.similar 0 ⟨false, 4⟩)
            (.terminal (.hubcap [⟨0, some 1, -4⟩, ⟨2, some 3, -4⟩, ⟨4, none, -2⟩])))))))

theorem structureCheck_eq_true :
    structureCheck arity code = true := by
  rfl

end ClassicalCertificatePresentationData5

end Mettapedia.GraphTheory.FourColor
