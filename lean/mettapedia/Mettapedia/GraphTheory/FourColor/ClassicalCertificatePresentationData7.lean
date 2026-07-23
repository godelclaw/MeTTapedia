import Mettapedia.GraphTheory.FourColor.ClassicalCertificatePresentationCertificate

/-! Generated finite unavoidability presentation certificate. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificatePresentationData7

open ClassicalCertificatePresentationPattern
open ClassicalCertificatePresentationCertificate

def sourceSha256 : String := "ebec114766046f546eb6dc645622bab0b80fc42e13fe46120f9770655833ef00"
def arity : Nat := 7
def splitCount : Nat := 2649
def leafCount : Nat := 2650

def code : Code :=
  (.split true ⟨.spoke, 0, 5, true⟩
    (.split true ⟨.spoke, 1, 5, true⟩
      (.split true ⟨.spoke, 2, 5, true⟩
        (.split false ⟨.spoke, 3, 5, true⟩
          (.terminal .reducible)
          (.split false ⟨.spoke, 6, 5, true⟩
            (.terminal .reducible)
            (.split true ⟨.spoke, 3, 6, false⟩
              (.split false ⟨.spoke, 6, 6, false⟩
                (.split false ⟨.hat, 5, 5, true⟩
                  (.split true ⟨.spoke, 4, 7, false⟩
                    (.split false ⟨.spoke, 3, 7, false⟩
                      (.terminal (.hubcap [⟨1, none, 5⟩, ⟨3, none, -2⟩, ⟨4, none, 0⟩, ⟨0, some 2, 7⟩, ⟨5, some 6, 0⟩]))
                      (.split false ⟨.spoke, 5, 5, false⟩
                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩, ⟨2, some 3, 2⟩]))
                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, -3⟩, ⟨2, some 3, 2⟩]))))
                    (.split false ⟨.spoke, 5, 7, false⟩
                      (.similar 0 ⟨true, 4⟩)
                      (.split true ⟨.spoke, 3, 7, false⟩
                        (.split true ⟨.spoke, 3, 8, false⟩
                          (.split true ⟨.spoke, 4, 5, false⟩
                            (.split false ⟨.spoke, 4, 6, true⟩
                              (.terminal (.hubcap [⟨1, none, 5⟩, ⟨3, none, -2⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, -1⟩, ⟨0, some 2, 7⟩]))
                              (.split false ⟨.spoke, 5, 5, false⟩
                                (.terminal (.hubcap [⟨1, none, 5⟩, ⟨3, none, -2⟩, ⟨4, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩, ⟨0, some 2, 7⟩]))
                                (.terminal (.hubcap [⟨1, none, 5⟩, ⟨3, none, -3⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, -3⟩, ⟨0, some 2, 7⟩]))))
                            (.split false ⟨.spoke, 5, 6, true⟩
                              (.terminal .reducible)
                              (.split false ⟨.spoke, 6, 8, false⟩
                                (.similar 0 ⟨true, 4⟩)
                                (.terminal (.hubcap [⟨1, none, 5⟩, ⟨3, none, -3⟩, ⟨4, none, 2⟩, ⟨0, some 2, 7⟩, ⟨5, some 6, -1⟩])))))
                          (.split false ⟨.spoke, 6, 8, false⟩
                            (.similar 0 ⟨true, 4⟩)
                            (.split true ⟨.spoke, 4, 5, false⟩
                              (.split false ⟨.spoke, 4, 6, true⟩
                                (.terminal (.hubcap [⟨1, none, 5⟩, ⟨3, none, -2⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, -1⟩, ⟨0, some 2, 7⟩]))
                                (.split false ⟨.spoke, 5, 5, false⟩
                                  (.terminal (.hubcap [⟨1, none, 5⟩, ⟨3, none, -2⟩, ⟨4, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩, ⟨0, some 2, 7⟩]))
                                  (.terminal (.hubcap [⟨1, none, 5⟩, ⟨3, none, -3⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, -3⟩, ⟨0, some 2, 7⟩]))))
                              (.split false ⟨.spoke, 5, 6, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.spoke, 6, 7, false⟩
                                  (.similar 0 ⟨true, 4⟩)
                                  (.split false ⟨.hat, 6, 5, true⟩
                                    (.terminal .reducible)
                                    (.terminal (.hubcap [⟨1, none, 5⟩, ⟨3, none, -3⟩, ⟨4, none, 2⟩, ⟨0, some 2, 7⟩, ⟨5, some 6, -1⟩]))))))))
                        (.split false ⟨.spoke, 6, 7, false⟩
                          (.similar 0 ⟨true, 4⟩)
                          (.split false ⟨.hat, 4, 5, true⟩
                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩, ⟨2, some 3, 2⟩]))
                            (.split false ⟨.hat, 6, 5, true⟩
                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩, ⟨2, some 3, 2⟩]))
                              (.split true ⟨.spoke, 4, 5, false⟩
                                (.split false ⟨.spoke, 4, 6, true⟩
                                  (.terminal (.hubcap [⟨1, none, 5⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨0, some 6, 2⟩, ⟨2, some 3, 2⟩]))
                                  (.split false ⟨.spoke, 5, 5, false⟩
                                    (.terminal (.hubcap [⟨1, none, 5⟩, ⟨4, none, 1⟩, ⟨5, none, 0⟩, ⟨0, some 6, 2⟩, ⟨2, some 3, 2⟩]))
                                    (.terminal (.hubcap [⟨1, none, 5⟩, ⟨5, none, 2⟩, ⟨6, none, -3⟩, ⟨0, some 2, 7⟩, ⟨3, some 4, -1⟩]))))
                                (.split false ⟨.spoke, 5, 5, false⟩
                                  (.similar 0 ⟨true, 4⟩)
                                  (.terminal .reducible)))))))))
                  (.split true ⟨.spoke, 4, 7, false⟩
                    (.split false ⟨.spoke, 3, 7, false⟩
                      (.terminal (.hubcap [⟨1, none, 5⟩, ⟨3, none, -2⟩, ⟨4, none, 0⟩, ⟨0, some 2, 7⟩, ⟨5, some 6, 0⟩]))
                      (.split false ⟨.spoke, 5, 5, false⟩
                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩, ⟨2, some 3, 2⟩]))
                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, -3⟩, ⟨2, some 3, 2⟩]))))
                    (.split false ⟨.spoke, 5, 7, false⟩
                      (.similar 0 ⟨true, 4⟩)
                      (.split true ⟨.spoke, 4, 5, false⟩
                        (.split false ⟨.spoke, 5, 6, false⟩
                          (.terminal (.hubcap [⟨1, none, 5⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨0, some 6, 2⟩, ⟨2, some 3, 2⟩]))
                          (.split false ⟨.spoke, 5, 5, false⟩
                            (.split false ⟨.spoke, 4, 6, false⟩
                              (.terminal (.hubcap [⟨1, none, 5⟩, ⟨4, none, 1⟩, ⟨5, none, 0⟩, ⟨0, some 6, 2⟩, ⟨2, some 3, 2⟩]))
                              (.split false ⟨.hat, 5, 6, false⟩
                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩, ⟨2, some 3, 2⟩]))
                                (.split false ⟨.fan1, 4, 6, false⟩
                                  (.terminal (.hubcap [⟨1, none, 5⟩, ⟨5, none, 0⟩, ⟨0, some 2, 7⟩, ⟨0, some 6, 2⟩, ⟨2, some 3, 2⟩, ⟨3, some 4, 0⟩, ⟨4, some 6, 0⟩]))
                                  (.split false ⟨.fan1, 4, 5, true⟩
                                    (.terminal (.hubcap [⟨1, none, 5⟩, ⟨4, none, 0⟩, ⟨6, none, -2⟩, ⟨0, some 2, 7⟩, ⟨3, some 5, 0⟩]))
                                    (.split false ⟨.spoke, 3, 7, true⟩
                                      (.terminal (.hubcap [⟨1, none, 5⟩, ⟨5, none, 0⟩, ⟨0, some 2, 7⟩, ⟨0, some 6, 2⟩, ⟨2, some 3, 2⟩, ⟨3, some 4, 0⟩, ⟨4, some 6, 0⟩]))
                                      (.split false ⟨.spoke, 6, 7, false⟩
                                        (.terminal (.hubcap [⟨1, none, 5⟩, ⟨3, none, -2⟩, ⟨6, none, -2⟩, ⟨0, some 2, 7⟩, ⟨4, some 5, 2⟩]))
                                        (.terminal (.hubcap [⟨1, none, 5⟩, ⟨3, none, -2⟩, ⟨6, none, -1⟩, ⟨0, some 2, 7⟩, ⟨4, some 5, 1⟩]))))))))
                            (.split false ⟨.spoke, 4, 6, true⟩
                              (.terminal (.hubcap [⟨1, none, 5⟩, ⟨3, none, -3⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, -3⟩, ⟨0, some 2, 7⟩]))
                              (.split false ⟨.spoke, 3, 7, false⟩
                                (.terminal (.hubcap [⟨1, none, 5⟩, ⟨3, none, -2⟩, ⟨4, none, 1⟩, ⟨5, none, 2⟩, ⟨6, none, -3⟩, ⟨0, some 2, 7⟩]))
                                (.split false ⟨.hat, 1, 5, false⟩
                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨4, none, 1⟩, ⟨5, none, 2⟩, ⟨6, none, -3⟩, ⟨2, some 3, 2⟩]))
                                  (.split false ⟨.hat, 2, 6, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.hat, 0, 5, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.hat, 3, 5, false⟩
                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, 1⟩, ⟨5, none, 2⟩, ⟨6, none, -3⟩]))
                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, -3⟩]))))))))))
                        (.split false ⟨.spoke, 5, 5, false⟩
                          (.similar 0 ⟨true, 4⟩)
                          (.terminal (.hubcap [⟨1, none, 5⟩, ⟨3, none, -4⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, -4⟩, ⟨0, some 2, 7⟩])))))))
                (.split false ⟨.spoke, 5, 5, true⟩
                  (.terminal .reducible)
                  (.split false ⟨.hat, 0, 5, true⟩
                    (.terminal .reducible)
                    (.split false ⟨.spoke, 4, 5, true⟩
                      (.split false ⟨.spoke, 5, 6, true⟩
                        (.terminal .reducible)
                        (.terminal (.hubcap [⟨3, none, -3⟩, ⟨4, none, 2⟩, ⟨5, none, -2⟩, ⟨0, some 2, 7⟩, ⟨1, some 6, 6⟩])))
                      (.split false ⟨.spoke, 5, 7, false⟩
                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨4, none, 0⟩, ⟨5, none, -2⟩, ⟨1, some 6, 6⟩, ⟨2, some 3, 2⟩]))
                        (.split false ⟨.hat, 2, 5, true⟩
                          (.split false ⟨.hat, 1, 6, true⟩
                            (.terminal .reducible)
                            (.split false ⟨.hat, 3, 5, true⟩
                              (.terminal .reducible)
                              (.split false ⟨.spoke, 5, 6, false⟩
                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, -2⟩, ⟨4, none, 0⟩, ⟨5, none, -1⟩, ⟨6, none, 1⟩]))
                                (.split false ⟨.hat, 6, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.spoke, 4, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, -2⟩, ⟨4, none, -1⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                    (.split false ⟨.spoke, 4, 6, true⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, -3⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                      (.split false ⟨.hat, 5, 5, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, -2⟩, ⟨4, none, -1⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, -2⟩, ⟨4, none, -1⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩])))))))))
                          (.split false ⟨.hat, 2, 6, true⟩
                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨6, none, 1⟩, ⟨4, some 5, 1⟩]))
                            (.split false ⟨.hat, 0, 6, true⟩
                              (.split false ⟨.hat, 1, 5, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.fan1, 6, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.spoke, 5, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, -1⟩, ⟨6, none, 2⟩]))
                                    (.split false ⟨.hat, 6, 5, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.spoke, 4, 7, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, -1⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩]))
                                        (.split false ⟨.spoke, 4, 6, true⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, -3⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩]))
                                          (.split false ⟨.spoke, 3, 7, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩]))
                                            (.split false ⟨.hat, 1, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                              (.split false ⟨.hat, 3, 5, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩]))
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩])))))))))))
                              (.split false ⟨.spoke, 5, 6, false⟩
                                (.split false ⟨.spoke, 3, 7, false⟩
                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, 0⟩, ⟨5, none, -1⟩, ⟨6, none, 1⟩]))
                                  (.split false ⟨.hat, 1, 5, false⟩
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, -1⟩, ⟨6, none, 1⟩]))
                                    (.split false ⟨.hat, 3, 5, false⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, 0⟩, ⟨5, none, -1⟩, ⟨6, none, 1⟩]))
                                      (.split false ⟨.fan1, 3, 5, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.hat, 6, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, -2⟩, ⟨6, none, 1⟩]))
                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, -2⟩, ⟨6, none, 1⟩])))))))
                                (.split false ⟨.hat, 6, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.spoke, 4, 6, true⟩
                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -3⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                    (.split false ⟨.hat, 1, 5, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                      (.split false ⟨.hat, 4, 5, true⟩
                                        (.split false ⟨.spoke, 3, 7, false⟩
                                          (.split false ⟨.spoke, 4, 7, false⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, -1⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                            (.split false ⟨.hat, 5, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, -1⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, -1⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))))
                                          (.split false ⟨.spoke, 4, 7, true⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, -1⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                            (.split false ⟨.hat, 3, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, -1⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, -1⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩])))))
                                        (.split false ⟨.spoke, 3, 7, false⟩
                                          (.split false ⟨.spoke, 4, 7, false⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, -1⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                            (.split false ⟨.hat, 5, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, -1⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, -1⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))))
                                          (.split false ⟨.hat, 3, 5, false⟩
                                            (.split false ⟨.spoke, 4, 7, false⟩
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, -1⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                              (.split false ⟨.hat, 5, 5, false⟩
                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, -1⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, -1⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))))
                                            (.split false ⟨.fan1, 3, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.spoke, 4, 7, false⟩
                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, -1⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                                (.split false ⟨.hat, 5, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, -1⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, -1⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))))))))))))))))))))
              (.split false ⟨.spoke, 6, 6, false⟩
                (.similar 0 ⟨true, 4⟩)
                (.split false ⟨.spoke, 4, 5, true⟩
                  (.terminal .reducible)
                  (.split false ⟨.spoke, 5, 5, true⟩
                    (.terminal .reducible)
                    (.split false ⟨.hat, 3, 5, true⟩
                      (.terminal .reducible)
                      (.split false ⟨.hat, 0, 5, true⟩
                        (.terminal .reducible)
                        (.split true ⟨.spoke, 4, 6, false⟩
                          (.split false ⟨.spoke, 5, 6, true⟩
                            (.terminal (.hubcap [⟨4, none, -4⟩, ⟨5, none, 0⟩, ⟨0, some 2, 7⟩, ⟨1, some 3, 6⟩, ⟨1, some 6, 6⟩, ⟨3, some 6, 3⟩]))
                            (.split true ⟨.spoke, 4, 7, false⟩
                              (.split false ⟨.spoke, 5, 7, false⟩
                                (.terminal (.hubcap [⟨4, none, -2⟩, ⟨5, none, -2⟩, ⟨0, some 2, 7⟩, ⟨1, some 3, 6⟩, ⟨1, some 6, 6⟩, ⟨3, some 6, 3⟩]))
                                (.split false ⟨.hat, 6, 5, false⟩
                                  (.terminal (.hubcap [⟨4, none, -2⟩, ⟨5, none, -2⟩, ⟨0, some 2, 7⟩, ⟨1, some 3, 6⟩, ⟨1, some 6, 6⟩, ⟨3, some 6, 3⟩]))
                                  (.terminal (.hubcap [⟨4, none, -2⟩, ⟨5, none, -2⟩, ⟨0, some 2, 7⟩, ⟨1, some 3, 6⟩, ⟨1, some 6, 6⟩, ⟨3, some 6, 3⟩]))))
                              (.split false ⟨.spoke, 5, 7, false⟩
                                (.similar 0 ⟨true, 4⟩)
                                (.split true ⟨.hat, 4, 5, false⟩
                                  (.split false ⟨.hat, 6, 5, false⟩
                                    (.terminal (.hubcap [⟨4, none, -2⟩, ⟨5, none, -2⟩, ⟨0, some 2, 7⟩, ⟨1, some 3, 6⟩, ⟨1, some 6, 6⟩, ⟨3, some 6, 3⟩]))
                                    (.terminal (.hubcap [⟨4, none, -2⟩, ⟨5, none, -2⟩, ⟨0, some 2, 7⟩, ⟨1, some 3, 6⟩, ⟨1, some 6, 6⟩, ⟨3, some 6, 3⟩])))
                                  (.split false ⟨.hat, 6, 5, false⟩
                                    (.similar 0 ⟨true, 4⟩)
                                    (.split false ⟨.fan1, 4, 5, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.fan2, 5, 5, true⟩
                                        (.terminal .reducible)
                                        (.terminal (.hubcap [⟨4, none, -2⟩, ⟨5, none, -2⟩, ⟨0, some 2, 7⟩, ⟨1, some 3, 6⟩, ⟨1, some 6, 6⟩, ⟨3, some 6, 3⟩])))))))))
                          (.split false ⟨.spoke, 5, 6, false⟩
                            (.similar 0 ⟨true, 4⟩)
                            (.terminal .reducible)))))))))))
        (.split false ⟨.spoke, 6, 5, true⟩
          (.similar 0 ⟨false, 6⟩)
          (.split true ⟨.spoke, 3, 5, true⟩
            (.split false ⟨.spoke, 2, 6, true⟩
              (.terminal .reducible)
              (.split false ⟨.spoke, 4, 5, false⟩
                (.split false ⟨.spoke, 6, 6, true⟩
                  (.split false ⟨.spoke, 5, 5, true⟩
                    (.terminal .reducible)
                    (.split false ⟨.spoke, 5, 6, true⟩
                      (.split false ⟨.spoke, 4, 6, true⟩
                        (.terminal .reducible)
                        (.split false ⟨.hat, 6, 5, true⟩
                          (.terminal .reducible)
                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -2⟩, ⟨3, none, 2⟩, ⟨4, none, -1⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩]))))
                      (.split false ⟨.spoke, 4, 7, false⟩
                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -2⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, -1⟩, ⟨6, none, 3⟩]))
                        (.split false ⟨.spoke, 4, 6, false⟩
                          (.split false ⟨.spoke, 5, 7, false⟩
                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -2⟩, ⟨3, none, 2⟩, ⟨5, none, -2⟩, ⟨4, some 6, 4⟩]))
                            (.split false ⟨.hat, 1, 5, false⟩
                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, -2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, -1⟩, ⟨6, none, 2⟩]))
                              (.split false ⟨.hat, 2, 5, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.hat, 0, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.hat, 4, 5, false⟩
                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -2⟩, ⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨4, some 5, -1⟩]))
                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -2⟩, ⟨3, none, 2⟩, ⟨5, none, -2⟩, ⟨4, some 6, 4⟩])))))))
                          (.split false ⟨.spoke, 2, 7, true⟩
                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -2⟩, ⟨3, none, 3⟩, ⟨5, none, -3⟩, ⟨4, some 6, 4⟩]))
                            (.split false ⟨.hat, 1, 5, false⟩
                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, -2⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, -3⟩, ⟨6, none, 2⟩]))
                              (.split false ⟨.hat, 2, 5, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.hat, 0, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.hat, 3, 5, false⟩
                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -2⟩, ⟨3, none, 3⟩, ⟨5, none, -3⟩, ⟨4, some 6, 4⟩]))
                                    (.split false ⟨.hat, 4, 5, false⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, -3⟩, ⟨6, none, 3⟩]))
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, -3⟩, ⟨6, none, 1⟩]))))))))))))
                  (.split false ⟨.spoke, 4, 8, false⟩
                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -2⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, some 6, 2⟩]))
                    (.split false ⟨.spoke, 5, 5, true⟩
                      (.split false ⟨.spoke, 4, 7, false⟩
                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, -2⟩]))
                        (.split false ⟨.spoke, 4, 6, false⟩
                          (.split false ⟨.hat, 1, 5, false⟩
                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -2⟩, ⟨3, none, 2⟩, ⟨4, none, 4⟩, ⟨5, none, 2⟩, ⟨6, none, -2⟩]))
                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, -2⟩])))
                          (.split false ⟨.hat, 1, 5, true⟩
                            (.terminal .reducible)
                            (.split false ⟨.hat, 4, 5, false⟩
                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -3⟩, ⟨3, none, 2⟩, ⟨4, none, 4⟩, ⟨5, none, 3⟩, ⟨6, none, -3⟩]))
                              (.split false ⟨.fan1, 4, 5, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.hat, 5, 5, false⟩
                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -3⟩, ⟨3, none, 3⟩, ⟨4, none, 4⟩, ⟨5, none, 2⟩, ⟨6, none, -3⟩]))
                                  (.split false ⟨.fan1, 4, 6, true⟩
                                    (.terminal .reducible)
                                    (.split true ⟨.spoke, 2, 7, false⟩
                                      (.split false ⟨.hat, 3, 5, true⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -4⟩, ⟨3, none, 3⟩, ⟨4, none, 5⟩, ⟨5, none, 3⟩, ⟨6, none, -3⟩]))
                                        (.split false ⟨.spoke, 6, 7, true⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -3⟩, ⟨3, none, 3⟩, ⟨4, none, 4⟩, ⟨5, none, 3⟩, ⟨6, none, -3⟩]))
                                          (.split false ⟨.hat, 6, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -3⟩, ⟨3, none, 3⟩, ⟨4, none, 4⟩, ⟨5, none, 3⟩, ⟨6, none, -3⟩]))
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -3⟩, ⟨3, none, 3⟩, ⟨4, none, 5⟩, ⟨5, none, 3⟩, ⟨6, none, -4⟩])))))
                                      (.split false ⟨.spoke, 6, 7, false⟩
                                        (.similar 0 ⟨true, 5⟩)
                                        (.split false ⟨.hat, 2, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.hat, 3, 6, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.hat, 6, 6, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.hat, 0, 5, true⟩
                                                (.terminal .reducible)
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -3⟩, ⟨3, none, 3⟩, ⟨4, none, 4⟩, ⟨5, none, 3⟩, ⟨6, none, -3⟩])))))))))))))))
                      (.split false ⟨.spoke, 4, 7, false⟩
                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -2⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩]))
                        (.split false ⟨.hat, 1, 5, false⟩
                          (.split false ⟨.spoke, 4, 6, false⟩
                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -2⟩, ⟨3, none, 2⟩, ⟨5, none, 0⟩, ⟨4, some 6, 4⟩]))
                            (.split false ⟨.spoke, 5, 6, true⟩
                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -2⟩, ⟨3, none, 3⟩, ⟨6, none, -2⟩, ⟨4, some 5, 5⟩]))
                              (.split false ⟨.spoke, 6, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -2⟩, ⟨3, none, 3⟩, ⟨6, none, -1⟩, ⟨4, some 5, 4⟩]))
                                (.split false ⟨.spoke, 2, 7, true⟩
                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -2⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, some 6, 1⟩]))
                                  (.split false ⟨.hat, 1, 6, true⟩
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -2⟩, ⟨3, some 6, 2⟩, ⟨4, some 5, 4⟩]))
                                    (.split false ⟨.hat, 3, 5, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -2⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, some 6, 1⟩]))
                                      (.split false ⟨.hat, 4, 5, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, some 6, 1⟩]))
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, some 6, 1⟩])))))))))
                          (.split false ⟨.hat, 2, 5, true⟩
                            (.terminal .reducible)
                            (.split false ⟨.hat, 0, 5, true⟩
                              (.terminal .reducible)
                              (.split false ⟨.spoke, 4, 6, false⟩
                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -2⟩, ⟨3, none, 2⟩, ⟨5, none, 0⟩, ⟨4, some 6, 2⟩]))
                                (.split false ⟨.spoke, 5, 6, true⟩
                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -2⟩, ⟨3, none, 3⟩, ⟨6, none, -2⟩, ⟨4, some 5, 3⟩]))
                                  (.split false ⟨.hat, 4, 5, false⟩
                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, some 6, 0⟩]))
                                    (.split false ⟨.fan1, 4, 5, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.spoke, 5, 8, false⟩
                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -2⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, -1⟩, ⟨6, none, -1⟩]))
                                        (.split false ⟨.spoke, 2, 7, true⟩
                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -2⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩]))
                                          (.split false ⟨.hat, 3, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -2⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩]))
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩]))))))))))))))))
                (.split false ⟨.spoke, 5, 5, true⟩
                  (.similar 0 ⟨false, 3⟩)
                  (.split true ⟨.spoke, 5, 6, false⟩
                    (.split false ⟨.spoke, 6, 6, true⟩
                      (.split false ⟨.hat, 1, 5, false⟩
                        (.terminal (.hubcap [⟨1, none, 3⟩, ⟨2, none, -3⟩, ⟨4, none, 4⟩, ⟨5, none, -3⟩, ⟨6, none, 2⟩, ⟨0, some 3, 7⟩]))
                        (.split false ⟨.hat, 2, 5, true⟩
                          (.terminal .reducible)
                          (.split false ⟨.hat, 0, 5, true⟩
                            (.terminal .reducible)
                            (.split false ⟨.hat, 4, 5, true⟩
                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -4⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, -3⟩, ⟨6, none, 1⟩]))
                              (.split false ⟨.hat, 0, 6, false⟩
                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, -3⟩, ⟨6, none, 1⟩]))
                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, -4⟩, ⟨6, none, 3⟩])))))))
                      (.split true ⟨.hat, 1, 5, false⟩
                        (.split false ⟨.hat, 3, 5, true⟩
                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, some 6, 1⟩]))
                          (.split false ⟨.hat, 4, 5, false⟩
                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, some 6, 1⟩]))
                            (.split false ⟨.hat, 5, 5, true⟩
                              (.terminal .reducible)
                              (.split false ⟨.spoke, 5, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -3⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, -1⟩, ⟨6, none, 0⟩]))
                                (.split false ⟨.hat, 5, 6, false⟩
                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -3⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, -1⟩, ⟨6, none, 0⟩]))
                                  (.split false ⟨.fan1, 5, 5, false⟩
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -3⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, -1⟩, ⟨6, none, -1⟩]))
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -3⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 1⟩, ⟨6, none, -2⟩]))))))))
                        (.split false ⟨.hat, 4, 5, false⟩
                          (.similar 0 ⟨true, 2⟩)
                          (.split false ⟨.hat, 2, 5, true⟩
                            (.terminal .reducible)
                            (.split false ⟨.hat, 3, 5, true⟩
                              (.terminal .reducible)
                              (.split false ⟨.hat, 5, 5, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.hat, 0, 5, true⟩
                                  (.terminal .reducible)
                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -4⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, -1⟩, ⟨6, none, -1⟩])))))))))
                    (.split false ⟨.spoke, 6, 6, false⟩
                      (.similar 0 ⟨true, 2⟩)
                      (.terminal .reducible))))))
            (.split false ⟨.spoke, 5, 5, true⟩
              (.similar 0 ⟨true, 5⟩)
              (.split false ⟨.spoke, 4, 5, true⟩
                (.split true ⟨.spoke, 2, 6, false⟩
                  (.split false ⟨.spoke, 6, 6, false⟩
                    (.split true ⟨.spoke, 3, 6, true⟩
                      (.split false ⟨.hat, 1, 5, true⟩
                        (.split false ⟨.hat, 2, 5, true⟩
                          (.terminal .reducible)
                          (.split false ⟨.hat, 0, 5, true⟩
                            (.terminal .reducible)
                            (.split false ⟨.spoke, 5, 6, true⟩
                              (.split false ⟨.hat, 4, 6, false⟩
                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -2⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, -2⟩]))
                                (.split false ⟨.hat, 4, 5, true⟩
                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -3⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, -2⟩]))
                                  (.split false ⟨.fan1, 3, 5, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.hat, 5, 5, false⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -2⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, -2⟩]))
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -2⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, -3⟩]))))))
                              (.split false ⟨.hat, 4, 6, false⟩
                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -2⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, some 6, 1⟩]))
                                (.split false ⟨.fan1, 3, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.hat, 4, 5, false⟩
                                    (.split false ⟨.spoke, 5, 7, false⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨3, some 6, 2⟩]))
                                      (.split false ⟨.hat, 5, 5, false⟩
                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -2⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, some 6, 1⟩]))
                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, -2⟩]))))
                                    (.split false ⟨.spoke, 5, 7, false⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩]))
                                      (.split false ⟨.hat, 5, 5, false⟩
                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -3⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 1⟩, ⟨6, none, -1⟩]))
                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 1⟩, ⟨6, none, -2⟩]))))))))))
                        (.split false ⟨.spoke, 5, 6, false⟩
                          (.split false ⟨.hat, 4, 5, false⟩
                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, some 6, 2⟩]))
                            (.split false ⟨.fan1, 3, 5, true⟩
                              (.terminal .reducible)
                              (.split false ⟨.spoke, 5, 7, true⟩
                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, some 6, 1⟩]))
                                (.split false ⟨.spoke, 6, 7, false⟩
                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩]))
                                  (.split false ⟨.hat, 1, 6, true⟩
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩]))
                                    (.split false ⟨.hat, 5, 5, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -3⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩]))
                                      (.split false ⟨.hat, 6, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                        (.split false ⟨.hat, 6, 5, true⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                          (.split false ⟨.hat, 0, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩]))
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, -1⟩, ⟨6, none, 2⟩])))))))))))
                          (.split false ⟨.hat, 4, 5, false⟩
                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -2⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, -2⟩]))
                            (.split false ⟨.fan1, 3, 5, true⟩
                              (.terminal .reducible)
                              (.split false ⟨.hat, 5, 5, false⟩
                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -3⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, -2⟩]))
                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -3⟩, ⟨3, none, 3⟩, ⟨4, none, 4⟩, ⟨5, none, 3⟩, ⟨6, none, -3⟩])))))))
                      (.split false ⟨.spoke, 5, 6, true⟩
                        (.similar 0 ⟨true, 5⟩)
                        (.split true ⟨.spoke, 3, 7, false⟩
                          (.split false ⟨.spoke, 5, 7, false⟩
                            (.split false ⟨.spoke, 2, 7, false⟩
                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨2, none, -1⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨1, some 6, 5⟩]))
                              (.split false ⟨.spoke, 6, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩, ⟨1, some 2, 5⟩]))
                                (.split false ⟨.hat, 1, 6, true⟩
                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨2, some 6, 0⟩]))
                                  (.split false ⟨.hat, 2, 5, false⟩
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩]))
                                    (.split false ⟨.hat, 3, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, -1⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩]))
                                      (.split false ⟨.hat, 3, 5, true⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, -1⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩]))
                                        (.split false ⟨.hat, 6, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, -1⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                          (.split false ⟨.hat, 6, 5, true⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, -1⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                            (.split false ⟨.hat, 0, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, -1⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩]))
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, -1⟩, ⟨4, none, 2⟩, ⟨5, none, -1⟩, ⟨6, none, 2⟩])))))))))))
                            (.split false ⟨.spoke, 2, 7, false⟩
                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, some 6, 1⟩]))
                              (.split false ⟨.hat, 2, 6, false⟩
                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, some 6, 1⟩]))
                                (.split false ⟨.hat, 2, 5, true⟩
                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, -1⟩, ⟨4, none, 2⟩, ⟨5, some 6, 1⟩]))
                                  (.split false ⟨.hat, 1, 5, false⟩
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, some 6, 1⟩]))
                                    (.split false ⟨.hat, 0, 5, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.hat, 5, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨2, some 6, 0⟩]))
                                        (.split false ⟨.hat, 5, 5, true⟩
                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨6, none, -2⟩, ⟨2, some 5, 2⟩]))
                                          (.split false ⟨.spoke, 6, 7, false⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨6, none, -1⟩, ⟨2, some 5, 1⟩]))
                                            (.split false ⟨.hat, 4, 5, true⟩
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨6, none, -1⟩, ⟨2, some 5, 1⟩]))
                                              (.split false ⟨.hat, 6, 5, true⟩
                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩]))
                                                (.split false ⟨.hat, 0, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨6, none, -1⟩, ⟨2, some 5, 1⟩]))
                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨2, some 6, 0⟩]))))))))))))))
                          (.split false ⟨.spoke, 5, 7, false⟩
                            (.similar 0 ⟨true, 5⟩)
                            (.split false ⟨.hat, 1, 5, false⟩
                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨4, none, 2⟩, ⟨2, some 3, 1⟩, ⟨5, some 6, 1⟩]))
                              (.split false ⟨.hat, 2, 5, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.hat, 0, 5, true⟩
                                  (.terminal .reducible)
                                  (.split true ⟨.hat, 4, 5, true⟩
                                    (.split false ⟨.hat, 5, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨3, some 6, 2⟩]))
                                      (.split false ⟨.hat, 5, 5, true⟩
                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, -2⟩]))
                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, -1⟩]))))
                                    (.split false ⟨.hat, 5, 5, true⟩
                                      (.similar 0 ⟨true, 5⟩)
                                      (.split true ⟨.hat, 3, 5, true⟩
                                        (.split false ⟨.spoke, 2, 7, true⟩
                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, some 6, 1⟩]))
                                          (.split false ⟨.spoke, 6, 7, false⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, -1⟩]))
                                            (.split false ⟨.hat, 4, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, some 6, 1⟩]))
                                              (.split false ⟨.hat, 5, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨3, some 6, 1⟩]))
                                                (.split false ⟨.hat, 6, 5, true⟩
                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩]))
                                                  (.split false ⟨.hat, 0, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, -1⟩]))
                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨3, some 6, 1⟩]))))))))
                                        (.split false ⟨.hat, 6, 5, true⟩
                                          (.similar 0 ⟨true, 5⟩)
                                          (.split false ⟨.fan1, 3, 5, true⟩
                                            (.split false ⟨.spoke, 2, 7, false⟩
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, some 6, 1⟩]))
                                              (.split false ⟨.spoke, 6, 7, false⟩
                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨6, none, -1⟩, ⟨2, some 5, 1⟩]))
                                                (.split false ⟨.hat, 2, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, some 6, 1⟩]))
                                                  (.split false ⟨.hat, 3, 6, true⟩
                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, some 6, 1⟩]))
                                                    (.split false ⟨.hat, 5, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨2, some 6, 0⟩]))
                                                      (.split false ⟨.hat, 0, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨6, none, -1⟩, ⟨2, some 5, 1⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨2, some 6, 0⟩]))))))))
                                            (.split false ⟨.fan2, 5, 5, true⟩
                                              (.split false ⟨.spoke, 2, 7, false⟩
                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨3, some 6, 1⟩]))
                                                (.split false ⟨.spoke, 6, 7, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩, ⟨2, some 3, 1⟩]))
                                                  (.split false ⟨.hat, 2, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨3, some 6, 1⟩]))
                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨2, some 6, 0⟩])))))
                                              (.split true ⟨.spoke, 2, 7, false⟩
                                                (.split false ⟨.spoke, 6, 7, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, -1⟩]))
                                                  (.split false ⟨.hat, 4, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, some 6, 1⟩]))
                                                    (.split false ⟨.hat, 5, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨3, some 6, 1⟩]))
                                                      (.split false ⟨.hat, 0, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, -1⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨3, some 6, 1⟩]))))))
                                                (.split false ⟨.spoke, 6, 7, false⟩
                                                  (.similar 0 ⟨true, 5⟩)
                                                  (.split true ⟨.hat, 2, 6, false⟩
                                                    (.split false ⟨.hat, 4, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, some 6, 1⟩]))
                                                      (.split false ⟨.hat, 5, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨3, some 6, 1⟩]))
                                                        (.split false ⟨.hat, 0, 6, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, -1⟩]))
                                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨3, some 6, 1⟩])))))
                                                    (.split false ⟨.hat, 0, 6, false⟩
                                                      (.similar 0 ⟨true, 5⟩)
                                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨2, some 6, 0⟩])))))))))))))))))))
                    (.split false ⟨.spoke, 5, 6, true⟩
                      (.terminal .reducible)
                      (.split false ⟨.spoke, 3, 6, false⟩
                        (.split false ⟨.spoke, 3, 7, false⟩
                          (.split false ⟨.spoke, 2, 7, false⟩
                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, -2⟩, ⟨6, none, 3⟩]))
                            (.split false ⟨.hat, 1, 5, false⟩
                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, -2⟩, ⟨2, some 6, 3⟩]))
                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, -2⟩, ⟨2, some 6, 2⟩]))))
                          (.split false ⟨.hat, 1, 5, false⟩
                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, -2⟩, ⟨6, none, 2⟩, ⟨2, some 3, 1⟩]))
                            (.split false ⟨.hat, 2, 5, true⟩
                              (.terminal .reducible)
                              (.split false ⟨.hat, 0, 5, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.hat, 4, 6, false⟩
                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, -2⟩, ⟨2, some 6, 2⟩]))
                                  (.split false ⟨.hat, 4, 5, true⟩
                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -2⟩, ⟨4, none, 2⟩, ⟨5, none, -2⟩, ⟨3, some 6, 4⟩]))
                                    (.split false ⟨.spoke, 2, 7, false⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨4, none, 2⟩, ⟨5, none, -2⟩, ⟨3, some 6, 3⟩]))
                                      (.split false ⟨.hat, 2, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨4, none, 2⟩, ⟨5, none, -2⟩, ⟨3, some 6, 3⟩]))
                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, -2⟩, ⟨2, some 6, 2⟩]))))))))))
                        (.split false ⟨.hat, 4, 5, false⟩
                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -2⟩, ⟨4, none, 2⟩, ⟨5, none, -2⟩, ⟨3, some 6, 4⟩]))
                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨2, none, -3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, -2⟩, ⟨1, some 6, 5⟩]))))))
                  (.split false ⟨.spoke, 6, 6, false⟩
                    (.similar 0 ⟨true, 5⟩)
                    (.split false ⟨.spoke, 3, 6, true⟩
                      (.terminal .reducible)
                      (.split false ⟨.spoke, 5, 6, true⟩
                        (.terminal .reducible)
                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, -2⟩, ⟨4, none, 2⟩, ⟨5, none, -2⟩, ⟨2, some 6, 4⟩]))))))
                (.split true ⟨.spoke, 2, 6, true⟩
                  (.split true ⟨.spoke, 3, 6, false⟩
                    (.split false ⟨.spoke, 6, 6, false⟩
                      (.split false ⟨.spoke, 4, 7, false⟩
                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨2, some 6, 3⟩]))
                        (.split false ⟨.spoke, 5, 7, false⟩
                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨2, some 6, 3⟩]))
                          (.split false ⟨.hat, 5, 6, false⟩
                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨2, some 6, 3⟩]))
                            (.split false ⟨.hat, 1, 5, false⟩
                              (.split false ⟨.spoke, 3, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, -2⟩, ⟨4, some 5, 3⟩, ⟨4, some 6, 2⟩, ⟨5, some 6, 2⟩]))
                                (.split false ⟨.spoke, 4, 6, false⟩
                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, -1⟩, ⟨5, none, 0⟩, ⟨4, some 6, 2⟩]))
                                  (.split false ⟨.hat, 4, 5, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.spoke, 5, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, some 6, 2⟩]))
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, some 4, 0⟩, ⟨5, some 6, 1⟩]))))))
                              (.split false ⟨.hat, 2, 5, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.hat, 0, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.spoke, 4, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨5, none, 0⟩, ⟨2, some 6, 2⟩, ⟨3, some 4, 0⟩]))
                                    (.split false ⟨.spoke, 5, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨4, none, 0⟩, ⟨2, some 6, 2⟩, ⟨3, some 5, 0⟩]))
                                      (.split false ⟨.hat, 5, 5, true⟩
                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 1⟩, ⟨3, none, -1⟩, ⟨6, none, -1⟩, ⟨4, some 5, 3⟩]))
                                        (.split false ⟨.spoke, 6, 7, true⟩
                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, some 6, 2⟩, ⟨3, some 4, -1⟩, ⟨3, some 5, 0⟩, ⟨4, some 5, 2⟩]))
                                          (.split false ⟨.spoke, 3, 7, false⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨6, none, -1⟩, ⟨4, some 5, 2⟩]))
                                            (.split false ⟨.hat, 4, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.hat, 2, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 1⟩, ⟨3, none, -1⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, -1⟩]))
                                                (.split false ⟨.fan1, 2, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.hat, 3, 5, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨6, none, -1⟩, ⟨4, some 5, 2⟩]))
                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨6, none, -1⟩, ⟨4, some 5, 1⟩])))))))))))))))))
                      (.split false ⟨.spoke, 5, 6, false⟩
                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, -1⟩, ⟨2, some 6, 4⟩]))
                        (.split false ⟨.hat, 6, 5, true⟩
                          (.terminal .reducible)
                          (.split false ⟨.spoke, 4, 7, false⟩
                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, -1⟩, ⟨4, none, -1⟩, ⟨5, none, 0⟩, ⟨2, some 6, 4⟩]))
                            (.split false ⟨.spoke, 4, 6, true⟩
                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, -2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨2, some 6, 4⟩]))
                              (.split false ⟨.spoke, 3, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, -2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨2, some 6, 4⟩]))
                                (.split false ⟨.hat, 3, 5, false⟩
                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, -2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨2, some 6, 4⟩]))
                                  (.split false ⟨.fan1, 3, 5, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.hat, 5, 5, false⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, -1⟩, ⟨4, none, -1⟩, ⟨5, none, 0⟩, ⟨2, some 6, 4⟩]))
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, -1⟩, ⟨4, none, -1⟩, ⟨5, none, 0⟩, ⟨2, some 6, 4⟩])))))))))))
                    (.split false ⟨.hat, 3, 5, true⟩
                      (.terminal .reducible)
                      (.split false ⟨.spoke, 4, 6, false⟩
                        (.split false ⟨.spoke, 6, 7, false⟩
                          (.split false ⟨.spoke, 4, 7, false⟩
                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, -1⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩]))
                            (.split false ⟨.spoke, 5, 6, false⟩
                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩]))
                              (.split false ⟨.hat, 5, 5, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.hat, 1, 5, false⟩
                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩]))
                                  (.split false ⟨.hat, 2, 5, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.hat, 0, 5, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.hat, 2, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩]))
                                        (.split false ⟨.fan1, 2, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.hat, 4, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩]))
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩])))))))))))
                          (.split false ⟨.spoke, 4, 7, false⟩
                            (.split false ⟨.spoke, 6, 6, false⟩
                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, -1⟩, ⟨5, none, 0⟩, ⟨2, some 6, 3⟩]))
                              (.split false ⟨.spoke, 5, 6, false⟩
                                (.similar 0 ⟨true, 5⟩)
                                (.split false ⟨.hat, 6, 5, true⟩
                                  (.terminal .reducible)
                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, -2⟩, ⟨5, none, 0⟩, ⟨2, some 6, 4⟩])))))
                            (.split true ⟨.hat, 4, 5, false⟩
                              (.split false ⟨.spoke, 5, 7, false⟩
                                (.split false ⟨.spoke, 6, 6, true⟩
                                  (.similar 0 ⟨true, 5⟩)
                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, -1⟩, ⟨5, none, 0⟩, ⟨2, some 6, 3⟩])))
                                (.split false ⟨.spoke, 6, 6, false⟩
                                  (.split false ⟨.spoke, 5, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, -1⟩, ⟨5, none, 0⟩, ⟨2, some 6, 3⟩]))
                                    (.split false ⟨.hat, 5, 5, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.hat, 1, 5, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨2, some 6, 2⟩])))))
                                  (.split false ⟨.spoke, 5, 6, false⟩
                                    (.similar 0 ⟨true, 5⟩)
                                    (.split false ⟨.hat, 5, 5, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.hat, 6, 5, true⟩
                                        (.terminal .reducible)
                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, -2⟩, ⟨5, none, 0⟩, ⟨2, some 6, 4⟩])))))))
                              (.split false ⟨.fan1, 4, 5, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.spoke, 5, 7, false⟩
                                  (.split false ⟨.spoke, 6, 6, true⟩
                                    (.similar 1 ⟨true, 5⟩)
                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, -1⟩, ⟨5, none, 0⟩, ⟨2, some 6, 3⟩])))
                                  (.split false ⟨.spoke, 6, 6, false⟩
                                    (.split false ⟨.spoke, 5, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, -1⟩, ⟨5, none, 0⟩, ⟨2, some 6, 3⟩]))
                                      (.split false ⟨.hat, 5, 5, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.hat, 1, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩])))))
                                    (.split false ⟨.spoke, 5, 6, false⟩
                                      (.similar 1 ⟨true, 5⟩)
                                      (.split false ⟨.hat, 5, 5, false⟩
                                        (.similar 0 ⟨true, 5⟩)
                                        (.terminal .reducible)))))))))
                        (.split false ⟨.hat, 4, 5, true⟩
                          (.terminal .reducible)
                          (.split false ⟨.spoke, 6, 6, false⟩
                            (.split false ⟨.hat, 2, 5, true⟩
                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, some 6, 1⟩]))
                              (.split false ⟨.hat, 1, 5, false⟩
                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, some 6, 2⟩]))
                                (.split false ⟨.hat, 0, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.spoke, 5, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨2, some 6, 2⟩]))
                                    (.split false ⟨.spoke, 5, 6, true⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨2, some 6, 2⟩]))
                                      (.split false ⟨.hat, 2, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, some 6, 1⟩]))
                                        (.split false ⟨.fan1, 2, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.hat, 5, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩]))
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩]))))))))))
                            (.split false ⟨.spoke, 5, 6, false⟩
                              (.similar 0 ⟨true, 5⟩)
                              (.terminal .reducible)))))))
                  (.split false ⟨.spoke, 6, 6, true⟩
                    (.similar 0 ⟨true, 5⟩)
                    (.split false ⟨.spoke, 4, 7, false⟩
                      (.terminal (.hubcap [⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨0, some 2, 5⟩, ⟨1, some 6, 5⟩]))
                      (.split false ⟨.hat, 1, 5, false⟩
                        (.split true ⟨.spoke, 2, 7, false⟩
                          (.split false ⟨.spoke, 3, 6, false⟩
                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -1⟩, ⟨3, none, 2⟩, ⟨4, some 5, 3⟩, ⟨4, some 6, 2⟩, ⟨5, some 6, 2⟩]))
                            (.split false ⟨.spoke, 4, 6, false⟩
                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -1⟩, ⟨3, none, 0⟩, ⟨5, none, 0⟩, ⟨4, some 6, 4⟩]))
                              (.split false ⟨.spoke, 5, 6, false⟩
                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -1⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 2⟩]))
                                (.split false ⟨.spoke, 6, 7, false⟩
                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -1⟩, ⟨3, none, 2⟩, ⟨6, none, -1⟩, ⟨4, some 5, 4⟩]))
                                  (.split false ⟨.hat, 4, 5, false⟩
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -1⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 1⟩]))
                                    (.split false ⟨.hat, 0, 5, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.hat, 5, 5, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -1⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 2⟩]))
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -1⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨5, none, 1⟩, ⟨6, none, -1⟩])))))))))
                          (.split false ⟨.spoke, 6, 7, false⟩
                            (.similar 0 ⟨true, 5⟩)
                            (.split true ⟨.hat, 2, 5, true⟩
                              (.split false ⟨.hat, 1, 6, true⟩
                                (.terminal .reducible)
                                (.split true ⟨.hat, 3, 5, true⟩
                                  (.split false ⟨.spoke, 3, 6, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.spoke, 3, 7, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, some 5, 3⟩, ⟨4, some 6, 2⟩, ⟨5, some 6, 2⟩]))
                                      (.split false ⟨.spoke, 4, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨5, none, 0⟩, ⟨4, some 6, 2⟩]))
                                        (.split false ⟨.hat, 4, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.spoke, 5, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨4, none, 0⟩, ⟨2, some 3, 2⟩, ⟨5, some 6, 2⟩]))
                                            (.split false ⟨.hat, 5, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨4, none, 1⟩, ⟨2, some 3, 2⟩, ⟨5, some 6, 1⟩]))
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, some 3, 2⟩, ⟨4, some 5, 3⟩, ⟨4, some 6, 1⟩, ⟨5, some 6, 1⟩]))))))))
                                  (.split false ⟨.hat, 6, 5, true⟩
                                    (.split false ⟨.hat, 0, 5, true⟩
                                      (.similar 0 ⟨true, 5⟩)
                                      (.split false ⟨.spoke, 3, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨6, none, 1⟩, ⟨2, some 3, 2⟩, ⟨4, some 5, 1⟩]))
                                        (.split false ⟨.spoke, 4, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                          (.split false ⟨.spoke, 5, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, some 6, 1⟩]))
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨4, none, 1⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩, ⟨2, some 3, 1⟩]))))))
                                    (.split false ⟨.hat, 0, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨6, none, -1⟩, ⟨2, some 3, 2⟩, ⟨4, some 5, 3⟩]))
                                      (.split false ⟨.hat, 0, 5, false⟩
                                        (.split false ⟨.spoke, 4, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨3, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩, ⟨2, some 4, 4⟩]))
                                          (.split false ⟨.spoke, 5, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨6, none, 0⟩, ⟨2, some 3, 2⟩, ⟨4, some 5, 2⟩]))
                                            (.split false ⟨.spoke, 3, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, some 3, 2⟩, ⟨4, some 5, 3⟩, ⟨4, some 6, 1⟩, ⟨5, some 6, 1⟩]))
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, some 6, 0⟩])))))
                                        (.split false ⟨.fan1, 2, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, some 4, 2⟩, ⟨5, some 6, 2⟩]))
                                          (.split false ⟨.fan2, 2, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.spoke, 5, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨5, some 6, 2⟩, ⟨2, some 3, 2⟩, ⟨2, some 4, 2⟩, ⟨3, some 4, 1⟩]))
                                              (.split false ⟨.spoke, 3, 7, true⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨3, none, 0⟩, ⟨2, some 4, 3⟩, ⟨5, some 6, 1⟩]))
                                                (.split false ⟨.spoke, 4, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                                  (.split false ⟨.hat, 3, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩]))
                                                    (.split false ⟨.hat, 4, 5, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨5, some 6, 1⟩]))
                                                      (.split false ⟨.hat, 5, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨6, none, 1⟩, ⟨4, some 5, 1⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨5, none, 1⟩, ⟨6, none, 0⟩])))))))))))))))
                              (.split false ⟨.hat, 0, 5, true⟩
                                (.similar 0 ⟨true, 5⟩)
                                (.split false ⟨.spoke, 3, 7, false⟩
                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, some 6, 2⟩]))
                                  (.split false ⟨.spoke, 5, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩, ⟨3, some 4, 3⟩]))
                                    (.split false ⟨.spoke, 4, 6, false⟩
                                      (.split false ⟨.spoke, 3, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                        (.split false ⟨.spoke, 5, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                          (.split false ⟨.hat, 3, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨5, none, 0⟩, ⟨4, some 6, 4⟩]))
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨5, none, 0⟩, ⟨4, some 6, 3⟩])))))
                                      (.split false ⟨.hat, 4, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨5, none, 2⟩, ⟨4, some 6, 1⟩]))
                                        (.split false ⟨.hat, 5, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨3, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩, ⟨2, some 4, 1⟩]))
                                          (.split true ⟨.hat, 3, 5, true⟩
                                            (.split false ⟨.hat, 4, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.spoke, 3, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨5, none, 2⟩, ⟨2, some 3, 1⟩, ⟨4, some 6, 1⟩]))
                                                (.split false ⟨.fan1, 3, 6, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.fan1, 4, 5, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.fan2, 2, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.spoke, 5, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, some 6, 2⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨5, none, 1⟩, ⟨4, some 6, 1⟩]))))))))
                                            (.split false ⟨.hat, 6, 5, true⟩
                                              (.similar 0 ⟨true, 5⟩)
                                              (.split false ⟨.spoke, 5, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨5, none, 2⟩, ⟨2, some 6, -1⟩, ⟨3, some 4, 3⟩]))
                                                (.split false ⟨.spoke, 3, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨3, none, 2⟩, ⟨2, some 4, 1⟩, ⟨5, some 6, 1⟩]))
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, some 3, 1⟩, ⟨4, some 5, 4⟩, ⟨4, some 6, 2⟩, ⟨5, some 6, 1⟩])))))))))))))))
                        (.split false ⟨.hat, 2, 5, true⟩
                          (.terminal .reducible)
                          (.split false ⟨.hat, 0, 5, true⟩
                            (.terminal .reducible)
                            (.split true ⟨.spoke, 3, 6, false⟩
                              (.split false ⟨.spoke, 4, 6, false⟩
                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨2, some 6, 0⟩]))
                                (.split false ⟨.spoke, 5, 6, false⟩
                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨4, none, 0⟩, ⟨2, some 3, 1⟩, ⟨5, some 6, 1⟩]))
                                  (.split false ⟨.hat, 5, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩, ⟨2, some 3, 1⟩]))
                                    (.split false ⟨.hat, 5, 5, true⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨3, none, 1⟩, ⟨6, none, -1⟩, ⟨4, some 5, 3⟩]))
                                      (.split false ⟨.spoke, 6, 7, false⟩
                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨6, none, -1⟩, ⟨2, some 3, 1⟩, ⟨4, some 5, 2⟩]))
                                        (.split false ⟨.hat, 6, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.spoke, 3, 7, false⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, 0⟩, ⟨2, some 6, 0⟩, ⟨4, some 5, 2⟩]))
                                            (.split false ⟨.hat, 4, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, 1⟩, ⟨2, some 6, 0⟩, ⟨4, some 5, 1⟩]))
                                              (.split false ⟨.hat, 0, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨3, none, 2⟩, ⟨6, none, -1⟩, ⟨4, some 5, 2⟩]))
                                                (.split false ⟨.fan2, 3, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.hat, 6, 6, true⟩
                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨3, none, 1⟩, ⟨4, some 5, 2⟩, ⟨4, some 6, 1⟩, ⟨5, some 6, 2⟩]))
                                                    (.split false ⟨.fan1, 4, 5, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨3, none, 1⟩, ⟨6, none, 1⟩, ⟨4, some 5, 1⟩]))
                                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, -1⟩]))))))))))))))
                              (.split false ⟨.spoke, 5, 6, false⟩
                                (.similar 0 ⟨true, 5⟩)
                                (.split true ⟨.hat, 3, 5, true⟩
                                  (.split false ⟨.spoke, 2, 7, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.spoke, 4, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨3, none, 0⟩, ⟨5, none, 0⟩, ⟨4, some 6, 3⟩]))
                                      (.split true ⟨.spoke, 6, 7, false⟩
                                        (.split false ⟨.hat, 4, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨6, none, -1⟩, ⟨3, some 4, 3⟩, ⟨3, some 5, 2⟩, ⟨4, some 5, 4⟩]))
                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨6, none, -1⟩, ⟨3, some 4, 4⟩, ⟨3, some 5, 2⟩, ⟨4, some 5, 3⟩])))
                                        (.split false ⟨.hat, 6, 5, true⟩
                                          (.similar 0 ⟨true, 5⟩)
                                          (.split false ⟨.hat, 4, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, some 6, 1⟩]))
                                            (.split false ⟨.hat, 4, 5, true⟩
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨3, none, 2⟩, ⟨6, none, -1⟩, ⟨4, some 5, 2⟩]))
                                              (.split false ⟨.hat, 5, 5, false⟩
                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨3, some 4, 2⟩, ⟨5, some 6, 1⟩]))
                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨5, none, 1⟩, ⟨6, none, -1⟩, ⟨3, some 4, 3⟩])))))))))
                                  (.split false ⟨.hat, 6, 5, true⟩
                                    (.similar 0 ⟨true, 5⟩)
                                    (.split false ⟨.spoke, 4, 6, false⟩
                                      (.split false ⟨.spoke, 2, 7, false⟩
                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨3, none, 0⟩, ⟨5, none, 0⟩, ⟨4, some 6, 3⟩]))
                                        (.split false ⟨.spoke, 6, 7, false⟩
                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩, ⟨2, some 4, 3⟩]))
                                          (.split false ⟨.hat, 2, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨3, none, 0⟩, ⟨5, none, 0⟩, ⟨4, some 6, 3⟩]))
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨2, some 6, 0⟩])))))
                                      (.split false ⟨.hat, 4, 5, true⟩
                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨5, none, 1⟩, ⟨6, none, -1⟩, ⟨3, some 4, 3⟩]))
                                        (.split false ⟨.hat, 5, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 0⟩, ⟨2, some 6, 0⟩]))
                                          (.split false ⟨.hat, 5, 5, true⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨3, none, 1⟩, ⟨6, none, -1⟩, ⟨4, some 5, 3⟩]))
                                            (.split false ⟨.spoke, 6, 7, false⟩
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨6, none, -1⟩, ⟨2, some 3, 1⟩, ⟨4, some 5, 2⟩]))
                                              (.split false ⟨.spoke, 2, 7, false⟩
                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨3, some 4, 2⟩, ⟨5, some 6, 1⟩]))
                                                (.split false ⟨.hat, 2, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨3, some 4, 2⟩, ⟨5, some 6, 1⟩]))
                                                  (.split false ⟨.hat, 4, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨5, none, 1⟩, ⟨2, some 6, 0⟩]))
                                                    (.split false ⟨.hat, 0, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨6, none, -1⟩, ⟨2, some 3, 1⟩, ⟨4, some 5, 2⟩]))
                                                      (.split false ⟨.fan1, 2, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, -1⟩, ⟨3, some 4, 2⟩, ⟨5, some 6, 1⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩])))))))))))))))))))))))))))
      (.split false ⟨.spoke, 6, 5, true⟩
        (.similar 0 ⟨false, 6⟩)
        (.split true ⟨.spoke, 2, 5, true⟩
          (.split false ⟨.spoke, 3, 5, true⟩
            (.similar 0 ⟨false, 2⟩)
            (.split true ⟨.spoke, 4, 5, true⟩
              (.split false ⟨.spoke, 5, 5, true⟩
                (.similar 0 ⟨false, 4⟩)
                (.split true ⟨.spoke, 5, 6, false⟩
                  (.split false ⟨.spoke, 6, 6, false⟩
                    (.split true ⟨.spoke, 1, 6, true⟩
                      (.split false ⟨.spoke, 3, 6, true⟩
                        (.terminal .reducible)
                        (.split false ⟨.hat, 1, 5, false⟩
                          (.split false ⟨.spoke, 5, 7, false⟩
                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩, ⟨2, some 3, 2⟩]))
                            (.split false ⟨.spoke, 6, 7, false⟩
                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨4, none, 2⟩, ⟨6, none, -1⟩, ⟨3, some 5, 0⟩]))
                              (.split false ⟨.hat, 6, 5, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.hat, 2, 5, false⟩
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 0⟩]))
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 0⟩]))))))
                          (.split false ⟨.fan1, 1, 5, true⟩
                            (.terminal .reducible)
                            (.split false ⟨.hat, 2, 5, false⟩
                              (.split false ⟨.spoke, 3, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, -1⟩, ⟨4, none, 2⟩, ⟨5, some 6, 0⟩]))
                                (.split false ⟨.hat, 3, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.hat, 4, 5, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.spoke, 6, 7, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, -1⟩, ⟨3, some 5, 0⟩]))
                                      (.split false ⟨.hat, 4, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, -1⟩, ⟨4, none, 2⟩, ⟨5, some 6, 0⟩]))
                                        (.split false ⟨.hat, 5, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.hat, 0, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩]))
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, -1⟩, ⟨6, none, -1⟩])))))))))
                              (.split false ⟨.fan1, 1, 6, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.spoke, 3, 7, false⟩
                                  (.split false ⟨.spoke, 3, 8, false⟩
                                    (.split false ⟨.spoke, 5, 7, false⟩
                                      (.split false ⟨.spoke, 6, 7, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩]))
                                        (.split false ⟨.hat, 3, 5, true⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩]))
                                          (.split false ⟨.hat, 0, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩]))
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, 2⟩, ⟨5, none, -1⟩, ⟨6, none, -1⟩])))))
                                      (.split false ⟨.hat, 5, 5, true⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, -2⟩]))
                                        (.split false ⟨.spoke, 6, 7, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩]))
                                          (.split false ⟨.hat, 6, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.hat, 3, 5, true⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩]))
                                              (.split false ⟨.hat, 0, 5, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩]))
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, 2⟩, ⟨5, none, -1⟩, ⟨6, none, -1⟩]))))))))
                                    (.split false ⟨.spoke, 5, 7, false⟩
                                      (.split false ⟨.spoke, 6, 7, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩]))
                                        (.split false ⟨.hat, 3, 5, true⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩]))
                                          (.split false ⟨.hat, 0, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩]))
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, 2⟩, ⟨5, none, -1⟩, ⟨6, none, -1⟩])))))
                                      (.split false ⟨.hat, 5, 5, true⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, -2⟩]))
                                        (.split false ⟨.spoke, 6, 7, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩]))
                                          (.split false ⟨.hat, 6, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.hat, 3, 5, true⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩]))
                                              (.split false ⟨.hat, 0, 5, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩]))
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, 2⟩, ⟨5, none, -1⟩, ⟨6, none, -1⟩])))))))))
                                  (.split false ⟨.hat, 3, 6, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.hat, 4, 5, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.hat, 0, 5, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, -1⟩]))
                                        (.split false ⟨.spoke, 6, 7, true⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, 2⟩, ⟨5, none, -1⟩, ⟨6, none, -1⟩]))
                                          (.split false ⟨.spoke, 5, 7, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩]))
                                            (.split false ⟨.hat, 4, 6, true⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩]))
                                              (.split false ⟨.hat, 5, 5, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩]))
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, -2⟩])))))))))))))))
                      (.split false ⟨.spoke, 3, 6, true⟩
                        (.similar 0 ⟨true, 2⟩)
                        (.split true ⟨.spoke, 1, 7, false⟩
                          (.split false ⟨.spoke, 3, 8, false⟩
                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, some 6, 2⟩]))
                            (.split false ⟨.spoke, 3, 7, false⟩
                              (.split false ⟨.spoke, 1, 8, false⟩
                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, some 6, 2⟩]))
                                (.split false ⟨.hat, 1, 6, false⟩
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨1, some 3, 2⟩, ⟨5, some 6, 2⟩]))
                                  (.split false ⟨.hat, 4, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨1, some 3, 2⟩, ⟨5, some 6, 2⟩]))
                                    (.split true ⟨.spoke, 5, 7, false⟩
                                      (.split false ⟨.spoke, 6, 7, false⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩]))
                                        (.split false ⟨.hat, 1, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨1, some 6, 2⟩]))
                                          (.split false ⟨.hat, 2, 5, true⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                            (.split false ⟨.hat, 3, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩]))
                                              (.split false ⟨.hat, 4, 5, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩]))
                                                (.split false ⟨.hat, 5, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩]))
                                                  (.split false ⟨.hat, 0, 5, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, -1⟩, ⟨6, none, 2⟩])))))))))
                                      (.split false ⟨.spoke, 6, 7, false⟩
                                        (.similar 0 ⟨true, 2⟩)
                                        (.split false ⟨.hat, 2, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨1, some 3, 2⟩, ⟨5, some 6, 2⟩]))
                                          (.split false ⟨.hat, 3, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨1, some 3, 2⟩, ⟨5, some 6, 2⟩]))
                                            (.split false ⟨.hat, 5, 5, true⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨1, some 3, 3⟩, ⟨5, some 6, 1⟩]))
                                              (.split false ⟨.hat, 2, 5, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, some 6, 2⟩]))
                                                (.split false ⟨.hat, 4, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩, ⟨1, some 3, 2⟩]))
                                                  (.split false ⟨.hat, 5, 6, true⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩, ⟨1, some 3, 2⟩]))
                                                    (.split false ⟨.hat, 6, 5, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩, ⟨1, some 3, 3⟩]))
                                                      (.split false ⟨.hat, 0, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩, ⟨1, some 3, 2⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩, ⟨1, some 3, 3⟩])))))))))))))))
                              (.split false ⟨.spoke, 1, 8, false⟩
                                (.split false ⟨.fan1, 3, 5, true⟩
                                  (.split false ⟨.spoke, 6, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, 0⟩, ⟨3, some 5, 4⟩]))
                                    (.split false ⟨.hat, 3, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, some 6, 2⟩]))
                                      (.split false ⟨.fan2, 3, 5, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.hat, 0, 5, true⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨3, some 5, 3⟩, ⟨3, some 6, 5⟩, ⟨5, some 6, 1⟩]))
                                          (.split false ⟨.spoke, 5, 7, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨3, some 6, 4⟩]))
                                            (.split false ⟨.hat, 3, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, 1⟩, ⟨3, some 5, 3⟩]))
                                              (.split false ⟨.hat, 4, 6, true⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨3, some 6, 4⟩]))
                                                (.split false ⟨.hat, 5, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 0⟩]))))))))))
                                  (.split false ⟨.hat, 4, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, some 6, 2⟩]))
                                    (.split false ⟨.spoke, 5, 7, false⟩
                                      (.split false ⟨.spoke, 6, 7, false⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩]))
                                        (.split false ⟨.hat, 4, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨3, some 6, 4⟩]))
                                          (.split false ⟨.hat, 0, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩]))
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, -1⟩, ⟨3, some 6, 5⟩])))))
                                      (.split false ⟨.hat, 5, 5, true⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨3, some 6, 3⟩]))
                                        (.split false ⟨.spoke, 6, 7, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, 0⟩, ⟨3, some 5, 4⟩]))
                                          (.split false ⟨.hat, 4, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨3, some 5, 3⟩, ⟨3, some 6, 4⟩, ⟨5, some 6, 2⟩]))
                                            (.split false ⟨.hat, 6, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.hat, 5, 6, true⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩]))
                                                (.split false ⟨.hat, 0, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩]))
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, -1⟩, ⟨3, some 6, 5⟩])))))))))))
                                (.split false ⟨.spoke, 5, 7, false⟩
                                  (.split false ⟨.spoke, 6, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩, ⟨1, some 3, 4⟩]))
                                    (.split false ⟨.hat, 0, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩, ⟨1, some 3, 4⟩]))
                                      (.split false ⟨.hat, 4, 5, false⟩
                                        (.split false ⟨.hat, 1, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨3, some 6, 4⟩]))
                                          (.split false ⟨.hat, 0, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩, ⟨1, some 3, 3⟩]))
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, -1⟩, ⟨1, some 3, 4⟩, ⟨1, some 6, 3⟩, ⟨3, some 6, 4⟩]))))
                                        (.split false ⟨.hat, 0, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩]))
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, -1⟩, ⟨3, some 6, 5⟩]))))))
                                  (.split false ⟨.hat, 5, 5, true⟩
                                    (.split false ⟨.hat, 1, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨3, some 5, 5⟩, ⟨3, some 6, 3⟩, ⟨5, some 6, 1⟩]))
                                      (.split false ⟨.hat, 4, 5, true⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, -1⟩]))
                                        (.split false ⟨.hat, 2, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨1, some 6, 0⟩, ⟨3, some 5, 4⟩]))
                                          (.split false ⟨.hat, 1, 5, true⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨1, some 6, 1⟩, ⟨3, some 5, 3⟩]))
                                            (.split false ⟨.spoke, 6, 7, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, -1⟩, ⟨3, some 5, 4⟩]))
                                              (.split false ⟨.hat, 3, 5, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, some 6, 1⟩]))
                                                (.split false ⟨.fan1, 5, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.fan3, 1, 5, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.hat, 4, 6, true⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 0⟩]))
                                                      (.split false ⟨.hat, 0, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 0⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩]))))))))))))
                                    (.split false ⟨.hat, 3, 5, false⟩
                                      (.split false ⟨.spoke, 6, 7, false⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 0⟩, ⟨1, some 3, 3⟩]))
                                        (.split false ⟨.hat, 0, 5, true⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨1, some 3, 3⟩, ⟨5, some 6, 1⟩]))
                                          (.split false ⟨.hat, 1, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, 1⟩, ⟨3, some 5, 3⟩]))
                                            (.split false ⟨.hat, 2, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, 1⟩, ⟨3, some 5, 3⟩]))
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩]))))))
                                      (.split false ⟨.spoke, 6, 7, false⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩, ⟨1, some 3, 4⟩]))
                                        (.split false ⟨.hat, 0, 5, true⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, -1⟩, ⟨6, none, 1⟩, ⟨1, some 3, 4⟩]))
                                          (.split false ⟨.hat, 1, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨3, some 6, 4⟩]))
                                            (.split false ⟨.hat, 2, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨3, some 6, 4⟩]))
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))))))))))))
                          (.split false ⟨.spoke, 3, 7, false⟩
                            (.similar 0 ⟨true, 2⟩)
                            (.split true ⟨.spoke, 5, 7, false⟩
                              (.split false ⟨.spoke, 6, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩, ⟨1, some 3, 4⟩]))
                                (.split false ⟨.hat, 0, 6, false⟩
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩, ⟨1, some 3, 4⟩]))
                                  (.split false ⟨.hat, 0, 5, false⟩
                                    (.split false ⟨.hat, 1, 5, true⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩, ⟨1, some 3, 4⟩]))
                                      (.split false ⟨.hat, 2, 5, true⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩, ⟨1, some 3, 4⟩]))
                                        (.split false ⟨.hat, 2, 6, true⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨3, some 6, 3⟩]))
                                          (.split false ⟨.hat, 1, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨3, some 6, 4⟩]))
                                            (.split false ⟨.hat, 3, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨3, some 6, 3⟩]))
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨3, some 6, 4⟩])))))))
                                    (.split false ⟨.hat, 1, 6, true⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, -1⟩, ⟨6, none, 1⟩, ⟨1, some 3, 4⟩]))
                                      (.split false ⟨.hat, 2, 5, false⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, -1⟩, ⟨1, some 3, 4⟩, ⟨1, some 6, 2⟩, ⟨3, some 6, 5⟩]))
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, -1⟩, ⟨6, none, 1⟩, ⟨1, some 3, 4⟩])))))))
                              (.split false ⟨.spoke, 6, 7, false⟩
                                (.similar 0 ⟨true, 2⟩)
                                (.split true ⟨.hat, 5, 5, true⟩
                                  (.split false ⟨.hat, 1, 5, true⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨6, none, -1⟩, ⟨1, some 5, 5⟩]))
                                    (.split false ⟨.hat, 4, 5, true⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, -1⟩, ⟨1, some 3, 4⟩]))
                                      (.split false ⟨.hat, 0, 5, true⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩, ⟨1, some 3, 4⟩]))
                                        (.split false ⟨.hat, 2, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨1, some 3, 3⟩, ⟨5, some 6, 1⟩]))
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, -1⟩, ⟨1, some 3, 4⟩]))))))
                                  (.split false ⟨.hat, 0, 5, true⟩
                                    (.similar 0 ⟨true, 2⟩)
                                    (.split false ⟨.hat, 1, 5, true⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩, ⟨1, some 3, 4⟩]))
                                      (.split false ⟨.hat, 4, 5, true⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩, ⟨1, some 3, 4⟩]))
                                        (.split true ⟨.hat, 2, 5, false⟩
                                          (.split false ⟨.hat, 2, 6, true⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩]))
                                            (.split false ⟨.hat, 1, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, 1⟩, ⟨3, some 5, 3⟩]))
                                              (.split false ⟨.hat, 3, 5, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩]))
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩])))))
                                          (.split false ⟨.hat, 3, 5, false⟩
                                            (.similar 0 ⟨true, 2⟩)
                                            (.split false ⟨.fan1, 3, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.fan2, 1, 5, true⟩
                                                (.terminal .reducible)
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩]))))))))))))))))
                    (.split false ⟨.spoke, 1, 7, false⟩
                      (.split false ⟨.spoke, 3, 8, false⟩
                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨1, some 6, 3⟩]))
                        (.split false ⟨.spoke, 3, 6, true⟩
                          (.split false ⟨.hat, 0, 5, true⟩
                            (.terminal .reducible)
                            (.split false ⟨.hat, 3, 5, false⟩
                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, -1⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, -1⟩, ⟨6, none, 1⟩]))
                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, -2⟩, ⟨2, none, 3⟩, ⟨3, none, 5⟩, ⟨6, none, 1⟩, ⟨4, some 5, 1⟩]))))
                          (.split false ⟨.hat, 0, 5, true⟩
                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, -1⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, 3⟩, ⟨3, some 5, 1⟩]))
                            (.split false ⟨.spoke, 3, 7, false⟩
                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨1, some 6, 3⟩, ⟨3, some 5, 1⟩]))
                              (.split false ⟨.spoke, 5, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, -1⟩, ⟨1, some 3, 4⟩, ⟨1, some 6, 2⟩, ⟨3, some 6, 5⟩]))
                                (.split false ⟨.hat, 6, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.hat, 1, 5, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, 1⟩, ⟨3, some 5, 3⟩]))
                                    (.split false ⟨.hat, 3, 5, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨1, some 6, 2⟩, ⟨3, some 5, 2⟩]))
                                      (.split false ⟨.hat, 0, 6, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.spoke, 1, 8, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, 1⟩, ⟨3, some 5, 3⟩]))
                                          (.split false ⟨.hat, 2, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, 1⟩, ⟨3, some 5, 3⟩]))
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩])))))))))))))
                      (.split false ⟨.hat, 0, 5, true⟩
                        (.split false ⟨.spoke, 1, 6, true⟩
                          (.terminal .reducible)
                          (.split false ⟨.spoke, 3, 6, true⟩
                            (.terminal .reducible)
                            (.split false ⟨.hat, 1, 6, true⟩
                              (.terminal .reducible)
                              (.split false ⟨.hat, 2, 5, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.fan1, 6, 5, true⟩
                                  (.terminal .reducible)
                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, 2⟩, ⟨3, some 5, 1⟩])))))))
                        (.split false ⟨.spoke, 3, 6, true⟩
                          (.split false ⟨.spoke, 1, 6, true⟩
                            (.terminal .reducible)
                            (.split false ⟨.hat, 1, 5, true⟩
                              (.terminal .reducible)
                              (.split false ⟨.hat, 2, 5, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.spoke, 5, 7, true⟩
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 4⟩, ⟨6, none, 1⟩, ⟨1, some 2, 2⟩, ⟨4, some 5, 1⟩]))
                                  (.split false ⟨.hat, 2, 6, true⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, -2⟩, ⟨6, none, 1⟩]))
                                    (.split false ⟨.hat, 3, 5, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, -2⟩, ⟨6, none, 1⟩]))
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, -2⟩, ⟨2, none, 3⟩, ⟨3, none, 5⟩, ⟨4, none, 3⟩, ⟨5, none, -2⟩, ⟨6, none, 1⟩]))))))))
                          (.split false ⟨.spoke, 1, 6, false⟩
                            (.split false ⟨.spoke, 3, 8, false⟩
                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨6, none, 1⟩, ⟨1, some 5, 3⟩]))
                              (.split false ⟨.spoke, 5, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, -1⟩, ⟨6, none, 1⟩, ⟨1, some 3, 4⟩]))
                                (.split false ⟨.hat, 6, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.hat, 1, 5, true⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, 1⟩, ⟨1, some 3, 4⟩, ⟨1, some 5, 3⟩, ⟨3, some 5, 0⟩]))
                                    (.split false ⟨.spoke, 3, 7, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩, ⟨1, some 3, 3⟩]))
                                      (.split false ⟨.hat, 2, 5, true⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, -1⟩, ⟨6, none, 1⟩, ⟨1, some 3, 4⟩]))
                                        (.split false ⟨.hat, 2, 6, true⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, 1⟩, ⟨3, some 5, 2⟩]))
                                          (.split false ⟨.hat, 1, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, 1⟩, ⟨3, some 5, 3⟩]))
                                            (.split false ⟨.hat, 3, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, 1⟩, ⟨3, some 5, 2⟩]))
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, 1⟩, ⟨3, some 5, 3⟩])))))))))))
                            (.split false ⟨.spoke, 3, 7, true⟩
                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨4, none, 2⟩, ⟨6, none, 1⟩, ⟨1, some 5, 2⟩, ⟨2, some 3, 2⟩]))
                              (.split false ⟨.hat, 1, 5, false⟩
                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 2⟩, ⟨5, none, -1⟩, ⟨6, none, 1⟩]))
                                (.split false ⟨.hat, 0, 6, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.fan1, 1, 5, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.hat, 2, 5, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, -1⟩, ⟨4, none, 2⟩, ⟨5, none, -2⟩, ⟨6, none, 1⟩]))
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, 2⟩, ⟨5, none, -2⟩, ⟨6, none, 1⟩]))))))))))))
                  (.split false ⟨.spoke, 6, 6, false⟩
                    (.similar 0 ⟨true, 2⟩)
                    (.split false ⟨.spoke, 1, 6, true⟩
                      (.terminal .reducible)
                      (.split false ⟨.spoke, 3, 6, true⟩
                        (.terminal .reducible)
                        (.split false ⟨.hat, 5, 5, true⟩
                          (.terminal .reducible)
                          (.split false ⟨.hat, 6, 5, true⟩
                            (.terminal .reducible)
                            (.split false ⟨.hat, 0, 5, true⟩
                              (.terminal .reducible)
                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩, ⟨1, some 3, 2⟩]))))))))))
              (.split false ⟨.spoke, 5, 5, true⟩
                (.similar 0 ⟨false, 5⟩)
                (.split false ⟨.spoke, 1, 6, true⟩
                  (.split true ⟨.spoke, 3, 6, false⟩
                    (.split true ⟨.hat, 1, 5, false⟩
                      (.split false ⟨.spoke, 5, 8, false⟩
                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩, ⟨2, some 3, 3⟩]))
                        (.split false ⟨.spoke, 6, 7, false⟩
                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨6, none, -1⟩, ⟨2, some 5, 4⟩, ⟨3, some 4, 1⟩]))
                          (.split false ⟨.fan1, 1, 5, true⟩
                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, some 4, 1⟩, ⟨5, some 6, 3⟩]))
                            (.split false ⟨.hat, 6, 5, true⟩
                              (.split false ⟨.spoke, 5, 6, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.spoke, 6, 6, false⟩
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨4, none, 0⟩, ⟨2, some 3, 3⟩, ⟨5, some 6, 1⟩]))
                                  (.split false ⟨.hat, 0, 5, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.spoke, 3, 7, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩]))
                                      (.split false ⟨.spoke, 4, 6, true⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨6, none, 1⟩, ⟨1, some 5, 4⟩]))
                                        (.split false ⟨.spoke, 5, 7, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩, ⟨2, some 3, 3⟩]))
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩, ⟨2, some 3, 3⟩]))))))))
                              (.split false ⟨.spoke, 5, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩, ⟨2, some 3, 3⟩]))
                                (.split false ⟨.hat, 0, 5, true⟩
                                  (.split false ⟨.spoke, 6, 6, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.fan2, 6, 5, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.spoke, 3, 7, false⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 1⟩, ⟨5, none, 1⟩, ⟨6, none, 0⟩]))
                                        (.split false ⟨.spoke, 4, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩, ⟨3, some 4, 1⟩]))
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨3, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 0⟩, ⟨2, some 4, 3⟩]))))))
                                  (.split false ⟨.spoke, 6, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨6, none, -1⟩, ⟨2, some 5, 4⟩, ⟨3, some 4, 1⟩]))
                                    (.split false ⟨.spoke, 3, 7, false⟩
                                      (.split false ⟨.spoke, 5, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩]))
                                        (.split false ⟨.spoke, 4, 7, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, -1⟩, ⟨5, some 6, 3⟩]))
                                          (.split false ⟨.spoke, 4, 6, false⟩
                                            (.split false ⟨.hat, 2, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩]))
                                              (.split false ⟨.hat, 3, 5, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, some 6, 3⟩]))
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, 0⟩, ⟨5, some 6, 3⟩]))))
                                            (.split false ⟨.hat, 2, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, -1⟩, ⟨4, none, 1⟩, ⟨5, some 6, 3⟩]))
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, some 6, 2⟩]))))))
                                      (.split false ⟨.hat, 2, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, some 4, 1⟩, ⟨5, some 6, 3⟩]))
                                        (.split false ⟨.hat, 6, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨6, none, 1⟩, ⟨2, some 5, 3⟩, ⟨1, some 3, 4⟩, ⟨1, some 4, 4⟩, ⟨3, some 4, 1⟩]))
                                          (.split false ⟨.fan1, 3, 5, true⟩
                                            (.split false ⟨.hat, 3, 6, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.spoke, 4, 7, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, some 6, 3⟩]))
                                                (.split false ⟨.spoke, 4, 6, true⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨3, none, -1⟩, ⟨2, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                                  (.split false ⟨.spoke, 5, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩]))
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨3, some 4, -1⟩, ⟨5, some 6, 3⟩]))))))
                                            (.split false ⟨.fan1, 6, 5, true⟩
                                              (.split false ⟨.hat, 0, 6, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.spoke, 5, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩, ⟨2, some 3, 3⟩]))
                                                  (.split false ⟨.fan1, 5, 5, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.spoke, 4, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩, ⟨1, some 4, 3⟩]))
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨3, none, -1⟩, ⟨5, none, 2⟩, ⟨6, none, 1⟩, ⟨2, some 4, 3⟩]))))))
                                              (.split false ⟨.spoke, 5, 6, false⟩
                                                (.split false ⟨.hat, 2, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩]))
                                                  (.split false ⟨.hat, 3, 5, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩]))
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩]))))
                                                (.split false ⟨.spoke, 4, 6, true⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨3, none, -1⟩, ⟨2, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                                  (.split false ⟨.hat, 2, 5, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, some 6, 3⟩]))
                                                    (.split false ⟨.hat, 3, 5, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, some 6, 3⟩]))
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, -1⟩, ⟨5, some 6, 3⟩]))))))))))))))))))
                      (.split false ⟨.fan1, 1, 5, true⟩
                        (.terminal .reducible)
                        (.split true ⟨.spoke, 4, 6, false⟩
                          (.split false ⟨.fan1, 1, 6, true⟩
                            (.split false ⟨.hat, 2, 6, true⟩
                              (.terminal .reducible)
                              (.split false ⟨.spoke, 6, 6, false⟩
                                (.similar 0 ⟨true, 4⟩)
                                (.split false ⟨.hat, 0, 6, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.spoke, 3, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, -1⟩, ⟨4, none, 1⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩]))
                                    (.split false ⟨.spoke, 4, 7, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩]))
                                      (.split false ⟨.spoke, 5, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))))))))
                            (.split false ⟨.spoke, 6, 7, false⟩
                              (.split false ⟨.hat, 2, 5, false⟩
                                (.similar 0 ⟨true, 4⟩)
                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩, ⟨3, some 4, 0⟩])))
                              (.split false ⟨.hat, 2, 6, false⟩
                                (.split false ⟨.spoke, 6, 6, false⟩
                                  (.similar 0 ⟨true, 4⟩)
                                  (.split false ⟨.hat, 0, 6, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.spoke, 3, 7, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, -1⟩, ⟨4, none, 1⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩]))
                                      (.split false ⟨.spoke, 4, 7, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩]))
                                        (.split false ⟨.spoke, 5, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩])))))))
                                (.split false ⟨.hat, 0, 5, true⟩
                                  (.split false ⟨.spoke, 6, 6, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.hat, 3, 5, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.fan2, 6, 5, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.hat, 2, 5, false⟩
                                          (.similar 0 ⟨true, 4⟩)
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩]))))))
                                  (.split false ⟨.hat, 0, 6, true⟩
                                    (.split false ⟨.spoke, 6, 6, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.fan2, 6, 5, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.hat, 2, 5, false⟩
                                          (.similar 0 ⟨true, 4⟩)
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩, ⟨3, some 4, 0⟩])))))
                                    (.split false ⟨.spoke, 6, 6, false⟩
                                      (.split false ⟨.hat, 2, 5, false⟩
                                        (.similar 0 ⟨true, 4⟩)
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, -1⟩, ⟨3, some 4, 0⟩])))
                                      (.split false ⟨.spoke, 5, 6, false⟩
                                        (.split false ⟨.hat, 3, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩, ⟨2, some 3, 2⟩]))
                                          (.split false ⟨.spoke, 3, 7, false⟩
                                            (.split false ⟨.spoke, 5, 7, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, -1⟩, ⟨6, none, 1⟩]))
                                              (.split false ⟨.hat, 2, 5, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                                (.split false ⟨.hat, 6, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, -1⟩, ⟨6, none, 1⟩]))
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, -1⟩, ⟨6, none, 1⟩])))))
                                            (.split false ⟨.fan1, 3, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.hat, 2, 5, false⟩
                                                (.split false ⟨.spoke, 4, 7, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                                  (.split false ⟨.spoke, 5, 7, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, -1⟩, ⟨6, none, 1⟩]))
                                                    (.split false ⟨.hat, 4, 5, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                                      (.split false ⟨.hat, 6, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, -1⟩, ⟨6, none, 1⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, -1⟩, ⟨6, none, 1⟩]))))))
                                                (.split false ⟨.spoke, 5, 7, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, -1⟩, ⟨6, none, 1⟩]))
                                                  (.split false ⟨.hat, 6, 5, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, -1⟩, ⟨6, none, 1⟩]))
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, -1⟩, ⟨6, none, 1⟩]))))))))
                                        (.split false ⟨.hat, 6, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.spoke, 3, 7, false⟩
                                            (.split false ⟨.spoke, 4, 7, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, -1⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                              (.split false ⟨.hat, 2, 5, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                                (.split false ⟨.hat, 3, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩])))))
                                            (.split false ⟨.hat, 2, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                              (.split false ⟨.hat, 3, 5, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, -1⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩])))))))))))))
                          (.split false ⟨.fan1, 1, 6, true⟩
                            (.split false ⟨.hat, 2, 6, true⟩
                              (.terminal .reducible)
                              (.split false ⟨.spoke, 6, 6, false⟩
                                (.similar 1 ⟨true, 4⟩)
                                (.split false ⟨.hat, 0, 6, true⟩
                                  (.terminal .reducible)
                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩])))))
                            (.split false ⟨.spoke, 5, 6, true⟩
                              (.split false ⟨.hat, 5, 5, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.spoke, 6, 6, false⟩
                                  (.split false ⟨.hat, 2, 5, false⟩
                                    (.similar 1 ⟨true, 4⟩)
                                    (.split false ⟨.hat, 5, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨3, some 6, -1⟩]))
                                      (.split false ⟨.fan1, 4, 5, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.fan1, 5, 5, true⟩
                                          (.terminal .reducible)
                                          (.split true ⟨.spoke, 3, 7, false⟩
                                            (.split false ⟨.spoke, 6, 7, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨6, none, -1⟩, ⟨4, some 5, 1⟩]))
                                              (.split false ⟨.hat, 6, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.hat, 3, 5, true⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, -1⟩]))
                                                  (.split false ⟨.hat, 4, 5, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩]))
                                                    (.split false ⟨.hat, 0, 5, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, -1⟩]))
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, -1⟩])))))))
                                            (.split false ⟨.spoke, 6, 7, false⟩
                                              (.similar 0 ⟨true, 4⟩)
                                              (.split false ⟨.hat, 4, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.hat, 6, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨3, some 6, -1⟩]))))))))))
                                  (.split false ⟨.hat, 6, 5, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.hat, 0, 6, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.spoke, 3, 7, true⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                        (.split false ⟨.hat, 2, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                          (.split false ⟨.hat, 3, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩])))))))))
                              (.split false ⟨.spoke, 6, 6, false⟩
                                (.similar 0 ⟨true, 4⟩)
                                (.split false ⟨.hat, 0, 6, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.spoke, 3, 7, false⟩
                                    (.split false ⟨.spoke, 5, 7, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, -1⟩, ⟨6, none, 1⟩]))
                                      (.split false ⟨.hat, 5, 5, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.hat, 2, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                          (.split false ⟨.hat, 3, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                            (.split false ⟨.hat, 6, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, -1⟩, ⟨6, none, 1⟩]))
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, -1⟩, ⟨6, none, 1⟩])))))))
                                    (.split false ⟨.hat, 4, 5, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.hat, 2, 5, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                        (.split false ⟨.hat, 3, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, -1⟩, ⟨6, none, 1⟩])))))))))))))
                    (.split false ⟨.spoke, 6, 6, false⟩
                      (.similar 0 ⟨true, 4⟩)
                      (.split false ⟨.hat, 3, 5, true⟩
                        (.terminal .reducible)
                        (.split false ⟨.hat, 0, 5, true⟩
                          (.terminal .reducible)
                          (.split true ⟨.spoke, 4, 6, false⟩
                            (.split false ⟨.spoke, 5, 6, false⟩
                              (.split false ⟨.fan1, 1, 5, true⟩
                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩]))
                                (.split true ⟨.hat, 3, 6, true⟩
                                  (.split false ⟨.hat, 2, 5, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.fan1, 3, 5, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.spoke, 4, 7, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨6, none, 1⟩, ⟨1, some 5, 3⟩]))
                                        (.split false ⟨.spoke, 5, 7, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨6, none, 1⟩, ⟨1, some 5, 2⟩]))
                                          (.split false ⟨.hat, 1, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩]))
                                            (.split false ⟨.hat, 0, 6, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.hat, 4, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, -1⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                                (.split false ⟨.hat, 4, 5, true⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                                  (.split false ⟨.hat, 5, 6, true⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨6, none, 1⟩, ⟨4, some 5, 0⟩]))
                                                    (.split false ⟨.hat, 6, 5, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, -1⟩, ⟨6, none, 1⟩]))
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, -1⟩, ⟨6, none, 1⟩]))))))))))))
                                  (.split false ⟨.hat, 0, 6, true⟩
                                    (.similar 0 ⟨true, 4⟩)
                                    (.split false ⟨.fan1, 1, 6, true⟩
                                      (.split false ⟨.spoke, 4, 7, false⟩
                                        (.terminal (.hubcap [⟨1, none, 3⟩, ⟨3, none, 1⟩, ⟨6, none, 1⟩, ⟨0, some 5, 3⟩, ⟨2, some 4, 2⟩]))
                                        (.split false ⟨.spoke, 5, 7, false⟩
                                          (.terminal (.hubcap [⟨1, none, 3⟩, ⟨3, none, 1⟩, ⟨6, none, 1⟩, ⟨0, some 5, 2⟩, ⟨2, some 4, 3⟩]))
                                          (.split false ⟨.hat, 4, 6, false⟩
                                            (.terminal (.hubcap [⟨1, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, -1⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩, ⟨0, some 2, 5⟩]))
                                            (.split false ⟨.hat, 4, 5, true⟩
                                              (.terminal (.hubcap [⟨1, none, 3⟩, ⟨3, none, 1⟩, ⟨6, none, 1⟩, ⟨0, some 5, 3⟩, ⟨2, some 4, 2⟩]))
                                              (.split false ⟨.hat, 2, 5, true⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, -1⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩]))
                                                (.split false ⟨.hat, 1, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩]))
                                                  (.split false ⟨.hat, 2, 6, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.hat, 5, 6, true⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨6, none, 1⟩, ⟨4, some 5, 0⟩]))
                                                      (.split false ⟨.hat, 6, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, -1⟩, ⟨6, none, 1⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, -1⟩, ⟨6, none, 1⟩])))))))))))
                                      (.split true ⟨.spoke, 4, 7, false⟩
                                        (.split false ⟨.spoke, 5, 7, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 1⟩, ⟨6, none, 1⟩, ⟨1, some 5, 3⟩, ⟨2, some 4, 2⟩]))
                                          (.split false ⟨.hat, 1, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨3, none, 1⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩, ⟨2, some 4, 2⟩]))
                                            (.split false ⟨.hat, 2, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                              (.split false ⟨.hat, 6, 5, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, -1⟩, ⟨5, none, -1⟩, ⟨6, none, 1⟩]))
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, -1⟩, ⟨5, none, -1⟩, ⟨6, none, 1⟩]))))))
                                        (.split false ⟨.spoke, 5, 7, false⟩
                                          (.similar 0 ⟨true, 4⟩)
                                          (.split true ⟨.hat, 4, 5, true⟩
                                            (.split false ⟨.fan1, 4, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.hat, 1, 5, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨3, none, 1⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩, ⟨2, some 4, 2⟩]))
                                                (.split false ⟨.hat, 2, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                                  (.split false ⟨.hat, 6, 5, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, -1⟩, ⟨5, none, -1⟩, ⟨6, none, 1⟩]))
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, -1⟩, ⟨5, none, -1⟩, ⟨6, none, 1⟩]))))))
                                            (.split false ⟨.hat, 6, 5, true⟩
                                              (.similar 0 ⟨true, 4⟩)
                                              (.split false ⟨.hat, 5, 5, true⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 1⟩, ⟨6, none, 1⟩, ⟨1, some 5, 3⟩, ⟨2, some 4, 2⟩]))
                                                (.split true ⟨.hat, 1, 5, false⟩
                                                  (.split false ⟨.hat, 2, 5, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩]))
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, -1⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩])))
                                                  (.split false ⟨.hat, 2, 5, false⟩
                                                    (.similar 0 ⟨true, 4⟩)
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, -1⟩, ⟨5, none, -1⟩, ⟨6, none, 1⟩])))))))))))))
                              (.split false ⟨.hat, 6, 5, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.spoke, 4, 7, false⟩
                                  (.split false ⟨.hat, 1, 5, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, -2⟩, ⟨5, some 6, 3⟩]))
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, -2⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩])))
                                  (.split false ⟨.hat, 4, 5, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.hat, 5, 5, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.hat, 1, 5, false⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨3, none, 1⟩, ⟨2, some 4, 2⟩, ⟨5, some 6, 2⟩]))
                                        (.split false ⟨.hat, 0, 6, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.fan1, 1, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.hat, 2, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, -2⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩])))))))))))
                            (.split false ⟨.spoke, 5, 6, false⟩
                              (.similar 0 ⟨true, 4⟩)
                              (.terminal .reducible)))))))
                  (.split true ⟨.spoke, 4, 6, false⟩
                    (.split true ⟨.spoke, 3, 6, false⟩
                      (.split false ⟨.spoke, 5, 6, false⟩
                        (.split false ⟨.spoke, 6, 7, false⟩
                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩, ⟨1, some 3, 5⟩]))
                          (.split false ⟨.spoke, 6, 6, false⟩
                            (.split false ⟨.spoke, 1, 8, false⟩
                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩]))
                              (.split false ⟨.spoke, 3, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨1, some 6, 5⟩]))
                                (.split false ⟨.hat, 3, 6, false⟩
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨1, some 6, 5⟩]))
                                  (.split false ⟨.hat, 0, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩, ⟨1, some 3, 5⟩]))
                                    (.split false ⟨.fan1, 3, 5, false⟩
                                      (.split false ⟨.spoke, 1, 7, false⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨1, some 6, 4⟩]))
                                        (.split false ⟨.spoke, 4, 7, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨1, some 6, 5⟩]))
                                          (.split false ⟨.hat, 2, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨1, some 6, 4⟩]))
                                            (.split false ⟨.fan2, 6, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.spoke, 5, 7, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩, ⟨1, some 3, 5⟩]))
                                                (.split false ⟨.hat, 1, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨1, some 3, 4⟩]))
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))))))))
                                      (.split false ⟨.fan2, 3, 5, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.spoke, 4, 7, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨1, some 3, 3⟩]))
                                          (.split false ⟨.spoke, 5, 7, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨1, some 3, 4⟩]))
                                            (.split false ⟨.hat, 1, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨1, some 6, 3⟩]))
                                              (.split false ⟨.spoke, 1, 7, true⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨1, some 3, 4⟩]))
                                                (.split false ⟨.hat, 1, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨1, some 6, 3⟩]))
                                                  (.split false ⟨.hat, 2, 5, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨1, some 3, 3⟩]))
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩]))))))))))))))
                            (.split false ⟨.hat, 0, 5, true⟩
                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨1, some 5, 1⟩, ⟨1, some 6, 2⟩, ⟨5, some 6, 4⟩]))
                              (.split false ⟨.spoke, 1, 8, false⟩
                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 0⟩, ⟨5, some 6, 3⟩]))
                                (.split false ⟨.spoke, 3, 7, false⟩
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨6, none, 2⟩, ⟨1, some 5, 4⟩]))
                                  (.split false ⟨.spoke, 5, 8, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, -1⟩, ⟨6, none, 2⟩, ⟨1, some 3, 5⟩]))
                                    (.split false ⟨.hat, 6, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, -1⟩, ⟨6, none, 2⟩, ⟨1, some 3, 5⟩]))
                                      (.split false ⟨.hat, 0, 6, true⟩
                                        (.split false ⟨.fan1, 6, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.spoke, 5, 7, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨1, some 3, 4⟩]))
                                            (.split false ⟨.hat, 1, 5, true⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩, ⟨1, some 3, 3⟩]))
                                              (.split false ⟨.spoke, 1, 7, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 0⟩, ⟨6, none, 1⟩, ⟨1, some 5, 2⟩]))
                                                (.split false ⟨.hat, 2, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 1⟩, ⟨1, some 3, 3⟩]))
                                                  (.split false ⟨.hat, 2, 5, true⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩, ⟨1, some 3, 4⟩]))
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨6, none, 1⟩, ⟨1, some 5, 3⟩]))))))))
                                        (.split false ⟨.spoke, 5, 7, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩, ⟨1, some 3, 5⟩]))
                                          (.split false ⟨.hat, 3, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨6, none, 1⟩, ⟨1, some 5, 4⟩]))
                                            (.split false ⟨.fan2, 5, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩, ⟨1, some 3, 5⟩]))
                                              (.split false ⟨.fan1, 3, 5, false⟩
                                                (.split false ⟨.spoke, 1, 7, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨6, none, 1⟩, ⟨1, some 5, 3⟩]))
                                                  (.split false ⟨.spoke, 4, 7, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨6, none, 1⟩, ⟨1, some 5, 4⟩]))
                                                    (.split false ⟨.hat, 1, 5, true⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩, ⟨1, some 3, 5⟩]))
                                                      (.split false ⟨.hat, 2, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨6, none, 1⟩, ⟨1, some 5, 3⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩, ⟨1, some 3, 4⟩]))))))
                                                (.split false ⟨.fan2, 3, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.spoke, 4, 7, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 1⟩]))
                                                    (.split false ⟨.spoke, 1, 7, true⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 1⟩, ⟨1, some 3, 3⟩]))
                                                      (.split false ⟨.hat, 1, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 0⟩, ⟨6, none, 1⟩, ⟨1, some 5, 2⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 1⟩, ⟨1, some 3, 3⟩]))))))))))))))))))
                        (.split false ⟨.spoke, 6, 6, false⟩
                          (.split false ⟨.spoke, 1, 8, false⟩
                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨3, some 4, 3⟩, ⟨3, some 6, 6⟩, ⟨4, some 6, 4⟩]))
                            (.split false ⟨.hat, 6, 5, true⟩
                              (.split false ⟨.spoke, 3, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨1, some 6, 4⟩]))
                                (.split false ⟨.spoke, 4, 7, false⟩
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨1, some 6, 4⟩]))
                                  (.split false ⟨.hat, 3, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨1, some 6, 4⟩, ⟨3, some 4, 2⟩]))
                                    (.split false ⟨.spoke, 1, 7, false⟩
                                      (.split false ⟨.spoke, 6, 7, false⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩, ⟨3, some 4, 3⟩]))
                                        (.split false ⟨.hat, 1, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨3, some 4, 3⟩, ⟨3, some 6, 6⟩, ⟨4, some 6, 4⟩]))
                                          (.split false ⟨.hat, 2, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.fan1, 1, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.hat, 2, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨3, some 4, 3⟩, ⟨3, some 6, 6⟩, ⟨4, some 6, 4⟩]))
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨1, some 6, 4⟩, ⟨3, some 4, 2⟩])))))))
                                      (.split false ⟨.spoke, 6, 7, false⟩
                                        (.split false ⟨.hat, 1, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩, ⟨3, some 4, 3⟩]))
                                          (.split false ⟨.fan1, 3, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.hat, 2, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩, ⟨3, some 4, 3⟩]))
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩, ⟨3, some 4, 2⟩])))))
                                        (.split false ⟨.hat, 1, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.hat, 2, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.hat, 1, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨3, some 4, 3⟩, ⟨3, some 6, 6⟩, ⟨4, some 6, 4⟩]))
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨1, some 3, 3⟩, ⟨4, some 6, 3⟩]))))))))))
                              (.split false ⟨.spoke, 1, 7, false⟩
                                (.split false ⟨.spoke, 3, 7, false⟩
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨5, none, 0⟩, ⟨4, some 6, 4⟩]))
                                  (.split false ⟨.spoke, 4, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨1, some 3, 3⟩]))
                                    (.split false ⟨.spoke, 6, 7, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩, ⟨3, some 4, 3⟩]))
                                      (.split false ⟨.hat, 1, 5, false⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨1, some 6, 3⟩, ⟨3, some 4, 3⟩]))
                                        (.split false ⟨.hat, 3, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨1, some 6, 4⟩, ⟨3, some 4, 2⟩]))
                                          (.split false ⟨.hat, 5, 5, true⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨5, none, 0⟩, ⟨1, some 4, 3⟩, ⟨1, some 6, 4⟩, ⟨4, some 6, 4⟩]))
                                            (.split false ⟨.hat, 3, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨1, some 6, 4⟩, ⟨3, some 4, 2⟩]))
                                              (.split false ⟨.hat, 2, 5, true⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 0⟩, ⟨1, some 6, 3⟩]))
                                                (.split false ⟨.hat, 4, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨3, some 4, 2⟩]))
                                                  (.split false ⟨.hat, 5, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨1, some 3, 3⟩]))
                                                    (.split false ⟨.hat, 6, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨3, some 4, 3⟩]))
                                                      (.split false ⟨.hat, 0, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                                        (.split false ⟨.hat, 2, 6, true⟩
                                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨3, some 4, 2⟩]))
                                                          (.split false ⟨.fan1, 1, 5, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨3, some 4, 3⟩]))
                                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨3, some 4, 2⟩]))))))))))))))))
                                (.split false ⟨.hat, 1, 5, true⟩
                                  (.split false ⟨.spoke, 3, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨5, none, 0⟩, ⟨4, some 6, 2⟩]))
                                    (.split false ⟨.spoke, 4, 7, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                      (.split false ⟨.hat, 3, 5, false⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨5, none, 0⟩, ⟨4, some 6, 2⟩]))
                                        (.split false ⟨.fan1, 3, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.spoke, 6, 7, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩, ⟨1, some 3, 5⟩, ⟨1, some 4, 5⟩, ⟨3, some 4, 3⟩]))
                                            (.split false ⟨.hat, 5, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩, ⟨1, some 3, 5⟩]))
                                              (.split false ⟨.hat, 5, 5, true⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨5, none, 0⟩, ⟨4, some 6, 2⟩]))
                                                (.split false ⟨.hat, 2, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                                  (.split false ⟨.fan1, 1, 5, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.hat, 0, 5, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩]))
                                                      (.split false ⟨.fan2, 1, 5, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.fan2, 6, 5, true⟩
                                                          (.terminal .reducible)
                                                          (.split false ⟨.fan1, 4, 5, true⟩
                                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                                            (.split false ⟨.fan2, 4, 5, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))))))))))))))))
                                  (.split false ⟨.spoke, 6, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩, ⟨3, some 4, 3⟩]))
                                    (.split false ⟨.hat, 0, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨1, some 3, 4⟩, ⟨4, some 6, 2⟩]))
                                      (.split false ⟨.hat, 2, 5, false⟩
                                        (.split false ⟨.spoke, 3, 7, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨5, none, 0⟩, ⟨4, some 6, 4⟩]))
                                          (.split false ⟨.spoke, 4, 7, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨1, some 3, 3⟩]))
                                            (.split false ⟨.hat, 3, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨1, some 6, 4⟩, ⟨3, some 4, 2⟩]))
                                              (.split false ⟨.hat, 6, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨1, some 6, 3⟩, ⟨3, some 4, 3⟩]))
                                                (.split false ⟨.hat, 0, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩, ⟨3, some 4, 3⟩]))
                                                  (.split false ⟨.hat, 2, 6, true⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨1, some 6, 4⟩, ⟨3, some 4, 2⟩]))
                                                    (.split false ⟨.hat, 1, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨3, some 4, 3⟩]))
                                                      (.split false ⟨.fan2, 6, 5, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.hat, 3, 5, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨3, some 4, 2⟩]))
                                                          (.split false ⟨.hat, 4, 5, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨3, some 4, 2⟩]))
                                                            (.split false ⟨.hat, 5, 6, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨1, some 3, 4⟩]))
                                                              (.split false ⟨.hat, 5, 5, true⟩
                                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩]))
                                                                (.split false ⟨.fan1, 1, 5, false⟩
                                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨3, some 4, 3⟩]))
                                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨3, some 4, 2⟩])))))))))))))))
                                        (.split false ⟨.fan2, 6, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.spoke, 3, 7, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨5, none, 0⟩, ⟨4, some 6, 3⟩]))
                                            (.split false ⟨.spoke, 4, 7, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩]))
                                              (.split false ⟨.hat, 5, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨1, some 3, 4⟩]))
                                                (.split false ⟨.hat, 5, 5, true⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨5, none, 0⟩, ⟨4, some 6, 3⟩]))
                                                  (.split false ⟨.hat, 6, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩, ⟨1, some 3, 4⟩]))
                                                    (.split false ⟨.hat, 0, 5, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩, ⟨1, some 3, 4⟩]))
                                                      (.split false ⟨.hat, 3, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨3, some 4, 1⟩]))
                                                        (.split false ⟨.fan1, 3, 5, true⟩
                                                          (.terminal .reducible)
                                                          (.split false ⟨.hat, 1, 6, true⟩
                                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨3, some 4, 2⟩]))
                                                            (.split false ⟨.fan1, 1, 5, true⟩
                                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨3, some 4, 2⟩]))
                                                              (.split false ⟨.fan1, 4, 5, true⟩
                                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨1, some 3, 4⟩]))
                                                                (.split false ⟨.fan1, 6, 5, false⟩
                                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                                                  (.split false ⟨.fan2, 6, 6, true⟩
                                                                    (.terminal .reducible)
                                                                    (.split false ⟨.fan2, 1, 5, false⟩
                                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩]))
                                                                      (.split false ⟨.fan2, 4, 5, false⟩
                                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩]))
                                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩])))))))))))))))))))))))))
                          (.split false ⟨.hat, 0, 5, true⟩
                            (.split false ⟨.fan1, 6, 5, true⟩
                              (.terminal .reducible)
                              (.split false ⟨.spoke, 1, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, -1⟩, ⟨2, none, 2⟩, ⟨3, some 4, 1⟩, ⟨5, some 6, 5⟩]))
                                (.split false ⟨.hat, 1, 6, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.hat, 2, 5, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.spoke, 3, 7, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, some 6, 5⟩]))
                                      (.split false ⟨.spoke, 4, 7, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 2⟩, ⟨4, none, -1⟩, ⟨1, some 3, 1⟩, ⟨5, some 6, 5⟩]))
                                        (.split false ⟨.hat, 2, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, -1⟩, ⟨2, none, 2⟩, ⟨3, some 4, 1⟩, ⟨5, some 6, 5⟩]))
                                          (.split false ⟨.fan2, 1, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.hat, 3, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, -1⟩, ⟨2, none, 2⟩, ⟨3, some 4, 1⟩, ⟨5, some 6, 5⟩]))
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, some 6, 4⟩])))))))))))
                            (.split false ⟨.spoke, 1, 8, false⟩
                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, some 6, 4⟩]))
                              (.split false ⟨.hat, 6, 6, false⟩
                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨1, some 6, 5⟩, ⟨3, some 4, 1⟩]))
                                (.split false ⟨.hat, 6, 5, true⟩
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, some 4, 1⟩, ⟨5, some 6, 4⟩]))
                                  (.split false ⟨.spoke, 1, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, some 4, 1⟩, ⟨5, some 6, 3⟩]))
                                    (.split false ⟨.spoke, 3, 7, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨1, some 5, 4⟩, ⟨1, some 6, 6⟩, ⟨5, some 6, 3⟩]))
                                      (.split false ⟨.hat, 5, 5, false⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, some 4, 1⟩, ⟨1, some 5, 4⟩, ⟨1, some 6, 5⟩, ⟨5, some 6, 2⟩]))
                                        (.split false ⟨.hat, 2, 5, true⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, some 4, 0⟩, ⟨1, some 5, 4⟩, ⟨1, some 6, 6⟩, ⟨5, some 6, 3⟩]))
                                          (.split false ⟨.spoke, 4, 7, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, -1⟩, ⟨1, some 3, 4⟩, ⟨5, some 6, 3⟩]))
                                            (.split false ⟨.fan2, 4, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.hat, 1, 5, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, some 6, 3⟩]))
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, some 6, 2⟩])))))))))))))))
                      (.split true ⟨.hat, 3, 5, true⟩
                        (.split false ⟨.fan1, 3, 5, true⟩
                          (.terminal .reducible)
                          (.split false ⟨.spoke, 6, 7, false⟩
                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩]))
                            (.split false ⟨.spoke, 5, 6, false⟩
                              (.split false ⟨.spoke, 6, 6, false⟩
                                (.similar 0 ⟨true, 4⟩)
                                (.split false ⟨.spoke, 4, 8, false⟩
                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, -1⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, -1⟩, ⟨5, some 6, 3⟩]))
                                  (.split false ⟨.hat, 4, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, -1⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, -1⟩, ⟨5, some 6, 3⟩]))
                                    (.split false ⟨.hat, 0, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, -1⟩, ⟨2, none, 3⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩, ⟨3, some 4, 4⟩]))
                                      (.split false ⟨.hat, 0, 5, true⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, -2⟩, ⟨2, none, 3⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                        (.split false ⟨.fan1, 6, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.spoke, 1, 7, true⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, -1⟩, ⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩]))
                                            (.split false ⟨.spoke, 4, 7, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, -1⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩]))
                                              (.split false ⟨.spoke, 5, 7, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, -1⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨6, none, 2⟩, ⟨4, some 5, 1⟩]))
                                                (.split false ⟨.hat, 1, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, -1⟩, ⟨2, none, 3⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩, ⟨3, some 4, 4⟩]))
                                                  (.split false ⟨.spoke, 1, 8, true⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, -1⟩, ⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨6, none, 2⟩, ⟨4, some 5, 2⟩]))
                                                    (.split false ⟨.hat, 2, 5, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, -1⟩, ⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨6, none, 2⟩, ⟨4, some 5, 2⟩]))
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, -1⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨6, none, 2⟩, ⟨4, some 5, 1⟩]))))))))))))))
                              (.split false ⟨.spoke, 6, 6, false⟩
                                (.split false ⟨.spoke, 1, 7, true⟩
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨5, none, 0⟩, ⟨1, some 4, 1⟩, ⟨1, some 6, 2⟩, ⟨4, some 6, 4⟩]))
                                  (.split false ⟨.spoke, 4, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, -1⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, -1⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩]))
                                    (.split false ⟨.hat, 2, 5, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, -1⟩, ⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨5, none, 0⟩, ⟨4, some 6, 4⟩]))
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, -1⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨5, none, 0⟩, ⟨4, some 6, 3⟩])))))
                                (.split false ⟨.hat, 6, 6, false⟩
                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, -1⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨5, none, 0⟩, ⟨4, some 6, 2⟩]))
                                  (.split false ⟨.hat, 0, 5, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, -1⟩, ⟨2, none, 3⟩, ⟨3, some 4, 2⟩, ⟨5, some 6, 4⟩]))
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, -2⟩, ⟨2, none, 3⟩, ⟨3, some 4, 1⟩, ⟨5, some 6, 5⟩]))))))))
                        (.split false ⟨.spoke, 6, 7, false⟩
                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩, ⟨1, some 4, 4⟩]))
                          (.split false ⟨.spoke, 1, 7, false⟩
                            (.split false ⟨.spoke, 6, 6, false⟩
                              (.split false ⟨.spoke, 5, 6, false⟩
                                (.similar 1 ⟨true, 4⟩)
                                (.split false ⟨.spoke, 4, 7, false⟩
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, -1⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨1, some 3, 3⟩]))
                                  (.split false ⟨.hat, 2, 5, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨5, none, 0⟩, ⟨1, some 4, 2⟩, ⟨1, some 6, 4⟩, ⟨4, some 6, 5⟩]))
                                    (.split false ⟨.hat, 4, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨1, some 6, 4⟩]))
                                      (.split false ⟨.hat, 6, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨1, some 3, 3⟩, ⟨4, some 6, 3⟩]))
                                        (.split false ⟨.hat, 0, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨1, some 3, 2⟩, ⟨4, some 6, 4⟩]))
                                          (.split false ⟨.fan1, 3, 5, true⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 0⟩, ⟨1, some 6, 4⟩]))
                                            (.split false ⟨.fan1, 4, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨1, some 6, 4⟩]))
                                              (.split false ⟨.fan1, 6, 5, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨1, some 6, 3⟩, ⟨3, some 4, 3⟩]))
                                                (.split false ⟨.fan2, 6, 6, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.hat, 4, 5, true⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨1, some 3, 3⟩, ⟨1, some 4, 3⟩, ⟨3, some 4, 3⟩]))
                                                    (.split false ⟨.hat, 3, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 0⟩, ⟨1, some 6, 4⟩]))
                                                      (.split false ⟨.spoke, 1, 8, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨5, none, 0⟩, ⟨4, some 6, 4⟩]))
                                                        (.split false ⟨.hat, 1, 5, true⟩
                                                          (.terminal .reducible)
                                                          (.split false ⟨.hat, 1, 6, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨5, none, 0⟩, ⟨4, some 6, 4⟩]))
                                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩])))))))))))))))))
                              (.split false ⟨.spoke, 5, 8, false⟩
                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 2⟩, ⟨5, none, -1⟩, ⟨1, some 3, 2⟩, ⟨4, some 6, 4⟩]))
                                (.split false ⟨.spoke, 5, 6, true⟩
                                  (.split false ⟨.spoke, 4, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 2⟩, ⟨4, none, -2⟩, ⟨1, some 3, 2⟩, ⟨5, some 6, 5⟩]))
                                    (.split false ⟨.hat, 4, 5, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.hat, 2, 5, false⟩
                                        (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨0, some 4, 2⟩, ⟨5, some 6, 5⟩]))
                                        (.split false ⟨.hat, 3, 6, false⟩
                                          (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨0, some 1, 3⟩, ⟨4, some 5, 1⟩, ⟨4, some 6, 3⟩, ⟨5, some 6, 5⟩]))
                                          (.split false ⟨.fan1, 3, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.hat, 5, 5, false⟩
                                              (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨0, some 4, 1⟩, ⟨5, some 6, 5⟩]))
                                              (.split false ⟨.fan2, 4, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.spoke, 1, 8, true⟩
                                                  (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨0, some 4, 2⟩, ⟨5, some 6, 4⟩]))
                                                  (.split false ⟨.hat, 1, 5, false⟩
                                                    (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨0, some 4, 2⟩, ⟨5, some 6, 4⟩]))
                                                    (.split false ⟨.hat, 6, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩]))
                                                      (.split false ⟨.hat, 0, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, some 6, 4⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, -1⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, -1⟩, ⟨5, some 6, 5⟩])))))))))))))
                                  (.split false ⟨.hat, 0, 5, true⟩
                                    (.similar 0 ⟨true, 4⟩)
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨1, some 3, 2⟩, ⟨1, some 6, 2⟩, ⟨3, some 4, 3⟩, ⟨4, some 5, 3⟩, ⟨5, some 6, 3⟩]))))))
                            (.split false ⟨.spoke, 5, 6, false⟩
                              (.split false ⟨.spoke, 6, 6, false⟩
                                (.similar 1 ⟨true, 4⟩)
                                (.split false ⟨.hat, 0, 5, true⟩
                                  (.similar 0 ⟨true, 4⟩)
                                  (.split false ⟨.spoke, 4, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨6, none, 1⟩, ⟨1, some 5, 4⟩]))
                                    (.split false ⟨.spoke, 5, 7, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩, ⟨1, some 4, 4⟩]))
                                      (.split false ⟨.hat, 1, 5, true⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩, ⟨1, some 4, 4⟩]))
                                        (.split false ⟨.hat, 2, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨6, none, 1⟩, ⟨4, some 5, 3⟩]))
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩]))))))))
                              (.split false ⟨.spoke, 6, 6, false⟩
                                (.split false ⟨.spoke, 4, 7, false⟩
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, -1⟩, ⟨5, none, 0⟩, ⟨1, some 6, 5⟩]))
                                  (.split false ⟨.hat, 1, 5, true⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩, ⟨1, some 4, 4⟩]))
                                    (.split false ⟨.hat, 2, 5, true⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩]))
                                      (.split false ⟨.hat, 1, 6, true⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨5, none, 0⟩, ⟨1, some 4, 3⟩, ⟨1, some 6, 4⟩, ⟨4, some 6, 4⟩]))
                                        (.split false ⟨.hat, 2, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨5, none, 0⟩, ⟨4, some 6, 5⟩]))
                                          (.split false ⟨.hat, 4, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 0⟩, ⟨1, some 6, 4⟩]))
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨1, some 6, 3⟩]))))))))
                                (.split false ⟨.hat, 1, 5, true⟩
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨1, some 4, 3⟩, ⟨5, some 6, 2⟩]))
                                  (.split false ⟨.hat, 2, 5, false⟩
                                    (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨0, some 1, 3⟩, ⟨4, some 5, 1⟩, ⟨4, some 6, 3⟩, ⟨5, some 6, 5⟩]))
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, -1⟩, ⟨5, some 6, 3⟩]))))))))))
                    (.split false ⟨.spoke, 5, 6, false⟩
                      (.similar 0 ⟨true, 4⟩)
                      (.split false ⟨.hat, 5, 5, true⟩
                        (.split false ⟨.spoke, 1, 8, false⟩
                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨3, some 6, 2⟩]))
                          (.split false ⟨.spoke, 3, 7, false⟩
                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, some 5, 3⟩, ⟨4, some 6, 3⟩, ⟨5, some 6, 3⟩]))
                            (.split false ⟨.spoke, 3, 6, true⟩
                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 0⟩, ⟨3, some 4, 3⟩]))
                              (.split false ⟨.hat, 4, 5, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.spoke, 6, 6, false⟩
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, some 4, 2⟩, ⟨5, some 6, 2⟩]))
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨5, some 6, 3⟩])))))))
                        (.split true ⟨.hat, 4, 5, false⟩
                          (.split true ⟨.spoke, 3, 6, true⟩
                            (.split false ⟨.spoke, 6, 6, true⟩
                              (.terminal .reducible)
                              (.split false ⟨.spoke, 1, 7, false⟩
                                (.split false ⟨.spoke, 6, 7, false⟩
                                  (.split false ⟨.spoke, 1, 8, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩]))
                                    (.split false ⟨.hat, 1, 5, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩, ⟨1, some 2, 3⟩]))
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩, ⟨1, some 2, 4⟩, ⟨3, some 4, 4⟩]))))
                                  (.split false ⟨.hat, 6, 5, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.hat, 0, 5, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.hat, 1, 5, true⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 3⟩, ⟨5, none, 0⟩, ⟨1, some 2, 3⟩, ⟨4, some 6, 2⟩]))
                                        (.split false ⟨.hat, 2, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩, ⟨3, some 4, 4⟩]))
                                          (.split false ⟨.hat, 3, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, -1⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))))))))
                                (.split false ⟨.hat, 1, 5, true⟩
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩, ⟨3, some 4, 2⟩]))
                                  (.split false ⟨.hat, 2, 6, true⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩, ⟨3, some 4, 2⟩]))
                                    (.split false ⟨.spoke, 6, 7, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩, ⟨1, some 2, 4⟩, ⟨3, some 4, 4⟩]))
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩, ⟨1, some 2, 3⟩, ⟨3, some 4, 4⟩])))))))
                            (.split true ⟨.spoke, 6, 7, false⟩
                              (.split false ⟨.spoke, 1, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨6, none, 0⟩, ⟨1, some 3, 4⟩, ⟨4, some 5, 2⟩]))
                                (.split false ⟨.spoke, 3, 7, false⟩
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨6, none, 0⟩, ⟨4, some 5, 2⟩]))
                                  (.split false ⟨.hat, 1, 5, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨6, none, 0⟩, ⟨1, some 3, 4⟩, ⟨4, some 5, 2⟩]))
                                    (.split false ⟨.hat, 3, 5, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨6, none, 0⟩, ⟨1, some 3, 4⟩, ⟨4, some 5, 2⟩]))
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨6, none, 0⟩, ⟨1, some 3, 5⟩, ⟨4, some 5, 1⟩]))))))
                              (.split false ⟨.hat, 6, 5, true⟩
                                (.split false ⟨.spoke, 3, 7, false⟩
                                  (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨0, some 1, 3⟩, ⟨5, some 6, 5⟩]))
                                  (.split false ⟨.spoke, 6, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨3, some 6, 5⟩]))
                                    (.split false ⟨.hat, 3, 5, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.hat, 2, 5, true⟩
                                        (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨0, some 1, 3⟩, ⟨5, some 6, 5⟩]))
                                        (.split false ⟨.hat, 3, 6, false⟩
                                          (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨0, some 1, 3⟩, ⟨5, some 6, 5⟩]))
                                          (.split false ⟨.hat, 0, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, some 6, 4⟩]))
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, -1⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 4⟩]))))))))
                                (.split false ⟨.spoke, 3, 7, false⟩
                                  (.similar 0 ⟨true, 4⟩)
                                  (.split false ⟨.spoke, 6, 6, true⟩
                                    (.similar 1 ⟨true, 4⟩)
                                    (.split false ⟨.spoke, 1, 8, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                      (.split false ⟨.fan1, 3, 5, true⟩
                                        (.split false ⟨.hat, 3, 5, true⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 0⟩, ⟨1, some 6, 3⟩, ⟨3, some 5, 3⟩]))
                                          (.split false ⟨.spoke, 1, 7, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨1, some 5, 2⟩, ⟨4, some 6, 3⟩]))
                                            (.split false ⟨.hat, 1, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨1, some 3, 3⟩, ⟨4, some 5, 1⟩, ⟨4, some 6, 3⟩, ⟨5, some 6, 3⟩]))
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 1⟩, ⟨1, some 3, 4⟩, ⟨5, some 6, 1⟩])))))
                                        (.split true ⟨.hat, 2, 5, false⟩
                                          (.split false ⟨.spoke, 1, 7, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, some 4, 2⟩, ⟨5, some 6, 3⟩]))
                                            (.split false ⟨.hat, 1, 5, true⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, some 4, 2⟩, ⟨5, some 6, 1⟩]))
                                              (.split false ⟨.hat, 1, 6, true⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, some 4, 2⟩, ⟨5, some 6, 2⟩]))
                                                (.split false ⟨.hat, 2, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, some 6, 3⟩]))
                                                  (.split false ⟨.hat, 3, 5, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, some 6, 3⟩]))
                                                    (.split false ⟨.hat, 4, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, some 6, 3⟩]))
                                                      (.split false ⟨.hat, 5, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨1, some 6, 4⟩]))
                                                        (.split false ⟨.fan1, 5, 5, true⟩
                                                          (.terminal .reducible)
                                                          (.split false ⟨.hat, 6, 6, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, some 6, 2⟩]))
                                                            (.split false ⟨.hat, 0, 5, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩]))
                                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨1, some 6, 4⟩]))))))))))))
                                          (.split false ⟨.hat, 1, 5, false⟩
                                            (.similar 0 ⟨true, 4⟩)
                                            (.split false ⟨.spoke, 1, 7, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, some 4, 2⟩, ⟨5, some 6, 2⟩]))
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, some 4, 1⟩, ⟨5, some 6, 1⟩]))))))))))))
                          (.split false ⟨.hat, 6, 5, false⟩
                            (.similar 0 ⟨true, 4⟩)
                            (.split false ⟨.spoke, 3, 6, true⟩
                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩, ⟨1, some 2, 3⟩, ⟨3, some 4, 5⟩]))
                              (.split false ⟨.spoke, 6, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨6, none, 0⟩, ⟨1, some 3, 4⟩, ⟨4, some 5, 2⟩]))
                                (.split false ⟨.spoke, 6, 6, true⟩
                                  (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨0, some 1, 3⟩, ⟨5, some 6, 5⟩]))
                                  (.split false ⟨.spoke, 3, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 4⟩]))
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨3, some 6, 6⟩])))))))))))))))
          (.split false ⟨.spoke, 5, 5, true⟩
            (.similar 0 ⟨false, 5⟩)
            (.split true ⟨.spoke, 3, 5, true⟩
              (.split false ⟨.spoke, 4, 5, true⟩
                (.similar 1 ⟨false, 3⟩)
                (.split true ⟨.spoke, 4, 6, false⟩
                  (.split false ⟨.spoke, 6, 6, false⟩
                    (.split false ⟨.hat, 2, 5, true⟩
                      (.split true ⟨.spoke, 1, 6, false⟩
                        (.split false ⟨.spoke, 1, 7, true⟩
                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 2⟩, ⟨5, none, 0⟩, ⟨1, some 2, 2⟩, ⟨4, some 6, 4⟩]))
                          (.split false ⟨.spoke, 2, 6, false⟩
                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨5, none, 0⟩, ⟨4, some 6, 4⟩]))
                            (.split false ⟨.spoke, 6, 7, false⟩
                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, -1⟩, ⟨2, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩, ⟨3, some 4, 6⟩]))
                              (.split false ⟨.hat, 3, 5, false⟩
                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, -1⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨5, none, 0⟩, ⟨4, some 6, 4⟩]))
                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, -2⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨5, none, 0⟩, ⟨4, some 6, 4⟩]))))))
                        (.split false ⟨.spoke, 2, 6, false⟩
                          (.similar 0 ⟨true, 3⟩)
                          (.terminal .reducible)))
                      (.split true ⟨.spoke, 1, 7, false⟩
                        (.split false ⟨.spoke, 2, 6, false⟩
                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨5, none, 0⟩, ⟨4, some 6, 4⟩]))
                          (.split false ⟨.spoke, 6, 7, false⟩
                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, -1⟩, ⟨2, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩, ⟨3, some 4, 6⟩]))
                            (.split false ⟨.hat, 3, 5, false⟩
                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, -1⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨5, none, 0⟩, ⟨4, some 6, 4⟩]))
                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, -2⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨5, none, 0⟩, ⟨4, some 6, 4⟩])))))
                        (.split false ⟨.spoke, 2, 7, false⟩
                          (.similar 0 ⟨true, 3⟩)
                          (.split true ⟨.hat, 1, 5, false⟩
                            (.split false ⟨.hat, 3, 5, false⟩
                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 2⟩, ⟨5, none, 0⟩, ⟨1, some 2, 2⟩, ⟨4, some 6, 4⟩]))
                              (.split false ⟨.spoke, 1, 6, true⟩
                                (.split false ⟨.spoke, 2, 6, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.hat, 4, 5, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.fan2, 2, 5, true⟩
                                      (.terminal .reducible)
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨5, none, 0⟩, ⟨4, some 6, 4⟩])))))
                                (.split false ⟨.spoke, 2, 6, false⟩
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨5, none, 0⟩, ⟨4, some 6, 4⟩]))
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, -2⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨5, none, 0⟩, ⟨4, some 6, 4⟩])))))
                            (.split false ⟨.hat, 3, 5, false⟩
                              (.similar 0 ⟨true, 3⟩)
                              (.split true ⟨.spoke, 1, 6, true⟩
                                (.split false ⟨.spoke, 2, 6, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.hat, 4, 5, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.fan1, 1, 5, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.fan2, 2, 5, true⟩
                                        (.terminal .reducible)
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -1⟩, ⟨3, none, 2⟩, ⟨5, none, 0⟩, ⟨4, some 6, 3⟩]))))))
                                (.split false ⟨.spoke, 2, 6, true⟩
                                  (.similar 0 ⟨true, 3⟩)
                                  (.split false ⟨.hat, 4, 5, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.hat, 0, 5, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.fan1, 1, 5, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.fan2, 2, 5, true⟩
                                          (.terminal .reducible)
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩])))))))))))))
                    (.split false ⟨.spoke, 5, 6, true⟩
                      (.split false ⟨.spoke, 2, 6, false⟩
                        (.split false ⟨.spoke, 1, 6, false⟩
                          (.split false ⟨.spoke, 2, 7, false⟩
                            (.terminal (.hubcap [⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨0, some 4, 2⟩, ⟨1, some 5, 3⟩, ⟨1, some 6, 5⟩, ⟨5, some 6, 5⟩]))
                            (.split false ⟨.hat, 3, 5, true⟩
                              (.terminal (.hubcap [⟨3, none, 2⟩, ⟨0, some 4, 2⟩, ⟨1, some 2, 1⟩, ⟨5, some 6, 5⟩]))
                              (.split false ⟨.spoke, 1, 7, false⟩
                                (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨0, some 4, 2⟩, ⟨5, some 6, 5⟩]))
                                (.split false ⟨.hat, 1, 6, false⟩
                                  (.terminal (.hubcap [⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨0, some 1, 3⟩, ⟨4, some 5, 1⟩, ⟨4, some 6, 3⟩, ⟨5, some 6, 5⟩]))
                                  (.split false ⟨.hat, 1, 5, true⟩
                                    (.terminal (.hubcap [⟨3, none, 2⟩, ⟨0, some 4, 2⟩, ⟨1, some 2, 1⟩, ⟨5, some 6, 5⟩]))
                                    (.split false ⟨.hat, 2, 5, false⟩
                                      (.terminal (.hubcap [⟨1, none, 1⟩, ⟨3, none, 2⟩, ⟨0, some 2, 3⟩, ⟨4, some 5, 1⟩, ⟨4, some 6, 3⟩, ⟨5, some 6, 5⟩]))
                                      (.terminal (.hubcap [⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨0, some 1, 3⟩, ⟨4, some 5, 1⟩, ⟨4, some 6, 3⟩, ⟨5, some 6, 5⟩]))))))))
                          (.split false ⟨.hat, 1, 5, false⟩
                            (.terminal (.hubcap [⟨3, none, 2⟩, ⟨0, some 2, 2⟩, ⟨1, some 4, 1⟩, ⟨5, some 6, 5⟩]))
                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, -1⟩, ⟨3, none, 2⟩, ⟨5, none, 0⟩, ⟨4, some 6, 2⟩]))))
                        (.split false ⟨.spoke, 1, 6, true⟩
                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, some 6, 4⟩]))
                          (.split false ⟨.spoke, 4, 7, true⟩
                            (.terminal (.hubcap [⟨0, some 1, 2⟩, ⟨2, some 4, 1⟩, ⟨3, some 5, 4⟩, ⟨3, some 6, 6⟩, ⟨5, some 6, 5⟩]))
                            (.split false ⟨.hat, 3, 5, false⟩
                              (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, -1⟩, ⟨0, some 1, 2⟩, ⟨5, some 6, 5⟩]))
                              (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, -1⟩, ⟨0, some 1, 1⟩, ⟨5, some 6, 4⟩]))))))
                      (.split false ⟨.spoke, 2, 6, false⟩
                        (.split false ⟨.spoke, 1, 6, false⟩
                          (.split false ⟨.hat, 0, 5, false⟩
                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 2⟩, ⟨1, some 2, 2⟩, ⟨4, some 5, 2⟩]))
                            (.split false ⟨.fan1, 6, 5, true⟩
                              (.terminal .reducible)
                              (.split false ⟨.hat, 1, 5, false⟩
                                (.split false ⟨.spoke, 2, 7, false⟩
                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨6, none, 2⟩, ⟨4, some 5, 2⟩]))
                                  (.split false ⟨.spoke, 5, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 2⟩, ⟨6, none, 2⟩, ⟨1, some 2, 2⟩, ⟨4, some 5, 1⟩]))
                                    (.split false ⟨.hat, 3, 5, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 2⟩, ⟨6, none, 2⟩, ⟨1, some 2, 1⟩, ⟨4, some 5, 2⟩]))
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, -1⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 2⟩, ⟨4, some 5, 2⟩])))))
                                (.split false ⟨.spoke, 1, 7, true⟩
                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨1, some 2, 1⟩, ⟨4, some 5, 1⟩]))
                                  (.split false ⟨.spoke, 2, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨4, some 5, 1⟩]))
                                    (.split false ⟨.hat, 3, 5, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨4, some 5, 1⟩]))
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, -1⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨4, some 5, 1⟩]))))))))
                          (.split false ⟨.hat, 1, 5, false⟩
                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨3, none, 2⟩, ⟨2, some 6, 1⟩, ⟨4, some 5, 2⟩]))
                            (.split false ⟨.fan1, 1, 5, true⟩
                              (.terminal .reducible)
                              (.split false ⟨.spoke, 4, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨2, some 6, 1⟩]))
                                (.split false ⟨.spoke, 5, 7, false⟩
                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 2⟩, ⟨5, none, -1⟩, ⟨1, some 2, 1⟩, ⟨4, some 6, 4⟩]))
                                  (.split false ⟨.hat, 4, 5, false⟩
                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨3, none, 2⟩, ⟨2, some 6, 1⟩, ⟨4, some 5, 0⟩]))
                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, -2⟩, ⟨3, none, 2⟩, ⟨5, none, -1⟩, ⟨4, some 6, 4⟩]))))))))
                        (.split false ⟨.spoke, 1, 6, true⟩
                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨6, none, 1⟩, ⟨4, some 5, 2⟩]))
                          (.split false ⟨.hat, 3, 6, false⟩
                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨1, some 6, 2⟩, ⟨4, some 5, 2⟩]))
                            (.split false ⟨.fan1, 2, 5, true⟩
                              (.terminal .reducible)
                              (.split false ⟨.hat, 3, 5, false⟩
                                (.split false ⟨.spoke, 1, 7, true⟩
                                  (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 2⟩, ⟨0, some 1, 2⟩, ⟨4, some 5, 2⟩]))
                                  (.split false ⟨.spoke, 4, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, -1⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, some 6, 4⟩]))
                                    (.split false ⟨.spoke, 5, 7, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, -1⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨4, some 5, 1⟩]))
                                      (.split false ⟨.hat, 1, 5, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, -1⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 2⟩, ⟨4, some 5, 2⟩]))
                                        (.split false ⟨.hat, 4, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, -1⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, some 6, 4⟩]))
                                          (.split false ⟨.hat, 6, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.hat, 5, 5, true⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, -1⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨4, some 5, 1⟩]))
                                              (.split false ⟨.hat, 6, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, -1⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, -1⟩, ⟨6, none, 3⟩]))
                                                (.split false ⟨.hat, 0, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, -1⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩]))
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, -1⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨4, some 5, 1⟩])))))))))))
                                (.split false ⟨.spoke, 4, 7, false⟩
                                  (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 0⟩, ⟨0, some 1, 1⟩, ⟨5, some 6, 3⟩]))
                                  (.split false ⟨.spoke, 5, 7, false⟩
                                    (.terminal (.hubcap [⟨3, none, 3⟩, ⟨0, some 1, 1⟩, ⟨2, some 5, 2⟩, ⟨4, some 6, 4⟩]))
                                    (.split false ⟨.hat, 1, 5, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, -2⟩, ⟨3, none, 3⟩, ⟨2, some 5, 3⟩, ⟨4, some 6, 3⟩]))
                                      (.split false ⟨.hat, 4, 5, false⟩
                                        (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 1⟩, ⟨0, some 1, 1⟩, ⟨5, some 6, 3⟩]))
                                        (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨5, none, -1⟩, ⟨0, some 1, 1⟩, ⟨4, some 6, 4⟩])))))))))))))
                  (.split false ⟨.spoke, 6, 6, false⟩
                    (.similar 0 ⟨true, 3⟩)
                    (.split false ⟨.spoke, 5, 6, true⟩
                      (.terminal .reducible)
                      (.split true ⟨.hat, 4, 5, false⟩
                        (.split true ⟨.spoke, 1, 7, false⟩
                          (.split false ⟨.spoke, 2, 7, false⟩
                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, -1⟩, ⟨6, none, 3⟩]))
                            (.split false ⟨.spoke, 2, 6, false⟩
                              (.split false ⟨.spoke, 5, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, -2⟩, ⟨6, none, 3⟩]))
                                (.split false ⟨.hat, 5, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.hat, 6, 5, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.hat, 1, 5, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, -1⟩, ⟨6, none, 2⟩]))
                                      (.split false ⟨.hat, 3, 5, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, -1⟩, ⟨6, none, 3⟩]))
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, -1⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, -1⟩, ⟨6, none, 3⟩])))))))
                              (.split false ⟨.spoke, 5, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, -1⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, -2⟩, ⟨6, none, 3⟩]))
                                (.split false ⟨.hat, 5, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.hat, 6, 5, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.hat, 1, 5, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, -1⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, -1⟩, ⟨6, none, 2⟩]))
                                      (.split false ⟨.hat, 3, 5, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, -1⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, -1⟩, ⟨6, none, 3⟩]))
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, -2⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, -1⟩, ⟨6, none, 3⟩])))))))))
                          (.split false ⟨.hat, 0, 6, false⟩
                            (.terminal (.hubcap [⟨4, none, 2⟩, ⟨5, none, -1⟩, ⟨6, none, 1⟩, ⟨0, some 2, 4⟩, ⟨1, some 3, 4⟩]))
                            (.split false ⟨.fan1, 6, 5, true⟩
                              (.terminal .reducible)
                              (.split true ⟨.spoke, 2, 6, true⟩
                                (.split false ⟨.hat, 2, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.spoke, 1, 6, false⟩
                                    (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, -1⟩, ⟨6, none, 2⟩, ⟨0, some 1, 2⟩]))
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, -1⟩, ⟨6, none, 1⟩]))))
                                (.split false ⟨.spoke, 1, 6, false⟩
                                  (.split false ⟨.spoke, 2, 7, true⟩
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 2⟩, ⟨5, none, -1⟩, ⟨1, some 2, 2⟩, ⟨4, some 6, 4⟩]))
                                    (.split false ⟨.hat, 0, 5, false⟩
                                      (.similar 1 ⟨true, 3⟩)
                                      (.split false ⟨.spoke, 5, 7, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, -2⟩, ⟨6, none, 3⟩]))
                                        (.split false ⟨.hat, 5, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.hat, 6, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.hat, 1, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, -1⟩, ⟨6, none, 2⟩]))
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, -1⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, -1⟩, ⟨6, none, 3⟩]))))))))
                                  (.split false ⟨.hat, 0, 5, false⟩
                                    (.similar 0 ⟨true, 3⟩)
                                    (.split false ⟨.spoke, 2, 7, true⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, -1⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, some 6, 1⟩]))
                                      (.split false ⟨.hat, 1, 5, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, -1⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, -1⟩, ⟨6, none, 2⟩]))
                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, -2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, -2⟩, ⟨6, none, 3⟩]))))))))))
                        (.split false ⟨.hat, 0, 5, false⟩
                          (.similar 0 ⟨true, 3⟩)
                          (.split false ⟨.fan1, 4, 5, true⟩
                            (.terminal .reducible)
                            (.split false ⟨.fan1, 6, 5, true⟩
                              (.terminal .reducible)
                              (.split true ⟨.spoke, 1, 6, true⟩
                                (.split false ⟨.spoke, 2, 6, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.hat, 1, 5, true⟩
                                    (.terminal .reducible)
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, -1⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, -2⟩, ⟨6, none, 2⟩]))))
                                (.split false ⟨.spoke, 2, 6, true⟩
                                  (.similar 0 ⟨true, 3⟩)
                                  (.split false ⟨.hat, 1, 5, false⟩
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, -2⟩, ⟨6, none, 2⟩, ⟨1, some 2, 1⟩]))
                                    (.split false ⟨.spoke, 1, 7, true⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, -1⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, -2⟩, ⟨6, none, 3⟩]))
                                      (.split false ⟨.spoke, 2, 7, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, -2⟩, ⟨6, none, 3⟩]))
                                        (.split false ⟨.hat, 3, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 1⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, -2⟩, ⟨6, none, 3⟩]))
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, -1⟩, ⟨2, none, 1⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, -2⟩, ⟨6, none, 3⟩]))))))))))))))))
              (.split false ⟨.spoke, 4, 5, true⟩
                (.similar 0 ⟨false, 4⟩)
                (.split true ⟨.hat, 3, 5, true⟩
                  (.split true ⟨.spoke, 1, 7, false⟩
                    (.split false ⟨.spoke, 3, 7, false⟩
                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, some 6, 5⟩]))
                      (.split false ⟨.spoke, 6, 7, false⟩
                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨6, none, 0⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 4⟩]))
                        (.split false ⟨.spoke, 2, 6, true⟩
                          (.split false ⟨.spoke, 4, 7, false⟩
                            (.split false ⟨.spoke, 3, 6, false⟩
                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, some 6, 5⟩]))
                              (.split false ⟨.spoke, 5, 6, false⟩
                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨4, none, 0⟩, ⟨2, some 3, 3⟩, ⟨5, some 6, 4⟩]))
                                (.split false ⟨.spoke, 6, 6, false⟩
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩]))
                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨4, none, -1⟩, ⟨2, some 3, 3⟩, ⟨5, some 6, 5⟩])))))
                            (.split false ⟨.spoke, 5, 8, false⟩
                              (.split false ⟨.spoke, 3, 6, false⟩
                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 4⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩]))
                                (.split false ⟨.spoke, 4, 6, false⟩
                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨5, none, 0⟩, ⟨2, some 3, 3⟩, ⟨4, some 6, 4⟩]))
                                  (.split false ⟨.spoke, 6, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨3, some 4, 4⟩]))
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨5, none, -1⟩, ⟨2, some 3, 4⟩, ⟨4, some 6, 4⟩])))))
                              (.split false ⟨.hat, 6, 6, false⟩
                                (.split false ⟨.spoke, 3, 6, false⟩
                                  (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨5, some 6, 3⟩, ⟨0, some 3, 6⟩, ⟨0, some 4, 4⟩, ⟨3, some 4, 5⟩]))
                                  (.split false ⟨.spoke, 4, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨5, none, 0⟩, ⟨2, some 3, 3⟩, ⟨4, some 6, 4⟩]))
                                    (.split false ⟨.spoke, 5, 6, true⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨4, none, 2⟩, ⟨2, some 3, 4⟩, ⟨5, some 6, 2⟩]))
                                      (.split false ⟨.spoke, 6, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, some 4, 4⟩, ⟨5, some 6, 2⟩]))
                                        (.terminal (.hubcap [⟨1, none, 0⟩, ⟨0, some 4, 4⟩, ⟨2, some 3, 4⟩, ⟨5, some 6, 2⟩]))))))
                                (.split false ⟨.spoke, 3, 6, false⟩
                                  (.split false ⟨.spoke, 5, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨4, none, 0⟩, ⟨6, none, 3⟩, ⟨3, some 5, 4⟩]))
                                    (.split false ⟨.spoke, 4, 6, false⟩
                                      (.split false ⟨.spoke, 5, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, some 6, 5⟩]))
                                        (.split false ⟨.spoke, 6, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩]))
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, some 6, 5⟩]))))
                                      (.split false ⟨.spoke, 5, 6, true⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, some 5, 4⟩, ⟨4, some 6, 4⟩]))
                                        (.split false ⟨.spoke, 6, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 4⟩, ⟨4, none, 0⟩, ⟨5, some 6, 3⟩]))
                                          (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨4, none, 0⟩, ⟨0, some 3, 6⟩, ⟨5, some 6, 4⟩]))))))
                                  (.split false ⟨.spoke, 4, 6, false⟩
                                    (.split false ⟨.spoke, 6, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨2, some 3, 3⟩]))
                                      (.split false ⟨.spoke, 5, 6, false⟩
                                        (.terminal (.hubcap [⟨1, none, 0⟩, ⟨0, some 4, 4⟩, ⟨2, some 3, 3⟩, ⟨5, some 6, 3⟩]))
                                        (.terminal (.hubcap [⟨1, none, 0⟩, ⟨0, some 4, 2⟩, ⟨2, some 3, 3⟩, ⟨5, some 6, 5⟩]))))
                                    (.split false ⟨.hat, 4, 6, false⟩
                                      (.terminal (.hubcap [⟨1, none, 0⟩, ⟨0, some 4, 3⟩, ⟨2, some 3, 3⟩, ⟨5, some 6, 4⟩]))
                                      (.split false ⟨.spoke, 5, 6, true⟩
                                        (.split false ⟨.spoke, 6, 6, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.hat, 4, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 1⟩, ⟨3, none, 3⟩, ⟨5, none, 1⟩, ⟨4, some 6, 3⟩]))))
                                        (.split false ⟨.spoke, 6, 6, false⟩
                                          (.split false ⟨.spoke, 5, 7, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨3, some 4, 4⟩]))
                                            (.split false ⟨.hat, 4, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 1⟩, ⟨3, none, 3⟩, ⟨4, none, 1⟩, ⟨5, some 6, 3⟩]))))
                                          (.split false ⟨.spoke, 5, 7, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨5, none, -1⟩, ⟨2, some 3, 4⟩, ⟨4, some 6, 4⟩]))
                                            (.split false ⟨.hat, 4, 5, false⟩
                                              (.terminal (.hubcap [⟨1, none, 0⟩, ⟨0, some 2, 4⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                              (.split false ⟨.fan1, 3, 6, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.hat, 1, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 1⟩, ⟨3, none, 3⟩, ⟨4, none, 1⟩, ⟨5, some 6, 2⟩]))
                                                  (.split false ⟨.hat, 5, 6, true⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 1⟩, ⟨3, none, 3⟩, ⟨4, none, 1⟩, ⟨5, some 6, 2⟩]))
                                                    (.split false ⟨.hat, 6, 5, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 1⟩, ⟨3, none, 3⟩, ⟨4, none, 1⟩, ⟨5, some 6, 2⟩]))
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 1⟩, ⟨3, none, 3⟩, ⟨4, none, 1⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩]))))))))))))))))
                          (.split false ⟨.spoke, 4, 7, false⟩
                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, some 6, 5⟩]))
                            (.split false ⟨.spoke, 6, 6, false⟩
                              (.split false ⟨.spoke, 2, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, some 4, 4⟩, ⟨5, some 6, 4⟩]))
                                (.split false ⟨.spoke, 3, 6, false⟩
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, some 6, 4⟩]))
                                  (.split false ⟨.spoke, 4, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨5, none, 0⟩, ⟨4, some 6, 5⟩]))
                                    (.split false ⟨.spoke, 5, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                      (.split false ⟨.hat, 4, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, some 6, 4⟩]))
                                        (.split false ⟨.hat, 4, 5, true⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨3, none, 2⟩, ⟨2, some 5, 3⟩, ⟨4, some 6, 3⟩]))
                                          (.split false ⟨.hat, 5, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, some 4, 2⟩, ⟨5, some 6, 4⟩]))
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨5, some 6, 2⟩])))))))))
                              (.split false ⟨.spoke, 5, 8, false⟩
                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨5, none, -1⟩, ⟨6, none, 3⟩, ⟨3, some 4, 3⟩]))
                                (.split false ⟨.spoke, 3, 6, false⟩
                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, some 4, 2⟩, ⟨5, some 6, 5⟩]))
                                  (.split false ⟨.spoke, 5, 6, true⟩
                                    (.split false ⟨.spoke, 2, 7, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, some 4, 2⟩, ⟨5, some 6, 5⟩]))
                                      (.split false ⟨.spoke, 4, 6, false⟩
                                        (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨0, some 4, 3⟩, ⟨5, some 6, 5⟩]))
                                        (.terminal (.hubcap [⟨1, none, 0⟩, ⟨0, some 3, 3⟩, ⟨2, some 4, 2⟩, ⟨5, some 6, 5⟩]))))
                                    (.split false ⟨.spoke, 2, 7, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 4⟩]))
                                      (.split false ⟨.hat, 4, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩]))
                                        (.split false ⟨.hat, 6, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 2⟩]))
                                          (.split false ⟨.hat, 0, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                            (.split false ⟨.fan1, 6, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.hat, 1, 5, false⟩
                                                (.split false ⟨.spoke, 4, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨6, none, 2⟩, ⟨4, some 5, 3⟩]))
                                                  (.split false ⟨.spoke, 5, 7, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, -1⟩, ⟨6, none, 2⟩]))
                                                    (.split false ⟨.hat, 4, 5, true⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩]))
                                                      (.split false ⟨.hat, 5, 6, true⟩
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩, ⟨3, some 4, 2⟩]))
                                                        (.split false ⟨.hat, 6, 5, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩, ⟨3, some 4, 2⟩]))
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩, ⟨3, some 4, 1⟩])))))))
                                                (.split false ⟨.spoke, 4, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨6, none, 3⟩, ⟨4, some 5, 2⟩]))
                                                  (.split false ⟨.spoke, 5, 7, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨5, none, -1⟩, ⟨6, none, 3⟩, ⟨3, some 4, 3⟩]))
                                                    (.split false ⟨.hat, 5, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.hat, 4, 5, true⟩
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, -1⟩, ⟨6, none, 3⟩]))
                                                        (.split false ⟨.hat, 6, 5, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨3, some 4, 2⟩]))
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩, ⟨3, some 4, 1⟩])))))))))))))))))))))
                    (.split false ⟨.spoke, 6, 7, false⟩
                      (.split false ⟨.hat, 5, 5, true⟩
                        (.similar 0 ⟨true, 6⟩)
                        (.split false ⟨.spoke, 3, 7, false⟩
                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 0⟩, ⟨6, none, 0⟩, ⟨1, some 2, 5⟩, ⟨4, some 5, 2⟩]))
                          (.split false ⟨.spoke, 4, 7, false⟩
                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩, ⟨2, some 3, 3⟩]))
                            (.split false ⟨.spoke, 3, 6, false⟩
                              (.split false ⟨.spoke, 1, 6, false⟩
                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 0⟩, ⟨6, none, 0⟩, ⟨1, some 3, 5⟩, ⟨4, some 5, 2⟩]))
                                (.split false ⟨.spoke, 2, 7, false⟩
                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -1⟩, ⟨3, none, 2⟩, ⟨6, none, 0⟩, ⟨4, some 5, 2⟩]))
                                  (.split false ⟨.spoke, 2, 6, true⟩
                                    (.terminal (.hubcap [⟨6, none, 0⟩, ⟨0, some 3, 3⟩, ⟨1, some 2, 5⟩, ⟨4, some 5, 2⟩]))
                                    (.split false ⟨.spoke, 4, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩]))
                                      (.split false ⟨.spoke, 5, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 0⟩]))
                                        (.split false ⟨.hat, 1, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨6, none, 0⟩, ⟨4, some 5, 2⟩]))
                                          (.split false ⟨.fan1, 1, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.hat, 2, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 2⟩, ⟨6, none, 0⟩, ⟨1, some 2, 3⟩, ⟨4, some 5, 2⟩]))
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨6, none, 0⟩, ⟨4, some 5, 2⟩]))))))))))
                              (.split false ⟨.spoke, 2, 6, true⟩
                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨6, none, 0⟩, ⟨1, some 3, 3⟩, ⟨4, some 5, 3⟩]))
                                (.split false ⟨.spoke, 5, 7, false⟩
                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩, ⟨1, some 2, 4⟩, ⟨3, some 4, 3⟩]))
                                  (.split false ⟨.spoke, 1, 6, false⟩
                                    (.split false ⟨.spoke, 2, 7, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨6, none, 0⟩, ⟨4, some 5, 4⟩]))
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨6, none, 0⟩, ⟨2, some 5, 3⟩, ⟨3, some 4, 4⟩])))
                                    (.split false ⟨.spoke, 4, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 4⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩, ⟨1, some 2, 3⟩]))
                                      (.split false ⟨.spoke, 5, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨5, none, 1⟩, ⟨6, none, 0⟩, ⟨1, some 2, 3⟩, ⟨3, some 4, 3⟩]))
                                        (.split false ⟨.spoke, 2, 7, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -1⟩, ⟨3, none, 2⟩, ⟨6, none, 0⟩, ⟨4, some 5, 3⟩]))
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨6, none, 0⟩, ⟨2, some 3, 2⟩, ⟨4, some 5, 3⟩]))))))))))))
                      (.split true ⟨.spoke, 3, 7, false⟩
                        (.split false ⟨.spoke, 6, 6, false⟩
                          (.split false ⟨.spoke, 1, 6, false⟩
                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, some 5, 3⟩, ⟨4, some 6, 4⟩, ⟨5, some 6, 4⟩]))
                            (.split false ⟨.spoke, 2, 7, false⟩
                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, -1⟩, ⟨3, none, 0⟩, ⟨1, some 4, 4⟩, ⟨5, some 6, 4⟩]))
                              (.split false ⟨.spoke, 5, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨1, some 2, 5⟩]))
                                (.split false ⟨.spoke, 2, 6, false⟩
                                  (.split false ⟨.spoke, 4, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨1, some 6, 6⟩]))
                                    (.split false ⟨.spoke, 5, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, some 6, 3⟩]))
                                      (.split false ⟨.hat, 1, 5, false⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨1, some 4, 3⟩, ⟨5, some 6, 4⟩]))
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 0⟩, ⟨2, some 6, 2⟩, ⟨1, some 4, 4⟩, ⟨1, some 5, 4⟩, ⟨4, some 5, 3⟩])))))
                                  (.split false ⟨.spoke, 4, 7, false⟩
                                    (.terminal (.hubcap [⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨0, some 6, 6⟩, ⟨1, some 2, 5⟩]))
                                    (.split false ⟨.spoke, 5, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨1, some 2, 5⟩, ⟨5, some 6, 3⟩]))
                                      (.split false ⟨.hat, 1, 5, false⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, -1⟩, ⟨1, some 2, 4⟩, ⟨4, some 5, 3⟩, ⟨4, some 6, 4⟩, ⟨5, some 6, 4⟩]))
                                        (.split false ⟨.hat, 6, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.fan1, 1, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.spoke, 4, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, -1⟩, ⟨5, none, 0⟩, ⟨1, some 2, 5⟩, ⟨4, some 6, 3⟩]))
                                              (.split false ⟨.hat, 2, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, -1⟩, ⟨4, none, 2⟩, ⟨5, some 6, 3⟩]))
                                                (.split false ⟨.hat, 2, 5, true⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, -1⟩, ⟨1, some 4, 5⟩, ⟨5, some 6, 2⟩]))
                                                  (.split false ⟨.hat, 5, 5, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, -1⟩, ⟨4, some 5, 2⟩, ⟨1, some 2, 5⟩, ⟨1, some 6, 5⟩, ⟨2, some 6, 3⟩]))
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, -1⟩, ⟨1, some 2, 5⟩, ⟨4, some 5, 3⟩, ⟨4, some 6, 2⟩, ⟨5, some 6, 2⟩])))))))))))))))
                          (.split false ⟨.spoke, 5, 7, false⟩
                            (.terminal (.hubcap [⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨6, none, 3⟩, ⟨0, some 5, 3⟩, ⟨1, some 2, 4⟩]))
                            (.split false ⟨.spoke, 5, 6, false⟩
                              (.split false ⟨.spoke, 1, 6, false⟩
                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, some 6, 4⟩]))
                                (.split false ⟨.spoke, 2, 7, false⟩
                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, -1⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, some 6, 4⟩]))
                                  (.split false ⟨.spoke, 2, 6, false⟩
                                    (.split false ⟨.hat, 1, 5, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩]))
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨2, some 6, 3⟩])))
                                    (.split false ⟨.hat, 1, 5, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨2, some 6, 3⟩]))
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨1, some 2, 4⟩]))))))
                              (.split false ⟨.fan1, 6, 5, true⟩
                                (.split false ⟨.hat, 0, 6, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.spoke, 1, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩]))
                                    (.split false ⟨.spoke, 2, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨6, none, 2⟩, ⟨1, some 5, 3⟩]))
                                      (.terminal (.hubcap [⟨3, none, -1⟩, ⟨4, none, 1⟩, ⟨6, none, 2⟩, ⟨0, some 5, 4⟩, ⟨1, some 2, 4⟩])))))
                                (.split false ⟨.hat, 6, 5, true⟩
                                  (.split false ⟨.spoke, 1, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨5, none, 1⟩, ⟨1, some 6, 5⟩]))
                                    (.split false ⟨.hat, 1, 5, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.spoke, 2, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨5, none, 1⟩, ⟨4, some 6, 4⟩]))
                                        (.terminal (.hubcap [⟨3, none, -1⟩, ⟨5, none, 1⟩, ⟨4, some 6, 4⟩, ⟨0, some 1, 5⟩, ⟨0, some 2, 4⟩, ⟨1, some 2, 4⟩])))))
                                  (.split false ⟨.spoke, 4, 6, false⟩
                                    (.split false ⟨.spoke, 1, 6, false⟩
                                      (.terminal (.hubcap [⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨0, some 1, 5⟩, ⟨5, some 6, 5⟩]))
                                      (.split false ⟨.spoke, 2, 7, false⟩
                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, -1⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, some 6, 4⟩]))
                                        (.split false ⟨.spoke, 2, 6, false⟩
                                          (.split false ⟨.spoke, 4, 7, false⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, -1⟩, ⟨1, some 2, 3⟩, ⟨5, some 6, 4⟩]))
                                            (.split false ⟨.hat, 1, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, some 6, 4⟩]))
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨2, some 6, 3⟩]))))
                                          (.split false ⟨.spoke, 4, 7, false⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, -1⟩, ⟨4, none, -1⟩, ⟨1, some 2, 4⟩, ⟨5, some 6, 4⟩]))
                                            (.split false ⟨.hat, 1, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨1, some 2, 4⟩, ⟨5, some 6, 4⟩]))
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨1, some 2, 4⟩])))))))
                                    (.split false ⟨.spoke, 1, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨1, some 5, 4⟩, ⟨4, some 6, 3⟩]))
                                      (.split false ⟨.spoke, 2, 7, false⟩
                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨2, none, -1⟩, ⟨3, none, 0⟩, ⟨1, some 4, 3⟩, ⟨5, some 6, 4⟩]))
                                        (.split false ⟨.spoke, 2, 6, false⟩
                                          (.split false ⟨.hat, 1, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨1, some 2, 2⟩, ⟨5, some 6, 4⟩]))
                                            (.terminal (.hubcap [⟨3, none, 0⟩, ⟨0, some 2, 4⟩, ⟨1, some 4, 3⟩, ⟨5, some 6, 3⟩])))
                                          (.split false ⟨.hat, 1, 5, false⟩
                                            (.terminal (.hubcap [⟨3, none, -1⟩, ⟨0, some 4, 3⟩, ⟨1, some 2, 4⟩, ⟨5, some 6, 4⟩]))
                                            (.terminal (.hubcap [⟨3, none, -1⟩, ⟨0, some 4, 4⟩, ⟨1, some 2, 4⟩, ⟨5, some 6, 3⟩]))))))))))))
                        (.split false ⟨.spoke, 4, 7, false⟩
                          (.split false ⟨.hat, 5, 5, true⟩
                            (.similar 0 ⟨true, 6⟩)
                            (.split false ⟨.spoke, 6, 6, false⟩
                              (.split false ⟨.spoke, 2, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩]))
                                (.split false ⟨.spoke, 3, 6, true⟩
                                  (.split false ⟨.spoke, 1, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨3, some 6, 5⟩]))
                                    (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨0, some 3, 3⟩, ⟨0, some 6, 6⟩, ⟨3, some 6, 4⟩])))
                                  (.split false ⟨.spoke, 1, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨1, some 3, 4⟩]))
                                    (.split false ⟨.spoke, 2, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨1, some 6, 6⟩]))
                                      (.split false ⟨.fan1, 3, 5, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.spoke, 5, 6, false⟩
                                          (.terminal (.hubcap [⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨0, some 6, 5⟩, ⟨1, some 2, 5⟩]))
                                          (.split false ⟨.hat, 1, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨2, some 6, 5⟩]))
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨2, some 6, 3⟩])))))))))
                              (.split false ⟨.spoke, 5, 6, false⟩
                                (.split false ⟨.hat, 1, 5, false⟩
                                  (.split false ⟨.spoke, 2, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩, ⟨1, some 2, 3⟩]))
                                    (.split false ⟨.spoke, 3, 6, true⟩
                                      (.terminal (.hubcap [⟨4, none, 0⟩, ⟨0, some 1, 4⟩, ⟨2, some 3, 3⟩, ⟨5, some 6, 3⟩]))
                                      (.split false ⟨.spoke, 5, 7, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨1, some 3, 4⟩, ⟨2, some 6, 3⟩]))
                                        (.split false ⟨.spoke, 1, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩, ⟨1, some 3, 3⟩]))
                                          (.terminal (.hubcap [⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨0, some 1, 5⟩, ⟨2, some 6, 3⟩]))))))
                                  (.split false ⟨.spoke, 2, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨6, none, 3⟩, ⟨1, some 5, 3⟩]))
                                    (.split false ⟨.spoke, 3, 6, true⟩
                                      (.terminal (.hubcap [⟨4, none, 0⟩, ⟨0, some 5, 4⟩, ⟨1, some 3, 2⟩, ⟨2, some 6, 4⟩]))
                                      (.split false ⟨.spoke, 1, 6, false⟩
                                        (.terminal (.hubcap [⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨0, some 1, 5⟩, ⟨5, some 6, 4⟩]))
                                        (.split false ⟨.fan1, 1, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.spoke, 2, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨2, some 6, 3⟩]))
                                            (.split false ⟨.fan1, 3, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.spoke, 5, 7, false⟩
                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, -1⟩, ⟨6, none, 3⟩, ⟨1, some 2, 4⟩]))
                                                (.split false ⟨.hat, 2, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩]))
                                                  (.split false ⟨.hat, 2, 5, true⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩]))
                                                    (.split false ⟨.hat, 6, 5, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, -1⟩, ⟨6, none, 3⟩, ⟨1, some 2, 4⟩]))
                                                      (.split false ⟨.fan2, 5, 5, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.hat, 0, 5, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨1, some 2, 4⟩]))
                                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩])))))))))))))))
                                (.split false ⟨.spoke, 2, 7, false⟩
                                  (.terminal (.hubcap [⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, -1⟩, ⟨0, some 5, 5⟩, ⟨1, some 6, 6⟩]))
                                  (.split false ⟨.spoke, 1, 6, false⟩
                                    (.split false ⟨.spoke, 2, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, -1⟩, ⟨1, some 2, 3⟩, ⟨5, some 6, 5⟩]))
                                      (.split false ⟨.spoke, 3, 6, true⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨4, none, -1⟩, ⟨5, some 6, 5⟩, ⟨1, some 2, 2⟩, ⟨1, some 3, 2⟩, ⟨2, some 3, 3⟩]))
                                        (.split false ⟨.hat, 1, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, -1⟩, ⟨5, none, 2⟩, ⟨1, some 6, 4⟩]))
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, -1⟩, ⟨5, none, 2⟩, ⟨1, some 6, 5⟩])))))
                                    (.split false ⟨.spoke, 2, 6, false⟩
                                      (.terminal (.hubcap [⟨3, none, 0⟩, ⟨4, none, -1⟩, ⟨0, some 2, 4⟩, ⟨1, some 5, 4⟩, ⟨1, some 6, 6⟩, ⟨5, some 6, 5⟩]))
                                      (.split false ⟨.spoke, 3, 6, true⟩
                                        (.terminal (.hubcap [⟨3, none, 1⟩, ⟨4, none, -1⟩, ⟨5, some 6, 5⟩, ⟨0, some 1, 4⟩, ⟨0, some 2, 4⟩, ⟨1, some 2, 3⟩]))
                                        (.split false ⟨.fan1, 3, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.hat, 1, 5, false⟩
                                            (.terminal (.hubcap [⟨3, none, 0⟩, ⟨4, none, -1⟩, ⟨5, some 6, 5⟩, ⟨0, some 1, 5⟩, ⟨0, some 2, 4⟩, ⟨1, some 2, 4⟩]))
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, -1⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨1, some 2, 4⟩])))))))))))
                          (.split true ⟨.spoke, 5, 7, false⟩
                            (.split false ⟨.spoke, 2, 7, false⟩
                              (.split true ⟨.spoke, 6, 6, false⟩
                                (.split false ⟨.spoke, 1, 6, false⟩
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩]))
                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -1⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨3, some 4, 3⟩])))
                                (.split false ⟨.spoke, 1, 6, false⟩
                                  (.split false ⟨.hat, 5, 5, true⟩
                                    (.similar 0 ⟨true, 6⟩)
                                    (.split false ⟨.spoke, 3, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩]))
                                      (.split false ⟨.spoke, 4, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩]))
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨5, none, -1⟩, ⟨6, none, 3⟩, ⟨3, some 4, 3⟩])))))
                                  (.split false ⟨.spoke, 3, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, -1⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, some 6, 2⟩]))
                                    (.split false ⟨.spoke, 4, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, -1⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, some 6, 2⟩]))
                                      (.split false ⟨.hat, 1, 5, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, -1⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, -1⟩, ⟨6, none, 2⟩]))
                                        (.split false ⟨.fan1, 1, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.hat, 4, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, -1⟩, ⟨5, none, -1⟩, ⟨6, none, 3⟩, ⟨3, some 4, 2⟩]))
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, -1⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, -1⟩, ⟨6, none, 2⟩])))))))))
                              (.split false ⟨.spoke, 6, 6, false⟩
                                (.split false ⟨.spoke, 3, 6, false⟩
                                  (.split false ⟨.spoke, 1, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨1, some 3, 5⟩]))
                                    (.split false ⟨.spoke, 2, 6, true⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨1, some 3, 4⟩, ⟨2, some 6, 3⟩]))
                                      (.split false ⟨.spoke, 4, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩]))
                                        (.split false ⟨.hat, 1, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩]))
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨2, some 6, 2⟩]))))))
                                  (.split false ⟨.spoke, 1, 6, false⟩
                                    (.split false ⟨.spoke, 2, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨3, some 4, 3⟩]))
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨1, some 2, 2⟩, ⟨3, some 4, 4⟩])))
                                    (.split false ⟨.hat, 2, 5, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.spoke, 2, 6, false⟩
                                        (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨5, none, 0⟩, ⟨0, some 6, 4⟩, ⟨3, some 4, 3⟩]))
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩]))))))
                                (.split false ⟨.fan1, 6, 5, true⟩
                                  (.split false ⟨.hat, 0, 6, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.spoke, 1, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨5, none, -1⟩, ⟨6, none, 1⟩, ⟨1, some 2, 3⟩, ⟨3, some 4, 4⟩]))
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨5, none, -1⟩, ⟨6, none, 1⟩, ⟨1, some 2, 4⟩, ⟨3, some 4, 3⟩]))))
                                  (.split false ⟨.hat, 2, 5, true⟩
                                    (.split false ⟨.spoke, 2, 6, true⟩
                                      (.terminal (.hubcap [⟨1, none, 3⟩, ⟨4, none, 0⟩, ⟨6, none, 2⟩, ⟨0, some 5, 2⟩, ⟨2, some 3, 3⟩]))
                                      (.split false ⟨.spoke, 4, 6, false⟩
                                        (.terminal (.hubcap [⟨3, none, 0⟩, ⟨0, some 5, 3⟩, ⟨1, some 4, 3⟩, ⟨2, some 6, 4⟩]))
                                        (.split false ⟨.spoke, 1, 6, true⟩
                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, -1⟩, ⟨2, some 6, 3⟩]))
                                          (.split false ⟨.spoke, 3, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, -1⟩, ⟨6, none, 3⟩]))
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨5, none, -1⟩, ⟨2, some 6, 4⟩, ⟨3, some 4, 3⟩]))))))
                                    (.split false ⟨.hat, 4, 6, false⟩
                                      (.split false ⟨.spoke, 1, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨1, some 2, 3⟩, ⟨3, some 6, 4⟩]))
                                        (.split false ⟨.spoke, 2, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, some 6, 2⟩]))
                                          (.split false ⟨.spoke, 3, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨1, some 2, 4⟩, ⟨5, some 6, 2⟩]))
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩])))))
                                      (.split false ⟨.hat, 0, 6, false⟩
                                        (.split false ⟨.spoke, 1, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩, ⟨1, some 2, 3⟩, ⟨3, some 4, 4⟩]))
                                          (.terminal (.hubcap [⟨6, none, 1⟩, ⟨0, some 5, 2⟩, ⟨1, some 2, 4⟩, ⟨3, some 4, 3⟩])))
                                        (.split false ⟨.spoke, 3, 6, false⟩
                                          (.split false ⟨.spoke, 1, 6, false⟩
                                            (.terminal (.hubcap [⟨2, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨0, some 1, 5⟩, ⟨3, some 6, 5⟩]))
                                            (.split false ⟨.spoke, 2, 6, true⟩
                                              (.terminal (.hubcap [⟨4, none, 0⟩, ⟨0, some 3, 4⟩, ⟨1, some 2, 4⟩, ⟨5, some 6, 2⟩]))
                                              (.split false ⟨.spoke, 4, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, some 6, 2⟩]))
                                                (.split false ⟨.hat, 1, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, -1⟩, ⟨6, none, 2⟩]))
                                                  (.split false ⟨.fan1, 1, 5, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.hat, 2, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, -1⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, -1⟩, ⟨6, none, 3⟩]))
                                                      (.split false ⟨.hat, 4, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, -1⟩, ⟨2, some 6, 3⟩]))
                                                        (.split false ⟨.hat, 0, 5, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, -1⟩, ⟨6, none, 2⟩]))
                                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, -1⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, -1⟩, ⟨6, none, 3⟩]))))))))))
                                          (.split false ⟨.spoke, 2, 6, true⟩
                                            (.split false ⟨.spoke, 1, 6, true⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 0⟩, ⟨2, some 6, 3⟩]))
                                              (.split false ⟨.spoke, 4, 6, false⟩
                                                (.terminal (.hubcap [⟨5, none, 0⟩, ⟨0, some 4, 4⟩, ⟨1, some 2, 2⟩, ⟨3, some 6, 4⟩]))
                                                (.split false ⟨.hat, 1, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨5, none, -1⟩, ⟨4, some 6, 3⟩]))
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨5, none, -1⟩, ⟨6, none, 3⟩, ⟨3, some 4, 3⟩])))))
                                            (.split false ⟨.spoke, 1, 6, false⟩
                                              (.split false ⟨.spoke, 4, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨2, some 6, 4⟩]))
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨5, none, -1⟩, ⟨2, some 6, 4⟩, ⟨3, some 4, 3⟩])))
                                              (.split false ⟨.fan2, 2, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.spoke, 4, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩]))
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨5, none, -1⟩, ⟨6, none, 2⟩, ⟨3, some 4, 3⟩])))))))))))))
                            (.split true ⟨.hat, 0, 5, false⟩
                              (.split false ⟨.spoke, 2, 7, false⟩
                                (.split false ⟨.hat, 5, 5, true⟩
                                  (.similar 0 ⟨true, 6⟩)
                                  (.split false ⟨.spoke, 4, 6, false⟩
                                    (.split false ⟨.spoke, 1, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨1, some 6, 4⟩, ⟨4, some 5, 4⟩]))
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, -1⟩, ⟨3, none, 0⟩, ⟨1, some 6, 4⟩, ⟨4, some 5, 4⟩])))
                                    (.split false ⟨.spoke, 1, 6, false⟩
                                      (.split false ⟨.spoke, 6, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                        (.split false ⟨.spoke, 3, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, some 6, 4⟩]))
                                          (.split false ⟨.spoke, 5, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩])))))
                                      (.split false ⟨.spoke, 6, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, -1⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                        (.split false ⟨.spoke, 3, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, -1⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, some 6, 4⟩]))
                                          (.split false ⟨.spoke, 5, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, -1⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, -1⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩]))))))))
                                (.split false ⟨.hat, 4, 6, false⟩
                                  (.split false ⟨.spoke, 1, 6, false⟩
                                    (.split false ⟨.spoke, 2, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 0⟩, ⟨1, some 2, 3⟩, ⟨4, some 5, 3⟩, ⟨4, some 6, 4⟩, ⟨5, some 6, 4⟩]))
                                      (.split false ⟨.spoke, 3, 6, false⟩
                                        (.split false ⟨.spoke, 5, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 0⟩, ⟨4, none, 0⟩, ⟨1, some 3, 4⟩, ⟨5, some 6, 4⟩]))
                                          (.split false ⟨.spoke, 6, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 0⟩, ⟨1, some 3, 4⟩, ⟨4, some 5, 3⟩, ⟨4, some 6, 3⟩, ⟨5, some 6, 3⟩]))
                                            (.split false ⟨.spoke, 4, 6, true⟩
                                              (.terminal .reducible)
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 0⟩, ⟨4, none, 0⟩, ⟨1, some 3, 4⟩, ⟨5, some 6, 4⟩])))))
                                        (.split false ⟨.hat, 2, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.spoke, 4, 6, true⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨6, none, 2⟩, ⟨2, some 3, 3⟩, ⟨4, some 5, 2⟩]))
                                            (.split false ⟨.spoke, 5, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨4, none, 0⟩, ⟨2, some 3, 3⟩, ⟨5, some 6, 4⟩]))
                                              (.split false ⟨.spoke, 6, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨5, none, 0⟩, ⟨4, some 6, 3⟩]))
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, some 4, 1⟩, ⟨5, some 6, 4⟩]))))))))
                                    (.split false ⟨.hat, 1, 5, false⟩
                                      (.split false ⟨.spoke, 2, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, some 6, 4⟩]))
                                        (.split true ⟨.spoke, 3, 6, false⟩
                                          (.split false ⟨.fan1, 3, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.spoke, 5, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨1, some 2, 4⟩, ⟨5, some 6, 4⟩]))
                                              (.split false ⟨.spoke, 6, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 0⟩, ⟨5, none, 1⟩, ⟨1, some 2, 4⟩, ⟨4, some 6, 3⟩]))
                                                (.split false ⟨.spoke, 4, 6, true⟩
                                                  (.terminal .reducible)
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨1, some 2, 4⟩, ⟨5, some 6, 4⟩]))))))
                                          (.split false ⟨.hat, 2, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.fan1, 2, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.fan1, 3, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.spoke, 4, 6, true⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨1, some 2, 3⟩, ⟨5, some 6, 3⟩]))
                                                  (.split false ⟨.hat, 5, 5, true⟩
                                                    (.similar 0 ⟨true, 6⟩)
                                                    (.split false ⟨.spoke, 5, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨1, some 2, 3⟩, ⟨5, some 6, 4⟩]))
                                                      (.split false ⟨.spoke, 6, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨1, some 2, 3⟩, ⟨5, some 6, 4⟩])))))))))))
                                      (.split false ⟨.fan1, 1, 5, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.spoke, 2, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, some 5, 3⟩, ⟨4, some 6, 3⟩, ⟨5, some 6, 3⟩]))
                                          (.split false ⟨.spoke, 3, 6, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.fan1, 3, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.spoke, 4, 6, true⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 0⟩, ⟨1, some 2, 4⟩, ⟨4, some 5, 2⟩, ⟨4, some 6, 2⟩, ⟨5, some 6, 3⟩]))
                                                (.split false ⟨.spoke, 5, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩, ⟨1, some 2, 4⟩]))
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 0⟩, ⟨5, none, 0⟩, ⟨1, some 2, 4⟩, ⟨4, some 6, 3⟩]))))))))))
                                  (.split true ⟨.spoke, 1, 6, false⟩
                                    (.split false ⟨.spoke, 3, 6, false⟩
                                      (.split false ⟨.spoke, 4, 6, false⟩
                                        (.split false ⟨.spoke, 2, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, some 5, 3⟩, ⟨4, some 6, 4⟩, ⟨5, some 6, 4⟩]))
                                          (.split false ⟨.spoke, 5, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 0⟩, ⟨4, none, 0⟩, ⟨1, some 3, 4⟩, ⟨5, some 6, 4⟩]))
                                            (.split false ⟨.spoke, 6, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨5, none, 0⟩, ⟨4, some 6, 3⟩]))
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 0⟩, ⟨4, none, 0⟩, ⟨1, some 3, 4⟩, ⟨5, some 6, 4⟩])))))
                                        (.split false ⟨.hat, 6, 5, true⟩
                                          (.split false ⟨.spoke, 6, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 0⟩, ⟨4, none, 0⟩, ⟨1, some 3, 5⟩, ⟨5, some 6, 3⟩]))
                                            (.split false ⟨.hat, 5, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.spoke, 2, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, some 6, 4⟩]))
                                                (.split false ⟨.spoke, 5, 6, true⟩
                                                  (.terminal .reducible)
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 0⟩, ⟨4, none, 0⟩, ⟨1, some 3, 5⟩, ⟨5, some 6, 3⟩]))))))
                                          (.split false ⟨.spoke, 5, 6, false⟩
                                            (.split false ⟨.spoke, 6, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 1⟩, ⟨1, some 3, 5⟩]))
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩, ⟨1, some 3, 5⟩])))
                                            (.split false ⟨.spoke, 2, 6, true⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 0⟩, ⟨4, none, 1⟩, ⟨1, some 3, 5⟩, ⟨5, some 6, 2⟩]))
                                              (.split false ⟨.spoke, 6, 6, true⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, some 6, 3⟩]))
                                                (.split false ⟨.hat, 1, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨6, none, 1⟩, ⟨4, some 5, 3⟩]))
                                                  (.split false ⟨.hat, 2, 5, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨6, none, 1⟩, ⟨4, some 5, 3⟩]))
                                                    (.split false ⟨.hat, 4, 5, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, some 6, 2⟩]))
                                                      (.split false ⟨.hat, 5, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨6, none, 1⟩, ⟨4, some 5, 2⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 0⟩])))))))))))
                                      (.split false ⟨.fan1, 3, 5, true⟩
                                        (.split false ⟨.hat, 4, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.spoke, 6, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, some 3, 1⟩, ⟨2, some 4, 4⟩, ⟨5, some 6, 3⟩]))
                                            (.split false ⟨.spoke, 5, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, some 6, 2⟩, ⟨4, some 5, 3⟩]))
                                              (.split false ⟨.spoke, 4, 6, true⟩
                                                (.terminal .reducible)
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, some 4, 1⟩, ⟨5, some 6, 4⟩]))))))
                                        (.split false ⟨.fan1, 3, 6, true⟩
                                          (.split false ⟨.hat, 4, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.spoke, 2, 6, false⟩
                                              (.split false ⟨.spoke, 5, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨5, some 6, 4⟩]))
                                                (.split false ⟨.spoke, 6, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨5, none, 1⟩, ⟨4, some 6, 4⟩]))
                                                  (.split false ⟨.spoke, 4, 6, true⟩
                                                    (.terminal .reducible)
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨5, some 6, 4⟩])))))
                                              (.split false ⟨.hat, 2, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.spoke, 4, 6, true⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 1⟩, ⟨6, none, 2⟩, ⟨1, some 3, 2⟩, ⟨4, some 5, 3⟩]))
                                                  (.split false ⟨.spoke, 5, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 1⟩, ⟨4, none, 1⟩, ⟨1, some 3, 2⟩, ⟨5, some 6, 4⟩]))
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 1⟩, ⟨1, some 3, 2⟩, ⟨4, some 5, 3⟩, ⟨4, some 6, 4⟩, ⟨5, some 6, 4⟩])))))))
                                          (.split false ⟨.spoke, 4, 6, false⟩
                                            (.split false ⟨.spoke, 2, 6, false⟩
                                              (.split false ⟨.spoke, 6, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨5, none, 0⟩, ⟨4, some 6, 5⟩]))
                                                (.split false ⟨.spoke, 5, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, some 6, 3⟩]))
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨5, some 6, 4⟩]))))
                                              (.split false ⟨.hat, 2, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.spoke, 5, 6, true⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 1⟩, ⟨1, some 3, 2⟩, ⟨4, some 5, 3⟩, ⟨4, some 6, 4⟩, ⟨5, some 6, 4⟩]))
                                                  (.split false ⟨.spoke, 6, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩]))
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, some 6, 3⟩, ⟨4, some 5, 3⟩]))))))
                                            (.split false ⟨.spoke, 6, 6, false⟩
                                              (.split false ⟨.hat, 1, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨4, some 6, 3⟩, ⟨2, some 3, 4⟩, ⟨2, some 5, 3⟩, ⟨3, some 5, 4⟩]))
                                                (.split false ⟨.hat, 5, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨5, none, 0⟩, ⟨2, some 3, 4⟩, ⟨4, some 6, 3⟩]))
                                                  (.split false ⟨.hat, 4, 5, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨4, some 6, 2⟩, ⟨2, some 3, 4⟩, ⟨2, some 5, 3⟩, ⟨3, some 5, 4⟩]))
                                                    (.split false ⟨.spoke, 2, 6, true⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 1⟩, ⟨3, none, 3⟩, ⟨5, none, 1⟩, ⟨4, some 6, 3⟩]))
                                                      (.split false ⟨.hat, 5, 5, true⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨3, none, 1⟩, ⟨2, some 5, 3⟩, ⟨4, some 6, 3⟩]))
                                                        (.split false ⟨.spoke, 5, 6, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, some 6, 2⟩]))
                                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, some 3, 3⟩, ⟨4, some 5, 3⟩, ⟨4, some 6, 3⟩, ⟨5, some 6, 3⟩]))))))))
                                              (.split false ⟨.spoke, 5, 6, true⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨4, none, 1⟩, ⟨2, some 3, 2⟩, ⟨5, some 6, 4⟩]))
                                                (.split false ⟨.spoke, 2, 6, true⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 3⟩, ⟨5, none, 1⟩, ⟨4, some 6, 2⟩]))
                                                  (.split false ⟨.hat, 1, 5, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨4, none, 1⟩, ⟨6, none, 1⟩, ⟨3, some 5, 3⟩]))
                                                    (.split false ⟨.fan1, 1, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.hat, 4, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, some 6, 3⟩]))
                                                        (.split false ⟨.hat, 5, 6, true⟩
                                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨4, none, 1⟩, ⟨6, none, 2⟩, ⟨3, some 5, 2⟩]))
                                                          (.split false ⟨.hat, 6, 5, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, some 6, 2⟩]))
                                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, some 6, 3⟩]))))))))))))))
                                    (.split false ⟨.spoke, 2, 6, false⟩
                                      (.split false ⟨.spoke, 6, 6, false⟩
                                        (.split false ⟨.hat, 1, 5, false⟩
                                          (.split false ⟨.hat, 5, 5, true⟩
                                            (.similar 0 ⟨true, 6⟩)
                                            (.split false ⟨.spoke, 3, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, some 6, 3⟩]))
                                              (.split false ⟨.hat, 2, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.fan2, 2, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.spoke, 4, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨5, none, 0⟩, ⟨4, some 6, 5⟩]))
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 3⟩])))))))
                                          (.split false ⟨.fan1, 1, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.hat, 2, 5, true⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, some 5, 3⟩, ⟨4, some 6, 2⟩, ⟨5, some 6, 2⟩]))
                                              (.split false ⟨.spoke, 4, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 4⟩, ⟨5, none, 0⟩, ⟨2, some 6, 1⟩]))
                                                (.split false ⟨.hat, 5, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩, ⟨3, some 4, 3⟩]))
                                                  (.split false ⟨.hat, 6, 5, true⟩
                                                    (.split false ⟨.spoke, 5, 6, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.fan2, 5, 5, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.spoke, 3, 6, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, some 6, 2⟩]))
                                                          (.split false ⟨.fan2, 2, 5, true⟩
                                                            (.terminal .reducible)
                                                            (.split false ⟨.hat, 2, 6, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 2⟩]))
                                                              (.split false ⟨.hat, 4, 5, false⟩
                                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, some 4, 2⟩, ⟨5, some 6, 2⟩]))
                                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, some 6, 2⟩]))))))))
                                                    (.split false ⟨.fan1, 4, 5, true⟩
                                                      (.split false ⟨.spoke, 3, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, some 4, 2⟩, ⟨5, some 6, 2⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨3, none, 2⟩, ⟨2, some 4, 1⟩, ⟨5, some 6, 2⟩])))
                                                      (.split false ⟨.spoke, 5, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, some 4, 2⟩, ⟨5, some 6, 2⟩]))
                                                        (.split false ⟨.spoke, 3, 6, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨5, none, 1⟩, ⟨2, some 6, 1⟩, ⟨3, some 4, 3⟩]))
                                                          (.split false ⟨.fan2, 2, 5, true⟩
                                                            (.terminal .reducible)
                                                            (.split false ⟨.hat, 2, 6, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨5, none, 1⟩, ⟨4, some 6, 3⟩]))
                                                              (.split false ⟨.hat, 4, 5, false⟩
                                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 1⟩]))
                                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨5, none, 1⟩, ⟨4, some 6, 3⟩]))))))))))))))
                                        (.split false ⟨.spoke, 5, 6, true⟩
                                          (.split false ⟨.spoke, 4, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨1, some 5, 3⟩, ⟨4, some 6, 3⟩]))
                                            (.split false ⟨.hat, 1, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, some 6, 4⟩]))
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, some 6, 2⟩]))))
                                          (.split false ⟨.hat, 1, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨6, none, 1⟩, ⟨4, some 5, 3⟩]))
                                            (.split false ⟨.fan1, 1, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.spoke, 3, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩]))
                                                (.split false ⟨.hat, 2, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.fan2, 2, 5, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.spoke, 4, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩]))
                                                      (.split false ⟨.hat, 2, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨3, some 4, 3⟩]))
                                                        (.split false ⟨.hat, 4, 5, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨3, some 4, 2⟩]))
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩]))))))))))))
                                      (.split true ⟨.spoke, 3, 6, false⟩
                                        (.split false ⟨.fan1, 3, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.hat, 2, 6, false⟩
                                            (.terminal (.hubcap [⟨2, none, 0⟩, ⟨0, some 3, 3⟩, ⟨1, some 6, 4⟩, ⟨4, some 5, 3⟩]))
                                            (.split false ⟨.hat, 6, 5, false⟩
                                              (.split false ⟨.spoke, 4, 6, true⟩
                                                (.terminal (.hubcap [⟨0, some 3, 3⟩, ⟨1, some 2, 4⟩, ⟨4, some 5, 2⟩, ⟨4, some 6, 2⟩, ⟨5, some 6, 3⟩]))
                                                (.split false ⟨.spoke, 5, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨1, some 2, 4⟩, ⟨5, some 6, 3⟩]))
                                                  (.split false ⟨.spoke, 6, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 1⟩, ⟨1, some 2, 4⟩]))
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨1, some 2, 4⟩, ⟨5, some 6, 3⟩])))))
                                              (.split false ⟨.spoke, 6, 6, false⟩
                                                (.terminal (.hubcap [⟨1, some 2, 4⟩, ⟨5, some 6, 3⟩, ⟨0, some 3, 3⟩, ⟨0, some 4, 3⟩, ⟨3, some 4, 1⟩]))
                                                (.split false ⟨.spoke, 5, 6, false⟩
                                                  (.terminal (.hubcap [⟨4, none, 0⟩, ⟨0, some 3, 3⟩, ⟨1, some 2, 4⟩, ⟨5, some 6, 3⟩]))
                                                  (.split false ⟨.spoke, 4, 6, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.hat, 1, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨1, some 2, 4⟩, ⟨5, some 6, 4⟩])))))))))
                                        (.split false ⟨.hat, 1, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.hat, 2, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.fan1, 2, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.fan1, 3, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.spoke, 4, 6, true⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨1, some 2, 3⟩, ⟨5, some 6, 3⟩]))
                                                  (.split false ⟨.hat, 5, 5, true⟩
                                                    (.similar 0 ⟨true, 6⟩)
                                                    (.split false ⟨.spoke, 6, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨5, none, 0⟩, ⟨4, some 6, 3⟩]))
                                                      (.split false ⟨.spoke, 5, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 2⟩, ⟨6, none, 1⟩, ⟨1, some 2, 3⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨1, some 2, 3⟩, ⟨5, some 6, 4⟩])))))))))))))))
                              (.split true ⟨.spoke, 1, 6, false⟩
                                (.split false ⟨.spoke, 3, 6, false⟩
                                  (.split false ⟨.spoke, 6, 6, false⟩
                                    (.split false ⟨.spoke, 2, 7, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, some 4, 2⟩, ⟨5, some 6, 4⟩]))
                                      (.split false ⟨.spoke, 4, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 0⟩, ⟨5, none, 0⟩, ⟨1, some 3, 4⟩, ⟨4, some 6, 4⟩]))
                                        (.split false ⟨.spoke, 5, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 0⟩, ⟨4, none, 0⟩, ⟨1, some 3, 5⟩, ⟨5, some 6, 3⟩]))
                                          (.split false ⟨.hat, 5, 5, true⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩]))
                                            (.split false ⟨.spoke, 2, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨1, some 6, 6⟩, ⟨4, some 5, 1⟩]))
                                              (.split false ⟨.hat, 1, 5, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 0⟩, ⟨1, some 3, 4⟩, ⟨4, some 5, 1⟩, ⟨4, some 6, 4⟩, ⟨5, some 6, 4⟩]))
                                                (.split false ⟨.fan1, 3, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.hat, 2, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨1, some 5, 2⟩, ⟨4, some 6, 4⟩]))
                                                    (.split false ⟨.hat, 2, 5, true⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨6, none, 2⟩, ⟨4, some 5, 1⟩]))
                                                      (.split false ⟨.hat, 4, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨5, none, 0⟩, ⟨4, some 6, 4⟩]))
                                                        (.split false ⟨.hat, 4, 5, true⟩
                                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, some 5, 1⟩, ⟨4, some 6, 4⟩, ⟨5, some 6, 4⟩]))
                                                          (.split false ⟨.hat, 5, 6, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨1, some 6, 6⟩]))
                                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨5, none, 0⟩, ⟨4, some 6, 3⟩]))))))))))))))
                                    (.split false ⟨.fan1, 6, 5, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.spoke, 5, 6, false⟩
                                        (.split false ⟨.spoke, 4, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 0⟩, ⟨4, none, 0⟩, ⟨1, some 3, 3⟩, ⟨5, some 6, 4⟩]))
                                          (.split false ⟨.hat, 1, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 3⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩]))
                                            (.split false ⟨.hat, 1, 5, true⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨6, none, 3⟩, ⟨1, some 5, 2⟩]))
                                              (.split false ⟨.hat, 5, 5, true⟩
                                                (.similar 0 ⟨true, 6⟩)
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨4, none, 0⟩, ⟨6, none, 2⟩, ⟨3, some 5, 4⟩]))))))
                                        (.split false ⟨.spoke, 2, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 0⟩, ⟨3, some 4, 1⟩, ⟨1, some 5, 3⟩, ⟨1, some 6, 5⟩, ⟨5, some 6, 5⟩]))
                                          (.split false ⟨.spoke, 4, 6, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.hat, 2, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.hat, 1, 5, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 0⟩, ⟨4, none, 0⟩, ⟨1, some 3, 2⟩, ⟨5, some 6, 5⟩]))
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨1, some 5, 3⟩, ⟨1, some 6, 5⟩, ⟨5, some 6, 5⟩])))))))))
                                  (.split false ⟨.hat, 1, 5, true⟩
                                    (.split false ⟨.hat, 4, 5, true⟩
                                      (.split false ⟨.fan1, 3, 6, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.spoke, 5, 6, true⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 1⟩, ⟨5, none, 0⟩, ⟨1, some 2, 2⟩, ⟨4, some 6, 5⟩]))
                                          (.split false ⟨.spoke, 6, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, some 2, 2⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                            (.split false ⟨.fan1, 6, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.spoke, 2, 6, true⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩]))
                                                (.split false ⟨.spoke, 4, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 0⟩, ⟨6, none, 3⟩, ⟨1, some 2, 2⟩, ⟨4, some 5, 2⟩]))
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, -1⟩, ⟨6, none, 3⟩, ⟨1, some 2, 2⟩]))))))))
                                      (.split false ⟨.spoke, 6, 6, false⟩
                                        (.split false ⟨.spoke, 2, 6, true⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                          (.split false ⟨.spoke, 4, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨5, none, 0⟩, ⟨4, some 6, 5⟩]))
                                            (.split false ⟨.spoke, 5, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, some 4, 2⟩, ⟨5, some 6, 3⟩]))
                                              (.split false ⟨.hat, 4, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨5, some 6, 4⟩]))
                                                (.split false ⟨.hat, 5, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨1, some 2, 2⟩, ⟨3, some 4, 2⟩]))
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩, ⟨3, some 4, 3⟩])))))))
                                        (.split false ⟨.fan1, 6, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.spoke, 5, 6, false⟩
                                            (.split false ⟨.spoke, 2, 7, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 0⟩, ⟨6, none, 3⟩, ⟨1, some 5, 2⟩, ⟨3, some 4, 2⟩]))
                                              (.split false ⟨.spoke, 2, 6, true⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨3, some 4, 2⟩]))
                                                (.split false ⟨.fan1, 1, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.fan2, 2, 5, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.spoke, 4, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩]))
                                                      (.split false ⟨.hat, 5, 5, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.hat, 4, 6, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩]))
                                                          (.split false ⟨.hat, 6, 5, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨3, some 4, 2⟩]))
                                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩, ⟨3, some 4, 1⟩]))))))))))
                                            (.split false ⟨.spoke, 2, 7, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨1, some 5, 3⟩, ⟨1, some 6, 5⟩, ⟨5, some 6, 5⟩]))
                                              (.split false ⟨.fan1, 1, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.spoke, 4, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, some 4, 0⟩, ⟨5, some 6, 5⟩]))
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, some 6, 5⟩])))))))))
                                    (.split false ⟨.hat, 5, 5, true⟩
                                      (.similar 0 ⟨true, 6⟩)
                                      (.split false ⟨.spoke, 5, 6, true⟩
                                        (.split false ⟨.spoke, 2, 7, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨3, some 6, 4⟩, ⟨4, some 5, 2⟩]))
                                          (.split false ⟨.spoke, 6, 6, false⟩
                                            (.split false ⟨.spoke, 2, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨3, some 4, 2⟩]))
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨2, some 3, 3⟩])))
                                            (.split false ⟨.hat, 4, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.fan1, 6, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.spoke, 4, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨4, none, -1⟩, ⟨2, some 3, 3⟩, ⟨5, some 6, 5⟩]))
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, some 6, 5⟩])))))))
                                        (.split false ⟨.spoke, 6, 6, false⟩
                                          (.split false ⟨.spoke, 2, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, some 2, 2⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                            (.split false ⟨.hat, 2, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.spoke, 4, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨2, some 3, 3⟩]))
                                                (.split false ⟨.hat, 4, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 1⟩, ⟨3, none, 3⟩, ⟨4, none, 1⟩, ⟨5, some 6, 3⟩]))))))
                                          (.split false ⟨.fan1, 6, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.spoke, 2, 7, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨6, none, 2⟩, ⟨3, some 4, 3⟩, ⟨3, some 5, 3⟩, ⟨4, some 5, 3⟩]))
                                              (.split false ⟨.spoke, 2, 6, false⟩
                                                (.split false ⟨.spoke, 4, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨6, none, 2⟩, ⟨4, some 5, 3⟩]))
                                                  (.split false ⟨.hat, 4, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩]))
                                                    (.split false ⟨.hat, 4, 5, true⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩]))
                                                      (.split false ⟨.hat, 5, 6, true⟩
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨6, none, 2⟩, ⟨4, some 5, 2⟩]))
                                                        (.split false ⟨.hat, 6, 5, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩, ⟨3, some 4, 2⟩]))
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩, ⟨3, some 4, 1⟩])))))))
                                                (.split false ⟨.hat, 2, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.spoke, 4, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨4, none, 1⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩, ⟨2, some 3, 3⟩]))
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨6, none, 2⟩, ⟨2, some 4, 2⟩, ⟨3, some 5, 3⟩]))))))))))))
                                (.split false ⟨.hat, 1, 5, false⟩
                                  (.split false ⟨.hat, 5, 5, true⟩
                                    (.similar 1 ⟨true, 6⟩)
                                    (.split false ⟨.fan1, 1, 5, true⟩
                                      (.split false ⟨.hat, 1, 6, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.spoke, 2, 7, false⟩
                                          (.split false ⟨.spoke, 3, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, -1⟩, ⟨3, some 4, 2⟩, ⟨5, some 6, 5⟩]))
                                            (.split false ⟨.spoke, 4, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, -1⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, some 6, 5⟩]))
                                              (.split false ⟨.spoke, 5, 6, false⟩
                                                (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, -1⟩, ⟨0, some 6, 5⟩, ⟨3, some 4, 3⟩, ⟨3, some 5, 4⟩, ⟨4, some 5, 4⟩]))
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, -1⟩, ⟨3, none, 1⟩, ⟨6, none, 4⟩, ⟨4, some 5, 2⟩])))))
                                          (.split false ⟨.hat, 6, 6, false⟩
                                            (.split false ⟨.spoke, 2, 6, false⟩
                                              (.terminal (.hubcap [⟨1, none, 1⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩, ⟨0, some 2, 3⟩, ⟨3, some 4, 3⟩]))
                                              (.split false ⟨.spoke, 3, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨6, none, 2⟩, ⟨2, some 3, 2⟩, ⟨4, some 5, 1⟩]))
                                                (.terminal (.hubcap [⟨1, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩, ⟨0, some 2, 4⟩]))))
                                            (.split false ⟨.spoke, 2, 6, false⟩
                                              (.split false ⟨.hat, 4, 6, false⟩
                                                (.terminal (.hubcap [⟨1, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨0, some 2, 3⟩, ⟨5, some 6, 5⟩]))
                                                (.split false ⟨.spoke, 5, 6, true⟩
                                                  (.split false ⟨.spoke, 3, 6, true⟩
                                                    (.terminal (.hubcap [⟨1, none, 1⟩, ⟨0, some 2, 3⟩, ⟨3, some 6, 4⟩, ⟨4, some 5, 2⟩]))
                                                    (.split false ⟨.spoke, 4, 6, false⟩
                                                      (.terminal (.hubcap [⟨1, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨0, some 2, 3⟩, ⟨5, some 6, 5⟩]))
                                                      (.terminal (.hubcap [⟨1, none, 1⟩, ⟨3, none, 1⟩, ⟨0, some 2, 3⟩, ⟨4, some 5, 2⟩, ⟨4, some 6, 4⟩, ⟨5, some 6, 5⟩]))))
                                                  (.split false ⟨.spoke, 3, 6, false⟩
                                                    (.terminal (.hubcap [⟨1, none, 1⟩, ⟨4, none, 0⟩, ⟨3, some 5, 4⟩, ⟨0, some 2, 3⟩, ⟨0, some 6, 5⟩, ⟨2, some 6, 3⟩]))
                                                    (.split false ⟨.hat, 2, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.fan2, 2, 5, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.spoke, 6, 6, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨6, none, 2⟩, ⟨3, some 4, 3⟩, ⟨3, some 5, 3⟩, ⟨4, some 5, 3⟩]))))))))
                                              (.split false ⟨.spoke, 3, 6, false⟩
                                                (.split false ⟨.fan1, 3, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.spoke, 5, 6, false⟩
                                                    (.terminal (.hubcap [⟨4, none, 0⟩, ⟨0, some 6, 5⟩, ⟨1, some 3, 2⟩, ⟨2, some 5, 3⟩]))
                                                    (.split false ⟨.spoke, 6, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, some 3, 2⟩, ⟨2, some 5, 2⟩, ⟨4, some 6, 4⟩]))
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨5, some 6, 5⟩])))))
                                                (.split false ⟨.hat, 2, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.fan1, 2, 5, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.fan1, 3, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.spoke, 6, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, some 6, 3⟩]))
                                                        (.split false ⟨.hat, 2, 6, true⟩
                                                          (.terminal .reducible)
                                                          (.split false ⟨.fan1, 6, 5, true⟩
                                                            (.terminal .reducible)
                                                            (.split false ⟨.spoke, 5, 6, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩]))
                                                              (.split false ⟨.spoke, 4, 6, true⟩
                                                                (.terminal .reducible)
                                                                (.split false ⟨.hat, 4, 5, true⟩
                                                                  (.terminal .reducible)
                                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, -1⟩, ⟨5, some 6, 5⟩]))))))))))))))))
                                      (.split false ⟨.spoke, 2, 7, false⟩
                                        (.split false ⟨.spoke, 6, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, -1⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 4⟩]))
                                          (.split false ⟨.fan1, 6, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.spoke, 5, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, -1⟩, ⟨6, none, 2⟩, ⟨3, some 4, 3⟩, ⟨3, some 5, 3⟩, ⟨4, some 5, 3⟩]))
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, -1⟩, ⟨3, some 4, 1⟩, ⟨5, some 6, 5⟩])))))
                                        (.split false ⟨.hat, 2, 5, true⟩
                                          (.split false ⟨.spoke, 3, 6, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.fan1, 3, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.spoke, 2, 6, true⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩]))
                                                (.split false ⟨.spoke, 6, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, some 5, 1⟩, ⟨4, some 6, 4⟩, ⟨5, some 6, 4⟩]))
                                                  (.split false ⟨.fan1, 2, 5, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.fan1, 6, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.spoke, 5, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩]))
                                                        (.split false ⟨.spoke, 4, 6, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, some 6, 5⟩]))
                                                          (.split false ⟨.hat, 1, 6, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, some 6, 5⟩]))
                                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, some 6, 4⟩])))))))))))
                                          (.split false ⟨.hat, 6, 6, false⟩
                                            (.split false ⟨.spoke, 4, 6, false⟩
                                              (.terminal (.hubcap [⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨3, some 4, 2⟩, ⟨0, some 1, 5⟩, ⟨0, some 2, 4⟩, ⟨1, some 2, 4⟩]))
                                              (.split false ⟨.hat, 4, 6, false⟩
                                                (.terminal (.hubcap [⟨6, none, 2⟩, ⟨0, some 1, 5⟩, ⟨2, some 3, 2⟩, ⟨4, some 5, 1⟩]))
                                                (.split false ⟨.spoke, 2, 6, false⟩
                                                  (.split false ⟨.spoke, 3, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 2⟩, ⟨6, none, 2⟩, ⟨1, some 2, 2⟩, ⟨4, some 5, 1⟩]))
                                                    (.split false ⟨.fan2, 2, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.spoke, 5, 6, true⟩
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨3, some 4, 2⟩]))
                                                        (.split false ⟨.spoke, 6, 6, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 2⟩]))
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨3, some 4, 3⟩]))))))
                                                  (.split false ⟨.spoke, 3, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 1⟩, ⟨6, none, 2⟩, ⟨1, some 2, 3⟩, ⟨4, some 5, 1⟩]))
                                                    (.terminal (.hubcap [⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩, ⟨0, some 1, 4⟩]))))))
                                            (.split false ⟨.spoke, 2, 6, false⟩
                                              (.split false ⟨.spoke, 5, 6, true⟩
                                                (.split false ⟨.spoke, 6, 6, false⟩
                                                  (.split false ⟨.spoke, 3, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨1, some 2, 2⟩, ⟨5, some 6, 4⟩]))
                                                    (.split false ⟨.fan2, 2, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.spoke, 4, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨5, none, 0⟩, ⟨4, some 6, 5⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨5, none, 0⟩, ⟨2, some 4, 2⟩, ⟨3, some 6, 4⟩])))))
                                                  (.split false ⟨.fan1, 6, 5, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.spoke, 3, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, some 2, 1⟩, ⟨3, some 4, 1⟩, ⟨5, some 6, 5⟩]))
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, some 6, 5⟩])))))
                                                (.split false ⟨.spoke, 6, 6, false⟩
                                                  (.split false ⟨.spoke, 3, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, some 6, 3⟩]))
                                                    (.split false ⟨.fan2, 2, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.spoke, 4, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨5, some 6, 3⟩, ⟨2, some 3, 2⟩, ⟨2, some 4, 2⟩, ⟨3, some 4, 3⟩])))))
                                                  (.split false ⟨.fan1, 6, 5, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.spoke, 3, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨4, none, 0⟩, ⟨6, none, 2⟩, ⟨3, some 5, 3⟩]))
                                                      (.split false ⟨.fan2, 2, 5, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.spoke, 4, 6, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨6, none, 2⟩, ⟨4, some 5, 3⟩]))
                                                          (.split false ⟨.hat, 1, 6, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨6, none, 2⟩, ⟨3, some 4, 3⟩, ⟨3, some 5, 3⟩, ⟨4, some 5, 3⟩]))
                                                            (.split false ⟨.hat, 4, 6, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩]))
                                                              (.split false ⟨.hat, 4, 5, true⟩
                                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩]))
                                                                (.split false ⟨.hat, 5, 6, true⟩
                                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨6, none, 2⟩, ⟨4, some 5, 2⟩]))
                                                                  (.split false ⟨.hat, 6, 5, false⟩
                                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩, ⟨3, some 4, 2⟩]))
                                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩, ⟨3, some 4, 1⟩])))))))))))))
                                              (.split false ⟨.spoke, 3, 6, false⟩
                                                (.split false ⟨.fan1, 3, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.spoke, 6, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 1⟩, ⟨1, some 2, 3⟩, ⟨4, some 5, 1⟩, ⟨4, some 6, 4⟩, ⟨5, some 6, 4⟩]))
                                                    (.split false ⟨.fan1, 6, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.spoke, 5, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩]))
                                                        (.split false ⟨.spoke, 4, 6, true⟩
                                                          (.terminal .reducible)
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, some 6, 5⟩])))))))
                                                (.split false ⟨.hat, 1, 6, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.fan1, 2, 5, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.fan1, 3, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.spoke, 6, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, some 6, 3⟩]))
                                                        (.split false ⟨.fan1, 6, 5, true⟩
                                                          (.terminal .reducible)
                                                          (.split false ⟨.spoke, 5, 6, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩]))
                                                            (.split false ⟨.spoke, 4, 6, true⟩
                                                              (.terminal .reducible)
                                                              (.split false ⟨.hat, 4, 5, true⟩
                                                                (.terminal .reducible)
                                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, -1⟩, ⟨5, some 6, 5⟩])))))))))))))))))
                                  (.split false ⟨.fan1, 1, 5, true⟩
                                    (.terminal .reducible)
                                    (.split true ⟨.spoke, 2, 6, true⟩
                                      (.split false ⟨.spoke, 3, 6, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.fan1, 3, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.spoke, 6, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 0⟩, ⟨4, some 5, 1⟩, ⟨1, some 2, 5⟩, ⟨1, some 6, 5⟩, ⟨2, some 6, 3⟩]))
                                            (.split false ⟨.hat, 2, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.fan1, 6, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.spoke, 5, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩]))
                                                  (.split false ⟨.spoke, 4, 6, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.hat, 6, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩]))))))))))
                                      (.split false ⟨.spoke, 6, 6, false⟩
                                        (.split false ⟨.hat, 5, 5, true⟩
                                          (.similar 1 ⟨true, 6⟩)
                                          (.split false ⟨.spoke, 2, 7, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -1⟩, ⟨6, none, 2⟩, ⟨3, some 4, 3⟩, ⟨3, some 5, 2⟩, ⟨4, some 5, 2⟩]))
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, some 6, 2⟩, ⟨3, some 4, 2⟩, ⟨3, some 5, 2⟩, ⟨4, some 5, 1⟩]))))
                                        (.split false ⟨.fan1, 6, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.spoke, 5, 6, true⟩
                                            (.split false ⟨.hat, 5, 5, true⟩
                                              (.similar 0 ⟨true, 6⟩)
                                              (.split false ⟨.hat, 6, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.spoke, 2, 7, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, -1⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨3, some 4, 1⟩]))
                                                  (.split false ⟨.spoke, 3, 6, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.spoke, 4, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩]))
                                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨2, some 3, 0⟩])))))))
                                            (.split false ⟨.spoke, 2, 7, false⟩
                                              (.split false ⟨.hat, 5, 5, true⟩
                                                (.similar 3 ⟨true, 6⟩)
                                                (.split false ⟨.spoke, 3, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, -1⟩, ⟨4, none, 0⟩, ⟨6, none, 3⟩, ⟨3, some 5, 1⟩]))
                                                  (.split false ⟨.spoke, 4, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, -1⟩, ⟨3, none, 0⟩, ⟨6, none, 3⟩, ⟨4, some 5, 1⟩]))
                                                    (.split false ⟨.hat, 4, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.hat, 4, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, -1⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩]))
                                                        (.split false ⟨.hat, 6, 5, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, -1⟩, ⟨5, none, -1⟩, ⟨6, none, 3⟩, ⟨3, some 4, 2⟩]))
                                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, -1⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨3, some 4, 1⟩]))))))))
                                              (.split false ⟨.spoke, 3, 6, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.spoke, 4, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩]))
                                                  (.split false ⟨.hat, 5, 5, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.hat, 2, 5, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, -1⟩, ⟨4, none, 0⟩, ⟨6, none, 3⟩, ⟨3, some 5, 1⟩]))
                                                      (.split false ⟨.hat, 4, 5, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.fan1, 1, 6, true⟩
                                                          (.terminal .reducible)
                                                          (.split false ⟨.fan1, 2, 5, true⟩
                                                            (.terminal .reducible)
                                                            (.split false ⟨.fan1, 3, 5, true⟩
                                                              (.terminal .reducible)
                                                              (.split false ⟨.hat, 4, 6, false⟩
                                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩]))
                                                                (.split false ⟨.hat, 6, 5, false⟩
                                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, -1⟩, ⟨6, none, 3⟩]))
                                                                  (.split false ⟨.fan1, 6, 6, true⟩
                                                                    (.terminal .reducible)
                                                                    (.split false ⟨.fan2, 5, 5, true⟩
                                                                      (.terminal .reducible)
                                                                      (.split false ⟨.fan1, 3, 6, true⟩
                                                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩]))
                                                                        (.split false ⟨.fan2, 3, 5, false⟩
                                                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩]))
                                                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩]))))))))))))))))))))))))))))))
                  (.split false ⟨.hat, 5, 5, true⟩
                    (.similar 0 ⟨true, 6⟩)
                    (.split true ⟨.hat, 1, 5, false⟩
                      (.split true ⟨.spoke, 6, 7, false⟩
                        (.split false ⟨.spoke, 1, 7, false⟩
                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨6, none, 0⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 4⟩]))
                          (.split false ⟨.spoke, 2, 8, false⟩
                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨6, none, 0⟩, ⟨4, some 5, 4⟩]))
                            (.split false ⟨.spoke, 3, 6, false⟩
                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨6, none, 0⟩, ⟨4, some 5, 2⟩, ⟨1, some 2, 4⟩, ⟨1, some 3, 5⟩, ⟨2, some 3, 4⟩]))
                              (.split false ⟨.spoke, 4, 6, false⟩
                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩, ⟨1, some 2, 4⟩, ⟨3, some 4, 4⟩]))
                                (.split false ⟨.spoke, 5, 6, false⟩
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 0⟩, ⟨1, some 2, 4⟩, ⟨3, some 4, 3⟩]))
                                  (.split false ⟨.spoke, 1, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 0⟩, ⟨1, some 2, 3⟩, ⟨4, some 5, 3⟩]))
                                    (.split false ⟨.spoke, 2, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨6, none, 0⟩, ⟨2, some 3, 3⟩, ⟨4, some 5, 3⟩]))
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 0⟩])))))))))
                        (.split true ⟨.spoke, 3, 7, false⟩
                          (.split false ⟨.spoke, 1, 7, false⟩
                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨5, some 6, 5⟩]))
                            (.split false ⟨.spoke, 2, 8, false⟩
                              (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨0, some 4, 3⟩, ⟨5, some 6, 5⟩]))
                              (.split false ⟨.spoke, 5, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩, ⟨1, some 2, 4⟩]))
                                (.split false ⟨.hat, 2, 6, false⟩
                                  (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨0, some 4, 3⟩, ⟨5, some 6, 5⟩]))
                                  (.split false ⟨.hat, 6, 6, false⟩
                                    (.terminal (.hubcap [⟨3, none, 0⟩, ⟨0, some 4, 3⟩, ⟨1, some 2, 4⟩, ⟨5, some 6, 3⟩]))
                                    (.split false ⟨.spoke, 1, 6, false⟩
                                      (.split false ⟨.spoke, 2, 6, false⟩
                                        (.terminal (.hubcap [⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨0, some 1, 4⟩, ⟨5, some 6, 5⟩]))
                                        (.split false ⟨.spoke, 4, 7, false⟩
                                          (.terminal (.hubcap [⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨0, some 1, 5⟩, ⟨5, some 6, 5⟩]))
                                          (.split false ⟨.spoke, 5, 6, false⟩
                                            (.terminal (.hubcap [⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨0, some 1, 5⟩, ⟨5, some 6, 5⟩]))
                                            (.split false ⟨.spoke, 6, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨5, some 6, 4⟩]))
                                              (.terminal (.hubcap [⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨5, none, 2⟩, ⟨0, some 4, 3⟩, ⟨1, some 6, 5⟩]))))))
                                      (.split false ⟨.spoke, 2, 7, false⟩
                                        (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨0, some 2, 2⟩, ⟨5, some 6, 5⟩]))
                                        (.split false ⟨.spoke, 2, 6, false⟩
                                          (.split false ⟨.spoke, 6, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨1, some 2, 3⟩, ⟨5, some 6, 4⟩]))
                                            (.split false ⟨.spoke, 5, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨2, some 6, 3⟩]))
                                              (.split false ⟨.spoke, 4, 6, false⟩
                                                (.terminal (.hubcap [⟨3, none, 0⟩, ⟨0, some 2, 4⟩, ⟨1, some 4, 1⟩, ⟨5, some 6, 5⟩]))
                                                (.split false ⟨.hat, 1, 6, false⟩
                                                  (.terminal (.hubcap [⟨1, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨0, some 2, 4⟩, ⟨5, some 6, 5⟩]))
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨1, some 2, 3⟩, ⟨5, some 6, 4⟩]))))))
                                          (.split false ⟨.spoke, 4, 7, false⟩
                                            (.terminal (.hubcap [⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, some 6, 5⟩, ⟨0, some 1, 5⟩, ⟨0, some 2, 4⟩, ⟨1, some 2, 4⟩]))
                                            (.split false ⟨.spoke, 5, 6, false⟩
                                              (.terminal (.hubcap [⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, some 6, 5⟩, ⟨0, some 1, 5⟩, ⟨0, some 2, 4⟩, ⟨1, some 2, 4⟩]))
                                              (.split false ⟨.spoke, 6, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, -1⟩, ⟨4, none, 1⟩, ⟨1, some 2, 4⟩, ⟨5, some 6, 4⟩]))
                                                (.split false ⟨.spoke, 4, 6, false⟩
                                                  (.terminal (.hubcap [⟨3, none, -1⟩, ⟨0, some 4, 2⟩, ⟨1, some 2, 4⟩, ⟨5, some 6, 5⟩]))
                                                  (.terminal (.hubcap [⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, some 6, 5⟩, ⟨0, some 1, 5⟩, ⟨0, some 2, 4⟩, ⟨1, some 2, 4⟩]))))))))))))))
                          (.split false ⟨.spoke, 4, 7, false⟩
                            (.split false ⟨.hat, 0, 5, false⟩
                              (.similar 0 ⟨true, 6⟩)
                              (.split false ⟨.spoke, 1, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨4, none, 0⟩, ⟨2, some 3, 2⟩, ⟨5, some 6, 5⟩]))
                                (.split false ⟨.spoke, 2, 7, false⟩
                                  (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨0, some 2, 3⟩, ⟨5, some 6, 5⟩]))
                                  (.split false ⟨.spoke, 5, 8, false⟩
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨1, some 2, 4⟩]))
                                    (.split false ⟨.spoke, 6, 6, false⟩
                                      (.split false ⟨.spoke, 1, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨1, some 2, 3⟩]))
                                        (.split false ⟨.spoke, 2, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩]))
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨1, some 2, 4⟩, ⟨1, some 6, 6⟩, ⟨2, some 6, 5⟩]))))
                                      (.split false ⟨.fan1, 6, 5, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.spoke, 5, 7, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩]))
                                          (.split false ⟨.spoke, 1, 6, false⟩
                                            (.split false ⟨.spoke, 2, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, some 6, 5⟩]))
                                              (.split false ⟨.hat, 2, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.spoke, 3, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, some 6, 5⟩]))
                                                  (.split false ⟨.spoke, 5, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩, ⟨2, some 3, 2⟩]))
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨4, none, -1⟩, ⟨2, some 3, 2⟩, ⟨5, some 6, 5⟩]))))))
                                            (.split false ⟨.spoke, 2, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, some 6, 5⟩]))
                                              (.split false ⟨.hat, 2, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.spoke, 3, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, some 6, 5⟩]))
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, some 6, 5⟩])))))))))))))
                            (.split false ⟨.spoke, 5, 8, false⟩
                              (.split false ⟨.spoke, 2, 7, false⟩
                                (.terminal (.hubcap [⟨1, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨0, some 2, 3⟩, ⟨3, some 4, 3⟩]))
                                (.split false ⟨.spoke, 1, 6, false⟩
                                  (.split false ⟨.spoke, 2, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨1, some 2, 2⟩, ⟨3, some 4, 3⟩]))
                                    (.split false ⟨.spoke, 3, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨1, some 3, 5⟩]))
                                      (.split false ⟨.spoke, 1, 7, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨2, some 3, 3⟩]))
                                        (.split false ⟨.spoke, 6, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨1, some 2, 3⟩, ⟨3, some 4, 3⟩]))
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨5, none, -1⟩, ⟨6, none, 2⟩, ⟨1, some 2, 3⟩, ⟨3, some 4, 3⟩]))))))
                                  (.split false ⟨.spoke, 2, 6, true⟩
                                    (.terminal (.hubcap [⟨5, none, 0⟩, ⟨0, some 1, 5⟩, ⟨2, some 6, 3⟩, ⟨3, some 4, 2⟩]))
                                    (.split false ⟨.spoke, 3, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨2, some 3, 3⟩]))
                                      (.split false ⟨.spoke, 4, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨3, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨2, some 4, 3⟩]))
                                        (.split false ⟨.spoke, 6, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨5, none, 0⟩, ⟨2, some 6, 3⟩, ⟨3, some 4, 3⟩]))
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨5, none, -1⟩, ⟨2, some 6, 3⟩, ⟨3, some 4, 3⟩]))))))))
                              (.split false ⟨.hat, 4, 6, false⟩
                                (.split false ⟨.spoke, 1, 7, false⟩
                                  (.terminal (.hubcap [⟨1, none, 0⟩, ⟨0, some 4, 3⟩, ⟨2, some 3, 2⟩, ⟨5, some 6, 5⟩]))
                                  (.split false ⟨.spoke, 2, 8, false⟩
                                    (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨0, some 4, 3⟩, ⟨5, some 6, 5⟩]))
                                    (.split false ⟨.spoke, 1, 6, false⟩
                                      (.split false ⟨.spoke, 2, 6, false⟩
                                        (.terminal (.hubcap [⟨3, none, 0⟩, ⟨0, some 4, 3⟩, ⟨1, some 2, 2⟩, ⟨5, some 6, 5⟩]))
                                        (.split false ⟨.spoke, 5, 7, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩, ⟨2, some 3, 1⟩]))
                                          (.split false ⟨.spoke, 6, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, some 6, 6⟩, ⟨2, some 3, 1⟩, ⟨4, some 5, 1⟩]))
                                            (.split false ⟨.spoke, 5, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨1, some 6, 4⟩, ⟨2, some 3, 1⟩]))
                                              (.split false ⟨.spoke, 4, 6, false⟩
                                                (.terminal (.hubcap [⟨5, none, 2⟩, ⟨0, some 4, 2⟩, ⟨1, some 6, 5⟩, ⟨2, some 3, 1⟩]))
                                                (.split false ⟨.hat, 2, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨4, none, 0⟩, ⟨2, some 3, 1⟩, ⟨5, some 6, 5⟩]))
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩]))))))))
                                      (.split false ⟨.spoke, 2, 7, false⟩
                                        (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨0, some 2, 2⟩, ⟨5, some 6, 5⟩]))
                                        (.split true ⟨.spoke, 3, 6, true⟩
                                          (.split false ⟨.spoke, 5, 7, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩, ⟨1, some 2, 4⟩]))
                                            (.split false ⟨.spoke, 6, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 0⟩, ⟨1, some 2, 4⟩, ⟨4, some 5, 1⟩, ⟨4, some 6, 4⟩, ⟨5, some 6, 4⟩]))
                                              (.split false ⟨.hat, 6, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 0⟩, ⟨6, none, 2⟩, ⟨1, some 2, 4⟩, ⟨4, some 5, 1⟩]))
                                                (.split false ⟨.hat, 0, 5, false⟩
                                                  (.split false ⟨.spoke, 2, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨5, some 6, 4⟩]))
                                                    (.split false ⟨.spoke, 4, 6, true⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨1, some 2, 4⟩, ⟨5, some 6, 4⟩]))
                                                      (.split false ⟨.spoke, 5, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 1⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨1, some 2, 4⟩, ⟨5, some 6, 4⟩])))))
                                                  (.split false ⟨.fan1, 6, 5, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.spoke, 5, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩]))
                                                      (.split false ⟨.spoke, 2, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, some 6, 5⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, some 6, 5⟩])))))))))
                                          (.split false ⟨.spoke, 2, 6, false⟩
                                            (.split false ⟨.spoke, 5, 7, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩]))
                                              (.split false ⟨.spoke, 6, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨1, some 2, 3⟩, ⟨5, some 6, 4⟩]))
                                                (.split false ⟨.spoke, 5, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨2, some 6, 3⟩]))
                                                  (.split false ⟨.spoke, 4, 6, false⟩
                                                    (.terminal (.hubcap [⟨3, none, 0⟩, ⟨0, some 2, 4⟩, ⟨1, some 4, 1⟩, ⟨5, some 6, 5⟩]))
                                                    (.split false ⟨.hat, 0, 5, false⟩
                                                      (.similar 0 ⟨true, 6⟩)
                                                      (.split false ⟨.fan1, 6, 5, true⟩
                                                        (.terminal .reducible)
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, some 6, 5⟩]))))))))
                                            (.split false ⟨.spoke, 5, 7, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨2, some 6, 3⟩]))
                                              (.split false ⟨.spoke, 6, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 0⟩, ⟨1, some 2, 4⟩, ⟨4, some 5, 1⟩, ⟨4, some 6, 4⟩, ⟨5, some 6, 4⟩]))
                                                (.split false ⟨.spoke, 5, 6, false⟩
                                                  (.terminal (.hubcap [⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨0, some 1, 5⟩, ⟨2, some 6, 3⟩]))
                                                  (.split false ⟨.spoke, 4, 6, false⟩
                                                    (.split false ⟨.hat, 1, 6, true⟩
                                                      (.terminal (.hubcap [⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨0, some 1, 5⟩, ⟨5, some 6, 4⟩]))
                                                      (.split false ⟨.hat, 2, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨1, some 2, 2⟩, ⟨5, some 6, 5⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨1, some 2, 4⟩, ⟨5, some 6, 4⟩]))))
                                                    (.split false ⟨.hat, 0, 5, false⟩
                                                      (.similar 0 ⟨true, 6⟩)
                                                      (.split false ⟨.hat, 2, 5, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.fan1, 6, 5, true⟩
                                                          (.terminal .reducible)
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, some 6, 5⟩])))))))))))))))
                                (.split false ⟨.spoke, 1, 7, false⟩
                                  (.split false ⟨.hat, 0, 5, false⟩
                                    (.similar 1 ⟨true, 6⟩)
                                    (.split false ⟨.spoke, 5, 6, true⟩
                                      (.split false ⟨.spoke, 2, 7, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, some 4, 2⟩, ⟨5, some 6, 5⟩]))
                                        (.split false ⟨.spoke, 6, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨4, none, 2⟩, ⟨2, some 3, 2⟩, ⟨5, some 6, 4⟩]))
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨5, some 6, 5⟩, ⟨2, some 3, 2⟩, ⟨2, some 4, 1⟩, ⟨3, some 4, 2⟩]))))
                                      (.split false ⟨.spoke, 2, 7, false⟩
                                        (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨0, some 6, 5⟩, ⟨3, some 4, 3⟩, ⟨3, some 5, 4⟩, ⟨4, some 5, 4⟩]))
                                        (.split false ⟨.spoke, 3, 6, false⟩
                                          (.split false ⟨.spoke, 2, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, some 6, 5⟩]))
                                            (.split false ⟨.spoke, 4, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩]))
                                              (.split false ⟨.spoke, 5, 7, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 4⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩]))
                                                (.split false ⟨.spoke, 6, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 4⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩]))
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨4, none, 0⟩, ⟨6, none, 2⟩, ⟨3, some 5, 5⟩]))))))
                                          (.split false ⟨.spoke, 6, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨4, none, 2⟩, ⟨2, some 3, 3⟩, ⟨5, some 6, 3⟩]))
                                            (.split false ⟨.fan1, 6, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.spoke, 2, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 1⟩, ⟨6, none, 2⟩, ⟨3, some 4, 3⟩, ⟨3, some 5, 3⟩, ⟨4, some 5, 3⟩]))
                                                (.split false ⟨.spoke, 4, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨6, none, 2⟩, ⟨2, some 3, 2⟩, ⟨4, some 5, 3⟩]))
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨6, none, 2⟩, ⟨2, some 3, 3⟩, ⟨4, some 5, 2⟩]))))))))))
                                  (.split true ⟨.spoke, 2, 7, false⟩
                                    (.split false ⟨.spoke, 4, 6, false⟩
                                      (.split false ⟨.spoke, 5, 7, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨3, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩, ⟨2, some 4, 2⟩]))
                                        (.split false ⟨.spoke, 6, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨5, none, 0⟩, ⟨4, some 6, 5⟩]))
                                          (.split false ⟨.spoke, 5, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨3, none, 0⟩, ⟨2, some 6, 2⟩, ⟨4, some 5, 3⟩]))
                                            (.terminal (.hubcap [⟨3, none, 0⟩, ⟨0, some 2, 3⟩, ⟨1, some 4, 2⟩, ⟨5, some 6, 5⟩])))))
                                      (.split false ⟨.spoke, 5, 7, false⟩
                                        (.terminal (.hubcap [⟨1, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨0, some 2, 3⟩, ⟨3, some 4, 3⟩]))
                                        (.split false ⟨.spoke, 1, 6, false⟩
                                          (.split false ⟨.spoke, 6, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 4⟩]))
                                            (.split false ⟨.spoke, 5, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨6, none, 2⟩, ⟨3, some 4, 3⟩, ⟨3, some 5, 3⟩, ⟨4, some 5, 3⟩]))
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, some 6, 5⟩]))))
                                          (.split false ⟨.hat, 6, 6, false⟩
                                            (.terminal (.hubcap [⟨1, none, 2⟩, ⟨0, some 2, 2⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                            (.split false ⟨.hat, 0, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 4⟩]))
                                              (.split false ⟨.spoke, 5, 6, true⟩
                                                (.split false ⟨.spoke, 3, 6, false⟩
                                                  (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 1⟩, ⟨0, some 2, 2⟩, ⟨4, some 5, 2⟩, ⟨4, some 6, 4⟩, ⟨5, some 6, 5⟩]))
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, -1⟩, ⟨3, some 6, 4⟩, ⟨4, some 5, 2⟩])))
                                                (.split false ⟨.spoke, 6, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, -1⟩, ⟨3, none, 2⟩, ⟨6, none, 2⟩, ⟨4, some 5, 2⟩])))))))))
                                    (.split false ⟨.spoke, 5, 7, false⟩
                                      (.split false ⟨.hat, 0, 5, false⟩
                                        (.similar 0 ⟨true, 6⟩)
                                        (.split false ⟨.spoke, 6, 6, false⟩
                                          (.split false ⟨.spoke, 3, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨1, some 6, 4⟩, ⟨2, some 3, 4⟩]))
                                            (.split false ⟨.spoke, 1, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨1, some 2, 3⟩, ⟨3, some 4, 3⟩]))
                                              (.split false ⟨.spoke, 2, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨5, none, 0⟩, ⟨2, some 6, 3⟩, ⟨3, some 4, 3⟩]))
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩])))))
                                          (.split false ⟨.fan1, 6, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.spoke, 1, 6, false⟩
                                              (.split false ⟨.spoke, 2, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨3, some 4, 3⟩]))
                                                (.split false ⟨.hat, 2, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.spoke, 3, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨3, none, 4⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩]))
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨1, some 2, 2⟩, ⟨3, some 4, 3⟩])))))
                                              (.split false ⟨.spoke, 2, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨3, some 4, 3⟩]))
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩])))))))
                                      (.split true ⟨.hat, 6, 5, false⟩
                                        (.split true ⟨.spoke, 4, 6, false⟩
                                          (.split false ⟨.hat, 2, 5, false⟩
                                            (.split false ⟨.spoke, 6, 6, false⟩
                                              (.split false ⟨.spoke, 1, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨5, none, 0⟩, ⟨2, some 3, 2⟩, ⟨4, some 6, 5⟩]))
                                                (.split false ⟨.spoke, 2, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨5, none, 0⟩, ⟨4, some 6, 5⟩]))
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨5, none, 0⟩, ⟨4, some 6, 4⟩]))))
                                              (.split false ⟨.spoke, 5, 6, true⟩
                                                (.split false ⟨.spoke, 1, 6, false⟩
                                                  (.terminal (.hubcap [⟨1, none, 1⟩, ⟨0, some 4, 3⟩, ⟨2, some 3, 2⟩, ⟨5, some 6, 4⟩]))
                                                  (.split false ⟨.spoke, 2, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨3, none, 0⟩, ⟨2, some 5, 2⟩, ⟨4, some 6, 3⟩]))
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, some 2, 2⟩, ⟨3, some 4, 1⟩, ⟨5, some 6, 4⟩]))))
                                                (.split false ⟨.spoke, 3, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩, ⟨2, some 3, 2⟩]))
                                                  (.split false ⟨.hat, 4, 5, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨4, none, 1⟩, ⟨5, none, 1⟩, ⟨1, some 3, 2⟩, ⟨2, some 6, 3⟩]))
                                                    (.split false ⟨.hat, 6, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, -1⟩, ⟨6, none, 2⟩, ⟨2, some 3, 2⟩]))
                                                      (.split false ⟨.hat, 0, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩, ⟨2, some 3, 2⟩]))
                                                        (.split false ⟨.fan1, 6, 5, true⟩
                                                          (.terminal .reducible)
                                                          (.split false ⟨.spoke, 1, 6, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨4, none, 2⟩, ⟨6, none, 2⟩, ⟨1, some 5, 1⟩, ⟨2, some 3, 2⟩]))
                                                            (.split false ⟨.spoke, 2, 6, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩]))
                                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩])))))))))))
                                            (.split false ⟨.spoke, 1, 6, false⟩
                                              (.split false ⟨.spoke, 3, 6, false⟩
                                                (.terminal (.hubcap [⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨0, some 1, 5⟩, ⟨5, some 6, 4⟩]))
                                                (.split false ⟨.spoke, 6, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 0⟩, ⟨5, none, 0⟩, ⟨1, some 2, 3⟩, ⟨4, some 6, 5⟩]))
                                                  (.split false ⟨.spoke, 2, 6, true⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨1, some 2, 3⟩, ⟨5, some 6, 3⟩]))
                                                    (.split false ⟨.spoke, 5, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩, ⟨1, some 2, 2⟩]))
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨1, some 2, 2⟩, ⟨5, some 6, 4⟩]))))))
                                              (.split false ⟨.spoke, 6, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨5, none, 0⟩, ⟨1, some 2, 4⟩, ⟨3, some 4, 2⟩, ⟨3, some 6, 3⟩, ⟨4, some 6, 4⟩]))
                                                (.split false ⟨.spoke, 2, 6, false⟩
                                                  (.split false ⟨.spoke, 5, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨5, none, 1⟩, ⟨2, some 6, 3⟩]))
                                                    (.terminal (.hubcap [⟨3, none, 0⟩, ⟨0, some 2, 4⟩, ⟨1, some 4, 2⟩, ⟨5, some 6, 4⟩])))
                                                  (.split false ⟨.hat, 0, 5, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.spoke, 3, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨1, some 2, 4⟩, ⟨5, some 6, 3⟩]))
                                                      (.split false ⟨.spoke, 5, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨5, some 6, 2⟩])))))))))
                                          (.split false ⟨.spoke, 3, 6, false⟩
                                            (.split false ⟨.spoke, 1, 6, false⟩
                                              (.split false ⟨.spoke, 2, 6, false⟩
                                                (.terminal (.hubcap [⟨2, none, 0⟩, ⟨0, some 1, 4⟩, ⟨3, some 6, 4⟩, ⟨4, some 5, 2⟩]))
                                                (.split false ⟨.hat, 2, 5, true⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, some 6, 3⟩, ⟨4, some 5, 2⟩]))
                                                  (.split false ⟨.hat, 0, 5, false⟩
                                                    (.similar 0 ⟨true, 6⟩)
                                                    (.split false ⟨.spoke, 5, 6, true⟩
                                                      (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨0, some 4, 3⟩, ⟨5, some 6, 4⟩]))
                                                      (.split false ⟨.spoke, 6, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨3, none, 4⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 4⟩, ⟨4, none, 0⟩, ⟨6, none, 2⟩, ⟨1, some 5, 1⟩])))))))
                                              (.split false ⟨.spoke, 2, 6, true⟩
                                                (.split false ⟨.hat, 1, 6, true⟩
                                                  (.terminal (.hubcap [⟨0, some 2, 3⟩, ⟨1, some 3, 3⟩, ⟨4, some 5, 2⟩, ⟨4, some 6, 3⟩, ⟨5, some 6, 4⟩]))
                                                  (.split false ⟨.hat, 2, 5, false⟩
                                                    (.terminal (.hubcap [⟨3, none, 1⟩, ⟨0, some 4, 3⟩, ⟨1, some 2, 2⟩, ⟨5, some 6, 4⟩]))
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨1, some 2, 4⟩, ⟨5, some 6, 3⟩]))))
                                                (.split false ⟨.hat, 2, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, -1⟩, ⟨3, some 6, 4⟩, ⟨4, some 5, 2⟩]))
                                                  (.split false ⟨.hat, 0, 5, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, some 6, 3⟩, ⟨4, some 5, 2⟩]))
                                                    (.split false ⟨.spoke, 6, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, some 2, 3⟩, ⟨3, some 6, 4⟩, ⟨4, some 5, 1⟩]))
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨4, none, 0⟩, ⟨2, some 3, 1⟩, ⟨5, some 6, 4⟩])))))))
                                            (.split false ⟨.fan1, 4, 5, false⟩
                                              (.split false ⟨.spoke, 6, 6, false⟩
                                                (.split false ⟨.hat, 0, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨4, none, 2⟩, ⟨5, some 6, 1⟩, ⟨1, some 2, 4⟩, ⟨1, some 3, 3⟩, ⟨2, some 3, 4⟩]))
                                                  (.split false ⟨.hat, 4, 5, false⟩
                                                    (.split false ⟨.spoke, 1, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, some 2, 3⟩, ⟨3, some 4, 2⟩, ⟨5, some 6, 3⟩]))
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 0⟩, ⟨1, some 2, 4⟩, ⟨4, some 5, 2⟩, ⟨4, some 6, 4⟩, ⟨5, some 6, 3⟩])))
                                                    (.split false ⟨.spoke, 1, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨4, none, 2⟩, ⟨5, some 6, 2⟩, ⟨1, some 2, 3⟩, ⟨1, some 3, 3⟩, ⟨2, some 3, 3⟩]))
                                                      (.split false ⟨.spoke, 2, 6, true⟩
                                                        (.terminal .reducible)
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨1, some 2, 3⟩, ⟨5, some 6, 2⟩]))))))
                                                (.split false ⟨.spoke, 5, 6, false⟩
                                                  (.split false ⟨.hat, 0, 5, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨6, none, 1⟩, ⟨4, some 5, 2⟩, ⟨1, some 2, 4⟩, ⟨1, some 3, 3⟩, ⟨2, some 3, 4⟩]))
                                                    (.split false ⟨.fan1, 6, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.spoke, 1, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨6, none, 2⟩, ⟨1, some 2, 2⟩, ⟨3, some 4, 3⟩, ⟨3, some 5, 2⟩, ⟨4, some 5, 2⟩]))
                                                        (.split false ⟨.spoke, 2, 6, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨6, none, 2⟩, ⟨4, some 5, 2⟩]))
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩]))))))
                                                  (.split false ⟨.hat, 4, 5, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.fan1, 3, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.spoke, 1, 6, false⟩
                                                        (.terminal (.hubcap [⟨4, none, 0⟩, ⟨0, some 1, 5⟩, ⟨2, some 3, 1⟩, ⟨5, some 6, 4⟩]))
                                                        (.split false ⟨.spoke, 2, 6, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨1, some 2, 3⟩, ⟨5, some 6, 4⟩]))
                                                          (.terminal (.hubcap [⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨0, some 1, 5⟩, ⟨2, some 5, 3⟩, ⟨2, some 6, 4⟩, ⟨5, some 6, 4⟩]))))))))
                                              (.split false ⟨.fan1, 3, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.hat, 0, 5, false⟩
                                                  (.split false ⟨.spoke, 1, 6, true⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 2⟩, ⟨6, none, 1⟩, ⟨2, some 3, 3⟩]))
                                                    (.split false ⟨.spoke, 2, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 2⟩, ⟨6, none, 1⟩, ⟨1, some 2, 2⟩]))
                                                      (.split false ⟨.spoke, 5, 6, true⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨1, some 2, 3⟩, ⟨5, some 6, 2⟩]))
                                                        (.split false ⟨.spoke, 6, 6, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩, ⟨1, some 2, 3⟩]))
                                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩, ⟨1, some 2, 3⟩]))))))
                                                  (.split false ⟨.spoke, 5, 6, true⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨1, some 2, 3⟩]))
                                                    (.split false ⟨.spoke, 6, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨1, some 2, 3⟩, ⟨5, some 6, 2⟩]))
                                                      (.split false ⟨.fan1, 6, 5, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.spoke, 1, 6, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨6, none, 2⟩, ⟨4, some 5, 1⟩]))
                                                          (.split false ⟨.spoke, 2, 6, true⟩
                                                            (.terminal .reducible)
                                                            (.split false ⟨.hat, 2, 5, true⟩
                                                              (.terminal .reducible)
                                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨6, none, 2⟩, ⟨4, some 5, 1⟩])))))))))))))
                                        (.split false ⟨.hat, 2, 5, true⟩
                                          (.split true ⟨.spoke, 2, 6, true⟩
                                            (.split false ⟨.spoke, 1, 6, false⟩
                                              (.split false ⟨.spoke, 3, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 0⟩, ⟨4, none, 0⟩, ⟨1, some 3, 4⟩, ⟨5, some 6, 4⟩]))
                                                (.split false ⟨.spoke, 6, 6, false⟩
                                                  (.split false ⟨.spoke, 4, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨5, none, 0⟩, ⟨4, some 6, 4⟩]))
                                                    (.split false ⟨.hat, 3, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 0⟩, ⟨5, some 6, 3⟩, ⟨1, some 3, 4⟩, ⟨1, some 4, 4⟩, ⟨3, some 4, 3⟩]))
                                                      (.split false ⟨.fan1, 2, 6, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.fan1, 3, 5, true⟩
                                                          (.terminal .reducible)
                                                          (.split false ⟨.spoke, 5, 6, true⟩
                                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, some 5, 2⟩, ⟨4, some 6, 3⟩]))
                                                            (.split false ⟨.hat, 4, 5, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩]))
                                                              (.split false ⟨.fan2, 1, 5, true⟩
                                                                (.terminal .reducible)
                                                                (.split false ⟨.hat, 5, 6, false⟩
                                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩]))
                                                                  (.split false ⟨.hat, 0, 5, false⟩
                                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, some 6, 2⟩]))
                                                                    (.split false ⟨.fan2, 6, 5, true⟩
                                                                      (.terminal .reducible)
                                                                      (.split false ⟨.fan1, 1, 5, false⟩
                                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩]))
                                                                        (.split false ⟨.fan1, 3, 6, false⟩
                                                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩]))
                                                                          (.split false ⟨.fan1, 4, 5, false⟩
                                                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩]))
                                                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, some 6, 2⟩])))))))))))))))
                                                  (.split false ⟨.spoke, 5, 6, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.hat, 0, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 2⟩, ⟨6, none, 1⟩, ⟨1, some 2, 3⟩]))))))
                                              (.split false ⟨.spoke, 6, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 1⟩, ⟨6, none, 2⟩, ⟨1, some 2, 4⟩, ⟨4, some 5, 1⟩]))
                                                (.split false ⟨.hat, 0, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.spoke, 5, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 1⟩, ⟨1, some 2, 4⟩, ⟨3, some 4, 1⟩]))
                                                    (.split true ⟨.spoke, 3, 6, false⟩
                                                      (.split false ⟨.spoke, 4, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨1, some 2, 4⟩, ⟨5, some 6, 4⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨1, some 2, 4⟩, ⟨5, some 6, 4⟩])))
                                                      (.split false ⟨.spoke, 4, 6, false⟩
                                                        (.similar 0 ⟨true, 6⟩)
                                                        (.split false ⟨.hat, 4, 5, true⟩
                                                          (.terminal .reducible)
                                                          (.split false ⟨.fan1, 3, 5, true⟩
                                                            (.terminal .reducible)
                                                            (.split false ⟨.fan1, 4, 5, true⟩
                                                              (.terminal .reducible)
                                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨1, some 2, 4⟩, ⟨5, some 6, 4⟩])))))))))))
                                            (.split false ⟨.spoke, 1, 6, false⟩
                                              (.split false ⟨.fan1, 2, 5, true⟩
                                                (.split false ⟨.spoke, 3, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, some 4, 2⟩, ⟨5, some 6, 4⟩]))
                                                  (.split false ⟨.spoke, 4, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨1, some 2, 2⟩, ⟨5, some 6, 4⟩]))
                                                    (.split false ⟨.spoke, 6, 6, true⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨1, some 2, 2⟩, ⟨5, some 6, 4⟩]))
                                                      (.split false ⟨.spoke, 5, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩, ⟨1, some 2, 2⟩, ⟨3, some 4, 3⟩]))
                                                        (.split false ⟨.hat, 0, 5, false⟩
                                                          (.similar 0 ⟨true, 6⟩)
                                                          (.split false ⟨.hat, 4, 5, true⟩
                                                            (.terminal .reducible)
                                                            (.split false ⟨.fan2, 6, 5, true⟩
                                                              (.terminal .reducible)
                                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨3, some 4, 1⟩])))))))))
                                                (.split false ⟨.spoke, 3, 6, false⟩
                                                  (.terminal (.hubcap [⟨2, none, 0⟩, ⟨0, some 3, 4⟩, ⟨1, some 4, 1⟩, ⟨5, some 6, 5⟩]))
                                                  (.split false ⟨.fan2, 1, 5, true⟩
                                                    (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨5, some 6, 5⟩, ⟨0, some 3, 4⟩, ⟨0, some 4, 4⟩, ⟨3, some 4, 3⟩]))
                                                    (.split false ⟨.spoke, 5, 6, true⟩
                                                      (.split false ⟨.hat, 0, 5, false⟩
                                                        (.similar 0 ⟨true, 6⟩)
                                                        (.terminal (.hubcap [⟨2, none, 1⟩, ⟨0, some 1, 3⟩, ⟨3, some 5, 1⟩, ⟨4, some 6, 5⟩])))
                                                      (.split false ⟨.spoke, 6, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                                        (.split false ⟨.spoke, 4, 6, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩]))
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨5, none, 2⟩, ⟨4, some 6, 2⟩]))))))))
                                              (.split true ⟨.spoke, 3, 6, false⟩
                                                (.split false ⟨.spoke, 6, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨1, some 2, 3⟩, ⟨5, some 6, 4⟩]))
                                                  (.split false ⟨.spoke, 5, 6, false⟩
                                                    (.split false ⟨.spoke, 4, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨2, some 6, 3⟩]))
                                                      (.split false ⟨.hat, 1, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨2, some 6, 3⟩]))
                                                        (.split false ⟨.fan1, 1, 6, true⟩
                                                          (.terminal .reducible)
                                                          (.split false ⟨.hat, 5, 6, true⟩
                                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨2, some 6, 3⟩]))
                                                            (.split false ⟨.hat, 0, 5, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 1⟩]))
                                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩])))))))
                                                    (.split false ⟨.hat, 0, 5, false⟩
                                                      (.similar 0 ⟨true, 6⟩)
                                                      (.split false ⟨.hat, 1, 6, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.fan1, 2, 5, true⟩
                                                          (.terminal .reducible)
                                                          (.split false ⟨.fan1, 6, 6, true⟩
                                                            (.terminal .reducible)
                                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 4⟩, ⟨3, some 4, 1⟩]))))))))
                                                (.split false ⟨.spoke, 5, 6, true⟩
                                                  (.split false ⟨.hat, 0, 5, false⟩
                                                    (.similar 1 ⟨true, 6⟩)
                                                    (.terminal (.hubcap [⟨3, none, 0⟩, ⟨6, none, 4⟩, ⟨4, some 5, 1⟩, ⟨0, some 1, 4⟩, ⟨0, some 2, 4⟩, ⟨1, some 2, 3⟩])))
                                                  (.split false ⟨.spoke, 6, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨1, some 2, 3⟩, ⟨5, some 6, 3⟩]))
                                                    (.split false ⟨.spoke, 4, 6, true⟩
                                                      (.terminal (.hubcap [⟨5, none, 2⟩, ⟨0, some 2, 4⟩, ⟨1, some 3, 2⟩, ⟨4, some 6, 2⟩]))
                                                      (.split false ⟨.hat, 0, 5, false⟩
                                                        (.similar 0 ⟨true, 6⟩)
                                                        (.split false ⟨.fan1, 2, 5, true⟩
                                                          (.terminal .reducible)
                                                          (.split false ⟨.fan1, 6, 6, true⟩
                                                            (.terminal .reducible)
                                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩])))))))))))
                                          (.split false ⟨.hat, 0, 5, false⟩
                                            (.similar 0 ⟨true, 6⟩)
                                            (.split false ⟨.spoke, 6, 6, false⟩
                                              (.split false ⟨.spoke, 3, 6, false⟩
                                                (.split false ⟨.spoke, 4, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨2, some 3, 2⟩]))
                                                  (.split false ⟨.spoke, 1, 6, false⟩
                                                    (.split false ⟨.spoke, 2, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 4⟩]))
                                                      (.split false ⟨.spoke, 5, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨3, none, 4⟩, ⟨4, none, 0⟩, ⟨5, some 6, 3⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 4⟩]))))
                                                    (.split false ⟨.spoke, 5, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨1, some 2, 3⟩, ⟨5, some 6, 3⟩]))
                                                      (.split false ⟨.spoke, 2, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, some 6, 4⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, some 6, 4⟩]))))))
                                                (.split false ⟨.spoke, 4, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨5, none, 0⟩, ⟨4, some 6, 5⟩, ⟨1, some 2, 3⟩, ⟨1, some 3, 2⟩, ⟨2, some 3, 2⟩]))
                                                  (.split false ⟨.spoke, 5, 6, false⟩
                                                    (.split false ⟨.spoke, 1, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, some 2, 2⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                                      (.split false ⟨.spoke, 2, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, some 2, 2⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩]))))
                                                    (.split false ⟨.hat, 4, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.spoke, 1, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨3, some 4, 2⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨1, some 2, 3⟩, ⟨3, some 4, 1⟩])))))))
                                              (.split false ⟨.fan1, 6, 6, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.spoke, 5, 6, true⟩
                                                  (.split false ⟨.spoke, 1, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 4⟩, ⟨2, some 3, 2⟩, ⟨2, some 4, 1⟩, ⟨3, some 4, 2⟩]))
                                                    (.split false ⟨.hat, 1, 6, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.spoke, 2, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 4⟩, ⟨3, some 4, 1⟩]))
                                                        (.split false ⟨.spoke, 3, 6, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 4⟩, ⟨3, some 4, 1⟩]))
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 4⟩]))))))
                                                  (.split false ⟨.spoke, 2, 6, false⟩
                                                    (.split false ⟨.spoke, 1, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩, ⟨3, some 4, 1⟩]))
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩, ⟨3, some 4, 1⟩])))
                                                    (.split false ⟨.hat, 3, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩, ⟨3, some 4, 1⟩]))
                                                      (.split false ⟨.fan1, 5, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩, ⟨1, some 2, 2⟩, ⟨3, some 4, 2⟩]))
                                                        (.split false ⟨.fan2, 5, 5, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩, ⟨1, some 2, 2⟩, ⟨3, some 4, 2⟩]))
                                                          (.split false ⟨.spoke, 1, 6, false⟩
                                                            (.split false ⟨.spoke, 3, 6, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩]))
                                                              (.split false ⟨.spoke, 4, 6, true⟩
                                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩]))
                                                                (.split false ⟨.hat, 1, 6, false⟩
                                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨4, none, 1⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩, ⟨2, some 3, 2⟩]))
                                                                  (.split false ⟨.hat, 2, 6, true⟩
                                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨4, none, 1⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩, ⟨1, some 2, 2⟩, ⟨1, some 3, 1⟩, ⟨2, some 3, 2⟩]))
                                                                    (.split false ⟨.hat, 4, 5, false⟩
                                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩, ⟨2, some 3, 1⟩]))
                                                                      (.split false ⟨.fan1, 4, 5, true⟩
                                                                        (.terminal .reducible)
                                                                        (.split false ⟨.fan1, 1, 5, false⟩
                                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨4, none, 1⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩, ⟨2, some 3, 2⟩]))
                                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩, ⟨2, some 3, 1⟩])))))))))
                                                            (.split false ⟨.spoke, 4, 6, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩, ⟨3, some 4, 1⟩]))
                                                              (.split false ⟨.hat, 5, 6, true⟩
                                                                (.terminal .reducible)
                                                                (.split false ⟨.spoke, 3, 6, false⟩
                                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩]))
                                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩]))))))))))))))))))))))))
                      (.split false ⟨.hat, 0, 5, false⟩
                        (.similar 0 ⟨true, 6⟩)
                        (.split true ⟨.spoke, 1, 7, false⟩
                          (.split false ⟨.spoke, 3, 7, false⟩
                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, some 6, 5⟩]))
                            (.split false ⟨.spoke, 4, 7, false⟩
                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨4, none, 0⟩, ⟨2, some 3, 2⟩, ⟨5, some 6, 5⟩]))
                              (.split false ⟨.spoke, 6, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨6, none, 0⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 4⟩]))
                                (.split false ⟨.spoke, 3, 6, false⟩
                                  (.split false ⟨.spoke, 2, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, some 4, 2⟩, ⟨5, some 6, 5⟩]))
                                    (.split false ⟨.spoke, 4, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, some 6, 5⟩]))
                                      (.split false ⟨.spoke, 5, 7, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 4⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩]))
                                        (.split false ⟨.spoke, 5, 6, true⟩
                                          (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨0, some 4, 3⟩, ⟨5, some 6, 5⟩]))
                                          (.split false ⟨.spoke, 6, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 4⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩]))
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨4, none, 0⟩, ⟨6, none, 3⟩, ⟨3, some 5, 4⟩])))))))
                                  (.split false ⟨.hat, 4, 6, false⟩
                                    (.terminal (.hubcap [⟨1, none, 0⟩, ⟨0, some 4, 3⟩, ⟨2, some 3, 2⟩, ⟨5, some 6, 5⟩]))
                                    (.split false ⟨.spoke, 5, 6, true⟩
                                      (.split false ⟨.spoke, 2, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 1⟩, ⟨3, some 6, 4⟩, ⟨4, some 5, 2⟩]))
                                        (.split false ⟨.spoke, 6, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨2, some 3, 2⟩]))
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨4, none, 0⟩, ⟨2, some 3, 2⟩, ⟨5, some 6, 5⟩]))))
                                      (.split false ⟨.spoke, 6, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨4, none, 2⟩, ⟨2, some 3, 3⟩, ⟨5, some 6, 3⟩]))
                                        (.split false ⟨.fan1, 6, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.spoke, 2, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 1⟩, ⟨6, none, 3⟩, ⟨3, some 4, 3⟩, ⟨3, some 5, 2⟩, ⟨4, some 5, 2⟩]))
                                            (.split false ⟨.spoke, 4, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨6, none, 3⟩, ⟨2, some 3, 2⟩, ⟨4, some 5, 2⟩]))
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨6, none, 3⟩, ⟨2, some 3, 3⟩, ⟨4, some 5, 1⟩]))))))))))))
                          (.split false ⟨.spoke, 6, 7, false⟩
                            (.similar 0 ⟨true, 6⟩)
                            (.split true ⟨.spoke, 1, 6, true⟩
                              (.split false ⟨.fan1, 1, 5, true⟩
                                (.terminal .reducible)
                                (.split true ⟨.spoke, 2, 6, true⟩
                                  (.split false ⟨.spoke, 3, 7, false⟩
                                    (.terminal (.hubcap [⟨3, none, -1⟩, ⟨0, some 1, 7⟩, ⟨2, some 6, 3⟩, ⟨4, some 5, 1⟩]))
                                    (.split false ⟨.spoke, 6, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨5, none, 0⟩, ⟨3, some 4, 1⟩, ⟨1, some 2, 5⟩, ⟨1, some 6, 5⟩, ⟨2, some 6, 3⟩]))
                                      (.split false ⟨.hat, 2, 5, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.fan1, 6, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.spoke, 5, 7, false⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨5, none, -1⟩, ⟨6, none, 3⟩, ⟨3, some 4, 1⟩]))
                                            (.split false ⟨.spoke, 3, 6, false⟩
                                              (.split false ⟨.spoke, 4, 7, false⟩
                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩]))
                                                (.split false ⟨.spoke, 4, 6, true⟩
                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, -1⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩]))
                                                  (.split false ⟨.spoke, 5, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩]))
                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩])))))
                                              (.split false ⟨.spoke, 5, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨6, none, 3⟩, ⟨4, some 5, 0⟩]))
                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩])))))))))
                                  (.split false ⟨.spoke, 5, 6, true⟩
                                    (.split false ⟨.spoke, 6, 6, true⟩
                                      (.similar 0 ⟨true, 6⟩)
                                      (.split false ⟨.hat, 6, 5, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.spoke, 2, 8, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -1⟩, ⟨3, none, 1⟩, ⟨6, none, 2⟩, ⟨4, some 5, 2⟩]))
                                          (.split false ⟨.spoke, 3, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨3, none, 1⟩, ⟨2, some 6, 2⟩, ⟨4, some 5, 1⟩]))
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨5, none, 0⟩, ⟨2, some 6, 2⟩, ⟨3, some 4, 2⟩]))))))
                                    (.split false ⟨.spoke, 6, 6, false⟩
                                      (.split false ⟨.spoke, 2, 8, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -1⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨3, some 4, 3⟩]))
                                        (.split false ⟨.spoke, 3, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨2, some 3, 2⟩]))
                                          (.split false ⟨.spoke, 4, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨3, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨2, some 4, 2⟩]))
                                            (.split false ⟨.spoke, 2, 7, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, -1⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨3, some 4, 3⟩]))
                                              (.split false ⟨.hat, 2, 5, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨2, some 3, 1⟩, ⟨2, some 4, 1⟩, ⟨3, some 4, 3⟩]))
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩])))))))
                                      (.split false ⟨.fan1, 6, 5, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.spoke, 3, 7, false⟩
                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩]))
                                          (.split false ⟨.spoke, 4, 7, false⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩]))
                                            (.split true ⟨.spoke, 3, 6, false⟩
                                              (.split false ⟨.spoke, 2, 7, false⟩
                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, -1⟩, ⟨4, none, 0⟩, ⟨6, none, 3⟩, ⟨3, some 5, 1⟩]))
                                                (.split false ⟨.spoke, 4, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩]))
                                                  (.split false ⟨.spoke, 5, 7, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨4, none, 0⟩, ⟨5, none, -1⟩, ⟨6, none, 3⟩, ⟨2, some 3, 1⟩]))
                                                    (.split false ⟨.hat, 2, 5, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, -1⟩, ⟨4, none, 0⟩, ⟨6, none, 3⟩, ⟨3, some 5, 1⟩]))
                                                      (.split false ⟨.hat, 4, 5, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.fan1, 1, 6, true⟩
                                                          (.terminal .reducible)
                                                          (.split false ⟨.fan1, 2, 5, true⟩
                                                            (.terminal .reducible)
                                                            (.split false ⟨.hat, 4, 6, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩]))
                                                              (.split false ⟨.hat, 6, 5, false⟩
                                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, -1⟩, ⟨6, none, 3⟩]))
                                                                (.split false ⟨.fan1, 6, 6, true⟩
                                                                  (.terminal .reducible)
                                                                  (.split false ⟨.fan2, 5, 5, true⟩
                                                                    (.terminal .reducible)
                                                                    (.split false ⟨.fan1, 3, 5, true⟩
                                                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩]))
                                                                      (.split false ⟨.fan2, 3, 5, false⟩
                                                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩]))
                                                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩])))))))))))))))
                                              (.split false ⟨.spoke, 4, 6, false⟩
                                                (.similar 0 ⟨true, 6⟩)
                                                (.split false ⟨.hat, 4, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨6, none, 3⟩, ⟨2, some 3, 0⟩, ⟨4, some 5, 0⟩]))))))))))))
                              (.split false ⟨.spoke, 6, 6, true⟩
                                (.similar 0 ⟨true, 6⟩)
                                (.split false ⟨.spoke, 3, 7, false⟩
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨5, none, 1⟩, ⟨1, some 6, 6⟩]))
                                  (.split false ⟨.spoke, 4, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨1, some 6, 6⟩]))
                                    (.split true ⟨.spoke, 2, 6, false⟩
                                      (.split false ⟨.spoke, 4, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 0⟩, ⟨5, none, 0⟩, ⟨1, some 2, 3⟩, ⟨4, some 6, 5⟩]))
                                        (.split false ⟨.spoke, 5, 7, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨1, some 2, 3⟩, ⟨3, some 4, 3⟩]))
                                          (.split false ⟨.spoke, 5, 6, false⟩
                                            (.split false ⟨.spoke, 2, 7, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                              (.split false ⟨.spoke, 3, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, some 6, 3⟩]))
                                                (.split false ⟨.hat, 2, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, some 2, 2⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                                  (.split false ⟨.hat, 3, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 0⟩, ⟨5, none, 1⟩, ⟨1, some 6, 4⟩, ⟨3, some 4, 3⟩]))
                                                    (.split false ⟨.hat, 4, 5, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 1⟩, ⟨1, some 6, 4⟩]))
                                                      (.split false ⟨.hat, 5, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 1⟩, ⟨5, none, 0⟩, ⟨1, some 6, 4⟩, ⟨3, some 4, 3⟩]))
                                                        (.split false ⟨.hat, 6, 5, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, some 2, 3⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 2⟩]))
                                                          (.split false ⟨.fan1, 1, 5, true⟩
                                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 2⟩]))
                                                            (.split false ⟨.fan1, 2, 5, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                                              (.split false ⟨.fan2, 6, 5, true⟩
                                                                (.terminal .reducible)
                                                                (.split false ⟨.fan1, 3, 6, true⟩
                                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩, ⟨3, some 4, 3⟩]))
                                                                  (.split false ⟨.fan1, 4, 5, false⟩
                                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩]))
                                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, some 6, 2⟩]))))))))))))))
                                            (.split false ⟨.spoke, 2, 7, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, some 4, 2⟩, ⟨5, some 6, 4⟩]))
                                              (.split false ⟨.spoke, 3, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨1, some 6, 6⟩, ⟨4, some 5, 1⟩]))
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨5, none, 0⟩, ⟨1, some 2, 3⟩, ⟨3, some 4, 2⟩, ⟨3, some 6, 4⟩, ⟨4, some 6, 5⟩])))))))
                                      (.split false ⟨.spoke, 5, 6, false⟩
                                        (.similar 0 ⟨true, 6⟩)
                                        (.split false ⟨.hat, 4, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 0⟩, ⟨5, none, 0⟩, ⟨1, some 6, 6⟩, ⟨3, some 4, 2⟩]))
                                          (.split true ⟨.spoke, 3, 6, false⟩
                                            (.split false ⟨.spoke, 4, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 0⟩, ⟨1, some 6, 6⟩]))
                                              (.split false ⟨.fan1, 1, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.fan2, 3, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.hat, 2, 5, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, some 5, 1⟩, ⟨4, some 6, 4⟩, ⟨5, some 6, 4⟩]))
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨6, none, 2⟩, ⟨4, some 5, 1⟩]))))))
                                            (.split false ⟨.spoke, 4, 6, false⟩
                                              (.similar 0 ⟨true, 6⟩)
                                              (.terminal .reducible))))))))))))))))))))))
    (.split false ⟨.spoke, 1, 5, true⟩
      (.similar 0 ⟨false, 1⟩)
      (.split false ⟨.spoke, 2, 5, true⟩
        (.similar 0 ⟨false, 2⟩)
        (.split false ⟨.spoke, 3, 5, true⟩
          (.similar 0 ⟨false, 3⟩)
          (.split false ⟨.spoke, 4, 5, true⟩
            (.similar 0 ⟨false, 4⟩)
            (.split false ⟨.spoke, 5, 5, true⟩
              (.similar 0 ⟨false, 5⟩)
              (.split false ⟨.spoke, 6, 5, true⟩
                (.similar 0 ⟨false, 6⟩)
                (.split true ⟨.spoke, 0, 6, false⟩
                  (.split true ⟨.spoke, 3, 6, false⟩
                    (.split false ⟨.spoke, 5, 7, false⟩
                      (.terminal (.hubcap [⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 0⟩, ⟨0, some 2, 5⟩, ⟨1, some 3, 5⟩]))
                      (.split true ⟨.spoke, 1, 6, false⟩
                        (.split false ⟨.spoke, 2, 6, false⟩
                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, some 6, 4⟩]))
                          (.split false ⟨.spoke, 3, 7, false⟩
                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, some 6, 4⟩]))
                            (.split false ⟨.spoke, 4, 6, false⟩
                              (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨0, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                              (.split false ⟨.spoke, 5, 6, false⟩
                                (.terminal (.hubcap [⟨2, none, 0⟩, ⟨4, none, 0⟩, ⟨6, none, 0⟩, ⟨0, some 5, 5⟩, ⟨1, some 3, 5⟩]))
                                (.split false ⟨.spoke, 6, 6, false⟩
                                  (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨4, none, 2⟩, ⟨6, none, 2⟩, ⟨3, some 5, 4⟩]))
                                  (.split false ⟨.spoke, 1, 7, false⟩
                                    (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨0, some 4, 3⟩, ⟨3, some 5, 6⟩, ⟨3, some 6, 5⟩, ⟨5, some 6, 4⟩]))
                                    (.split false ⟨.hat, 2, 6, false⟩
                                      (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨0, some 4, 3⟩, ⟨3, some 5, 6⟩, ⟨3, some 6, 5⟩, ⟨5, some 6, 4⟩]))
                                      (.split false ⟨.hat, 3, 6, false⟩
                                        (.terminal (.hubcap [⟨2, none, 0⟩, ⟨0, some 4, 3⟩, ⟨1, some 3, 3⟩, ⟨5, some 6, 4⟩]))
                                        (.split false ⟨.hat, 4, 6, false⟩
                                          (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, some 6, 3⟩, ⟨0, some 4, 3⟩, ⟨0, some 5, 4⟩, ⟨4, some 5, 4⟩]))
                                          (.split false ⟨.hat, 5, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 0⟩, ⟨4, none, 0⟩, ⟨1, some 3, 5⟩, ⟨5, some 6, 3⟩]))
                                            (.split false ⟨.hat, 5, 5, true⟩
                                              (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, some 6, 3⟩, ⟨4, some 5, 4⟩]))
                                              (.split false ⟨.spoke, 0, 7, false⟩
                                                (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, some 6, 5⟩, ⟨4, some 5, 3⟩]))
                                                (.split false ⟨.hat, 6, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 0⟩, ⟨4, none, 1⟩, ⟨1, some 3, 5⟩, ⟨5, some 6, 2⟩]))
                                                  (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨0, some 6, 3⟩, ⟨4, some 5, 3⟩])))))))))))))))
                        (.split false ⟨.spoke, 2, 6, false⟩
                          (.similar 0 ⟨true, 3⟩)
                          (.split true ⟨.hat, 2, 5, true⟩
                            (.split false ⟨.spoke, 4, 7, false⟩
                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨1, some 2, 3⟩, ⟨5, some 6, 3⟩]))
                              (.split false ⟨.spoke, 6, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 0⟩, ⟨1, some 2, 3⟩, ⟨4, some 5, 3⟩]))
                                (.split false ⟨.hat, 5, 6, false⟩
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨1, some 2, 3⟩, ⟨5, some 6, 3⟩]))
                                  (.split false ⟨.hat, 6, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 0⟩, ⟨1, some 2, 3⟩, ⟨4, some 5, 3⟩]))
                                    (.split false ⟨.fan1, 1, 5, true⟩
                                      (.split false ⟨.hat, 1, 5, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.fan1, 2, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.spoke, 3, 7, false⟩
                                            (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨0, some 4, 3⟩, ⟨5, some 6, 4⟩]))
                                            (.split false ⟨.spoke, 5, 6, false⟩
                                              (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨6, none, 0⟩, ⟨0, some 5, 5⟩]))
                                              (.split false ⟨.spoke, 6, 6, false⟩
                                                (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨6, none, 2⟩, ⟨0, some 3, 2⟩, ⟨4, some 5, 3⟩]))
                                                (.split false ⟨.spoke, 4, 6, false⟩
                                                  (.split false ⟨.spoke, 0, 7, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, some 6, 3⟩]))
                                                    (.split false ⟨.hat, 3, 5, false⟩
                                                      (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨0, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                                      (.split false ⟨.fan1, 2, 6, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.hat, 6, 5, false⟩
                                                          (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨0, some 4, 3⟩, ⟨5, some 6, 2⟩]))
                                                          (.split false ⟨.hat, 0, 6, false⟩
                                                            (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨0, some 3, 2⟩, ⟨5, some 6, 3⟩]))
                                                            (.split false ⟨.fan1, 3, 5, false⟩
                                                              (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨0, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                                              (.split false ⟨.fan1, 0, 5, false⟩
                                                                (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨0, some 5, 2⟩, ⟨4, some 6, 3⟩]))
                                                                (.split false ⟨.hat, 5, 5, true⟩
                                                                  (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 1⟩, ⟨0, some 4, 3⟩, ⟨0, some 5, 3⟩, ⟨4, some 5, 3⟩]))
                                                                  (.split false ⟨.hat, 0, 5, false⟩
                                                                    (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, some 6, 3⟩]))
                                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨5, none, 1⟩, ⟨4, some 6, 2⟩])))))))))))
                                                  (.split false ⟨.hat, 4, 5, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.spoke, 0, 7, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 4⟩]))
                                                      (.split false ⟨.hat, 3, 6, false⟩
                                                        (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨0, some 4, 3⟩, ⟨5, some 6, 4⟩]))
                                                        (.split false ⟨.fan1, 5, 6, false⟩
                                                          (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨5, none, 3⟩, ⟨0, some 4, 2⟩, ⟨3, some 6, 2⟩]))
                                                          (.split false ⟨.fan1, 5, 5, true⟩
                                                            (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩, ⟨3, some 4, 3⟩]))
                                                            (.split false ⟨.hat, 3, 5, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 2⟩, ⟨6, none, 1⟩]))
                                                              (.split false ⟨.fan1, 2, 6, true⟩
                                                                (.terminal .reducible)
                                                                (.split false ⟨.hat, 5, 5, false⟩
                                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 1⟩, ⟨3, some 4, 2⟩]))
                                                                  (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 2⟩, ⟨6, none, 1⟩]))))))))))))))))
                                      (.split false ⟨.fan1, 2, 5, false⟩
                                        (.split false ⟨.spoke, 0, 7, false⟩
                                          (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, some 6, 4⟩]))
                                          (.split false ⟨.spoke, 3, 7, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, some 6, 4⟩]))
                                            (.split false ⟨.spoke, 5, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 4⟩, ⟨6, none, 0⟩]))
                                              (.split false ⟨.fan1, 1, 6, true⟩
                                                (.split false ⟨.hat, 1, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.spoke, 4, 6, false⟩
                                                    (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨0, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                                    (.split false ⟨.spoke, 6, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨6, none, 2⟩, ⟨4, some 5, 3⟩]))
                                                      (.split false ⟨.hat, 3, 5, true⟩
                                                        (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, some 6, 3⟩, ⟨0, some 4, 3⟩, ⟨0, some 5, 4⟩, ⟨4, some 5, 4⟩]))
                                                        (.split false ⟨.hat, 4, 6, false⟩
                                                          (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨0, some 4, 3⟩, ⟨5, some 6, 4⟩]))
                                                          (.split false ⟨.hat, 5, 5, false⟩
                                                            (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨0, some 6, 3⟩, ⟨4, some 5, 3⟩]))
                                                            (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 4⟩]))))))))
                                                (.split false ⟨.fan1, 2, 6, true⟩
                                                  (.split false ⟨.hat, 3, 5, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.spoke, 4, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, some 6, 3⟩]))
                                                      (.split false ⟨.spoke, 6, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, some 6, 3⟩, ⟨4, some 5, 3⟩]))
                                                        (.split false ⟨.hat, 1, 5, true⟩
                                                          (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨0, some 4, 3⟩, ⟨3, some 5, 4⟩, ⟨3, some 6, 3⟩, ⟨5, some 6, 4⟩]))
                                                          (.split false ⟨.hat, 5, 5, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, some 6, 3⟩, ⟨4, some 5, 3⟩]))
                                                            (.split false ⟨.hat, 1, 6, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 4⟩]))
                                                              (.split false ⟨.hat, 4, 6, false⟩
                                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, some 4, 2⟩, ⟨5, some 6, 4⟩]))
                                                                (.split false ⟨.hat, 6, 5, false⟩
                                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 1⟩]))))))))))
                                                  (.split false ⟨.fan1, 5, 5, true⟩
                                                    (.split false ⟨.spoke, 4, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨6, none, 2⟩, ⟨4, some 5, 2⟩]))
                                                      (.split false ⟨.fan1, 4, 5, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.spoke, 6, 6, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, some 6, 2⟩]))
                                                          (.split false ⟨.fan1, 6, 5, true⟩
                                                            (.terminal .reducible)
                                                            (.split false ⟨.hat, 1, 6, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩]))
                                                              (.split false ⟨.hat, 1, 5, true⟩
                                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩, ⟨3, some 4, 3⟩]))
                                                                (.split false ⟨.hat, 3, 6, false⟩
                                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩]))
                                                                  (.split false ⟨.hat, 3, 5, true⟩
                                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩, ⟨3, some 4, 3⟩]))
                                                                    (.split false ⟨.hat, 4, 6, false⟩
                                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩]))
                                                                      (.split false ⟨.hat, 4, 5, true⟩
                                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩]))
                                                                        (.split false ⟨.hat, 5, 5, false⟩
                                                                          (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩, ⟨0, some 4, 3⟩]))
                                                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩])))))))))))))
                                                    (.split false ⟨.spoke, 4, 6, false⟩
                                                      (.split false ⟨.spoke, 6, 6, false⟩
                                                        (.similar 0 ⟨false, 3⟩)
                                                        (.split false ⟨.hat, 1, 6, false⟩
                                                          (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 1⟩, ⟨0, some 4, 3⟩]))
                                                          (.split false ⟨.hat, 1, 5, true⟩
                                                            (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 1⟩, ⟨0, some 3, 3⟩]))
                                                            (.split false ⟨.hat, 3, 5, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 1⟩]))
                                                              (.split false ⟨.hat, 5, 5, false⟩
                                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 2⟩, ⟨6, none, 1⟩]))
                                                                (.split false ⟨.hat, 6, 5, false⟩
                                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, some 6, 2⟩]))
                                                                  (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, 1⟩, ⟨0, some 5, 3⟩]))))))))
                                                      (.split false ⟨.hat, 6, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, some 6, 3⟩]))
                                                        (.split false ⟨.hat, 3, 6, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨4, none, 1⟩, ⟨3, some 5, 4⟩, ⟨3, some 6, 3⟩, ⟨5, some 6, 4⟩]))
                                                          (.split false ⟨.hat, 3, 5, true⟩
                                                            (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨4, none, 1⟩, ⟨0, some 3, 3⟩, ⟨5, some 6, 4⟩]))
                                                            (.split false ⟨.hat, 4, 6, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, some 6, 4⟩]))
                                                              (.split false ⟨.hat, 4, 5, true⟩
                                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨4, none, 1⟩, ⟨3, some 5, 4⟩, ⟨3, some 6, 3⟩, ⟨5, some 6, 4⟩]))
                                                                (.split false ⟨.spoke, 6, 6, false⟩
                                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨4, none, 1⟩, ⟨6, none, 2⟩, ⟨3, some 5, 3⟩]))
                                                                  (.split false ⟨.hat, 1, 6, false⟩
                                                                    (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨6, none, 1⟩, ⟨0, some 5, 4⟩]))
                                                                    (.split false ⟨.hat, 1, 5, true⟩
                                                                      (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨6, none, 1⟩, ⟨0, some 5, 4⟩]))
                                                                      (.split false ⟨.hat, 5, 5, false⟩
                                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 2⟩, ⟨6, none, 1⟩]))
                                                                        (.split false ⟨.fan1, 5, 6, true⟩
                                                                          (.terminal .reducible)
                                                                          (.split false ⟨.hat, 0, 6, false⟩
                                                                            (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 1⟩]))
                                                                            (.split false ⟨.hat, 0, 5, true⟩
                                                                              (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 1⟩]))
                                                                              (.split false ⟨.fan1, 0, 5, false⟩
                                                                                (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 1⟩]))
                                                                                (.split false ⟨.fan1, 3, 5, false⟩
                                                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 1⟩]))
                                                                                  (.split false ⟨.fan1, 4, 5, false⟩
                                                                                    (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨6, none, 1⟩, ⟨0, some 5, 4⟩]))
                                                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 1⟩]))))))))))))))))))))))))
                                        (.split false ⟨.hat, 3, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.spoke, 5, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨4, none, 0⟩, ⟨6, none, 0⟩, ⟨3, some 5, 5⟩]))
                                            (.split false ⟨.spoke, 0, 7, false⟩
                                              (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, some 6, 3⟩, ⟨4, some 5, 4⟩]))
                                              (.split false ⟨.spoke, 4, 6, false⟩
                                                (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨4, none, 2⟩, ⟨0, some 3, 2⟩, ⟨5, some 6, 3⟩]))
                                                (.split false ⟨.spoke, 6, 6, false⟩
                                                  (.split false ⟨.spoke, 3, 7, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨6, none, 2⟩, ⟨4, some 5, 3⟩]))
                                                    (.split false ⟨.hat, 1, 5, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, some 6, 3⟩, ⟨4, some 5, 3⟩]))
                                                      (.split false ⟨.fan1, 1, 6, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.hat, 4, 6, false⟩
                                                          (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨6, none, 2⟩, ⟨0, some 3, 2⟩, ⟨4, some 5, 3⟩]))
                                                          (.split false ⟨.hat, 5, 5, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, some 6, 3⟩, ⟨4, some 5, 2⟩]))
                                                            (.split false ⟨.fan1, 5, 5, true⟩
                                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨3, some 6, 2⟩]))
                                                              (.split false ⟨.hat, 4, 5, true⟩
                                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 1⟩, ⟨3, some 6, 3⟩]))
                                                                (.split false ⟨.hat, 6, 5, false⟩
                                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 2⟩, ⟨6, none, 1⟩]))
                                                                  (.split false ⟨.fan1, 5, 6, true⟩
                                                                    (.terminal .reducible)
                                                                    (.split false ⟨.fan1, 4, 5, false⟩
                                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩]))
                                                                      (.split false ⟨.hat, 3, 6, false⟩
                                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 2⟩, ⟨3, some 6, 2⟩]))
                                                                        (.split false ⟨.fan1, 3, 5, false⟩
                                                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 2⟩, ⟨3, some 6, 2⟩]))
                                                                          (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩]))))))))))))))
                                                  (.split false ⟨.hat, 0, 5, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.spoke, 3, 7, false⟩
                                                      (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨0, some 4, 3⟩, ⟨5, some 6, 4⟩]))
                                                      (.split false ⟨.hat, 1, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 4⟩]))
                                                        (.split false ⟨.fan1, 4, 5, true⟩
                                                          (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨6, none, 1⟩, ⟨0, some 4, 2⟩, ⟨3, some 5, 4⟩]))
                                                          (.split false ⟨.hat, 6, 5, false⟩
                                                            (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, some 6, 3⟩, ⟨0, some 4, 3⟩, ⟨0, some 5, 3⟩, ⟨4, some 5, 3⟩]))
                                                            (.split false ⟨.hat, 1, 5, false⟩
                                                              (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨0, some 4, 2⟩, ⟨5, some 6, 4⟩]))
                                                              (.split false ⟨.fan1, 1, 6, true⟩
                                                                (.terminal .reducible)
                                                                (.split false ⟨.fan1, 5, 5, true⟩
                                                                  (.terminal .reducible)
                                                                  (.split false ⟨.hat, 4, 5, false⟩
                                                                    (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨6, none, 1⟩, ⟨0, some 5, 4⟩]))
                                                                    (.split false ⟨.fan2, 3, 5, true⟩
                                                                      (.terminal .reducible)
                                                                      (.split false ⟨.hat, 5, 5, false⟩
                                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨6, none, 1⟩, ⟨4, some 5, 3⟩]))
                                                                        (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 1⟩]))))))))))))))))))))))))
                            (.split true ⟨.spoke, 4, 7, false⟩
                              (.split false ⟨.spoke, 5, 6, false⟩
                                (.similar 1 ⟨false, 4⟩)
                                (.split false ⟨.spoke, 6, 6, false⟩
                                  (.similar 1 ⟨false, 3⟩)
                                  (.split false ⟨.hat, 6, 5, true⟩
                                    (.similar 0 ⟨false, 4⟩)
                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨1, some 2, 2⟩, ⟨5, some 6, 2⟩])))))
                              (.split false ⟨.spoke, 6, 7, false⟩
                                (.similar 0 ⟨true, 3⟩)
                                (.split true ⟨.hat, 5, 6, false⟩
                                  (.split false ⟨.spoke, 0, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 0⟩, ⟨3, none, 4⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩, ⟨1, some 2, 2⟩]))
                                    (.split false ⟨.spoke, 3, 7, false⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩, ⟨1, some 2, 2⟩]))
                                      (.split false ⟨.spoke, 4, 6, false⟩
                                        (.terminal (.hubcap [⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨1, some 2, 2⟩, ⟨0, some 5, 5⟩, ⟨0, some 6, 5⟩, ⟨5, some 6, 3⟩]))
                                        (.split false ⟨.spoke, 5, 6, false⟩
                                          (.terminal (.hubcap [⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 0⟩, ⟨0, some 2, 4⟩, ⟨1, some 3, 4⟩]))
                                          (.split false ⟨.spoke, 6, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨1, some 2, 2⟩]))
                                            (.split false ⟨.hat, 1, 5, false⟩
                                              (.terminal (.hubcap [⟨2, none, 1⟩, ⟨4, none, 0⟩, ⟨1, some 3, 4⟩, ⟨0, some 5, 4⟩, ⟨0, some 6, 4⟩, ⟨5, some 6, 3⟩]))
                                              (.terminal (.hubcap [⟨4, none, 0⟩, ⟨6, none, 1⟩, ⟨0, some 2, 4⟩, ⟨0, some 5, 4⟩, ⟨1, some 2, 2⟩, ⟨1, some 3, 4⟩, ⟨3, some 5, 5⟩]))))))))
                                  (.split false ⟨.hat, 6, 6, false⟩
                                    (.similar 0 ⟨true, 3⟩)
                                    (.split true ⟨.spoke, 0, 7, false⟩
                                      (.split false ⟨.spoke, 6, 6, false⟩
                                        (.similar 1 ⟨false, 3⟩)
                                        (.split false ⟨.spoke, 3, 7, false⟩
                                          (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, some 6, 4⟩]))
                                          (.split false ⟨.spoke, 4, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩, ⟨1, some 2, 2⟩]))
                                            (.split false ⟨.spoke, 5, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 0⟩, ⟨3, none, 4⟩, ⟨4, none, 0⟩, ⟨5, none, 4⟩, ⟨6, none, 0⟩, ⟨1, some 2, 2⟩]))
                                              (.split false ⟨.hat, 2, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 4⟩, ⟨4, none, 2⟩, ⟨5, some 6, 4⟩]))
                                                (.split false ⟨.hat, 3, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, some 2, 2⟩, ⟨3, some 4, 4⟩, ⟨5, some 6, 4⟩]))
                                                  (.split false ⟨.hat, 4, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨1, some 2, 2⟩, ⟨5, some 6, 4⟩]))
                                                    (.split false ⟨.hat, 4, 5, true⟩
                                                      (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, some 6, 4⟩, ⟨4, some 5, 3⟩]))
                                                      (.split false ⟨.hat, 5, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, some 2, 2⟩, ⟨3, some 4, 5⟩, ⟨5, some 6, 3⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 1⟩, ⟨1, some 2, 2⟩])))))))))))
                                      (.split false ⟨.spoke, 3, 7, false⟩
                                        (.similar 0 ⟨true, 3⟩)
                                        (.split false ⟨.spoke, 5, 6, false⟩
                                          (.split false ⟨.spoke, 4, 6, false⟩
                                            (.similar 4 ⟨false, 4⟩)
                                            (.split false ⟨.spoke, 6, 6, false⟩
                                              (.similar 4 ⟨true, 0⟩)
                                              (.split false ⟨.hat, 1, 6, false⟩
                                                (.terminal (.hubcap [⟨2, none, 1⟩, ⟨4, none, 0⟩, ⟨6, none, 0⟩, ⟨0, some 5, 5⟩, ⟨1, some 3, 4⟩]))
                                                (.split false ⟨.hat, 3, 6, false⟩
                                                  (.terminal (.hubcap [⟨1, none, 1⟩, ⟨4, none, 0⟩, ⟨6, none, 0⟩, ⟨0, some 2, 4⟩, ⟨3, some 5, 5⟩]))
                                                  (.split false ⟨.fan1, 4, 5, true⟩
                                                    (.split false ⟨.hat, 1, 5, false⟩
                                                      (.terminal (.hubcap [⟨4, none, 0⟩, ⟨6, none, 0⟩, ⟨0, some 2, 4⟩, ⟨0, some 5, 6⟩, ⟨1, some 2, 2⟩, ⟨1, some 3, 4⟩, ⟨3, some 5, 5⟩]))
                                                      (.terminal (.hubcap [⟨4, none, 0⟩, ⟨6, none, 0⟩, ⟨3, some 5, 5⟩, ⟨0, some 1, 5⟩, ⟨0, some 2, 4⟩, ⟨1, some 2, 2⟩])))
                                                    (.split false ⟨.fan1, 6, 5, true⟩
                                                      (.split false ⟨.hat, 1, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 3⟩, ⟨6, none, 0⟩, ⟨1, some 3, 4⟩]))
                                                        (.split false ⟨.hat, 2, 6, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 4⟩, ⟨4, none, 0⟩, ⟨5, none, 3⟩, ⟨6, none, 0⟩]))
                                                          (.split false ⟨.hat, 3, 5, false⟩
                                                            (.terminal (.hubcap [⟨4, none, 0⟩, ⟨6, none, 0⟩, ⟨0, some 2, 4⟩, ⟨0, some 5, 5⟩, ⟨1, some 2, 2⟩, ⟨1, some 3, 4⟩, ⟨3, some 5, 6⟩]))
                                                            (.terminal (.hubcap [⟨4, none, 0⟩, ⟨6, none, 0⟩, ⟨0, some 5, 5⟩, ⟨1, some 2, 2⟩, ⟨1, some 3, 4⟩, ⟨2, some 3, 5⟩])))))
                                                      (.split true ⟨.hat, 1, 5, false⟩
                                                        (.split false ⟨.hat, 2, 6, false⟩
                                                          (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 4⟩, ⟨4, none, 0⟩, ⟨6, none, 0⟩, ⟨0, some 5, 6⟩]))
                                                          (.split false ⟨.hat, 3, 5, false⟩
                                                            (.terminal (.hubcap [⟨4, none, 0⟩, ⟨6, none, 0⟩, ⟨0, some 2, 4⟩, ⟨0, some 5, 6⟩, ⟨1, some 2, 1⟩, ⟨1, some 3, 4⟩, ⟨3, some 5, 6⟩]))
                                                            (.split false ⟨.hat, 4, 6, false⟩
                                                              (.terminal (.hubcap [⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨6, none, 0⟩, ⟨0, some 5, 6⟩, ⟨1, some 2, 2⟩]))
                                                              (.split false ⟨.hat, 4, 5, true⟩
                                                                (.terminal (.hubcap [⟨3, none, 3⟩, ⟨4, none, 0⟩, ⟨6, none, 0⟩, ⟨0, some 5, 6⟩, ⟨1, some 2, 1⟩]))
                                                                (.split false ⟨.hat, 0, 5, false⟩
                                                                  (.terminal (.hubcap [⟨4, none, 0⟩, ⟨5, none, 4⟩, ⟨6, none, 0⟩, ⟨0, some 2, 2⟩, ⟨1, some 3, 4⟩]))
                                                                  (.split false ⟨.fan1, 1, 5, false⟩
                                                                    (.terminal (.hubcap [⟨2, none, 0⟩, ⟨4, none, 0⟩, ⟨6, none, 0⟩, ⟨0, some 5, 6⟩, ⟨1, some 3, 4⟩]))
                                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 4⟩, ⟨6, none, 0⟩]))))))))
                                                        (.split false ⟨.hat, 3, 5, false⟩
                                                          (.similar 0 ⟨true, 3⟩)
                                                          (.split false ⟨.fan1, 3, 5, false⟩
                                                            (.split false ⟨.hat, 2, 6, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨4, none, 0⟩, ⟨6, none, 0⟩, ⟨3, some 5, 6⟩]))
                                                              (.split false ⟨.hat, 4, 6, false⟩
                                                                (.terminal (.hubcap [⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 4⟩, ⟨6, none, 0⟩, ⟨0, some 1, 5⟩, ⟨0, some 2, 4⟩, ⟨1, some 2, 2⟩]))
                                                                (.split false ⟨.hat, 0, 6, false⟩
                                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨4, none, 0⟩, ⟨6, none, 0⟩, ⟨1, some 2, 2⟩, ⟨3, some 5, 6⟩]))
                                                                  (.split false ⟨.fan1, 1, 6, true⟩
                                                                    (.terminal (.hubcap [⟨1, none, 0⟩, ⟨4, none, 0⟩, ⟨6, none, 0⟩, ⟨0, some 2, 4⟩, ⟨3, some 5, 6⟩]))
                                                                    (.split false ⟨.hat, 4, 5, true⟩
                                                                      (.terminal (.hubcap [⟨2, none, 0⟩, ⟨4, none, 0⟩, ⟨6, none, 0⟩, ⟨0, some 1, 4⟩, ⟨3, some 5, 6⟩]))
                                                                      (.split false ⟨.hat, 5, 5, false⟩
                                                                        (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨6, none, 0⟩, ⟨0, some 5, 6⟩]))
                                                                        (.split false ⟨.hat, 6, 5, true⟩
                                                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨2, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 3⟩, ⟨6, none, 0⟩, ⟨1, some 3, 3⟩]))
                                                                          (.split false ⟨.hat, 0, 5, false⟩
                                                                            (.terminal (.hubcap [⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 4⟩, ⟨6, none, 0⟩, ⟨0, some 1, 4⟩]))
                                                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 4⟩, ⟨6, none, 0⟩, ⟨1, some 3, 3⟩]))))))))))
                                                            (.split false ⟨.fan2, 0, 5, true⟩
                                                              (.terminal .reducible)
                                                              (.split false ⟨.hat, 2, 6, false⟩
                                                                (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 4⟩, ⟨4, none, 0⟩, ⟨6, none, 0⟩, ⟨0, some 5, 6⟩]))
                                                                (.split false ⟨.hat, 4, 6, false⟩
                                                                  (.terminal (.hubcap [⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨6, none, 0⟩, ⟨0, some 5, 6⟩, ⟨1, some 2, 2⟩]))
                                                                  (.split false ⟨.hat, 6, 5, false⟩
                                                                    (.terminal (.hubcap [⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 0⟩, ⟨0, some 2, 4⟩, ⟨1, some 3, 4⟩]))
                                                                    (.split false ⟨.hat, 0, 6, false⟩
                                                                      (.terminal (.hubcap [⟨0, none, 1⟩, ⟨4, none, 0⟩, ⟨5, none, 4⟩, ⟨6, none, 0⟩, ⟨1, some 2, 2⟩, ⟨1, some 3, 4⟩, ⟨2, some 3, 5⟩]))
                                                                      (.split false ⟨.fan1, 1, 6, false⟩
                                                                        (.terminal (.hubcap [⟨2, none, 0⟩, ⟨4, none, 0⟩, ⟨6, none, 0⟩, ⟨0, some 5, 6⟩, ⟨1, some 3, 4⟩]))
                                                                        (.split false ⟨.fan1, 1, 5, true⟩
                                                                          (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 0⟩, ⟨5, none, 4⟩, ⟨6, none, 0⟩]))
                                                                          (.split false ⟨.fan1, 2, 6, true⟩
                                                                            (.terminal .reducible)
                                                                            (.split false ⟨.fan2, 3, 5, true⟩
                                                                              (.terminal .reducible)
                                                                              (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 1⟩, ⟨3, none, 3⟩, ⟨4, none, 0⟩, ⟨6, none, 0⟩, ⟨0, some 5, 6⟩]))))))))))))))))))))
                                          (.split true ⟨.hat, 5, 5, false⟩
                                            (.split false ⟨.fan1, 2, 5, true⟩
                                              (.split false ⟨.spoke, 6, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 0⟩, ⟨6, none, 2⟩, ⟨1, some 3, 4⟩, ⟨4, some 5, 2⟩]))
                                                (.split false ⟨.hat, 0, 6, false⟩
                                                  (.terminal (.hubcap [⟨2, none, 0⟩, ⟨0, some 6, 3⟩, ⟨1, some 3, 4⟩, ⟨4, some 5, 3⟩]))
                                                  (.split false ⟨.hat, 2, 6, false⟩
                                                    (.split false ⟨.spoke, 4, 6, false⟩
                                                      (.similar 1 ⟨false, 4⟩)
                                                      (.split false ⟨.hat, 1, 5, false⟩
                                                        (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 3⟩, ⟨0, some 6, 4⟩, ⟨4, some 5, 3⟩]))
                                                        (.split false ⟨.hat, 3, 5, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨6, none, 1⟩, ⟨4, some 5, 3⟩]))
                                                          (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 3⟩, ⟨4, none, 1⟩, ⟨6, none, 1⟩, ⟨0, some 5, 5⟩])))))
                                                    (.split false ⟨.fan1, 1, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.spoke, 4, 6, false⟩
                                                        (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨0, some 5, 4⟩, ⟨0, some 6, 4⟩, ⟨5, some 6, 3⟩]))
                                                        (.split false ⟨.hat, 1, 6, false⟩
                                                          (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨0, some 6, 3⟩, ⟨4, some 5, 3⟩]))
                                                          (.split false ⟨.hat, 3, 5, false⟩
                                                            (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨0, some 6, 4⟩, ⟨4, some 5, 3⟩]))
                                                            (.split false ⟨.hat, 4, 5, true⟩
                                                              (.terminal .reducible)
                                                              (.split false ⟨.hat, 1, 5, true⟩
                                                                (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨6, none, 1⟩, ⟨0, some 5, 4⟩]))
                                                                (.split false ⟨.hat, 6, 5, false⟩
                                                                  (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨0, some 4, 4⟩, ⟨5, some 6, 2⟩]))
                                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, some 6, 3⟩]))))))))))))
                                              (.split false ⟨.hat, 3, 6, false⟩
                                                (.terminal (.hubcap [⟨1, none, 0⟩, ⟨0, some 2, 4⟩, ⟨3, some 6, 3⟩, ⟨4, some 5, 3⟩]))
                                                (.split true ⟨.spoke, 4, 6, false⟩
                                                  (.split false ⟨.spoke, 6, 6, false⟩
                                                    (.similar 4 ⟨false, 3⟩)
                                                    (.split false ⟨.hat, 2, 6, false⟩
                                                      (.similar 1 ⟨false, 4⟩)
                                                      (.split false ⟨.hat, 6, 5, true⟩
                                                        (.similar 3 ⟨false, 4⟩)
                                                        (.terminal (.hubcap [⟨1, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨0, some 2, 4⟩, ⟨5, some 6, 2⟩])))))
                                                  (.split false ⟨.fan1, 4, 5, true⟩
                                                    (.terminal (.hubcap [⟨4, none, 0⟩, ⟨0, some 6, 4⟩, ⟨1, some 2, 2⟩, ⟨3, some 5, 4⟩]))
                                                    (.split false ⟨.hat, 1, 6, false⟩
                                                      (.split false ⟨.spoke, 6, 6, false⟩
                                                        (.similar 2 ⟨false, 3⟩)
                                                        (.split false ⟨.hat, 2, 6, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, some 6, 5⟩, ⟨4, some 5, 3⟩]))
                                                          (.split false ⟨.hat, 3, 5, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 1⟩, ⟨3, some 6, 4⟩, ⟨4, some 5, 3⟩]))
                                                            (.terminal (.hubcap [⟨0, some 6, 3⟩, ⟨4, some 5, 3⟩, ⟨1, some 2, 1⟩, ⟨1, some 3, 4⟩, ⟨2, some 3, 4⟩])))))
                                                      (.split false ⟨.hat, 6, 5, false⟩
                                                        (.split false ⟨.spoke, 6, 6, false⟩
                                                          (.similar 0 ⟨true, 3⟩)
                                                          (.split false ⟨.hat, 3, 5, false⟩
                                                            (.terminal (.hubcap [⟨1, none, 0⟩, ⟨0, some 2, 4⟩, ⟨3, some 4, 4⟩, ⟨5, some 6, 2⟩]))
                                                            (.split false ⟨.hat, 1, 5, false⟩
                                                              (.terminal (.hubcap [⟨0, some 4, 4⟩, ⟨5, some 6, 2⟩, ⟨1, some 2, 1⟩, ⟨1, some 3, 4⟩, ⟨2, some 3, 4⟩]))
                                                              (.split false ⟨.hat, 2, 6, false⟩
                                                                (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨4, none, 1⟩, ⟨0, some 3, 7⟩, ⟨5, some 6, 2⟩]))
                                                                (.split false ⟨.hat, 4, 5, false⟩
                                                                  (.terminal (.hubcap [⟨4, none, 1⟩, ⟨0, some 1, 4⟩, ⟨2, some 3, 4⟩, ⟨5, some 6, 1⟩]))
                                                                  (.split false ⟨.hat, 0, 5, false⟩
                                                                    (.terminal (.hubcap [⟨1, none, 1⟩, ⟨3, none, 3⟩, ⟨4, none, 1⟩, ⟨0, some 2, 4⟩, ⟨5, some 6, 1⟩]))
                                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 1⟩, ⟨1, some 2, 1⟩, ⟨5, some 6, 2⟩]))))))))
                                                        (.split false ⟨.spoke, 6, 6, true⟩
                                                          (.terminal (.hubcap [⟨3, none, 2⟩, ⟨0, some 6, 3⟩, ⟨1, some 2, 2⟩, ⟨4, some 5, 3⟩]))
                                                          (.split false ⟨.hat, 1, 5, false⟩
                                                            (.similar 0 ⟨false, 3⟩)
                                                            (.split false ⟨.hat, 2, 6, false⟩
                                                              (.similar 2 ⟨true, 0⟩)
                                                              (.split false ⟨.hat, 4, 6, false⟩
                                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨1, some 2, 2⟩]))
                                                                (.split true ⟨.hat, 3, 5, false⟩
                                                                  (.split false ⟨.hat, 4, 5, false⟩
                                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩]))
                                                                    (.split false ⟨.fan1, 0, 5, true⟩
                                                                      (.terminal (.hubcap [⟨1, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩, ⟨0, some 2, 3⟩, ⟨3, some 4, 4⟩]))
                                                                      (.split false ⟨.fan1, 1, 5, false⟩
                                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 1⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩, ⟨3, some 4, 4⟩]))
                                                                        (.split false ⟨.fan1, 3, 5, false⟩
                                                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 2⟩, ⟨4, some 5, 2⟩]))
                                                                          (.split false ⟨.fan1, 4, 6, false⟩
                                                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨3, some 4, 4⟩]))
                                                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩])))))))
                                                                  (.split false ⟨.hat, 4, 5, false⟩
                                                                    (.similar 0 ⟨true, 0⟩)
                                                                    (.split false ⟨.fan1, 0, 5, true⟩
                                                                      (.terminal (.hubcap [⟨3, none, 3⟩, ⟨6, none, 2⟩, ⟨4, some 5, 2⟩, ⟨0, some 1, 2⟩, ⟨0, some 2, 3⟩, ⟨1, some 2, 2⟩]))
                                                                      (.split false ⟨.fan1, 1, 5, false⟩
                                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 3⟩, ⟨6, none, 2⟩, ⟨1, some 2, 1⟩, ⟨4, some 5, 2⟩]))
                                                                        (.split false ⟨.fan1, 2, 6, true⟩
                                                                          (.terminal .reducible)
                                                                          (.split false ⟨.fan1, 3, 5, false⟩
                                                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, some 6, 4⟩, ⟨4, some 5, 2⟩]))
                                                                            (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨6, none, 2⟩, ⟨4, some 5, 2⟩]))))))))))))))))))
                                            (.split false ⟨.spoke, 4, 6, false⟩
                                              (.similar 0 ⟨false, 4⟩)
                                              (.split false ⟨.spoke, 6, 6, false⟩
                                                (.similar 4 ⟨false, 3⟩)
                                                (.split false ⟨.hat, 6, 5, false⟩
                                                  (.similar 0 ⟨true, 3⟩)
                                                  (.split false ⟨.fan1, 5, 6, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.hat, 1, 5, false⟩
                                                      (.terminal (.hubcap [⟨4, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 1⟩, ⟨0, some 2, 2⟩, ⟨1, some 3, 3⟩]))
                                                      (.terminal (.hubcap [⟨0, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 1⟩, ⟨1, some 2, 2⟩])))))))))))))))))))
                    (.split false ⟨.spoke, 4, 6, false⟩
                      (.similar 0 ⟨false, 4⟩)
                      (.split true ⟨.hat, 4, 5, true⟩
                        (.split false ⟨.spoke, 2, 7, false⟩
                          (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, some 4, 4⟩, ⟨0, some 5, 6⟩, ⟨0, some 6, 4⟩, ⟨5, some 6, 3⟩]))
                          (.split false ⟨.spoke, 5, 7, false⟩
                            (.terminal (.hubcap [⟨5, none, 0⟩, ⟨6, none, 0⟩, ⟨3, some 4, 4⟩, ⟨0, some 1, 4⟩, ⟨0, some 2, 6⟩, ⟨1, some 2, 3⟩]))
                            (.split false ⟨.fan1, 3, 5, true⟩
                              (.split false ⟨.hat, 3, 5, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.fan1, 4, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.spoke, 0, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨5, some 6, 3⟩]))
                                    (.split false ⟨.spoke, 1, 7, false⟩
                                      (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨0, some 4, 4⟩, ⟨5, some 6, 3⟩]))
                                      (.split false ⟨.spoke, 6, 6, false⟩
                                        (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨0, some 1, 2⟩, ⟨5, some 6, 2⟩]))
                                        (.split false ⟨.hat, 6, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.spoke, 1, 6, false⟩
                                            (.terminal (.hubcap [⟨1, none, 1⟩, ⟨3, none, 1⟩, ⟨0, some 4, 4⟩, ⟨2, some 5, 4⟩, ⟨2, some 6, 2⟩, ⟨5, some 6, 3⟩]))
                                            (.split false ⟨.hat, 1, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨3, none, 1⟩, ⟨2, some 4, 4⟩, ⟨5, some 6, 3⟩]))
                                              (.split false ⟨.hat, 5, 5, false⟩
                                                (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨6, none, 0⟩, ⟨0, some 5, 5⟩]))
                                                (.split false ⟨.fan1, 4, 6, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.spoke, 5, 6, true⟩
                                                    (.terminal (.hubcap [⟨1, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨0, some 2, 3⟩, ⟨5, some 6, 3⟩]))
                                                    (.split false ⟨.spoke, 2, 6, false⟩
                                                      (.similar 0 ⟨false, 2⟩)
                                                      (.split false ⟨.hat, 2, 5, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.hat, 1, 5, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨6, none, 0⟩, ⟨2, some 5, 3⟩]))
                                                          (.split false ⟨.hat, 2, 6, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨6, none, 0⟩, ⟨2, some 5, 3⟩]))
                                                            (.split false ⟨.fan1, 2, 5, true⟩
                                                              (.terminal .reducible)
                                                              (.split false ⟨.hat, 3, 6, false⟩
                                                                (.terminal (.hubcap [⟨1, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 0⟩, ⟨0, some 2, 4⟩]))
                                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 0⟩])))))))))))))))))))
                              (.split true ⟨.spoke, 6, 6, false⟩
                                (.split false ⟨.spoke, 2, 6, false⟩
                                  (.similar 0 ⟨false, 6⟩)
                                  (.split false ⟨.spoke, 1, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 3⟩, ⟨6, none, 1⟩, ⟨4, some 5, 4⟩]))
                                    (.split false ⟨.spoke, 5, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨4, none, 1⟩, ⟨6, none, 0⟩, ⟨1, some 2, 3⟩, ⟨3, some 5, 4⟩]))
                                      (.split false ⟨.hat, 2, 6, false⟩
                                        (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 1⟩, ⟨6, none, 1⟩, ⟨0, some 3, 4⟩, ⟨4, some 5, 4⟩]))
                                        (.split false ⟨.fan1, 2, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.spoke, 0, 7, false⟩
                                            (.terminal (.hubcap [⟨0, none, 0⟩, ⟨6, none, 1⟩, ⟨1, some 2, 3⟩, ⟨3, some 4, 5⟩, ⟨3, some 5, 4⟩, ⟨4, some 5, 4⟩]))
                                            (.split false ⟨.hat, 1, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 1⟩, ⟨6, none, 1⟩, ⟨2, some 5, 3⟩, ⟨3, some 4, 5⟩]))
                                              (.split false ⟨.hat, 3, 5, true⟩
                                                (.terminal (.hubcap [⟨0, none, 1⟩, ⟨6, none, 1⟩, ⟨1, some 2, 3⟩, ⟨3, some 4, 5⟩, ⟨3, some 5, 3⟩, ⟨4, some 5, 3⟩]))
                                                (.split false ⟨.hat, 1, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 1⟩, ⟨6, none, 1⟩, ⟨2, some 3, 3⟩, ⟨4, some 5, 4⟩]))
                                                  (.split false ⟨.hat, 2, 5, true⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨6, none, 1⟩, ⟨2, some 3, 3⟩, ⟨4, some 5, 3⟩]))
                                                    (.split false ⟨.spoke, 6, 7, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 0⟩, ⟨4, some 5, 4⟩]))
                                                      (.split false ⟨.hat, 5, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 1⟩, ⟨4, some 5, 3⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩]))))))))))))))
                                (.split false ⟨.spoke, 1, 6, false⟩
                                  (.similar 0 ⟨true, 6⟩)
                                  (.split true ⟨.spoke, 2, 6, false⟩
                                    (.split false ⟨.spoke, 5, 6, false⟩
                                      (.similar 1 ⟨false, 2⟩)
                                      (.split false ⟨.spoke, 0, 7, false⟩
                                        (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨5, some 6, 3⟩]))
                                        (.split false ⟨.hat, 1, 6, false⟩
                                          (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨0, some 4, 4⟩, ⟨3, some 5, 4⟩, ⟨3, some 6, 2⟩, ⟨5, some 6, 3⟩]))
                                          (.split false ⟨.hat, 5, 6, false⟩
                                            (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨6, none, 1⟩, ⟨0, some 5, 4⟩]))
                                            (.split false ⟨.hat, 5, 5, true⟩
                                              (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨0, some 5, 4⟩, ⟨4, some 6, 3⟩]))
                                              (.terminal (.hubcap [⟨1, none, 0⟩, ⟨0, some 6, 4⟩, ⟨2, some 3, 3⟩, ⟨4, some 5, 3⟩])))))))
                                    (.split false ⟨.spoke, 5, 6, false⟩
                                      (.similar 0 ⟨true, 6⟩)
                                      (.split true ⟨.hat, 5, 5, false⟩
                                        (.split false ⟨.spoke, 0, 7, false⟩
                                          (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 1⟩, ⟨2, none, 3⟩, ⟨3, some 6, 3⟩, ⟨4, some 5, 3⟩]))
                                          (.split false ⟨.hat, 2, 6, false⟩
                                            (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 1⟩, ⟨4, some 5, 3⟩, ⟨0, some 3, 6⟩, ⟨0, some 6, 4⟩, ⟨3, some 6, 3⟩]))
                                            (.split false ⟨.fan1, 2, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.hat, 3, 6, false⟩
                                                (.terminal (.hubcap [⟨1, none, 1⟩, ⟨0, some 2, 4⟩, ⟨3, some 6, 2⟩, ⟨4, some 5, 3⟩]))
                                                (.split false ⟨.hat, 6, 5, true⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨6, none, 1⟩, ⟨2, some 3, 3⟩, ⟨4, some 5, 3⟩]))
                                                  (.split false ⟨.hat, 1, 6, false⟩
                                                    (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨6, none, 0⟩, ⟨0, some 3, 4⟩, ⟨4, some 5, 3⟩]))
                                                    (.split false ⟨.hat, 2, 5, true⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 0⟩, ⟨4, some 5, 3⟩]))
                                                      (.split false ⟨.hat, 3, 5, false⟩
                                                        (.terminal (.hubcap [⟨1, none, 0⟩, ⟨3, none, 2⟩, ⟨6, none, 0⟩, ⟨0, some 2, 5⟩, ⟨4, some 5, 3⟩]))
                                                        (.split false ⟨.fan1, 3, 6, true⟩
                                                          (.terminal .reducible)
                                                          (.split false ⟨.hat, 1, 5, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 3⟩, ⟨6, none, 0⟩, ⟨1, some 2, 2⟩, ⟨4, some 5, 3⟩]))
                                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨6, none, 0⟩, ⟨1, some 2, 3⟩, ⟨3, some 4, 4⟩, ⟨3, some 5, 4⟩, ⟨4, some 5, 3⟩]))))))))))))
                                        (.split false ⟨.hat, 3, 5, false⟩
                                          (.similar 0 ⟨true, 6⟩)
                                          (.split false ⟨.hat, 2, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.hat, 6, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.fan1, 2, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.fan1, 3, 6, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.fan1, 4, 6, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.fan1, 5, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.spoke, 0, 7, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨1, some 2, 3⟩, ⟨5, some 6, 3⟩]))
                                                        (.split false ⟨.hat, 1, 6, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨1, some 2, 2⟩, ⟨5, some 6, 3⟩]))
                                                          (.split false ⟨.hat, 2, 6, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, some 6, 3⟩]))
                                                            (.split false ⟨.hat, 6, 6, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 0⟩, ⟨1, some 2, 3⟩]))
                                                              (.split false ⟨.hat, 0, 6, false⟩
                                                                (.terminal (.hubcap [⟨0, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨1, some 2, 3⟩, ⟨5, some 6, 2⟩]))
                                                                (.split true ⟨.hat, 1, 5, false⟩
                                                                  (.split false ⟨.hat, 0, 5, false⟩
                                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨1, some 2, 2⟩, ⟨5, some 6, 2⟩]))
                                                                    (.split false ⟨.fan1, 0, 5, true⟩
                                                                      (.terminal .reducible)
                                                                      (.split false ⟨.fan1, 5, 6, false⟩
                                                                        (.terminal (.hubcap [⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, 0⟩, ⟨0, some 5, 4⟩, ⟨1, some 2, 2⟩]))
                                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 1⟩, ⟨1, some 2, 2⟩])))))
                                                                  (.split false ⟨.hat, 0, 5, false⟩
                                                                    (.similar 0 ⟨true, 6⟩)
                                                                    (.split false ⟨.fan1, 0, 5, true⟩
                                                                      (.terminal .reducible)
                                                                      (.split false ⟨.fan1, 1, 5, true⟩
                                                                        (.terminal .reducible)
                                                                        (.split false ⟨.fan1, 6, 5, true⟩
                                                                          (.terminal .reducible)
                                                                          (.split false ⟨.fan2, 0, 5, true⟩
                                                                            (.terminal .reducible)
                                                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨1, some 2, 2⟩, ⟨5, some 6, 2⟩]))))))))))))))))))))))))))))
                        (.split true ⟨.spoke, 2, 6, false⟩
                          (.split false ⟨.spoke, 5, 6, false⟩
                            (.similar 1 ⟨false, 2⟩)
                            (.split false ⟨.spoke, 6, 6, false⟩
                              (.similar 1 ⟨false, 6⟩)
                              (.split false ⟨.hat, 6, 5, true⟩
                                (.similar 0 ⟨false, 2⟩)
                                (.split false ⟨.spoke, 0, 7, false⟩
                                  (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 0⟩, ⟨2, none, 4⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                  (.split false ⟨.spoke, 1, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                    (.split false ⟨.spoke, 2, 7, false⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                      (.split false ⟨.hat, 5, 6, false⟩
                                        (.terminal (.hubcap [⟨1, none, 0⟩, ⟨3, none, 1⟩, ⟨6, none, 1⟩, ⟨0, some 5, 4⟩, ⟨2, some 4, 4⟩]))
                                        (.split false ⟨.hat, 5, 5, true⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                          (.split false ⟨.hat, 1, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 4⟩, ⟨3, some 4, 2⟩, ⟨5, some 6, 2⟩]))
                                            (.split false ⟨.hat, 2, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, some 4, 2⟩, ⟨5, some 6, 2⟩]))
                                              (.split false ⟨.hat, 3, 5, false⟩
                                                (.terminal (.hubcap [⟨1, none, 0⟩, ⟨0, some 2, 6⟩, ⟨3, some 4, 2⟩, ⟨5, some 6, 2⟩]))
                                                (.split false ⟨.hat, 2, 5, true⟩
                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, some 4, 1⟩, ⟨5, some 6, 2⟩]))
                                                  (.split false ⟨.hat, 6, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨6, none, 0⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 2⟩]))
                                                    (.split false ⟨.hat, 0, 5, false⟩
                                                      (.terminal (.hubcap [⟨1, none, 0⟩, ⟨0, some 2, 6⟩, ⟨3, some 4, 2⟩, ⟨5, some 6, 2⟩]))
                                                      (.split false ⟨.hat, 1, 5, true⟩
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 4⟩, ⟨3, some 4, 2⟩, ⟨5, some 6, 1⟩]))
                                                        (.split false ⟨.hat, 4, 6, false⟩
                                                          (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 4⟩, ⟨3, none, 0⟩, ⟨0, some 4, 4⟩, ⟨5, some 6, 2⟩]))
                                                          (.split false ⟨.fan1, 0, 5, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 4⟩, ⟨3, some 4, 2⟩, ⟨5, some 6, 2⟩]))
                                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨6, none, 0⟩, ⟨2, some 4, 4⟩, ⟨3, some 5, 2⟩])))))))))))))))))))
                          (.split false ⟨.spoke, 5, 6, false⟩
                            (.similar 0 ⟨false, 5⟩)
                            (.split true ⟨.hat, 3, 5, true⟩
                              (.split false ⟨.spoke, 6, 6, false⟩
                                (.similar 1 ⟨false, 6⟩)
                                (.split false ⟨.hat, 6, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.spoke, 0, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, some 2, 4⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                    (.split false ⟨.spoke, 1, 7, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                      (.split false ⟨.hat, 2, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                        (.split false ⟨.hat, 6, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 0⟩, ⟨1, some 2, 4⟩, ⟨3, some 4, 3⟩]))
                                          (.split false ⟨.hat, 0, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, some 2, 4⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 2⟩]))
                                            (.split false ⟨.hat, 5, 5, false⟩
                                              (.split false ⟨.spoke, 1, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, some 4, 3⟩, ⟨2, some 3, 3⟩, ⟨5, some 6, 2⟩]))
                                                (.split false ⟨.hat, 1, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, some 2, 4⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 2⟩]))
                                                  (.split false ⟨.hat, 1, 5, true⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, some 2, 4⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 1⟩]))
                                                    (.split false ⟨.hat, 2, 5, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, some 2, 3⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 2⟩]))
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 3⟩, ⟨3, some 4, 2⟩, ⟨5, some 6, 2⟩]))))))
                                              (.split false ⟨.spoke, 1, 6, false⟩
                                                (.similar 1 ⟨false, 1⟩)
                                                (.split false ⟨.hat, 2, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.fan1, 2, 5, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.fan1, 3, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.fan1, 4, 5, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.fan1, 5, 5, true⟩
                                                          (.terminal .reducible)
                                                          (.split false ⟨.hat, 1, 5, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, some 2, 2⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, some 2, 3⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 2⟩])))))))))))))))))
                              (.split false ⟨.hat, 5, 5, true⟩
                                (.similar 0 ⟨true, 6⟩)
                                (.split false ⟨.spoke, 0, 7, false⟩
                                  (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨2, some 3, 3⟩, ⟨5, some 6, 3⟩]))
                                  (.split false ⟨.spoke, 1, 6, false⟩
                                    (.terminal (.hubcap [⟨1, none, 2⟩, ⟨0, some 4, 3⟩, ⟨2, some 3, 2⟩, ⟨5, some 6, 3⟩]))
                                    (.split false ⟨.spoke, 6, 6, false⟩
                                      (.terminal (.hubcap [⟨6, none, 2⟩, ⟨0, some 3, 3⟩, ⟨1, some 2, 3⟩, ⟨4, some 5, 2⟩]))
                                      (.split false ⟨.hat, 2, 6, false⟩
                                        (.terminal (.hubcap [⟨1, none, 0⟩, ⟨0, some 6, 5⟩, ⟨2, some 3, 2⟩, ⟨4, some 5, 3⟩]))
                                        (.split false ⟨.hat, 6, 6, false⟩
                                          (.terminal (.hubcap [⟨6, none, 0⟩, ⟨0, some 1, 5⟩, ⟨2, some 3, 3⟩, ⟨4, some 5, 2⟩]))
                                          (.split true ⟨.hat, 2, 5, false⟩
                                            (.split false ⟨.hat, 1, 5, false⟩
                                              (.terminal (.hubcap [⟨1, none, 1⟩, ⟨0, some 6, 4⟩, ⟨2, some 3, 2⟩, ⟨4, some 5, 3⟩]))
                                              (.terminal (.hubcap [⟨6, none, 1⟩, ⟨0, some 5, 5⟩, ⟨1, some 2, 2⟩, ⟨3, some 4, 2⟩])))
                                            (.split false ⟨.hat, 6, 5, false⟩
                                              (.similar 0 ⟨true, 6⟩)
                                              (.split false ⟨.hat, 1, 5, true⟩
                                                (.terminal (.hubcap [⟨4, none, 1⟩, ⟨5, none, 2⟩, ⟨6, none, 1⟩, ⟨0, some 3, 3⟩, ⟨1, some 2, 3⟩]))
                                                (.split false ⟨.hat, 3, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨1, some 2, 3⟩, ⟨5, some 6, 3⟩]))
                                                  (.split false ⟨.hat, 5, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨4, none, 0⟩, ⟨2, some 3, 3⟩, ⟨5, some 6, 3⟩]))
                                                    (.split false ⟨.hat, 0, 6, false⟩
                                                      (.terminal (.hubcap [⟨1, none, 2⟩, ⟨0, some 4, 2⟩, ⟨2, some 3, 3⟩, ⟨5, some 6, 3⟩]))
                                                      (.split false ⟨.hat, 0, 5, true⟩
                                                        (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨0, some 4, 3⟩, ⟨5, some 6, 3⟩]))
                                                        (.split false ⟨.hat, 1, 6, false⟩
                                                          (.terminal (.hubcap [⟨4, none, 2⟩, ⟨0, some 1, 2⟩, ⟨2, some 3, 3⟩, ⟨5, some 6, 3⟩]))
                                                          (.split false ⟨.fan1, 0, 5, false⟩
                                                            (.terminal (.hubcap [⟨1, none, 2⟩, ⟨0, some 4, 2⟩, ⟨2, some 3, 3⟩, ⟨5, some 6, 3⟩]))
                                                            (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨0, some 4, 3⟩, ⟨5, some 6, 3⟩])))))))))))))))))))))))
                  (.split false ⟨.spoke, 1, 6, false⟩
                    (.similar 0 ⟨false, 1⟩)
                    (.split false ⟨.spoke, 2, 6, false⟩
                      (.similar 0 ⟨false, 2⟩)
                      (.split false ⟨.spoke, 3, 6, false⟩
                        (.similar 0 ⟨false, 3⟩)
                        (.split false ⟨.spoke, 4, 6, false⟩
                          (.similar 0 ⟨false, 4⟩)
                          (.split false ⟨.spoke, 5, 6, false⟩
                            (.similar 0 ⟨false, 5⟩)
                            (.split false ⟨.spoke, 6, 6, false⟩
                              (.similar 0 ⟨false, 6⟩)
                              (.split true ⟨.hat, 1, 5, true⟩
                                (.split false ⟨.hat, 4, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.hat, 5, 5, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.hat, 2, 6, false⟩
                                      (.terminal (.hubcap [⟨2, none, 1⟩, ⟨0, some 1, 4⟩, ⟨3, some 6, 3⟩, ⟨4, some 5, 2⟩]))
                                      (.split false ⟨.hat, 2, 5, true⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨1, some 3, 4⟩, ⟨4, some 5, 1⟩, ⟨4, some 6, 2⟩, ⟨5, some 6, 2⟩]))
                                        (.terminal (.hubcap [⟨1, some 2, 3⟩, ⟨4, some 5, 2⟩, ⟨0, some 3, 4⟩, ⟨0, some 6, 4⟩, ⟨3, some 6, 3⟩]))))))
                                (.split false ⟨.hat, 2, 5, true⟩
                                  (.similar 0 ⟨false, 1⟩)
                                  (.split false ⟨.hat, 3, 5, true⟩
                                    (.similar 0 ⟨false, 2⟩)
                                    (.split false ⟨.hat, 4, 5, true⟩
                                      (.similar 0 ⟨false, 3⟩)
                                      (.split false ⟨.hat, 5, 5, true⟩
                                        (.similar 0 ⟨false, 4⟩)
                                        (.split false ⟨.hat, 6, 5, true⟩
                                          (.similar 0 ⟨false, 5⟩)
                                          (.split false ⟨.hat, 0, 5, true⟩
                                            (.similar 0 ⟨false, 6⟩)
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, some 4, 2⟩, ⟨5, some 6, 2⟩])))))))))))))))))))))))

theorem structureCheck_eq_true :
    structureCheck arity code = true := by
  rfl

end ClassicalCertificatePresentationData7

end Mettapedia.GraphTheory.FourColor
