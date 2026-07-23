import Mettapedia.GraphTheory.FourColor.ClassicalCertificatePresentationCertificate

/-! Generated finite unavoidability presentation certificate. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificatePresentationData10

open ClassicalCertificatePresentationPattern
open ClassicalCertificatePresentationCertificate

def sourceSha256 : String := "047eb59bb00d53329ae7deaf618850aa704ceb3da061e579b3e15b2f72303eb0"
def arity : Nat := 10
def splitCount : Nat := 432
def leafCount : Nat := 433

def code : Code :=
  (.split true ⟨.spoke, 9, 5, false⟩
    (.split true ⟨.spoke, 8, 5, false⟩
      (.split true ⟨.spoke, 7, 5, false⟩
        (.split true ⟨.spoke, 6, 5, false⟩
          (.split true ⟨.spoke, 5, 5, false⟩
            (.split true ⟨.spoke, 4, 5, false⟩
              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 5⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨9, none, 4⟩, ⟨7, some 8, 6⟩]))
              (.split false ⟨.spoke, 0, 5, false⟩
                (.similar 0 ⟨false, 1⟩)
                (.split true ⟨.spoke, 3, 5, false⟩
                  (.split false ⟨.spoke, 2, 5, false⟩
                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 5⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, some 9, 7⟩]))
                    (.split false ⟨.spoke, 1, 5, false⟩
                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨9, none, 4⟩, ⟨7, some 8, 6⟩]))
                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨9, none, 4⟩, ⟨7, some 8, 6⟩]))))
                  (.split false ⟨.spoke, 1, 5, false⟩
                    (.similar 0 ⟨true, 5⟩)
                    (.split false ⟨.spoke, 2, 5, false⟩
                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 5⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, some 9, 7⟩]))
                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 5⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, some 7, 6⟩, ⟨8, some 9, 7⟩])))))))
            (.split false ⟨.spoke, 0, 5, false⟩
              (.similar 0 ⟨false, 1⟩)
              (.split true ⟨.spoke, 4, 5, false⟩
                (.split true ⟨.spoke, 3, 5, false⟩
                  (.split false ⟨.spoke, 2, 5, false⟩
                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, none, 4⟩, ⟨9, none, 4⟩]))
                    (.split false ⟨.spoke, 1, 5, false⟩
                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, some 9, 7⟩]))
                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨9, none, 4⟩, ⟨7, some 8, 6⟩]))))
                  (.split false ⟨.spoke, 2, 5, false⟩
                    (.split false ⟨.spoke, 1, 5, false⟩
                      (.similar 0 ⟨true, 4⟩)
                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 5⟩, ⟨3, none, 4⟩, ⟨4, none, 5⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨9, none, 4⟩, ⟨7, some 8, 6⟩])))
                    (.split false ⟨.spoke, 1, 5, false⟩
                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 5⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨9, none, 4⟩, ⟨7, some 8, 6⟩]))
                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 5⟩, ⟨3, none, 4⟩, ⟨4, none, 5⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨9, none, 4⟩, ⟨7, some 8, 6⟩])))))
                (.split false ⟨.spoke, 1, 5, false⟩
                  (.similar 0 ⟨true, 4⟩)
                  (.split true ⟨.spoke, 3, 5, false⟩
                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨9, none, 4⟩, ⟨2, some 3, 9⟩, ⟨7, some 8, 6⟩]))
                    (.split false ⟨.spoke, 2, 5, false⟩
                      (.similar 0 ⟨true, 4⟩)
                      (.split false ⟨.spoke, 6, 6, false⟩
                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 5⟩, ⟨3, none, 5⟩, ⟨4, none, 5⟩, ⟨5, none, 4⟩, ⟨6, some 7, 5⟩, ⟨8, some 9, 7⟩]))
                        (.split false ⟨.spoke, 7, 6, false⟩
                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 5⟩, ⟨3, none, 5⟩, ⟨4, none, 5⟩, ⟨5, none, 4⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨8, some 9, 5⟩]))
                          (.split false ⟨.spoke, 8, 6, false⟩
                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 5⟩, ⟨3, none, 5⟩, ⟨4, none, 5⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 2⟩, ⟨8, some 9, 6⟩]))
                            (.split false ⟨.spoke, 9, 6, false⟩
                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 5⟩, ⟨3, none, 5⟩, ⟨4, none, 5⟩, ⟨5, none, 4⟩, ⟨6, some 7, 7⟩, ⟨8, some 9, 5⟩]))
                              (.split false ⟨.hat, 6, 6, false⟩
                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 5⟩, ⟨3, none, 5⟩, ⟨4, none, 5⟩, ⟨5, none, 4⟩, ⟨6, some 7, 5⟩, ⟨8, some 9, 7⟩]))
                                (.split false ⟨.fan1, 6, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.hat, 7, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 5⟩, ⟨3, none, 5⟩, ⟨4, none, 5⟩, ⟨5, none, 4⟩, ⟨6, none, 3⟩, ⟨7, none, 2⟩, ⟨8, some 9, 7⟩]))
                                    (.split false ⟨.hat, 8, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 5⟩, ⟨3, none, 5⟩, ⟨4, none, 5⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 2⟩, ⟨8, none, 2⟩, ⟨9, none, 4⟩]))
                                      (.split false ⟨.hat, 9, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 5⟩, ⟨3, none, 5⟩, ⟨4, none, 5⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨9, none, 3⟩, ⟨7, some 8, 5⟩]))
                                        (.split false ⟨.hat, 0, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 5⟩, ⟨3, none, 5⟩, ⟨4, none, 5⟩, ⟨5, none, 4⟩, ⟨6, some 7, 7⟩, ⟨8, some 9, 5⟩]))
                                          (.split false ⟨.fan1, 9, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.hat, 8, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 5⟩, ⟨3, none, 5⟩, ⟨4, none, 5⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨9, none, 4⟩, ⟨7, some 8, 4⟩]))
                                              (.split true ⟨.hat, 1, 5, false⟩
                                                (.split false ⟨.hat, 1, 6, true⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 5⟩, ⟨3, none, 5⟩, ⟨4, none, 5⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, some 9, 6⟩]))
                                                  (.split false ⟨.hat, 2, 5, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 5⟩, ⟨3, none, 5⟩, ⟨4, none, 5⟩, ⟨5, none, 4⟩, ⟨6, some 7, 7⟩, ⟨8, some 9, 6⟩]))
                                                    (.split false ⟨.hat, 3, 6, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.hat, 4, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 5⟩, ⟨3, none, 4⟩, ⟨4, none, 5⟩, ⟨5, none, 4⟩, ⟨6, some 7, 7⟩, ⟨8, some 9, 6⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 5⟩, ⟨3, none, 5⟩, ⟨4, none, 5⟩, ⟨5, none, 4⟩, ⟨6, some 7, 6⟩, ⟨8, some 9, 6⟩]))))))
                                                (.split false ⟨.hat, 5, 5, false⟩
                                                  (.similar 0 ⟨true, 4⟩)
                                                  (.split false ⟨.hat, 2, 6, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.hat, 4, 6, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.hat, 6, 5, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.hat, 0, 5, true⟩
                                                          (.terminal .reducible)
                                                          (.split false ⟨.fan1, 7, 5, true⟩
                                                            (.terminal .reducible)
                                                            (.split false ⟨.fan1, 8, 5, true⟩
                                                              (.terminal .reducible)
                                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 5⟩, ⟨3, none, 5⟩, ⟨4, none, 5⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 2⟩, ⟨8, none, 2⟩, ⟨9, none, 4⟩]))))))))))))))))))))))))))))
          (.split false ⟨.spoke, 0, 5, false⟩
            (.similar 0 ⟨false, 1⟩)
            (.split true ⟨.spoke, 5, 5, false⟩
              (.split true ⟨.spoke, 4, 5, false⟩
                (.split false ⟨.spoke, 3, 5, false⟩
                  (.split false ⟨.spoke, 2, 5, false⟩
                    (.similar 0 ⟨false, 6⟩)
                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, some 9, 7⟩])))
                  (.split false ⟨.spoke, 2, 5, false⟩
                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 5⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, some 9, 7⟩]))
                    (.split false ⟨.spoke, 1, 5, false⟩
                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 8⟩, ⟨8, some 9, 7⟩]))
                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 5⟩, ⟨3, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, none, 4⟩, ⟨9, none, 4⟩, ⟨4, some 5, 6⟩])))))
                (.split false ⟨.spoke, 3, 5, false⟩
                  (.split false ⟨.spoke, 2, 5, false⟩
                    (.split false ⟨.spoke, 1, 5, false⟩
                      (.similar 0 ⟨false, 4⟩)
                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 5⟩, ⟨3, none, 4⟩, ⟨5, none, 5⟩, ⟨7, none, 4⟩, ⟨4, some 6, 7⟩, ⟨8, some 9, 7⟩])))
                    (.split false ⟨.spoke, 1, 5, false⟩
                      (.terminal (.hubcap [⟨1, none, 5⟩, ⟨3, none, 5⟩, ⟨5, none, 5⟩, ⟨7, none, 4⟩, ⟨0, some 2, 7⟩, ⟨4, some 6, 7⟩, ⟨8, some 9, 7⟩]))
                      (.split false ⟨.spoke, 3, 6, false⟩
                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, some 9, 7⟩]))
                        (.split false ⟨.spoke, 5, 6, false⟩
                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨8, none, 4⟩, ⟨9, none, 4⟩]))
                          (.split false ⟨.spoke, 7, 6, false⟩
                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨8, none, 2⟩, ⟨9, none, 4⟩]))
                            (.split false ⟨.spoke, 8, 6, false⟩
                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨8, some 9, 6⟩]))
                              (.split false ⟨.spoke, 9, 6, false⟩
                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, some 9, 5⟩]))
                                (.split false ⟨.hat, 1, 5, false⟩
                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨5, none, 5⟩, ⟨7, none, 4⟩, ⟨4, some 6, 7⟩, ⟨8, some 9, 6⟩]))
                                  (.split false ⟨.hat, 2, 6, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.hat, 0, 5, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.hat, 3, 5, false⟩
                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, some 9, 7⟩]))
                                        (.split false ⟨.fan1, 3, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.hat, 4, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, some 9, 7⟩]))
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, some 6, 7⟩, ⟨5, some 7, 8⟩, ⟨8, some 9, 7⟩])))))))))))))))
                  (.split false ⟨.spoke, 2, 5, false⟩
                    (.split false ⟨.spoke, 1, 5, false⟩
                      (.similar 0 ⟨true, 3⟩)
                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 5, 9⟩, ⟨8, some 9, 7⟩])))
                    (.split false ⟨.spoke, 1, 5, false⟩
                      (.terminal (.hubcap [⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 5, 8⟩, ⟨1, some 6, 8⟩, ⟨8, some 9, 7⟩]))
                      (.split false ⟨.spoke, 5, 6, true⟩
                        (.terminal .reducible)
                        (.split false ⟨.spoke, 5, 7, false⟩
                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 5⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨8, none, 4⟩, ⟨9, none, 4⟩]))
                          (.split false ⟨.spoke, 7, 6, false⟩
                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 5⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 2⟩, ⟨7, none, 4⟩, ⟨8, none, 2⟩, ⟨9, none, 4⟩]))
                            (.split false ⟨.spoke, 8, 6, false⟩
                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 5⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨8, none, 4⟩, ⟨9, none, 3⟩]))
                              (.split false ⟨.spoke, 9, 6, false⟩
                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 5⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨8, none, 2⟩, ⟨9, none, 4⟩]))
                                (.split false ⟨.hat, 1, 5, false⟩
                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 5⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨8, some 9, 6⟩]))
                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨3, none, 5⟩, ⟨5, none, 4⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨2, some 4, 8⟩, ⟨8, some 9, 7⟩]))))))))))))
              (.split false ⟨.spoke, 1, 5, false⟩
                (.similar 0 ⟨true, 3⟩)
                (.split true ⟨.spoke, 4, 5, false⟩
                  (.split false ⟨.spoke, 3, 5, false⟩
                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨3, some 4, 8⟩, ⟨8, some 9, 7⟩]))
                    (.split false ⟨.spoke, 2, 5, false⟩
                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 5⟩, ⟨3, none, 3⟩, ⟨4, none, 5⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, some 9, 7⟩]))
                      (.split false ⟨.spoke, 4, 6, true⟩
                        (.terminal .reducible)
                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 5⟩, ⟨3, none, 4⟩, ⟨4, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, none, 4⟩, ⟨9, none, 4⟩])))))
                  (.split false ⟨.spoke, 2, 5, false⟩
                    (.similar 0 ⟨true, 3⟩)
                    (.split false ⟨.spoke, 3, 5, true⟩
                      (.terminal .reducible)
                      (.split false ⟨.spoke, 3, 7, false⟩
                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 1⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, none, 4⟩, ⟨9, none, 4⟩]))
                        (.split false ⟨.spoke, 7, 6, false⟩
                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, some 9, 5⟩]))
                          (.split false ⟨.spoke, 8, 6, false⟩
                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨8, some 9, 6⟩]))
                            (.split false ⟨.spoke, 9, 6, false⟩
                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, some 9, 5⟩]))
                              (.split false ⟨.hat, 8, 6, false⟩
                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨8, none, 2⟩, ⟨9, none, 4⟩]))
                                (.split false ⟨.hat, 9, 6, false⟩
                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, none, 2⟩, ⟨9, none, 3⟩]))
                                  (.split false ⟨.fan1, 7, 5, true⟩
                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 2⟩, ⟨8, some 9, 7⟩]))
                                    (.split false ⟨.hat, 7, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨8, some 9, 6⟩]))
                                      (.split true ⟨.hat, 6, 5, false⟩
                                        (.split false ⟨.spoke, 3, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨9, none, 4⟩, ⟨7, some 8, 6⟩]))
                                          (.split false ⟨.hat, 2, 5, true⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨4, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨3, some 5, 9⟩, ⟨8, some 9, 6⟩]))
                                            (.split false ⟨.hat, 1, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, some 9, 6⟩]))
                                              (.split false ⟨.hat, 2, 6, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.hat, 0, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.hat, 3, 5, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, some 9, 7⟩]))
                                                    (.split false ⟨.fan1, 3, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.hat, 4, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 3⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, some 9, 7⟩]))
                                                        (.split false ⟨.hat, 4, 5, true⟩
                                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, some 9, 7⟩]))
                                                          (.split false ⟨.fan1, 3, 6, true⟩
                                                            (.terminal .reducible)
                                                            (.split false ⟨.hat, 5, 5, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, none, 4⟩, ⟨9, none, 4⟩]))
                                                              (.split false ⟨.hat, 6, 6, true⟩
                                                                (.terminal .reducible)
                                                                (.split false ⟨.hat, 7, 5, false⟩
                                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨8, none, 3⟩, ⟨9, none, 4⟩]))
                                                                  (.split false ⟨.hat, 8, 5, true⟩
                                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, some 8, 6⟩, ⟨7, some 9, 7⟩, ⟨8, some 9, 6⟩]))
                                                                    (.split false ⟨.hat, 9, 5, false⟩
                                                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨8, none, 3⟩, ⟨9, none, 3⟩]))
                                                                      (.split false ⟨.hat, 0, 6, false⟩
                                                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨9, none, 3⟩, ⟨7, some 8, 6⟩]))
                                                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨9, none, 4⟩, ⟨7, some 8, 5⟩]))))))))))))))))))
                                        (.split false ⟨.hat, 1, 5, false⟩
                                          (.similar 0 ⟨true, 3⟩)
                                          (.split false ⟨.hat, 2, 6, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.hat, 5, 6, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.hat, 7, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.hat, 0, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.fan1, 8, 5, true⟩
                                                    (.terminal .reducible)
                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, some 9, 6⟩]))))))))))))))))))))))))
        (.split false ⟨.spoke, 0, 5, false⟩
          (.similar 0 ⟨false, 1⟩)
          (.split true ⟨.spoke, 5, 5, false⟩
            (.split true ⟨.spoke, 4, 5, false⟩
              (.split false ⟨.spoke, 3, 5, false⟩
                (.similar 0 ⟨false, 6⟩)
                (.split false ⟨.spoke, 6, 5, false⟩
                  (.similar 0 ⟨false, 7⟩)
                  (.split true ⟨.spoke, 2, 5, false⟩
                    (.split false ⟨.spoke, 1, 5, false⟩
                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 8⟩, ⟨8, some 9, 8⟩]))
                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 5, 9⟩, ⟨3, some 4, 7⟩, ⟨8, some 9, 8⟩])))
                    (.split false ⟨.spoke, 1, 5, false⟩
                      (.similar 0 ⟨true, 6⟩)
                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 5⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, some 9, 6⟩]))))))
              (.split false ⟨.spoke, 2, 5, false⟩
                (.split false ⟨.spoke, 3, 5, false⟩
                  (.similar 0 ⟨false, 4⟩)
                  (.split false ⟨.spoke, 1, 6, false⟩
                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, none, 5⟩, ⟨9, none, 4⟩]))
                    (.split false ⟨.spoke, 2, 7, false⟩
                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 1⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, none, 5⟩, ⟨9, none, 5⟩]))
                      (.split false ⟨.spoke, 5, 7, false⟩
                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 5⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, none, 5⟩, ⟨9, none, 5⟩]))
                        (.split false ⟨.spoke, 6, 6, false⟩
                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 5⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨8, none, 4⟩, ⟨9, none, 5⟩]))
                          (.split false ⟨.spoke, 8, 6, false⟩
                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 5⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, some 9, 6⟩]))
                            (.split false ⟨.spoke, 9, 6, false⟩
                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 5⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, some 9, 6⟩]))
                              (.split false ⟨.hat, 8, 6, false⟩
                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 5⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, some 9, 6⟩]))
                                (.split false ⟨.fan1, 8, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.hat, 9, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 5⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, none, 3⟩, ⟨9, none, 3⟩]))
                                    (.split false ⟨.hat, 0, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 5⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, some 9, 6⟩]))
                                      (.split false ⟨.fan1, 9, 5, true⟩
                                        (.terminal .reducible)
                                        (.split true ⟨.hat, 3, 5, true⟩
                                          (.split false ⟨.hat, 4, 6, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.spoke, 1, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 2, 7⟩, ⟨8, some 9, 8⟩]))
                                              (.split false ⟨.spoke, 2, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 4⟩, ⟨3, none, 3⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, some 9, 8⟩]))
                                                (.split false ⟨.fan1, 2, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.spoke, 5, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 5⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, some 9, 8⟩]))
                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 5⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨7, none, 4⟩, ⟨5, some 6, 7⟩, ⟨8, some 9, 8⟩])))))))
                                          (.split false ⟨.hat, 5, 5, true⟩
                                            (.similar 0 ⟨true, 2⟩)
                                            (.split false ⟨.spoke, 2, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 2, 7⟩, ⟨8, some 9, 8⟩]))
                                              (.split false ⟨.spoke, 5, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 5⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨7, none, 4⟩, ⟨5, some 6, 7⟩, ⟨8, some 9, 8⟩]))
                                                (.split true ⟨.spoke, 1, 5, false⟩
                                                  (.split false ⟨.spoke, 6, 5, false⟩
                                                    (.similar 1 ⟨false, 7⟩)
                                                    (.split false ⟨.hat, 6, 5, true⟩
                                                      (.similar 0 ⟨false, 3⟩)
                                                      (.split false ⟨.hat, 8, 5, true⟩
                                                        (.similar 0 ⟨true, 9⟩)
                                                        (.split false ⟨.hat, 1, 5, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, none, 5⟩, ⟨9, none, 3⟩]))
                                                          (.split false ⟨.fan1, 1, 5, true⟩
                                                            (.terminal .reducible)
                                                            (.split false ⟨.hat, 2, 6, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, none, 5⟩, ⟨9, none, 4⟩]))
                                                              (.split false ⟨.hat, 3, 6, false⟩
                                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, some 9, 8⟩]))
                                                                (.split false ⟨.fan1, 2, 5, true⟩
                                                                  (.terminal .reducible)
                                                                  (.split false ⟨.hat, 4, 5, false⟩
                                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 4⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, none, 5⟩, ⟨9, none, 4⟩]))
                                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 2, 8⟩, ⟨5, some 6, 8⟩, ⟨8, some 9, 8⟩])))))))))))
                                                  (.split false ⟨.spoke, 6, 5, false⟩
                                                    (.similar 0 ⟨false, 7⟩)
                                                    (.terminal .reducible)))))))))))))))))))
                (.split true ⟨.spoke, 1, 5, false⟩
                  (.split false ⟨.spoke, 1, 7, false⟩
                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, none, 5⟩, ⟨9, none, 4⟩]))
                    (.split false ⟨.spoke, 3, 6, false⟩
                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, some 9, 8⟩]))
                      (.split false ⟨.spoke, 5, 7, false⟩
                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, some 9, 8⟩]))
                        (.split false ⟨.spoke, 6, 6, false⟩
                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨8, none, 4⟩, ⟨9, none, 4⟩]))
                          (.split false ⟨.spoke, 8, 7, false⟩
                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, none, 0⟩, ⟨9, none, 3⟩]))
                            (.split false ⟨.spoke, 9, 6, false⟩
                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, some 9, 6⟩]))
                              (.split false ⟨.spoke, 8, 6, false⟩
                                (.split false ⟨.spoke, 1, 6, false⟩
                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, none, 4⟩, ⟨9, none, 3⟩]))
                                  (.split false ⟨.spoke, 3, 5, false⟩
                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨3, none, 5⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 4, 7⟩, ⟨8, some 9, 6⟩]))
                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨7, none, 4⟩, ⟨5, some 6, 8⟩, ⟨8, some 9, 6⟩]))))
                                (.split false ⟨.spoke, 5, 6, false⟩
                                  (.terminal (.hubcap [⟨3, none, 5⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 2, 7⟩, ⟨1, some 4, 8⟩, ⟨8, some 9, 8⟩]))
                                  (.split false ⟨.hat, 1, 5, false⟩
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, some 9, 7⟩]))
                                    (.split false ⟨.hat, 5, 6, false⟩
                                      (.terminal (.hubcap [⟨3, none, 5⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 2, 7⟩, ⟨1, some 4, 8⟩, ⟨8, some 9, 8⟩]))
                                      (.split false ⟨.fan1, 5, 5, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.hat, 8, 6, false⟩
                                          (.terminal (.hubcap [⟨1, none, 5⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 2, 7⟩, ⟨8, some 9, 6⟩]))
                                          (.split false ⟨.fan1, 8, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.hat, 9, 6, false⟩
                                              (.terminal (.hubcap [⟨1, none, 5⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, none, 3⟩, ⟨9, none, 3⟩, ⟨0, some 2, 7⟩]))
                                              (.split false ⟨.hat, 0, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, some 9, 6⟩]))
                                                (.split false ⟨.fan1, 9, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.hat, 0, 5, false⟩
                                                    (.split false ⟨.spoke, 1, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, none, 4⟩, ⟨9, none, 4⟩]))
                                                      (.split false ⟨.fan1, 1, 5, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.spoke, 3, 5, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨3, none, 5⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 4, 7⟩, ⟨8, some 9, 7⟩]))
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨7, none, 4⟩, ⟨5, some 6, 8⟩, ⟨8, some 9, 7⟩])))))
                                                    (.split false ⟨.spoke, 1, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 2, 7⟩, ⟨8, some 9, 8⟩]))
                                                      (.split false ⟨.spoke, 3, 5, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.fan1, 1, 5, true⟩
                                                          (.terminal .reducible)
                                                          (.split false ⟨.spoke, 6, 5, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨2, none, 3⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, none, 4⟩, ⟨9, none, 4⟩, ⟨1, some 3, 9⟩]))
                                                            (.split false ⟨.hat, 4, 5, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, some 9, 8⟩]))
                                                              (.split false ⟨.fan1, 3, 5, true⟩
                                                                (.terminal .reducible)
                                                                (.split false ⟨.hat, 5, 5, false⟩
                                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, none, 5⟩, ⟨9, none, 4⟩]))
                                                                  (.split false ⟨.hat, 6, 5, false⟩
                                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨2, none, 3⟩, ⟨4, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 3, 9⟩, ⟨5, some 6, 8⟩, ⟨8, some 9, 8⟩]))
                                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨2, none, 3⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 3, 9⟩, ⟨8, some 9, 7⟩])))))))))))))))))))))))))))
                  (.split false ⟨.spoke, 3, 5, false⟩
                    (.split false ⟨.spoke, 6, 5, false⟩
                      (.similar 0 ⟨true, 5⟩)
                      (.split false ⟨.spoke, 3, 7, false⟩
                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, some 9, 8⟩]))
                        (.split false ⟨.spoke, 5, 7, false⟩
                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, some 9, 8⟩]))
                          (.split false ⟨.spoke, 8, 6, false⟩
                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 3⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, some 9, 6⟩]))
                            (.split false ⟨.spoke, 9, 6, false⟩
                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 3⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, some 9, 6⟩]))
                              (.split false ⟨.hat, 1, 5, false⟩
                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨4, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨3, some 5, 9⟩, ⟨8, some 9, 7⟩]))
                                (.split false ⟨.hat, 2, 6, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.hat, 0, 5, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.spoke, 3, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, some 9, 8⟩]))
                                      (.split false ⟨.spoke, 5, 6, true⟩
                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, none, 4⟩, ⟨9, none, 5⟩]))
                                        (.split false ⟨.hat, 3, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, none, 4⟩, ⟨9, none, 5⟩]))
                                          (.split false ⟨.fan1, 3, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.hat, 4, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, none, 4⟩, ⟨9, none, 5⟩]))
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 3⟩, ⟨7, none, 4⟩, ⟨5, some 6, 7⟩, ⟨8, some 9, 8⟩])))))))))))))))
                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 5⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨7, none, 4⟩, ⟨5, some 6, 6⟩, ⟨8, some 9, 6⟩]))))))
            (.split false ⟨.spoke, 2, 5, false⟩
              (.similar 0 ⟨true, 2⟩)
              (.split true ⟨.spoke, 3, 5, false⟩
                (.split false ⟨.spoke, 4, 5, false⟩
                  (.split true ⟨.spoke, 1, 5, false⟩
                    (.split false ⟨.spoke, 1, 6, false⟩
                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 5⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨8, some 9, 8⟩]))
                      (.split false ⟨.spoke, 3, 6, false⟩
                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨8, some 9, 8⟩]))
                        (.split false ⟨.spoke, 4, 6, false⟩
                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 3⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨4, some 5, 7⟩, ⟨8, some 9, 8⟩]))
                          (.split false ⟨.spoke, 6, 5, false⟩
                            (.terminal (.hubcap [⟨1, none, 5⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨6, none, 5⟩, ⟨8, none, 4⟩, ⟨9, none, 4⟩, ⟨0, some 2, 7⟩, ⟨5, some 7, 7⟩]))
                            (.split false ⟨.spoke, 8, 6, false⟩
                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨4, some 7, 8⟩, ⟨8, some 9, 6⟩]))
                              (.split false ⟨.spoke, 9, 6, false⟩
                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 5⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨8, some 9, 6⟩]))
                                (.split false ⟨.hat, 1, 5, false⟩
                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 5⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨8, some 9, 7⟩]))
                                  (.split false ⟨.fan1, 1, 5, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.hat, 2, 5, false⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨8, none, 5⟩, ⟨9, none, 4⟩, ⟨3, some 4, 7⟩]))
                                      (.split false ⟨.fan1, 1, 6, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.hat, 3, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨3, some 4, 7⟩, ⟨8, some 9, 8⟩]))
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨3, some 4, 8⟩, ⟨8, some 9, 7⟩])))))))))))))
                    (.split false ⟨.spoke, 6, 5, false⟩
                      (.similar 0 ⟨false, 5⟩)
                      (.split false ⟨.spoke, 3, 6, false⟩
                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨3, some 4, 6⟩, ⟨8, some 9, 8⟩]))
                        (.split false ⟨.spoke, 4, 6, false⟩
                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 3⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨4, some 5, 7⟩, ⟨8, some 9, 8⟩]))
                          (.split false ⟨.spoke, 8, 6, false⟩
                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨3, some 4, 8⟩, ⟨8, some 9, 6⟩]))
                            (.split false ⟨.spoke, 9, 6, false⟩
                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨3, some 4, 8⟩, ⟨8, some 9, 6⟩]))
                              (.split false ⟨.hat, 3, 6, false⟩
                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨3, some 4, 6⟩, ⟨8, some 9, 8⟩]))
                                (.split false ⟨.fan1, 3, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.hat, 4, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨8, some 9, 8⟩]))
                                    (.split false ⟨.hat, 5, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨3, some 4, 6⟩, ⟨8, some 9, 8⟩]))
                                      (.split false ⟨.fan1, 4, 5, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.hat, 8, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨3, some 4, 8⟩, ⟨8, some 9, 6⟩]))
                                          (.split false ⟨.fan1, 8, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.hat, 9, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨8, none, 3⟩, ⟨9, none, 3⟩, ⟨3, some 4, 8⟩]))
                                              (.split false ⟨.hat, 0, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨3, some 4, 8⟩, ⟨8, some 9, 6⟩]))
                                                (.split false ⟨.fan1, 9, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split true ⟨.hat, 1, 5, false⟩
                                                    (.split false ⟨.hat, 1, 6, true⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 5⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨8, some 9, 7⟩]))
                                                      (.split false ⟨.hat, 2, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨3, some 4, 7⟩, ⟨8, some 9, 7⟩]))
                                                        (.split false ⟨.hat, 3, 5, true⟩
                                                          (.terminal .reducible)
                                                          (.split false ⟨.hat, 5, 5, true⟩
                                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨3, some 4, 7⟩, ⟨8, some 9, 7⟩]))
                                                            (.split false ⟨.hat, 6, 5, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨8, some 9, 7⟩]))
                                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨8, some 9, 6⟩])))))))
                                                    (.split false ⟨.hat, 2, 5, false⟩
                                                      (.similar 0 ⟨true, 7⟩)
                                                      (.split false ⟨.hat, 6, 5, false⟩
                                                        (.similar 0 ⟨false, 5⟩)
                                                        (.split false ⟨.hat, 7, 5, false⟩
                                                          (.similar 0 ⟨true, 2⟩)
                                                          (.terminal .reducible)))))))))))))))))))))
                  (.split false ⟨.spoke, 1, 6, false⟩
                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 5⟩, ⟨9, none, 4⟩, ⟨7, some 8, 7⟩]))
                    (.split false ⟨.spoke, 3, 7, false⟩
                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 2⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, some 9, 9⟩, ⟨7, some 8, 7⟩]))
                      (.split false ⟨.spoke, 6, 7, false⟩
                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩, ⟨8, none, 4⟩, ⟨9, none, 5⟩]))
                        (.split false ⟨.spoke, 8, 7, false⟩
                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨8, none, 0⟩, ⟨9, none, 3⟩]))
                          (.split false ⟨.spoke, 9, 7, false⟩
                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨8, none, 3⟩, ⟨9, none, 0⟩]))
                            (.split false ⟨.spoke, 6, 5, true⟩
                              (.split false ⟨.spoke, 1, 5, false⟩
                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨2, none, 3⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨1, some 3, 9⟩, ⟨8, some 9, 6⟩]))
                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 2⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨8, some 9, 6⟩])))
                              (.split false ⟨.spoke, 8, 6, false⟩
                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨8, some 9, 6⟩]))
                                (.split false ⟨.spoke, 1, 5, false⟩
                                  (.split false ⟨.spoke, 3, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨9, none, 4⟩, ⟨7, some 8, 7⟩]))
                                    (.split false ⟨.spoke, 6, 6, false⟩
                                      (.terminal (.hubcap [⟨1, none, 5⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨8, none, 4⟩, ⟨9, none, 4⟩, ⟨0, some 2, 7⟩]))
                                      (.terminal (.hubcap [⟨1, none, 5⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨0, some 2, 7⟩, ⟨7, some 8, 7⟩, ⟨7, some 9, 7⟩, ⟨8, some 9, 7⟩]))))
                                  (.split false ⟨.spoke, 9, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨7, none, 4⟩, ⟨3, some 6, 9⟩, ⟨8, some 9, 6⟩]))
                                    (.split false ⟨.spoke, 6, 6, true⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨8, some 9, 7⟩]))
                                      (.split false ⟨.spoke, 3, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨8, some 9, 8⟩]))
                                        (.split false ⟨.hat, 1, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨8, some 9, 7⟩]))
                                          (.split false ⟨.hat, 2, 6, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.hat, 0, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.hat, 3, 5, false⟩
                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨8, none, 4⟩, ⟨9, none, 5⟩]))
                                                (.split false ⟨.fan1, 3, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.hat, 4, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 3⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨8, none, 4⟩, ⟨9, none, 5⟩]))
                                                    (.split false ⟨.hat, 4, 5, true⟩
                                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨8, none, 4⟩, ⟨9, none, 5⟩]))
                                                      (.split false ⟨.fan1, 3, 6, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.hat, 5, 5, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨8, none, 4⟩, ⟨9, none, 5⟩]))
                                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, some 7, 6⟩, ⟨8, some 9, 8⟩])))))))))))))))))))))))
                (.split false ⟨.spoke, 4, 5, false⟩
                  (.similar 0 ⟨true, 2⟩)
                  (.split true ⟨.spoke, 1, 5, false⟩
                    (.split false ⟨.spoke, 1, 7, false⟩
                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 5⟩, ⟨5, none, 5⟩, ⟨6, none, 5⟩, ⟨9, none, 4⟩, ⟨7, some 8, 7⟩]))
                      (.split false ⟨.spoke, 6, 7, false⟩
                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 5⟩, ⟨5, none, 4⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩, ⟨8, none, 4⟩, ⟨9, none, 4⟩]))
                        (.split false ⟨.spoke, 8, 7, false⟩
                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 5⟩, ⟨5, none, 5⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨8, none, 0⟩, ⟨9, none, 3⟩]))
                          (.split false ⟨.spoke, 9, 6, false⟩
                            (.terminal (.hubcap [⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 5⟩, ⟨6, none, 5⟩, ⟨0, some 5, 7⟩, ⟨1, some 7, 8⟩, ⟨8, some 9, 6⟩]))
                            (.split true ⟨.spoke, 1, 6, false⟩
                              (.split false ⟨.spoke, 6, 6, false⟩
                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 5⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨8, none, 4⟩, ⟨9, none, 4⟩]))
                                (.split false ⟨.spoke, 8, 6, true⟩
                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 5⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨8, some 9, 7⟩]))
                                  (.split false ⟨.spoke, 6, 5, false⟩
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 5⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨8, none, 4⟩, ⟨9, none, 3⟩]))
                                    (.split false ⟨.hat, 1, 5, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 5⟩, ⟨5, none, 5⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨8, none, 4⟩, ⟨9, none, 2⟩]))
                                      (.split false ⟨.hat, 2, 5, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 5⟩, ⟨5, none, 5⟩, ⟨6, none, 5⟩, ⟨1, some 9, 6⟩, ⟨7, some 8, 7⟩]))
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, 5⟩, ⟨4, none, 5⟩, ⟨5, none, 5⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨8, some 9, 6⟩])))))))
                              (.split false ⟨.spoke, 6, 6, false⟩
                                (.similar 0 ⟨true, 2⟩)
                                (.split false ⟨.spoke, 6, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.hat, 0, 5, true⟩
                                    (.terminal .reducible)
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 5⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨8, some 9, 6⟩]))))))))))
                    (.split false ⟨.spoke, 6, 5, false⟩
                      (.similar 0 ⟨true, 2⟩)
                      (.terminal .reducible)))))))))
      (.split false ⟨.spoke, 0, 5, false⟩
        (.similar 0 ⟨false, 1⟩)
        (.split true ⟨.spoke, 6, 5, false⟩
          (.split false ⟨.spoke, 5, 5, false⟩
            (.similar 0 ⟨false, 7⟩)
            (.split false ⟨.spoke, 7, 5, false⟩
              (.similar 0 ⟨false, 8⟩)
              (.split true ⟨.spoke, 3, 5, false⟩
                (.split false ⟨.spoke, 2, 5, false⟩
                  (.similar 0 ⟨false, 4⟩)
                  (.split false ⟨.spoke, 4, 5, false⟩
                    (.similar 0 ⟨false, 5⟩)
                    (.split false ⟨.spoke, 1, 5, false⟩
                      (.split false ⟨.spoke, 1, 6, false⟩
                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨7, none, 4⟩, ⟨8, none, 4⟩, ⟨6, some 9, 9⟩]))
                        (.split false ⟨.spoke, 3, 7, false⟩
                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨8, none, 4⟩, ⟨9, none, 5⟩]))
                          (.split false ⟨.spoke, 6, 7, false⟩
                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 1⟩, ⟨7, none, 4⟩, ⟨8, none, 4⟩, ⟨9, none, 5⟩]))
                            (.split false ⟨.spoke, 6, 6, true⟩
                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨8, none, 4⟩, ⟨9, none, 4⟩]))
                              (.split false ⟨.spoke, 9, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, none, 4⟩, ⟨9, none, 2⟩]))
                                (.split false ⟨.hat, 5, 5, true⟩
                                  (.terminal (.hubcap [⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨8, none, 4⟩, ⟨9, none, 5⟩, ⟨0, some 2, 7⟩, ⟨1, some 3, 9⟩, ⟨6, some 7, 7⟩]))
                                  (.split false ⟨.spoke, 9, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, none, 4⟩, ⟨9, none, 4⟩]))
                                    (.split false ⟨.spoke, 3, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, none, 4⟩, ⟨9, none, 5⟩]))
                                      (.split false ⟨.hat, 1, 5, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, none, 4⟩, ⟨9, none, 5⟩]))
                                        (.terminal (.hubcap [⟨1, none, 5⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨8, none, 4⟩, ⟨0, some 2, 7⟩, ⟨7, some 9, 8⟩])))))))))))
                      (.split false ⟨.spoke, 3, 7, false⟩
                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 1⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨8, none, 4⟩, ⟨9, none, 5⟩]))
                        (.split false ⟨.spoke, 6, 7, false⟩
                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 1⟩, ⟨7, none, 4⟩, ⟨8, none, 4⟩, ⟨9, none, 5⟩]))
                          (.split false ⟨.spoke, 9, 7, false⟩
                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨8, none, 4⟩, ⟨9, none, 1⟩]))
                            (.split false ⟨.spoke, 6, 6, true⟩
                              (.split false ⟨.spoke, 3, 6, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.spoke, 9, 6, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.hat, 1, 6, true⟩
                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨8, some 9, 7⟩]))
                                    (.split false ⟨.hat, 2, 5, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨8, none, 4⟩, ⟨9, none, 4⟩]))
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨8, none, 4⟩, ⟨9, none, 4⟩, ⟨3, some 4, 7⟩]))))))
                              (.split false ⟨.hat, 4, 5, true⟩
                                (.terminal (.hubcap [⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, none, 4⟩, ⟨0, some 3, 8⟩, ⟨4, some 9, 8⟩]))
                                (.split false ⟨.hat, 5, 5, false⟩
                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨7, none, 4⟩, ⟨8, none, 4⟩, ⟨9, none, 5⟩, ⟨3, some 6, 8⟩]))
                                  (.split false ⟨.hat, 6, 5, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.spoke, 9, 6, true⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨8, none, 4⟩, ⟨9, none, 5⟩, ⟨2, some 3, 7⟩, ⟨6, some 7, 7⟩]))
                                      (.split false ⟨.spoke, 3, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨8, none, 4⟩, ⟨9, none, 4⟩, ⟨6, some 7, 7⟩]))
                                        (.split false ⟨.hat, 1, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨8, none, 4⟩, ⟨9, none, 4⟩, ⟨6, some 7, 7⟩]))
                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, some 7, 7⟩, ⟨8, some 9, 7⟩])))))))))))))))
                (.split false ⟨.spoke, 2, 5, false⟩
                  (.similar 0 ⟨false, 3⟩)
                  (.split true ⟨.spoke, 1, 5, false⟩
                    (.split false ⟨.spoke, 1, 7, false⟩
                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 5⟩, ⟨7, none, 4⟩, ⟨8, none, 4⟩, ⟨9, none, 5⟩, ⟨5, some 6, 8⟩]))
                      (.split false ⟨.spoke, 4, 5, false⟩
                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨5, none, 3⟩, ⟨7, none, 4⟩, ⟨8, none, 4⟩, ⟨1, some 9, 9⟩, ⟨4, some 6, 9⟩]))
                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 5⟩, ⟨5, none, 4⟩, ⟨6, none, 2⟩, ⟨7, none, 4⟩, ⟨8, none, 4⟩, ⟨1, some 9, 9⟩]))))
                    (.split false ⟨.spoke, 4, 5, false⟩
                      (.similar 0 ⟨true, 4⟩)
                      (.split false ⟨.spoke, 6, 6, true⟩
                        (.terminal .reducible)
                        (.split false ⟨.spoke, 9, 6, true⟩
                          (.terminal .reducible)
                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 5⟩, ⟨3, none, 5⟩, ⟨4, none, 5⟩, ⟨5, none, 4⟩, ⟨6, none, 2⟩, ⟨7, none, 4⟩, ⟨8, none, 4⟩, ⟨9, none, 2⟩]))))))))))
          (.split false ⟨.spoke, 2, 5, false⟩
            (.similar 0 ⟨false, 3⟩)
            (.split false ⟨.spoke, 4, 5, false⟩
              (.split false ⟨.spoke, 1, 5, false⟩
                (.similar 0 ⟨false, 5⟩)
                (.split false ⟨.spoke, 3, 5, false⟩
                  (.similar 1 ⟨false, 5⟩)
                  (.split false ⟨.spoke, 5, 5, false⟩
                    (.similar 1 ⟨false, 6⟩)
                    (.split false ⟨.spoke, 7, 5, false⟩
                      (.similar 0 ⟨false, 8⟩)
                      (.split false ⟨.spoke, 4, 6, true⟩
                        (.terminal .reducible)
                        (.split false ⟨.spoke, 9, 6, true⟩
                          (.terminal .reducible)
                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 5⟩, ⟨3, none, 4⟩, ⟨4, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 5⟩, ⟨8, none, 4⟩, ⟨9, none, 2⟩]))))))))
              (.split true ⟨.spoke, 3, 5, false⟩
                (.split true ⟨.spoke, 1, 5, false⟩
                  (.split false ⟨.spoke, 1, 7, false⟩
                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨7, none, 5⟩, ⟨8, none, 4⟩, ⟨6, some 9, 9⟩]))
                    (.split false ⟨.spoke, 3, 7, false⟩
                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨5, none, 5⟩, ⟨7, none, 5⟩, ⟨8, none, 4⟩, ⟨3, some 4, 5⟩, ⟨6, some 9, 9⟩]))
                      (.split false ⟨.spoke, 5, 7, false⟩
                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 3⟩, ⟨7, none, 5⟩, ⟨8, none, 4⟩, ⟨9, none, 5⟩, ⟨5, some 6, 5⟩]))
                        (.split false ⟨.spoke, 7, 7, false⟩
                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨8, none, 3⟩, ⟨9, none, 5⟩, ⟨6, some 7, 5⟩]))
                          (.split false ⟨.spoke, 9, 7, false⟩
                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨7, none, 5⟩, ⟨3, some 6, 9⟩, ⟨8, some 9, 5⟩]))
                            (.split true ⟨.hat, 3, 5, false⟩
                              (.split false ⟨.spoke, 1, 6, false⟩
                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨7, none, 5⟩, ⟨8, none, 4⟩, ⟨6, some 9, 9⟩]))
                                (.split true ⟨.spoke, 5, 6, false⟩
                                  (.split false ⟨.spoke, 3, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 5⟩, ⟨8, none, 4⟩, ⟨9, none, 5⟩]))
                                    (.split false ⟨.spoke, 7, 5, false⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 3⟩, ⟨7, none, 5⟩, ⟨8, none, 4⟩, ⟨9, none, 5⟩]))
                                      (.split false ⟨.spoke, 9, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 5⟩, ⟨8, none, 4⟩, ⟨9, none, 4⟩]))
                                        (.split false ⟨.hat, 1, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 5⟩, ⟨8, none, 4⟩, ⟨9, none, 5⟩]))
                                          (.split false ⟨.fan1, 1, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.hat, 2, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 5⟩, ⟨8, none, 4⟩, ⟨9, none, 5⟩]))
                                              (.split false ⟨.fan1, 1, 6, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.hat, 3, 6, true⟩
                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 5⟩, ⟨8, none, 4⟩, ⟨9, none, 5⟩, ⟨4, some 5, 6⟩]))
                                                  (.split false ⟨.hat, 4, 5, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 5⟩, ⟨8, none, 4⟩, ⟨9, none, 5⟩]))
                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨7, none, 5⟩, ⟨8, none, 4⟩, ⟨9, none, 5⟩, ⟨5, some 6, 7⟩])))))))))))
                                  (.split false ⟨.spoke, 3, 6, false⟩
                                    (.terminal (.hubcap [⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨5, none, 5⟩, ⟨7, none, 5⟩, ⟨0, some 8, 7⟩, ⟨3, some 4, 6⟩, ⟨6, some 9, 9⟩]))
                                    (.split false ⟨.hat, 1, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 5⟩, ⟨8, none, 4⟩, ⟨9, none, 5⟩]))
                                      (.split false ⟨.fan1, 1, 5, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.hat, 2, 5, false⟩
                                          (.terminal (.hubcap [⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 5⟩, ⟨9, none, 5⟩, ⟨0, some 8, 7⟩]))
                                          (.split false ⟨.fan1, 1, 6, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.hat, 4, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨9, none, 5⟩, ⟨3, some 6, 7⟩, ⟨4, some 7, 8⟩, ⟨5, some 8, 8⟩]))
                                              (.split false ⟨.fan1, 3, 5, true⟩
                                                (.terminal .reducible)
                                                (.split true ⟨.spoke, 7, 5, false⟩
                                                  (.split false ⟨.spoke, 5, 5, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨9, none, 5⟩, ⟨1, some 8, 8⟩, ⟨4, some 6, 7⟩, ⟨5, some 7, 9⟩]))
                                                    (.split false ⟨.spoke, 7, 6, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.hat, 5, 6, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.hat, 0, 5, false⟩
                                                          (.similar 0 ⟨true, 7⟩)
                                                          (.split false ⟨.spoke, 9, 6, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, none, 2⟩, ⟨9, none, 4⟩]))
                                                            (.split false ⟨.fan1, 9, 5, true⟩
                                                              (.terminal .reducible)
                                                              (.split false ⟨.hat, 1, 5, false⟩
                                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨8, none, 3⟩, ⟨9, none, 5⟩]))
                                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨9, none, 5⟩, ⟨7, some 8, 6⟩])))))))))
                                                  (.split false ⟨.spoke, 5, 5, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.spoke, 9, 6, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.hat, 5, 5, false⟩
                                                        (.similar 0 ⟨false, 2⟩)
                                                        (.split false ⟨.hat, 0, 5, false⟩
                                                          (.similar 0 ⟨true, 7⟩)
                                                          (.split false ⟨.hat, 3, 6, true⟩
                                                            (.terminal .reducible)
                                                            (.split false ⟨.fan1, 5, 5, true⟩
                                                              (.terminal .reducible)
                                                              (.split false ⟨.hat, 1, 5, false⟩
                                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 5⟩, ⟨8, none, 4⟩, ⟨9, none, 4⟩]))
                                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 5⟩, ⟨8, some 9, 7⟩])))))))))))))))))))
                              (.split false ⟨.hat, 0, 5, false⟩
                                (.similar 0 ⟨true, 7⟩)
                                (.split true ⟨.spoke, 5, 5, true⟩
                                  (.split false ⟨.spoke, 1, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨2, some 7, 7⟩, ⟨3, some 8, 8⟩, ⟨6, some 9, 9⟩]))
                                    (.split false ⟨.spoke, 7, 5, true⟩
                                      (.terminal (.hubcap [⟨1, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 5⟩, ⟨7, none, 5⟩, ⟨8, none, 4⟩, ⟨9, none, 4⟩, ⟨0, some 2, 5⟩]))
                                      (.split false ⟨.hat, 1, 5, false⟩
                                        (.similar 0 ⟨false, 8⟩)
                                        (.split false ⟨.hat, 8, 5, false⟩
                                          (.similar 0 ⟨true, 9⟩)
                                          (.split false ⟨.hat, 2, 6, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.fan1, 1, 5, true⟩
                                              (.terminal .reducible)
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨7, none, 5⟩, ⟨8, none, 3⟩, ⟨9, none, 4⟩, ⟨3, some 6, 8⟩]))))))))
                                  (.split false ⟨.spoke, 7, 5, true⟩
                                    (.similar 0 ⟨false, 2⟩)
                                    (.split false ⟨.hat, 1, 5, false⟩
                                      (.similar 1 ⟨false, 8⟩)
                                      (.split false ⟨.hat, 2, 5, false⟩
                                        (.similar 1 ⟨true, 5⟩)
                                        (.split false ⟨.hat, 4, 5, false⟩
                                          (.similar 1 ⟨true, 3⟩)
                                          (.split false ⟨.hat, 5, 5, false⟩
                                            (.similar 1 ⟨false, 2⟩)
                                            (.split false ⟨.hat, 6, 5, false⟩
                                              (.similar 1 ⟨true, 1⟩)
                                              (.split false ⟨.hat, 7, 5, false⟩
                                                (.similar 1 ⟨false, 4⟩)
                                                (.split false ⟨.hat, 8, 5, false⟩
                                                  (.similar 1 ⟨true, 9⟩)
                                                  (.split false ⟨.hat, 9, 5, false⟩
                                                    (.similar 1 ⟨false, 6⟩)
                                                    (.split false ⟨.spoke, 1, 6, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.spoke, 3, 6, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.spoke, 5, 6, true⟩
                                                          (.terminal .reducible)
                                                          (.split false ⟨.spoke, 7, 6, true⟩
                                                            (.terminal .reducible)
                                                            (.split false ⟨.spoke, 9, 6, true⟩
                                                              (.terminal .reducible)
                                                              (.split false ⟨.fan1, 1, 5, true⟩
                                                                (.terminal .reducible)
                                                                (.split false ⟨.fan1, 3, 5, true⟩
                                                                  (.terminal .reducible)
                                                                  (.split false ⟨.fan1, 5, 5, true⟩
                                                                    (.terminal .reducible)
                                                                    (.split false ⟨.fan1, 7, 5, true⟩
                                                                      (.terminal .reducible)
                                                                      (.split false ⟨.fan1, 9, 5, true⟩
                                                                        (.terminal .reducible)
                                                                        (.split false ⟨.fan2, 1, 5, true⟩
                                                                          (.terminal .reducible)
                                                                          (.split false ⟨.fan2, 3, 5, true⟩
                                                                            (.terminal .reducible)
                                                                            (.split false ⟨.fan2, 5, 5, true⟩
                                                                              (.terminal .reducible)
                                                                              (.split false ⟨.fan2, 7, 5, true⟩
                                                                                (.terminal .reducible)
                                                                                (.split false ⟨.fan2, 9, 5, true⟩
                                                                                  (.terminal .reducible)
                                                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 2⟩, ⟨7, none, 4⟩, ⟨8, none, 2⟩, ⟨9, none, 4⟩]))))))))))))))))))))))))))))))))))
                  (.split true ⟨.spoke, 5, 5, false⟩
                    (.split false ⟨.spoke, 7, 5, false⟩
                      (.similar 0 ⟨false, 6⟩)
                      (.split false ⟨.spoke, 3, 7, false⟩
                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 5⟩, ⟨8, none, 4⟩, ⟨5, some 9, 9⟩]))
                        (.split false ⟨.spoke, 5, 7, false⟩
                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 3⟩, ⟨7, none, 5⟩, ⟨8, none, 4⟩, ⟨9, none, 5⟩, ⟨5, some 6, 5⟩]))
                          (.split false ⟨.spoke, 9, 7, false⟩
                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 3⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 5⟩, ⟨8, none, 4⟩, ⟨9, none, 1⟩]))
                            (.split false ⟨.hat, 2, 5, true⟩
                              (.terminal (.hubcap [⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨7, none, 5⟩, ⟨8, none, 4⟩, ⟨0, some 4, 6⟩, ⟨3, some 5, 8⟩, ⟨6, some 9, 8⟩]))
                              (.split false ⟨.spoke, 9, 6, true⟩
                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 5⟩, ⟨8, none, 4⟩, ⟨9, none, 5⟩]))
                                (.split true ⟨.spoke, 5, 6, false⟩
                                  (.split false ⟨.spoke, 3, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 5⟩, ⟨8, none, 4⟩, ⟨9, none, 4⟩]))
                                    (.split false ⟨.hat, 1, 5, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 5⟩, ⟨8, none, 4⟩, ⟨9, none, 4⟩]))
                                      (.split false ⟨.hat, 2, 6, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.hat, 0, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.hat, 3, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 5⟩, ⟨8, none, 4⟩, ⟨9, none, 4⟩]))
                                            (.split false ⟨.fan1, 3, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.hat, 4, 5, false⟩
                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 5⟩, ⟨8, none, 4⟩, ⟨9, none, 4⟩]))
                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 3⟩, ⟨7, none, 5⟩, ⟨5, some 6, 7⟩, ⟨8, some 9, 7⟩])))))))))
                                  (.split false ⟨.spoke, 3, 6, false⟩
                                    (.similar 0 ⟨true, 1⟩)
                                    (.split false ⟨.hat, 4, 5, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.hat, 5, 5, true⟩
                                        (.terminal .reducible)
                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 5⟩, ⟨8, none, 4⟩, ⟨9, none, 4⟩]))))))))))))
                    (.split false ⟨.spoke, 7, 5, false⟩
                      (.similar 0 ⟨false, 4⟩)
                      (.split false ⟨.spoke, 3, 6, true⟩
                        (.terminal .reducible)
                        (.split false ⟨.spoke, 9, 6, true⟩
                          (.terminal .reducible)
                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 5⟩, ⟨2, none, 4⟩, ⟨3, none, 2⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 5⟩, ⟨7, none, 5⟩, ⟨8, none, 4⟩, ⟨9, none, 2⟩])))))))
                (.split false ⟨.spoke, 5, 5, false⟩
                  (.similar 0 ⟨false, 6⟩)
                  (.split false ⟨.spoke, 1, 6, true⟩
                    (.terminal .reducible)
                    (.split false ⟨.spoke, 7, 6, true⟩
                      (.terminal .reducible)
                      (.similar 0 ⟨false, 8⟩))))))))))
    (.split false ⟨.spoke, 0, 5, false⟩
      (.similar 0 ⟨false, 1⟩)
      (.split false ⟨.spoke, 1, 5, false⟩
        (.similar 0 ⟨false, 2⟩)
        (.split false ⟨.spoke, 2, 5, false⟩
          (.similar 0 ⟨false, 3⟩)
          (.split false ⟨.spoke, 3, 5, false⟩
            (.similar 0 ⟨false, 4⟩)
            (.split false ⟨.spoke, 4, 5, false⟩
              (.similar 0 ⟨false, 5⟩)
              (.split false ⟨.spoke, 5, 5, false⟩
                (.similar 0 ⟨false, 6⟩)
                (.split false ⟨.spoke, 6, 5, false⟩
                  (.similar 0 ⟨false, 7⟩)
                  (.split false ⟨.spoke, 7, 5, false⟩
                    (.similar 0 ⟨false, 8⟩)
                    (.split false ⟨.spoke, 8, 5, false⟩
                      (.similar 0 ⟨false, 9⟩)
                      (.terminal .reducible)))))))))))

theorem structureCheck_eq_true :
    structureCheck arity code = true := by
  rfl

end ClassicalCertificatePresentationData10

end Mettapedia.GraphTheory.FourColor
