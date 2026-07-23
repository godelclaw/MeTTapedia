import Mettapedia.GraphTheory.FourColor.ClassicalCertificatePresentationCertificate

/-! Generated finite unavoidability presentation certificate. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificatePresentationData6

open ClassicalCertificatePresentationPattern
open ClassicalCertificatePresentationCertificate

def sourceSha256 : String := "5013d6d61c330a4918a6aaeca5b8cf3f826f8e31f8d18a5f33cb09d6ab7f27b0"
def arity : Nat := 6
def splitCount : Nat := 318
def leafCount : Nat := 319

def code : Code :=
  (.split true ⟨.spoke, 0, 6, false⟩
    (.split true ⟨.spoke, 2, 6, false⟩
      (.split false ⟨.spoke, 1, 5, false⟩
        (.split false ⟨.spoke, 4, 6, false⟩
          (.split false ⟨.spoke, 3, 5, false⟩
            (.split false ⟨.spoke, 5, 5, false⟩
              (.terminal (.hubcap [⟨0, some 1, 0⟩, ⟨2, some 4, 0⟩, ⟨3, some 5, 0⟩]))
              (.terminal (.hubcap [⟨0, some 1, -1⟩, ⟨2, some 4, -1⟩, ⟨3, some 5, 2⟩])))
            (.split false ⟨.spoke, 5, 5, false⟩
              (.terminal (.hubcap [⟨0, some 1, 0⟩, ⟨2, some 4, -2⟩, ⟨3, some 5, 2⟩]))
              (.terminal (.hubcap [⟨0, some 1, -1⟩, ⟨2, some 4, -3⟩, ⟨3, some 5, 4⟩]))))
          (.split true ⟨.spoke, 5, 6, false⟩
            (.split false ⟨.spoke, 3, 6, false⟩
              (.split false ⟨.spoke, 4, 5, false⟩
                (.terminal (.hubcap [⟨0, some 1, 0⟩, ⟨2, some 4, 0⟩, ⟨3, some 5, 0⟩]))
                (.terminal (.hubcap [⟨0, some 1, 0⟩, ⟨2, some 4, 2⟩, ⟨3, some 5, -2⟩])))
              (.split false ⟨.spoke, 3, 5, false⟩
                (.split false ⟨.spoke, 4, 5, false⟩
                  (.terminal (.hubcap [⟨0, some 1, 0⟩, ⟨2, some 4, 0⟩, ⟨3, some 5, 0⟩]))
                  (.terminal (.hubcap [⟨0, some 1, 0⟩, ⟨2, some 4, 1⟩, ⟨3, some 5, -1⟩])))
                (.split false ⟨.spoke, 4, 5, false⟩
                  (.terminal (.hubcap [⟨0, some 1, 0⟩, ⟨2, some 4, -1⟩, ⟨3, some 5, 1⟩]))
                  (.terminal (.hubcap [⟨0, some 1, 0⟩, ⟨2, some 4, 0⟩, ⟨3, some 5, 0⟩])))))
            (.split false ⟨.spoke, 3, 6, false⟩
              (.similar 0 ⟨true, 3⟩)
              (.split true ⟨.spoke, 5, 5, true⟩
                (.split false ⟨.spoke, 3, 5, true⟩
                  (.terminal .reducible)
                  (.split false ⟨.spoke, 4, 5, true⟩
                    (.terminal (.hubcap [⟨1, some 2, -1⟩, ⟨0, some 4, 0⟩, ⟨3, some 5, 1⟩]))
                    (.terminal (.hubcap [⟨1, some 2, 0⟩, ⟨0, some 4, -1⟩, ⟨3, some 5, 1⟩]))))
                (.split false ⟨.spoke, 3, 5, true⟩
                  (.similar 0 ⟨true, 3⟩)
                  (.split false ⟨.spoke, 4, 5, true⟩
                    (.split true ⟨.hat, 5, 6, false⟩
                      (.terminal (.hubcap [⟨0, some 1, -1⟩, ⟨2, some 4, 1⟩, ⟨3, some 5, 0⟩]))
                      (.split false ⟨.hat, 4, 6, false⟩
                        (.similar 0 ⟨true, 3⟩)
                        (.terminal (.hubcap [⟨1, some 2, -1⟩, ⟨0, some 4, 1⟩, ⟨3, some 5, 0⟩]))))
                    (.split false ⟨.hat, 5, 6, false⟩
                      (.terminal (.hubcap [⟨0, some 1, 0⟩, ⟨2, some 4, 0⟩, ⟨3, some 5, 0⟩]))
                      (.split false ⟨.hat, 5, 5, true⟩
                        (.split false ⟨.fan1, 5, 6, false⟩
                          (.terminal (.hubcap [⟨0, some 1, -1⟩, ⟨2, some 4, 1⟩, ⟨3, some 5, 0⟩]))
                          (.split false ⟨.fan1, 5, 5, true⟩
                            (.terminal (.hubcap [⟨0, some 1, -2⟩, ⟨2, some 4, 2⟩, ⟨3, some 5, 0⟩]))
                            (.terminal (.hubcap [⟨0, some 1, -1⟩, ⟨2, some 4, 1⟩, ⟨3, some 5, 0⟩]))))
                        (.split false ⟨.fan1, 5, 6, false⟩
                          (.terminal (.hubcap [⟨0, some 1, 0⟩, ⟨2, some 4, 0⟩, ⟨3, some 5, 0⟩]))
                          (.split false ⟨.fan1, 5, 5, true⟩
                            (.split false ⟨.hat, 0, 5, true⟩
                              (.terminal (.hubcap [⟨0, some 1, -2⟩, ⟨2, some 4, 2⟩, ⟨3, some 5, 0⟩]))
                              (.terminal (.hubcap [⟨0, some 1, -1⟩, ⟨2, some 4, 1⟩, ⟨3, some 5, 0⟩])))
                            (.split false ⟨.hat, 0, 5, true⟩
                              (.terminal (.hubcap [⟨0, some 1, -1⟩, ⟨2, some 4, 1⟩, ⟨3, some 5, 0⟩]))
                              (.terminal (.hubcap [⟨0, some 1, 0⟩, ⟨2, some 4, 0⟩, ⟨3, some 5, 0⟩])))))))))))))
        (.split false ⟨.spoke, 4, 6, false⟩
          (.split false ⟨.spoke, 3, 5, false⟩
            (.split false ⟨.spoke, 5, 5, false⟩
              (.terminal (.hubcap [⟨0, some 1, 1⟩, ⟨2, some 4, -1⟩, ⟨3, some 5, 0⟩]))
              (.terminal (.hubcap [⟨0, some 1, 0⟩, ⟨2, some 4, -2⟩, ⟨3, some 5, 2⟩])))
            (.split false ⟨.spoke, 5, 5, false⟩
              (.terminal (.hubcap [⟨0, some 1, 1⟩, ⟨2, some 4, -3⟩, ⟨3, some 5, 2⟩]))
              (.terminal (.hubcap [⟨0, some 1, 0⟩, ⟨2, some 4, -4⟩, ⟨3, some 5, 4⟩]))))
          (.split true ⟨.spoke, 5, 6, false⟩
            (.split false ⟨.spoke, 3, 6, false⟩
              (.split false ⟨.spoke, 4, 5, false⟩
                (.terminal (.hubcap [⟨0, some 1, 1⟩, ⟨2, some 4, -1⟩, ⟨3, some 5, 0⟩]))
                (.terminal (.hubcap [⟨0, some 1, 1⟩, ⟨2, some 4, 1⟩, ⟨3, some 5, -2⟩])))
              (.split false ⟨.spoke, 3, 5, false⟩
                (.split false ⟨.spoke, 4, 5, false⟩
                  (.terminal (.hubcap [⟨0, some 1, 1⟩, ⟨2, some 4, -1⟩, ⟨3, some 5, 0⟩]))
                  (.terminal (.hubcap [⟨0, some 1, 1⟩, ⟨2, some 4, 0⟩, ⟨3, some 5, -1⟩])))
                (.split false ⟨.spoke, 4, 5, false⟩
                  (.terminal (.hubcap [⟨0, some 1, 1⟩, ⟨2, some 4, -2⟩, ⟨3, some 5, 1⟩]))
                  (.terminal (.hubcap [⟨0, some 1, 1⟩, ⟨2, some 4, -1⟩, ⟨3, some 5, 0⟩])))))
            (.split false ⟨.spoke, 3, 6, false⟩
              (.similar 0 ⟨true, 3⟩)
              (.split true ⟨.spoke, 5, 5, true⟩
                (.split false ⟨.spoke, 3, 5, true⟩
                  (.terminal .reducible)
                  (.split false ⟨.spoke, 4, 5, true⟩
                    (.terminal (.hubcap [⟨1, some 2, 0⟩, ⟨0, some 4, -1⟩, ⟨3, some 5, 1⟩]))
                    (.terminal (.hubcap [⟨1, some 2, 1⟩, ⟨0, some 4, -2⟩, ⟨3, some 5, 1⟩]))))
                (.split false ⟨.spoke, 3, 5, true⟩
                  (.similar 0 ⟨true, 3⟩)
                  (.split false ⟨.spoke, 4, 5, true⟩
                    (.split true ⟨.hat, 5, 6, false⟩
                      (.terminal (.hubcap [⟨0, some 1, 0⟩, ⟨2, some 4, 0⟩, ⟨3, some 5, 0⟩]))
                      (.split false ⟨.hat, 4, 6, false⟩
                        (.similar 0 ⟨true, 3⟩)
                        (.terminal (.hubcap [⟨1, some 2, 0⟩, ⟨0, some 4, 0⟩, ⟨3, some 5, 0⟩]))))
                    (.split false ⟨.hat, 5, 6, false⟩
                      (.terminal (.hubcap [⟨0, some 1, 1⟩, ⟨2, some 4, -1⟩, ⟨3, some 5, 0⟩]))
                      (.split false ⟨.hat, 5, 5, true⟩
                        (.split false ⟨.fan1, 5, 6, false⟩
                          (.terminal (.hubcap [⟨0, some 1, 0⟩, ⟨2, some 4, 0⟩, ⟨3, some 5, 0⟩]))
                          (.split false ⟨.fan1, 5, 5, true⟩
                            (.terminal (.hubcap [⟨0, some 1, -1⟩, ⟨2, some 4, 1⟩, ⟨3, some 5, 0⟩]))
                            (.terminal (.hubcap [⟨0, some 1, 0⟩, ⟨2, some 4, 0⟩, ⟨3, some 5, 0⟩]))))
                        (.split false ⟨.fan1, 5, 6, false⟩
                          (.terminal (.hubcap [⟨0, some 1, 1⟩, ⟨2, some 4, -1⟩, ⟨3, some 5, 0⟩]))
                          (.split false ⟨.fan1, 5, 5, true⟩
                            (.split false ⟨.hat, 0, 5, true⟩
                              (.terminal (.hubcap [⟨0, some 1, -1⟩, ⟨2, some 4, 1⟩, ⟨3, some 5, 0⟩]))
                              (.terminal (.hubcap [⟨0, some 1, 0⟩, ⟨2, some 4, 0⟩, ⟨3, some 5, 0⟩])))
                            (.split false ⟨.hat, 0, 5, true⟩
                              (.terminal (.hubcap [⟨0, some 1, 0⟩, ⟨2, some 4, 0⟩, ⟨3, some 5, 0⟩]))
                              (.terminal (.hubcap [⟨0, some 1, 1⟩, ⟨2, some 4, -1⟩, ⟨3, some 5, 0⟩]))))))))))))))
      (.split false ⟨.spoke, 4, 6, false⟩
        (.similar 0 ⟨false, 4⟩)
        (.split false ⟨.spoke, 3, 6, false⟩
          (.split false ⟨.spoke, 1, 6, false⟩
            (.similar 0 ⟨false, 1⟩)
            (.split false ⟨.spoke, 5, 6, false⟩
              (.similar 0 ⟨false, 3⟩)
              (.split true ⟨.spoke, 1, 5, true⟩
                (.split false ⟨.spoke, 2, 5, true⟩
                  (.split true ⟨.spoke, 4, 5, true⟩
                    (.split false ⟨.spoke, 5, 5, true⟩
                      (.split false ⟨.hat, 5, 5, true⟩
                        (.terminal (.hubcap [⟨0, some 2, -3⟩, ⟨1, some 3, -3⟩, ⟨4, some 5, 6⟩]))
                        (.terminal (.hubcap [⟨0, some 2, -2⟩, ⟨1, some 3, -2⟩, ⟨4, some 5, 4⟩])))
                      (.split false ⟨.hat, 2, 5, true⟩
                        (.terminal (.hubcap [⟨0, some 4, -2⟩, ⟨3, some 5, -4⟩, ⟨1, some 2, 6⟩]))
                        (.terminal (.hubcap [⟨0, some 4, -1⟩, ⟨3, some 5, -3⟩, ⟨1, some 2, 4⟩]))))
                    (.split false ⟨.spoke, 5, 5, true⟩
                      (.similar 0 ⟨true, 2⟩)
                      (.split false ⟨.hat, 2, 5, true⟩
                        (.terminal (.hubcap [⟨0, some 4, -3⟩, ⟨3, some 5, -3⟩, ⟨1, some 2, 6⟩]))
                        (.terminal (.hubcap [⟨0, some 4, -2⟩, ⟨3, some 5, -2⟩, ⟨1, some 2, 4⟩])))))
                  (.split false ⟨.spoke, 4, 5, true⟩
                    (.split false ⟨.spoke, 5, 5, true⟩
                      (.split false ⟨.hat, 5, 5, true⟩
                        (.terminal (.hubcap [⟨0, some 2, -4⟩, ⟨1, some 3, -2⟩, ⟨4, some 5, 6⟩]))
                        (.terminal (.hubcap [⟨0, some 2, -3⟩, ⟨1, some 3, -1⟩, ⟨4, some 5, 4⟩])))
                      (.split false ⟨.hat, 5, 5, true⟩
                        (.split false ⟨.hat, 4, 5, false⟩
                          (.terminal (.hubcap [⟨0, some 2, -3⟩, ⟨1, some 3, -1⟩, ⟨4, some 5, 4⟩]))
                          (.terminal (.hubcap [⟨0, some 2, -3⟩, ⟨1, some 3, -2⟩, ⟨4, some 5, 5⟩])))
                        (.split false ⟨.hat, 5, 6, true⟩
                          (.split false ⟨.hat, 4, 5, false⟩
                            (.terminal (.hubcap [⟨0, some 2, -2⟩, ⟨1, some 3, 0⟩, ⟨4, some 5, 2⟩]))
                            (.terminal (.hubcap [⟨0, some 2, -2⟩, ⟨1, some 3, -1⟩, ⟨4, some 5, 3⟩])))
                          (.terminal (.hubcap [⟨0, some 2, -2⟩, ⟨1, some 3, 0⟩, ⟨4, some 5, 2⟩])))))
                    (.split false ⟨.spoke, 5, 5, true⟩
                      (.split false ⟨.hat, 5, 5, true⟩
                        (.split false ⟨.hat, 0, 5, false⟩
                          (.terminal (.hubcap [⟨0, some 2, -3⟩, ⟨1, some 3, -1⟩, ⟨4, some 5, 4⟩]))
                          (.terminal (.hubcap [⟨0, some 2, -4⟩, ⟨1, some 3, -1⟩, ⟨4, some 5, 5⟩])))
                        (.split false ⟨.hat, 0, 5, false⟩
                          (.terminal (.hubcap [⟨0, some 2, -2⟩, ⟨1, some 3, 0⟩, ⟨4, some 5, 2⟩]))
                          (.split false ⟨.hat, 5, 6, false⟩
                            (.terminal (.hubcap [⟨0, some 2, -2⟩, ⟨1, some 3, 0⟩, ⟨4, some 5, 2⟩]))
                            (.terminal (.hubcap [⟨0, some 2, -3⟩, ⟨1, some 3, 0⟩, ⟨4, some 5, 3⟩])))))
                      (.split false ⟨.hat, 2, 5, true⟩
                        (.split false ⟨.hat, 1, 5, true⟩
                          (.terminal (.hubcap [⟨0, some 4, -3⟩, ⟨3, some 5, -2⟩, ⟨1, some 2, 5⟩]))
                          (.terminal (.hubcap [⟨0, some 4, -2⟩, ⟨3, some 5, -2⟩, ⟨1, some 2, 4⟩])))
                        (.split false ⟨.hat, 2, 6, false⟩
                          (.terminal (.hubcap [⟨0, some 4, -1⟩, ⟨3, some 5, -1⟩, ⟨1, some 2, 2⟩]))
                          (.split false ⟨.hat, 1, 5, true⟩
                            (.terminal (.hubcap [⟨0, some 4, -2⟩, ⟨3, some 5, -1⟩, ⟨1, some 2, 3⟩]))
                            (.terminal (.hubcap [⟨0, some 4, -1⟩, ⟨3, some 5, -1⟩, ⟨1, some 2, 2⟩]))))))))
                (.split false ⟨.spoke, 2, 5, true⟩
                  (.similar 0 ⟨true, 2⟩)
                  (.split false ⟨.spoke, 4, 5, true⟩
                    (.similar 0 ⟨false, 3⟩)
                    (.split false ⟨.spoke, 5, 5, true⟩
                      (.similar 0 ⟨true, 5⟩)
                      (.split false ⟨.hat, 2, 6, false⟩
                        (.terminal (.hubcap [⟨0, some 4, 0⟩, ⟨3, some 5, 0⟩, ⟨1, some 2, 0⟩]))
                        (.split false ⟨.hat, 2, 5, true⟩
                          (.split true ⟨.fan1, 1, 5, true⟩
                            (.terminal (.hubcap [⟨0, some 4, -2⟩, ⟨3, some 5, -1⟩, ⟨1, some 2, 3⟩]))
                            (.split false ⟨.fan1, 2, 5, true⟩
                              (.similar 0 ⟨true, 2⟩)
                              (.terminal (.hubcap [⟨0, some 4, -1⟩, ⟨3, some 5, -1⟩, ⟨1, some 2, 2⟩]))))
                          (.split true ⟨.fan1, 1, 5, true⟩
                            (.split false ⟨.hat, 1, 5, true⟩
                              (.terminal (.hubcap [⟨0, some 4, -2⟩, ⟨3, some 5, 0⟩, ⟨1, some 2, 2⟩]))
                              (.terminal (.hubcap [⟨0, some 4, -1⟩, ⟨3, some 5, 0⟩, ⟨1, some 2, 1⟩])))
                            (.split false ⟨.fan1, 2, 5, true⟩
                              (.similar 0 ⟨true, 2⟩)
                              (.split true ⟨.fan1, 1, 6, false⟩
                                (.split false ⟨.fan1, 2, 6, false⟩
                                  (.terminal (.hubcap [⟨0, some 4, 0⟩, ⟨3, some 5, 0⟩, ⟨1, some 2, 0⟩]))
                                  (.split false ⟨.hat, 3, 5, false⟩
                                    (.terminal (.hubcap [⟨0, some 4, 0⟩, ⟨3, some 5, 0⟩, ⟨1, some 2, 0⟩]))
                                    (.terminal (.hubcap [⟨0, some 4, 0⟩, ⟨3, some 5, -1⟩, ⟨1, some 2, 1⟩]))))
                                (.split false ⟨.fan1, 2, 6, false⟩
                                  (.similar 0 ⟨true, 2⟩)
                                  (.split true ⟨.hat, 1, 5, true⟩
                                    (.terminal (.hubcap [⟨0, some 4, -1⟩, ⟨3, some 5, 0⟩, ⟨1, some 2, 1⟩]))
                                    (.split false ⟨.hat, 3, 5, true⟩
                                      (.similar 0 ⟨true, 2⟩)
                                      (.terminal (.hubcap [⟨0, some 4, 0⟩, ⟨3, some 5, 0⟩, ⟨1, some 2, 0⟩]))))))))))))))))
          (.split true ⟨.spoke, 1, 6, false⟩
            (.split false ⟨.spoke, 5, 6, false⟩
              (.similar 0 ⟨false, 5⟩)
              (.split true ⟨.spoke, 2, 5, true⟩
                (.split false ⟨.spoke, 4, 5, true⟩
                  (.terminal .reducible)
                  (.split false ⟨.spoke, 5, 5, true⟩
                    (.terminal .reducible)
                    (.split false ⟨.spoke, 3, 5, true⟩
                      (.terminal (.hubcap [⟨2, some 4, 1⟩, ⟨1, some 3, 0⟩, ⟨0, some 5, -1⟩]))
                      (.terminal (.hubcap [⟨2, some 4, 1⟩, ⟨1, some 3, -1⟩, ⟨0, some 5, 0⟩])))))
                (.split false ⟨.spoke, 5, 5, true⟩
                  (.similar 0 ⟨true, 4⟩)
                  (.split true ⟨.spoke, 3, 5, true⟩
                    (.split false ⟨.spoke, 4, 5, true⟩
                      (.terminal (.hubcap [⟨0, some 1, -2⟩, ⟨2, some 4, 1⟩, ⟨3, some 5, 1⟩]))
                      (.split false ⟨.hat, 3, 5, false⟩
                        (.terminal (.hubcap [⟨0, some 1, -1⟩, ⟨2, some 4, 0⟩, ⟨3, some 5, 1⟩]))
                        (.terminal (.hubcap [⟨3, some 1, 1⟩, ⟨2, some 4, 0⟩, ⟨0, some 5, -1⟩]))))
                    (.split false ⟨.spoke, 4, 5, true⟩
                      (.similar 0 ⟨true, 4⟩)
                      (.split true ⟨.hat, 3, 6, false⟩
                        (.split false ⟨.hat, 4, 6, false⟩
                          (.terminal (.hubcap [⟨0, some 4, 0⟩, ⟨1, some 2, 0⟩, ⟨3, some 5, 0⟩]))
                          (.split false ⟨.hat, 4, 5, true⟩
                            (.split false ⟨.fan1, 3, 5, false⟩
                              (.terminal (.hubcap [⟨0, some 4, 1⟩, ⟨1, some 2, -1⟩, ⟨3, some 5, 0⟩]))
                              (.terminal (.hubcap [⟨0, some 4, 2⟩, ⟨1, some 2, -2⟩, ⟨3, some 5, 0⟩])))
                            (.split false ⟨.fan1, 3, 5, true⟩
                              (.terminal (.hubcap [⟨0, some 4, 1⟩, ⟨1, some 2, -1⟩, ⟨3, some 5, 0⟩]))
                              (.terminal (.hubcap [⟨0, some 4, 0⟩, ⟨1, some 2, 0⟩, ⟨3, some 5, 0⟩])))))
                        (.split false ⟨.hat, 5, 6, false⟩
                          (.similar 0 ⟨true, 4⟩)
                          (.split false ⟨.hat, 4, 6, false⟩
                            (.split false ⟨.hat, 3, 5, true⟩
                              (.split false ⟨.fan1, 2, 5, true⟩
                                (.terminal (.hubcap [⟨0, some 4, -1⟩, ⟨3, some 5, 2⟩, ⟨1, some 2, -1⟩]))
                                (.split false ⟨.fan1, 3, 5, true⟩
                                  (.terminal (.hubcap [⟨0, some 4, -2⟩, ⟨3, some 5, 1⟩, ⟨1, some 2, 1⟩]))
                                  (.terminal (.hubcap [⟨0, some 4, -1⟩, ⟨3, some 5, 1⟩, ⟨1, some 2, 0⟩]))))
                              (.split false ⟨.fan1, 2, 5, true⟩
                                (.split false ⟨.hat, 2, 5, true⟩
                                  (.terminal (.hubcap [⟨0, some 4, 0⟩, ⟨3, some 5, 2⟩, ⟨1, some 2, -2⟩]))
                                  (.terminal (.hubcap [⟨0, some 4, 0⟩, ⟨3, some 5, 1⟩, ⟨1, some 2, -1⟩])))
                                (.split false ⟨.fan1, 3, 5, true⟩
                                  (.terminal (.hubcap [⟨0, some 4, -1⟩, ⟨3, some 5, 0⟩, ⟨1, some 2, 1⟩]))
                                  (.split false ⟨.fan1, 2, 6, false⟩
                                    (.terminal (.hubcap [⟨0, some 4, 0⟩, ⟨3, some 5, 0⟩, ⟨1, some 2, 0⟩]))
                                    (.split false ⟨.hat, 2, 5, true⟩
                                      (.terminal (.hubcap [⟨0, some 4, 0⟩, ⟨3, some 5, 1⟩, ⟨1, some 2, -1⟩]))
                                      (.terminal (.hubcap [⟨0, some 4, 0⟩, ⟨3, some 5, 0⟩, ⟨1, some 2, 0⟩])))))))
                            (.split true ⟨.hat, 5, 5, true⟩
                              (.split false ⟨.hat, 3, 5, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.fan1, 2, 5, true⟩
                                  (.split false ⟨.hat, 2, 5, true⟩
                                    (.terminal (.hubcap [⟨0, some 4, 0⟩, ⟨3, some 5, 2⟩, ⟨1, some 2, -2⟩]))
                                    (.terminal (.hubcap [⟨0, some 4, 0⟩, ⟨3, some 5, 1⟩, ⟨1, some 2, -1⟩])))
                                  (.split false ⟨.fan1, 2, 6, false⟩
                                    (.terminal (.hubcap [⟨0, some 4, 0⟩, ⟨3, some 5, 0⟩, ⟨1, some 2, 0⟩]))
                                    (.split false ⟨.hat, 2, 5, true⟩
                                      (.terminal (.hubcap [⟨0, some 4, 0⟩, ⟨3, some 5, 1⟩, ⟨1, some 2, -1⟩]))
                                      (.terminal (.hubcap [⟨0, some 4, 0⟩, ⟨3, some 5, 0⟩, ⟨1, some 2, 0⟩]))))))
                              (.split false ⟨.hat, 3, 5, true⟩
                                (.similar 0 ⟨true, 4⟩)
                                (.split true ⟨.fan1, 3, 6, false⟩
                                  (.split false ⟨.hat, 4, 5, false⟩
                                    (.split false ⟨.fan1, 2, 6, false⟩
                                      (.terminal (.hubcap [⟨0, some 4, 0⟩, ⟨3, some 5, 0⟩, ⟨1, some 2, 0⟩]))
                                      (.split false ⟨.fan1, 2, 5, false⟩
                                        (.split false ⟨.hat, 2, 5, false⟩
                                          (.terminal (.hubcap [⟨0, some 4, 0⟩, ⟨3, some 5, 0⟩, ⟨1, some 2, 0⟩]))
                                          (.terminal (.hubcap [⟨0, some 4, 0⟩, ⟨3, some 5, 1⟩, ⟨1, some 2, -1⟩])))
                                        (.split false ⟨.hat, 2, 5, false⟩
                                          (.terminal (.hubcap [⟨0, some 4, 0⟩, ⟨3, some 5, 1⟩, ⟨1, some 2, -1⟩]))
                                          (.terminal (.hubcap [⟨0, some 4, 0⟩, ⟨3, some 5, 2⟩, ⟨1, some 2, -2⟩])))))
                                    (.split false ⟨.fan1, 2, 6, false⟩
                                      (.terminal (.hubcap [⟨0, some 4, 1⟩, ⟨3, some 5, 0⟩, ⟨1, some 2, -1⟩]))
                                      (.split false ⟨.fan1, 2, 5, false⟩
                                        (.split false ⟨.hat, 2, 5, false⟩
                                          (.terminal (.hubcap [⟨0, some 4, 1⟩, ⟨3, some 5, 0⟩, ⟨1, some 2, -1⟩]))
                                          (.terminal (.hubcap [⟨0, some 4, 1⟩, ⟨3, some 5, 1⟩, ⟨1, some 2, -2⟩])))
                                        (.split false ⟨.hat, 2, 5, false⟩
                                          (.terminal (.hubcap [⟨0, some 4, 1⟩, ⟨3, some 5, 1⟩, ⟨1, some 2, -2⟩]))
                                          (.terminal (.hubcap [⟨0, some 4, 1⟩, ⟨3, some 5, 2⟩, ⟨1, some 2, -3⟩]))))))
                                  (.split false ⟨.fan1, 4, 6, false⟩
                                    (.similar 0 ⟨true, 4⟩)
                                    (.split false ⟨.fan1, 2, 6, false⟩
                                      (.terminal (.hubcap [⟨0, some 4, 0⟩, ⟨3, some 5, 0⟩, ⟨1, some 2, 0⟩]))
                                      (.split false ⟨.fan1, 2, 5, false⟩
                                        (.split false ⟨.hat, 2, 5, false⟩
                                          (.terminal (.hubcap [⟨0, some 4, 0⟩, ⟨3, some 5, 0⟩, ⟨1, some 2, 0⟩]))
                                          (.terminal (.hubcap [⟨0, some 4, 0⟩, ⟨3, some 5, 1⟩, ⟨1, some 2, -1⟩])))
                                        (.split false ⟨.hat, 2, 5, false⟩
                                          (.terminal (.hubcap [⟨0, some 4, 0⟩, ⟨3, some 5, 1⟩, ⟨1, some 2, -1⟩]))
                                          (.terminal (.hubcap [⟨0, some 4, 0⟩, ⟨3, some 5, 2⟩, ⟨1, some 2, -2⟩])))))))))))))))))
            (.split false ⟨.spoke, 5, 6, false⟩
              (.similar 0 ⟨true, 5⟩)
              (.split true ⟨.spoke, 1, 5, true⟩
                (.split false ⟨.spoke, 3, 5, true⟩
                  (.terminal .reducible)
                  (.split false ⟨.spoke, 4, 5, true⟩
                    (.terminal .reducible)
                    (.split false ⟨.spoke, 5, 5, true⟩
                      (.terminal .reducible)
                      (.split false ⟨.hat, 5, 5, true⟩
                        (.terminal .reducible)
                        (.split false ⟨.spoke, 2, 5, true⟩
                          (.terminal (.hubcap [⟨0, some 2, 0⟩, ⟨1, some 3, 1⟩, ⟨4, some 5, -1⟩]))
                          (.split false ⟨.hat, 5, 6, false⟩
                            (.terminal (.hubcap [⟨0, some 2, -1⟩, ⟨1, some 3, 1⟩, ⟨4, some 5, 0⟩]))
                            (.split false ⟨.fan1, 4, 5, true⟩
                              (.terminal (.hubcap [⟨0, some 2, -1⟩, ⟨1, some 3, 0⟩, ⟨4, some 5, 1⟩]))
                              (.split false ⟨.fan1, 5, 6, false⟩
                                (.terminal (.hubcap [⟨0, some 2, -1⟩, ⟨1, some 3, 1⟩, ⟨4, some 5, 0⟩]))
                                (.split false ⟨.fan1, 5, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.hat, 0, 5, false⟩
                                    (.terminal (.hubcap [⟨0, some 2, -1⟩, ⟨1, some 3, 1⟩, ⟨4, some 5, 0⟩]))
                                    (.terminal (.hubcap [⟨0, some 2, -2⟩, ⟨1, some 3, 1⟩, ⟨4, some 5, 1⟩]))))))))))))
                (.split false ⟨.spoke, 5, 5, true⟩
                  (.similar 0 ⟨true, 5⟩)
                  (.split true ⟨.spoke, 2, 5, true⟩
                    (.split false ⟨.spoke, 4, 5, true⟩
                      (.terminal .reducible)
                      (.split false ⟨.spoke, 3, 5, true⟩
                        (.terminal (.hubcap [⟨0, some 5, -2⟩, ⟨1, some 3, 1⟩, ⟨2, some 4, 1⟩]))
                        (.split false ⟨.hat, 2, 6, false⟩
                          (.terminal (.hubcap [⟨0, some 5, -1⟩, ⟨1, some 3, 0⟩, ⟨2, some 4, 1⟩]))
                          (.terminal (.hubcap [⟨0, some 2, 1⟩, ⟨1, some 3, 0⟩, ⟨4, some 5, -1⟩])))))
                    (.split false ⟨.spoke, 4, 5, true⟩
                      (.similar 0 ⟨true, 5⟩)
                      (.split false ⟨.spoke, 3, 5, true⟩
                        (.split false ⟨.hat, 3, 6, false⟩
                          (.terminal (.hubcap [⟨0, some 1, -1⟩, ⟨2, some 4, 0⟩, ⟨3, some 5, 1⟩]))
                          (.terminal (.hubcap [⟨0, some 5, -1⟩, ⟨1, some 3, 1⟩, ⟨2, some 4, 0⟩])))
                        (.split true ⟨.hat, 2, 5, true⟩
                          (.split false ⟨.hat, 5, 5, true⟩
                            (.terminal (.hubcap [⟨0, some 2, -1⟩, ⟨1, some 3, -1⟩, ⟨4, some 5, 2⟩]))
                            (.split false ⟨.hat, 5, 6, false⟩
                              (.split false ⟨.hat, 4, 5, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.hat, 4, 6, false⟩
                                  (.terminal (.hubcap [⟨0, some 2, 0⟩, ⟨1, some 3, 0⟩, ⟨4, some 5, 0⟩]))
                                  (.split false ⟨.fan1, 4, 5, true⟩
                                    (.terminal (.hubcap [⟨0, some 2, 0⟩, ⟨1, some 3, 1⟩, ⟨4, some 5, -1⟩]))
                                    (.terminal (.hubcap [⟨0, some 2, 0⟩, ⟨1, some 3, 0⟩, ⟨4, some 5, 0⟩])))))
                              (.split false ⟨.fan1, 5, 5, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.fan1, 5, 6, false⟩
                                  (.terminal (.hubcap [⟨0, some 2, 0⟩, ⟨1, some 3, 0⟩, ⟨4, some 5, 0⟩]))
                                  (.split false ⟨.hat, 0, 5, false⟩
                                    (.terminal (.hubcap [⟨0, some 2, 0⟩, ⟨1, some 3, 0⟩, ⟨4, some 5, 0⟩]))
                                    (.terminal (.hubcap [⟨0, some 2, -1⟩, ⟨1, some 3, 0⟩, ⟨4, some 5, 1⟩])))))))
                          (.split false ⟨.hat, 5, 5, true⟩
                            (.similar 0 ⟨true, 5⟩)
                            (.split true ⟨.hat, 3, 5, true⟩
                              (.split false ⟨.fan1, 2, 5, true⟩
                                (.split false ⟨.fan1, 3, 5, true⟩
                                  (.terminal (.hubcap [⟨0, some 4, -2⟩, ⟨1, some 2, 0⟩, ⟨3, some 5, 2⟩]))
                                  (.terminal (.hubcap [⟨0, some 4, -1⟩, ⟨1, some 2, -1⟩, ⟨3, some 5, 2⟩])))
                                (.split false ⟨.fan1, 3, 5, true⟩
                                  (.split false ⟨.hat, 2, 6, false⟩
                                    (.terminal (.hubcap [⟨0, some 4, -2⟩, ⟨1, some 2, 1⟩, ⟨3, some 5, 1⟩]))
                                    (.split false ⟨.fan1, 1, 5, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.fan1, 1, 6, false⟩
                                        (.terminal (.hubcap [⟨0, some 4, -2⟩, ⟨1, some 2, 1⟩, ⟨3, some 5, 1⟩]))
                                        (.split false ⟨.hat, 1, 5, false⟩
                                          (.terminal (.hubcap [⟨0, some 4, -2⟩, ⟨1, some 2, 1⟩, ⟨3, some 5, 1⟩]))
                                          (.terminal (.hubcap [⟨0, some 4, -3⟩, ⟨1, some 2, 2⟩, ⟨3, some 5, 1⟩]))))))
                                  (.split false ⟨.hat, 2, 6, false⟩
                                    (.terminal (.hubcap [⟨0, some 4, -1⟩, ⟨1, some 2, 0⟩, ⟨3, some 5, 1⟩]))
                                    (.split false ⟨.fan1, 1, 5, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.fan1, 1, 6, false⟩
                                        (.terminal (.hubcap [⟨0, some 4, -1⟩, ⟨1, some 2, 0⟩, ⟨3, some 5, 1⟩]))
                                        (.split false ⟨.hat, 1, 5, false⟩
                                          (.terminal (.hubcap [⟨0, some 4, -1⟩, ⟨1, some 2, 0⟩, ⟨3, some 5, 1⟩]))
                                          (.terminal (.hubcap [⟨0, some 4, -2⟩, ⟨1, some 2, 1⟩, ⟨3, some 5, 1⟩]))))))))
                              (.split false ⟨.hat, 4, 5, true⟩
                                (.similar 0 ⟨true, 5⟩)
                                (.split true ⟨.hat, 3, 6, false⟩
                                  (.split false ⟨.hat, 4, 6, false⟩
                                    (.split true ⟨.hat, 2, 6, false⟩
                                      (.terminal (.hubcap [⟨0, some 4, 0⟩, ⟨1, some 2, 0⟩, ⟨3, some 5, 0⟩]))
                                      (.split false ⟨.hat, 5, 6, false⟩
                                        (.similar 0 ⟨true, 5⟩)
                                        (.split false ⟨.fan1, 4, 5, true⟩
                                          (.terminal (.hubcap [⟨0, some 2, 0⟩, ⟨1, some 3, -1⟩, ⟨4, some 5, 1⟩]))
                                          (.split false ⟨.fan1, 5, 6, false⟩
                                            (.terminal (.hubcap [⟨0, some 2, 0⟩, ⟨1, some 3, 0⟩, ⟨4, some 5, 0⟩]))
                                            (.split false ⟨.fan1, 5, 5, true⟩
                                              (.split false ⟨.hat, 0, 5, true⟩
                                                (.terminal (.hubcap [⟨0, some 2, -2⟩, ⟨1, some 3, 0⟩, ⟨4, some 5, 2⟩]))
                                                (.terminal (.hubcap [⟨0, some 2, -1⟩, ⟨1, some 3, 0⟩, ⟨4, some 5, 1⟩])))
                                              (.split false ⟨.hat, 0, 5, true⟩
                                                (.terminal (.hubcap [⟨0, some 2, -1⟩, ⟨1, some 3, 0⟩, ⟨4, some 5, 1⟩]))
                                                (.terminal (.hubcap [⟨0, some 2, 0⟩, ⟨1, some 3, 0⟩, ⟨4, some 5, 0⟩]))))))))
                                    (.split false ⟨.hat, 5, 6, false⟩
                                      (.split false ⟨.fan1, 3, 5, false⟩
                                        (.split false ⟨.fan1, 4, 5, false⟩
                                          (.terminal (.hubcap [⟨0, some 2, 0⟩, ⟨1, some 3, 0⟩, ⟨4, some 5, 0⟩]))
                                          (.terminal (.hubcap [⟨0, some 2, 0⟩, ⟨1, some 3, 1⟩, ⟨4, some 5, -1⟩])))
                                        (.split false ⟨.fan1, 4, 5, false⟩
                                          (.terminal (.hubcap [⟨0, some 2, -1⟩, ⟨1, some 3, 0⟩, ⟨4, some 5, 1⟩]))
                                          (.terminal (.hubcap [⟨0, some 2, -1⟩, ⟨1, some 3, 1⟩, ⟨4, some 5, 0⟩]))))
                                      (.split false ⟨.fan1, 3, 5, true⟩
                                        (.split false ⟨.fan1, 5, 5, true⟩
                                          (.terminal (.hubcap [⟨0, some 2, -2⟩, ⟨1, some 3, 0⟩, ⟨4, some 5, 2⟩]))
                                          (.terminal (.hubcap [⟨0, some 2, -1⟩, ⟨1, some 3, 0⟩, ⟨4, some 5, 1⟩])))
                                        (.split false ⟨.fan1, 5, 6, false⟩
                                          (.terminal (.hubcap [⟨0, some 2, 0⟩, ⟨1, some 3, 0⟩, ⟨4, some 5, 0⟩]))
                                          (.split false ⟨.fan1, 5, 5, true⟩
                                            (.split false ⟨.hat, 0, 5, true⟩
                                              (.terminal (.hubcap [⟨0, some 2, -2⟩, ⟨1, some 3, 0⟩, ⟨4, some 5, 2⟩]))
                                              (.terminal (.hubcap [⟨0, some 2, -1⟩, ⟨1, some 3, 0⟩, ⟨4, some 5, 1⟩])))
                                            (.split false ⟨.hat, 0, 5, true⟩
                                              (.terminal (.hubcap [⟨0, some 2, -1⟩, ⟨1, some 3, 0⟩, ⟨4, some 5, 1⟩]))
                                              (.terminal (.hubcap [⟨0, some 2, 0⟩, ⟨1, some 3, 0⟩, ⟨4, some 5, 0⟩]))))))))
                                  (.split false ⟨.hat, 4, 6, false⟩
                                    (.similar 0 ⟨true, 5⟩)
                                    (.split true ⟨.hat, 5, 6, false⟩
                                      (.split false ⟨.fan1, 4, 5, false⟩
                                        (.terminal (.hubcap [⟨0, some 2, 0⟩, ⟨1, some 3, 0⟩, ⟨4, some 5, 0⟩]))
                                        (.terminal (.hubcap [⟨0, some 2, 0⟩, ⟨1, some 3, 1⟩, ⟨4, some 5, -1⟩])))
                                      (.split false ⟨.hat, 2, 6, false⟩
                                        (.similar 0 ⟨true, 5⟩)
                                        (.split false ⟨.fan1, 5, 6, false⟩
                                          (.terminal (.hubcap [⟨0, some 2, 0⟩, ⟨1, some 3, 0⟩, ⟨4, some 5, 0⟩]))
                                          (.split false ⟨.fan1, 5, 5, true⟩
                                            (.split false ⟨.hat, 0, 5, true⟩
                                              (.terminal (.hubcap [⟨0, some 2, -2⟩, ⟨1, some 3, 0⟩, ⟨4, some 5, 2⟩]))
                                              (.terminal (.hubcap [⟨0, some 2, -1⟩, ⟨1, some 3, 0⟩, ⟨4, some 5, 1⟩])))
                                            (.split false ⟨.hat, 0, 5, true⟩
                                              (.terminal (.hubcap [⟨0, some 2, -1⟩, ⟨1, some 3, 0⟩, ⟨4, some 5, 1⟩]))
                                              (.terminal (.hubcap [⟨0, some 2, 0⟩, ⟨1, some 3, 0⟩, ⟨4, some 5, 0⟩])))))))))))))))))))))))
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
              (.split false ⟨.spoke, 0, 5, true⟩
                (.terminal .reducible)
                (.split false ⟨.spoke, 1, 5, true⟩
                  (.terminal .reducible)
                  (.split false ⟨.spoke, 2, 5, true⟩
                    (.terminal .reducible)
                    (.split false ⟨.spoke, 3, 5, true⟩
                      (.terminal .reducible)
                      (.split false ⟨.spoke, 4, 5, true⟩
                        (.terminal .reducible)
                        (.split false ⟨.spoke, 5, 5, true⟩
                          (.terminal .reducible)
                          (.split true ⟨.hat, 0, 6, false⟩
                            (.split true ⟨.hat, 2, 6, false⟩
                              (.split false ⟨.hat, 4, 6, false⟩
                                (.split true ⟨.hat, 1, 6, false⟩
                                  (.split false ⟨.hat, 5, 6, false⟩
                                    (.terminal (.hubcap [⟨0, some 5, 0⟩, ⟨1, some 3, 0⟩, ⟨2, some 4, 0⟩]))
                                    (.split false ⟨.hat, 5, 5, true⟩
                                      (.split false ⟨.fan1, 4, 5, true⟩
                                        (.terminal (.hubcap [⟨0, some 5, 1⟩, ⟨1, some 3, -2⟩, ⟨2, some 4, 1⟩]))
                                        (.split false ⟨.fan1, 5, 5, true⟩
                                          (.terminal (.hubcap [⟨0, some 5, -1⟩, ⟨1, some 3, -1⟩, ⟨2, some 4, 2⟩]))
                                          (.terminal (.hubcap [⟨0, some 5, 0⟩, ⟨1, some 3, -1⟩, ⟨2, some 4, 1⟩]))))
                                      (.split false ⟨.fan1, 4, 5, true⟩
                                        (.terminal (.hubcap [⟨0, some 5, 1⟩, ⟨1, some 3, -1⟩, ⟨2, some 4, 0⟩]))
                                        (.split false ⟨.fan1, 5, 5, true⟩
                                          (.terminal (.hubcap [⟨0, some 5, -1⟩, ⟨1, some 3, 0⟩, ⟨2, some 4, 1⟩]))
                                          (.terminal (.hubcap [⟨0, some 5, 0⟩, ⟨1, some 3, 0⟩, ⟨2, some 4, 0⟩]))))))
                                  (.split false ⟨.hat, 5, 6, false⟩
                                    (.similar 0 ⟨true, 0⟩)
                                    (.split true ⟨.hat, 1, 5, true⟩
                                      (.split false ⟨.fan1, 0, 5, true⟩
                                        (.split false ⟨.fan1, 4, 5, true⟩
                                          (.terminal (.hubcap [⟨0, some 5, 0⟩, ⟨1, some 3, 1⟩, ⟨2, some 4, -1⟩]))
                                          (.split false ⟨.fan1, 5, 5, true⟩
                                            (.terminal (.hubcap [⟨0, some 5, -2⟩, ⟨1, some 3, 2⟩, ⟨2, some 4, 0⟩]))
                                            (.terminal (.hubcap [⟨0, some 5, -1⟩, ⟨1, some 3, 2⟩, ⟨2, some 4, -1⟩]))))
                                        (.split false ⟨.fan1, 1, 5, true⟩
                                          (.split false ⟨.fan1, 4, 5, true⟩
                                            (.terminal (.hubcap [⟨0, some 5, 2⟩, ⟨1, some 3, 0⟩, ⟨2, some 4, -2⟩]))
                                            (.split false ⟨.fan1, 5, 5, true⟩
                                              (.terminal (.hubcap [⟨0, some 5, 0⟩, ⟨1, some 3, 1⟩, ⟨2, some 4, -1⟩]))
                                              (.terminal (.hubcap [⟨0, some 5, 1⟩, ⟨1, some 3, 1⟩, ⟨2, some 4, -2⟩]))))
                                          (.split false ⟨.fan1, 4, 5, true⟩
                                            (.terminal (.hubcap [⟨0, some 5, 1⟩, ⟨1, some 3, 0⟩, ⟨2, some 4, -1⟩]))
                                            (.split false ⟨.fan1, 5, 5, true⟩
                                              (.terminal (.hubcap [⟨0, some 5, -1⟩, ⟨1, some 3, 1⟩, ⟨2, some 4, 0⟩]))
                                              (.terminal (.hubcap [⟨0, some 5, 0⟩, ⟨1, some 3, 1⟩, ⟨2, some 4, -1⟩]))))))
                                      (.split false ⟨.hat, 5, 5, true⟩
                                        (.similar 0 ⟨true, 0⟩)
                                        (.split true ⟨.fan1, 0, 5, true⟩
                                          (.split false ⟨.fan1, 4, 5, true⟩
                                            (.terminal (.hubcap [⟨0, some 5, 0⟩, ⟨1, some 3, 0⟩, ⟨2, some 4, 0⟩]))
                                            (.split false ⟨.fan1, 5, 5, true⟩
                                              (.terminal (.hubcap [⟨0, some 5, -2⟩, ⟨1, some 3, 1⟩, ⟨2, some 4, 1⟩]))
                                              (.terminal (.hubcap [⟨0, some 5, -1⟩, ⟨1, some 3, 1⟩, ⟨2, some 4, 0⟩]))))
                                          (.split false ⟨.fan1, 5, 5, true⟩
                                            (.similar 0 ⟨true, 0⟩)
                                            (.split true ⟨.fan1, 1, 5, true⟩
                                              (.split false ⟨.fan1, 4, 5, true⟩
                                                (.terminal (.hubcap [⟨0, some 5, 2⟩, ⟨1, some 3, -1⟩, ⟨2, some 4, -1⟩]))
                                                (.terminal (.hubcap [⟨0, some 5, 1⟩, ⟨1, some 3, 0⟩, ⟨2, some 4, -1⟩])))
                                              (.split false ⟨.fan1, 4, 5, true⟩
                                                (.similar 0 ⟨true, 0⟩)
                                                (.terminal (.hubcap [⟨0, some 5, 0⟩, ⟨1, some 3, 0⟩, ⟨2, some 4, 0⟩]))))))))))
                                (.split true ⟨.hat, 3, 6, false⟩
                                  (.split false ⟨.hat, 5, 6, false⟩
                                    (.split false ⟨.hat, 4, 5, true⟩
                                      (.split false ⟨.fan1, 4, 5, true⟩
                                        (.terminal (.hubcap [⟨0, some 2, -1⟩, ⟨1, some 5, -2⟩, ⟨3, some 4, 3⟩]))
                                        (.split false ⟨.fan1, 3, 5, true⟩
                                          (.terminal (.hubcap [⟨0, some 2, -2⟩, ⟨1, some 5, -1⟩, ⟨3, some 4, 3⟩]))
                                          (.terminal (.hubcap [⟨0, some 2, -1⟩, ⟨1, some 5, -1⟩, ⟨3, some 4, 2⟩]))))
                                      (.split false ⟨.fan1, 4, 5, true⟩
                                        (.terminal (.hubcap [⟨0, some 2, 0⟩, ⟨1, some 5, -1⟩, ⟨3, some 4, 1⟩]))
                                        (.split false ⟨.fan1, 3, 5, true⟩
                                          (.terminal (.hubcap [⟨0, some 2, -1⟩, ⟨1, some 5, 0⟩, ⟨3, some 4, 1⟩]))
                                          (.terminal (.hubcap [⟨0, some 2, 0⟩, ⟨1, some 5, 0⟩, ⟨3, some 4, 0⟩])))))
                                    (.split false ⟨.hat, 4, 5, true⟩
                                      (.split false ⟨.fan1, 3, 5, true⟩
                                        (.split false ⟨.fan1, 5, 5, true⟩
                                          (.terminal (.hubcap [⟨0, some 2, -3⟩, ⟨1, some 5, -1⟩, ⟨3, some 4, 4⟩]))
                                          (.terminal (.hubcap [⟨0, some 2, -2⟩, ⟨1, some 5, -1⟩, ⟨3, some 4, 3⟩])))
                                        (.split false ⟨.fan1, 5, 5, true⟩
                                          (.terminal (.hubcap [⟨0, some 2, -2⟩, ⟨1, some 5, -1⟩, ⟨3, some 4, 3⟩]))
                                          (.terminal (.hubcap [⟨0, some 2, -1⟩, ⟨1, some 5, -1⟩, ⟨3, some 4, 2⟩]))))
                                      (.split false ⟨.hat, 5, 5, true⟩
                                        (.split false ⟨.fan1, 3, 5, true⟩
                                          (.split false ⟨.fan1, 5, 5, true⟩
                                            (.terminal (.hubcap [⟨0, some 2, -3⟩, ⟨1, some 5, 1⟩, ⟨3, some 4, 2⟩]))
                                            (.terminal (.hubcap [⟨0, some 2, -2⟩, ⟨1, some 5, 1⟩, ⟨3, some 4, 1⟩])))
                                          (.split false ⟨.fan1, 5, 5, true⟩
                                            (.terminal (.hubcap [⟨0, some 2, -2⟩, ⟨1, some 5, 1⟩, ⟨3, some 4, 1⟩]))
                                            (.terminal (.hubcap [⟨0, some 2, -1⟩, ⟨1, some 5, 1⟩, ⟨3, some 4, 0⟩]))))
                                        (.split false ⟨.fan1, 3, 5, true⟩
                                          (.split false ⟨.fan1, 5, 5, true⟩
                                            (.terminal (.hubcap [⟨0, some 2, -2⟩, ⟨1, some 5, 0⟩, ⟨3, some 4, 2⟩]))
                                            (.terminal (.hubcap [⟨0, some 2, -1⟩, ⟨1, some 5, 0⟩, ⟨3, some 4, 1⟩])))
                                          (.split false ⟨.fan1, 5, 5, true⟩
                                            (.terminal (.hubcap [⟨0, some 2, -1⟩, ⟨1, some 5, 0⟩, ⟨3, some 4, 1⟩]))
                                            (.terminal (.hubcap [⟨0, some 2, 0⟩, ⟨1, some 5, 0⟩, ⟨3, some 4, 0⟩])))))))
                                  (.split false ⟨.hat, 5, 6, false⟩
                                    (.similar 0 ⟨true, 4⟩)
                                    (.split true ⟨.hat, 3, 5, true⟩
                                      (.split false ⟨.fan1, 2, 5, true⟩
                                        (.split false ⟨.fan1, 5, 5, true⟩
                                          (.terminal (.hubcap [⟨0, some 2, 0⟩, ⟨1, some 5, -2⟩, ⟨3, some 4, 2⟩]))
                                          (.terminal (.hubcap [⟨0, some 2, 1⟩, ⟨1, some 5, -2⟩, ⟨3, some 4, 1⟩])))
                                        (.split false ⟨.fan1, 5, 5, true⟩
                                          (.terminal (.hubcap [⟨0, some 2, 0⟩, ⟨1, some 5, -1⟩, ⟨3, some 4, 1⟩]))
                                          (.terminal (.hubcap [⟨0, some 2, 1⟩, ⟨1, some 5, -1⟩, ⟨3, some 4, 0⟩]))))
                                      (.split false ⟨.hat, 5, 5, true⟩
                                        (.similar 0 ⟨true, 4⟩)
                                        (.split true ⟨.fan1, 2, 5, true⟩
                                          (.split false ⟨.fan1, 5, 5, true⟩
                                            (.terminal (.hubcap [⟨0, some 2, -1⟩, ⟨1, some 5, -1⟩, ⟨3, some 4, 2⟩]))
                                            (.split false ⟨.hat, 4, 5, true⟩
                                              (.terminal (.hubcap [⟨0, some 2, -1⟩, ⟨1, some 5, -2⟩, ⟨3, some 4, 3⟩]))
                                              (.terminal (.hubcap [⟨0, some 2, 0⟩, ⟨1, some 5, -1⟩, ⟨3, some 4, 1⟩]))))
                                          (.split false ⟨.fan1, 5, 5, true⟩
                                            (.similar 0 ⟨true, 4⟩)
                                            (.split false ⟨.hat, 4, 5, true⟩
                                              (.terminal (.hubcap [⟨0, some 2, -1⟩, ⟨1, some 5, -1⟩, ⟨3, some 4, 2⟩]))
                                              (.terminal (.hubcap [⟨0, some 2, 0⟩, ⟨1, some 5, 0⟩, ⟨3, some 4, 0⟩]))))))))))
                              (.split false ⟨.hat, 4, 6, false⟩
                                (.similar 0 ⟨false, 4⟩)
                                (.split true ⟨.hat, 1, 6, false⟩
                                  (.split false ⟨.hat, 3, 6, false⟩
                                    (.similar 0 ⟨false, 1⟩)
                                    (.split false ⟨.hat, 5, 6, false⟩
                                      (.similar 0 ⟨false, 5⟩)
                                      (.split true ⟨.hat, 2, 5, true⟩
                                        (.split false ⟨.fan1, 1, 5, true⟩
                                          (.terminal (.hubcap [⟨0, some 4, -2⟩, ⟨1, some 2, 3⟩, ⟨3, some 5, -1⟩]))
                                          (.terminal (.hubcap [⟨0, some 4, -1⟩, ⟨1, some 2, 2⟩, ⟨3, some 5, -1⟩])))
                                        (.split false ⟨.hat, 5, 5, true⟩
                                          (.similar 0 ⟨true, 5⟩)
                                          (.split true ⟨.fan1, 1, 5, true⟩
                                            (.split false ⟨.fan1, 5, 5, true⟩
                                              (.terminal (.hubcap [⟨0, some 5, -2⟩, ⟨1, some 3, 0⟩, ⟨2, some 4, 2⟩]))
                                              (.split false ⟨.hat, 4, 5, true⟩
                                                (.terminal (.hubcap [⟨0, some 5, -2⟩, ⟨1, some 3, 1⟩, ⟨2, some 4, 1⟩]))
                                                (.terminal (.hubcap [⟨0, some 5, -1⟩, ⟨1, some 3, 0⟩, ⟨2, some 4, 1⟩]))))
                                            (.split false ⟨.fan1, 5, 5, true⟩
                                              (.similar 0 ⟨true, 5⟩)
                                              (.split false ⟨.hat, 4, 5, true⟩
                                                (.terminal (.hubcap [⟨0, some 5, -1⟩, ⟨1, some 3, 1⟩, ⟨2, some 4, 0⟩]))
                                                (.terminal (.hubcap [⟨0, some 5, 0⟩, ⟨1, some 3, 0⟩, ⟨2, some 4, 0⟩])))))))))
                                  (.split false ⟨.hat, 5, 6, false⟩
                                    (.similar 0 ⟨true, 0⟩)
                                    (.split true ⟨.hat, 1, 5, true⟩
                                      (.split false ⟨.hat, 4, 5, true⟩
                                        (.terminal (.hubcap [⟨0, some 5, -1⟩, ⟨1, some 3, 2⟩, ⟨2, some 4, -1⟩]))
                                        (.split false ⟨.fan1, 0, 5, true⟩
                                          (.terminal (.hubcap [⟨0, some 5, -1⟩, ⟨1, some 3, 2⟩, ⟨2, some 4, -1⟩]))
                                          (.terminal (.hubcap [⟨0, some 5, 0⟩, ⟨1, some 3, 1⟩, ⟨2, some 4, -1⟩]))))
                                      (.split false ⟨.hat, 5, 5, true⟩
                                        (.similar 0 ⟨true, 0⟩)
                                        (.split true ⟨.hat, 2, 5, true⟩
                                          (.terminal (.hubcap [⟨0, some 5, -1⟩, ⟨1, some 3, 0⟩, ⟨2, some 4, 1⟩]))
                                          (.split false ⟨.hat, 4, 5, true⟩
                                            (.similar 0 ⟨true, 0⟩)
                                            (.split true ⟨.fan1, 0, 5, true⟩
                                              (.split false ⟨.fan1, 5, 5, true⟩
                                                (.terminal (.hubcap [⟨0, some 5, -2⟩, ⟨1, some 3, 1⟩, ⟨2, some 4, 1⟩]))
                                                (.terminal (.hubcap [⟨0, some 5, -1⟩, ⟨1, some 3, 1⟩, ⟨2, some 4, 0⟩])))
                                              (.split false ⟨.fan1, 5, 5, true⟩
                                                (.similar 0 ⟨true, 0⟩)
                                                (.terminal (.hubcap [⟨0, some 5, 0⟩, ⟨1, some 3, 0⟩, ⟨2, some 4, 0⟩]))))))))))))
                            (.split false ⟨.hat, 1, 6, false⟩
                              (.similar 0 ⟨false, 1⟩)
                              (.split false ⟨.hat, 2, 6, false⟩
                                (.similar 0 ⟨false, 2⟩)
                                (.split false ⟨.hat, 3, 6, false⟩
                                  (.similar 0 ⟨false, 3⟩)
                                  (.split false ⟨.hat, 4, 6, false⟩
                                    (.similar 0 ⟨false, 4⟩)
                                    (.split false ⟨.hat, 5, 6, false⟩
                                      (.similar 0 ⟨false, 5⟩)
                                      (.split true ⟨.hat, 0, 5, true⟩
                                        (.terminal (.hubcap [⟨0, some 5, 2⟩, ⟨1, some 3, -1⟩, ⟨2, some 4, -1⟩]))
                                        (.split false ⟨.hat, 1, 5, true⟩
                                          (.similar 0 ⟨false, 1⟩)
                                          (.split false ⟨.hat, 2, 5, true⟩
                                            (.similar 0 ⟨false, 2⟩)
                                            (.split false ⟨.hat, 3, 5, true⟩
                                              (.similar 0 ⟨false, 3⟩)
                                              (.split false ⟨.hat, 4, 5, true⟩
                                                (.similar 0 ⟨false, 4⟩)
                                                (.split false ⟨.hat, 5, 5, true⟩
                                                  (.similar 0 ⟨false, 5⟩)
                                                  (.terminal (.hubcap [⟨0, some 5, 0⟩, ⟨1, some 3, 0⟩, ⟨2, some 4, 0⟩]))))))))))))))))))))))))))

theorem structureCheck_eq_true :
    structureCheck arity code = true := by
  rfl

end ClassicalCertificatePresentationData6

end Mettapedia.GraphTheory.FourColor
