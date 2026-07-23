import Mettapedia.GraphTheory.FourColor.ClassicalCertificatePresentationCertificate

/-! Generated finite unavoidability presentation certificate. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000000

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificatePresentationData8

open ClassicalCertificatePresentationPattern
open ClassicalCertificatePresentationCertificate

def sourceSha256 : String := "92d46e0d17b5332c3e7190360fe758e9a8ca0c37c3baa9d95f467732432c7eba"
def arity : Nat := 8
def splitCount : Nat := 2211
def leafCount : Nat := 2212

def code : Code :=
  (.split true ⟨.spoke, 7, 5, true⟩
    (.split true ⟨.spoke, 6, 5, true⟩
      (.split true ⟨.spoke, 5, 5, true⟩
        (.split true ⟨.spoke, 4, 5, true⟩
          (.split false ⟨.spoke, 0, 5, true⟩
            (.terminal .reducible)
            (.split false ⟨.spoke, 3, 5, true⟩
              (.terminal .reducible)
              (.split true ⟨.hat, 4, 5, true⟩
                (.split false ⟨.spoke, 3, 6, true⟩
                  (.terminal .reducible)
                  (.split false ⟨.hat, 5, 6, true⟩
                    (.terminal .reducible)
                    (.split false ⟨.spoke, 1, 7, false⟩
                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨4, none, 3⟩, ⟨6, none, 5⟩, ⟨2, some 3, 2⟩, ⟨5, some 7, 8⟩]))
                      (.split false ⟨.spoke, 2, 7, false⟩
                        (.terminal (.hubcap [⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨6, none, 5⟩, ⟨0, some 1, 3⟩, ⟨5, some 7, 8⟩]))
                        (.split false ⟨.spoke, 0, 6, true⟩
                          (.split false ⟨.spoke, 1, 5, true⟩
                            (.terminal .reducible)
                            (.split false ⟨.hat, 0, 5, true⟩
                              (.terminal .reducible)
                              (.split false ⟨.spoke, 1, 6, false⟩
                                (.terminal (.hubcap [⟨1, none, 1⟩, ⟨4, none, 3⟩, ⟨0, some 6, 6⟩, ⟨2, some 3, 2⟩, ⟨5, some 7, 8⟩]))
                                (.split false ⟨.hat, 1, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.spoke, 2, 5, false⟩
                                    (.terminal (.hubcap [⟨1, none, 0⟩, ⟨4, none, 3⟩, ⟨0, some 6, 6⟩, ⟨2, some 3, 3⟩, ⟨5, some 7, 8⟩]))
                                    (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 3⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨0, some 5, 6⟩])))))))
                          (.split false ⟨.hat, 2, 5, true⟩
                            (.split false ⟨.spoke, 0, 7, false⟩
                              (.terminal (.hubcap [⟨0, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨6, none, 5⟩, ⟨1, some 2, 3⟩, ⟨5, some 7, 8⟩]))
                              (.split false ⟨.spoke, 1, 5, true⟩
                                (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨6, none, 5⟩, ⟨5, some 7, 8⟩]))
                                (.split false ⟨.spoke, 2, 5, false⟩
                                  (.terminal (.hubcap [⟨0, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨6, none, 5⟩, ⟨1, some 2, 2⟩, ⟨5, some 7, 8⟩]))
                                  (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 3⟩, ⟨6, none, 5⟩, ⟨5, some 7, 8⟩])))))
                            (.split false ⟨.spoke, 3, 7, true⟩
                              (.split false ⟨.spoke, 2, 5, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.fan2, 3, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.spoke, 0, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 0⟩, ⟨4, none, 3⟩, ⟨6, none, 5⟩, ⟨5, some 7, 8⟩, ⟨1, some 2, 3⟩, ⟨1, some 3, 3⟩, ⟨2, some 3, 3⟩]))
                                    (.split false ⟨.spoke, 1, 5, false⟩
                                      (.terminal (.hubcap [⟨4, none, 3⟩, ⟨6, none, 5⟩, ⟨0, some 2, 2⟩, ⟨1, some 3, 2⟩, ⟨5, some 7, 8⟩]))
                                      (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨6, none, 5⟩, ⟨5, some 7, 8⟩]))))))
                              (.split false ⟨.spoke, 1, 5, false⟩
                                (.terminal (.hubcap [⟨3, none, 0⟩, ⟨4, none, 3⟩, ⟨6, none, 5⟩, ⟨5, some 7, 8⟩, ⟨0, some 1, 3⟩, ⟨0, some 2, 3⟩, ⟨1, some 2, 3⟩]))
                                (.split false ⟨.spoke, 2, 5, false⟩
                                  (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 3⟩, ⟨5, none, 5⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩]))
                                  (.terminal (.hubcap [⟨0, none, -1⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 3⟩, ⟨6, none, 5⟩, ⟨5, some 7, 8⟩])))))))))))
                (.split false ⟨.hat, 0, 5, true⟩
                  (.similar 0 ⟨true, 4⟩)
                  (.split false ⟨.hat, 6, 5, true⟩
                    (.split false ⟨.hat, 5, 6, true⟩
                      (.terminal .reducible)
                      (.split false ⟨.hat, 7, 6, true⟩
                        (.terminal .reducible)
                        (.split false ⟨.spoke, 0, 6, true⟩
                          (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 1⟩, ⟨4, none, 3⟩, ⟨5, none, 5⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨2, some 3, 2⟩]))
                          (.split false ⟨.spoke, 1, 5, false⟩
                            (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 5⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨2, some 3, 2⟩]))
                            (.split false ⟨.spoke, 2, 5, false⟩
                              (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨5, none, 5⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩]))
                              (.split false ⟨.spoke, 3, 6, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.hat, 2, 5, true⟩
                                  (.terminal .reducible)
                                  (.terminal (.hubcap [⟨0, none, -1⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 3⟩, ⟨5, none, 5⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩])))))))))
                    (.split false ⟨.hat, 6, 6, true⟩
                      (.terminal (.hubcap [⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨0, some 1, 3⟩, ⟨2, some 3, 3⟩]))
                      (.split true ⟨.spoke, 0, 6, true⟩
                        (.split false ⟨.spoke, 1, 5, true⟩
                          (.terminal .reducible)
                          (.split true ⟨.spoke, 1, 6, true⟩
                            (.split false ⟨.hat, 1, 5, true⟩
                              (.terminal .reducible)
                              (.split false ⟨.spoke, 2, 7, false⟩
                                (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨5, none, 5⟩, ⟨7, none, 4⟩, ⟨0, some 6, 6⟩, ⟨3, some 4, 5⟩]))
                                (.split false ⟨.spoke, 3, 6, true⟩
                                  (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨5, none, 5⟩, ⟨7, none, 4⟩, ⟨0, some 6, 6⟩, ⟨3, some 4, 5⟩]))
                                  (.split false ⟨.spoke, 2, 5, false⟩
                                    (.terminal (.hubcap [⟨1, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨0, some 6, 6⟩, ⟨2, some 7, 5⟩]))
                                    (.split false ⟨.hat, 2, 5, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.hat, 7, 5, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.hat, 5, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩]))
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, -1⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩])))))))))
                            (.split false ⟨.hat, 5, 6, false⟩
                              (.terminal (.hubcap [⟨1, none, 1⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 6, 6⟩, ⟨2, some 3, 2⟩]))
                              (.split false ⟨.hat, 7, 6, false⟩
                                (.terminal (.hubcap [⟨0, none, 1⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨1, some 2, 2⟩, ⟨3, some 4, 5⟩]))
                                (.split false ⟨.spoke, 2, 5, true⟩
                                  (.split false ⟨.spoke, 3, 6, true⟩
                                    (.similar 0 ⟨true, 4⟩)
                                    (.split false ⟨.hat, 5, 5, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩]))
                                      (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, -1⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨7, none, 4⟩, ⟨0, some 6, 6⟩]))))
                                  (.split false ⟨.spoke, 3, 6, false⟩
                                    (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨7, none, 4⟩, ⟨0, some 6, 6⟩]))
                                    (.split false ⟨.spoke, 2, 6, true⟩
                                      (.similar 0 ⟨true, 4⟩)
                                      (.split true ⟨.hat, 4, 6, true⟩
                                        (.split false ⟨.hat, 5, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.fan1, 3, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.spoke, 1, 7, false⟩
                                              (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 6, 6⟩]))
                                              (.split false ⟨.spoke, 2, 7, false⟩
                                                (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 6, 6⟩]))
                                                (.split false ⟨.hat, 1, 5, false⟩
                                                  (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 6, 6⟩]))
                                                  (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 6, 6⟩])))))))
                                        (.split false ⟨.hat, 0, 6, true⟩
                                          (.similar 0 ⟨true, 4⟩)
                                          (.split false ⟨.hat, 5, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩]))
                                            (.split false ⟨.hat, 7, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩]))
                                              (.split true ⟨.spoke, 1, 7, false⟩
                                                (.split false ⟨.spoke, 2, 7, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩]))
                                                  (.split false ⟨.hat, 3, 5, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩]))
                                                    (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩]))))
                                                (.split false ⟨.spoke, 2, 7, false⟩
                                                  (.similar 0 ⟨true, 4⟩)
                                                  (.split true ⟨.hat, 1, 5, false⟩
                                                    (.split false ⟨.hat, 3, 5, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩]))
                                                      (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩])))
                                                    (.split false ⟨.hat, 3, 5, false⟩
                                                      (.similar 0 ⟨true, 4⟩)
                                                      (.split false ⟨.fan1, 1, 5, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.fan2, 2, 5, true⟩
                                                          (.terminal .reducible)
                                                          (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩])))))))))))))))))))
                        (.split false ⟨.spoke, 3, 6, true⟩
                          (.similar 0 ⟨true, 4⟩)
                          (.split false ⟨.spoke, 1, 7, false⟩
                            (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩]))
                            (.split false ⟨.spoke, 2, 7, false⟩
                              (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩]))
                              (.split false ⟨.hat, 2, 5, true⟩
                                (.split false ⟨.hat, 5, 5, false⟩
                                  (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩]))
                                  (.split false ⟨.spoke, 2, 5, true⟩
                                    (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, -1⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩]))
                                    (.split false ⟨.spoke, 1, 5, false⟩
                                      (.terminal (.hubcap [⟨0, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨1, some 2, 2⟩]))
                                      (.split false ⟨.spoke, 2, 6, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.fan1, 2, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.hat, 7, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩]))
                                            (.terminal (.hubcap [⟨0, none, -1⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩]))))))))
                                (.split true ⟨.spoke, 1, 5, false⟩
                                  (.split false ⟨.spoke, 2, 5, false⟩
                                    (.terminal (.hubcap [⟨0, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨1, some 2, 2⟩]))
                                    (.split false ⟨.hat, 5, 5, false⟩
                                      (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩]))
                                      (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, -1⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩]))))
                                  (.split false ⟨.spoke, 2, 5, false⟩
                                    (.similar 0 ⟨true, 4⟩)
                                    (.split false ⟨.hat, 5, 5, false⟩
                                      (.terminal (.hubcap [⟨0, none, -1⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨3, none, -1⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩]))
                                      (.split false ⟨.hat, 7, 5, false⟩
                                        (.terminal (.hubcap [⟨0, none, -1⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩]))
                                        (.terminal (.hubcap [⟨0, none, -2⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨3, none, -2⟩, ⟨4, none, 4⟩, ⟨5, none, 5⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩])))))))))))))))))
          (.split false ⟨.spoke, 0, 5, true⟩
            (.similar 0 ⟨false, 1⟩)
            (.split true ⟨.spoke, 3, 5, true⟩
              (.split false ⟨.spoke, 4, 6, true⟩
                (.terminal .reducible)
                (.split false ⟨.spoke, 2, 5, true⟩
                  (.split false ⟨.spoke, 1, 5, true⟩
                    (.terminal .reducible)
                    (.split false ⟨.spoke, 0, 7, false⟩
                      (.terminal (.hubcap [⟨0, none, 0⟩, ⟨2, none, 4⟩, ⟨4, none, -1⟩, ⟨6, none, 5⟩, ⟨1, some 3, 5⟩, ⟨5, some 7, 7⟩]))
                      (.split false ⟨.spoke, 1, 6, true⟩
                        (.split false ⟨.hat, 1, 5, true⟩
                          (.terminal .reducible)
                          (.split false ⟨.spoke, 0, 6, false⟩
                            (.terminal (.hubcap [⟨4, none, -1⟩, ⟨6, none, 5⟩, ⟨0, some 2, 4⟩, ⟨1, some 3, 5⟩, ⟨5, some 7, 7⟩]))
                            (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, -1⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨0, some 5, 5⟩]))))
                        (.split false ⟨.spoke, 0, 6, false⟩
                          (.terminal (.hubcap [⟨4, none, -1⟩, ⟨6, none, 5⟩, ⟨0, some 2, 5⟩, ⟨1, some 3, 4⟩, ⟨5, some 7, 7⟩]))
                          (.split false ⟨.hat, 2, 5, true⟩
                            (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, -1⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨0, some 5, 6⟩]))
                            (.split false ⟨.hat, 3, 5, false⟩
                              (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, -1⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨0, some 5, 6⟩]))
                              (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, -1⟩, ⟨0, some 6, 6⟩, ⟨5, some 7, 7⟩]))))))))
                  (.split false ⟨.spoke, 1, 5, true⟩
                    (.split false ⟨.spoke, 0, 6, true⟩
                      (.terminal .reducible)
                      (.split false ⟨.spoke, 2, 6, true⟩
                        (.terminal .reducible)
                        (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨6, none, 5⟩, ⟨5, some 7, 7⟩]))))
                    (.split false ⟨.spoke, 0, 7, false⟩
                      (.terminal (.hubcap [⟨0, none, 0⟩, ⟨3, none, 3⟩, ⟨4, none, 0⟩, ⟨6, none, 5⟩, ⟨1, some 2, 5⟩, ⟨5, some 7, 7⟩]))
                      (.split false ⟨.spoke, 2, 7, false⟩
                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩]))
                        (.split false ⟨.spoke, 0, 6, true⟩
                          (.split false ⟨.hat, 3, 5, false⟩
                            (.terminal (.hubcap [⟨1, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨6, none, 5⟩, ⟨0, some 5, 6⟩, ⟨2, some 7, 6⟩]))
                            (.split false ⟨.spoke, 2, 6, true⟩
                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 0⟩, ⟨6, none, 5⟩, ⟨5, some 7, 7⟩]))
                              (.split false ⟨.spoke, 1, 6, false⟩
                                (.terminal (.hubcap [⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨0, some 5, 6⟩, ⟨1, some 2, 3⟩]))
                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 4⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩])))))
                          (.split false ⟨.spoke, 1, 7, false⟩
                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 0⟩, ⟨6, none, 5⟩, ⟨5, some 7, 7⟩]))
                            (.split false ⟨.spoke, 2, 6, false⟩
                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 4⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨6, none, 5⟩, ⟨5, some 7, 7⟩]))
                              (.split false ⟨.spoke, 1, 6, false⟩
                                (.split false ⟨.spoke, 4, 7, true⟩
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 0⟩, ⟨6, none, 5⟩, ⟨5, some 7, 7⟩]))
                                  (.split false ⟨.hat, 2, 5, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 0⟩, ⟨6, none, 5⟩, ⟨1, some 2, 3⟩, ⟨5, some 7, 7⟩]))
                                    (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 1⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 0⟩, ⟨6, none, 5⟩, ⟨5, some 7, 7⟩]))))
                                (.split false ⟨.hat, 1, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.hat, 2, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 0⟩, ⟨6, none, 5⟩, ⟨5, some 7, 7⟩]))
                                    (.split false ⟨.hat, 3, 5, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨6, none, 5⟩, ⟨1, some 2, 4⟩, ⟨5, some 7, 7⟩]))
                                      (.terminal (.hubcap [⟨0, none, 0⟩, ⟨3, none, 3⟩, ⟨4, none, 0⟩, ⟨6, none, 5⟩, ⟨1, some 2, 5⟩, ⟨5, some 7, 7⟩]))))))))))))))
              (.split false ⟨.spoke, 1, 5, true⟩
                (.similar 0 ⟨true, 3⟩)
                (.split false ⟨.spoke, 2, 5, true⟩
                  (.split true ⟨.hat, 6, 5, true⟩
                    (.split false ⟨.hat, 5, 5, true⟩
                      (.terminal .reducible)
                      (.split false ⟨.hat, 7, 6, true⟩
                        (.terminal .reducible)
                        (.split false ⟨.spoke, 1, 7, false⟩
                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨2, some 7, 6⟩, ⟨3, some 4, 3⟩]))
                          (.split false ⟨.spoke, 0, 6, true⟩
                            (.split false ⟨.hat, 1, 5, true⟩
                              (.terminal .reducible)
                              (.split false ⟨.hat, 2, 5, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.spoke, 1, 6, false⟩
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨2, some 7, 6⟩, ⟨3, some 4, 3⟩]))
                                  (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨3, some 4, 3⟩])))))
                            (.split false ⟨.spoke, 3, 6, true⟩
                              (.split false ⟨.spoke, 4, 6, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.spoke, 0, 7, false⟩
                                  (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 0⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩]))
                                  (.split false ⟨.spoke, 1, 6, true⟩
                                    (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨0, some 1, 3⟩]))
                                    (.split false ⟨.hat, 2, 5, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩]))
                                      (.split false ⟨.hat, 3, 5, false⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩]))
                                        (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 0⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨0, some 1, 2⟩])))))))
                              (.split false ⟨.spoke, 4, 6, false⟩
                                (.split false ⟨.spoke, 0, 7, false⟩
                                  (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨3, some 4, 2⟩]))
                                  (.split false ⟨.spoke, 1, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨3, some 4, 2⟩]))
                                    (.split false ⟨.hat, 1, 5, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.hat, 2, 5, false⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨3, some 4, 2⟩]))
                                        (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨3, some 4, 2⟩]))))))
                                (.split false ⟨.spoke, 3, 7, true⟩
                                  (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 0⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨0, some 2, 4⟩, ⟨0, some 4, 4⟩, ⟨2, some 4, 5⟩]))
                                  (.split false ⟨.spoke, 0, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨3, none, 0⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨2, some 4, 5⟩]))
                                    (.split false ⟨.spoke, 1, 6, false⟩
                                      (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨0, some 4, 4⟩]))
                                      (.split false ⟨.hat, 1, 5, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.hat, 2, 5, false⟩
                                          (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨0, some 4, 4⟩]))
                                          (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩])))))))))))))
                    (.split false ⟨.hat, 7, 5, true⟩
                      (.similar 0 ⟨true, 3⟩)
                      (.split false ⟨.spoke, 0, 7, false⟩
                        (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨2, some 5, 6⟩, ⟨3, some 4, 4⟩]))
                        (.split false ⟨.spoke, 1, 7, false⟩
                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 4, 4⟩, ⟨3, some 5, 6⟩]))
                          (.split false ⟨.spoke, 3, 7, false⟩
                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨6, none, 4⟩, ⟨1, some 5, 6⟩, ⟨2, some 7, 6⟩]))
                            (.split false ⟨.spoke, 3, 6, true⟩
                              (.terminal (.hubcap [⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨0, some 3, 4⟩, ⟨1, some 7, 5⟩, ⟨2, some 4, 4⟩]))
                              (.split false ⟨.spoke, 4, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨2, some 7, 6⟩]))
                                (.split false ⟨.spoke, 4, 6, true⟩
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 5, 6⟩]))
                                  (.split false ⟨.spoke, 0, 6, false⟩
                                    (.terminal (.hubcap [⟨3, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨0, some 2, 4⟩, ⟨1, some 4, 4⟩]))
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 3, 3⟩])))))))))))
                  (.split false ⟨.spoke, 2, 7, false⟩
                    (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨0, some 4, 5⟩]))
                    (.split true ⟨.spoke, 0, 7, false⟩
                      (.split false ⟨.spoke, 1, 6, false⟩
                        (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨2, some 3, 3⟩, ⟨4, some 7, 6⟩]))
                        (.split false ⟨.spoke, 2, 6, false⟩
                          (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 0⟩, ⟨2, none, 4⟩, ⟨3, none, 1⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨4, some 7, 6⟩]))
                          (.split false ⟨.spoke, 3, 6, false⟩
                            (.terminal (.hubcap [⟨0, none, 0⟩, ⟨3, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨1, some 2, 3⟩, ⟨4, some 7, 6⟩]))
                            (.split false ⟨.spoke, 4, 6, false⟩
                              (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, 5⟩, ⟨2, some 3, 4⟩, ⟨5, some 7, 7⟩]))
                              (.terminal (.hubcap [⟨0, none, 0⟩, ⟨2, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨1, some 3, 2⟩, ⟨4, some 7, 6⟩]))))))
                      (.split false ⟨.spoke, 4, 7, false⟩
                        (.similar 0 ⟨true, 3⟩)
                        (.split true ⟨.hat, 1, 5, true⟩
                          (.split false ⟨.spoke, 1, 6, true⟩
                            (.terminal .reducible)
                            (.split false ⟨.spoke, 3, 7, false⟩
                              (.terminal (.hubcap [⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨0, some 1, 4⟩]))
                              (.split false ⟨.hat, 0, 6, false⟩
                                (.terminal (.hubcap [⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨0, some 1, 2⟩, ⟨2, some 3, 3⟩, ⟨4, some 7, 6⟩]))
                                (.split true ⟨.hat, 6, 5, false⟩
                                  (.split false ⟨.spoke, 0, 6, false⟩
                                    (.terminal (.hubcap [⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨7, none, 4⟩, ⟨0, some 6, 6⟩, ⟨2, some 3, 3⟩, ⟨2, some 5, 5⟩, ⟨3, some 5, 5⟩]))
                                    (.split false ⟨.fan1, 0, 6, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.spoke, 1, 7, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨4, none, 2⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨2, some 3, 3⟩, ⟨2, some 5, 5⟩, ⟨3, some 5, 5⟩]))
                                        (.split false ⟨.fan1, 1, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.spoke, 3, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨4, none, 2⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨3, some 5, 5⟩]))
                                            (.split false ⟨.hat, 4, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.spoke, 4, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨5, none, 3⟩, ⟨7, none, 4⟩, ⟨2, some 3, 3⟩, ⟨4, some 6, 6⟩]))
                                                (.split false ⟨.spoke, 2, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨2, some 5, 5⟩]))
                                                  (.split false ⟨.hat, 2, 5, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.hat, 3, 5, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩]))
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨5, none, 3⟩, ⟨7, none, 4⟩, ⟨4, some 6, 6⟩]))))))))))))
                                  (.split false ⟨.hat, 5, 5, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.hat, 7, 6, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.hat, 4, 5, true⟩
                                        (.similar 0 ⟨true, 3⟩)
                                        (.split false ⟨.spoke, 1, 7, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨3, some 4, 3⟩]))
                                          (.split false ⟨.fan1, 1, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.spoke, 2, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨3, none, 0⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨2, some 4, 4⟩]))
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨1, some 7, 5⟩, ⟨2, some 3, 3⟩, ⟨2, some 4, 3⟩, ⟨3, some 4, 3⟩]))))))))))))
                          (.split false ⟨.hat, 4, 5, true⟩
                            (.similar 0 ⟨true, 3⟩)
                            (.split true ⟨.hat, 6, 5, true⟩
                              (.split false ⟨.hat, 5, 5, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.hat, 7, 6, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.spoke, 1, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨3, some 4, 3⟩]))
                                    (.split false ⟨.spoke, 3, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨3, some 4, 3⟩, ⟨1, some 2, 3⟩, ⟨1, some 7, 5⟩, ⟨2, some 7, 5⟩]))
                                      (.split false ⟨.spoke, 2, 6, false⟩
                                        (.split false ⟨.spoke, 0, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨3, none, 0⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨2, some 4, 6⟩]))
                                          (.split false ⟨.spoke, 1, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩]))
                                            (.split false ⟨.spoke, 4, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩]))
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨3, none, 0⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨2, some 7, 6⟩])))))
                                        (.split false ⟨.spoke, 1, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨1, some 7, 5⟩, ⟨2, some 3, 3⟩, ⟨2, some 4, 3⟩, ⟨3, some 4, 3⟩]))
                                          (.split false ⟨.hat, 2, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨3, some 4, 3⟩]))
                                            (.split false ⟨.hat, 3, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨3, some 4, 3⟩, ⟨1, some 2, 3⟩, ⟨1, some 7, 5⟩, ⟨2, some 7, 5⟩]))
                                              (.split false ⟨.spoke, 4, 6, true⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨2, some 7, 6⟩]))
                                                (.split false ⟨.spoke, 0, 6, true⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨2, some 7, 6⟩]))
                                                  (.split false ⟨.hat, 2, 5, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨2, some 3, 3⟩]))
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩])))))))))))))
                              (.split false ⟨.hat, 7, 5, true⟩
                                (.similar 0 ⟨true, 3⟩)
                                (.split false ⟨.spoke, 3, 6, false⟩
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, 4⟩, ⟨2, some 7, 5⟩, ⟨3, some 5, 5⟩]))
                                  (.split false ⟨.spoke, 4, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨1, some 7, 5⟩, ⟨2, some 3, 4⟩]))
                                    (.split false ⟨.spoke, 0, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨1, some 2, 4⟩, ⟨3, some 5, 5⟩]))
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 2, 3⟩, ⟨3, some 5, 5⟩])))))))))))))))))
        (.split false ⟨.spoke, 0, 5, true⟩
          (.similar 0 ⟨false, 1⟩)
          (.split true ⟨.spoke, 3, 5, true⟩
            (.split false ⟨.spoke, 4, 5, true⟩
              (.split false ⟨.spoke, 2, 5, true⟩
                (.similar 0 ⟨false, 5⟩)
                (.split false ⟨.spoke, 5, 6, true⟩
                  (.terminal .reducible)
                  (.split false ⟨.spoke, 1, 5, true⟩
                    (.split true ⟨.spoke, 0, 6, true⟩
                      (.split false ⟨.spoke, 2, 6, true⟩
                        (.terminal .reducible)
                        (.split false ⟨.hat, 4, 5, true⟩
                          (.terminal .reducible)
                          (.split false ⟨.hat, 1, 5, false⟩
                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                            (.split false ⟨.fan1, 0, 5, true⟩
                              (.terminal .reducible)
                              (.split false ⟨.hat, 2, 5, true⟩
                                (.terminal (.hubcap [⟨1, none, 3⟩, ⟨2, none, -1⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨7, none, 4⟩, ⟨0, some 6, 8⟩]))
                                (.split false ⟨.hat, 6, 5, true⟩
                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, -1⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩]))
                                  (.split false ⟨.hat, 7, 5, false⟩
                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, -1⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩]))
                                    (.terminal (.hubcap [⟨0, none, 5⟩, ⟨1, none, 3⟩, ⟨2, none, -1⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, -1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩])))))))))
                      (.split false ⟨.spoke, 2, 6, true⟩
                        (.similar 0 ⟨true, 5⟩)
                        (.split true ⟨.hat, 4, 5, false⟩
                          (.split false ⟨.spoke, 0, 7, false⟩
                            (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨0, some 6, 5⟩, ⟨2, some 7, 7⟩]))
                            (.split false ⟨.spoke, 2, 8, false⟩
                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                              (.split false ⟨.hat, 6, 5, true⟩
                                (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 2, 6⟩]))
                                (.split false ⟨.hat, 7, 5, false⟩
                                  (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 2, 6⟩]))
                                  (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, -1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 2, 5⟩]))))))
                          (.split false ⟨.hat, 7, 5, false⟩
                            (.similar 0 ⟨true, 5⟩)
                            (.split false ⟨.hat, 3, 5, true⟩
                              (.terminal .reducible)
                              (.split false ⟨.hat, 5, 5, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.hat, 6, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.hat, 0, 5, true⟩
                                    (.terminal .reducible)
                                    (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, -1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 2, 3⟩]))))))))))
                    (.split true ⟨.hat, 3, 5, true⟩
                      (.split false ⟨.hat, 4, 6, true⟩
                        (.terminal .reducible)
                        (.split false ⟨.spoke, 0, 7, false⟩
                          (.terminal (.hubcap [⟨0, none, 0⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 2, 5⟩]))
                          (.split false ⟨.spoke, 1, 7, false⟩
                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                            (.split false ⟨.spoke, 2, 7, false⟩
                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                              (.split false ⟨.spoke, 2, 6, false⟩
                                (.split false ⟨.spoke, 0, 6, false⟩
                                  (.terminal (.hubcap [⟨1, none, 0⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 2, 6⟩]))
                                  (.split false ⟨.spoke, 1, 6, true⟩
                                    (.terminal (.hubcap [⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 1, 5⟩, ⟨0, some 2, 7⟩, ⟨1, some 2, 5⟩]))
                                    (.split false ⟨.hat, 1, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                      (.split false ⟨.hat, 1, 5, true⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 2, 3⟩]))
                                        (.split false ⟨.hat, 2, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                          (.split false ⟨.hat, 6, 5, true⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩]))
                                            (.split false ⟨.hat, 7, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩]))
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, -1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩])))))))))
                                (.split false ⟨.fan1, 2, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.spoke, 1, 6, false⟩
                                    (.split false ⟨.hat, 6, 5, true⟩
                                      (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨0, some 1, 4⟩]))
                                      (.split false ⟨.hat, 7, 5, false⟩
                                        (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨0, some 1, 4⟩]))
                                        (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, -1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 4⟩]))))
                                    (.split false ⟨.spoke, 0, 6, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.hat, 0, 5, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.hat, 1, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 0⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 2, 5⟩]))
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩]))))))))))))
                      (.split false ⟨.hat, 0, 5, true⟩
                        (.similar 0 ⟨true, 5⟩)
                        (.split true ⟨.hat, 5, 5, true⟩
                          (.split false ⟨.spoke, 5, 7, true⟩
                            (.terminal .reducible)
                            (.split false ⟨.hat, 4, 6, true⟩
                              (.terminal .reducible)
                              (.split false ⟨.spoke, 0, 6, false⟩
                                (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 2, 4⟩]))
                                (.split false ⟨.spoke, 1, 6, false⟩
                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 2, 3⟩]))
                                  (.split false ⟨.spoke, 2, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                    (.split false ⟨.spoke, 2, 6, true⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                      (.split false ⟨.hat, 1, 5, false⟩
                                        (.terminal (.hubcap [⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨7, none, 4⟩, ⟨0, some 1, 4⟩, ⟨2, some 6, 6⟩]))
                                        (.split false ⟨.hat, 2, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                          (.split false ⟨.fan1, 1, 6, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.hat, 3, 6, true⟩
                                              (.terminal (.hubcap [⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨2, some 6, 5⟩]))
                                              (.split false ⟨.hat, 6, 5, true⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩]))
                                                (.split false ⟨.hat, 7, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩]))
                                                  (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, -1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩]))))))))))))))
                          (.split false ⟨.hat, 6, 5, true⟩
                            (.similar 0 ⟨true, 5⟩)
                            (.split true ⟨.spoke, 0, 7, false⟩
                              (.split false ⟨.spoke, 1, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                (.split false ⟨.spoke, 2, 6, false⟩
                                  (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                  (.split false ⟨.hat, 2, 5, false⟩
                                    (.terminal (.hubcap [⟨0, none, 0⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 2, 4⟩]))
                                    (.split false ⟨.hat, 3, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 0⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 2, 4⟩]))
                                      (.split false ⟨.fan1, 2, 6, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.hat, 4, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                          (.split false ⟨.hat, 7, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, -1⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩]))
                                            (.terminal (.hubcap [⟨0, none, 0⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, -1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 2, 5⟩])))))))))
                              (.split false ⟨.spoke, 2, 7, false⟩
                                (.similar 0 ⟨true, 5⟩)
                                (.split false ⟨.spoke, 1, 7, false⟩
                                  (.split false ⟨.hat, 3, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 1⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                    (.split false ⟨.hat, 4, 5, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                      (.split false ⟨.hat, 7, 5, false⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, -1⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩]))
                                        (.terminal (.hubcap [⟨1, none, 0⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, -1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 2, 5⟩])))))
                                  (.split true ⟨.hat, 4, 6, false⟩
                                    (.split false ⟨.spoke, 0, 6, false⟩
                                      (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 2, 4⟩]))
                                      (.split false ⟨.spoke, 1, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 2, 3⟩]))
                                        (.split false ⟨.spoke, 2, 6, true⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                          (.split false ⟨.hat, 1, 5, false⟩
                                            (.terminal (.hubcap [⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨7, none, 4⟩, ⟨0, some 1, 4⟩, ⟨2, some 6, 6⟩]))
                                            (.split false ⟨.hat, 2, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                              (.split false ⟨.fan1, 1, 6, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.hat, 3, 6, true⟩
                                                  (.terminal (.hubcap [⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨2, some 6, 5⟩]))
                                                  (.split false ⟨.hat, 7, 5, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩]))
                                                    (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, -1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩]))))))))))
                                    (.split false ⟨.hat, 7, 6, false⟩
                                      (.similar 0 ⟨true, 5⟩)
                                      (.split true ⟨.hat, 4, 5, false⟩
                                        (.split false ⟨.spoke, 0, 6, false⟩
                                          (.split false ⟨.spoke, 1, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                            (.split false ⟨.spoke, 2, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                              (.split false ⟨.hat, 1, 5, false⟩
                                                (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩])))))
                                          (.split false ⟨.hat, 1, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨1, some 6, 5⟩, ⟨2, some 7, 6⟩]))
                                            (.split false ⟨.hat, 7, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩]))
                                              (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, -1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩])))))
                                        (.split false ⟨.hat, 7, 5, false⟩
                                          (.similar 0 ⟨true, 5⟩)
                                          (.split false ⟨.spoke, 1, 6, true⟩
                                            (.split false ⟨.hat, 1, 5, true⟩
                                              (.terminal (.hubcap [⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, -1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨0, some 2, 4⟩, ⟨1, some 2, 2⟩]))
                                              (.split false ⟨.spoke, 0, 6, false⟩
                                                (.terminal (.hubcap [⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, -1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 2⟩, ⟨0, some 2, 4⟩, ⟨1, some 2, 5⟩]))
                                                (.terminal (.hubcap [⟨1, none, 1⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, -1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 2, 4⟩]))))
                                            (.split false ⟨.spoke, 0, 6, false⟩
                                              (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, -1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 2⟩]))
                                              (.split false ⟨.spoke, 2, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, -1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 2, 2⟩]))
                                                (.terminal (.hubcap [⟨1, none, 1⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, -1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 2, 4⟩])))))))))))))))))))
              (.split false ⟨.spoke, 2, 5, true⟩
                (.split false ⟨.spoke, 1, 5, true⟩
                  (.similar 0 ⟨false, 4⟩)
                  (.split true ⟨.hat, 3, 5, true⟩
                    (.split false ⟨.hat, 2, 5, true⟩
                      (.terminal .reducible)
                      (.split false ⟨.hat, 4, 5, true⟩
                        (.terminal .reducible)
                        (.split true ⟨.spoke, 0, 6, false⟩
                          (.split false ⟨.hat, 6, 5, true⟩
                            (.split false ⟨.hat, 7, 6, true⟩
                              (.terminal .reducible)
                              (.split false ⟨.spoke, 1, 6, false⟩
                                (.terminal (.hubcap [⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨0, some 1, 2⟩, ⟨4, some 5, 3⟩]))
                                (.split false ⟨.spoke, 4, 6, false⟩
                                  (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨4, some 5, 2⟩]))
                                  (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩])))))
                            (.split false ⟨.hat, 7, 5, false⟩
                              (.terminal (.hubcap [⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 1, 3⟩, ⟨4, some 5, 3⟩]))
                              (.split false ⟨.hat, 0, 5, true⟩
                                (.terminal .reducible)
                                (.split true ⟨.spoke, 1, 6, false⟩
                                  (.split false ⟨.spoke, 4, 6, true⟩
                                    (.terminal (.hubcap [⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 2⟩, ⟨0, some 4, 3⟩, ⟨1, some 4, 3⟩]))
                                    (.split false ⟨.spoke, 5, 6, false⟩
                                      (.terminal (.hubcap [⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 2⟩, ⟨4, some 5, 2⟩]))
                                      (.terminal (.hubcap [⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 2⟩, ⟨0, some 5, 3⟩, ⟨1, some 5, 3⟩]))))
                                  (.split false ⟨.spoke, 4, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 0⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 5, 4⟩]))
                                    (.split false ⟨.spoke, 4, 6, true⟩
                                      (.terminal (.hubcap [⟨0, none, 0⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 4, 4⟩]))
                                      (.split false ⟨.spoke, 5, 6, false⟩
                                        (.similar 0 ⟨false, 4⟩)
                                        (.split false ⟨.hat, 4, 6, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.hat, 5, 5, true⟩
                                            (.terminal .reducible)
                                            (.terminal (.hubcap [⟨0, none, 0⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 5, 4⟩])))))))))))
                          (.split false ⟨.spoke, 5, 6, false⟩
                            (.similar 0 ⟨true, 2⟩)
                            (.split false ⟨.spoke, 1, 6, true⟩
                              (.terminal .reducible)
                              (.split false ⟨.spoke, 4, 6, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.hat, 7, 5, true⟩
                                  (.similar 0 ⟨false, 4⟩)
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩])))))))))
                    (.split false ⟨.hat, 7, 5, true⟩
                      (.similar 0 ⟨false, 4⟩)
                      (.split false ⟨.spoke, 0, 7, false⟩
                        (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨7, none, 3⟩, ⟨3, some 6, 7⟩, ⟨4, some 5, 4⟩]))
                        (.split false ⟨.spoke, 1, 7, false⟩
                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨7, none, 4⟩, ⟨3, some 6, 7⟩, ⟨4, some 5, 4⟩]))
                          (.split false ⟨.spoke, 4, 7, false⟩
                            (.terminal (.hubcap [⟨3, none, 3⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨0, some 1, 4⟩, ⟨2, some 7, 7⟩]))
                            (.split false ⟨.spoke, 5, 7, false⟩
                              (.terminal (.hubcap [⟨3, none, 4⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨0, some 1, 4⟩, ⟨2, some 7, 7⟩]))
                              (.split true ⟨.hat, 1, 5, true⟩
                                (.split false ⟨.hat, 4, 5, true⟩
                                  (.terminal (.hubcap [⟨2, none, 3⟩, ⟨4, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 1, 4⟩, ⟨3, some 5, 5⟩]))
                                  (.split false ⟨.spoke, 4, 6, true⟩
                                    (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 1, 4⟩, ⟨4, some 5, 4⟩]))
                                    (.split false ⟨.spoke, 5, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨4, some 5, 2⟩]))
                                      (.split false ⟨.hat, 5, 5, false⟩
                                        (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨0, some 1, 4⟩]))
                                        (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 1, 4⟩, ⟨4, some 5, 4⟩]))))))
                                (.split false ⟨.hat, 5, 5, true⟩
                                  (.similar 0 ⟨false, 4⟩)
                                  (.split true ⟨.hat, 2, 5, true⟩
                                    (.split false ⟨.hat, 3, 6, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.spoke, 0, 6, true⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 3⟩, ⟨7, none, 3⟩, ⟨3, some 5, 6⟩, ⟨4, some 6, 5⟩]))
                                        (.split false ⟨.spoke, 1, 6, true⟩
                                          (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨7, none, 3⟩, ⟨3, some 5, 6⟩, ⟨4, some 6, 5⟩]))
                                          (.split false ⟨.spoke, 4, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨5, none, 2⟩, ⟨7, none, 3⟩, ⟨4, some 6, 5⟩]))
                                            (.split false ⟨.spoke, 5, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩]))
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨4, some 5, 4⟩])))))))
                                    (.split false ⟨.hat, 4, 5, true⟩
                                      (.similar 0 ⟨true, 2⟩)
                                      (.split false ⟨.hat, 6, 5, true⟩
                                        (.similar 0 ⟨false, 4⟩)
                                        (.split false ⟨.hat, 0, 5, true⟩
                                          (.similar 0 ⟨true, 6⟩)
                                          (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 1, 4⟩, ⟨4, some 5, 4⟩])))))))))))))))
                (.split false ⟨.spoke, 1, 5, true⟩
                  (.split false ⟨.spoke, 2, 6, true⟩
                    (.split false ⟨.spoke, 0, 6, true⟩
                      (.terminal .reducible)
                      (.split false ⟨.spoke, 5, 6, true⟩
                        (.terminal (.hubcap [⟨2, none, 5⟩, ⟨6, none, 4⟩, ⟨0, some 1, 3⟩, ⟨3, some 4, 3⟩, ⟨5, some 7, 5⟩]))
                        (.split false ⟨.hat, 3, 5, false⟩
                          (.split false ⟨.spoke, 4, 7, false⟩
                            (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨2, none, 4⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                            (.split false ⟨.spoke, 4, 6, true⟩
                              (.terminal (.hubcap [⟨2, none, 4⟩, ⟨0, some 1, 3⟩, ⟨4, some 7, 5⟩, ⟨3, some 5, 5⟩, ⟨3, some 6, 6⟩, ⟨5, some 6, 6⟩]))
                              (.split false ⟨.spoke, 5, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨2, none, 4⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                (.split false ⟨.hat, 2, 5, false⟩
                                  (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨7, none, 4⟩, ⟨5, some 6, 6⟩]))
                                  (.terminal (.hubcap [⟨0, none, -1⟩, ⟨1, none, 3⟩, ⟨2, none, 4⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨7, none, 4⟩, ⟨5, some 6, 6⟩]))))))
                          (.split false ⟨.fan1, 2, 5, true⟩
                            (.terminal .reducible)
                            (.split false ⟨.hat, 2, 5, false⟩
                              (.split false ⟨.spoke, 0, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨7, none, 4⟩, ⟨3, some 6, 7⟩, ⟨4, some 5, 3⟩]))
                                (.split false ⟨.hat, 1, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.hat, 0, 5, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.spoke, 4, 7, false⟩
                                      (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨3, none, 3⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                      (.split false ⟨.spoke, 4, 6, true⟩
                                        (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨5, none, 0⟩, ⟨3, some 6, 7⟩, ⟨4, some 7, 6⟩]))
                                        (.split false ⟨.spoke, 5, 7, false⟩
                                          (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                          (.split false ⟨.hat, 1, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨3, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 3⟩]))
                                            (.split false ⟨.hat, 4, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 1⟩, ⟨7, none, 4⟩, ⟨5, some 6, 6⟩]))
                                              (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨3, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 2⟩]))))))))))
                              (.split false ⟨.fan1, 2, 6, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.spoke, 4, 7, false⟩
                                  (.terminal (.hubcap [⟨0, none, -1⟩, ⟨1, none, 3⟩, ⟨2, none, 5⟩, ⟨3, none, 3⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                  (.split false ⟨.spoke, 4, 6, true⟩
                                    (.terminal (.hubcap [⟨0, none, -1⟩, ⟨1, none, 3⟩, ⟨2, none, 5⟩, ⟨5, none, 0⟩, ⟨3, some 6, 7⟩, ⟨4, some 7, 6⟩]))
                                    (.split false ⟨.spoke, 5, 7, false⟩
                                      (.terminal (.hubcap [⟨0, none, -1⟩, ⟨1, none, 3⟩, ⟨2, none, 5⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                      (.split false ⟨.hat, 4, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, -1⟩, ⟨1, none, 3⟩, ⟨2, none, 5⟩, ⟨3, none, 3⟩, ⟨4, none, 0⟩, ⟨7, none, 4⟩, ⟨5, some 6, 6⟩]))
                                        (.split false ⟨.hat, 4, 5, true⟩
                                          (.terminal (.hubcap [⟨0, none, -1⟩, ⟨1, none, 3⟩, ⟨2, none, 5⟩, ⟨3, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 2⟩]))
                                          (.split false ⟨.spoke, 0, 7, true⟩
                                            (.terminal (.hubcap [⟨0, none, -1⟩, ⟨1, none, 3⟩, ⟨2, none, 4⟩, ⟨3, none, 3⟩, ⟨4, none, 1⟩, ⟨7, none, 4⟩, ⟨5, some 6, 6⟩]))
                                            (.split false ⟨.hat, 1, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, -1⟩, ⟨1, none, 3⟩, ⟨2, none, 4⟩, ⟨3, none, 3⟩, ⟨4, none, 1⟩, ⟨7, none, 4⟩, ⟨5, some 6, 6⟩]))
                                              (.split false ⟨.hat, 5, 5, false⟩
                                                (.terminal (.hubcap [⟨0, none, -1⟩, ⟨1, none, 3⟩, ⟨2, none, 5⟩, ⟨3, none, 3⟩, ⟨4, none, 1⟩, ⟨7, none, 4⟩, ⟨5, some 6, 5⟩]))
                                                (.split false ⟨.fan1, 5, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.hat, 6, 5, false⟩
                                                    (.terminal (.hubcap [⟨0, none, -1⟩, ⟨1, none, 3⟩, ⟨2, none, 5⟩, ⟨3, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 2⟩]))
                                                    (.terminal (.hubcap [⟨0, none, -1⟩, ⟨1, none, 3⟩, ⟨2, none, 5⟩, ⟨3, none, 3⟩, ⟨4, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩]))))))))))))))))))
                    (.split false ⟨.hat, 7, 5, true⟩
                      (.split false ⟨.hat, 6, 5, true⟩
                        (.terminal .reducible)
                        (.split false ⟨.hat, 0, 5, true⟩
                          (.terminal .reducible)
                          (.split false ⟨.spoke, 0, 7, false⟩
                            (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 6⟩, ⟨4, some 5, 3⟩]))
                            (.split false ⟨.spoke, 0, 6, true⟩
                              (.terminal (.hubcap [⟨0, none, 5⟩, ⟨3, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 2, 3⟩, ⟨4, some 5, 2⟩]))
                              (.split false ⟨.spoke, 2, 8, false⟩
                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 3⟩]))
                                (.split false ⟨.hat, 1, 5, true⟩
                                  (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 2, 6⟩, ⟨4, some 5, 2⟩]))
                                  (.split false ⟨.spoke, 2, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 3⟩]))
                                    (.split false ⟨.spoke, 4, 7, false⟩
                                      (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 5, 4⟩]))
                                      (.split false ⟨.spoke, 4, 6, true⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 6⟩]))
                                        (.split false ⟨.spoke, 5, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨3, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 2⟩]))
                                          (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 5, 4⟩]))))))))))))
                      (.split false ⟨.spoke, 0, 8, false⟩
                        (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨7, none, 3⟩, ⟨3, some 6, 6⟩, ⟨4, some 5, 5⟩]))
                        (.split false ⟨.spoke, 4, 7, false⟩
                          (.terminal (.hubcap [⟨1, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨0, some 2, 6⟩, ⟨6, some 7, 7⟩]))
                          (.split false ⟨.spoke, 5, 7, false⟩
                            (.terminal (.hubcap [⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨0, some 2, 6⟩, ⟨1, some 3, 5⟩, ⟨4, some 7, 6⟩]))
                            (.split false ⟨.spoke, 0, 6, true⟩
                              (.split false ⟨.spoke, 2, 7, true⟩
                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩]))
                                (.split false ⟨.spoke, 4, 6, true⟩
                                  (.terminal (.hubcap [⟨0, none, 5⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩]))
                                  (.split false ⟨.spoke, 5, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 5⟩, ⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨1, some 2, 3⟩, ⟨4, some 5, 3⟩]))
                                    (.terminal (.hubcap [⟨0, none, 5⟩, ⟨1, none, 3⟩, ⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨2, some 4, 2⟩, ⟨5, some 7, 5⟩])))))
                              (.split false ⟨.spoke, 2, 8, false⟩
                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨7, none, 3⟩, ⟨3, some 6, 6⟩, ⟨4, some 5, 5⟩]))
                                (.split false ⟨.spoke, 5, 6, true⟩
                                  (.split false ⟨.hat, 4, 5, true⟩
                                    (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨0, some 2, 6⟩]))
                                    (.split false ⟨.hat, 5, 6, false⟩
                                      (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 2⟩, ⟨5, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 2, 6⟩, ⟨4, some 6, 5⟩]))
                                      (.split false ⟨.hat, 6, 6, false⟩
                                        (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 2, 6⟩, ⟨4, some 5, 4⟩]))
                                        (.split false ⟨.fan1, 5, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.spoke, 2, 7, false⟩
                                            (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 2⟩, ⟨7, none, 3⟩, ⟨2, some 4, 4⟩, ⟨0, some 5, 6⟩, ⟨0, some 6, 7⟩, ⟨5, some 6, 6⟩]))
                                            (.split false ⟨.hat, 2, 5, true⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩]))
                                              (.split false ⟨.spoke, 0, 7, false⟩
                                                (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨5, some 6, 6⟩]))
                                                (.split false ⟨.hat, 1, 5, true⟩
                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨5, some 6, 6⟩]))
                                                  (.split false ⟨.spoke, 4, 6, false⟩
                                                    (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨0, some 5, 4⟩]))
                                                    (.split false ⟨.hat, 5, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.hat, 6, 5, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.hat, 2, 6, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨4, some 5, 5⟩]))
                                                          (.split false ⟨.hat, 3, 5, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩]))
                                                            (.split false ⟨.fan2, 2, 5, true⟩
                                                              (.terminal .reducible)
                                                              (.split false ⟨.hat, 4, 6, false⟩
                                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨4, some 5, 4⟩]))
                                                                (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 5, 4⟩])))))))))))))))))
                                  (.split false ⟨.spoke, 4, 6, false⟩
                                    (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 2, 6⟩, ⟨4, some 5, 4⟩]))
                                    (.split false ⟨.hat, 4, 5, false⟩
                                      (.split false ⟨.hat, 5, 5, false⟩
                                        (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 2, 6⟩, ⟨4, some 5, 4⟩]))
                                        (.split false ⟨.spoke, 2, 7, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨4, some 5, 5⟩]))
                                          (.split false ⟨.hat, 3, 5, false⟩
                                            (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 4⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 2, 5⟩]))
                                            (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 2, 6⟩, ⟨4, some 5, 4⟩])))))
                                      (.split false ⟨.hat, 5, 5, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.hat, 6, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.fan1, 4, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.spoke, 0, 7, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 5, 4⟩]))
                                              (.split false ⟨.hat, 1, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.spoke, 2, 7, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩]))
                                                  (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 2, 6⟩, ⟨4, some 5, 3⟩]))))))))))))))))))
                  (.split false ⟨.hat, 7, 5, true⟩
                    (.split false ⟨.hat, 6, 5, true⟩
                      (.terminal .reducible)
                      (.split false ⟨.hat, 0, 5, true⟩
                        (.terminal .reducible)
                        (.split false ⟨.spoke, 0, 7, false⟩
                          (.terminal (.hubcap [⟨0, none, 0⟩, ⟨3, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 2, 5⟩, ⟨4, some 5, 3⟩]))
                          (.split false ⟨.spoke, 1, 7, false⟩
                            (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 3, 6⟩, ⟨4, some 5, 3⟩]))
                            (.split false ⟨.spoke, 2, 7, false⟩
                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 3⟩]))
                              (.split false ⟨.spoke, 0, 6, false⟩
                                (.split false ⟨.spoke, 2, 6, false⟩
                                  (.terminal (.hubcap [⟨1, none, 0⟩, ⟨3, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 2, 5⟩, ⟨4, some 5, 3⟩]))
                                  (.split false ⟨.spoke, 4, 6, false⟩
                                    (.terminal (.hubcap [⟨3, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 3⟩, ⟨0, some 1, 3⟩, ⟨0, some 2, 5⟩, ⟨1, some 2, 5⟩]))
                                    (.split false ⟨.spoke, 5, 6, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.spoke, 1, 6, true⟩
                                        (.terminal (.hubcap [⟨0, none, 0⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 2, 5⟩]))
                                        (.split false ⟨.hat, 1, 6, false⟩
                                          (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 2⟩]))
                                          (.split false ⟨.hat, 1, 5, true⟩
                                            (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 2⟩]))
                                            (.split false ⟨.hat, 2, 5, false⟩
                                              (.terminal (.hubcap [⟨1, none, 1⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 2, 4⟩]))
                                              (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩])))))))))
                                (.split false ⟨.spoke, 1, 6, false⟩
                                  (.split false ⟨.hat, 3, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 3⟩]))
                                    (.split false ⟨.hat, 0, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 1⟩, ⟨3, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 2, 4⟩, ⟨4, some 5, 3⟩]))
                                      (.split false ⟨.fan1, 0, 5, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.spoke, 2, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 2, 3⟩, ⟨4, some 5, 3⟩]))
                                          (.split false ⟨.fan1, 2, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.spoke, 4, 7, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨4, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 2, 4⟩, ⟨3, some 5, 5⟩]))
                                              (.split false ⟨.spoke, 4, 6, true⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                                (.split false ⟨.spoke, 5, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 2, 4⟩, ⟨4, some 5, 2⟩]))
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨3, some 5, 5⟩]))))))))))
                                  (.split false ⟨.hat, 3, 5, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.spoke, 4, 6, false⟩
                                      (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨4, some 5, 3⟩]))
                                      (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩])))))))))))
                    (.split false ⟨.spoke, 0, 7, false⟩
                      (.terminal (.hubcap [⟨0, none, 0⟩, ⟨7, none, 3⟩, ⟨1, some 2, 5⟩, ⟨3, some 5, 6⟩, ⟨4, some 6, 6⟩]))
                      (.split false ⟨.spoke, 2, 7, false⟩
                        (.terminal (.hubcap [⟨2, none, 0⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨3, some 6, 6⟩, ⟨4, some 5, 5⟩]))
                        (.split false ⟨.spoke, 5, 6, true⟩
                          (.split false ⟨.spoke, 1, 7, false⟩
                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, some 6, 6⟩, ⟨5, some 7, 6⟩]))
                            (.split false ⟨.hat, 6, 5, false⟩
                              (.split false ⟨.spoke, 4, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 3⟩, ⟨4, none, 0⟩, ⟨6, none, 3⟩, ⟨1, some 2, 5⟩, ⟨5, some 7, 5⟩]))
                                (.split false ⟨.spoke, 1, 6, false⟩
                                  (.terminal (.hubcap [⟨6, none, 3⟩, ⟨3, some 4, 5⟩, ⟨5, some 7, 6⟩, ⟨0, some 1, 4⟩, ⟨0, some 2, 5⟩, ⟨1, some 2, 4⟩]))
                                  (.split false ⟨.spoke, 4, 6, false⟩
                                    (.split false ⟨.hat, 1, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨6, none, 3⟩, ⟨1, some 2, 5⟩, ⟨3, some 4, 5⟩, ⟨5, some 7, 5⟩]))
                                      (.split false ⟨.hat, 2, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨6, none, 3⟩, ⟨1, some 3, 4⟩, ⟨2, some 7, 5⟩, ⟨4, some 5, 4⟩]))
                                        (.split false ⟨.hat, 3, 5, false⟩
                                          (.terminal (.hubcap [⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨0, some 1, 5⟩, ⟨2, some 7, 6⟩, ⟨4, some 5, 4⟩]))
                                          (.split false ⟨.spoke, 2, 6, true⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨3, none, 3⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩]))
                                            (.split false ⟨.spoke, 0, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨2, none, 4⟩, ⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨4, some 5, 4⟩]))
                                              (.split false ⟨.hat, 0, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.hat, 1, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨1, some 2, 4⟩, ⟨4, some 5, 4⟩]))
                                                  (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 1, 5⟩, ⟨4, some 5, 4⟩])))))))))
                                    (.split false ⟨.hat, 4, 5, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.hat, 5, 5, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.spoke, 2, 6, true⟩
                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨4, some 5, 4⟩]))
                                          (.split false ⟨.spoke, 0, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨4, some 5, 5⟩]))
                                            (.split false ⟨.hat, 1, 5, false⟩
                                              (.terminal (.hubcap [⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨0, some 1, 4⟩, ⟨2, some 4, 5⟩, ⟨5, some 7, 6⟩]))
                                              (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨0, some 1, 5⟩, ⟨4, some 5, 5⟩, ⟨4, some 7, 6⟩, ⟨5, some 7, 6⟩]))))))))))
                              (.split false ⟨.spoke, 4, 6, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.hat, 7, 6, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.fan1, 5, 5, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.hat, 1, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨3, some 4, 4⟩, ⟨1, some 2, 5⟩, ⟨1, some 7, 5⟩, ⟨2, some 7, 7⟩]))
                                      (.split false ⟨.hat, 3, 5, false⟩
                                        (.split false ⟨.spoke, 1, 6, false⟩
                                          (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 4⟩]))
                                          (.split false ⟨.spoke, 4, 7, false⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨2, some 7, 6⟩]))
                                            (.split false ⟨.hat, 2, 6, false⟩
                                              (.terminal (.hubcap [⟨3, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨2, some 4, 3⟩]))
                                              (.split false ⟨.hat, 4, 5, true⟩
                                                (.terminal (.hubcap [⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨0, some 1, 5⟩, ⟨2, some 7, 6⟩]))
                                                (.split false ⟨.spoke, 0, 6, false⟩
                                                  (.terminal (.hubcap [⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨0, some 1, 5⟩, ⟨0, some 2, 6⟩, ⟨1, some 2, 4⟩]))
                                                  (.split false ⟨.spoke, 2, 6, true⟩
                                                    (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩]))
                                                    (.split false ⟨.hat, 1, 5, false⟩
                                                      (.terminal (.hubcap [⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨0, some 1, 4⟩, ⟨2, some 7, 6⟩]))
                                                      (.terminal (.hubcap [⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨0, some 2, 5⟩, ⟨1, some 7, 5⟩])))))))))
                                        (.split false ⟨.spoke, 0, 6, false⟩
                                          (.terminal (.hubcap [⟨3, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨0, some 2, 6⟩, ⟨1, some 4, 2⟩]))
                                          (.split false ⟨.spoke, 2, 6, true⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                            (.split false ⟨.spoke, 4, 7, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨2, some 7, 7⟩]))
                                              (.split false ⟨.spoke, 1, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 2, 4⟩]))
                                                (.split false ⟨.hat, 0, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.hat, 1, 5, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨1, some 2, 4⟩]))
                                                    (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨0, some 1, 4⟩])))))))))))))))
                          (.split false ⟨.spoke, 4, 7, false⟩
                            (.terminal (.hubcap [⟨3, none, 3⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩, ⟨0, some 1, 5⟩, ⟨2, some 7, 7⟩]))
                            (.split false ⟨.spoke, 1, 6, false⟩
                              (.split false ⟨.hat, 3, 6, false⟩
                                (.terminal (.hubcap [⟨2, none, 1⟩, ⟨3, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨0, some 1, 4⟩, ⟨4, some 5, 5⟩]))
                                (.split false ⟨.hat, 4, 6, false⟩
                                  (.terminal (.hubcap [⟨4, none, 1⟩, ⟨6, none, 3⟩, ⟨0, some 7, 6⟩, ⟨1, some 2, 4⟩, ⟨3, some 5, 6⟩]))
                                  (.split false ⟨.spoke, 2, 6, false⟩
                                    (.split false ⟨.spoke, 0, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨4, some 5, 5⟩]))
                                      (.split false ⟨.spoke, 1, 7, false⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩]))
                                        (.split false ⟨.spoke, 4, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨4, some 5, 4⟩]))
                                          (.split false ⟨.fan1, 4, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.spoke, 5, 7, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩]))
                                              (.split false ⟨.hat, 1, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨4, some 5, 5⟩]))
                                                (.split false ⟨.hat, 1, 5, true⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨1, some 2, 3⟩, ⟨4, some 5, 5⟩]))
                                                  (.split false ⟨.hat, 2, 5, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨4, some 5, 5⟩]))
                                                    (.split false ⟨.hat, 3, 5, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩]))
                                                      (.split false ⟨.hat, 4, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩]))))))))))))
                                    (.split false ⟨.fan1, 2, 5, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.spoke, 1, 7, false⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨4, some 5, 4⟩]))
                                        (.split false ⟨.hat, 3, 5, false⟩
                                          (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨0, some 1, 4⟩, ⟨4, some 5, 4⟩]))
                                          (.split false ⟨.spoke, 4, 6, false⟩
                                            (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨0, some 1, 4⟩, ⟨4, some 5, 3⟩]))
                                            (.split false ⟨.fan1, 4, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.spoke, 0, 6, false⟩
                                                (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 1, 4⟩]))
                                                (.split false ⟨.hat, 1, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.hat, 1, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨1, some 7, 5⟩]))
                                                    (.split false ⟨.hat, 2, 5, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨1, some 2, 4⟩]))
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩]))))))))))))))
                              (.split false ⟨.hat, 4, 5, true⟩
                                (.split false ⟨.hat, 1, 6, false⟩
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨6, none, 3⟩, ⟨1, some 2, 5⟩, ⟨3, some 5, 4⟩, ⟨4, some 7, 6⟩]))
                                  (.split false ⟨.hat, 2, 6, false⟩
                                    (.terminal (.hubcap [⟨6, none, 3⟩, ⟨3, some 5, 4⟩, ⟨4, some 7, 6⟩, ⟨0, some 1, 5⟩, ⟨0, some 2, 6⟩, ⟨1, some 2, 4⟩]))
                                    (.split false ⟨.hat, 3, 5, false⟩
                                      (.terminal (.hubcap [⟨4, none, 2⟩, ⟨6, none, 3⟩, ⟨0, some 1, 5⟩, ⟨2, some 7, 6⟩, ⟨3, some 5, 4⟩]))
                                      (.split false ⟨.spoke, 2, 6, true⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 4⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨1, some 2, 5⟩, ⟨4, some 5, 3⟩]))
                                        (.split false ⟨.spoke, 4, 6, false⟩
                                          (.terminal (.hubcap [⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 1, 5⟩, ⟨0, some 2, 7⟩, ⟨1, some 2, 5⟩]))
                                          (.split false ⟨.fan1, 4, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.spoke, 5, 7, false⟩
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨1, some 2, 4⟩]))
                                              (.split false ⟨.hat, 5, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.hat, 6, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.spoke, 0, 6, false⟩
                                                    (.terminal (.hubcap [⟨1, none, 0⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 2, 6⟩]))
                                                    (.split false ⟨.hat, 0, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.hat, 1, 5, false⟩
                                                        (.terminal (.hubcap [⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 1, 4⟩, ⟨0, some 2, 7⟩, ⟨1, some 2, 4⟩]))
                                                        (.terminal (.hubcap [⟨1, none, 1⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 2, 6⟩]))))))))))))))
                                (.split false ⟨.spoke, 5, 7, false⟩
                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨1, some 2, 5⟩, ⟨4, some 7, 5⟩]))
                                  (.split false ⟨.spoke, 4, 6, false⟩
                                    (.terminal (.hubcap [⟨6, none, 3⟩, ⟨4, some 5, 3⟩, ⟨0, some 1, 5⟩, ⟨0, some 3, 6⟩, ⟨1, some 2, 5⟩, ⟨2, some 7, 7⟩, ⟨3, some 7, 6⟩]))
                                    (.split false ⟨.hat, 1, 6, false⟩
                                      (.terminal (.hubcap [⟨6, none, 3⟩, ⟨0, some 3, 4⟩, ⟨4, some 5, 5⟩, ⟨1, some 2, 5⟩, ⟨1, some 7, 5⟩, ⟨2, some 7, 7⟩]))
                                      (.split false ⟨.hat, 2, 6, false⟩
                                        (.terminal (.hubcap [⟨6, none, 3⟩, ⟨2, some 7, 5⟩, ⟨4, some 5, 5⟩, ⟨0, some 1, 5⟩, ⟨0, some 3, 6⟩, ⟨1, some 3, 4⟩]))
                                        (.split false ⟨.hat, 7, 6, true⟩
                                          (.split false ⟨.hat, 6, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.hat, 0, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.spoke, 0, 6, false⟩
                                                (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 2, 5⟩, ⟨4, some 5, 4⟩]))
                                                (.split false ⟨.spoke, 2, 6, true⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩]))
                                                  (.split false ⟨.hat, 1, 5, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨1, some 2, 4⟩, ⟨4, some 5, 4⟩]))
                                                    (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 1, 5⟩, ⟨4, some 5, 4⟩])))))))
                                          (.split false ⟨.hat, 5, 6, false⟩
                                            (.terminal (.hubcap [⟨6, none, 3⟩, ⟨3, some 5, 4⟩, ⟨4, some 7, 5⟩, ⟨0, some 1, 5⟩, ⟨0, some 2, 7⟩, ⟨1, some 2, 5⟩]))
                                            (.split false ⟨.hat, 0, 5, false⟩
                                              (.split false ⟨.hat, 3, 5, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 4⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨1, some 2, 4⟩]))
                                                (.split false ⟨.spoke, 2, 6, true⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩]))
                                                  (.split false ⟨.spoke, 0, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 4⟩, ⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨4, some 5, 5⟩]))
                                                    (.split false ⟨.hat, 1, 5, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨1, some 2, 4⟩, ⟨4, some 5, 5⟩]))
                                                      (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 1, 4⟩, ⟨4, some 5, 5⟩]))))))
                                              (.split false ⟨.spoke, 0, 6, false⟩
                                                (.terminal (.hubcap [⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨4, some 5, 5⟩, ⟨0, some 1, 5⟩, ⟨0, some 2, 6⟩, ⟨1, some 2, 4⟩]))
                                                (.split false ⟨.spoke, 2, 6, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.hat, 3, 5, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.fan1, 0, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.hat, 1, 5, false⟩
                                                        (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 4⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨0, some 1, 4⟩]))
                                                        (.terminal (.hubcap [⟨1, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 4⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨0, some 2, 5⟩]))))))))))))))))))))))))
            (.split false ⟨.spoke, 2, 5, true⟩
              (.similar 0 ⟨true, 2⟩)
              (.split true ⟨.spoke, 1, 5, true⟩
                (.split false ⟨.spoke, 4, 5, false⟩
                  (.split false ⟨.spoke, 0, 6, true⟩
                    (.split false ⟨.spoke, 3, 7, false⟩
                      (.terminal (.hubcap [⟨0, none, 5⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨7, none, 4⟩, ⟨5, some 6, 6⟩]))
                      (.split false ⟨.spoke, 2, 6, true⟩
                        (.split false ⟨.hat, 2, 5, true⟩
                          (.terminal .reducible)
                          (.split false ⟨.spoke, 4, 7, false⟩
                            (.terminal (.hubcap [⟨4, none, 0⟩, ⟨7, none, 4⟩, ⟨0, some 2, 7⟩, ⟨1, some 3, 4⟩, ⟨5, some 6, 5⟩]))
                            (.split false ⟨.spoke, 3, 6, false⟩
                              (.split false ⟨.spoke, 4, 6, false⟩
                                (.terminal (.hubcap [⟨0, none, 5⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨7, none, 4⟩, ⟨5, some 6, 5⟩]))
                                (.split false ⟨.spoke, 5, 6, false⟩
                                  (.terminal (.hubcap [⟨0, none, 5⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 3⟩, ⟨4, none, 0⟩, ⟨7, none, 4⟩, ⟨5, some 6, 4⟩]))
                                  (.terminal (.hubcap [⟨2, none, 1⟩, ⟨4, none, 1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 5, 6⟩, ⟨1, some 3, 4⟩]))))
                              (.split false ⟨.spoke, 5, 7, false⟩
                                (.split false ⟨.spoke, 4, 6, false⟩
                                  (.terminal (.hubcap [⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 4, 4⟩, ⟨0, some 2, 7⟩, ⟨0, some 3, 6⟩, ⟨2, some 3, 4⟩]))
                                  (.split false ⟨.hat, 4, 5, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.hat, 1, 5, false⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨3, some 4, 3⟩]))
                                      (.terminal (.hubcap [⟨0, none, 5⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩])))))
                                (.split false ⟨.hat, 1, 5, true⟩
                                  (.terminal (.hubcap [⟨0, none, 5⟩, ⟨1, none, 3⟩, ⟨4, none, 1⟩, ⟨7, none, 4⟩, ⟨2, some 3, 2⟩, ⟨5, some 6, 5⟩]))
                                  (.split false ⟨.spoke, 5, 6, true⟩
                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, some 3, 4⟩, ⟨4, some 6, 5⟩, ⟨5, some 7, 5⟩]))
                                    (.split false ⟨.spoke, 4, 6, true⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨7, none, 4⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 4⟩]))
                                      (.split false ⟨.hat, 2, 6, true⟩
                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨3, none, 1⟩, ⟨7, none, 4⟩, ⟨2, some 4, 4⟩, ⟨5, some 6, 5⟩]))
                                        (.split false ⟨.hat, 3, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨7, none, 4⟩, ⟨5, some 6, 5⟩]))
                                          (.split false ⟨.hat, 4, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨4, none, 1⟩, ⟨7, none, 4⟩, ⟨2, some 3, 4⟩, ⟨5, some 6, 5⟩]))
                                            (.split false ⟨.fan1, 3, 6, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.hat, 5, 5, false⟩
                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨7, none, 4⟩, ⟨5, some 6, 4⟩]))
                                                (.split false ⟨.hat, 6, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 2⟩]))
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩])))))))))))))))
                        (.split false ⟨.spoke, 4, 7, false⟩
                          (.terminal (.hubcap [⟨0, none, 5⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨7, none, 4⟩, ⟨1, some 2, 6⟩, ⟨5, some 6, 5⟩]))
                          (.split false ⟨.spoke, 3, 6, false⟩
                            (.split false ⟨.spoke, 4, 6, false⟩
                              (.terminal (.hubcap [⟨0, none, 5⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨7, none, 4⟩, ⟨5, some 6, 5⟩]))
                              (.split false ⟨.spoke, 5, 6, false⟩
                                (.terminal (.hubcap [⟨0, none, 5⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨7, none, 4⟩, ⟨5, some 6, 4⟩]))
                                (.split false ⟨.hat, 5, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.hat, 6, 5, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.spoke, 2, 7, false⟩
                                      (.terminal (.hubcap [⟨0, none, 5⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨4, none, 1⟩, ⟨3, some 6, 5⟩, ⟨5, some 7, 6⟩]))
                                      (.split false ⟨.hat, 1, 5, false⟩
                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 1⟩, ⟨3, some 6, 5⟩, ⟨5, some 7, 6⟩]))
                                        (.split false ⟨.fan1, 0, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.hat, 4, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 5⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨7, none, 4⟩, ⟨5, some 6, 5⟩]))
                                            (.split false ⟨.hat, 5, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 5⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨4, none, 0⟩, ⟨3, some 6, 5⟩, ⟨5, some 7, 5⟩]))
                                              (.split false ⟨.fan1, 4, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.hat, 7, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 5⟩, ⟨1, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨2, some 3, 3⟩, ⟨4, some 5, 2⟩]))
                                                  (.split false ⟨.hat, 7, 5, true⟩
                                                    (.terminal (.hubcap [⟨1, none, 3⟩, ⟨3, none, 1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 2, 6⟩, ⟨4, some 5, 2⟩]))
                                                    (.split false ⟨.hat, 0, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.terminal (.hubcap [⟨0, none, 5⟩, ⟨1, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 3⟩, ⟨4, some 5, 3⟩])))))))))))))))
                            (.split false ⟨.spoke, 2, 7, false⟩
                              (.terminal (.hubcap [⟨0, none, 5⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨7, none, 4⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 5⟩]))
                              (.split false ⟨.hat, 1, 5, false⟩
                                (.split false ⟨.spoke, 4, 6, false⟩
                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨3, none, 0⟩, ⟨7, none, 4⟩, ⟨2, some 4, 5⟩, ⟨5, some 6, 5⟩]))
                                  (.split false ⟨.spoke, 5, 6, true⟩
                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨7, none, 4⟩, ⟨5, some 6, 5⟩]))
                                    (.split false ⟨.hat, 2, 5, false⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨7, none, 4⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 4⟩]))
                                      (.split false ⟨.fan1, 2, 5, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.hat, 3, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨7, none, 4⟩, ⟨5, some 6, 4⟩]))
                                          (.split false ⟨.hat, 4, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨7, none, 4⟩, ⟨3, some 4, 2⟩, ⟨5, some 6, 4⟩]))
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨7, none, 4⟩, ⟨5, some 6, 4⟩]))))))))
                                (.split false ⟨.hat, 3, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.fan1, 0, 5, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.spoke, 5, 6, true⟩
                                      (.terminal (.hubcap [⟨0, none, 5⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, some 6, 5⟩, ⟨5, some 7, 5⟩]))
                                      (.split false ⟨.spoke, 4, 6, false⟩
                                        (.split false ⟨.spoke, 5, 7, false⟩
                                          (.terminal (.hubcap [⟨0, none, 5⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                          (.split false ⟨.hat, 2, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 5⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨7, none, 4⟩, ⟨5, some 6, 5⟩]))
                                            (.terminal (.hubcap [⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨7, none, 4⟩, ⟨0, some 6, 8⟩, ⟨4, some 5, 3⟩]))))
                                        (.split false ⟨.spoke, 5, 7, true⟩
                                          (.terminal (.hubcap [⟨0, none, 5⟩, ⟨1, none, 3⟩, ⟨7, none, 4⟩, ⟨5, some 6, 4⟩, ⟨2, some 3, 3⟩, ⟨2, some 4, 3⟩, ⟨3, some 4, 3⟩]))
                                          (.split false ⟨.hat, 2, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 5⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨3, some 4, 3⟩]))
                                            (.terminal (.hubcap [⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨5, none, 0⟩, ⟨7, none, 4⟩, ⟨0, some 6, 8⟩, ⟨3, some 4, 3⟩]))))))))))))))
                    (.split false ⟨.spoke, 0, 7, false⟩
                      (.split false ⟨.spoke, 2, 7, false⟩
                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 5⟩]))
                        (.split false ⟨.spoke, 3, 7, false⟩
                          (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 4⟩, ⟨4, some 5, 5⟩]))
                          (.split false ⟨.spoke, 4, 7, false⟩
                            (.terminal (.hubcap [⟨4, none, 0⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 4⟩, ⟨2, some 3, 5⟩]))
                            (.split false ⟨.hat, 7, 5, false⟩
                              (.split false ⟨.spoke, 4, 6, false⟩
                                (.terminal (.hubcap [⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 1, 4⟩, ⟨2, some 3, 5⟩, ⟨5, some 6, 6⟩]))
                                (.split false ⟨.spoke, 5, 7, false⟩
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 4⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨3, some 4, 5⟩]))
                                  (.split false ⟨.spoke, 5, 6, false⟩
                                    (.split false ⟨.spoke, 2, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 5⟩]))
                                      (.split false ⟨.spoke, 3, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨4, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨3, some 5, 7⟩]))
                                        (.split false ⟨.hat, 1, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 6⟩, ⟨4, some 5, 5⟩]))
                                          (.split false ⟨.hat, 2, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨4, some 5, 5⟩]))
                                            (.split false ⟨.fan1, 2, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.hat, 3, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨4, some 5, 5⟩]))
                                                (.split false ⟨.hat, 4, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨2, none, 4⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 4⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩]))
                                                  (.split false ⟨.hat, 7, 6, true⟩
                                                    (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨2, none, 4⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨3, some 4, 5⟩]))
                                                    (.split false ⟨.hat, 1, 5, false⟩
                                                      (.split false ⟨.spoke, 0, 8, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 6⟩, ⟨4, some 5, 5⟩]))
                                                        (.split false ⟨.hat, 4, 5, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 5⟩]))
                                                          (.split false ⟨.hat, 3, 5, true⟩
                                                            (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩]))
                                                            (.split false ⟨.hat, 5, 6, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 6⟩]))
                                                              (.split false ⟨.hat, 5, 5, true⟩
                                                                (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 5⟩]))
                                                                (.split false ⟨.hat, 6, 5, false⟩
                                                                  (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨2, none, 4⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨3, some 4, 5⟩]))
                                                                  (.split false ⟨.hat, 0, 5, false⟩
                                                                    (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 6⟩]))
                                                                    (.split false ⟨.fan1, 0, 5, true⟩
                                                                      (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 6⟩]))
                                                                      (.split false ⟨.fan1, 2, 6, false⟩
                                                                        (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨2, none, 4⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨3, some 4, 3⟩]))
                                                                        (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩])))))))))))
                                                      (.split false ⟨.fan1, 3, 5, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.spoke, 0, 8, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 7⟩, ⟨4, some 5, 4⟩]))
                                                          (.split false ⟨.fan3, 0, 5, true⟩
                                                            (.terminal .reducible)
                                                            (.split false ⟨.hat, 4, 5, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 6⟩, ⟨4, some 5, 4⟩]))
                                                              (.split false ⟨.fan1, 3, 6, true⟩
                                                                (.terminal .reducible)
                                                                (.split false ⟨.hat, 3, 5, false⟩
                                                                  (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨4, none, 1⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨3, some 5, 6⟩]))
                                                                  (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨2, none, 4⟩, ⟨4, none, 1⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨3, some 5, 5⟩])))))))))))))))))
                                    (.split false ⟨.spoke, 2, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 5⟩]))
                                      (.split false ⟨.hat, 2, 5, false⟩
                                        (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 5⟩]))
                                        (.split false ⟨.fan1, 2, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.hat, 3, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨7, none, 3⟩, ⟨3, some 6, 5⟩, ⟨4, some 5, 5⟩]))
                                            (.split false ⟨.hat, 3, 5, true⟩
                                              (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨2, none, 4⟩, ⟨7, none, 3⟩, ⟨3, some 6, 5⟩, ⟨4, some 5, 4⟩]))
                                              (.split false ⟨.hat, 1, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨7, none, 3⟩, ⟨4, some 5, 5⟩, ⟨2, some 3, 6⟩, ⟨2, some 6, 6⟩, ⟨3, some 6, 7⟩]))
                                                (.split false ⟨.hat, 4, 5, true⟩
                                                  (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨7, none, 3⟩, ⟨4, some 5, 4⟩, ⟨2, some 3, 6⟩, ⟨2, some 6, 6⟩, ⟨3, some 6, 7⟩]))
                                                  (.split false ⟨.spoke, 3, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 5⟩]))
                                                    (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨4, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨3, some 5, 4⟩])))))))))))))
                              (.split false ⟨.hat, 6, 5, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.hat, 0, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.spoke, 5, 7, false⟩
                                    (.terminal (.hubcap [⟨2, none, 4⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 3⟩, ⟨3, some 4, 5⟩]))
                                    (.split false ⟨.spoke, 5, 6, false⟩
                                      (.split false ⟨.spoke, 2, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 4⟩]))
                                        (.split false ⟨.spoke, 3, 6, false⟩
                                          (.terminal (.hubcap [⟨2, none, 3⟩, ⟨4, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 3⟩, ⟨3, some 5, 6⟩]))
                                          (.split false ⟨.spoke, 4, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 3⟩]))
                                            (.split false ⟨.hat, 2, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨3, some 4, 4⟩, ⟨3, some 5, 5⟩, ⟨4, some 5, 4⟩]))
                                              (.split false ⟨.fan1, 2, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.hat, 3, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 4⟩]))
                                                  (.split false ⟨.hat, 4, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨2, none, 4⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                                    (.split false ⟨.hat, 4, 5, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨2, none, 4⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨3, some 4, 3⟩]))
                                                      (.split false ⟨.hat, 3, 5, true⟩
                                                        (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨2, none, 4⟩, ⟨4, none, 1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨3, some 5, 4⟩]))
                                                        (.split false ⟨.hat, 1, 5, true⟩
                                                          (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨4, none, 1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨3, some 5, 5⟩]))
                                                          (.split false ⟨.hat, 5, 6, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 6⟩]))
                                                            (.split false ⟨.hat, 5, 5, true⟩
                                                              (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 5⟩]))
                                                              (.split false ⟨.hat, 6, 6, false⟩
                                                                (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 6⟩]))
                                                                (.split false ⟨.fan1, 2, 6, false⟩
                                                                  (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨2, none, 4⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨3, some 4, 3⟩]))
                                                                  (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 1⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))))))))))))))))
                                      (.split false ⟨.spoke, 2, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 5⟩]))
                                        (.split false ⟨.hat, 3, 6, false⟩
                                          (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 3⟩, ⟨4, some 5, 5⟩]))
                                          (.split false ⟨.hat, 5, 5, false⟩
                                            (.split false ⟨.spoke, 3, 6, false⟩
                                              (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 3⟩, ⟨4, some 5, 4⟩]))
                                              (.split false ⟨.spoke, 4, 6, false⟩
                                                (.terminal (.hubcap [⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 3⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 4⟩]))
                                                (.split false ⟨.hat, 1, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 4⟩]))
                                                  (.split false ⟨.hat, 2, 5, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 4⟩]))
                                                    (.split false ⟨.fan1, 2, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.fan1, 3, 5, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.hat, 4, 5, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨4, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 5⟩]))
                                                          (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 6⟩, ⟨4, some 5, 3⟩])))))))))
                                            (.split false ⟨.spoke, 4, 6, true⟩
                                              (.terminal (.hubcap [⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 3⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 5⟩]))
                                              (.split false ⟨.spoke, 0, 8, false⟩
                                                (.terminal (.hubcap [⟨0, none, 0⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 4, 4⟩, ⟨2, some 3, 5⟩]))
                                                (.split false ⟨.spoke, 3, 6, false⟩
                                                  (.terminal (.hubcap [⟨3, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 3⟩, ⟨2, some 4, 4⟩]))
                                                  (.terminal (.hubcap [⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 3⟩, ⟨2, some 3, 5⟩, ⟨2, some 4, 5⟩, ⟨3, some 4, 3⟩]))))))))))))))))
                      (.split false ⟨.hat, 1, 5, false⟩
                        (.split false ⟨.spoke, 2, 7, false⟩
                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 5⟩]))
                          (.split false ⟨.spoke, 3, 7, false⟩
                            (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨4, some 5, 5⟩]))
                            (.split false ⟨.hat, 0, 5, true⟩
                              (.split false ⟨.hat, 7, 6, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.spoke, 3, 6, false⟩
                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 4⟩]))
                                  (.split false ⟨.spoke, 4, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 4⟩]))
                                    (.split false ⟨.spoke, 5, 7, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩]))
                                      (.split false ⟨.spoke, 5, 6, true⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 4⟩]))
                                        (.split false ⟨.hat, 3, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨4, some 5, 5⟩]))
                                          (.split false ⟨.hat, 4, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 4⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 4⟩]))
                                            (.split false ⟨.hat, 5, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 5⟩]))
                                              (.split false ⟨.hat, 6, 5, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 5⟩]))
                                                (.split false ⟨.fan1, 3, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 4⟩]))
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 4⟩]))))))))))))
                              (.split false ⟨.spoke, 4, 7, false⟩
                                (.terminal (.hubcap [⟨4, none, 0⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 4⟩, ⟨2, some 3, 5⟩]))
                                (.split false ⟨.spoke, 5, 7, false⟩
                                  (.terminal (.hubcap [⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 4⟩, ⟨2, some 3, 6⟩]))
                                  (.split false ⟨.hat, 1, 6, true⟩
                                    (.split false ⟨.hat, 6, 5, true⟩
                                      (.split false ⟨.hat, 7, 6, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.spoke, 2, 6, true⟩
                                          (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 5⟩]))
                                          (.split false ⟨.spoke, 3, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨7, none, 3⟩, ⟨3, some 6, 5⟩, ⟨4, some 5, 5⟩]))
                                            (.split false ⟨.spoke, 4, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩]))
                                              (.split false ⟨.spoke, 5, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 5⟩]))
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 5⟩])))))))
                                      (.split false ⟨.spoke, 4, 6, false⟩
                                        (.terminal (.hubcap [⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 5, 4⟩, ⟨2, some 3, 4⟩]))
                                        (.split false ⟨.hat, 7, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 5⟩]))
                                          (.split false ⟨.hat, 3, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 5, 5⟩, ⟨3, some 4, 3⟩]))
                                            (.split false ⟨.hat, 5, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 3⟩]))
                                              (.split false ⟨.hat, 2, 5, true⟩
                                                (.split false ⟨.spoke, 2, 6, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.spoke, 3, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 4⟩]))
                                                    (.split false ⟨.spoke, 5, 6, true⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 4⟩]))
                                                      (.split false ⟨.hat, 3, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨4, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨3, some 5, 3⟩]))
                                                        (.split false ⟨.hat, 4, 5, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 4⟩]))
                                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩])))))))
                                                (.split false ⟨.hat, 0, 6, false⟩
                                                  (.split false ⟨.spoke, 2, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 5⟩]))
                                                    (.split false ⟨.spoke, 3, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨3, some 4, 4⟩]))
                                                      (.split false ⟨.spoke, 5, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 4⟩]))
                                                        (.split false ⟨.hat, 2, 6, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 4, 4⟩, ⟨3, some 5, 5⟩]))
                                                          (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 5⟩]))))))
                                                  (.split false ⟨.fan2, 0, 5, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.spoke, 2, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 4⟩]))
                                                      (.split false ⟨.spoke, 3, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨3, some 4, 4⟩]))
                                                        (.split false ⟨.hat, 3, 5, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 4⟩]))
                                                          (.split false ⟨.spoke, 5, 6, true⟩
                                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 3⟩]))
                                                            (.split false ⟨.hat, 4, 6, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                                              (.split false ⟨.hat, 4, 5, true⟩
                                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 1⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨3, some 4, 3⟩]))))))))))))))))
                                    (.split false ⟨.hat, 6, 5, true⟩
                                      (.split false ⟨.hat, 7, 6, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.spoke, 2, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨7, none, 3⟩, ⟨3, some 6, 5⟩, ⟨4, some 5, 5⟩]))
                                          (.split false ⟨.spoke, 4, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨2, some 3, 5⟩, ⟨5, some 6, 6⟩]))
                                            (.split false ⟨.spoke, 5, 6, true⟩
                                              (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨3, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨2, some 4, 4⟩, ⟨2, some 5, 6⟩, ⟨4, some 5, 5⟩]))
                                              (.split false ⟨.spoke, 3, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 0⟩, ⟨5, none, 4⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩]))
                                                (.split false ⟨.hat, 2, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨4, some 5, 5⟩]))
                                                  (.split false ⟨.fan1, 2, 5, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.hat, 3, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩]))
                                                      (.split false ⟨.hat, 4, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 5⟩]))
                                                        (.split false ⟨.hat, 3, 5, true⟩
                                                          (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩]))
                                                          (.split false ⟨.hat, 5, 6, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 6⟩]))
                                                            (.split false ⟨.hat, 5, 5, true⟩
                                                              (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 5⟩]))
                                                              (.split false ⟨.hat, 0, 6, false⟩
                                                                (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 6⟩]))
                                                                (.split false ⟨.fan1, 0, 5, false⟩
                                                                  (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 6⟩]))
                                                                  (.split false ⟨.fan2, 0, 5, true⟩
                                                                    (.terminal .reducible)
                                                                    (.split false ⟨.fan1, 2, 6, false⟩
                                                                      (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨2, none, 4⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨3, some 4, 3⟩]))
                                                                      (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩]))))))))))))))))))
                                      (.split false ⟨.hat, 7, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 6⟩, ⟨4, some 5, 4⟩]))
                                        (.split false ⟨.fan2, 0, 5, true⟩
                                          (.split false ⟨.hat, 3, 6, false⟩
                                            (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 3⟩, ⟨4, some 5, 5⟩]))
                                            (.split false ⟨.hat, 7, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 6⟩, ⟨4, some 5, 5⟩]))
                                              (.split false ⟨.spoke, 5, 6, false⟩
                                                (.split false ⟨.spoke, 2, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 4⟩]))
                                                  (.split false ⟨.spoke, 3, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨4, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨3, some 5, 6⟩]))
                                                    (.split false ⟨.spoke, 4, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 3⟩]))
                                                      (.split false ⟨.hat, 2, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 4⟩]))
                                                        (.split false ⟨.hat, 0, 6, true⟩
                                                          (.terminal .reducible)
                                                          (.split false ⟨.fan1, 2, 5, true⟩
                                                            (.terminal .reducible)
                                                            (.split false ⟨.hat, 4, 5, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 4⟩]))
                                                              (.split false ⟨.hat, 3, 5, true⟩
                                                                (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 1⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                                                (.split false ⟨.hat, 5, 6, false⟩
                                                                  (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 6⟩]))
                                                                  (.split false ⟨.hat, 5, 5, true⟩
                                                                    (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 5⟩]))
                                                                    (.split false ⟨.hat, 6, 6, false⟩
                                                                      (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 6⟩]))
                                                                      (.split false ⟨.fan1, 2, 6, false⟩
                                                                        (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨2, none, 4⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨3, some 4, 3⟩]))
                                                                        (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 1⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))))))))))))))
                                                (.split false ⟨.spoke, 2, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 5⟩]))
                                                  (.split false ⟨.spoke, 3, 6, false⟩
                                                    (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 3⟩, ⟨4, some 5, 5⟩]))
                                                    (.split false ⟨.hat, 4, 5, true⟩
                                                      (.terminal (.hubcap [⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 3⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 4⟩]))
                                                      (.split false ⟨.hat, 2, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 5⟩]))
                                                        (.split false ⟨.hat, 0, 6, true⟩
                                                          (.terminal .reducible)
                                                          (.split false ⟨.fan1, 2, 5, true⟩
                                                            (.terminal .reducible)
                                                            (.split false ⟨.spoke, 4, 6, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 4⟩]))
                                                              (.split false ⟨.hat, 3, 5, false⟩
                                                                (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 5⟩]))
                                                                (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨2, none, 4⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩])))))))))))))
                                          (.split false ⟨.spoke, 4, 6, false⟩
                                            (.split false ⟨.spoke, 2, 6, false⟩
                                              (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 5, 3⟩]))
                                              (.split false ⟨.spoke, 3, 6, false⟩
                                                (.terminal (.hubcap [⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 5, 3⟩]))
                                                (.split false ⟨.spoke, 5, 6, false⟩
                                                  (.terminal (.hubcap [⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 4⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 3⟩]))
                                                  (.split false ⟨.hat, 2, 5, false⟩
                                                    (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 5, 3⟩]))
                                                    (.terminal (.hubcap [⟨1, none, 3⟩, ⟨7, none, 4⟩, ⟨0, some 6, 4⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 4⟩]))))))
                                            (.split false ⟨.fan1, 4, 5, true⟩
                                              (.split false ⟨.spoke, 5, 6, false⟩
                                                (.split false ⟨.spoke, 2, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 3⟩]))
                                                  (.split false ⟨.spoke, 3, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨4, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨3, some 5, 5⟩]))
                                                    (.split false ⟨.hat, 2, 5, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 3⟩]))
                                                      (.terminal (.hubcap [⟨1, none, 3⟩, ⟨7, none, 4⟩, ⟨0, some 6, 4⟩, ⟨2, some 3, 6⟩, ⟨4, some 5, 3⟩])))))
                                                (.split false ⟨.spoke, 2, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨4, none, 1⟩, ⟨7, none, 4⟩, ⟨2, some 3, 4⟩, ⟨5, some 6, 7⟩]))
                                                  (.terminal (.hubcap [⟨7, none, 4⟩, ⟨0, some 1, 4⟩, ⟨5, some 6, 7⟩, ⟨2, some 3, 5⟩, ⟨2, some 4, 4⟩, ⟨3, some 4, 2⟩]))))
                                              (.split false ⟨.spoke, 2, 6, false⟩
                                                (.terminal (.hubcap [⟨1, none, 2⟩, ⟨7, none, 4⟩, ⟨0, some 5, 4⟩, ⟨2, some 3, 4⟩, ⟨4, some 6, 6⟩]))
                                                (.split false ⟨.hat, 2, 5, false⟩
                                                  (.split false ⟨.hat, 3, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 5⟩]))
                                                    (.split false ⟨.hat, 4, 6, false⟩
                                                      (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 5, 4⟩, ⟨3, some 4, 3⟩]))
                                                      (.split false ⟨.hat, 5, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 3⟩]))
                                                        (.split false ⟨.hat, 7, 5, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨4, some 5, 4⟩]))
                                                          (.split false ⟨.spoke, 3, 6, false⟩
                                                            (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 5, 4⟩, ⟨3, some 4, 4⟩]))
                                                            (.split false ⟨.hat, 2, 6, true⟩
                                                              (.terminal (.hubcap [⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 5, 4⟩, ⟨2, some 3, 4⟩]))
                                                              (.split false ⟨.hat, 3, 5, false⟩
                                                                (.terminal (.hubcap [⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 5, 4⟩, ⟨2, some 3, 4⟩]))
                                                                (.split false ⟨.hat, 4, 5, false⟩
                                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 5, 5⟩, ⟨3, some 4, 3⟩]))
                                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 3⟩]))))))))))
                                                  (.split false ⟨.fan1, 2, 5, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.hat, 3, 6, false⟩
                                                      (.terminal (.hubcap [⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨7, none, 4⟩, ⟨0, some 6, 4⟩, ⟨4, some 5, 5⟩]))
                                                      (.split false ⟨.hat, 5, 6, false⟩
                                                        (.terminal (.hubcap [⟨1, none, 3⟩, ⟨7, none, 4⟩, ⟨0, some 6, 4⟩, ⟨2, some 3, 6⟩, ⟨4, some 5, 3⟩]))
                                                        (.split false ⟨.hat, 7, 5, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 6⟩, ⟨4, some 5, 4⟩]))
                                                          (.split false ⟨.hat, 0, 6, true⟩
                                                            (.terminal .reducible)
                                                            (.split false ⟨.spoke, 3, 6, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨3, some 4, 4⟩, ⟨3, some 5, 6⟩, ⟨4, some 5, 5⟩]))
                                                              (.split false ⟨.spoke, 5, 6, false⟩
                                                                (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 5⟩]))
                                                                (.split false ⟨.hat, 3, 5, true⟩
                                                                  (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 4⟩]))
                                                                  (.split false ⟨.fan1, 3, 5, true⟩
                                                                    (.terminal .reducible)
                                                                    (.split false ⟨.hat, 4, 5, false⟩
                                                                      (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 5⟩]))
                                                                      (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 3⟩])))))))))))))))))))))))))
                        (.split false ⟨.spoke, 3, 7, false⟩
                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 4⟩]))
                          (.split false ⟨.spoke, 4, 7, false⟩
                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 4⟩]))
                            (.split false ⟨.spoke, 3, 6, false⟩
                              (.split false ⟨.spoke, 2, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 4⟩]))
                                (.split false ⟨.spoke, 5, 7, false⟩
                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 5⟩]))
                                  (.split false ⟨.hat, 5, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨4, none, 0⟩, ⟨6, none, 4⟩, ⟨2, some 3, 5⟩, ⟨5, some 7, 5⟩]))
                                    (.split false ⟨.hat, 0, 5, true⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 3⟩]))
                                      (.split false ⟨.hat, 7, 5, false⟩
                                        (.split false ⟨.spoke, 2, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨7, none, 3⟩, ⟨3, some 6, 5⟩, ⟨4, some 5, 4⟩]))
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨7, none, 3⟩, ⟨3, some 6, 7⟩, ⟨4, some 5, 4⟩])))
                                        (.split false ⟨.hat, 6, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.spoke, 2, 6, false⟩
                                            (.terminal (.hubcap [⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 2, 6⟩, ⟨3, some 4, 2⟩, ⟨3, some 5, 4⟩, ⟨4, some 5, 3⟩]))
                                            (.split false ⟨.hat, 2, 6, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.spoke, 4, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 3⟩]))
                                                (.split false ⟨.hat, 5, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.spoke, 5, 6, false⟩
                                                    (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 4⟩, ⟨4, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 5, 5⟩]))
                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 3⟩])))))))))))))
                              (.split false ⟨.spoke, 5, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 5⟩, ⟨2, some 4, 5⟩, ⟨3, some 4, 3⟩]))
                                (.split false ⟨.spoke, 2, 7, false⟩
                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, some 6, 6⟩, ⟨5, some 7, 6⟩]))
                                  (.split false ⟨.spoke, 5, 6, false⟩
                                    (.split false ⟨.hat, 4, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨4, none, 0⟩, ⟨7, none, 4⟩, ⟨2, some 3, 4⟩, ⟨5, some 6, 6⟩]))
                                      (.split false ⟨.hat, 7, 5, false⟩
                                        (.split false ⟨.spoke, 2, 6, true⟩
                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 3⟩]))
                                          (.split false ⟨.spoke, 4, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨3, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨4, some 5, 4⟩]))
                                            (.split false ⟨.hat, 5, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.hat, 3, 5, false⟩
                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 4, 4⟩, ⟨3, some 5, 4⟩]))
                                                (.split false ⟨.hat, 4, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 4, 5⟩, ⟨3, some 5, 3⟩]))
                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨4, none, 1⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨3, some 5, 4⟩])))))))
                                        (.split false ⟨.hat, 6, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.hat, 0, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.spoke, 2, 6, true⟩
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 3⟩, ⟨4, some 5, 3⟩]))
                                              (.split false ⟨.spoke, 4, 6, false⟩
                                                (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 2, 7⟩, ⟨4, some 5, 3⟩]))
                                                (.split false ⟨.hat, 5, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.hat, 3, 5, false⟩
                                                    (.terminal (.hubcap [⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 2, 6⟩, ⟨0, some 5, 5⟩, ⟨2, some 4, 4⟩, ⟨3, some 4, 3⟩, ⟨3, some 5, 3⟩]))
                                                    (.split false ⟨.hat, 4, 5, false⟩
                                                      (.terminal (.hubcap [⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 5, 5⟩, ⟨2, some 3, 4⟩, ⟨2, some 4, 5⟩, ⟨3, some 4, 2⟩]))
                                                      (.terminal (.hubcap [⟨1, none, 2⟩, ⟨4, none, 1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 2, 6⟩, ⟨3, some 5, 3⟩])))))))))))
                                    (.split false ⟨.spoke, 2, 6, true⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, 4⟩, ⟨2, some 3, 3⟩, ⟨5, some 7, 5⟩]))
                                      (.split false ⟨.hat, 6, 5, true⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨3, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨4, some 5, 4⟩]))
                                        (.split false ⟨.hat, 7, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 4⟩]))
                                          (.split false ⟨.hat, 0, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.spoke, 4, 6, false⟩
                                              (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨7, none, 4⟩, ⟨0, some 2, 7⟩, ⟨5, some 6, 5⟩]))
                                              (.split false ⟨.hat, 5, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.hat, 3, 6, false⟩
                                                  (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 1⟩, ⟨0, some 2, 5⟩, ⟨4, some 6, 6⟩, ⟨5, some 7, 6⟩]))
                                                  (.split false ⟨.hat, 4, 5, false⟩
                                                    (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨7, none, 4⟩, ⟨0, some 2, 7⟩, ⟨5, some 6, 6⟩]))
                                                    (.split false ⟨.fan1, 4, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.hat, 5, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨3, none, 1⟩, ⟨7, none, 4⟩, ⟨2, some 4, 4⟩, ⟨5, some 6, 5⟩]))
                                                        (.split false ⟨.hat, 6, 6, true⟩
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨4, some 5, 5⟩]))
                                                          (.split false ⟨.hat, 3, 5, true⟩
                                                            (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 2, 6⟩, ⟨4, some 5, 3⟩]))
                                                            (.split false ⟨.hat, 2, 5, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                                              (.split false ⟨.hat, 7, 5, false⟩
                                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩]))
                                                                (.split false ⟨.fan1, 0, 5, true⟩
                                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                                                  (.split false ⟨.fan1, 2, 5, false⟩
                                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 3⟩])))))))))))))))))))))))))))
                  (.split true ⟨.spoke, 2, 6, false⟩
                    (.split false ⟨.spoke, 3, 6, false⟩
                      (.split false ⟨.hat, 7, 5, false⟩
                        (.split false ⟨.spoke, 2, 7, false⟩
                          (.terminal (.hubcap [⟨2, none, 0⟩, ⟨0, some 5, 7⟩, ⟨6, some 7, 7⟩, ⟨1, some 3, 4⟩, ⟨1, some 4, 5⟩, ⟨3, some 4, 4⟩]))
                          (.split false ⟨.spoke, 3, 7, false⟩
                            (.terminal (.hubcap [⟨3, none, 0⟩, ⟨0, some 5, 7⟩, ⟨6, some 7, 7⟩, ⟨1, some 2, 4⟩, ⟨1, some 4, 5⟩, ⟨2, some 4, 4⟩]))
                            (.split false ⟨.hat, 3, 5, true⟩
                              (.split false ⟨.spoke, 0, 6, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.spoke, 5, 6, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.spoke, 0, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 4⟩]))
                                    (.split false ⟨.spoke, 5, 7, false⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 4⟩]))
                                      (.split false ⟨.hat, 1, 5, true⟩
                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 3⟩]))
                                        (.split false ⟨.hat, 2, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 3⟩]))
                                          (.split false ⟨.hat, 1, 6, true⟩
                                            (.terminal (.hubcap [⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 5, 6⟩, ⟨2, some 3, 4⟩]))
                                            (.split false ⟨.hat, 4, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 3⟩]))
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 4⟩]))))))))))
                              (.split false ⟨.spoke, 5, 7, false⟩
                                (.terminal (.hubcap [⟨4, none, 2⟩, ⟨6, none, 3⟩, ⟨0, some 5, 6⟩, ⟨1, some 2, 4⟩, ⟨3, some 7, 5⟩]))
                                (.split false ⟨.spoke, 0, 7, false⟩
                                  (.terminal (.hubcap [⟨1, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 5, 6⟩, ⟨2, some 4, 4⟩, ⟨3, some 6, 5⟩]))
                                  (.split true ⟨.spoke, 0, 6, false⟩
                                    (.split false ⟨.hat, 1, 5, true⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 3⟩]))
                                      (.split false ⟨.hat, 2, 6, false⟩
                                        (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨0, some 5, 7⟩, ⟨3, some 4, 4⟩]))
                                        (.split false ⟨.hat, 2, 5, true⟩
                                          (.terminal (.hubcap [⟨1, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 6, 6⟩, ⟨2, some 4, 4⟩, ⟨3, some 5, 5⟩]))
                                          (.split false ⟨.spoke, 5, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩]))
                                            (.split false ⟨.hat, 1, 6, false⟩
                                              (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨0, some 5, 6⟩]))
                                              (.split false ⟨.hat, 4, 5, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 0⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩]))
                                                (.split false ⟨.fan2, 3, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.hat, 5, 5, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩]))
                                                    (.split false ⟨.fan1, 5, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.hat, 6, 5, false⟩
                                                        (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 5, 7⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨5, none, 5⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩]))))))))))))
                                    (.split false ⟨.spoke, 5, 6, false⟩
                                      (.similar 0 ⟨true, 2⟩)
                                      (.terminal .reducible))))))))
                        (.split false ⟨.hat, 6, 5, true⟩
                          (.terminal .reducible)
                          (.split false ⟨.hat, 0, 5, true⟩
                            (.terminal .reducible)
                            (.split false ⟨.spoke, 2, 7, false⟩
                              (.terminal (.hubcap [⟨2, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 5, 6⟩, ⟨1, some 3, 4⟩, ⟨1, some 4, 5⟩, ⟨3, some 4, 4⟩]))
                              (.split false ⟨.spoke, 3, 7, false⟩
                                (.terminal (.hubcap [⟨3, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 5, 6⟩, ⟨1, some 2, 4⟩, ⟨1, some 4, 5⟩, ⟨2, some 4, 4⟩]))
                                (.split false ⟨.hat, 3, 5, true⟩
                                  (.split false ⟨.spoke, 0, 6, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.spoke, 5, 6, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.spoke, 0, 8, false⟩
                                        (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 4⟩]))
                                        (.split false ⟨.spoke, 5, 8, false⟩
                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 4⟩]))
                                          (.split false ⟨.hat, 2, 5, false⟩
                                            (.terminal (.hubcap [⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 5, 5⟩, ⟨2, some 3, 3⟩]))
                                            (.split false ⟨.spoke, 5, 7, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 4⟩]))
                                              (.split false ⟨.hat, 4, 5, false⟩
                                                (.terminal (.hubcap [⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 5, 5⟩, ⟨2, some 3, 3⟩]))
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 4⟩])))))))))
                                  (.split false ⟨.spoke, 5, 7, false⟩
                                    (.terminal (.hubcap [⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 2, 5⟩, ⟨1, some 3, 4⟩]))
                                    (.split false ⟨.spoke, 0, 7, false⟩
                                      (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 4, 4⟩, ⟨3, some 5, 5⟩]))
                                      (.split false ⟨.hat, 2, 6, false⟩
                                        (.terminal (.hubcap [⟨2, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 5, 6⟩, ⟨1, some 3, 4⟩, ⟨1, some 4, 5⟩, ⟨3, some 4, 4⟩]))
                                        (.split false ⟨.hat, 4, 6, false⟩
                                          (.terminal (.hubcap [⟨3, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 5, 6⟩, ⟨1, some 2, 4⟩, ⟨1, some 4, 5⟩, ⟨2, some 4, 4⟩]))
                                          (.split true ⟨.hat, 2, 5, false⟩
                                            (.split false ⟨.spoke, 0, 6, true⟩
                                              (.terminal (.hubcap [⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 5, 6⟩]))
                                              (.split false ⟨.spoke, 5, 6, false⟩
                                                (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 5, 5⟩]))
                                                (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨4, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨3, some 5, 5⟩]))))
                                            (.split false ⟨.hat, 4, 5, false⟩
                                              (.similar 0 ⟨true, 2⟩)
                                              (.split false ⟨.hat, 1, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.hat, 5, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.spoke, 5, 6, true⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                                    (.split false ⟨.spoke, 0, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))))))))))))))))))
                      (.split false ⟨.spoke, 5, 6, true⟩
                        (.split false ⟨.spoke, 0, 6, true⟩
                          (.terminal .reducible)
                          (.split false ⟨.hat, 4, 5, true⟩
                            (.terminal .reducible)
                            (.split false ⟨.spoke, 0, 8, false⟩
                              (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 5, 6⟩]))
                              (.split false ⟨.spoke, 2, 7, false⟩
                                (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 5, 6⟩]))
                                (.split false ⟨.hat, 2, 5, true⟩
                                  (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨6, none, 4⟩, ⟨0, some 5, 5⟩, ⟨2, some 7, 6⟩]))
                                  (.split false ⟨.spoke, 0, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 5, 5⟩]))
                                    (.split false ⟨.hat, 1, 5, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.hat, 1, 6, false⟩
                                        (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 5, 5⟩, ⟨2, some 4, 4⟩]))
                                        (.split false ⟨.hat, 3, 5, false⟩
                                          (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 5, 6⟩, ⟨2, some 4, 3⟩]))
                                          (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩])))))))))))
                        (.split false ⟨.hat, 4, 6, false⟩
                          (.split false ⟨.spoke, 0, 8, false⟩
                            (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 5, 7⟩]))
                            (.split false ⟨.spoke, 5, 8, false⟩
                              (.terminal (.hubcap [⟨1, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 2, 6⟩]))
                              (.split false ⟨.hat, 7, 5, false⟩
                                (.split false ⟨.spoke, 0, 7, false⟩
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 5, 7⟩]))
                                  (.split false ⟨.spoke, 2, 7, false⟩
                                    (.terminal (.hubcap [⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨0, some 5, 7⟩]))
                                    (.split false ⟨.spoke, 5, 7, false⟩
                                      (.terminal (.hubcap [⟨1, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨0, some 2, 6⟩]))
                                      (.split false ⟨.spoke, 0, 6, true⟩
                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨6, none, 3⟩, ⟨1, some 2, 4⟩, ⟨5, some 7, 6⟩]))
                                        (.split false ⟨.hat, 1, 5, true⟩
                                          (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 2, 6⟩]))
                                          (.split false ⟨.hat, 2, 5, false⟩
                                            (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 2, 4⟩]))
                                            (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 2, 6⟩]))))))))
                                (.split false ⟨.hat, 6, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.hat, 0, 5, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.spoke, 0, 6, false⟩
                                      (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 2, 5⟩, ⟨0, some 5, 5⟩, ⟨2, some 5, 5⟩]))
                                      (.terminal (.hubcap [⟨0, none, 5⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 2, 3⟩]))))))))
                          (.split false ⟨.fan1, 3, 5, true⟩
                            (.terminal .reducible)
                            (.split false ⟨.spoke, 0, 8, false⟩
                              (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨4, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨3, some 5, 4⟩]))
                              (.split false ⟨.hat, 7, 5, true⟩
                                (.split false ⟨.hat, 6, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.hat, 0, 5, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.spoke, 0, 7, false⟩
                                      (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨4, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨3, some 5, 3⟩]))
                                      (.split false ⟨.spoke, 0, 6, true⟩
                                        (.terminal (.hubcap [⟨0, none, 5⟩, ⟨4, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 2, 3⟩, ⟨3, some 5, 2⟩]))
                                        (.split false ⟨.spoke, 2, 7, false⟩
                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨4, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨3, some 5, 3⟩]))
                                          (.split false ⟨.hat, 3, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.hat, 1, 5, true⟩
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨4, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨3, some 5, 3⟩]))
                                              (.split false ⟨.spoke, 5, 7, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 5⟩]))
                                                (.split false ⟨.hat, 5, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.hat, 2, 5, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                                    (.split false ⟨.hat, 3, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 4⟩]))
                                                      (.split false ⟨.fan2, 2, 5, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.hat, 4, 5, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩])))))))))))))))
                                (.split false ⟨.spoke, 5, 8, false⟩
                                  (.terminal (.hubcap [⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨0, some 2, 6⟩, ⟨1, some 3, 5⟩, ⟨4, some 7, 6⟩]))
                                  (.split false ⟨.spoke, 0, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨4, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨3, some 5, 4⟩]))
                                    (.split false ⟨.spoke, 5, 7, false⟩
                                      (.split false ⟨.spoke, 2, 7, false⟩
                                        (.terminal (.hubcap [⟨0, none, 5⟩, ⟨2, none, 0⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩, ⟨1, some 3, 5⟩, ⟨4, some 7, 6⟩]))
                                        (.split false ⟨.spoke, 0, 6, true⟩
                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨1, some 2, 4⟩]))
                                          (.split false ⟨.hat, 1, 5, true⟩
                                            (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 2, 5⟩]))
                                            (.split false ⟨.hat, 2, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩]))
                                              (.split false ⟨.hat, 3, 5, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 5⟩]))
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩])))))))
                                      (.split false ⟨.hat, 5, 5, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.spoke, 2, 7, false⟩
                                          (.terminal (.hubcap [⟨2, none, 0⟩, ⟨6, none, 3⟩, ⟨0, some 3, 6⟩, ⟨1, some 4, 5⟩, ⟨5, some 7, 6⟩]))
                                          (.split false ⟨.spoke, 0, 6, true⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨6, none, 3⟩, ⟨1, some 2, 4⟩, ⟨5, some 7, 6⟩]))
                                            (.split false ⟨.hat, 1, 5, true⟩
                                              (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 2, 5⟩, ⟨4, some 5, 5⟩]))
                                              (.split false ⟨.hat, 2, 5, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨4, some 5, 5⟩]))
                                                (.split false ⟨.hat, 3, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨4, some 5, 5⟩]))
                                                  (.split false ⟨.hat, 3, 5, true⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨4, some 5, 5⟩]))
                                                    (.split false ⟨.hat, 4, 5, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩]))
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩])))))))))))))))))))
                    (.split false ⟨.spoke, 3, 6, false⟩
                      (.similar 0 ⟨true, 2⟩)
                      (.split false ⟨.spoke, 0, 6, true⟩
                        (.terminal .reducible)
                        (.split false ⟨.spoke, 5, 6, true⟩
                          (.terminal .reducible)
                          (.split true ⟨.hat, 2, 5, false⟩
                            (.split false ⟨.hat, 0, 5, true⟩
                              (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨4, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨3, some 5, 5⟩]))
                              (.split true ⟨.hat, 4, 6, false⟩
                                (.split false ⟨.spoke, 0, 8, false⟩
                                  (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 5⟩, ⟨2, some 5, 6⟩, ⟨3, some 5, 6⟩]))
                                  (.split false ⟨.spoke, 5, 8, false⟩
                                    (.terminal (.hubcap [⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 2, 6⟩, ⟨0, some 3, 6⟩, ⟨2, some 3, 5⟩]))
                                    (.split false ⟨.hat, 3, 6, false⟩
                                      (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 5, 5⟩]))
                                      (.split false ⟨.hat, 3, 5, true⟩
                                        (.terminal (.hubcap [⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 5, 3⟩, ⟨2, some 3, 5⟩]))
                                        (.split false ⟨.spoke, 0, 7, true⟩
                                          (.terminal (.hubcap [⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 5, 5⟩, ⟨2, some 3, 3⟩]))
                                          (.split false ⟨.spoke, 5, 7, false⟩
                                            (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                            (.split false ⟨.hat, 6, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.hat, 1, 5, false⟩
                                                (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                                (.split false ⟨.hat, 2, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 3⟩]))
                                                  (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩])))))))))))
                                (.split false ⟨.fan1, 3, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.spoke, 0, 8, false⟩
                                    (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, some 5, 5⟩, ⟨3, some 6, 7⟩, ⟨4, some 7, 6⟩]))
                                    (.split false ⟨.spoke, 0, 7, false⟩
                                      (.split false ⟨.spoke, 5, 7, false⟩
                                        (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨2, some 3, 7⟩, ⟨4, some 6, 6⟩, ⟨5, some 7, 4⟩]))
                                        (.split false ⟨.hat, 5, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.hat, 6, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.hat, 1, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨7, none, 4⟩, ⟨3, some 5, 5⟩, ⟨4, some 6, 6⟩]))
                                              (.split false ⟨.hat, 2, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨2, some 5, 4⟩, ⟨3, some 6, 7⟩, ⟨4, some 7, 6⟩]))
                                                (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨7, none, 4⟩, ⟨3, some 5, 4⟩, ⟨4, some 6, 6⟩])))))))
                                      (.split false ⟨.spoke, 5, 8, false⟩
                                        (.terminal (.hubcap [⟨1, none, 2⟩, ⟨5, none, 0⟩, ⟨0, some 3, 6⟩, ⟨2, some 6, 6⟩, ⟨4, some 7, 6⟩]))
                                        (.split false ⟨.hat, 1, 5, false⟩
                                          (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, some 6, 7⟩, ⟨4, some 7, 6⟩, ⟨0, some 2, 4⟩, ⟨0, some 5, 3⟩, ⟨2, some 5, 4⟩]))
                                          (.split false ⟨.hat, 2, 6, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.hat, 3, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.fan2, 0, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.hat, 4, 5, false⟩
                                                  (.similar 0 ⟨true, 2⟩)
                                                  (.split false ⟨.hat, 7, 5, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.spoke, 5, 7, true⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 5⟩]))
                                                      (.split false ⟨.hat, 3, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩]))
                                                        (.split false ⟨.hat, 5, 5, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 5⟩]))
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩])))))))))))))))))
                            (.split false ⟨.hat, 4, 5, false⟩
                              (.similar 0 ⟨true, 2⟩)
                              (.split false ⟨.hat, 7, 5, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.fan1, 2, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.fan1, 3, 5, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.hat, 3, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩]))
                                      (.split false ⟨.hat, 3, 5, true⟩
                                        (.terminal (.hubcap [⟨1, none, 3⟩, ⟨4, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 2, 4⟩, ⟨3, some 5, 4⟩]))
                                        (.split false ⟨.spoke, 5, 8, false⟩
                                          (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 7⟩]))
                                          (.split false ⟨.spoke, 0, 8, false⟩
                                            (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 7⟩]))
                                            (.split false ⟨.hat, 1, 5, true⟩
                                              (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩]))
                                              (.split false ⟨.spoke, 5, 7, true⟩
                                                (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 6⟩]))
                                                (.split false ⟨.hat, 5, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 6⟩]))
                                                  (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨2, none, 4⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩])))))))))))))))))))
                (.split false ⟨.spoke, 4, 5, true⟩
                  (.similar 0 ⟨true, 2⟩)
                  (.split false ⟨.spoke, 1, 7, false⟩
                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 5⟩]))
                    (.split false ⟨.spoke, 2, 7, false⟩
                      (.terminal (.hubcap [⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨4, some 5, 5⟩]))
                      (.split false ⟨.spoke, 3, 7, false⟩
                        (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨4, some 5, 5⟩]))
                        (.split false ⟨.spoke, 4, 7, false⟩
                          (.terminal (.hubcap [⟨4, none, 0⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨2, some 3, 4⟩]))
                          (.split true ⟨.spoke, 0, 7, false⟩
                            (.split false ⟨.spoke, 1, 6, false⟩
                              (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 5⟩]))
                              (.terminal (.hubcap [⟨0, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 5⟩, ⟨1, some 2, 4⟩, ⟨1, some 3, 5⟩, ⟨2, some 3, 6⟩])))
                            (.split false ⟨.spoke, 5, 7, false⟩
                              (.similar 0 ⟨true, 2⟩)
                              (.split true ⟨.spoke, 1, 6, false⟩
                                (.split false ⟨.hat, 3, 6, false⟩
                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 5⟩]))
                                  (.split false ⟨.hat, 0, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 5⟩]))
                                    (.split false ⟨.hat, 6, 5, true⟩
                                      (.split false ⟨.hat, 7, 6, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.spoke, 0, 6, false⟩
                                          (.terminal (.hubcap [⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨0, some 1, 4⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 5⟩]))
                                          (.split false ⟨.fan1, 0, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.spoke, 2, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨7, none, 4⟩, ⟨3, some 6, 5⟩, ⟨4, some 5, 5⟩]))
                                              (.split false ⟨.spoke, 3, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨7, none, 4⟩, ⟨3, some 6, 7⟩, ⟨4, some 5, 5⟩]))
                                                (.split false ⟨.spoke, 4, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨7, none, 4⟩, ⟨5, some 6, 6⟩]))
                                                  (.split false ⟨.spoke, 5, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 5⟩]))
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨3, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 4, 2⟩])))))))))
                                      (.split false ⟨.hat, 7, 5, false⟩
                                        (.terminal (.hubcap [⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨0, some 1, 4⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 5⟩]))
                                        (.split false ⟨.hat, 0, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.spoke, 0, 6, false⟩
                                            (.terminal (.hubcap [⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 3⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 5⟩]))
                                            (.split false ⟨.fan1, 0, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.spoke, 4, 6, false⟩
                                                (.split false ⟨.spoke, 2, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                                  (.split false ⟨.spoke, 3, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                                    (.split false ⟨.spoke, 5, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 3⟩]))
                                                      (.split false ⟨.hat, 1, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 3⟩]))
                                                        (.split false ⟨.hat, 2, 5, true⟩
                                                          (.terminal .reducible)
                                                          (.split false ⟨.fan1, 0, 6, true⟩
                                                            (.terminal .reducible)
                                                            (.split false ⟨.hat, 3, 5, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 2⟩]))
                                                              (.split false ⟨.fan1, 3, 5, true⟩
                                                                (.terminal .reducible)
                                                                (.split false ⟨.hat, 4, 6, false⟩
                                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨3, some 4, 3⟩]))
                                                                  (.split false ⟨.hat, 4, 5, true⟩
                                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                                                    (.split false ⟨.hat, 5, 5, false⟩
                                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 4⟩]))
                                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩])))))))))))))
                                                (.split false ⟨.spoke, 3, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨3, some 4, 4⟩, ⟨3, some 5, 7⟩, ⟨4, some 5, 4⟩]))
                                                  (.split false ⟨.spoke, 2, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨3, some 5, 3⟩]))
                                                    (.split false ⟨.hat, 1, 5, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 4⟩]))
                                                      (.split false ⟨.hat, 2, 5, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.fan1, 0, 6, true⟩
                                                          (.terminal .reducible)
                                                          (.split false ⟨.hat, 3, 5, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 3⟩, ⟨4, some 5, 4⟩]))
                                                            (.split false ⟨.fan1, 3, 5, true⟩
                                                              (.terminal .reducible)
                                                              (.split false ⟨.spoke, 5, 6, false⟩
                                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 3⟩]))
                                                                (.split false ⟨.hat, 5, 5, true⟩
                                                                  (.terminal .reducible)
                                                                  (.split false ⟨.hat, 4, 5, false⟩
                                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 3⟩]))))))))))))))))))))
                                (.split false ⟨.spoke, 4, 6, false⟩
                                  (.similar 0 ⟨true, 2⟩)
                                  (.split true ⟨.hat, 2, 6, false⟩
                                    (.split false ⟨.spoke, 0, 6, false⟩
                                      (.terminal (.hubcap [⟨1, none, 0⟩, ⟨6, none, 4⟩, ⟨0, some 7, 7⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 5⟩]))
                                      (.split false ⟨.hat, 1, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 5⟩]))
                                        (.split false ⟨.hat, 3, 6, false⟩
                                          (.terminal (.hubcap [⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨4, some 5, 5⟩]))
                                          (.split false ⟨.fan1, 0, 5, true⟩
                                            (.split false ⟨.hat, 0, 6, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.fan1, 1, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.hat, 1, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 5⟩]))
                                                  (.split false ⟨.hat, 4, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 2⟩]))
                                                    (.split false ⟨.hat, 5, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨3, some 4, 4⟩]))
                                                      (.split false ⟨.hat, 6, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 4⟩]))
                                                        (.split false ⟨.hat, 6, 5, true⟩
                                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 5⟩]))
                                                          (.split false ⟨.spoke, 5, 6, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 4⟩]))
                                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 5⟩]))))))))))
                                            (.split false ⟨.fan1, 0, 6, true⟩
                                              (.split false ⟨.hat, 4, 6, false⟩
                                                (.terminal (.hubcap [⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 4⟩, ⟨2, some 3, 3⟩, ⟨4, some 5, 5⟩]))
                                                (.split false ⟨.hat, 5, 6, false⟩
                                                  (.terminal (.hubcap [⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 4⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 4⟩]))
                                                  (.split false ⟨.hat, 6, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨7, none, 4⟩, ⟨1, some 6, 5⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 4⟩]))
                                                    (.split false ⟨.spoke, 3, 6, false⟩
                                                      (.terminal (.hubcap [⟨2, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 4⟩, ⟨3, some 4, 5⟩, ⟨3, some 5, 7⟩, ⟨4, some 5, 5⟩]))
                                                      (.split false ⟨.hat, 3, 5, false⟩
                                                        (.terminal (.hubcap [⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 4⟩, ⟨2, some 3, 3⟩, ⟨4, some 5, 5⟩]))
                                                        (.split false ⟨.spoke, 2, 6, false⟩
                                                          (.terminal (.hubcap [⟨2, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 4⟩, ⟨3, some 4, 3⟩, ⟨3, some 5, 5⟩, ⟨4, some 5, 5⟩]))
                                                          (.split false ⟨.hat, 1, 5, true⟩
                                                            (.terminal .reducible)
                                                            (.split false ⟨.hat, 0, 5, true⟩
                                                              (.terminal .reducible)
                                                              (.split false ⟨.spoke, 5, 6, true⟩
                                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 4⟩]))
                                                                (.split false ⟨.hat, 4, 5, false⟩
                                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨7, none, 4⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 7⟩]))
                                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 3⟩, ⟨4, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))))))))))))
                                              (.split false ⟨.hat, 1, 5, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 5⟩]))
                                                (.split false ⟨.hat, 4, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 2⟩, ⟨4, some 5, 5⟩]))
                                                  (.split false ⟨.fan1, 4, 5, true⟩
                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 5, 4⟩, ⟨3, some 4, 3⟩]))
                                                    (.split false ⟨.spoke, 3, 6, false⟩
                                                      (.split false ⟨.spoke, 2, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨7, none, 4⟩, ⟨5, some 6, 7⟩]))
                                                        (.split false ⟨.spoke, 5, 6, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨3, none, 4⟩, ⟨4, none, 0⟩, ⟨7, none, 4⟩, ⟨5, some 6, 7⟩]))
                                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨7, none, 4⟩, ⟨3, some 6, 7⟩, ⟨4, some 5, 4⟩]))))
                                                      (.split false ⟨.hat, 4, 5, true⟩
                                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 1⟩, ⟨3, none, 1⟩, ⟨7, none, 4⟩, ⟨2, some 4, 4⟩, ⟨5, some 6, 6⟩]))
                                                        (.split false ⟨.spoke, 5, 6, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨7, none, 4⟩, ⟨3, some 4, 2⟩, ⟨5, some 6, 7⟩]))
                                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 4⟩])))))))))))))
                                    (.split false ⟨.hat, 4, 6, false⟩
                                      (.similar 0 ⟨true, 2⟩)
                                      (.split false ⟨.fan1, 1, 5, true⟩
                                        (.split false ⟨.spoke, 2, 6, true⟩
                                          (.split false ⟨.spoke, 0, 6, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.hat, 1, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.fan1, 2, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.spoke, 3, 6, true⟩
                                                  (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 3⟩, ⟨6, none, 4⟩, ⟨0, some 7, 5⟩, ⟨3, some 4, 4⟩, ⟨3, some 5, 6⟩, ⟨4, some 5, 5⟩]))
                                                  (.split false ⟨.spoke, 5, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 0⟩, ⟨7, none, 4⟩, ⟨5, some 6, 7⟩]))
                                                    (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨0, some 7, 5⟩, ⟨3, some 6, 7⟩, ⟨4, some 5, 5⟩])))))))
                                          (.split false ⟨.spoke, 5, 6, false⟩
                                            (.terminal (.hubcap [⟨7, none, 4⟩, ⟨0, some 6, 7⟩, ⟨1, some 2, 3⟩, ⟨3, some 4, 3⟩, ⟨3, some 5, 5⟩, ⟨4, some 5, 5⟩]))
                                            (.split false ⟨.spoke, 0, 6, false⟩
                                              (.terminal (.hubcap [⟨1, none, 0⟩, ⟨7, none, 4⟩, ⟨0, some 2, 6⟩, ⟨3, some 6, 5⟩, ⟨4, some 5, 5⟩]))
                                              (.split false ⟨.spoke, 3, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 1⟩, ⟨2, some 7, 5⟩, ⟨3, some 6, 5⟩, ⟨4, some 5, 5⟩]))
                                                (.split false ⟨.fan1, 4, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.hat, 1, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 5⟩]))
                                                    (.split false ⟨.fan1, 0, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.hat, 3, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 2, 2⟩, ⟨4, some 5, 5⟩]))
                                                        (.split false ⟨.fan1, 3, 6, true⟩
                                                          (.terminal .reducible)
                                                          (.split false ⟨.hat, 1, 5, true⟩
                                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 4⟩]))
                                                            (.split false ⟨.hat, 2, 5, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                                              (.split false ⟨.hat, 4, 5, true⟩
                                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨7, none, 4⟩, ⟨5, some 6, 6⟩]))
                                                                (.split false ⟨.hat, 5, 5, false⟩
                                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                                                  (.split false ⟨.hat, 6, 5, false⟩
                                                                    (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨7, none, 4⟩, ⟨0, some 6, 7⟩, ⟨4, some 5, 5⟩]))
                                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))))))))))))))))
                                        (.split true ⟨.spoke, 5, 6, false⟩
                                          (.split false ⟨.hat, 4, 5, true⟩
                                            (.split false ⟨.spoke, 3, 6, false⟩
                                              (.terminal (.hubcap [⟨4, none, 0⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨2, some 3, 5⟩, ⟨5, some 6, 6⟩]))
                                              (.split false ⟨.hat, 3, 6, false⟩
                                                (.terminal (.hubcap [⟨2, none, 2⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 6⟩]))
                                                (.split false ⟨.fan1, 3, 5, true⟩
                                                  (.split false ⟨.hat, 3, 5, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.fan1, 4, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.spoke, 0, 6, false⟩
                                                        (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨7, none, 4⟩, ⟨0, some 1, 4⟩, ⟨5, some 6, 6⟩]))
                                                        (.split false ⟨.spoke, 2, 6, false⟩
                                                          (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨5, some 6, 6⟩]))
                                                          (.split false ⟨.fan1, 2, 5, true⟩
                                                            (.terminal .reducible)
                                                            (.split false ⟨.hat, 1, 5, false⟩
                                                              (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨7, none, 4⟩, ⟨0, some 1, 4⟩, ⟨5, some 6, 6⟩]))
                                                              (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨5, some 6, 6⟩]))))))))
                                                  (.split false ⟨.fan1, 3, 6, true⟩
                                                    (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨5, some 6, 6⟩]))
                                                    (.split false ⟨.fan1, 4, 5, false⟩
                                                      (.split false ⟨.spoke, 2, 6, true⟩
                                                        (.terminal (.hubcap [⟨4, none, 1⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨2, some 3, 4⟩, ⟨5, some 6, 6⟩]))
                                                        (.split false ⟨.spoke, 0, 6, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨2, none, 4⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨7, none, 4⟩, ⟨5, some 6, 6⟩]))
                                                          (.terminal (.hubcap [⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨0, some 1, 5⟩, ⟨2, some 7, 7⟩, ⟨5, some 6, 6⟩]))))
                                                      (.split false ⟨.hat, 5, 5, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.spoke, 2, 6, true⟩
                                                          (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 1⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨5, some 6, 5⟩]))
                                                          (.split false ⟨.spoke, 0, 6, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨2, none, 4⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨7, none, 4⟩, ⟨5, some 6, 5⟩]))
                                                            (.terminal (.hubcap [⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨0, some 1, 5⟩, ⟨2, some 7, 7⟩, ⟨5, some 6, 5⟩]))))))))))
                                            (.split false ⟨.spoke, 3, 6, false⟩
                                              (.split false ⟨.spoke, 0, 6, false⟩
                                                (.terminal (.hubcap [⟨4, none, 0⟩, ⟨0, some 6, 7⟩, ⟨5, some 7, 7⟩, ⟨1, some 2, 3⟩, ⟨1, some 3, 5⟩, ⟨2, some 3, 5⟩]))
                                                (.split false ⟨.spoke, 2, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 0⟩, ⟨7, none, 4⟩, ⟨5, some 6, 7⟩]))
                                                  (.split false ⟨.hat, 1, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 1⟩, ⟨4, none, 0⟩, ⟨7, none, 4⟩, ⟨1, some 3, 5⟩, ⟨5, some 6, 7⟩]))
                                                    (.split false ⟨.hat, 1, 5, true⟩
                                                      (.terminal (.hubcap [⟨4, none, 0⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨2, some 3, 4⟩, ⟨5, some 6, 7⟩]))
                                                      (.split false ⟨.hat, 2, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 4⟩, ⟨4, none, 0⟩, ⟨7, none, 4⟩, ⟨5, some 6, 7⟩]))
                                                        (.terminal (.hubcap [⟨2, none, 1⟩, ⟨4, none, 0⟩, ⟨0, some 6, 6⟩, ⟨1, some 3, 6⟩, ⟨5, some 7, 7⟩])))))))
                                              (.split false ⟨.hat, 3, 6, false⟩
                                                (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨5, some 6, 7⟩]))
                                                (.split false ⟨.hat, 5, 6, false⟩
                                                  (.terminal (.hubcap [⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨5, some 6, 5⟩, ⟨2, some 3, 5⟩, ⟨2, some 4, 5⟩, ⟨3, some 4, 3⟩]))
                                                  (.split false ⟨.fan1, 4, 5, true⟩
                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨4, none, 0⟩, ⟨7, none, 4⟩, ⟨2, some 3, 5⟩, ⟨5, some 6, 5⟩]))
                                                    (.split false ⟨.hat, 7, 5, true⟩
                                                      (.split false ⟨.hat, 6, 5, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.hat, 0, 5, true⟩
                                                          (.terminal .reducible)
                                                          (.split false ⟨.spoke, 0, 6, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 2, 4⟩, ⟨3, some 4, 3⟩]))
                                                            (.split false ⟨.spoke, 2, 6, false⟩
                                                              (.terminal (.hubcap [⟨2, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨3, some 4, 2⟩]))
                                                              (.terminal (.hubcap [⟨1, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 2, 5⟩, ⟨3, some 4, 3⟩]))))))
                                                      (.split false ⟨.spoke, 2, 6, false⟩
                                                        (.terminal (.hubcap [⟨3, none, 1⟩, ⟨6, none, 3⟩, ⟨0, some 1, 4⟩, ⟨2, some 7, 7⟩, ⟨4, some 5, 5⟩]))
                                                        (.split false ⟨.spoke, 0, 6, false⟩
                                                          (.terminal (.hubcap [⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 1, 5⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 5⟩]))
                                                          (.terminal (.hubcap [⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨0, some 1, 4⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 5⟩]))))))))))
                                          (.split false ⟨.spoke, 0, 6, false⟩
                                            (.similar 0 ⟨true, 2⟩)
                                            (.split false ⟨.hat, 3, 6, false⟩
                                              (.terminal (.hubcap [⟨0, some 1, 5⟩, ⟨2, some 7, 5⟩, ⟨3, some 6, 5⟩, ⟨4, some 5, 5⟩]))
                                              (.split false ⟨.fan1, 4, 5, true⟩
                                                (.split false ⟨.spoke, 3, 6, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.spoke, 2, 6, false⟩
                                                    (.terminal (.hubcap [⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨0, some 1, 5⟩, ⟨2, some 7, 5⟩, ⟨3, some 4, 2⟩]))
                                                    (.split false ⟨.hat, 1, 6, false⟩
                                                      (.terminal (.hubcap [⟨2, none, 1⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 4⟩, ⟨3, some 4, 3⟩]))
                                                      (.split false ⟨.hat, 2, 5, true⟩
                                                        (.terminal (.hubcap [⟨2, none, 1⟩, ⟨6, none, 4⟩, ⟨0, some 1, 5⟩, ⟨3, some 4, 3⟩, ⟨5, some 7, 7⟩]))
                                                        (.split false ⟨.fan1, 2, 5, true⟩
                                                          (.terminal .reducible)
                                                          (.split false ⟨.hat, 1, 5, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨3, some 4, 3⟩]))
                                                            (.split false ⟨.hat, 3, 5, false⟩
                                                              (.terminal (.hubcap [⟨2, none, 1⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨3, some 4, 2⟩]))
                                                              (.split false ⟨.fan1, 2, 6, true⟩
                                                                (.terminal .reducible)
                                                                (.split false ⟨.hat, 5, 6, false⟩
                                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 3⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                                                  (.split false ⟨.hat, 5, 5, true⟩
                                                                    (.terminal (.hubcap [⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 4⟩]))
                                                                    (.split false ⟨.fan1, 5, 5, true⟩
                                                                      (.terminal .reducible)
                                                                      (.split false ⟨.hat, 4, 5, false⟩
                                                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                                                        (.split false ⟨.hat, 6, 5, false⟩
                                                                          (.terminal (.hubcap [⟨2, none, 1⟩, ⟨3, none, 3⟩, ⟨4, none, 0⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨5, some 6, 7⟩]))
                                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 3⟩, ⟨4, none, 0⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨1, some 7, 5⟩])))))))))))))))
                                                (.split true ⟨.hat, 6, 5, true⟩
                                                  (.split false ⟨.hat, 7, 6, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.fan1, 5, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.spoke, 2, 6, false⟩
                                                        (.terminal (.hubcap [⟨3, none, 1⟩, ⟨6, none, 4⟩, ⟨0, some 1, 4⟩, ⟨2, some 7, 7⟩, ⟨4, some 5, 4⟩]))
                                                        (.terminal (.hubcap [⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 4⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 4⟩])))))
                                                  (.split false ⟨.hat, 0, 5, true⟩
                                                    (.similar 0 ⟨true, 2⟩)
                                                    (.split false ⟨.hat, 7, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 4⟩]))
                                                      (.split false ⟨.hat, 7, 5, false⟩
                                                        (.split false ⟨.spoke, 2, 6, false⟩
                                                          (.terminal (.hubcap [⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 1, 4⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 5⟩]))
                                                          (.terminal (.hubcap [⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 1, 5⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 4⟩])))
                                                        (.split false ⟨.hat, 1, 6, false⟩
                                                          (.terminal (.hubcap [⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 3⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 5⟩]))
                                                          (.split false ⟨.hat, 5, 6, false⟩
                                                            (.terminal (.hubcap [⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 3⟩]))
                                                            (.split true ⟨.hat, 1, 5, false⟩
                                                              (.split false ⟨.hat, 2, 5, false⟩
                                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 3⟩, ⟨4, some 5, 5⟩]))
                                                                (.split false ⟨.hat, 3, 5, false⟩
                                                                  (.terminal (.hubcap [⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 4⟩, ⟨2, some 3, 3⟩, ⟨4, some 5, 5⟩]))
                                                                  (.split false ⟨.spoke, 2, 6, true⟩
                                                                    (.terminal (.hubcap [⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 3⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 5⟩]))
                                                                    (.split false ⟨.fan1, 2, 5, true⟩
                                                                      (.terminal .reducible)
                                                                      (.split false ⟨.spoke, 3, 6, false⟩
                                                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 5⟩]))
                                                                        (.split false ⟨.fan1, 3, 6, true⟩
                                                                          (.terminal .reducible)
                                                                          (.split false ⟨.hat, 4, 5, true⟩
                                                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 1⟩, ⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 3⟩]))
                                                                            (.split false ⟨.hat, 5, 5, false⟩
                                                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 1⟩, ⟨2, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨4, some 5, 5⟩]))))))))))
                                                              (.split false ⟨.hat, 5, 5, false⟩
                                                                (.similar 0 ⟨true, 2⟩)
                                                                (.split false ⟨.hat, 6, 6, true⟩
                                                                  (.terminal .reducible)
                                                                  (.split false ⟨.hat, 0, 6, true⟩
                                                                    (.terminal .reducible)
                                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 4⟩])))))))))))))))))))))))))))))))))
      (.split false ⟨.spoke, 0, 5, true⟩
        (.similar 0 ⟨false, 1⟩)
        (.split true ⟨.spoke, 4, 5, true⟩
          (.split false ⟨.spoke, 3, 5, true⟩
            (.similar 0 ⟨false, 5⟩)
            (.split false ⟨.spoke, 5, 5, true⟩
              (.similar 0 ⟨false, 6⟩)
              (.split true ⟨.spoke, 2, 5, true⟩
                (.split false ⟨.spoke, 1, 5, true⟩
                  (.similar 0 ⟨false, 3⟩)
                  (.split true ⟨.spoke, 0, 6, true⟩
                    (.split true ⟨.spoke, 1, 6, true⟩
                      (.split false ⟨.spoke, 3, 6, true⟩
                        (.terminal .reducible)
                        (.split false ⟨.spoke, 5, 7, false⟩
                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩, ⟨2, some 3, 5⟩]))
                          (.split false ⟨.spoke, 3, 7, false⟩
                            (.split false ⟨.hat, 2, 6, false⟩
                              (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨0, some 1, 6⟩, ⟨5, some 6, 6⟩, ⟨5, some 7, 6⟩, ⟨6, some 7, 5⟩]))
                              (.split false ⟨.fan1, 1, 5, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.hat, 0, 5, false⟩
                                  (.split false ⟨.spoke, 5, 6, false⟩
                                    (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨7, none, 2⟩, ⟨0, some 1, 7⟩, ⟨5, some 6, 5⟩]))
                                    (.split false ⟨.spoke, 6, 7, false⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 0⟩, ⟨7, none, 2⟩]))
                                      (.split false ⟨.spoke, 6, 6, false⟩
                                        (.split false ⟨.spoke, 3, 8, false⟩
                                          (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 3⟩, ⟨7, none, 2⟩, ⟨0, some 1, 7⟩, ⟨5, some 6, 5⟩]))
                                          (.split false ⟨.hat, 1, 5, false⟩
                                            (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨7, none, 2⟩, ⟨4, some 6, 5⟩, ⟨0, some 1, 7⟩, ⟨0, some 5, 6⟩, ⟨1, some 5, 6⟩]))
                                            (.split false ⟨.fan1, 1, 6, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.hat, 2, 5, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 2⟩]))
                                                (.terminal (.hubcap [⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨7, none, 2⟩, ⟨0, some 4, 5⟩, ⟨5, some 6, 5⟩]))))))
                                        (.split false ⟨.hat, 1, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.hat, 6, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.hat, 7, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.spoke, 3, 8, false⟩
                                                (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 3⟩, ⟨7, none, 2⟩, ⟨0, some 1, 6⟩, ⟨5, some 6, 6⟩]))
                                                (.split false ⟨.hat, 1, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 3⟩, ⟨7, none, 2⟩]))
                                                  (.split false ⟨.hat, 2, 5, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 3⟩, ⟨7, none, 2⟩]))
                                                    (.split false ⟨.hat, 3, 5, false⟩
                                                      (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨7, none, 2⟩, ⟨0, some 1, 5⟩, ⟨5, some 6, 6⟩]))
                                                      (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨7, none, 2⟩, ⟨0, some 1, 6⟩, ⟨5, some 6, 5⟩]))))))))))))
                                  (.split false ⟨.fan1, 0, 5, true⟩
                                    (.terminal .reducible)
                                    (.split false ⟨.spoke, 5, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨5, some 6, 3⟩]))
                                      (.split false ⟨.spoke, 6, 6, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.spoke, 6, 7, false⟩
                                          (.split false ⟨.spoke, 3, 8, false⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 0⟩, ⟨7, none, 3⟩]))
                                            (.split false ⟨.hat, 1, 5, false⟩
                                              (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 0⟩, ⟨7, none, 3⟩, ⟨0, some 1, 7⟩]))
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨6, none, 0⟩, ⟨7, none, 3⟩, ⟨1, some 5, 6⟩]))))
                                          (.split false ⟨.hat, 6, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.hat, 7, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.spoke, 3, 8, false⟩
                                                (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 1⟩, ⟨7, none, 3⟩, ⟨0, some 1, 7⟩]))
                                                (.split false ⟨.hat, 1, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 1⟩, ⟨7, none, 3⟩]))
                                                  (.split false ⟨.hat, 1, 5, true⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨6, none, 1⟩, ⟨7, none, 3⟩, ⟨1, some 5, 6⟩]))
                                                    (.split false ⟨.hat, 2, 5, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 1⟩, ⟨7, none, 3⟩]))
                                                      (.split false ⟨.hat, 3, 5, false⟩
                                                        (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 1⟩, ⟨7, none, 3⟩, ⟨0, some 1, 6⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 1⟩, ⟨7, none, 3⟩]))))))))))))))))
                            (.split false ⟨.hat, 4, 5, true⟩
                              (.terminal .reducible)
                              (.split false ⟨.spoke, 6, 7, false⟩
                                (.terminal (.hubcap [⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 0⟩, ⟨7, none, 3⟩, ⟨0, some 1, 7⟩, ⟨2, some 3, 5⟩]))
                                (.split false ⟨.spoke, 5, 6, false⟩
                                  (.split false ⟨.hat, 1, 6, false⟩
                                    (.terminal (.hubcap [⟨1, none, 3⟩, ⟨4, none, 2⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 5, 5⟩, ⟨2, some 3, 5⟩]))
                                    (.split false ⟨.hat, 6, 6, false⟩
                                      (.terminal (.hubcap [⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 1, 7⟩, ⟨2, some 3, 5⟩, ⟨5, some 6, 3⟩]))
                                      (.split false ⟨.hat, 0, 6, false⟩
                                        (.terminal (.hubcap [⟨4, none, 2⟩, ⟨7, none, 2⟩, ⟨0, some 1, 6⟩, ⟨2, some 3, 5⟩, ⟨5, some 6, 5⟩]))
                                        (.split false ⟨.hat, 0, 5, true⟩
                                          (.terminal (.hubcap [⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 1, 7⟩, ⟨2, some 3, 5⟩, ⟨5, some 6, 3⟩]))
                                          (.split false ⟨.fan1, 0, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.spoke, 6, 6, false⟩
                                              (.terminal (.hubcap [⟨4, none, 2⟩, ⟨7, none, 2⟩, ⟨0, some 1, 7⟩, ⟨2, some 3, 5⟩, ⟨5, some 6, 4⟩]))
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨4, none, 2⟩, ⟨6, none, 1⟩, ⟨7, none, 2⟩, ⟨1, some 5, 7⟩, ⟨2, some 3, 5⟩]))))))))
                                  (.split false ⟨.spoke, 6, 6, true⟩
                                    (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨7, none, 2⟩, ⟨0, some 1, 5⟩, ⟨5, some 6, 5⟩]))
                                    (.split false ⟨.hat, 1, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨2, some 3, 5⟩, ⟨6, some 7, 5⟩]))
                                      (.split false ⟨.hat, 3, 6, false⟩
                                        (.terminal (.hubcap [⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨0, some 1, 6⟩, ⟨2, some 3, 4⟩, ⟨6, some 7, 5⟩]))
                                        (.split false ⟨.hat, 1, 5, true⟩
                                          (.terminal (.hubcap [⟨3, none, 2⟩, ⟨5, none, 2⟩, ⟨0, some 1, 6⟩, ⟨2, some 4, 5⟩, ⟨6, some 7, 5⟩]))
                                          (.split false ⟨.hat, 2, 6, false⟩
                                            (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨0, some 1, 5⟩, ⟨6, some 7, 5⟩]))
                                            (.split false ⟨.hat, 2, 5, true⟩
                                              (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨0, some 1, 7⟩, ⟨6, some 7, 5⟩]))
                                              (.split false ⟨.fan1, 1, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.hat, 3, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨6, some 7, 5⟩]))
                                                  (.split false ⟨.fan1, 0, 5, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.fan1, 3, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.hat, 4, 6, false⟩
                                                        (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨0, some 1, 6⟩, ⟨6, some 7, 5⟩]))
                                                        (.split false ⟨.hat, 5, 5, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, some 7, 5⟩]))
                                                          (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨0, some 1, 6⟩, ⟨6, some 7, 4⟩]))))))))))))))))))))
                      (.split false ⟨.spoke, 3, 8, false⟩
                        (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 3⟩, ⟨1, some 7, 6⟩, ⟨0, some 5, 6⟩, ⟨0, some 6, 6⟩, ⟨5, some 6, 7⟩]))
                        (.split false ⟨.spoke, 3, 6, false⟩
                          (.split false ⟨.spoke, 5, 7, false⟩
                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨1, some 3, 6⟩]))
                            (.split false ⟨.spoke, 6, 7, false⟩
                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 0⟩, ⟨7, none, 3⟩, ⟨1, some 3, 6⟩]))
                              (.split false ⟨.hat, 0, 5, true⟩
                                (.split false ⟨.fan1, 0, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.spoke, 1, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨7, none, 4⟩, ⟨5, some 6, 4⟩]))
                                    (.split false ⟨.spoke, 3, 7, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, some 7, 6⟩, ⟨5, some 6, 4⟩]))
                                      (.split false ⟨.spoke, 5, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨7, none, 4⟩, ⟨1, some 3, 6⟩, ⟨5, some 6, 3⟩]))
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 1⟩, ⟨7, none, 3⟩, ⟨1, some 3, 6⟩]))))))
                                (.split false ⟨.spoke, 1, 7, false⟩
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨3, some 5, 7⟩, ⟨3, some 6, 7⟩, ⟨5, some 6, 7⟩]))
                                  (.split false ⟨.spoke, 5, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨1, some 3, 6⟩, ⟨5, some 6, 5⟩]))
                                    (.split false ⟨.spoke, 6, 6, true⟩
                                      (.similar 0 ⟨true, 1⟩)
                                      (.split false ⟨.spoke, 3, 7, false⟩
                                        (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨7, none, 2⟩, ⟨0, some 1, 5⟩, ⟨5, some 6, 6⟩]))
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 2⟩, ⟨4, none, 3⟩, ⟨7, none, 2⟩, ⟨1, some 3, 6⟩, ⟨5, some 6, 5⟩])))))))))
                          (.split false ⟨.spoke, 1, 7, false⟩
                            (.split false ⟨.spoke, 5, 7, false⟩
                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 5⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩]))
                              (.split false ⟨.spoke, 6, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨6, none, 0⟩, ⟨5, some 7, 5⟩]))
                                (.split false ⟨.spoke, 6, 6, true⟩
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 5⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩, ⟨4, some 5, 5⟩]))
                                  (.split false ⟨.spoke, 5, 6, true⟩
                                    (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨0, some 4, 5⟩, ⟨3, some 6, 7⟩, ⟨5, some 7, 5⟩]))
                                    (.split false ⟨.hat, 2, 5, false⟩
                                      (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 3, 7⟩, ⟨5, some 6, 4⟩]))
                                      (.split false ⟨.hat, 3, 5, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨5, some 6, 4⟩]))
                                        (.split false ⟨.fan1, 3, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.hat, 4, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨5, some 6, 4⟩]))
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 5⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨5, some 6, 3⟩]))))))))))
                            (.split false ⟨.hat, 1, 5, true⟩
                              (.terminal .reducible)
                              (.split false ⟨.hat, 2, 5, false⟩
                                (.split false ⟨.spoke, 5, 7, false⟩
                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 3⟩, ⟨3, none, 5⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩]))
                                  (.split false ⟨.spoke, 6, 7, false⟩
                                    (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 3⟩, ⟨3, none, 5⟩, ⟨6, none, 0⟩, ⟨0, some 4, 6⟩, ⟨5, some 7, 5⟩]))
                                    (.split false ⟨.spoke, 6, 6, true⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩, ⟨4, some 5, 5⟩]))
                                      (.split false ⟨.spoke, 5, 6, false⟩
                                        (.split false ⟨.hat, 3, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨5, some 6, 4⟩]))
                                          (.split false ⟨.fan1, 3, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.hat, 4, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨5, some 6, 4⟩]))
                                              (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 3⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 3, 7⟩, ⟨5, some 6, 3⟩])))))
                                        (.split false ⟨.hat, 3, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, some 6, 6⟩, ⟨5, some 7, 5⟩]))
                                          (.split false ⟨.fan1, 3, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.hat, 4, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨6, some 7, 5⟩]))
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 3⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨6, none, 0⟩, ⟨5, some 7, 5⟩])))))))))
                                (.split false ⟨.hat, 3, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.spoke, 5, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩]))
                                    (.split false ⟨.spoke, 6, 7, false⟩
                                      (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨6, none, 0⟩, ⟨0, some 1, 5⟩, ⟨5, some 7, 5⟩]))
                                      (.split false ⟨.spoke, 5, 6, false⟩
                                        (.split false ⟨.hat, 4, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨5, some 6, 4⟩]))
                                          (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 1, 5⟩, ⟨5, some 6, 3⟩])))
                                        (.split false ⟨.spoke, 6, 6, true⟩
                                          (.similar 0 ⟨true, 1⟩)
                                          (.split false ⟨.hat, 1, 6, false⟩
                                            (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨0, some 4, 5⟩, ⟨3, some 6, 6⟩, ⟨5, some 7, 5⟩]))
                                            (.split false ⟨.hat, 4, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨6, some 7, 5⟩]))
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨6, none, 0⟩, ⟨5, some 7, 5⟩])))))))))))))))
                    (.split false ⟨.spoke, 6, 6, true⟩
                      (.similar 0 ⟨true, 1⟩)
                      (.split false ⟨.spoke, 3, 8, false⟩
                        (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 3⟩, ⟨7, none, 2⟩, ⟨0, some 1, 6⟩, ⟨5, some 6, 6⟩]))
                        (.split false ⟨.spoke, 3, 7, false⟩
                          (.split false ⟨.spoke, 0, 7, false⟩
                            (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 2⟩]))
                            (.split false ⟨.spoke, 1, 6, false⟩
                              (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 2⟩, ⟨0, some 1, 4⟩]))
                              (.split false ⟨.spoke, 5, 6, false⟩
                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨7, none, 2⟩, ⟨5, some 6, 4⟩]))
                                (.split false ⟨.spoke, 6, 7, false⟩
                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 0⟩, ⟨7, none, 2⟩]))
                                  (.split false ⟨.hat, 2, 5, false⟩
                                    (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨7, none, 2⟩, ⟨0, some 1, 5⟩, ⟨5, some 6, 6⟩]))
                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨7, none, 2⟩, ⟨3, some 4, 4⟩, ⟨5, some 6, 5⟩])))))))
                          (.split true ⟨.spoke, 1, 7, false⟩
                            (.split false ⟨.spoke, 0, 7, false⟩
                              (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨7, none, 2⟩, ⟨5, some 6, 5⟩]))
                              (.split false ⟨.spoke, 3, 6, false⟩
                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 2⟩]))
                                (.split false ⟨.spoke, 5, 6, false⟩
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 5⟩, ⟨4, none, 3⟩, ⟨7, none, 2⟩, ⟨5, some 6, 4⟩]))
                                  (.split false ⟨.spoke, 6, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 3⟩, ⟨6, none, 0⟩, ⟨7, none, 2⟩]))
                                    (.split false ⟨.hat, 2, 5, true⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨7, none, 2⟩, ⟨3, some 4, 8⟩, ⟨5, some 6, 5⟩]))
                                      (.split false ⟨.hat, 3, 5, false⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 2⟩]))
                                        (.split false ⟨.fan1, 3, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.hat, 4, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 2⟩]))
                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨5, none, 3⟩, ⟨6, none, 0⟩, ⟨7, none, 2⟩]))))))))))
                            (.split false ⟨.spoke, 5, 7, false⟩
                              (.similar 0 ⟨true, 1⟩)
                              (.split true ⟨.spoke, 0, 7, false⟩
                                (.split false ⟨.spoke, 3, 6, false⟩
                                  (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨7, none, 2⟩, ⟨5, some 6, 5⟩]))
                                  (.split false ⟨.spoke, 6, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨3, none, 5⟩, ⟨5, none, 3⟩, ⟨6, none, 0⟩, ⟨7, none, 2⟩, ⟨2, some 4, 7⟩]))
                                    (.split false ⟨.spoke, 5, 6, false⟩
                                      (.split false ⟨.spoke, 1, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 5⟩, ⟨4, none, 3⟩, ⟨7, none, 2⟩, ⟨5, some 6, 4⟩]))
                                        (.split false ⟨.hat, 2, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 5⟩, ⟨4, none, 3⟩, ⟨7, none, 2⟩, ⟨5, some 6, 4⟩]))
                                          (.split false ⟨.fan1, 1, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.hat, 3, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 2⟩]))
                                              (.split false ⟨.fan1, 3, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.hat, 4, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 2⟩, ⟨7, none, 2⟩, ⟨5, some 6, 4⟩]))
                                                  (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨2, none, 4⟩, ⟨3, none, 5⟩, ⟨4, none, 3⟩, ⟨7, none, 2⟩, ⟨5, some 6, 3⟩]))))))))
                                      (.split false ⟨.hat, 2, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 1⟩, ⟨2, none, 3⟩, ⟨3, none, 5⟩, ⟨4, none, 4⟩, ⟨7, none, 2⟩, ⟨5, some 6, 5⟩]))
                                        (.split false ⟨.hat, 3, 5, false⟩
                                          (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 4⟩, ⟨7, none, 2⟩, ⟨5, some 6, 5⟩]))
                                          (.split false ⟨.fan1, 3, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.spoke, 1, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 5⟩, ⟨7, none, 2⟩, ⟨1, some 4, 5⟩, ⟨5, some 6, 5⟩]))
                                              (.split false ⟨.fan1, 1, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.hat, 4, 5, true⟩
                                                  (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨3, none, 5⟩, ⟨5, none, 3⟩, ⟨6, none, 0⟩, ⟨7, none, 2⟩, ⟨2, some 4, 7⟩]))
                                                  (.split false ⟨.hat, 2, 5, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 2⟩]))
                                                    (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨7, none, 2⟩, ⟨5, some 6, 4⟩]))))))))))))
                                (.split false ⟨.spoke, 6, 7, false⟩
                                  (.similar 0 ⟨true, 1⟩)
                                  (.split false ⟨.spoke, 3, 6, false⟩
                                    (.split false ⟨.spoke, 1, 6, false⟩
                                      (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨7, none, 2⟩, ⟨0, some 1, 4⟩, ⟨5, some 6, 5⟩]))
                                      (.split false ⟨.spoke, 5, 6, false⟩
                                        (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 2⟩, ⟨7, none, 2⟩, ⟨0, some 1, 5⟩, ⟨5, some 6, 4⟩]))
                                        (.split false ⟨.hat, 1, 6, false⟩
                                          (.terminal (.hubcap [⟨2, none, 3⟩, ⟨7, none, 2⟩, ⟨0, some 3, 5⟩, ⟨1, some 4, 5⟩, ⟨5, some 6, 5⟩]))
                                          (.split false ⟨.hat, 2, 6, false⟩
                                            (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨4, none, 3⟩, ⟨7, none, 2⟩, ⟨0, some 3, 7⟩, ⟨5, some 6, 5⟩]))
                                            (.split false ⟨.fan1, 1, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.hat, 2, 5, false⟩
                                                (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨7, none, 2⟩, ⟨0, some 1, 4⟩, ⟨5, some 6, 5⟩]))
                                                (.split false ⟨.hat, 3, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨7, none, 2⟩, ⟨3, some 4, 5⟩, ⟨5, some 6, 5⟩]))
                                                  (.split false ⟨.hat, 5, 5, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.hat, 0, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.hat, 1, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 2⟩, ⟨7, none, 2⟩, ⟨5, some 6, 5⟩]))
                                                        (.split false ⟨.fan1, 1, 6, true⟩
                                                          (.terminal .reducible)
                                                          (.split false ⟨.hat, 4, 5, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 4⟩, ⟨7, none, 2⟩]))
                                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 2⟩, ⟨7, none, 2⟩, ⟨5, some 6, 4⟩]))))))))))))))
                                    (.split true ⟨.hat, 3, 5, true⟩
                                      (.split false ⟨.fan1, 3, 5, true⟩
                                        (.terminal .reducible)
                                        (.split false ⟨.hat, 4, 5, true⟩
                                          (.terminal (.hubcap [⟨3, none, 5⟩, ⟨7, none, 2⟩, ⟨0, some 1, 3⟩, ⟨2, some 4, 7⟩, ⟨5, some 6, 3⟩]))
                                          (.split false ⟨.spoke, 5, 6, false⟩
                                            (.terminal (.hubcap [⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 2⟩, ⟨7, none, 2⟩, ⟨0, some 1, 3⟩, ⟨5, some 6, 4⟩]))
                                            (.split false ⟨.spoke, 1, 6, false⟩
                                              (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 2⟩, ⟨0, some 1, 3⟩]))
                                              (.split false ⟨.hat, 1, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.hat, 0, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.hat, 2, 5, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 2⟩]))
                                                    (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 3⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨7, none, 2⟩, ⟨5, some 6, 4⟩])))))))))
                                      (.split false ⟨.hat, 4, 5, true⟩
                                        (.similar 0 ⟨true, 1⟩)
                                        (.split false ⟨.spoke, 5, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨7, none, 2⟩, ⟨5, some 6, 4⟩]))
                                          (.split false ⟨.spoke, 1, 6, false⟩
                                            (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 2⟩, ⟨0, some 1, 4⟩]))
                                            (.split false ⟨.hat, 1, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 2⟩]))
                                              (.split false ⟨.hat, 2, 5, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 2⟩]))
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨7, none, 2⟩, ⟨5, some 6, 4⟩]))))))))))))))))))
                (.split false ⟨.spoke, 1, 5, true⟩
                  (.similar 0 ⟨false, 5⟩)
                  (.split true ⟨.spoke, 5, 6, false⟩
                    (.split false ⟨.spoke, 1, 7, false⟩
                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨4, none, 3⟩, ⟨6, none, 3⟩, ⟨2, some 3, 5⟩, ⟨5, some 7, 6⟩]))
                      (.split false ⟨.spoke, 2, 7, false⟩
                        (.terminal (.hubcap [⟨2, none, 0⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨6, none, 3⟩, ⟨0, some 1, 5⟩, ⟨5, some 7, 6⟩]))
                        (.split false ⟨.spoke, 3, 7, false⟩
                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨6, none, 3⟩, ⟨1, some 2, 5⟩, ⟨5, some 7, 6⟩]))
                          (.split false ⟨.spoke, 6, 6, false⟩
                            (.split false ⟨.spoke, 0, 7, false⟩
                              (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨7, none, 2⟩, ⟨5, some 6, 4⟩]))
                              (.split false ⟨.hat, 2, 6, false⟩
                                (.terminal (.hubcap [⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 1, 5⟩, ⟨2, some 3, 5⟩, ⟨5, some 6, 4⟩]))
                                (.split false ⟨.hat, 2, 5, false⟩
                                  (.split false ⟨.spoke, 5, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩, ⟨1, some 2, 4⟩]))
                                    (.split false ⟨.spoke, 6, 7, false⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 0⟩, ⟨7, none, 3⟩, ⟨1, some 2, 4⟩]))
                                      (.split false ⟨.hat, 4, 5, false⟩
                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨1, some 2, 4⟩, ⟨5, some 6, 4⟩]))
                                        (.split true ⟨.spoke, 3, 6, false⟩
                                          (.split false ⟨.spoke, 0, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 2⟩, ⟨7, none, 2⟩, ⟨5, some 6, 4⟩]))
                                            (.split false ⟨.spoke, 1, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 0⟩, ⟨3, none, 4⟩, ⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨5, some 6, 4⟩]))
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨1, some 2, 3⟩, ⟨5, some 6, 4⟩]))))
                                          (.split false ⟨.spoke, 0, 6, false⟩
                                            (.similar 0 ⟨true, 4⟩)
                                            (.split false ⟨.fan1, 3, 5, true⟩
                                              (.terminal .reducible)
                                              (.terminal (.hubcap [⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 3, 7⟩, ⟨1, some 2, 4⟩, ⟨5, some 6, 3⟩]))))))))
                                  (.split true ⟨.spoke, 0, 6, false⟩
                                    (.split false ⟨.spoke, 1, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨7, none, 2⟩, ⟨5, some 6, 4⟩]))
                                      (.split false ⟨.spoke, 2, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 4⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨7, none, 2⟩, ⟨5, some 6, 4⟩]))
                                        (.split false ⟨.spoke, 3, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 2⟩]))
                                          (.split false ⟨.spoke, 5, 7, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨7, none, 2⟩]))
                                            (.split false ⟨.spoke, 6, 7, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 0⟩, ⟨7, none, 2⟩]))
                                              (.split false ⟨.hat, 1, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨4, none, 3⟩, ⟨7, none, 2⟩, ⟨2, some 3, 7⟩, ⟨5, some 6, 4⟩]))
                                                (.split false ⟨.hat, 1, 5, true⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨4, none, 3⟩, ⟨7, none, 2⟩, ⟨2, some 3, 6⟩, ⟨5, some 6, 4⟩]))
                                                  (.split false ⟨.hat, 3, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨7, none, 2⟩, ⟨5, some 6, 4⟩]))
                                                    (.split false ⟨.hat, 3, 5, true⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨7, none, 2⟩, ⟨5, some 6, 4⟩]))
                                                      (.split false ⟨.hat, 4, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨7, none, 2⟩, ⟨5, some 6, 4⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨4, none, 3⟩, ⟨7, none, 2⟩, ⟨2, some 3, 7⟩, ⟨5, some 6, 3⟩]))))))))))))
                                    (.split false ⟨.spoke, 3, 6, false⟩
                                      (.similar 0 ⟨true, 4⟩)
                                      (.split true ⟨.hat, 4, 5, false⟩
                                        (.split false ⟨.spoke, 1, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨2, some 3, 4⟩, ⟨5, some 6, 4⟩]))
                                          (.split false ⟨.spoke, 2, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨2, some 3, 5⟩, ⟨5, some 6, 4⟩]))
                                            (.split false ⟨.spoke, 5, 7, false⟩
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩, ⟨1, some 2, 5⟩]))
                                              (.split false ⟨.spoke, 6, 7, false⟩
                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 0⟩, ⟨7, none, 3⟩, ⟨1, some 2, 5⟩]))
                                                (.terminal (.hubcap [⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 3, 6⟩, ⟨1, some 2, 5⟩, ⟨5, some 6, 4⟩]))))))
                                        (.split false ⟨.hat, 0, 5, false⟩
                                          (.similar 0 ⟨true, 4⟩)
                                          (.split false ⟨.fan1, 0, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.fan1, 3, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.spoke, 1, 6, false⟩
                                                (.terminal (.hubcap [⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 1, 6⟩, ⟨2, some 3, 5⟩, ⟨5, some 6, 3⟩]))
                                                (.split false ⟨.spoke, 2, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨1, some 2, 5⟩, ⟨5, some 6, 3⟩]))
                                                  (.split false ⟨.hat, 1, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨5, some 6, 3⟩, ⟨1, some 2, 5⟩, ⟨1, some 3, 5⟩, ⟨2, some 3, 7⟩]))
                                                    (.split false ⟨.hat, 1, 5, true⟩
                                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨5, some 6, 3⟩]))
                                                      (.split false ⟨.fan1, 1, 5, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.spoke, 5, 7, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩, ⟨1, some 2, 6⟩, ⟨1, some 3, 7⟩, ⟨2, some 3, 6⟩]))
                                                          (.split false ⟨.spoke, 6, 7, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 0⟩, ⟨7, none, 3⟩, ⟨1, some 2, 6⟩, ⟨1, some 3, 7⟩, ⟨2, some 3, 6⟩]))
                                                            (.split false ⟨.hat, 3, 6, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 1⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨5, some 6, 3⟩]))
                                                              (.split false ⟨.hat, 3, 5, true⟩
                                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨5, some 6, 3⟩]))
                                                                (.split false ⟨.fan1, 2, 5, true⟩
                                                                  (.terminal .reducible)
                                                                  (.split false ⟨.hat, 5, 5, false⟩
                                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 5⟩, ⟨5, some 6, 3⟩]))
                                                                    (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 1, 5⟩, ⟨5, some 6, 3⟩]))))))))))))))))))))))
                            (.split false ⟨.spoke, 5, 7, false⟩
                              (.split false ⟨.spoke, 0, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩]))
                                (.split false ⟨.spoke, 3, 6, false⟩
                                  (.terminal (.hubcap [⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨0, some 1, 6⟩, ⟨2, some 3, 5⟩]))
                                  (.split false ⟨.hat, 2, 6, false⟩
                                    (.terminal (.hubcap [⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨2, some 3, 5⟩]))
                                    (.split false ⟨.hat, 3, 6, false⟩
                                      (.terminal (.hubcap [⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨0, some 1, 6⟩, ⟨2, some 7, 5⟩]))
                                      (.split false ⟨.spoke, 1, 6, false⟩
                                        (.split false ⟨.spoke, 0, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩]))
                                          (.split false ⟨.spoke, 2, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩]))
                                            (.split false ⟨.hat, 1, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨2, some 3, 5⟩]))
                                              (.split false ⟨.hat, 1, 5, true⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨7, none, 4⟩, ⟨1, some 6, 5⟩, ⟨2, some 3, 5⟩]))
                                                (.split false ⟨.hat, 2, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨2, some 3, 5⟩]))
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩])))))))
                                        (.split false ⟨.hat, 4, 5, false⟩
                                          (.terminal (.hubcap [⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨2, some 3, 6⟩]))
                                          (.split false ⟨.fan1, 3, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.hat, 7, 5, false⟩
                                              (.terminal (.hubcap [⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 1, 5⟩, ⟨2, some 3, 7⟩]))
                                              (.split false ⟨.fan1, 6, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.hat, 0, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩, ⟨1, some 2, 5⟩]))
                                                  (.split false ⟨.spoke, 0, 6, false⟩
                                                    (.split false ⟨.spoke, 2, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨2, none, 4⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩]))
                                                      (.split false ⟨.hat, 1, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 7⟩]))
                                                        (.split false ⟨.hat, 2, 5, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨1, some 2, 3⟩]))
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 7⟩])))))
                                                    (.split false ⟨.fan1, 0, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.spoke, 2, 6, false⟩
                                                        (.terminal (.hubcap [⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨2, some 3, 5⟩]))
                                                        (.terminal (.hubcap [⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨0, some 2, 5⟩, ⟨1, some 3, 5⟩])))))))))))))))
                              (.split false ⟨.spoke, 0, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 6⟩, ⟨5, some 6, 6⟩]))
                                (.split false ⟨.hat, 5, 5, false⟩
                                  (.split false ⟨.hat, 6, 5, true⟩
                                    (.split false ⟨.spoke, 0, 6, false⟩
                                      (.terminal (.hubcap [⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 1, 5⟩, ⟨2, some 3, 5⟩, ⟨5, some 6, 5⟩]))
                                      (.terminal (.hubcap [⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 1, 6⟩, ⟨2, some 3, 5⟩, ⟨5, some 6, 4⟩])))
                                    (.split false ⟨.spoke, 3, 6, false⟩
                                      (.terminal (.hubcap [⟨4, none, 2⟩, ⟨6, none, 3⟩, ⟨0, some 1, 6⟩, ⟨2, some 3, 5⟩, ⟨5, some 7, 4⟩]))
                                      (.split false ⟨.hat, 1, 6, false⟩
                                        (.terminal (.hubcap [⟨4, none, 3⟩, ⟨6, none, 3⟩, ⟨0, some 1, 4⟩, ⟨2, some 3, 6⟩, ⟨5, some 7, 4⟩]))
                                        (.split false ⟨.hat, 2, 6, false⟩
                                          (.terminal (.hubcap [⟨4, none, 3⟩, ⟨6, none, 3⟩, ⟨0, some 1, 5⟩, ⟨2, some 3, 5⟩, ⟨5, some 7, 4⟩]))
                                          (.split false ⟨.hat, 3, 6, false⟩
                                            (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨6, none, 3⟩, ⟨0, some 1, 6⟩, ⟨5, some 7, 4⟩]))
                                            (.split false ⟨.spoke, 1, 6, false⟩
                                              (.split false ⟨.spoke, 0, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 5⟩]))
                                                (.split false ⟨.spoke, 2, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩]))
                                                  (.split false ⟨.hat, 1, 5, true⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨4, none, 3⟩, ⟨1, some 6, 5⟩, ⟨2, some 3, 5⟩, ⟨5, some 7, 4⟩]))
                                                    (.split false ⟨.hat, 2, 5, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨4, none, 3⟩, ⟨7, none, 4⟩, ⟨2, some 3, 5⟩, ⟨5, some 6, 3⟩]))
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩, ⟨2, some 3, 4⟩]))))))
                                              (.split false ⟨.hat, 4, 5, false⟩
                                                (.terminal (.hubcap [⟨4, none, 2⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨2, some 3, 5⟩]))
                                                (.split false ⟨.fan1, 3, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.hat, 7, 5, false⟩
                                                    (.terminal (.hubcap [⟨4, none, 3⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 1, 5⟩, ⟨2, some 3, 6⟩]))
                                                    (.split false ⟨.fan1, 6, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.spoke, 0, 6, true⟩
                                                        (.terminal (.hubcap [⟨4, none, 3⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨2, some 3, 5⟩, ⟨5, some 6, 3⟩]))
                                                        (.split false ⟨.spoke, 2, 6, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨2, none, 4⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩]))
                                                          (.split false ⟨.hat, 2, 5, false⟩
                                                            (.terminal (.hubcap [⟨4, none, 3⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 3, 7⟩, ⟨1, some 2, 3⟩]))
                                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 1⟩, ⟨7, none, 3⟩, ⟨1, some 6, 4⟩, ⟨2, some 3, 6⟩])))))))))))))))
                                  (.split false ⟨.spoke, 1, 6, false⟩
                                    (.terminal (.hubcap [⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 1, 5⟩, ⟨2, some 3, 4⟩, ⟨5, some 6, 6⟩]))
                                    (.split false ⟨.spoke, 2, 6, false⟩
                                      (.terminal (.hubcap [⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 1, 4⟩, ⟨2, some 3, 5⟩, ⟨5, some 6, 6⟩]))
                                      (.split false ⟨.spoke, 0, 6, false⟩
                                        (.split false ⟨.hat, 1, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨5, some 6, 6⟩, ⟨1, some 2, 4⟩, ⟨1, some 3, 5⟩, ⟨2, some 3, 6⟩]))
                                          (.split false ⟨.hat, 2, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 4⟩]))
                                            (.split false ⟨.hat, 3, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨1, some 2, 3⟩, ⟨5, some 6, 6⟩]))
                                              (.split false ⟨.hat, 7, 5, false⟩
                                                (.terminal (.hubcap [⟨4, none, 2⟩, ⟨7, none, 2⟩, ⟨0, some 1, 5⟩, ⟨2, some 3, 6⟩, ⟨5, some 6, 5⟩]))
                                                (.split false ⟨.fan1, 6, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.hat, 3, 5, false⟩
                                                    (.terminal (.hubcap [⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 1, 4⟩, ⟨2, some 3, 5⟩]))
                                                    (.split false ⟨.hat, 0, 5, false⟩
                                                      (.terminal (.hubcap [⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 1, 4⟩, ⟨2, some 3, 6⟩]))
                                                      (.split false ⟨.hat, 2, 5, false⟩
                                                        (.split false ⟨.spoke, 3, 6, false⟩
                                                          (.terminal (.hubcap [⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 3, 7⟩, ⟨1, some 2, 2⟩]))
                                                          (.split false ⟨.hat, 4, 5, true⟩
                                                            (.terminal .reducible)
                                                            (.split false ⟨.hat, 1, 5, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨1, some 2, 3⟩]))
                                                              (.split false ⟨.hat, 4, 6, false⟩
                                                                (.terminal (.hubcap [⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 3, 6⟩, ⟨1, some 2, 3⟩]))
                                                                (.terminal (.hubcap [⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 1, 4⟩, ⟨0, some 2, 6⟩, ⟨1, some 2, 3⟩]))))))
                                                        (.split false ⟨.fan1, 2, 6, true⟩
                                                          (.terminal .reducible)
                                                          (.split false ⟨.spoke, 3, 6, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩]))
                                                            (.split false ⟨.hat, 4, 5, true⟩
                                                              (.terminal .reducible)
                                                              (.split false ⟨.hat, 1, 5, true⟩
                                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 5⟩]))
                                                                (.split false ⟨.hat, 4, 6, false⟩
                                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩]))
                                                                  (.terminal (.hubcap [⟨1, none, 1⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 2, 5⟩])))))))))))))))
                                        (.split false ⟨.hat, 0, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.spoke, 3, 6, false⟩
                                            (.split false ⟨.hat, 1, 5, false⟩
                                              (.terminal (.hubcap [⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 1, 5⟩, ⟨2, some 3, 5⟩, ⟨5, some 6, 5⟩]))
                                              (.split false ⟨.hat, 2, 5, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨1, some 2, 3⟩, ⟨5, some 6, 5⟩]))
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨5, some 6, 5⟩]))))
                                            (.split false ⟨.hat, 4, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.hat, 1, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨5, some 6, 5⟩]))
                                                (.split false ⟨.hat, 1, 5, false⟩
                                                  (.terminal (.hubcap [⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 1, 5⟩, ⟨2, some 3, 5⟩, ⟨5, some 6, 5⟩]))
                                                  (.split false ⟨.hat, 3, 5, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.hat, 2, 5, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨5, some 6, 5⟩]))
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨2, some 3, 4⟩, ⟨5, some 6, 5⟩])))))))))))))))))))
                    (.split false ⟨.spoke, 6, 6, false⟩
                      (.similar 0 ⟨true, 4⟩)
                      (.split false ⟨.spoke, 1, 7, false⟩
                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨2, some 3, 4⟩]))
                        (.split false ⟨.spoke, 2, 7, false⟩
                          (.terminal (.hubcap [⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨0, some 1, 4⟩]))
                          (.split true ⟨.spoke, 0, 6, false⟩
                            (.split false ⟨.spoke, 3, 7, false⟩
                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨1, some 2, 3⟩]))
                              (.split false ⟨.spoke, 3, 6, false⟩
                                (.split false ⟨.spoke, 0, 7, false⟩
                                  (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨2, some 3, 4⟩]))
                                  (.split false ⟨.spoke, 1, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 0⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨1, some 3, 4⟩]))
                                    (.split false ⟨.spoke, 2, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨2, some 3, 3⟩]))
                                      (.split false ⟨.hat, 2, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩]))
                                        (.split false ⟨.hat, 5, 5, false⟩
                                          (.terminal (.hubcap [⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 1, 4⟩, ⟨2, some 3, 4⟩, ⟨5, some 6, 7⟩]))
                                          (.split false ⟨.fan1, 5, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.hat, 6, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨4, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨1, some 2, 3⟩, ⟨3, some 5, 5⟩]))
                                              (.split false ⟨.hat, 7, 5, false⟩
                                                (.terminal (.hubcap [⟨4, none, 3⟩, ⟨7, none, 2⟩, ⟨0, some 1, 4⟩, ⟨2, some 3, 4⟩, ⟨5, some 6, 7⟩]))
                                                (.split false ⟨.fan1, 6, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.hat, 2, 5, true⟩
                                                    (.terminal (.hubcap [⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨0, some 2, 3⟩, ⟨1, some 3, 3⟩]))
                                                    (.split false ⟨.hat, 1, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨2, some 3, 3⟩]))
                                                      (.split false ⟨.hat, 1, 5, true⟩
                                                        (.terminal (.hubcap [⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 3, 5⟩, ⟨1, some 2, 2⟩, ⟨5, some 6, 7⟩]))
                                                        (.split false ⟨.hat, 3, 5, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩]))
                                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 3⟩, ⟨5, some 6, 7⟩])))))))))))))))
                                (.split false ⟨.hat, 4, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.spoke, 0, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 5⟩, ⟨5, some 6, 7⟩]))
                                    (.split false ⟨.spoke, 1, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨7, none, 3⟩, ⟨1, some 4, 4⟩, ⟨2, some 3, 4⟩, ⟨5, some 6, 7⟩]))
                                      (.split false ⟨.hat, 2, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨5, some 6, 7⟩]))
                                        (.split false ⟨.hat, 5, 5, false⟩
                                          (.terminal (.hubcap [⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 1, 4⟩, ⟨2, some 3, 5⟩, ⟨5, some 6, 6⟩]))
                                          (.split false ⟨.fan1, 5, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.hat, 3, 6, false⟩
                                              (.terminal (.hubcap [⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨5, some 6, 7⟩, ⟨0, some 1, 4⟩, ⟨0, some 2, 4⟩, ⟨1, some 2, 3⟩]))
                                              (.split false ⟨.hat, 6, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨7, none, 3⟩, ⟨1, some 6, 4⟩, ⟨2, some 3, 5⟩]))
                                                (.split false ⟨.hat, 7, 5, false⟩
                                                  (.terminal (.hubcap [⟨4, none, 3⟩, ⟨7, none, 2⟩, ⟨0, some 1, 4⟩, ⟨2, some 3, 5⟩, ⟨5, some 6, 6⟩]))
                                                  (.split false ⟨.fan1, 6, 5, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.hat, 1, 5, false⟩
                                                      (.split false ⟨.spoke, 2, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 5⟩, ⟨5, some 6, 7⟩]))
                                                        (.split false ⟨.hat, 3, 5, true⟩
                                                          (.terminal .reducible)
                                                          (.split false ⟨.hat, 2, 5, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩]))
                                                            (.split false ⟨.hat, 4, 6, false⟩
                                                              (.terminal (.hubcap [⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 1, 3⟩, ⟨2, some 3, 4⟩, ⟨5, some 6, 7⟩]))
                                                              (.split false ⟨.fan1, 2, 5, true⟩
                                                                (.terminal .reducible)
                                                                (.split false ⟨.fan1, 3, 5, true⟩
                                                                  (.terminal .reducible)
                                                                  (.split false ⟨.hat, 1, 6, false⟩
                                                                    (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 1⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 5⟩, ⟨5, some 6, 7⟩]))
                                                                    (.split false ⟨.hat, 0, 5, false⟩
                                                                      (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 1⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨5, some 6, 6⟩]))
                                                                      (.split false ⟨.fan1, 0, 5, true⟩
                                                                        (.terminal .reducible)
                                                                        (.split false ⟨.fan1, 5, 6, true⟩
                                                                          (.terminal .reducible)
                                                                          (.split false ⟨.fan1, 0, 6, true⟩
                                                                            (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 1⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 5⟩, ⟨5, some 6, 7⟩]))
                                                                            (.split false ⟨.fan1, 1, 5, false⟩
                                                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 4⟩, ⟨5, some 6, 7⟩]))
                                                                              (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 1⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 5⟩, ⟨5, some 6, 7⟩]))))))))))))))
                                                      (.split false ⟨.hat, 0, 5, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.spoke, 2, 6, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 5⟩, ⟨5, some 6, 6⟩]))
                                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 4⟩, ⟨5, some 6, 6⟩])))))))))))))))))
                            (.split false ⟨.spoke, 3, 6, false⟩
                              (.similar 0 ⟨true, 4⟩)
                              (.split false ⟨.hat, 4, 5, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.hat, 0, 5, true⟩
                                  (.terminal .reducible)
                                  (.split false ⟨.hat, 2, 5, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨5, some 6, 6⟩]))
                                    (.split false ⟨.hat, 6, 6, false⟩
                                      (.terminal (.hubcap [⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 1, 5⟩, ⟨2, some 3, 5⟩]))
                                      (.split false ⟨.fan1, 0, 5, true⟩
                                        (.terminal (.hubcap [⟨0, none, 1⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨1, some 2, 4⟩, ⟨5, some 6, 6⟩]))
                                        (.split false ⟨.fan1, 3, 5, true⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨1, some 2, 4⟩, ⟨5, some 6, 6⟩]))
                                          (.split true ⟨.hat, 1, 5, true⟩
                                            (.split false ⟨.spoke, 1, 6, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.spoke, 2, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨5, some 6, 6⟩]))
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 3⟩, ⟨5, some 6, 6⟩]))))
                                            (.split false ⟨.hat, 3, 5, true⟩
                                              (.similar 0 ⟨true, 4⟩)
                                              (.split false ⟨.spoke, 2, 6, false⟩
                                                (.terminal (.hubcap [⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 1, 3⟩, ⟨2, some 3, 5⟩, ⟨5, some 6, 6⟩]))
                                                (.split false ⟨.spoke, 1, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨7, none, 3⟩, ⟨1, some 4, 6⟩, ⟨2, some 3, 3⟩, ⟨5, some 6, 6⟩]))
                                                  (.split false ⟨.hat, 1, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨5, some 6, 6⟩, ⟨1, some 2, 4⟩, ⟨1, some 3, 4⟩, ⟨2, some 3, 5⟩]))
                                                    (.split false ⟨.fan1, 1, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.hat, 3, 6, false⟩
                                                        (.terminal (.hubcap [⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 1, 5⟩, ⟨5, some 6, 6⟩]))
                                                        (.terminal (.hubcap [⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 1, 4⟩, ⟨2, some 3, 4⟩, ⟨5, some 6, 6⟩])))))))))))))))))))))))))
          (.split false ⟨.spoke, 2, 5, true⟩
            (.similar 0 ⟨false, 3⟩)
            (.split true ⟨.spoke, 5, 5, true⟩
              (.split true ⟨.spoke, 3, 5, true⟩
                (.split false ⟨.spoke, 1, 5, true⟩
                  (.split false ⟨.spoke, 0, 8, false⟩
                    (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, some 5, 5⟩, ⟨3, some 7, 5⟩, ⟨2, some 4, 6⟩, ⟨2, some 6, 9⟩, ⟨4, some 6, 6⟩]))
                    (.split false ⟨.spoke, 0, 6, true⟩
                      (.terminal (.hubcap [⟨0, none, 5⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 4⟩, ⟨5, none, 2⟩, ⟨6, some 7, 3⟩]))
                      (.split false ⟨.spoke, 2, 8, false⟩
                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨5, none, 3⟩, ⟨3, some 7, 5⟩, ⟨4, some 6, 6⟩]))
                        (.split false ⟨.spoke, 2, 6, true⟩
                          (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨2, none, 5⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 2⟩, ⟨3, some 4, 3⟩]))
                          (.split false ⟨.spoke, 4, 8, false⟩
                            (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 6, 6⟩]))
                            (.split false ⟨.spoke, 4, 6, true⟩
                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 3⟩, ⟨4, none, 5⟩, ⟨7, none, 2⟩, ⟨5, some 6, 3⟩]))
                              (.split false ⟨.spoke, 6, 6, false⟩
                                (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 2⟩, ⟨5, none, 2⟩, ⟨7, none, 2⟩, ⟨0, some 2, 6⟩, ⟨4, some 6, 6⟩]))
                                (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨3, none, 2⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨4, some 5, 3⟩])))))))))
                  (.split false ⟨.spoke, 0, 7, false⟩
                    (.terminal (.hubcap [⟨0, none, 0⟩, ⟨5, none, 3⟩, ⟨1, some 2, 5⟩, ⟨3, some 7, 6⟩, ⟨4, some 6, 6⟩]))
                    (.split false ⟨.spoke, 2, 7, false⟩
                      (.terminal (.hubcap [⟨2, none, 0⟩, ⟨5, none, 3⟩, ⟨0, some 1, 5⟩, ⟨3, some 7, 6⟩, ⟨4, some 6, 6⟩]))
                      (.split true ⟨.spoke, 4, 6, true⟩
                        (.split false ⟨.spoke, 6, 6, true⟩
                          (.terminal .reducible)
                          (.split false ⟨.spoke, 1, 7, false⟩
                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨4, none, 5⟩, ⟨3, some 7, 6⟩, ⟨5, some 6, 3⟩]))
                            (.split false ⟨.hat, 4, 5, false⟩
                              (.terminal (.hubcap [⟨4, none, 4⟩, ⟨0, some 1, 5⟩, ⟨5, some 6, 3⟩, ⟨2, some 3, 6⟩, ⟨2, some 7, 6⟩, ⟨3, some 7, 5⟩]))
                              (.split false ⟨.fan1, 4, 5, true⟩
                                (.terminal .reducible)
                                (.split false ⟨.hat, 3, 6, false⟩
                                  (.terminal (.hubcap [⟨3, none, 3⟩, ⟨4, none, 5⟩, ⟨0, some 1, 5⟩, ⟨2, some 7, 4⟩, ⟨5, some 6, 3⟩]))
                                  (.split false ⟨.hat, 5, 5, false⟩
                                    (.terminal (.hubcap [⟨4, none, 4⟩, ⟨5, none, 2⟩, ⟨6, none, 1⟩, ⟨3, some 7, 6⟩, ⟨0, some 1, 5⟩, ⟨0, some 2, 6⟩, ⟨1, some 2, 4⟩]))
                                    (.split false ⟨.fan1, 4, 6, true⟩
                                      (.terminal .reducible)
                                      (.split false ⟨.hat, 0, 5, false⟩
                                        (.terminal (.hubcap [⟨4, none, 5⟩, ⟨5, none, 3⟩, ⟨6, none, 0⟩, ⟨7, none, 2⟩, ⟨0, some 3, 6⟩, ⟨1, some 2, 4⟩]))
                                        (.split false ⟨.spoke, 0, 6, false⟩
                                          (.split false ⟨.spoke, 1, 6, false⟩
                                            (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 5⟩, ⟨5, none, 3⟩, ⟨6, none, 0⟩, ⟨7, none, 2⟩, ⟨0, some 1, 3⟩]))
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 3⟩, ⟨4, none, 5⟩, ⟨5, none, 3⟩, ⟨6, none, 0⟩, ⟨7, none, 2⟩, ⟨1, some 2, 3⟩])))
                                          (.split false ⟨.fan1, 0, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.spoke, 1, 6, true⟩
                                              (.terminal (.hubcap [⟨2, none, 1⟩, ⟨3, none, 3⟩, ⟨4, none, 5⟩, ⟨5, none, 3⟩, ⟨6, none, 0⟩, ⟨7, none, 3⟩, ⟨0, some 1, 5⟩]))
                                              (.split false ⟨.spoke, 2, 6, true⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 5⟩, ⟨5, none, 3⟩, ⟨6, none, 0⟩, ⟨7, none, 3⟩]))
                                                (.split false ⟨.spoke, 6, 7, true⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 5⟩, ⟨5, none, 3⟩, ⟨6, none, 0⟩, ⟨7, none, 3⟩, ⟨1, some 2, 4⟩]))
                                                  (.split false ⟨.hat, 1, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 5⟩, ⟨5, none, 3⟩, ⟨6, none, 0⟩, ⟨7, none, 3⟩]))
                                                    (.split false ⟨.hat, 1, 5, true⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 5⟩, ⟨5, none, 3⟩, ⟨6, none, 0⟩, ⟨7, none, 3⟩, ⟨1, some 2, 3⟩]))
                                                      (.split false ⟨.hat, 2, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 5⟩, ⟨5, none, 3⟩, ⟨6, none, 0⟩, ⟨7, none, 3⟩]))
                                                        (.split false ⟨.hat, 3, 5, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 5⟩, ⟨5, none, 3⟩, ⟨6, none, 0⟩, ⟨7, none, 3⟩]))
                                                          (.split false ⟨.hat, 6, 5, true⟩
                                                            (.terminal .reducible)
                                                            (.split false ⟨.hat, 7, 5, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 5⟩, ⟨5, none, 3⟩, ⟨6, none, 0⟩, ⟨7, none, 3⟩]))
                                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 5⟩, ⟨5, none, 3⟩, ⟨6, none, 0⟩, ⟨7, none, 3⟩, ⟨1, some 2, 3⟩])))))))))))))))))))))
                        (.split false ⟨.spoke, 6, 6, true⟩
                          (.similar 0 ⟨true, 5⟩)
                          (.split false ⟨.spoke, 1, 7, false⟩
                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨5, none, 2⟩, ⟨7, none, 3⟩, ⟨4, some 6, 6⟩]))
                            (.split true ⟨.hat, 1, 5, false⟩
                              (.split false ⟨.spoke, 0, 6, false⟩
                                (.terminal (.hubcap [⟨5, none, 2⟩, ⟨7, none, 2⟩, ⟨0, some 3, 5⟩, ⟨1, some 2, 5⟩, ⟨4, some 6, 6⟩]))
                                (.split false ⟨.spoke, 4, 8, false⟩
                                  (.terminal (.hubcap [⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨0, some 1, 5⟩, ⟨2, some 3, 6⟩]))
                                  (.split false ⟨.spoke, 6, 8, false⟩
                                    (.terminal (.hubcap [⟨4, none, 4⟩, ⟨5, none, 2⟩, ⟨6, none, 0⟩, ⟨7, none, 3⟩, ⟨0, some 1, 5⟩, ⟨2, some 3, 6⟩]))
                                    (.split false ⟨.hat, 2, 5, false⟩
                                      (.split false ⟨.spoke, 1, 6, true⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨3, none, 2⟩, ⟨5, none, 2⟩, ⟨2, some 7, 5⟩, ⟨4, some 6, 6⟩]))
                                        (.split false ⟨.spoke, 2, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨5, none, 2⟩, ⟨7, none, 3⟩, ⟨4, some 6, 6⟩]))
                                          (.split false ⟨.hat, 3, 5, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨5, none, 2⟩, ⟨7, none, 3⟩, ⟨4, some 6, 6⟩]))
                                            (.split false ⟨.fan1, 2, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.spoke, 4, 7, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 3⟩, ⟨5, none, 2⟩, ⟨7, none, 3⟩, ⟨1, some 2, 4⟩, ⟨4, some 6, 5⟩]))
                                                (.split false ⟨.hat, 1, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 3⟩, ⟨5, none, 2⟩, ⟨7, none, 3⟩, ⟨1, some 2, 3⟩, ⟨4, some 6, 6⟩]))
                                                  (.split false ⟨.hat, 4, 5, false⟩
                                                    (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨5, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 1, 4⟩, ⟨4, some 6, 6⟩]))
                                                    (.split false ⟨.spoke, 6, 7, true⟩
                                                      (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨5, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 1, 3⟩, ⟨4, some 6, 6⟩]))
                                                      (.split false ⟨.hat, 5, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 4⟩, ⟨5, none, 2⟩, ⟨6, some 7, 4⟩])))))))))))
                                      (.split false ⟨.hat, 1, 6, false⟩
                                        (.terminal (.hubcap [⟨5, none, 2⟩, ⟨0, some 1, 4⟩, ⟨4, some 6, 6⟩, ⟨2, some 3, 6⟩, ⟨2, some 7, 6⟩, ⟨3, some 7, 5⟩]))
                                        (.split false ⟨.fan1, 0, 5, true⟩
                                          (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨5, none, 2⟩, ⟨7, none, 2⟩, ⟨4, some 6, 6⟩]))
                                          (.split false ⟨.spoke, 1, 6, false⟩
                                            (.split false ⟨.spoke, 2, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨5, none, 2⟩, ⟨7, none, 3⟩, ⟨4, some 6, 6⟩]))
                                              (.split false ⟨.hat, 0, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.hat, 3, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨5, none, 2⟩, ⟨7, none, 2⟩, ⟨4, some 6, 6⟩]))
                                                  (.split false ⟨.fan1, 2, 6, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.spoke, 4, 7, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 3⟩, ⟨5, none, 2⟩, ⟨7, none, 2⟩, ⟨1, some 2, 6⟩, ⟨4, some 6, 5⟩]))
                                                      (.split false ⟨.hat, 4, 5, false⟩
                                                        (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨5, none, 2⟩, ⟨7, none, 2⟩, ⟨0, some 1, 5⟩, ⟨4, some 6, 6⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨5, none, 2⟩, ⟨7, none, 2⟩, ⟨4, some 6, 6⟩]))))))))
                                            (.split false ⟨.spoke, 2, 6, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.spoke, 4, 7, false⟩
                                                (.terminal (.hubcap [⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 6, 7⟩, ⟨1, some 2, 4⟩]))
                                                (.split false ⟨.spoke, 6, 7, false⟩
                                                  (.terminal (.hubcap [⟨3, none, 2⟩, ⟨4, none, 4⟩, ⟨5, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 6, 5⟩, ⟨1, some 2, 4⟩]))
                                                  (.split false ⟨.hat, 3, 5, true⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 4⟩, ⟨3, none, 2⟩, ⟨5, none, 2⟩, ⟨7, none, 2⟩, ⟨4, some 6, 6⟩]))
                                                    (.split false ⟨.hat, 5, 5, true⟩
                                                      (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨5, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 1, 4⟩, ⟨4, some 6, 6⟩]))
                                                      (.split false ⟨.hat, 4, 5, false⟩
                                                        (.terminal (.hubcap [⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 6, 7⟩, ⟨1, some 2, 4⟩]))
                                                        (.terminal (.hubcap [⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 6, 6⟩, ⟨1, some 2, 4⟩])))))))))))))))
                              (.split false ⟨.hat, 2, 5, false⟩
                                (.similar 0 ⟨true, 5⟩)
                                (.split false ⟨.spoke, 2, 6, false⟩
                                  (.terminal (.hubcap [⟨3, none, 2⟩, ⟨5, none, 2⟩, ⟨0, some 1, 5⟩, ⟨2, some 7, 5⟩, ⟨4, some 6, 6⟩]))
                                  (.terminal (.hubcap [⟨5, none, 2⟩, ⟨7, none, 2⟩, ⟨0, some 3, 5⟩, ⟨1, some 2, 5⟩, ⟨4, some 6, 6⟩])))))))))))
                (.split false ⟨.spoke, 1, 5, true⟩
                  (.similar 0 ⟨false, 2⟩)
                  (.split false ⟨.spoke, 6, 6, true⟩
                    (.split false ⟨.spoke, 2, 7, false⟩
                      (.terminal (.hubcap [⟨2, none, 0⟩, ⟨6, none, 5⟩, ⟨0, some 1, 4⟩, ⟨3, some 4, 4⟩, ⟨5, some 7, 7⟩]))
                      (.split false ⟨.spoke, 2, 6, false⟩
                        (.split false ⟨.spoke, 0, 7, false⟩
                          (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 0⟩, ⟨2, none, 4⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨3, some 4, 4⟩]))
                          (.split false ⟨.spoke, 4, 7, false⟩
                            (.terminal (.hubcap [⟨2, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 0⟩, ⟨5, none, 3⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨0, some 1, 4⟩]))
                            (.split false ⟨.fan1, 6, 5, true⟩
                              (.terminal (.hubcap [⟨2, none, 4⟩, ⟨5, none, 3⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 1, 4⟩, ⟨3, some 4, 4⟩]))
                              (.split false ⟨.fan1, 6, 6, true⟩
                                (.split false ⟨.spoke, 1, 7, false⟩
                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨6, none, 4⟩, ⟨3, some 4, 4⟩, ⟨5, some 7, 7⟩]))
                                  (.split false ⟨.spoke, 3, 7, false⟩
                                    (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 3⟩, ⟨6, none, 4⟩, ⟨0, some 1, 4⟩, ⟨5, some 7, 7⟩]))
                                    (.split false ⟨.spoke, 0, 6, false⟩
                                      (.split false ⟨.spoke, 1, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨3, some 4, 4⟩]))
                                        (.split false ⟨.spoke, 3, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨6, none, 4⟩, ⟨5, some 7, 6⟩]))
                                          (.split false ⟨.spoke, 4, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨3, none, 0⟩, ⟨6, none, 4⟩, ⟨2, some 4, 7⟩, ⟨5, some 7, 5⟩]))
                                            (.split false ⟨.hat, 1, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 4⟩, ⟨4, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨3, some 5, 4⟩]))
                                              (.split false ⟨.hat, 1, 5, true⟩
                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨4, none, 3⟩, ⟨7, none, 2⟩, ⟨2, some 6, 7⟩, ⟨3, some 5, 4⟩]))
                                                (.split false ⟨.hat, 2, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨6, none, 4⟩, ⟨5, some 7, 6⟩]))
                                                  (.split false ⟨.hat, 2, 5, true⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨4, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨3, some 5, 4⟩]))
                                                    (.split false ⟨.hat, 3, 5, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨6, none, 4⟩, ⟨5, some 7, 6⟩]))
                                                      (.split false ⟨.hat, 4, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 4⟩, ⟨6, none, 4⟩, ⟨3, some 4, 3⟩, ⟨5, some 7, 6⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 4⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩])))))))))))
                                      (.split false ⟨.fan1, 0, 5, true⟩
                                        (.split false ⟨.hat, 0, 6, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.spoke, 1, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 4⟩, ⟨5, none, 4⟩, ⟨6, some 7, 6⟩]))
                                            (.split false ⟨.spoke, 3, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, some 7, 6⟩]))
                                              (.split false ⟨.spoke, 4, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨3, none, 0⟩, ⟨4, some 5, 6⟩, ⟨6, some 7, 6⟩]))
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨4, none, 3⟩, ⟨3, some 5, 4⟩, ⟨6, some 7, 6⟩]))))))
                                        (.split false ⟨.spoke, 1, 6, false⟩
                                          (.split false ⟨.spoke, 3, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                            (.split false ⟨.spoke, 4, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 4⟩, ⟨6, none, 4⟩, ⟨5, some 7, 6⟩]))
                                              (.split false ⟨.hat, 1, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨4, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨3, some 5, 4⟩]))
                                                (.split false ⟨.hat, 3, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨4, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨3, some 5, 4⟩]))
                                                  (.split false ⟨.hat, 4, 5, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨6, none, 4⟩, ⟨3, some 4, 3⟩, ⟨5, some 7, 7⟩]))
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩])))))))
                                          (.split false ⟨.hat, 2, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨6, none, 4⟩, ⟨1, some 7, 4⟩, ⟨2, some 5, 5⟩, ⟨3, some 4, 4⟩]))
                                            (.split false ⟨.hat, 5, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, some 6, 4⟩, ⟨5, some 7, 6⟩, ⟨2, some 3, 5⟩, ⟨2, some 4, 6⟩, ⟨3, some 4, 4⟩]))
                                              (.split false ⟨.spoke, 3, 6, false⟩
                                                (.split false ⟨.spoke, 4, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩]))
                                                  (.split false ⟨.fan1, 4, 5, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.hat, 1, 5, false⟩
                                                      (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨6, none, 4⟩, ⟨0, some 1, 3⟩, ⟨5, some 7, 7⟩]))
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 2⟩])))))
                                                (.split false ⟨.hat, 1, 5, true⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨3, none, 0⟩, ⟨7, none, 2⟩, ⟨2, some 5, 7⟩, ⟨4, some 6, 7⟩]))
                                                  (.split false ⟨.spoke, 4, 6, false⟩
                                                    (.terminal (.hubcap [⟨3, none, 0⟩, ⟨6, none, 4⟩, ⟨0, some 1, 3⟩, ⟨2, some 4, 7⟩, ⟨5, some 7, 6⟩]))
                                                    (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 0⟩, ⟨4, none, 3⟩, ⟨6, none, 4⟩, ⟨0, some 1, 3⟩, ⟨5, some 7, 7⟩]))))))))))))
                                (.split true ⟨.spoke, 1, 7, false⟩
                                  (.split false ⟨.spoke, 0, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨3, some 4, 4⟩]))
                                    (.split false ⟨.spoke, 3, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩]))
                                      (.split false ⟨.spoke, 4, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨6, none, 5⟩, ⟨7, none, 4⟩, ⟨4, some 5, 6⟩]))
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨4, none, 3⟩, ⟨7, none, 4⟩, ⟨2, some 6, 6⟩, ⟨3, some 5, 4⟩])))))
                                  (.split false ⟨.spoke, 3, 7, false⟩
                                    (.similar 0 ⟨true, 3⟩)
                                    (.split true ⟨.spoke, 0, 6, false⟩
                                      (.split false ⟨.spoke, 1, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨2, some 5, 5⟩, ⟨3, some 4, 4⟩]))
                                        (.split false ⟨.hat, 2, 6, false⟩
                                          (.terminal (.hubcap [⟨1, none, 0⟩, ⟨7, none, 3⟩, ⟨0, some 6, 8⟩, ⟨2, some 5, 5⟩, ⟨3, some 4, 4⟩]))
                                          (.split true ⟨.hat, 1, 5, true⟩
                                            (.split false ⟨.hat, 7, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.spoke, 3, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 2⟩]))
                                                (.terminal (.hubcap [⟨1, none, 0⟩, ⟨7, none, 2⟩, ⟨0, some 2, 7⟩, ⟨3, some 5, 4⟩, ⟨4, some 6, 7⟩]))))
                                            (.split false ⟨.hat, 7, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 2⟩, ⟨2, some 5, 7⟩, ⟨3, some 4, 4⟩]))
                                              (.split false ⟨.spoke, 3, 6, false⟩
                                                (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨0, some 5, 6⟩]))
                                                (.split false ⟨.spoke, 4, 6, false⟩
                                                  (.split false ⟨.hat, 4, 5, true⟩
                                                    (.similar 0 ⟨true, 3⟩)
                                                    (.split false ⟨.hat, 1, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩]))
                                                      (.split false ⟨.hat, 3, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩]))
                                                        (.split false ⟨.hat, 4, 6, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩]))
                                                          (.split false ⟨.hat, 5, 5, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩]))
                                                            (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 3⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨0, some 5, 5⟩])))))))
                                                  (.split false ⟨.hat, 1, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 6, 8⟩, ⟨3, some 5, 4⟩]))
                                                    (.split false ⟨.hat, 3, 5, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨4, none, 3⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨3, some 5, 4⟩]))
                                                      (.split false ⟨.hat, 4, 5, false⟩
                                                        (.terminal (.hubcap [⟨1, none, 0⟩, ⟨7, none, 3⟩, ⟨0, some 5, 6⟩, ⟨2, some 6, 8⟩, ⟨3, some 4, 3⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 4⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩])))))))))))
                                      (.split false ⟨.spoke, 4, 6, false⟩
                                        (.similar 0 ⟨true, 3⟩)
                                        (.split false ⟨.fan1, 0, 5, true⟩
                                          (.split false ⟨.hat, 0, 6, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.spoke, 1, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨3, some 4, 4⟩]))
                                              (.split false ⟨.spoke, 3, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨5, none, 4⟩, ⟨1, some 6, 6⟩, ⟨2, some 7, 4⟩]))
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨4, none, 3⟩, ⟨1, some 7, 4⟩, ⟨2, some 6, 7⟩, ⟨3, some 5, 4⟩])))))
                                          (.split false ⟨.fan1, 4, 5, true⟩
                                            (.split false ⟨.hat, 5, 6, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.spoke, 1, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨7, none, 4⟩, ⟨3, some 5, 4⟩, ⟨4, some 6, 6⟩]))
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 3⟩, ⟨1, some 7, 4⟩, ⟨3, some 5, 4⟩, ⟨4, some 6, 6⟩]))))
                                            (.split true ⟨.spoke, 1, 6, false⟩
                                              (.split false ⟨.spoke, 3, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨6, none, 5⟩, ⟨5, some 7, 7⟩]))
                                                (.split false ⟨.hat, 1, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨2, some 6, 6⟩, ⟨5, some 7, 7⟩]))
                                                  (.split false ⟨.hat, 3, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨6, none, 5⟩, ⟨5, some 7, 7⟩]))
                                                    (.split false ⟨.hat, 3, 5, true⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, some 6, 6⟩, ⟨3, some 4, 3⟩, ⟨5, some 7, 7⟩]))
                                                      (.split false ⟨.hat, 4, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨6, none, 5⟩, ⟨3, some 4, 3⟩, ⟨5, some 7, 7⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩])))))))
                                              (.split false ⟨.spoke, 3, 6, false⟩
                                                (.similar 0 ⟨true, 3⟩)
                                                (.split false ⟨.hat, 1, 5, true⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 3⟩, ⟨4, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 2⟩, ⟨3, some 5, 4⟩]))
                                                  (.split false ⟨.hat, 2, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨4, none, 3⟩, ⟨1, some 7, 4⟩, ⟨2, some 6, 6⟩, ⟨3, some 5, 4⟩]))
                                                    (.split false ⟨.hat, 3, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨4, none, 3⟩, ⟨1, some 7, 4⟩, ⟨2, some 6, 6⟩, ⟨3, some 5, 4⟩]))
                                                      (.split false ⟨.hat, 3, 5, true⟩
                                                        (.terminal (.hubcap [⟨0, some 1, 3⟩, ⟨2, some 6, 7⟩, ⟨3, some 4, 3⟩, ⟨5, some 7, 7⟩]))
                                                        (.split false ⟨.hat, 4, 5, false⟩
                                                          (.terminal (.hubcap [⟨2, none, 2⟩, ⟨6, none, 5⟩, ⟨0, some 1, 3⟩, ⟨3, some 4, 3⟩, ⟨5, some 7, 7⟩]))
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩])))))))))))))))))))
                        (.split true ⟨.hat, 6, 5, false⟩
                          (.split false ⟨.spoke, 0, 7, false⟩
                            (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨3, some 4, 5⟩]))
                            (.split false ⟨.spoke, 1, 7, false⟩
                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 3⟩, ⟨4, some 5, 6⟩]))
                              (.split false ⟨.spoke, 3, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 2, 3⟩]))
                                (.split false ⟨.spoke, 4, 7, false⟩
                                  (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩]))
                                  (.split true ⟨.spoke, 1, 6, false⟩
                                    (.split false ⟨.spoke, 0, 6, false⟩
                                      (.terminal (.hubcap [⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨0, some 1, 4⟩, ⟨2, some 3, 3⟩, ⟨4, some 5, 6⟩]))
                                      (.split false ⟨.hat, 2, 5, true⟩
                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 3⟩, ⟨4, some 5, 6⟩]))
                                        (.split false ⟨.spoke, 3, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 3⟩, ⟨6, none, 4⟩, ⟨1, some 7, 5⟩, ⟨4, some 5, 5⟩]))
                                          (.split false ⟨.spoke, 4, 6, true⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨6, none, 4⟩, ⟨1, some 7, 5⟩, ⟨2, some 3, 3⟩, ⟨4, some 5, 5⟩]))
                                            (.split false ⟨.hat, 1, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨1, some 7, 4⟩, ⟨3, some 4, 5⟩]))
                                              (.split false ⟨.hat, 3, 5, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨1, some 7, 5⟩, ⟨3, some 4, 4⟩]))
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨1, some 7, 5⟩, ⟨2, some 3, 3⟩]))))))))
                                    (.split false ⟨.hat, 1, 5, true⟩
                                      (.terminal (.hubcap [⟨6, none, 3⟩, ⟨7, none, 2⟩, ⟨0, some 1, 5⟩, ⟨2, some 5, 5⟩, ⟨3, some 4, 5⟩]))
                                      (.split false ⟨.spoke, 4, 6, false⟩
                                        (.split false ⟨.spoke, 3, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 2, 3⟩, ⟨3, some 4, 4⟩]))
                                          (.split false ⟨.hat, 2, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨1, some 7, 4⟩, ⟨3, some 4, 5⟩]))
                                            (.split false ⟨.hat, 3, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 4⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨2, some 7, 5⟩]))
                                              (.split false ⟨.hat, 4, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨1, some 2, 4⟩, ⟨3, some 7, 5⟩]))
                                                (.split false ⟨.hat, 5, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨3, some 4, 4⟩, ⟨1, some 2, 4⟩, ⟨1, some 7, 5⟩, ⟨2, some 7, 6⟩]))
                                                  (.split false ⟨.hat, 6, 6, true⟩
                                                    (.terminal (.hubcap [⟨5, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 6, 6⟩, ⟨1, some 2, 4⟩, ⟨3, some 4, 5⟩]))
                                                    (.split false ⟨.hat, 7, 5, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨1, some 2, 4⟩, ⟨3, some 4, 5⟩]))
                                                      (.split false ⟨.fan1, 6, 5, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.spoke, 0, 6, true⟩
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 2⟩, ⟨5, none, 2⟩, ⟨7, none, 4⟩, ⟨1, some 6, 5⟩, ⟨3, some 4, 4⟩]))
                                                          (.split false ⟨.hat, 1, 6, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨1, some 2, 4⟩, ⟨3, some 4, 5⟩]))
                                                            (.split false ⟨.hat, 2, 5, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨1, some 2, 3⟩, ⟨3, some 4, 5⟩]))
                                                              (.split false ⟨.hat, 3, 5, false⟩
                                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨1, some 4, 5⟩, ⟨2, some 3, 3⟩]))
                                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩]))))))))))))))
                                        (.split false ⟨.hat, 2, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨2, some 3, 3⟩, ⟨4, some 5, 5⟩]))
                                          (.split false ⟨.hat, 3, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨6, none, 4⟩, ⟨1, some 3, 3⟩, ⟨2, some 7, 5⟩, ⟨4, some 5, 5⟩]))
                                            (.split false ⟨.hat, 5, 5, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 2, 3⟩, ⟨3, some 4, 4⟩]))
                                              (.split false ⟨.fan1, 4, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.spoke, 3, 6, true⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨1, some 2, 3⟩, ⟨3, some 7, 5⟩]))
                                                  (.split false ⟨.hat, 7, 5, false⟩
                                                    (.similar 0 ⟨true, 3⟩)
                                                    (.split false ⟨.fan1, 6, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.hat, 2, 5, true⟩
                                                        (.terminal (.hubcap [⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨0, some 1, 4⟩, ⟨2, some 3, 4⟩]))
                                                        (.split false ⟨.spoke, 0, 6, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨1, some 2, 2⟩]))
                                                          (.split false ⟨.fan1, 2, 5, true⟩
                                                            (.terminal .reducible)
                                                            (.split false ⟨.hat, 1, 6, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 2, 1⟩]))
                                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨1, some 7, 5⟩]))))))))))))))))))))
                          (.split false ⟨.hat, 7, 5, false⟩
                            (.similar 0 ⟨true, 3⟩)
                            (.split false ⟨.fan1, 6, 6, true⟩
                              (.terminal .reducible)
                              (.split false ⟨.spoke, 3, 7, false⟩
                                (.terminal (.hubcap [⟨3, none, 0⟩, ⟨6, none, 5⟩, ⟨0, some 4, 5⟩, ⟨1, some 2, 3⟩, ⟨5, some 7, 7⟩]))
                                (.split false ⟨.spoke, 4, 7, false⟩
                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨4, none, 0⟩, ⟨5, none, 3⟩, ⟨6, none, 5⟩, ⟨1, some 7, 5⟩, ⟨2, some 3, 4⟩]))
                                  (.split false ⟨.spoke, 0, 7, false⟩
                                    (.terminal (.hubcap [⟨0, none, 0⟩, ⟨4, none, 3⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨1, some 2, 4⟩, ⟨3, some 5, 5⟩]))
                                    (.split false ⟨.spoke, 1, 7, false⟩
                                      (.terminal (.hubcap [⟨1, none, 0⟩, ⟨6, none, 5⟩, ⟨0, some 4, 5⟩, ⟨2, some 3, 3⟩, ⟨5, some 7, 7⟩]))
                                      (.split true ⟨.hat, 1, 5, true⟩
                                        (.split false ⟨.spoke, 1, 6, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.spoke, 3, 6, false⟩
                                            (.terminal (.hubcap [⟨2, none, 0⟩, ⟨6, none, 5⟩, ⟨0, some 1, 4⟩, ⟨3, some 4, 4⟩, ⟨5, some 7, 7⟩]))
                                            (.split false ⟨.hat, 4, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.hat, 3, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨6, none, 5⟩, ⟨3, some 4, 3⟩, ⟨5, some 7, 7⟩]))
                                                (.split false ⟨.hat, 5, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨4, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 5⟩, ⟨1, some 7, 5⟩, ⟨2, some 3, 3⟩]))
                                                  (.split false ⟨.hat, 0, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 2⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨2, some 4, 4⟩, ⟨3, some 5, 5⟩]))
                                                    (.split false ⟨.fan1, 1, 5, true⟩
                                                      (.terminal (.hubcap [⟨1, none, 1⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨0, some 4, 5⟩, ⟨2, some 3, 3⟩, ⟨2, some 5, 5⟩, ⟨3, some 5, 5⟩]))
                                                      (.split false ⟨.spoke, 0, 6, false⟩
                                                        (.terminal (.hubcap [⟨1, none, 2⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨0, some 4, 4⟩, ⟨2, some 3, 3⟩, ⟨2, some 5, 5⟩, ⟨3, some 5, 5⟩]))
                                                        (.split false ⟨.hat, 2, 5, true⟩
                                                          (.terminal .reducible)
                                                          (.split false ⟨.fan1, 0, 6, true⟩
                                                            (.terminal .reducible)
                                                            (.split false ⟨.spoke, 4, 6, true⟩
                                                              (.terminal (.hubcap [⟨2, none, 1⟩, ⟨6, none, 5⟩, ⟨0, some 1, 4⟩, ⟨3, some 4, 3⟩, ⟨5, some 7, 7⟩]))
                                                              (.split false ⟨.hat, 3, 5, false⟩
                                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 5⟩, ⟨2, some 3, 1⟩, ⟨4, some 7, 6⟩]))
                                                                (.split false ⟨.fan1, 3, 5, true⟩
                                                                  (.terminal .reducible)
                                                                  (.split false ⟨.hat, 4, 6, false⟩
                                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 5⟩, ⟨1, some 7, 5⟩, ⟨3, some 4, 3⟩]))
                                                                    (.split false ⟨.hat, 5, 5, false⟩
                                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 3⟩, ⟨7, none, 4⟩, ⟨1, some 6, 6⟩]))
                                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩])))))))))))))))))
                                        (.split false ⟨.hat, 4, 5, true⟩
                                          (.similar 0 ⟨true, 3⟩)
                                          (.split true ⟨.spoke, 0, 6, true⟩
                                            (.split false ⟨.hat, 2, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.spoke, 4, 6, true⟩
                                                (.terminal (.hubcap [⟨1, none, 1⟩, ⟨6, none, 5⟩, ⟨0, some 4, 5⟩, ⟨2, some 3, 2⟩, ⟨5, some 7, 7⟩]))
                                                (.split false ⟨.spoke, 3, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 5⟩, ⟨1, some 2, 2⟩, ⟨4, some 7, 5⟩]))
                                                  (.split false ⟨.hat, 3, 5, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 5⟩, ⟨2, some 3, 2⟩, ⟨4, some 7, 6⟩]))
                                                    (.split false ⟨.hat, 4, 6, false⟩
                                                      (.terminal (.hubcap [⟨5, none, 3⟩, ⟨6, none, 5⟩, ⟨0, some 1, 4⟩, ⟨2, some 3, 3⟩, ⟨4, some 7, 5⟩]))
                                                      (.split false ⟨.hat, 5, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨4, none, 1⟩, ⟨5, none, 3⟩, ⟨7, none, 4⟩, ⟨1, some 6, 6⟩, ⟨2, some 3, 3⟩]))
                                                        (.split false ⟨.hat, 0, 5, true⟩
                                                          (.terminal .reducible)
                                                          (.split false ⟨.fan1, 2, 5, true⟩
                                                            (.terminal .reducible)
                                                            (.split false ⟨.spoke, 1, 6, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩]))
                                                              (.split false ⟨.hat, 1, 6, false⟩
                                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩]))
                                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨3, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨2, some 4, 4⟩]))))))))))))
                                            (.split false ⟨.spoke, 4, 6, true⟩
                                              (.similar 0 ⟨true, 3⟩)
                                              (.split false ⟨.spoke, 3, 6, false⟩
                                                (.terminal (.hubcap [⟨3, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨0, some 4, 4⟩, ⟨1, some 2, 3⟩]))
                                                (.split false ⟨.spoke, 1, 6, false⟩
                                                  (.terminal (.hubcap [⟨1, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨0, some 4, 4⟩, ⟨2, some 3, 3⟩]))
                                                  (.split false ⟨.hat, 2, 5, false⟩
                                                    (.terminal (.hubcap [⟨1, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨0, some 4, 4⟩, ⟨2, some 3, 3⟩]))
                                                    (.split false ⟨.hat, 3, 5, false⟩
                                                      (.terminal (.hubcap [⟨1, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨0, some 4, 4⟩, ⟨2, some 3, 3⟩]))
                                                      (.terminal (.hubcap [⟨1, none, 1⟩, ⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 5⟩, ⟨7, none, 3⟩, ⟨0, some 4, 4⟩])))))))))))))))))))
                    (.split false ⟨.spoke, 0, 7, false⟩
                      (.terminal (.hubcap [⟨0, none, 0⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 2⟩, ⟨1, some 2, 4⟩, ⟨3, some 4, 7⟩]))
                      (.split false ⟨.spoke, 2, 7, false⟩
                        (.terminal (.hubcap [⟨2, none, 0⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨0, some 1, 5⟩, ⟨3, some 4, 5⟩]))
                        (.split false ⟨.spoke, 4, 7, false⟩
                          (.terminal (.hubcap [⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨0, some 1, 7⟩, ⟨2, some 3, 4⟩]))
                          (.split false ⟨.spoke, 6, 7, false⟩
                            (.split false ⟨.spoke, 1, 7, false⟩
                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩, ⟨3, some 4, 7⟩]))
                              (.split false ⟨.spoke, 3, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩, ⟨1, some 2, 5⟩]))
                                (.split true ⟨.hat, 5, 5, false⟩
                                  (.split false ⟨.spoke, 0, 6, false⟩
                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩, ⟨7, none, 2⟩, ⟨1, some 2, 4⟩, ⟨3, some 4, 6⟩]))
                                    (.split false ⟨.spoke, 1, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨7, none, 3⟩, ⟨1, some 6, 5⟩, ⟨2, some 3, 4⟩]))
                                      (.split false ⟨.spoke, 2, 6, false⟩
                                        (.terminal (.hubcap [⟨2, none, 4⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 1, 5⟩, ⟨3, some 4, 4⟩]))
                                        (.split false ⟨.spoke, 3, 6, false⟩
                                          (.split false ⟨.spoke, 4, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩, ⟨3, some 4, 3⟩]))
                                            (.split false ⟨.spoke, 6, 8, false⟩
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 0⟩, ⟨7, none, 3⟩, ⟨3, some 4, 5⟩]))
                                              (.split false ⟨.hat, 1, 5, false⟩
                                                (.terminal (.hubcap [⟨5, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 6, 5⟩, ⟨1, some 2, 5⟩, ⟨3, some 4, 5⟩]))
                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨5, none, 2⟩, ⟨7, none, 3⟩, ⟨2, some 6, 3⟩, ⟨3, some 4, 5⟩])))))
                                          (.split false ⟨.spoke, 6, 8, false⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨2, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 0⟩, ⟨7, none, 3⟩, ⟨1, some 3, 5⟩]))
                                            (.split false ⟨.spoke, 4, 6, false⟩
                                              (.split false ⟨.hat, 1, 5, false⟩
                                                (.terminal (.hubcap [⟨5, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 6, 5⟩, ⟨1, some 2, 6⟩, ⟨3, some 4, 4⟩]))
                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩, ⟨3, some 4, 3⟩])))
                                              (.split false ⟨.hat, 1, 5, false⟩
                                                (.terminal (.hubcap [⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 6, 5⟩, ⟨1, some 2, 5⟩, ⟨1, some 3, 5⟩, ⟨2, some 3, 5⟩]))
                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩, ⟨3, some 4, 4⟩])))))))))
                                  (.split false ⟨.hat, 0, 5, false⟩
                                    (.similar 0 ⟨true, 3⟩)
                                    (.split true ⟨.spoke, 0, 6, false⟩
                                      (.split false ⟨.spoke, 1, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 1⟩, ⟨7, none, 2⟩, ⟨3, some 4, 7⟩]))
                                        (.split false ⟨.spoke, 2, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨2, none, 4⟩, ⟨3, none, 2⟩, ⟨4, none, 4⟩, ⟨5, none, 3⟩, ⟨6, none, 1⟩, ⟨7, none, 2⟩]))
                                          (.split false ⟨.spoke, 3, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 1⟩, ⟨7, none, 2⟩, ⟨3, some 4, 6⟩]))
                                            (.split false ⟨.spoke, 4, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 4⟩, ⟨5, none, 2⟩, ⟨6, none, 1⟩, ⟨7, none, 2⟩]))
                                              (.split false ⟨.fan1, 4, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.spoke, 6, 8, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨2, none, 3⟩, ⟨4, none, 4⟩, ⟨5, none, 3⟩, ⟨6, none, 0⟩, ⟨7, none, 2⟩, ⟨1, some 3, 4⟩]))
                                                  (.split false ⟨.hat, 1, 5, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨4, none, 4⟩, ⟨5, none, 3⟩, ⟨6, none, 1⟩, ⟨7, none, 2⟩, ⟨2, some 3, 5⟩]))
                                                    (.split false ⟨.hat, 2, 5, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨5, none, 3⟩, ⟨6, none, 1⟩, ⟨7, none, 2⟩, ⟨1, some 2, 3⟩, ⟨3, some 4, 7⟩]))
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 4⟩, ⟨5, none, 3⟩, ⟨6, none, 1⟩, ⟨7, none, 2⟩]))))))))))
                                      (.split false ⟨.spoke, 4, 6, false⟩
                                        (.similar 0 ⟨true, 3⟩)
                                        (.split false ⟨.fan1, 0, 5, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.fan1, 4, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.spoke, 2, 6, false⟩
                                              (.terminal (.hubcap [⟨2, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 1⟩, ⟨7, none, 3⟩, ⟨0, some 1, 5⟩, ⟨3, some 4, 5⟩]))
                                              (.split true ⟨.spoke, 1, 6, false⟩
                                                (.split false ⟨.spoke, 3, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 0⟩, ⟨5, none, 3⟩, ⟨6, none, 1⟩, ⟨7, none, 3⟩, ⟨3, some 4, 6⟩]))
                                                  (.split false ⟨.hat, 3, 5, false⟩
                                                    (.terminal (.hubcap [⟨4, none, 4⟩, ⟨5, none, 3⟩, ⟨6, none, 1⟩, ⟨7, none, 3⟩, ⟨0, some 1, 6⟩, ⟨2, some 3, 3⟩]))
                                                    (.split false ⟨.hat, 2, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 1⟩, ⟨7, none, 3⟩, ⟨1, some 2, 3⟩, ⟨3, some 4, 7⟩]))
                                                      (.split false ⟨.hat, 4, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 1⟩, ⟨7, none, 3⟩, ⟨2, some 3, 3⟩]))
                                                        (.split false ⟨.hat, 6, 5, false⟩
                                                          (.split false ⟨.spoke, 6, 8, false⟩
                                                            (.terminal (.hubcap [⟨2, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 0⟩, ⟨7, none, 3⟩, ⟨0, some 1, 6⟩, ⟨3, some 4, 6⟩]))
                                                            (.split false ⟨.hat, 1, 6, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 1⟩, ⟨7, none, 3⟩, ⟨3, some 4, 6⟩]))
                                                              (.split false ⟨.hat, 1, 5, true⟩
                                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 1⟩, ⟨5, none, 3⟩, ⟨7, none, 3⟩, ⟨1, some 6, 4⟩, ⟨3, some 4, 6⟩]))
                                                                (.split false ⟨.hat, 2, 5, false⟩
                                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 1⟩, ⟨7, none, 3⟩, ⟨3, some 4, 6⟩]))
                                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 2⟩, ⟨5, none, 3⟩, ⟨7, none, 3⟩, ⟨1, some 6, 4⟩, ⟨3, some 4, 5⟩]))))))
                                                          (.split false ⟨.fan1, 3, 6, true⟩
                                                            (.terminal .reducible)
                                                            (.split false ⟨.spoke, 6, 8, false⟩
                                                              (.terminal (.hubcap [⟨2, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 0⟩, ⟨7, none, 3⟩, ⟨0, some 1, 6⟩, ⟨3, some 4, 7⟩]))
                                                              (.split false ⟨.hat, 1, 6, false⟩
                                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 1⟩, ⟨7, none, 3⟩, ⟨3, some 4, 7⟩]))
                                                                (.split false ⟨.hat, 2, 5, true⟩
                                                                  (.terminal (.hubcap [⟨2, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 1⟩, ⟨7, none, 3⟩, ⟨0, some 1, 6⟩, ⟨3, some 4, 6⟩]))
                                                                  (.split false ⟨.hat, 1, 5, false⟩
                                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 1⟩, ⟨7, none, 3⟩, ⟨3, some 4, 7⟩]))
                                                                    (.split false ⟨.fan1, 0, 6, true⟩
                                                                      (.terminal .reducible)
                                                                      (.split false ⟨.hat, 7, 5, true⟩
                                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 1⟩, ⟨7, none, 3⟩, ⟨3, some 4, 7⟩]))
                                                                        (.split false ⟨.hat, 4, 5, false⟩
                                                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 1⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 1⟩, ⟨7, none, 3⟩, ⟨1, some 3, 7⟩]))
                                                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨2, none, 1⟩, ⟨4, none, 4⟩, ⟨5, none, 3⟩, ⟨6, none, 1⟩, ⟨7, none, 3⟩, ⟨1, some 3, 6⟩])))))))))))))))
                                                (.split false ⟨.spoke, 3, 6, false⟩
                                                  (.similar 0 ⟨true, 3⟩)
                                                  (.split false ⟨.hat, 1, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 1⟩, ⟨7, none, 3⟩, ⟨1, some 4, 5⟩, ⟨2, some 3, 5⟩]))
                                                    (.split false ⟨.hat, 1, 5, true⟩
                                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨2, none, 2⟩, ⟨4, none, 4⟩, ⟨5, none, 3⟩, ⟨6, none, 1⟩, ⟨7, none, 3⟩, ⟨1, some 3, 3⟩]))
                                                      (.split false ⟨.spoke, 6, 8, false⟩
                                                        (.terminal (.hubcap [⟨2, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 0⟩, ⟨7, none, 3⟩, ⟨0, some 4, 7⟩, ⟨1, some 3, 4⟩]))
                                                        (.split false ⟨.hat, 2, 5, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 2⟩, ⟨4, none, 4⟩, ⟨5, none, 3⟩, ⟨6, none, 1⟩, ⟨7, none, 3⟩, ⟨1, some 3, 4⟩]))
                                                          (.terminal (.hubcap [⟨3, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 1⟩, ⟨7, none, 3⟩, ⟨0, some 4, 7⟩, ⟨1, some 2, 5⟩])))))))))))))))))
                            (.split false ⟨.spoke, 1, 7, false⟩
                              (.terminal (.hubcap [⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨0, some 5, 5⟩, ⟨3, some 4, 6⟩]))
                              (.split false ⟨.spoke, 3, 7, false⟩
                                (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨0, some 1, 6⟩, ⟨4, some 7, 5⟩]))
                                (.split true ⟨.hat, 6, 5, false⟩
                                  (.split false ⟨.hat, 7, 5, false⟩
                                    (.split false ⟨.hat, 1, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩, ⟨1, some 2, 4⟩, ⟨3, some 4, 6⟩]))
                                      (.split false ⟨.hat, 4, 6, false⟩
                                        (.terminal (.hubcap [⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 1, 6⟩, ⟨2, some 3, 4⟩]))
                                        (.split true ⟨.hat, 6, 6, true⟩
                                          (.split false ⟨.hat, 2, 6, false⟩
                                            (.terminal (.hubcap [⟨2, none, 2⟩, ⟨6, none, 2⟩, ⟨0, some 1, 5⟩, ⟨3, some 4, 6⟩, ⟨5, some 7, 5⟩]))
                                            (.split false ⟨.hat, 3, 6, false⟩
                                              (.terminal (.hubcap [⟨2, none, 2⟩, ⟨6, none, 2⟩, ⟨0, some 1, 6⟩, ⟨3, some 4, 5⟩, ⟨5, some 7, 5⟩]))
                                              (.split false ⟨.spoke, 0, 6, false⟩
                                                (.split false ⟨.spoke, 1, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 2⟩, ⟨7, none, 2⟩, ⟨3, some 4, 6⟩]))
                                                  (.split false ⟨.spoke, 2, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨2, none, 4⟩, ⟨5, none, 3⟩, ⟨6, none, 2⟩, ⟨7, none, 2⟩, ⟨3, some 4, 5⟩]))
                                                    (.split false ⟨.spoke, 3, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 4⟩, ⟨6, none, 2⟩, ⟨7, none, 2⟩, ⟨1, some 2, 3⟩, ⟨4, some 5, 5⟩]))
                                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨5, none, 3⟩, ⟨6, none, 2⟩, ⟨7, none, 2⟩, ⟨1, some 2, 4⟩, ⟨3, some 4, 5⟩])))))
                                                (.split false ⟨.spoke, 2, 6, false⟩
                                                  (.terminal (.hubcap [⟨6, none, 2⟩, ⟨0, some 1, 5⟩, ⟨5, some 7, 5⟩, ⟨2, some 3, 5⟩, ⟨2, some 4, 7⟩, ⟨3, some 4, 5⟩]))
                                                  (.split false ⟨.hat, 0, 5, false⟩
                                                    (.split false ⟨.spoke, 1, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 2⟩, ⟨7, none, 2⟩, ⟨3, some 4, 6⟩]))
                                                      (.split false ⟨.spoke, 3, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 4⟩, ⟨6, none, 2⟩, ⟨7, none, 2⟩, ⟨1, some 2, 4⟩, ⟨4, some 5, 5⟩]))
                                                        (.terminal (.hubcap [⟨2, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 2⟩, ⟨7, none, 2⟩, ⟨0, some 1, 5⟩, ⟨3, some 4, 5⟩]))))
                                                    (.split false ⟨.fan1, 0, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.spoke, 3, 6, false⟩
                                                        (.terminal (.hubcap [⟨2, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 1, 6⟩, ⟨3, some 4, 5⟩]))
                                                        (.split false ⟨.spoke, 1, 6, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩, ⟨3, some 4, 5⟩]))
                                                          (.terminal (.hubcap [⟨2, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 1, 5⟩, ⟨3, some 4, 5⟩]))))))))))
                                          (.split false ⟨.hat, 7, 6, true⟩
                                            (.similar 0 ⟨true, 3⟩)
                                            (.split false ⟨.spoke, 3, 6, false⟩
                                              (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨6, none, 0⟩, ⟨7, none, 3⟩, ⟨0, some 1, 6⟩, ⟨4, some 5, 5⟩]))
                                              (.split false ⟨.spoke, 4, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨5, none, 2⟩, ⟨6, none, 0⟩, ⟨7, none, 3⟩, ⟨1, some 2, 6⟩, ⟨3, some 4, 5⟩]))
                                                (.split false ⟨.spoke, 0, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨5, none, 3⟩, ⟨6, none, 0⟩, ⟨7, none, 2⟩, ⟨1, some 2, 4⟩, ⟨3, some 4, 6⟩]))
                                                  (.split false ⟨.spoke, 1, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 0⟩, ⟨7, none, 3⟩, ⟨3, some 4, 6⟩]))
                                                    (.split false ⟨.spoke, 2, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 0⟩, ⟨7, none, 3⟩, ⟨3, some 4, 5⟩]))
                                                      (.split false ⟨.hat, 1, 5, false⟩
                                                        (.terminal (.hubcap [⟨5, none, 3⟩, ⟨6, none, 0⟩, ⟨7, none, 3⟩, ⟨0, some 4, 7⟩, ⟨1, some 2, 5⟩, ⟨1, some 3, 5⟩, ⟨2, some 3, 5⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 0⟩, ⟨7, none, 3⟩, ⟨3, some 4, 5⟩]))))))))))))
                                    (.split false ⟨.hat, 3, 6, false⟩
                                      (.terminal (.hubcap [⟨6, none, 3⟩, ⟨3, some 4, 5⟩, ⟨5, some 7, 5⟩, ⟨0, some 1, 6⟩, ⟨0, some 2, 5⟩, ⟨1, some 2, 4⟩]))
                                      (.split false ⟨.hat, 4, 6, false⟩
                                        (.terminal (.hubcap [⟨4, none, 2⟩, ⟨6, none, 3⟩, ⟨0, some 1, 6⟩, ⟨2, some 3, 4⟩, ⟨5, some 7, 5⟩]))
                                        (.split false ⟨.spoke, 2, 6, false⟩
                                          (.split false ⟨.spoke, 0, 6, false⟩
                                            (.terminal (.hubcap [⟨1, none, 0⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 2⟩, ⟨0, some 2, 7⟩, ⟨3, some 4, 5⟩]))
                                            (.split false ⟨.spoke, 1, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨6, none, 3⟩, ⟨3, some 4, 5⟩, ⟨5, some 7, 5⟩]))
                                              (.split false ⟨.hat, 1, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.spoke, 3, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨6, none, 3⟩, ⟨5, some 7, 5⟩]))
                                                  (.split false ⟨.spoke, 4, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨3, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 4, 7⟩]))
                                                    (.split false ⟨.hat, 1, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 4⟩, ⟨6, none, 3⟩, ⟨5, some 7, 5⟩]))
                                                      (.split false ⟨.hat, 2, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨6, none, 3⟩, ⟨3, some 4, 5⟩, ⟨5, some 7, 5⟩]))
                                                        (.split false ⟨.hat, 3, 5, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨6, none, 3⟩, ⟨3, some 4, 5⟩, ⟨5, some 7, 5⟩]))
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨6, none, 3⟩, ⟨3, some 4, 4⟩, ⟨5, some 7, 5⟩]))))))))))
                                          (.split false ⟨.spoke, 0, 6, false⟩
                                            (.split false ⟨.spoke, 1, 6, false⟩
                                              (.terminal (.hubcap [⟨2, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 2⟩, ⟨0, some 1, 4⟩, ⟨3, some 4, 6⟩]))
                                              (.split false ⟨.spoke, 3, 6, false⟩
                                                (.terminal (.hubcap [⟨6, none, 3⟩, ⟨7, none, 2⟩, ⟨0, some 2, 5⟩, ⟨1, some 3, 5⟩, ⟨4, some 5, 5⟩]))
                                                (.split false ⟨.spoke, 4, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 2⟩, ⟨1, some 2, 4⟩, ⟨3, some 4, 5⟩]))
                                                  (.split false ⟨.hat, 1, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 2⟩, ⟨1, some 2, 4⟩, ⟨3, some 4, 6⟩]))
                                                    (.split false ⟨.hat, 2, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 2⟩, ⟨3, some 4, 6⟩]))
                                                      (.split false ⟨.hat, 2, 5, true⟩
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 2⟩, ⟨1, some 2, 4⟩, ⟨3, some 4, 5⟩]))
                                                        (.split false ⟨.fan1, 2, 5, true⟩
                                                          (.terminal .reducible)
                                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 2⟩, ⟨1, some 2, 3⟩, ⟨3, some 4, 5⟩])))))))))
                                            (.split false ⟨.hat, 0, 5, false⟩
                                              (.split false ⟨.spoke, 1, 6, true⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 2⟩, ⟨1, some 2, 4⟩, ⟨3, some 4, 6⟩]))
                                                (.split false ⟨.spoke, 3, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨2, none, 0⟩, ⟨3, none, 4⟩, ⟨6, none, 3⟩, ⟨7, none, 2⟩, ⟨4, some 5, 5⟩]))
                                                  (.split false ⟨.spoke, 4, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 2⟩, ⟨3, some 4, 5⟩]))
                                                    (.split false ⟨.hat, 1, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 2⟩, ⟨3, some 4, 6⟩]))
                                                      (.split false ⟨.hat, 2, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 2⟩, ⟨3, some 4, 6⟩]))
                                                        (.split false ⟨.hat, 3, 5, false⟩
                                                          (.terminal (.hubcap [⟨4, none, 4⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 2⟩, ⟨0, some 1, 5⟩, ⟨2, some 3, 3⟩]))
                                                          (.split false ⟨.hat, 1, 5, true⟩
                                                            (.terminal (.hubcap [⟨2, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 2⟩, ⟨0, some 1, 5⟩, ⟨3, some 4, 6⟩]))
                                                            (.split false ⟨.hat, 2, 5, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 2⟩, ⟨3, some 4, 6⟩]))
                                                              (.terminal (.hubcap [⟨2, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 2⟩, ⟨0, some 1, 5⟩, ⟨3, some 4, 5⟩]))))))))))
                                              (.split false ⟨.fan1, 0, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.spoke, 3, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨3, some 4, 5⟩]))
                                                  (.split false ⟨.spoke, 1, 6, true⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨3, some 4, 5⟩]))
                                                    (.split false ⟨.hat, 1, 5, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨3, some 4, 5⟩]))
                                                      (.split false ⟨.fan1, 0, 6, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.hat, 2, 5, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨3, some 4, 5⟩]))
                                                          (.split false ⟨.spoke, 4, 6, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨4, none, 4⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 2⟩]))
                                                            (.split false ⟨.hat, 5, 5, true⟩
                                                              (.terminal .reducible)
                                                              (.split false ⟨.hat, 3, 5, false⟩
                                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 3⟩]))
                                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩])))))))))))))))))
                                  (.split false ⟨.hat, 7, 5, false⟩
                                    (.similar 0 ⟨true, 3⟩)
                                    (.split false ⟨.spoke, 2, 6, false⟩
                                      (.split false ⟨.hat, 1, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨6, none, 4⟩, ⟨5, some 7, 5⟩, ⟨2, some 3, 5⟩, ⟨2, some 4, 7⟩, ⟨3, some 4, 5⟩]))
                                        (.split false ⟨.hat, 4, 6, false⟩
                                          (.terminal (.hubcap [⟨3, none, 0⟩, ⟨4, none, 3⟩, ⟨6, none, 4⟩, ⟨5, some 7, 5⟩, ⟨0, some 1, 5⟩, ⟨0, some 2, 7⟩, ⟨1, some 2, 5⟩]))
                                          (.split false ⟨.hat, 5, 6, false⟩
                                            (.terminal (.hubcap [⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨0, some 7, 6⟩, ⟨1, some 2, 5⟩, ⟨3, some 4, 3⟩]))
                                            (.split false ⟨.hat, 0, 6, false⟩
                                              (.terminal (.hubcap [⟨6, none, 4⟩, ⟨7, none, 2⟩, ⟨0, some 1, 3⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 6⟩]))
                                              (.split false ⟨.fan1, 6, 5, true⟩
                                                (.split false ⟨.hat, 0, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.fan2, 6, 6, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.spoke, 0, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨6, none, 4⟩, ⟨7, none, 2⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 6⟩]))
                                                      (.split false ⟨.fan1, 0, 5, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.spoke, 1, 6, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 2⟩, ⟨4, some 5, 6⟩]))
                                                          (.terminal (.hubcap [⟨6, none, 4⟩, ⟨7, none, 2⟩, ⟨0, some 1, 3⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 6⟩])))))))
                                                (.split false ⟨.hat, 0, 5, false⟩
                                                  (.terminal (.hubcap [⟨7, none, 2⟩, ⟨0, some 1, 4⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 6⟩, ⟨4, some 6, 7⟩, ⟨5, some 6, 6⟩]))
                                                  (.split true ⟨.spoke, 0, 6, false⟩
                                                    (.split false ⟨.spoke, 1, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 4⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 2⟩]))
                                                      (.split false ⟨.spoke, 3, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 2⟩]))
                                                        (.split false ⟨.spoke, 4, 6, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨2, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 4⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 2⟩]))
                                                          (.split false ⟨.hat, 4, 5, true⟩
                                                            (.terminal .reducible)
                                                            (.split false ⟨.fan1, 3, 5, true⟩
                                                              (.terminal .reducible)
                                                              (.split false ⟨.fan1, 4, 5, true⟩
                                                                (.terminal .reducible)
                                                                (.split false ⟨.hat, 1, 5, false⟩
                                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 2⟩, ⟨2, some 3, 5⟩]))
                                                                  (.split false ⟨.hat, 2, 6, false⟩
                                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 2⟩]))
                                                                    (.split false ⟨.hat, 2, 5, true⟩
                                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 2⟩]))
                                                                      (.split false ⟨.hat, 3, 5, false⟩
                                                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 2⟩]))
                                                                        (.split false ⟨.hat, 5, 5, false⟩
                                                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨2, none, 4⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 2⟩]))
                                                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 2⟩, ⟨2, some 3, 4⟩])))))))))))))
                                                    (.split false ⟨.spoke, 4, 6, false⟩
                                                      (.similar 0 ⟨true, 3⟩)
                                                      (.split false ⟨.hat, 5, 5, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.fan1, 0, 5, true⟩
                                                          (.terminal .reducible)
                                                          (.split false ⟨.fan1, 4, 5, true⟩
                                                            (.terminal .reducible)
                                                            (.split false ⟨.spoke, 1, 6, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨3, some 4, 4⟩]))
                                                              (.split false ⟨.hat, 1, 5, true⟩
                                                                (.terminal .reducible)
                                                                (.split false ⟨.fan1, 1, 5, true⟩
                                                                  (.terminal .reducible)
                                                                  (.split false ⟨.spoke, 3, 6, false⟩
                                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩]))
                                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨3, some 4, 3⟩])))))))))))))))))
                                      (.split false ⟨.fan1, 2, 5, true⟩
                                        (.split false ⟨.spoke, 0, 6, false⟩
                                          (.split false ⟨.spoke, 1, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 2⟩, ⟨2, some 3, 3⟩, ⟨4, some 5, 6⟩]))
                                            (.split false ⟨.spoke, 3, 6, false⟩
                                              (.terminal (.hubcap [⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 2⟩, ⟨0, some 1, 5⟩, ⟨2, some 3, 3⟩]))
                                              (.terminal (.hubcap [⟨2, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 2⟩, ⟨0, some 1, 5⟩, ⟨3, some 4, 5⟩]))))
                                          (.split false ⟨.spoke, 1, 6, true⟩
                                            (.terminal (.hubcap [⟨6, none, 4⟩, ⟨0, some 1, 5⟩, ⟨5, some 7, 5⟩, ⟨2, some 3, 3⟩, ⟨2, some 4, 4⟩, ⟨3, some 4, 6⟩]))
                                            (.split false ⟨.spoke, 3, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 0⟩, ⟨4, none, 3⟩, ⟨6, none, 4⟩, ⟨1, some 3, 5⟩, ⟨5, some 7, 5⟩]))
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨6, none, 4⟩, ⟨1, some 2, 3⟩, ⟨3, some 4, 5⟩, ⟨5, some 7, 5⟩])))))
                                        (.split false ⟨.fan1, 6, 5, true⟩
                                          (.split false ⟨.hat, 0, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.fan2, 6, 6, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.spoke, 0, 6, false⟩
                                                (.terminal (.hubcap [⟨6, none, 4⟩, ⟨7, none, 2⟩, ⟨0, some 1, 3⟩, ⟨2, some 5, 5⟩, ⟨3, some 4, 6⟩]))
                                                (.split false ⟨.spoke, 3, 6, true⟩
                                                  (.terminal (.hubcap [⟨6, none, 4⟩, ⟨7, none, 2⟩, ⟨0, some 1, 5⟩, ⟨2, some 3, 3⟩, ⟨4, some 5, 6⟩]))
                                                  (.split false ⟨.spoke, 4, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 2⟩]))
                                                    (.split false ⟨.spoke, 1, 6, false⟩
                                                      (.terminal (.hubcap [⟨2, none, 0⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 2⟩, ⟨0, some 1, 5⟩, ⟨3, some 4, 6⟩]))
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 2⟩, ⟨3, some 4, 6⟩]))))))))
                                          (.split false ⟨.fan2, 6, 5, true⟩
                                            (.split false ⟨.hat, 5, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.fan1, 6, 6, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.spoke, 0, 6, false⟩
                                                  (.terminal (.hubcap [⟨2, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 2⟩, ⟨0, some 1, 4⟩, ⟨3, some 4, 5⟩]))
                                                  (.split false ⟨.spoke, 4, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨1, some 7, 6⟩, ⟨3, some 4, 3⟩]))
                                                    (.split false ⟨.spoke, 1, 6, true⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨1, some 2, 3⟩, ⟨3, some 4, 5⟩]))
                                                      (.split false ⟨.spoke, 3, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 0⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨1, some 7, 6⟩, ⟨3, some 4, 5⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨2, some 3, 2⟩]))))))))
                                            (.split true ⟨.spoke, 0, 6, false⟩
                                              (.split false ⟨.spoke, 1, 6, false⟩
                                                (.terminal (.hubcap [⟨6, none, 4⟩, ⟨7, none, 2⟩, ⟨0, some 1, 4⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 6⟩]))
                                                (.split false ⟨.spoke, 3, 6, true⟩
                                                  (.terminal (.hubcap [⟨6, none, 4⟩, ⟨7, none, 2⟩, ⟨0, some 1, 4⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 6⟩]))
                                                  (.split false ⟨.spoke, 4, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 2⟩]))
                                                    (.split false ⟨.hat, 1, 5, false⟩
                                                      (.terminal (.hubcap [⟨1, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 2⟩, ⟨0, some 2, 4⟩, ⟨3, some 4, 6⟩]))
                                                      (.terminal (.hubcap [⟨5, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 2⟩, ⟨3, some 4, 6⟩, ⟨0, some 1, 4⟩, ⟨0, some 2, 5⟩, ⟨1, some 2, 2⟩]))))))
                                              (.split false ⟨.spoke, 4, 6, false⟩
                                                (.similar 0 ⟨true, 3⟩)
                                                (.split false ⟨.spoke, 1, 6, true⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨6, none, 3⟩, ⟨1, some 2, 3⟩, ⟨3, some 4, 6⟩, ⟨5, some 7, 5⟩]))
                                                  (.split false ⟨.spoke, 3, 6, false⟩
                                                    (.terminal (.hubcap [⟨2, none, 0⟩, ⟨6, none, 3⟩, ⟨0, some 1, 6⟩, ⟨3, some 4, 6⟩, ⟨5, some 7, 5⟩]))
                                                    (.terminal (.hubcap [⟨4, none, 3⟩, ⟨6, none, 3⟩, ⟨0, some 1, 6⟩, ⟨2, some 3, 3⟩, ⟨5, some 7, 5⟩])))))))))))))))))))))
              (.split false ⟨.spoke, 1, 5, true⟩
                (.similar 0 ⟨false, 2⟩)
                (.split false ⟨.spoke, 3, 5, true⟩
                  (.split true ⟨.hat, 3, 5, false⟩
                    (.split false ⟨.spoke, 0, 7, false⟩
                      (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, some 7, 6⟩, ⟨5, some 6, 6⟩]))
                      (.split false ⟨.spoke, 4, 7, false⟩
                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 2⟩, ⟨4, none, 0⟩, ⟨7, none, 4⟩, ⟨1, some 2, 5⟩, ⟨5, some 6, 5⟩]))
                        (.split false ⟨.spoke, 5, 7, false⟩
                          (.terminal (.hubcap [⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨0, some 1, 6⟩, ⟨2, some 7, 6⟩]))
                          (.split false ⟨.spoke, 6, 7, false⟩
                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 3⟩, ⟨6, none, 0⟩, ⟨7, none, 3⟩, ⟨1, some 2, 5⟩, ⟨4, some 5, 5⟩]))
                            (.split true ⟨.spoke, 5, 6, false⟩
                              (.split false ⟨.spoke, 1, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨7, none, 4⟩, ⟨3, some 4, 5⟩, ⟨5, some 6, 6⟩]))
                                (.split false ⟨.spoke, 2, 7, false⟩
                                  (.terminal (.hubcap [⟨2, none, 0⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨3, some 4, 5⟩, ⟨5, some 6, 6⟩]))
                                  (.split false ⟨.hat, 4, 5, false⟩
                                    (.split false ⟨.spoke, 4, 6, false⟩
                                      (.terminal (.hubcap [⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨0, some 1, 6⟩, ⟨2, some 7, 6⟩, ⟨4, some 5, 3⟩]))
                                      (.split false ⟨.spoke, 6, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨1, some 2, 5⟩]))
                                        (.split false ⟨.spoke, 0, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨7, none, 3⟩, ⟨1, some 2, 4⟩, ⟨5, some 6, 6⟩]))
                                          (.split false ⟨.spoke, 1, 6, true⟩
                                            (.terminal (.hubcap [⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨0, some 1, 5⟩, ⟨2, some 6, 5⟩, ⟨5, some 7, 7⟩]))
                                            (.split false ⟨.spoke, 2, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨7, none, 4⟩, ⟨5, some 6, 6⟩]))
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨1, some 6, 6⟩, ⟨5, some 7, 7⟩])))))))
                                    (.split false ⟨.hat, 1, 6, false⟩
                                      (.terminal (.hubcap [⟨0, some 1, 4⟩, ⟨2, some 7, 6⟩, ⟨3, some 4, 5⟩, ⟨5, some 6, 5⟩]))
                                      (.split false ⟨.spoke, 1, 6, true⟩
                                        (.split false ⟨.spoke, 4, 6, false⟩
                                          (.terminal (.hubcap [⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨0, some 1, 5⟩, ⟨2, some 7, 6⟩, ⟨4, some 5, 4⟩]))
                                          (.split false ⟨.fan1, 4, 5, true⟩
                                            (.terminal .reducible)
                                            (.split false ⟨.spoke, 6, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨1, some 2, 4⟩, ⟨5, some 6, 4⟩]))
                                              (.split false ⟨.hat, 6, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.spoke, 0, 6, false⟩
                                                  (.terminal (.hubcap [⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨5, some 6, 5⟩, ⟨0, some 1, 5⟩, ⟨0, some 2, 6⟩, ⟨1, some 2, 4⟩]))
                                                  (.split false ⟨.spoke, 2, 6, true⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩]))
                                                    (.split false ⟨.hat, 2, 5, false⟩
                                                      (.terminal (.hubcap [⟨2, none, 1⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨5, some 6, 5⟩]))
                                                      (.split false ⟨.hat, 5, 5, false⟩
                                                        (.terminal (.hubcap [⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨0, some 1, 5⟩, ⟨2, some 6, 5⟩, ⟨5, some 7, 5⟩]))
                                                        (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 1, 4⟩, ⟨5, some 6, 5⟩]))))))))))
                                        (.split false ⟨.spoke, 0, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨7, none, 3⟩, ⟨3, some 4, 5⟩, ⟨5, some 6, 5⟩]))
                                          (.split false ⟨.spoke, 2, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨7, none, 4⟩, ⟨1, some 2, 3⟩, ⟨3, some 4, 5⟩, ⟨5, some 6, 5⟩]))
                                            (.split false ⟨.spoke, 6, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨7, none, 3⟩, ⟨1, some 2, 5⟩, ⟨3, some 4, 5⟩, ⟨5, some 6, 4⟩]))
                                              (.split false ⟨.hat, 2, 5, true⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨7, none, 3⟩, ⟨1, some 2, 5⟩, ⟨3, some 4, 5⟩, ⟨5, some 6, 5⟩]))
                                                (.split false ⟨.hat, 1, 5, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨7, none, 4⟩, ⟨1, some 2, 3⟩, ⟨3, some 4, 5⟩, ⟨5, some 6, 5⟩]))
                                                  (.split false ⟨.hat, 6, 5, true⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨1, some 2, 5⟩, ⟨4, some 5, 3⟩]))
                                                    (.split false ⟨.hat, 7, 5, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨7, none, 3⟩, ⟨1, some 2, 5⟩, ⟨3, some 4, 5⟩, ⟨5, some 6, 5⟩]))
                                                      (.terminal (.hubcap [⟨2, none, 2⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨3, some 4, 5⟩, ⟨5, some 6, 4⟩]))))))))))))))
                              (.split false ⟨.spoke, 1, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, some 7, 7⟩, ⟨5, some 6, 5⟩]))
                                (.split false ⟨.spoke, 2, 7, false⟩
                                  (.terminal (.hubcap [⟨2, none, 0⟩, ⟨3, none, 3⟩, ⟨0, some 1, 5⟩, ⟨4, some 7, 7⟩, ⟨5, some 6, 5⟩]))
                                  (.split false ⟨.spoke, 1, 6, false⟩
                                    (.split false ⟨.hat, 4, 5, false⟩
                                      (.similar 0 ⟨true, 1⟩)
                                      (.split false ⟨.hat, 7, 5, false⟩
                                        (.similar 0 ⟨false, 4⟩)
                                        (.split false ⟨.spoke, 4, 6, true⟩
                                          (.terminal .reducible)
                                          (.split false ⟨.spoke, 6, 6, true⟩
                                            (.terminal .reducible)
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨5, none, 0⟩, ⟨7, none, 3⟩, ⟨4, some 6, 6⟩]))))))
                                    (.split false ⟨.hat, 5, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, some 2, 4⟩, ⟨4, some 7, 5⟩, ⟨3, some 5, 4⟩, ⟨3, some 6, 6⟩, ⟨5, some 6, 5⟩]))
                                      (.split false ⟨.hat, 0, 5, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, some 2, 4⟩, ⟨3, some 7, 5⟩, ⟨4, some 5, 5⟩, ⟨4, some 6, 7⟩, ⟨5, some 6, 5⟩]))
                                        (.split false ⟨.hat, 1, 6, false⟩
                                          (.terminal (.hubcap [⟨2, none, 3⟩, ⟨0, some 3, 5⟩, ⟨1, some 7, 4⟩, ⟨4, some 5, 5⟩, ⟨4, some 6, 7⟩, ⟨5, some 6, 5⟩]))
                                          (.split false ⟨.hat, 4, 5, false⟩
                                            (.terminal (.hubcap [⟨3, none, 2⟩, ⟨0, some 1, 5⟩, ⟨2, some 7, 6⟩, ⟨4, some 5, 4⟩, ⟨4, some 6, 6⟩, ⟨5, some 6, 5⟩]))
                                            (.split false ⟨.spoke, 6, 6, true⟩
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 2⟩, ⟨1, some 2, 4⟩, ⟨4, some 7, 6⟩, ⟨5, some 6, 4⟩]))
                                              (.split false ⟨.spoke, 2, 6, true⟩
                                                (.terminal (.hubcap [⟨4, none, 4⟩, ⟨7, none, 2⟩, ⟨0, some 3, 6⟩, ⟨1, some 2, 4⟩, ⟨5, some 6, 4⟩]))
                                                (.split false ⟨.spoke, 4, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨5, none, 0⟩, ⟨7, none, 3⟩, ⟨4, some 6, 6⟩]))
                                                  (.split false ⟨.hat, 7, 5, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.fan1, 4, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.spoke, 0, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 4⟩, ⟨7, none, 2⟩, ⟨5, some 6, 4⟩]))
                                                        (.split false ⟨.fan1, 0, 5, true⟩
                                                          (.terminal .reducible)
                                                          (.split false ⟨.hat, 1, 5, true⟩
                                                            (.terminal (.hubcap [⟨1, none, 1⟩, ⟨3, none, 3⟩, ⟨4, none, 4⟩, ⟨7, none, 3⟩, ⟨0, some 2, 5⟩, ⟨5, some 6, 4⟩]))
                                                            (.split false ⟨.hat, 2, 5, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 1⟩, ⟨3, none, 3⟩, ⟨4, none, 4⟩, ⟨7, none, 3⟩, ⟨5, some 6, 4⟩]))
                                                              (.split false ⟨.hat, 5, 5, false⟩
                                                                (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 1, 4⟩, ⟨4, some 5, 4⟩]))
                                                                (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 4⟩, ⟨5, none, 1⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 1, 4⟩]))))))))))))))))))))))))
                    (.split false ⟨.hat, 4, 5, false⟩
                      (.similar 0 ⟨true, 1⟩)
                      (.split false ⟨.hat, 7, 5, false⟩
                        (.similar 0 ⟨false, 4⟩)
                        (.split false ⟨.hat, 0, 5, false⟩
                          (.similar 0 ⟨true, 5⟩)
                          (.split false ⟨.spoke, 0, 7, false⟩
                            (.terminal (.hubcap [⟨0, none, 0⟩, ⟨3, none, 4⟩, ⟨5, none, 2⟩, ⟨7, none, 3⟩, ⟨1, some 2, 5⟩, ⟨4, some 6, 6⟩]))
                            (.split false ⟨.spoke, 2, 7, false⟩
                              (.terminal (.hubcap [⟨2, none, 0⟩, ⟨3, none, 3⟩, ⟨5, none, 2⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨4, some 6, 6⟩]))
                              (.split false ⟨.spoke, 4, 7, false⟩
                                (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 0⟩, ⟨7, none, 4⟩, ⟨0, some 2, 6⟩, ⟨5, some 6, 5⟩]))
                                (.split false ⟨.spoke, 6, 7, false⟩
                                  (.terminal (.hubcap [⟨1, none, 2⟩, ⟨3, none, 4⟩, ⟨6, none, 0⟩, ⟨7, none, 3⟩, ⟨0, some 2, 6⟩, ⟨4, some 5, 5⟩]))
                                  (.split false ⟨.spoke, 1, 6, true⟩
                                    (.terminal (.hubcap [⟨1, none, 0⟩, ⟨3, none, 3⟩, ⟨5, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 2, 6⟩, ⟨4, some 6, 6⟩]))
                                    (.split false ⟨.spoke, 5, 6, true⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨5, none, 0⟩, ⟨7, none, 3⟩, ⟨4, some 6, 6⟩]))
                                      (.split true ⟨.spoke, 0, 6, false⟩
                                        (.split false ⟨.spoke, 1, 7, false⟩
                                          (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩]))
                                          (.split false ⟨.spoke, 2, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩]))
                                            (.split false ⟨.fan1, 2, 5, true⟩
                                              (.terminal .reducible)
                                              (.split false ⟨.spoke, 4, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨4, some 5, 3⟩]))
                                                (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 1, 3⟩, ⟨5, some 6, 4⟩]))))))
                                        (.split false ⟨.spoke, 2, 6, false⟩
                                          (.similar 0 ⟨true, 5⟩)
                                          (.split false ⟨.spoke, 4, 6, false⟩
                                            (.similar 0 ⟨false, 4⟩)
                                            (.split false ⟨.spoke, 6, 6, false⟩
                                              (.similar 0 ⟨true, 1⟩)
                                              (.split false ⟨.fan1, 0, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.fan1, 2, 5, true⟩
                                                  (.terminal .reducible)
                                                  (.split false ⟨.fan1, 4, 5, true⟩
                                                    (.terminal .reducible)
                                                    (.split false ⟨.fan1, 6, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 3⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩]))))))))))))))))))))
                  (.split false ⟨.spoke, 0, 7, false⟩
                    (.terminal (.hubcap [⟨0, none, 0⟩, ⟨7, none, 3⟩, ⟨1, some 2, 4⟩, ⟨3, some 4, 6⟩, ⟨5, some 6, 7⟩]))
                    (.split false ⟨.spoke, 2, 7, false⟩
                      (.terminal (.hubcap [⟨2, none, 0⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨3, some 4, 4⟩, ⟨5, some 6, 7⟩]))
                      (.split false ⟨.spoke, 4, 7, false⟩
                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨4, none, 0⟩, ⟨1, some 7, 7⟩, ⟨2, some 3, 4⟩, ⟨5, some 6, 5⟩]))
                        (.split false ⟨.spoke, 6, 7, false⟩
                          (.terminal (.hubcap [⟨6, none, 0⟩, ⟨7, none, 3⟩, ⟨0, some 1, 7⟩, ⟨2, some 3, 6⟩, ⟨4, some 5, 4⟩]))
                          (.split true ⟨.spoke, 2, 6, false⟩
                            (.split false ⟨.spoke, 1, 7, false⟩
                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨7, none, 4⟩, ⟨3, some 4, 4⟩, ⟨5, some 6, 7⟩]))
                              (.split false ⟨.spoke, 3, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, some 7, 5⟩, ⟨5, some 6, 7⟩]))
                                (.split false ⟨.spoke, 5, 7, false⟩
                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨5, none, 0⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨3, some 4, 3⟩]))
                                  (.split false ⟨.spoke, 0, 6, false⟩
                                    (.split false ⟨.spoke, 1, 6, false⟩
                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨4, some 5, 6⟩]))
                                      (.split false ⟨.spoke, 3, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨5, some 6, 7⟩]))
                                        (.split false ⟨.spoke, 4, 6, false⟩
                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨2, none, 4⟩, ⟨3, none, 0⟩, ⟨4, none, 4⟩, ⟨7, none, 3⟩, ⟨5, some 6, 5⟩]))
                                          (.split false ⟨.spoke, 5, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨2, none, 4⟩, ⟨7, none, 3⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 6⟩]))
                                            (.split false ⟨.spoke, 6, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨2, none, 4⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨7, none, 2⟩, ⟨5, some 6, 5⟩]))
                                              (.split false ⟨.hat, 1, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 4⟩, ⟨7, none, 3⟩, ⟨3, some 4, 4⟩, ⟨5, some 6, 7⟩]))
                                                (.split false ⟨.hat, 2, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨7, none, 3⟩, ⟨3, some 4, 4⟩, ⟨5, some 6, 7⟩]))
                                                  (.split false ⟨.hat, 3, 5, false⟩
                                                    (.terminal (.hubcap [⟨1, none, 0⟩, ⟨7, none, 3⟩, ⟨0, some 2, 7⟩, ⟨3, some 6, 5⟩, ⟨4, some 5, 5⟩]))
                                                    (.split false ⟨.hat, 2, 5, true⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, none, 3⟩, ⟨7, none, 3⟩, ⟨3, some 4, 4⟩, ⟨5, some 6, 7⟩]))
                                                      (.split false ⟨.hat, 4, 5, false⟩
                                                        (.terminal (.hubcap [⟨1, none, 0⟩, ⟨7, none, 3⟩, ⟨0, some 2, 7⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 7⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨2, none, 4⟩, ⟨7, none, 3⟩, ⟨3, some 4, 4⟩, ⟨5, some 6, 5⟩]))))))))))))
                                    (.split false ⟨.spoke, 3, 6, false⟩
                                      (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨0, some 1, 5⟩, ⟨4, some 7, 5⟩, ⟨5, some 6, 6⟩]))
                                      (.split false ⟨.hat, 1, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, some 7, 7⟩, ⟨3, some 4, 4⟩, ⟨5, some 6, 6⟩]))
                                        (.split false ⟨.hat, 3, 6, false⟩
                                          (.terminal (.hubcap [⟨0, some 1, 5⟩, ⟨2, some 7, 5⟩, ⟨3, some 4, 4⟩, ⟨5, some 6, 6⟩]))
                                          (.split false ⟨.hat, 4, 6, false⟩
                                            (.terminal (.hubcap [⟨2, none, 4⟩, ⟨3, none, 0⟩, ⟨0, some 1, 5⟩, ⟨4, some 7, 5⟩, ⟨5, some 6, 6⟩]))
                                            (.split false ⟨.spoke, 5, 6, false⟩
                                              (.split false ⟨.spoke, 1, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨7, none, 4⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 6⟩]))
                                                (.split false ⟨.spoke, 4, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩, ⟨2, some 7, 7⟩]))
                                                  (.split false ⟨.spoke, 6, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨7, none, 3⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 4⟩]))
                                                    (.split false ⟨.hat, 2, 5, false⟩
                                                      (.terminal (.hubcap [⟨2, none, 2⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 6⟩]))
                                                      (.split false ⟨.hat, 4, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, some 1, 5⟩, ⟨2, some 6, 6⟩, ⟨3, some 4, 2⟩, ⟨5, some 7, 7⟩]))
                                                        (.split false ⟨.hat, 5, 6, false⟩
                                                          (.terminal (.hubcap [⟨3, none, 2⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨2, some 6, 6⟩, ⟨4, some 5, 3⟩]))
                                                          (.split false ⟨.hat, 6, 6, false⟩
                                                            (.terminal (.hubcap [⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨2, some 4, 5⟩, ⟨3, some 5, 3⟩]))
                                                            (.split false ⟨.hat, 7, 5, false⟩
                                                              (.terminal (.hubcap [⟨2, none, 4⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 1, 4⟩, ⟨5, some 6, 5⟩]))
                                                              (.split false ⟨.fan1, 2, 5, true⟩
                                                                (.terminal .reducible)
                                                                (.split false ⟨.fan1, 6, 5, true⟩
                                                                  (.terminal .reducible)
                                                                  (.split false ⟨.hat, 3, 5, false⟩
                                                                    (.terminal (.hubcap [⟨2, none, 2⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 6⟩]))
                                                                    (.split false ⟨.fan1, 3, 6, true⟩
                                                                      (.terminal .reducible)
                                                                      (.split false ⟨.hat, 5, 5, true⟩
                                                                        (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨4, none, 1⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨5, some 6, 6⟩]))
                                                                        (.split false ⟨.hat, 6, 5, false⟩
                                                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨7, none, 4⟩, ⟨5, some 6, 4⟩]))
                                                                          (.split false ⟨.fan1, 6, 6, true⟩
                                                                            (.terminal .reducible)
                                                                            (.split false ⟨.hat, 0, 5, false⟩
                                                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 4⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩]))
                                                                              (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩]))))))))))))))))))
                                              (.split false ⟨.spoke, 1, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨7, none, 4⟩, ⟨3, some 4, 4⟩, ⟨5, some 6, 5⟩]))
                                                (.split false ⟨.hat, 2, 5, false⟩
                                                  (.terminal (.hubcap [⟨2, none, 2⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨3, some 4, 4⟩, ⟨5, some 6, 5⟩]))
                                                  (.split false ⟨.hat, 5, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, some 1, 5⟩, ⟨2, some 7, 7⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 5⟩]))
                                                    (.split false ⟨.hat, 6, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, some 1, 5⟩, ⟨2, some 6, 6⟩, ⟨3, some 4, 4⟩, ⟨5, some 7, 5⟩]))
                                                      (.split false ⟨.hat, 7, 5, false⟩
                                                        (.terminal (.hubcap [⟨2, none, 4⟩, ⟨7, none, 3⟩, ⟨0, some 1, 4⟩, ⟨3, some 4, 4⟩, ⟨5, some 6, 5⟩]))
                                                        (.split false ⟨.spoke, 4, 6, false⟩
                                                          (.terminal (.hubcap [⟨3, none, 0⟩, ⟨0, some 1, 5⟩, ⟨2, some 7, 7⟩, ⟨4, some 5, 5⟩, ⟨4, some 6, 7⟩, ⟨5, some 6, 5⟩]))
                                                          (.split false ⟨.spoke, 6, 6, true⟩
                                                            (.terminal (.hubcap [⟨2, none, 3⟩, ⟨0, some 1, 5⟩, ⟨5, some 6, 5⟩, ⟨3, some 4, 4⟩, ⟨3, some 7, 5⟩, ⟨4, some 7, 6⟩]))
                                                            (.split false ⟨.hat, 1, 5, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨7, none, 3⟩, ⟨1, some 2, 5⟩, ⟨3, some 4, 4⟩, ⟨5, some 6, 5⟩]))
                                                              (.split false ⟨.fan1, 1, 6, true⟩
                                                                (.terminal .reducible)
                                                                (.split false ⟨.hat, 3, 5, true⟩
                                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨2, none, 3⟩, ⟨1, some 7, 4⟩, ⟨3, some 4, 4⟩, ⟨5, some 6, 5⟩]))
                                                                  (.split false ⟨.hat, 4, 5, false⟩
                                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨2, none, 4⟩, ⟨1, some 7, 4⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 5⟩]))
                                                                    (.split false ⟨.hat, 5, 5, false⟩
                                                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨2, none, 4⟩, ⟨1, some 7, 4⟩, ⟨3, some 6, 5⟩, ⟨4, some 5, 3⟩]))
                                                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨2, none, 4⟩, ⟨3, none, 1⟩, ⟨4, none, 3⟩, ⟨5, none, 1⟩, ⟨6, none, 3⟩, ⟨1, some 7, 4⟩])))))))))))))))))))))))
                            (.split false ⟨.spoke, 4, 6, false⟩
                              (.similar 0 ⟨true, 1⟩)
                              (.split false ⟨.spoke, 1, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 0⟩, ⟨2, some 3, 4⟩, ⟨4, some 7, 6⟩, ⟨5, some 6, 7⟩]))
                                (.split false ⟨.spoke, 5, 7, false⟩
                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨5, none, 0⟩, ⟨1, some 6, 6⟩, ⟨2, some 7, 6⟩, ⟨3, some 4, 4⟩]))
                                  (.split true ⟨.spoke, 0, 6, false⟩
                                    (.split false ⟨.spoke, 3, 7, false⟩
                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨5, some 6, 7⟩]))
                                      (.split false ⟨.hat, 5, 6, false⟩
                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨7, none, 3⟩, ⟨1, some 2, 4⟩, ⟨3, some 4, 4⟩, ⟨5, some 6, 5⟩]))
                                        (.split false ⟨.hat, 2, 5, false⟩
                                          (.split false ⟨.spoke, 5, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨7, none, 3⟩, ⟨1, some 2, 3⟩, ⟨3, some 4, 4⟩, ⟨5, some 6, 6⟩]))
                                            (.split false ⟨.spoke, 6, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨7, none, 2⟩, ⟨1, some 2, 3⟩, ⟨3, some 4, 6⟩, ⟨5, some 6, 5⟩]))
                                              (.split false ⟨.hat, 3, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨1, some 2, 2⟩, ⟨4, some 5, 5⟩]))
                                                (.split false ⟨.hat, 6, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨1, some 2, 3⟩, ⟨3, some 4, 6⟩, ⟨3, some 5, 5⟩, ⟨4, some 5, 4⟩]))
                                                  (.split false ⟨.hat, 7, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨7, none, 2⟩, ⟨1, some 2, 3⟩, ⟨3, some 4, 6⟩, ⟨5, some 6, 5⟩]))
                                                    (.split false ⟨.fan1, 6, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.hat, 4, 6, false⟩
                                                        (.terminal (.hubcap [⟨3, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 4, 5⟩, ⟨1, some 2, 3⟩, ⟨5, some 6, 7⟩]))
                                                        (.split false ⟨.spoke, 3, 6, false⟩
                                                          (.split false ⟨.spoke, 1, 6, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 0⟩, ⟨3, none, 4⟩, ⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨5, some 6, 7⟩]))
                                                            (.split false ⟨.hat, 1, 5, false⟩
                                                              (.terminal (.hubcap [⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 2, 3⟩, ⟨1, some 3, 5⟩, ⟨5, some 6, 7⟩]))
                                                              (.split false ⟨.hat, 2, 6, false⟩
                                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨2, none, 0⟩, ⟨3, none, 4⟩, ⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨5, some 6, 7⟩]))
                                                                (.split false ⟨.hat, 4, 5, false⟩
                                                                  (.terminal (.hubcap [⟨7, none, 3⟩, ⟨0, some 4, 5⟩, ⟨5, some 6, 7⟩, ⟨1, some 2, 2⟩, ⟨1, some 3, 5⟩, ⟨2, some 3, 4⟩]))
                                                                  (.split false ⟨.hat, 3, 5, true⟩
                                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨1, some 2, 2⟩, ⟨4, some 5, 4⟩]))
                                                                    (.split false ⟨.hat, 5, 5, false⟩
                                                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨1, some 2, 2⟩, ⟨4, some 5, 3⟩]))
                                                                      (.terminal (.hubcap [⟨3, none, 4⟩, ⟨7, none, 3⟩, ⟨0, some 4, 5⟩, ⟨1, some 2, 2⟩, ⟨5, some 6, 6⟩]))))))))
                                                          (.split false ⟨.spoke, 1, 6, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 4⟩, ⟨5, some 6, 6⟩]))
                                                            (.split false ⟨.hat, 1, 6, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨1, some 2, 3⟩, ⟨5, some 6, 6⟩]))
                                                              (.split false ⟨.hat, 2, 6, false⟩
                                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 4⟩, ⟨5, some 6, 6⟩]))
                                                                (.split false ⟨.hat, 3, 5, false⟩
                                                                  (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 2⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨1, some 2, 2⟩, ⟨5, some 6, 6⟩]))
                                                                  (.split false ⟨.hat, 4, 5, true⟩
                                                                    (.terminal (.hubcap [⟨3, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 4, 6⟩, ⟨1, some 2, 3⟩, ⟨5, some 6, 5⟩]))
                                                                    (.split false ⟨.fan1, 4, 5, true⟩
                                                                      (.terminal .reducible)
                                                                      (.split false ⟨.hat, 1, 5, false⟩
                                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨7, none, 3⟩, ⟨1, some 2, 3⟩, ⟨3, some 4, 5⟩, ⟨5, some 6, 6⟩]))
                                                                        (.split false ⟨.hat, 5, 5, false⟩
                                                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨1, some 2, 3⟩]))
                                                                          (.split false ⟨.hat, 6, 5, true⟩
                                                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨5, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨1, some 2, 3⟩, ⟨3, some 4, 4⟩]))
                                                                            (.split false ⟨.hat, 7, 5, false⟩
                                                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 2⟩, ⟨1, some 2, 3⟩]))
                                                                              (.split false ⟨.hat, 0, 5, false⟩
                                                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨1, some 2, 3⟩, ⟨5, some 6, 5⟩]))
                                                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨1, some 2, 3⟩, ⟨3, some 4, 4⟩])))))))))))))))))))))
                                          (.split false ⟨.spoke, 5, 6, false⟩
                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨7, none, 3⟩, ⟨1, some 2, 4⟩, ⟨3, some 4, 4⟩, ⟨5, some 6, 6⟩]))
                                            (.split false ⟨.spoke, 6, 6, false⟩
                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨7, none, 2⟩, ⟨1, some 2, 4⟩, ⟨3, some 4, 6⟩, ⟨5, some 6, 5⟩]))
                                              (.split false ⟨.hat, 3, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 2⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨1, some 2, 3⟩, ⟨4, some 5, 5⟩]))
                                                (.split false ⟨.hat, 6, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨1, some 2, 4⟩, ⟨3, some 4, 6⟩, ⟨3, some 5, 5⟩, ⟨4, some 5, 4⟩]))
                                                  (.split false ⟨.hat, 7, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨7, none, 2⟩, ⟨1, some 2, 4⟩, ⟨3, some 4, 6⟩, ⟨5, some 6, 5⟩]))
                                                    (.split false ⟨.fan1, 6, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.hat, 4, 6, false⟩
                                                        (.terminal (.hubcap [⟨1, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 4, 4⟩, ⟨2, some 3, 4⟩, ⟨5, some 6, 7⟩]))
                                                        (.split false ⟨.spoke, 3, 6, false⟩
                                                          (.split false ⟨.spoke, 1, 6, false⟩
                                                            (.terminal (.hubcap [⟨2, none, 0⟩, ⟨3, none, 4⟩, ⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 1, 4⟩, ⟨5, some 6, 7⟩]))
                                                            (.split false ⟨.hat, 1, 6, false⟩
                                                              (.terminal (.hubcap [⟨3, none, 4⟩, ⟨7, none, 3⟩, ⟨0, some 4, 3⟩, ⟨1, some 2, 3⟩, ⟨5, some 6, 7⟩]))
                                                              (.split false ⟨.hat, 1, 5, true⟩
                                                                (.terminal (.hubcap [⟨2, none, 1⟩, ⟨7, none, 3⟩, ⟨0, some 4, 4⟩, ⟨1, some 3, 5⟩, ⟨5, some 6, 7⟩]))
                                                                (.split false ⟨.hat, 4, 5, true⟩
                                                                  (.terminal (.hubcap [⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨0, some 2, 4⟩, ⟨1, some 3, 5⟩, ⟨4, some 5, 4⟩]))
                                                                  (.split false ⟨.hat, 3, 5, false⟩
                                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨1, some 2, 3⟩, ⟨5, some 6, 7⟩]))
                                                                    (.split false ⟨.fan1, 2, 6, true⟩
                                                                      (.terminal .reducible)
                                                                      (.split false ⟨.hat, 5, 5, false⟩
                                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨4, some 5, 3⟩]))
                                                                        (.split false ⟨.hat, 6, 5, true⟩
                                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨4, none, 1⟩, ⟨6, none, 4⟩, ⟨7, none, 3⟩, ⟨3, some 5, 6⟩]))
                                                                          (.split false ⟨.hat, 7, 5, false⟩
                                                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 2⟩]))
                                                                            (.split false ⟨.hat, 0, 5, false⟩
                                                                              (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨5, some 6, 6⟩]))
                                                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨4, none, 1⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨3, some 5, 7⟩]))))))))))))
                                                          (.split false ⟨.spoke, 1, 6, false⟩
                                                            (.terminal (.hubcap [⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 1, 4⟩, ⟨2, some 3, 4⟩, ⟨5, some 6, 6⟩]))
                                                            (.split false ⟨.hat, 4, 5, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨7, none, 3⟩, ⟨1, some 2, 4⟩, ⟨3, some 4, 4⟩, ⟨5, some 6, 6⟩]))
                                                              (.split false ⟨.hat, 6, 5, true⟩
                                                                (.terminal .reducible)
                                                                (.split false ⟨.hat, 1, 6, false⟩
                                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨1, some 2, 4⟩, ⟨5, some 6, 5⟩]))
                                                                  (.split false ⟨.hat, 3, 5, true⟩
                                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 3⟩, ⟨7, none, 3⟩, ⟨3, some 4, 5⟩, ⟨5, some 6, 5⟩]))
                                                                    (.split false ⟨.hat, 1, 5, true⟩
                                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 4⟩, ⟨5, some 6, 5⟩]))
                                                                      (.split false ⟨.hat, 5, 5, false⟩
                                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨2, some 3, 5⟩, ⟨5, some 6, 5⟩]))
                                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨2, some 3, 4⟩, ⟨5, some 6, 5⟩]))))))))))))))))))))
                                    (.split false ⟨.spoke, 6, 6, false⟩
                                      (.similar 0 ⟨true, 1⟩)
                                      (.split false ⟨.spoke, 3, 7, false⟩
                                        (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, none, 2⟩, ⟨7, none, 4⟩, ⟨0, some 1, 6⟩, ⟨5, some 6, 6⟩]))
                                        (.split false ⟨.fan1, 2, 5, true⟩
                                          (.split false ⟨.spoke, 3, 6, false⟩
                                            (.terminal (.hubcap [⟨0, some 1, 6⟩, ⟨2, some 3, 3⟩, ⟨4, some 7, 5⟩, ⟨5, some 6, 6⟩]))
                                            (.split false ⟨.hat, 3, 6, false⟩
                                              (.terminal (.hubcap [⟨0, some 1, 6⟩, ⟨2, some 7, 4⟩, ⟨3, some 4, 4⟩, ⟨5, some 6, 6⟩]))
                                              (.split false ⟨.fan1, 3, 5, true⟩
                                                (.terminal .reducible)
                                                (.split false ⟨.spoke, 1, 6, true⟩
                                                  (.terminal (.hubcap [⟨2, none, 1⟩, ⟨3, none, 3⟩, ⟨0, some 1, 4⟩, ⟨4, some 7, 6⟩, ⟨5, some 6, 6⟩]))
                                                  (.split false ⟨.spoke, 5, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 1⟩, ⟨7, none, 4⟩, ⟨1, some 2, 3⟩, ⟨5, some 6, 6⟩]))
                                                    (.split false ⟨.hat, 1, 5, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 3⟩, ⟨1, some 2, 2⟩, ⟨4, some 7, 6⟩, ⟨5, some 6, 6⟩]))
                                                      (.split false ⟨.hat, 4, 5, false⟩
                                                        (.terminal (.hubcap [⟨0, some 3, 5⟩, ⟨1, some 2, 3⟩, ⟨4, some 7, 6⟩, ⟨5, some 6, 6⟩]))
                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 3⟩, ⟨1, some 2, 3⟩, ⟨4, some 5, 4⟩, ⟨6, some 7, 7⟩])))))))))
                                          (.split false ⟨.spoke, 3, 6, false⟩
                                            (.split false ⟨.hat, 2, 6, false⟩
                                              (.terminal (.hubcap [⟨2, none, 0⟩, ⟨3, none, 4⟩, ⟨0, some 1, 5⟩, ⟨4, some 7, 5⟩, ⟨5, some 6, 6⟩]))
                                              (.split false ⟨.hat, 5, 6, false⟩
                                                (.terminal (.hubcap [⟨3, none, 4⟩, ⟨4, none, 0⟩, ⟨0, some 1, 6⟩, ⟨2, some 7, 5⟩, ⟨5, some 6, 5⟩]))
                                                (.split true ⟨.hat, 7, 5, false⟩
                                                  (.split false ⟨.spoke, 1, 6, false⟩
                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨2, none, 0⟩, ⟨3, none, 4⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨4, some 5, 4⟩]))
                                                    (.split false ⟨.spoke, 5, 6, false⟩
                                                      (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 0⟩, ⟨5, none, 4⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 1, 5⟩]))
                                                      (.split false ⟨.hat, 1, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 1⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩]))
                                                        (.split false ⟨.hat, 3, 6, false⟩
                                                          (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 1, 5⟩]))
                                                          (.split false ⟨.hat, 4, 6, false⟩
                                                            (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 1, 5⟩]))
                                                            (.split false ⟨.hat, 5, 5, false⟩
                                                              (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨6, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 1, 5⟩, ⟨4, some 5, 3⟩]))
                                                              (.split false ⟨.hat, 6, 6, false⟩
                                                                (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 1, 5⟩]))
                                                                (.split false ⟨.hat, 7, 6, true⟩
                                                                  (.terminal (.hubcap [⟨2, none, 2⟩, ⟨6, none, 3⟩, ⟨0, some 1, 5⟩, ⟨3, some 5, 6⟩, ⟨4, some 7, 4⟩]))
                                                                  (.split false ⟨.hat, 6, 5, false⟩
                                                                    (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 1, 5⟩, ⟨5, some 6, 4⟩]))
                                                                    (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, none, 1⟩, ⟨5, none, 3⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 1, 5⟩])))))))))))
                                                  (.split false ⟨.hat, 0, 5, false⟩
                                                    (.similar 0 ⟨true, 1⟩)
                                                    (.split false ⟨.fan1, 0, 5, true⟩
                                                      (.terminal .reducible)
                                                      (.split false ⟨.fan1, 6, 5, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.hat, 1, 6, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨3, none, 4⟩, ⟨4, none, 1⟩, ⟨7, none, 4⟩, ⟨1, some 2, 2⟩, ⟨5, some 6, 6⟩]))
                                                          (.split false ⟨.hat, 3, 6, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨7, none, 4⟩, ⟨1, some 2, 3⟩, ⟨5, some 6, 6⟩]))
                                                            (.split false ⟨.hat, 4, 6, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨7, none, 4⟩, ⟨1, some 2, 3⟩, ⟨5, some 6, 6⟩]))
                                                              (.split false ⟨.hat, 6, 6, false⟩
                                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 4⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨1, some 2, 3⟩, ⟨4, some 5, 2⟩]))
                                                                (.split true ⟨.hat, 3, 5, false⟩
                                                                  (.split false ⟨.spoke, 1, 6, false⟩
                                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨7, none, 4⟩, ⟨3, some 4, 4⟩, ⟨5, some 6, 6⟩]))
                                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨7, none, 4⟩, ⟨1, some 2, 2⟩, ⟨3, some 4, 4⟩, ⟨5, some 6, 6⟩])))
                                                                  (.split false ⟨.hat, 4, 5, false⟩
                                                                    (.similar 0 ⟨true, 1⟩)
                                                                    (.split false ⟨.spoke, 5, 6, false⟩
                                                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 3⟩, ⟨4, none, 0⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨1, some 2, 3⟩]))
                                                                      (.split false ⟨.hat, 5, 5, true⟩
                                                                        (.terminal .reducible)
                                                                        (.split false ⟨.fan1, 4, 5, true⟩
                                                                          (.terminal .reducible)
                                                                          (.split false ⟨.fan1, 5, 5, true⟩
                                                                            (.terminal .reducible)
                                                                            (.split false ⟨.spoke, 1, 6, false⟩
                                                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 3⟩, ⟨4, none, 1⟩, ⟨7, none, 4⟩, ⟨5, some 6, 6⟩]))
                                                                              (.split false ⟨.hat, 2, 5, true⟩
                                                                                (.terminal .reducible)
                                                                                (.split false ⟨.fan1, 1, 5, true⟩
                                                                                  (.terminal .reducible)
                                                                                  (.split false ⟨.hat, 1, 5, false⟩
                                                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 0⟩, ⟨3, none, 3⟩, ⟨4, none, 1⟩, ⟨7, none, 4⟩, ⟨5, some 6, 6⟩]))
                                                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 3⟩, ⟨4, none, 1⟩, ⟨7, none, 4⟩, ⟨1, some 2, 2⟩, ⟨5, some 6, 6⟩]))))))))))))))))))))))
                                            (.split true ⟨.spoke, 1, 6, false⟩
                                              (.split false ⟨.hat, 3, 6, false⟩
                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 0⟩, ⟨1, some 7, 7⟩, ⟨3, some 4, 4⟩, ⟨5, some 6, 6⟩]))
                                                (.split false ⟨.hat, 4, 6, false⟩
                                                  (.terminal (.hubcap [⟨2, none, 2⟩, ⟨3, none, 1⟩, ⟨0, some 1, 6⟩, ⟨4, some 7, 5⟩, ⟨5, some 6, 6⟩]))
                                                  (.split false ⟨.fan1, 0, 5, true⟩
                                                    (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨7, none, 3⟩, ⟨3, some 4, 5⟩, ⟨5, some 6, 6⟩]))
                                                    (.split false ⟨.fan1, 4, 5, false⟩
                                                      (.split false ⟨.spoke, 5, 6, true⟩
                                                        (.terminal (.hubcap [⟨0, some 1, 6⟩, ⟨2, some 3, 3⟩, ⟨4, some 7, 6⟩, ⟨5, some 6, 5⟩]))
                                                        (.split false ⟨.hat, 1, 6, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨7, none, 4⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 6⟩]))
                                                          (.split false ⟨.hat, 2, 6, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨7, none, 4⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 6⟩]))
                                                            (.split false ⟨.hat, 5, 6, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 2⟩, ⟨5, none, 2⟩, ⟨7, none, 4⟩, ⟨1, some 6, 6⟩, ⟨3, some 4, 3⟩]))
                                                              (.split false ⟨.hat, 6, 6, false⟩
                                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 2⟩, ⟨5, none, 2⟩, ⟨7, none, 4⟩, ⟨1, some 6, 6⟩, ⟨3, some 4, 3⟩]))
                                                                (.split false ⟨.hat, 7, 5, false⟩
                                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨5, some 6, 5⟩]))
                                                                  (.split false ⟨.fan1, 6, 5, true⟩
                                                                    (.terminal .reducible)
                                                                    (.split false ⟨.hat, 1, 5, false⟩
                                                                      (.terminal (.hubcap [⟨2, none, 2⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 6⟩]))
                                                                      (.split false ⟨.hat, 2, 5, false⟩
                                                                        (.terminal (.hubcap [⟨2, none, 2⟩, ⟨7, none, 4⟩, ⟨0, some 1, 5⟩, ⟨3, some 4, 3⟩, ⟨5, some 6, 6⟩]))
                                                                        (.split false ⟨.hat, 3, 5, true⟩
                                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨7, none, 4⟩, ⟨5, some 6, 6⟩]))
                                                                          (.split false ⟨.hat, 4, 5, false⟩
                                                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨7, none, 4⟩, ⟨5, some 6, 6⟩]))
                                                                            (.split false ⟨.hat, 6, 5, true⟩
                                                                              (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 2⟩, ⟨4, none, 1⟩, ⟨7, none, 4⟩, ⟨5, some 6, 6⟩]))
                                                                              (.split false ⟨.hat, 5, 5, false⟩
                                                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨7, none, 4⟩, ⟨5, some 6, 4⟩]))
                                                                                (.split false ⟨.fan1, 4, 6, true⟩
                                                                                  (.terminal .reducible)
                                                                                  (.split false ⟨.hat, 0, 5, false⟩
                                                                                    (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 4⟩, ⟨6, none, 2⟩, ⟨7, none, 3⟩]))
                                                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 2⟩, ⟨5, none, 2⟩, ⟨6, none, 3⟩, ⟨7, none, 4⟩, ⟨3, some 4, 3⟩])))))))))))))))))
                                                      (.split false ⟨.fan1, 3, 5, true⟩
                                                        (.terminal .reducible)
                                                        (.split false ⟨.spoke, 5, 6, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 3⟩, ⟨7, none, 4⟩, ⟨1, some 6, 6⟩, ⟨4, some 5, 3⟩]))
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 4⟩, ⟨2, none, 1⟩, ⟨3, none, 3⟩, ⟨4, none, 1⟩, ⟨7, none, 4⟩, ⟨5, some 6, 4⟩]))))))))
                                              (.split false ⟨.spoke, 5, 6, false⟩
                                                (.similar 0 ⟨true, 1⟩)
                                                (.split false ⟨.hat, 3, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, some 1, 5⟩, ⟨2, some 7, 5⟩, ⟨3, some 4, 4⟩, ⟨5, some 6, 6⟩]))
                                                  (.split false ⟨.hat, 4, 6, false⟩
                                                    (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 1⟩, ⟨0, some 1, 5⟩, ⟨4, some 7, 5⟩, ⟨5, some 6, 6⟩]))
                                                    (.split false ⟨.hat, 1, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, some 7, 6⟩, ⟨3, some 4, 5⟩, ⟨5, some 6, 5⟩]))
                                                      (.split false ⟨.hat, 1, 5, true⟩
                                                        (.terminal (.hubcap [⟨0, some 1, 5⟩, ⟨2, some 3, 4⟩, ⟨4, some 7, 6⟩, ⟨5, some 6, 5⟩]))
                                                        (.split false ⟨.hat, 2, 6, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, some 3, 4⟩, ⟨4, some 7, 6⟩, ⟨5, some 6, 5⟩]))
                                                          (.split false ⟨.hat, 4, 5, false⟩
                                                            (.terminal (.hubcap [⟨0, some 1, 5⟩, ⟨2, some 7, 6⟩, ⟨3, some 4, 4⟩, ⟨5, some 6, 5⟩]))
                                                            (.split false ⟨.hat, 6, 5, true⟩
                                                              (.terminal .reducible)
                                                              (.split false ⟨.hat, 2, 5, false⟩
                                                                (.terminal (.hubcap [⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨0, some 6, 6⟩, ⟨3, some 4, 5⟩, ⟨5, some 7, 5⟩]))
                                                                (.split false ⟨.hat, 5, 5, false⟩
                                                                  (.terminal (.hubcap [⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 1, 5⟩, ⟨5, some 6, 4⟩]))
                                                                  (.split false ⟨.fan1, 4, 6, true⟩
                                                                    (.terminal .reducible)
                                                                    (.split false ⟨.hat, 3, 5, false⟩
                                                                      (.terminal (.hubcap [⟨4, none, 3⟩, ⟨7, none, 3⟩, ⟨0, some 1, 5⟩, ⟨2, some 3, 4⟩, ⟨5, some 6, 5⟩]))
                                                                      (.terminal (.hubcap [⟨3, none, 2⟩, ⟨7, none, 3⟩, ⟨0, some 6, 7⟩, ⟨1, some 2, 4⟩, ⟨4, some 5, 4⟩])))))))))))))))))))))))))))))))))))
    (.split false ⟨.spoke, 0, 5, true⟩
      (.similar 0 ⟨false, 1⟩)
      (.split false ⟨.spoke, 1, 5, true⟩
        (.similar 0 ⟨false, 2⟩)
        (.split false ⟨.spoke, 2, 5, true⟩
          (.similar 0 ⟨false, 3⟩)
          (.split false ⟨.spoke, 3, 5, true⟩
            (.similar 0 ⟨false, 4⟩)
            (.split false ⟨.spoke, 4, 5, true⟩
              (.similar 0 ⟨false, 5⟩)
              (.split false ⟨.spoke, 5, 5, true⟩
                (.similar 0 ⟨false, 6⟩)
                (.split false ⟨.spoke, 6, 5, true⟩
                  (.similar 0 ⟨false, 7⟩)
                  (.split false ⟨.spoke, 0, 7, false⟩
                    (.terminal (.hubcap [⟨0, none, 0⟩, ⟨1, none, 2⟩, ⟨2, none, 4⟩, ⟨3, none, 4⟩, ⟨4, some 5, 6⟩, ⟨6, some 7, 4⟩]))
                    (.split false ⟨.spoke, 1, 7, false⟩
                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 0⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, some 5, 6⟩, ⟨6, some 7, 6⟩]))
                      (.split false ⟨.spoke, 2, 7, false⟩
                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 0⟩, ⟨3, none, 2⟩, ⟨4, some 5, 6⟩, ⟨6, some 7, 6⟩]))
                        (.split false ⟨.spoke, 3, 7, false⟩
                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 2⟩, ⟨3, none, 0⟩, ⟨4, some 5, 4⟩, ⟨6, some 7, 6⟩]))
                          (.split false ⟨.spoke, 4, 7, false⟩
                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨4, none, 0⟩, ⟨5, none, 2⟩, ⟨2, some 3, 4⟩, ⟨6, some 7, 6⟩]))
                            (.split false ⟨.spoke, 5, 7, false⟩
                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨2, none, 4⟩, ⟨5, none, 0⟩, ⟨3, some 4, 4⟩, ⟨6, some 7, 4⟩]))
                              (.split false ⟨.spoke, 6, 7, false⟩
                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 4⟩, ⟨6, none, 0⟩, ⟨7, none, 2⟩, ⟨2, some 3, 6⟩, ⟨4, some 5, 4⟩]))
                                (.split false ⟨.spoke, 7, 7, false⟩
                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 4⟩, ⟨2, none, 4⟩, ⟨7, none, 0⟩, ⟨3, some 4, 6⟩, ⟨5, some 6, 4⟩]))
                                  (.split false ⟨.hat, 1, 6, false⟩
                                    (.terminal (.hubcap [⟨0, some 7, 4⟩, ⟨1, some 2, 4⟩, ⟨3, some 4, 6⟩, ⟨5, some 6, 6⟩]))
                                    (.split false ⟨.hat, 2, 6, false⟩
                                      (.terminal (.hubcap [⟨0, some 1, 4⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 6⟩, ⟨6, some 7, 6⟩]))
                                      (.split false ⟨.hat, 3, 6, false⟩
                                        (.terminal (.hubcap [⟨0, some 7, 6⟩, ⟨1, some 2, 4⟩, ⟨3, some 4, 4⟩, ⟨5, some 6, 6⟩]))
                                        (.split false ⟨.hat, 4, 6, false⟩
                                          (.terminal (.hubcap [⟨0, some 1, 6⟩, ⟨2, some 3, 4⟩, ⟨4, some 5, 4⟩, ⟨6, some 7, 6⟩]))
                                          (.split false ⟨.hat, 5, 6, false⟩
                                            (.terminal (.hubcap [⟨0, some 7, 6⟩, ⟨1, some 2, 6⟩, ⟨3, some 4, 4⟩, ⟨5, some 6, 4⟩]))
                                            (.split false ⟨.hat, 6, 6, false⟩
                                              (.terminal (.hubcap [⟨0, some 1, 6⟩, ⟨2, some 3, 6⟩, ⟨4, some 5, 4⟩, ⟨6, some 7, 4⟩]))
                                              (.split false ⟨.hat, 7, 6, false⟩
                                                (.terminal (.hubcap [⟨0, some 7, 4⟩, ⟨1, some 2, 6⟩, ⟨3, some 4, 6⟩, ⟨5, some 6, 4⟩]))
                                                (.split false ⟨.hat, 0, 6, false⟩
                                                  (.terminal (.hubcap [⟨0, some 1, 4⟩, ⟨2, some 3, 6⟩, ⟨4, some 5, 6⟩, ⟨6, some 7, 4⟩]))
                                                  (.split true ⟨.spoke, 0, 6, false⟩
                                                    (.split false ⟨.spoke, 1, 6, false⟩
                                                      (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, some 5, 6⟩, ⟨6, some 7, 4⟩]))
                                                      (.split false ⟨.spoke, 2, 6, false⟩
                                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 0⟩, ⟨2, none, 4⟩, ⟨3, none, 2⟩, ⟨4, some 5, 6⟩, ⟨6, some 7, 4⟩]))
                                                        (.split false ⟨.spoke, 3, 6, false⟩
                                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 4⟩, ⟨4, some 5, 4⟩, ⟨6, some 7, 4⟩]))
                                                          (.split false ⟨.spoke, 4, 6, false⟩
                                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨4, none, 4⟩, ⟨5, none, 2⟩, ⟨2, some 3, 4⟩, ⟨6, some 7, 4⟩]))
                                                            (.split false ⟨.spoke, 5, 6, false⟩
                                                              (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨5, none, 4⟩, ⟨3, some 4, 4⟩, ⟨6, some 7, 3⟩]))
                                                              (.split false ⟨.spoke, 6, 6, false⟩
                                                                (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨6, none, 4⟩, ⟨7, none, 0⟩, ⟨4, some 5, 4⟩]))
                                                                (.split false ⟨.spoke, 7, 6, false⟩
                                                                  (.terminal (.hubcap [⟨0, none, 2⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨6, none, 2⟩, ⟨7, none, 2⟩]))
                                                                  (.split false ⟨.hat, 2, 5, false⟩
                                                                    (.terminal (.hubcap [⟨0, none, 4⟩, ⟨3, none, 3⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨1, some 2, 3⟩, ⟨6, some 7, 4⟩]))
                                                                    (.split false ⟨.hat, 3, 5, true⟩
                                                                      (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 1⟩, ⟨2, none, 3⟩, ⟨5, none, 3⟩, ⟨3, some 4, 5⟩, ⟨6, some 7, 4⟩]))
                                                                      (.split false ⟨.hat, 1, 5, true⟩
                                                                        (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨2, some 3, 4⟩, ⟨6, some 7, 4⟩]))
                                                                        (.split false ⟨.hat, 4, 5, false⟩
                                                                          (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 2⟩, ⟨4, none, 2⟩, ⟨5, none, 3⟩, ⟨6, none, 3⟩, ⟨7, none, 2⟩]))
                                                                          (.split false ⟨.hat, 5, 5, false⟩
                                                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨2, some 3, 5⟩, ⟨4, some 5, 5⟩, ⟨6, some 7, 4⟩]))
                                                                            (.terminal (.hubcap [⟨0, none, 4⟩, ⟨1, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨2, some 3, 4⟩, ⟨6, some 7, 4⟩]))))))))))))))
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
                                                                (.split false ⟨.spoke, 7, 6, false⟩
                                                                  (.similar 0 ⟨false, 7⟩)
                                                                  (.split false ⟨.fan1, 0, 5, true⟩
                                                                    (.terminal (.hubcap [⟨0, none, 1⟩, ⟨1, none, 3⟩, ⟨2, none, 3⟩, ⟨7, none, 3⟩, ⟨3, some 4, 5⟩, ⟨5, some 6, 5⟩]))
                                                                    (.split false ⟨.fan1, 1, 5, true⟩
                                                                      (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 1⟩, ⟨2, none, 3⟩, ⟨3, none, 3⟩, ⟨4, some 5, 5⟩, ⟨6, some 7, 5⟩]))
                                                                      (.split false ⟨.fan1, 2, 5, true⟩
                                                                        (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 3⟩, ⟨2, none, 1⟩, ⟨3, none, 3⟩, ⟨4, some 5, 5⟩, ⟨6, some 7, 5⟩]))
                                                                        (.split false ⟨.hat, 1, 5, false⟩
                                                                          (.terminal (.hubcap [⟨2, none, 3⟩, ⟨5, none, 3⟩, ⟨0, some 1, 4⟩, ⟨3, some 4, 5⟩, ⟨6, some 7, 5⟩]))
                                                                          (.split false ⟨.hat, 2, 5, false⟩
                                                                            (.terminal (.hubcap [⟨0, none, 3⟩, ⟨5, none, 3⟩, ⟨1, some 2, 4⟩, ⟨3, some 4, 5⟩, ⟨6, some 7, 5⟩]))
                                                                            (.split false ⟨.fan1, 1, 6, true⟩
                                                                              (.terminal .reducible)
                                                                              (.split false ⟨.hat, 3, 5, false⟩
                                                                                (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨4, none, 3⟩, ⟨5, none, 3⟩, ⟨2, some 3, 4⟩, ⟨6, some 7, 5⟩]))
                                                                                (.split false ⟨.fan1, 2, 6, true⟩
                                                                                  (.terminal .reducible)
                                                                                  (.split false ⟨.hat, 4, 5, false⟩
                                                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 3⟩, ⟨5, none, 3⟩, ⟨3, some 4, 4⟩, ⟨6, some 7, 5⟩]))
                                                                                    (.terminal (.hubcap [⟨0, none, 3⟩, ⟨1, none, 2⟩, ⟨2, none, 2⟩, ⟨3, none, 3⟩, ⟨4, some 5, 5⟩, ⟨6, some 7, 5⟩])))))))))))))))))))))))))))))))))))))))))))

theorem structureCheck_eq_true :
    structureCheck arity code = true := by
  rfl

end ClassicalCertificatePresentationData8

end Mettapedia.GraphTheory.FourColor
