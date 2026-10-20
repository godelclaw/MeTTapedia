import Mettapedia.Languages.Megalodon.SourceAdmission

/-! Untrusted source items; checked by NaturalRecursion. -/

namespace Mettapedia.Languages.Megalodon.NaturalRecursion.Evidence

open MathdataKernel NativeAdmission

def ncAnd : Item :=
Mettapedia.Languages.Megalodon.NativeAdmission.Item.definition
  "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738"
  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop)
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop)))
  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop)
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop)
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))

def naturalClosure : Item :=
Mettapedia.Languages.Megalodon.NativeAdmission.Item.definition
  "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be"
  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))))
  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))))))))

def ncAndIntro : Item :=
Mettapedia.Languages.Megalodon.NativeAdmission.Item.theorem_
  "7f6246d08629eeb16eab93529ffe4f929f43344833ab88c7786393693520e82b"
  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop)
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))))
  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop)
    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop)
            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0)
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 2))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 1))))))))

def ncAndLeft : Item :=
Mettapedia.Languages.Megalodon.NativeAdmission.Item.theorem_
  "eb8814e5b67181dcc2fdd7f757e9f1e3c90bcd9b3117f2bb9aa7650cdaac5b42"
  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop)
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
              "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))))
  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop)
    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
              "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0)
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 1)))))))

def ncAndRight : Item :=
Mettapedia.Languages.Megalodon.NativeAdmission.Item.theorem_
  "fec5ab340a042c8361bb0564ac980cfe10dabcf5c4aeacb0746c0daa4ac55417"
  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop)
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
              "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))
  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop)
    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
              "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0)
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0)))))))

def naturalClosureZero : Item :=
Mettapedia.Languages.Megalodon.NativeAdmission.Item.theorem_
  "a7a2e1cb291bdfdc11661c2875e62b3fb8fb502cb3c1f594c4e6f50789e4f911"
  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
              "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))))
  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 1))))))

def naturalClosureSuccessor : Item :=
Mettapedia.Languages.Megalodon.NativeAdmission.Item.theorem_
  "877913cb39467cac5218f875864ba9d5f794a079e124c150a2aa99edb28f6861"
  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                  "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                  "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))))
  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                  "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 2)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 1))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0))))))))))

def naturalClosureInduction : Item :=
Mettapedia.Languages.Megalodon.NativeAdmission.Item.theorem_
  "77e10b9988f12dc528ad73906107175925091da967df0552db1799b699955593"
  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                        "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                        "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))))))
  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                        "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                        "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                          "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3)))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3)))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                  "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                        "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                  "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                        "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3)
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3)
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                  "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                        "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                    "fec5ab340a042c8361bb0564ac980cfe10dabcf5c4aeacb0746c0daa4ac55417")
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                          "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0)))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 2)
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                        "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                              "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 1))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0))))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                      "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                      "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                            "7f6246d08629eeb16eab93529ffe4f929f43344833ab88c7786393693520e82b")
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                  "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3)
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3)
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                                "877913cb39467cac5218f875864ba9d5f794a079e124c150a2aa99edb28f6861")
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 1)))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 5)
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 1))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0))))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                        "fec5ab340a042c8361bb0564ac980cfe10dabcf5c4aeacb0746c0daa4ac55417")
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                              "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 1))))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                    "eb8814e5b67181dcc2fdd7f757e9f1e3c90bcd9b3117f2bb9aa7650cdaac5b42")
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                          "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0)))))))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                            "7f6246d08629eeb16eab93529ffe4f929f43344833ab88c7786393693520e82b")
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                  "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3)))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3)))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                            "a7a2e1cb291bdfdc11661c2875e62b3fb8fb502cb3c1f594c4e6f50789e4f911")
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 2))))))))))

def nrFalse : Item :=
Mettapedia.Languages.Megalodon.NativeAdmission.Item.definition
  "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87"
  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop)
  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop)
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))

def nrEq : Item :=
Mettapedia.Languages.Megalodon.NativeAdmission.Item.definition
  "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89"
  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.all
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))))
  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeLam
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))))))

def nrExists : Item :=
Mettapedia.Languages.Megalodon.NativeAdmission.Item.definition
  "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099"
  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.all
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop)))
  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeLam
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop)
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))

def nrEqRefl : Item :=
Mettapedia.Languages.Megalodon.NativeAdmission.Item.theorem_
  "0f730be4ec19d9c14f6f80059c561f714dcecb54d8fa04f3570d0607e71d8331"
  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeAll
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
              "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))
  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeLam
    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0)))))

def nrEqSym : Item :=
Mettapedia.Languages.Megalodon.NativeAdmission.Item.theorem_
  "284ee58e7aea454281b73a0d0acb6efade8eeb4f2f3bf29aaf48a8fef862ceff"
  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeAll
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                  "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                  "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))))))
  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeLam
    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                  "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                        "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                  "0f730be4ec19d9c14f6f80059c561f714dcecb54d8fa04f3570d0607e71d8331")
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))))))

def nrEqTrans : Item :=
Mettapedia.Languages.Megalodon.NativeAdmission.Item.theorem_
  "0224060d7b7d5b6b2e8e4157524c8e4a18e5d17073c5b2fb2bb0c2583274fbc7"
  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeAll
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                    "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                      "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                      "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))))))
  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeLam
    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                    "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                      "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 1)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 2)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0)))))))))))

def nrExistsIntro : Item :=
Mettapedia.Languages.Megalodon.NativeAdmission.Item.theorem_
  "cb01597ac16d6df38d6f584e549edd3603cd7abc72e2a1cfcc2ba44fc649758e"
  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeAll
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))))))
  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeLam
    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop)
            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0)
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 1))))))))

def nrGraph : Item :=
Mettapedia.Languages.Megalodon.NativeAdmission.Item.definition
  "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688"
  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.all
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))))))))
  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeLam
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop)))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7)
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5)
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))))))))))))

def nrGraphZero : Item :=
Mettapedia.Languages.Megalodon.NativeAdmission.Item.theorem_
  "87808ea7afe4abaac2f5537926b3f5aa22f42a8fd3ae8dbc26e5b2a1c8fdf8e6"
  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeAll
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                            "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))))))
  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeLam
    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop)))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5)
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3)
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 1)))))))))

def nrGraphSuccessor : Item :=
Mettapedia.Languages.Megalodon.NativeAdmission.Item.theorem_
  "96c29789eac08b76f3030c1438fa2ff7ca40becb4c3216e4f228b35b1177143b"
  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeAll
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                  "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                  "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))))))))
  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeLam
    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                  "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop)))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7)
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5)
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0)
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 2)
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 1))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0))))))))))))))

def nrGraphNatural : Item :=
Mettapedia.Languages.Megalodon.NativeAdmission.Item.theorem_
  "0c18ad07c050c2a11411a41a052edf0b03abaee9a9944d919b0661c4452a4e71"
  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeAll
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                  "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                          "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))))))))))
  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeLam
    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                  "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                    "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                            "a7a2e1cb291bdfdc11661c2875e62b3fb8fb502cb3c1f594c4e6f50789e4f911")
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                  "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                    "877913cb39467cac5218f875864ba9d5f794a079e124c150a2aa99edb28f6861")
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0))))))))))))))

def nrGraphExists : Item :=
Mettapedia.Languages.Megalodon.NativeAdmission.Item.theorem_
  "e9bc3463274b5a8e5dfe44cf95087e1baa1298d95aa1f8a771bfa5a4ae9b58bd"
  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeAll
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                        "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                      "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                    "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))))))))
  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeLam
    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                        "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                              "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                            "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                              "cb01597ac16d6df38d6f584e549edd3603cd7abc72e2a1cfcc2ba44fc649758e")
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                            "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                  "87808ea7afe4abaac2f5537926b3f5aa22f42a8fd3ae8dbc26e5b2a1c8fdf8e6")
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                            "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                          "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0)
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                              "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5)
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                            "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                      "cb01597ac16d6df38d6f584e549edd3603cd7abc72e2a1cfcc2ba44fc649758e")
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                    "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6)
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3)
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                                "96c29789eac08b76f3030c1438fa2ff7ca40becb4c3216e4f228b35b1177143b")
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0))))))))))))))))

def nrGraphZeroUnique : Item :=
Mettapedia.Languages.Megalodon.NativeAdmission.Item.theorem_
  "f91a57a5bd78694e5884aa1b325509ba1c324bb735928e38924bb7081d7e567b"
  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeAll
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                      "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87")))
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                  "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                          "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))))))))
  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeLam
    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                      "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87")))
          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                  "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 1)
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                            "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                      "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 1)))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                          "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                          "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6)
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 4)
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))))))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                              "0f730be4ec19d9c14f6f80059c561f714dcecb54d8fa04f3570d0607e71d8331")
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5)))))))))))))

def nrGraphSuccessorInverse : Item :=
Mettapedia.Languages.Megalodon.NativeAdmission.Item.theorem_
  "b6f91526fffc2274b066d609cf61e85df750465fdcfcc883602660ea5efff74c"
  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeAll
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                      "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87")))
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                          "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                          "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                      "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                            "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                              "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                    "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3)
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))))))))))))))
  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeLam
    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                      "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87")))
          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                          "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                          "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                      "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                              "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3)))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                        "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5)
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                      "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                          "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                        "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                              "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))))))))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                          "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                        "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                  "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7)
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                    "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                  "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var
                                                                  0))
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 9))
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 8))
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                        "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6)
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))))))))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                          "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                        "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6)
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                  "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7)
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7)
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                    "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                  "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var
                                                                  0))
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 9))
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 8))
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                        "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6)
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6)
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))))))))))))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                        "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                      "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5)
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5)
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                              "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                  "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                      "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))))))))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                              "fec5ab340a042c8361bb0564ac980cfe10dabcf5c4aeacb0746c0daa4ac55417")
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                            "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                      "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5)
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5)
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                    "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                        "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                      "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var
                                                                      0))
                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                    7))
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                            "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))))))))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                          "0f730be4ec19d9c14f6f80059c561f714dcecb54d8fa04f3570d0607e71d8331")
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 2)
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                              "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                        "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7)
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                      "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                          "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                        "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var
                                                                        0))
                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                      9))
                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                    8))
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                              "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6)
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                          2)))))))))))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 1))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0))))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                        "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                      "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7)
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                              "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                  "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 9))
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 8))
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                      "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6)
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))))))))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                      "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                                "7f6246d08629eeb16eab93529ffe4f929f43344833ab88c7786393693520e82b")
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                              "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6)
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                        "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7)
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7)
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                      "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                          "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                        "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var
                                                                        0))
                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                      9))
                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                    8))
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                              "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6)
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6)
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                            2)))))))))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                                            "96c29789eac08b76f3030c1438fa2ff7ca40becb4c3216e4f228b35b1177143b")
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0)))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                    "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7)
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7)
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                        "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                                          "cb01597ac16d6df38d6f584e549edd3603cd7abc72e2a1cfcc2ba44fc649758e")
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                              "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                            "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var
                                                                            0))
                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                          9))
                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                        8))
                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                      7))
                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                    6))
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                  "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var
                                                                  0))
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                    6)
                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                    1))
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                  0)))
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6)
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                2))))))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                                            "7f6246d08629eeb16eab93529ffe4f929f43344833ab88c7786393693520e82b")
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                          "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var
                                                                          0))
                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                        8))
                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                      7))
                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                    6))
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5)
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5)
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                                                    "284ee58e7aea454281b73a0d0acb6efade8eeb4f2f3bf29aaf48a8fef862ceff")
                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base
                                                                    0))
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0))
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                            "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var
                                                                            0))
                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                          9))
                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                        8))
                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                      7))
                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                    6))
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))))
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 2)))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0)
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                  "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var
                                                                  0))
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                    6)
                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                    1))
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                  2)))
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6)
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                2)))))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                                            "0f730be4ec19d9c14f6f80059c561f714dcecb54d8fa04f3570d0607e71d8331")
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5)
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))))))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 5)
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0)))))))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                            "eb8814e5b67181dcc2fdd7f757e9f1e3c90bcd9b3117f2bb9aa7650cdaac5b42")
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                          "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                    "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7)
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                  "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                      "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                    "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var
                                                                    0))
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 9))
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 8))
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                          "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6)
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))))))))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0))))))))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                  "7f6246d08629eeb16eab93529ffe4f929f43344833ab88c7786393693520e82b")
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3)))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                          "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5)
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                        "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                            "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                          "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))))))))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                        "87808ea7afe4abaac2f5537926b3f5aa22f42a8fd3ae8dbc26e5b2a1c8fdf8e6")
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                      "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5)
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 3)
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                      "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                          "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                        "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                              "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))))))))))))))))))))

def nrGraphFunctional : Item :=
Mettapedia.Languages.Megalodon.NativeAdmission.Item.theorem_
  "653fd64163dedfee84cae7ddf348949c2cfc59c5db33f3b662cc8fba4f41634a"
  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeAll
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                      "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87")))
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                          "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                          "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                            "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                          "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                            "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                    "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))))))))))))
  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeLam
    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                      "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87")))
          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                          "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                          "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                            "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                              "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                        "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                        "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                        "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                          "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                  "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                        "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6)
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                          "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6)
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                  "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))))))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                            "77e10b9988f12dc528ad73906107175925091da967df0552db1799b699955593")
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                              "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                        "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))))))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 1))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 2)))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                      "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                      "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                        "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                      "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6)
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                        "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6)
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                  "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                      "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                    "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var
                                                                    0))
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 8))
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                          "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5)
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)))))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                      "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                          "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                        "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var
                                                                        0))
                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                      8))
                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                    7))
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                              "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5)
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 1)
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                            "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                            "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                          "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var
                                                                          0))
                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                        8))
                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                      7))
                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                    6))
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5)
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 1)
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                  "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var
                                                                  0))
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                  "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                                "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var
                                                                                0))
                                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                              9))
                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                            8))
                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                          7))
                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                        6))
                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                      4))
                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                    0)))
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                      "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var
                                                                      0))
                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                        6)
                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                        4))
                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                      0)))
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                  2)))
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                                "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var
                                                                                0))
                                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                              9))
                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                            8))
                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                          7))
                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                        6))
                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                      4))
                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                    1))
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                                    "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var
                                                                                    0))
                                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                  9))
                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                8))
                                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                              7))
                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                            6))
                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                          4))
                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                        0))
                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                                "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var
                                                                                0))
                                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                  6)
                                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                  4))
                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                1)))
                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                            3))
                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                                    "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var
                                                                                    0))
                                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                      6)
                                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                      4))
                                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                    0)))
                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                2))
                                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                                        "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var
                                                                                        0))
                                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                      1))
                                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                    0))
                                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                                            "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var
                                                                                            0))
                                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                              6)
                                                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                              4))
                                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                            1)))
                                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                            6)
                                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                            4))
                                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                          0)))
                                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                                                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                                                                                  "0224060d7b7d5b6b2e8e4157524c8e4a18e5d17073c5b2fb2bb0c2583274fbc7")
                                                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var
                                                                                                  0))
                                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                                3))
                                                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                                  6)
                                                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                                  4))
                                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                                1)))
                                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                            2))
                                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                                                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                                                                                  "284ee58e7aea454281b73a0d0acb6efade8eeb4f2f3bf29aaf48a8fef862ceff")
                                                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var
                                                                                                  0))
                                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                                    6)
                                                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                                    4))
                                                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                                  1)))
                                                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                              3))
                                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp
                                                                                            3)))
                                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                                                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                                                                                    "0224060d7b7d5b6b2e8e4157524c8e4a18e5d17073c5b2fb2bb0c2583274fbc7")
                                                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var
                                                                                                    0))
                                                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                                      6)
                                                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                                      4))
                                                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                                    1)))
                                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                                    6)
                                                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                                    4))
                                                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                                  0)))
                                                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                              2))
                                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp
                                                                                            0))
                                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp
                                                                                          2))))
                                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp
                                                                                        0)
                                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var
                                                                                          0)
                                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                                                "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var
                                                                                                0))
                                                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                                  7)
                                                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                                  5))
                                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                                2)))
                                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                                7)
                                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                                5))
                                                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                              0)))))
                                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                                                                          "0f730be4ec19d9c14f6f80059c561f714dcecb54d8fa04f3570d0607e71d8331")
                                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var
                                                                                          0))
                                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                            6)
                                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                            4))
                                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                          1))))))
                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp
                                                                                        10)
                                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                        1))
                                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                      0))
                                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp
                                                                                    3))
                                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp
                                                                                  2))))
                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                                                                  "fec5ab340a042c8361bb0564ac980cfe10dabcf5c4aeacb0746c0daa4ac55417")
                                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                                                "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var
                                                                                                0))
                                                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                              9))
                                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                            8))
                                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                          7))
                                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                        6))
                                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                      4))
                                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                    0)))
                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                                      "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var
                                                                                      0))
                                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                        6)
                                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                        4))
                                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                      0)))
                                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                  2)))
                                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp
                                                                              3))))
                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                                                              "fec5ab340a042c8361bb0564ac980cfe10dabcf5c4aeacb0746c0daa4ac55417")
                                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                                            "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var
                                                                                            0))
                                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                          9))
                                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                        8))
                                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                      7))
                                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                    6))
                                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                  4))
                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                1)))
                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                                  "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var
                                                                                  0))
                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                    6)
                                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                    4))
                                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                  1)))
                                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                              3)))
                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp
                                                                          3))))
                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                                                          "eb8814e5b67181dcc2fdd7f757e9f1e3c90bcd9b3117f2bb9aa7650cdaac5b42")
                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                                        "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var
                                                                                        0))
                                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                      9))
                                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                    8))
                                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                  7))
                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                6))
                                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                              4))
                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                            0)))
                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                              "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var
                                                                              0))
                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                6)
                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                4))
                                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                              0)))
                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                          2)))
                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp
                                                                      1))))
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                                                      "eb8814e5b67181dcc2fdd7f757e9f1e3c90bcd9b3117f2bb9aa7650cdaac5b42")
                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                                    "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var
                                                                                    0))
                                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                  9))
                                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                                8))
                                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                              7))
                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                            6))
                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                          4))
                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                        1)))
                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                          "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var
                                                                          0))
                                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                            6)
                                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                            4))
                                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                          1)))
                                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db
                                                                      3)))
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp
                                                                  1))))))))))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                                                    "b6f91526fffc2274b066d609cf61e85df750465fdcfcc883602660ea5efff74c")
                                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var
                                                                    0))
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 8))
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 7))
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 1))))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                                                "b6f91526fffc2274b066d609cf61e85df750465fdcfcc883602660ea5efff74c")
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 7))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 6))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 1))))))))))))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                            "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                              "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                            "0224060d7b7d5b6b2e8e4157524c8e4a18e5d17073c5b2fb2bb0c2583274fbc7")
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                            "284ee58e7aea454281b73a0d0acb6efade8eeb4f2f3bf29aaf48a8fef862ceff")
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                                      "f91a57a5bd78694e5884aa1b325509ba1c324bb735928e38924bb7081d7e567b")
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 4))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 1))))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                                  "f91a57a5bd78694e5884aa1b325509ba1c324bb735928e38924bb7081d7e567b")
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 4))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0)))))))))))))))))

def nrRecursor : Item :=
Mettapedia.Languages.Megalodon.NativeAdmission.Item.definition
  "07c6d5bb8b1b51acf568b644d496c3805612be5b440432b88ee69c28280f8c5d"
  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.all
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))))))))
  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeLam
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))))))))

def nrRecursorGraph : Item :=
Mettapedia.Languages.Megalodon.NativeAdmission.Item.theorem_
  "fcb71074cf42d8987389724f3694303d976cba70c34d7ab333bd93760834c280"
  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeAll
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                          "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                            "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                    "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                      "07c6d5bb8b1b51acf568b644d496c3805612be5b440432b88ee69c28280f8c5d")
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))))))))))
  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeLam
    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                          "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                            "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 1)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                          "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                      "e9bc3463274b5a8e5dfe44cf95087e1baa1298d95aa1f8a771bfa5a4ae9b58bd")
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0))))))))))))

def nrRecursorZero : Item :=
Mettapedia.Languages.Megalodon.NativeAdmission.Item.theorem_
  "22e3b03874328016e540ab23671ef8d65aedae835b5a6300a63169ce15d2cf5c"
  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeAll
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                      "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87")))
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                            "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                          "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                    "07c6d5bb8b1b51acf568b644d496c3805612be5b440432b88ee69c28280f8c5d")
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)))))))))))
  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeLam
    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                      "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87")))
          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                            "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                    "f91a57a5bd78694e5884aa1b325509ba1c324bb735928e38924bb7081d7e567b")
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 1))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                      "07c6d5bb8b1b51acf568b644d496c3805612be5b440432b88ee69c28280f8c5d")
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                        "fcb71074cf42d8987389724f3694303d976cba70c34d7ab333bd93760834c280")
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                            "a7a2e1cb291bdfdc11661c2875e62b3fb8fb502cb3c1f594c4e6f50789e4f911")
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))))))))))))

def nrRecursorSuccessor : Item :=
Mettapedia.Languages.Megalodon.NativeAdmission.Item.theorem_
  "1d0d22f0333064db2f7008d20316b35d84fc8bf4adc664060b8860cd94977e5f"
  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeAll
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                      "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87")))
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                          "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                          "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                              "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                              "07c6d5bb8b1b51acf568b644d496c3805612be5b440432b88ee69c28280f8c5d")
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                          "07c6d5bb8b1b51acf568b644d496c3805612be5b440432b88ee69c28280f8c5d")
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))))))))))))
  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeLam
    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                      "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87")))
          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                          "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                          "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                              "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                            "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                              "07c6d5bb8b1b51acf568b644d496c3805612be5b440432b88ee69c28280f8c5d")
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                                        "653fd64163dedfee84cae7ddf348949c2cfc59c5db33f3b662cc8fba4f41634a")
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 4))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 3))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                                "877913cb39467cac5218f875864ba9d5f794a079e124c150a2aa99edb28f6861")
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 1)))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                      "07c6d5bb8b1b51acf568b644d496c3805612be5b440432b88ee69c28280f8c5d")
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                  "07c6d5bb8b1b51acf568b644d496c3805612be5b440432b88ee69c28280f8c5d")
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                                  "96c29789eac08b76f3030c1438fa2ff7ca40becb4c3216e4f228b35b1177143b")
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                    "07c6d5bb8b1b51acf568b644d496c3805612be5b440432b88ee69c28280f8c5d")
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0)))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                                  "fcb71074cf42d8987389724f3694303d976cba70c34d7ab333bd93760834c280")
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 2))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                          "877913cb39467cac5218f875864ba9d5f794a079e124c150a2aa99edb28f6861")
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 1)))))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                              "fcb71074cf42d8987389724f3694303d976cba70c34d7ab333bd93760834c280")
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 1))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0))))))))))))))

def nrGraphAgrees : Item :=
Mettapedia.Languages.Megalodon.NativeAdmission.Item.theorem_
  "3861803eb83e09998ef34c354bc50aff520951f2031b7842559c0195eed45b6a"
  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeAll
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                        "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                              "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                              "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                        "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))))))))))))))
  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeLam
    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                        "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                              "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                              "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                        "ad9228a14dce06c1cbff1f7336645797c843930d4066a43ea8871617dbd5e688")
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                  "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                        "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6)))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                      "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                            "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                  "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 8))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                            "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                  "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 8))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7)
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5)
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7)
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))))))))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                          "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                              "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                            "fec5ab340a042c8361bb0564ac980cfe10dabcf5c4aeacb0746c0daa4ac55417")
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                  "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0)))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 2)
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                  "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                        "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 8))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                      "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))))))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 1))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0))))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                          "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 8))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                              "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 8))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                    "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                                      "7f6246d08629eeb16eab93529ffe4f929f43344833ab88c7786393693520e82b")
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                            "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 8))
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7)
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                          "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5)
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7)
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                                          "877913cb39467cac5218f875864ba9d5f794a079e124c150a2aa99edb28f6861")
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 8))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 1)))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                                            "0224060d7b7d5b6b2e8e4157524c8e4a18e5d17073c5b2fb2bb0c2583274fbc7")
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5)
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5)
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7)
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0)
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                                "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6)
                                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6)
                                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                                          "0f730be4ec19d9c14f6f80059c561f714dcecb54d8fa04f3570d0607e71d8331")
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5)
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 5)
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 1)))))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                                  "fec5ab340a042c8361bb0564ac980cfe10dabcf5c4aeacb0746c0daa4ac55417")
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                        "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 8))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                      "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 1))))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                              "eb8814e5b67181dcc2fdd7f757e9f1e3c90bcd9b3117f2bb9aa7650cdaac5b42")
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                    "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 8))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                  "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0))))))))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                    "7f6246d08629eeb16eab93529ffe4f929f43344833ab88c7786393693520e82b")
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                          "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6)))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                        "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                    "a7a2e1cb291bdfdc11661c2875e62b3fb8fb502cb3c1f594c4e6f50789e4f911")
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5)))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 2))))))))))))))

def nrRecursorUnique : Item :=
Mettapedia.Languages.Megalodon.NativeAdmission.Item.theorem_
  "70070a87b34c9fe09d07002bd1a4cc494307f58100fa9aa1954e741d15c1d028"
  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeAll
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                          "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                            "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5)))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                  "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                  "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3)
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5)
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                  "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                  "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                              "07c6d5bb8b1b51acf568b644d496c3805612be5b440432b88ee69c28280f8c5d")
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))))))))))))
  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeLam
    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                          "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                            "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5)))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                  "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                  "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3)
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5)
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                  "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                                  "3861803eb83e09998ef34c354bc50aff520951f2031b7842559c0195eed45b6a")
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 2))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 1))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                              "07c6d5bb8b1b51acf568b644d496c3805612be5b440432b88ee69c28280f8c5d")
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                                "fcb71074cf42d8987389724f3694303d976cba70c34d7ab333bd93760834c280")
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 3))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0)))))))))))))))

def nrRecursorChoiceIndependent : Item :=
Mettapedia.Languages.Megalodon.NativeAdmission.Item.theorem_
  "774b429367f63d3e6b40bf4661f1818d19b4a7cb60f28dccfc014f27da5348f8"
  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeAll
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                      "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87")))
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                          "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                          "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                  "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                    "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                    "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                "07c6d5bb8b1b51acf568b644d496c3805612be5b440432b88ee69c28280f8c5d")
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                              "07c6d5bb8b1b51acf568b644d496c3805612be5b440432b88ee69c28280f8c5d")
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))))))))))))))
  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeLam
    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                      "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87")))
          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                          "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                          "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                  "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                              "70070a87b34c9fe09d07002bd1a4cc494307f58100fa9aa1954e741d15c1d028")
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 1))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                            "07c6d5bb8b1b51acf568b644d496c3805612be5b440432b88ee69c28280f8c5d")
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                              "22e3b03874328016e540ab23671ef8d65aedae835b5a6300a63169ce15d2cf5c")
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 3))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0)))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                              "1d0d22f0333064db2f7008d20316b35d84fc8bf4adc664060b8860cd94977e5f")
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 3))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 2))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0))))))))))))))

def nrRecursion : Item :=
Mettapedia.Languages.Megalodon.NativeAdmission.Item.theorem_
  "c68747a1a75e217cf39d616a8d4b4d58b3cb63e8e0a2cedb9e8b17094aaae1f4"
  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeAll
    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                      "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87")))
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                          "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                          "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                              "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                          "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                              "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                    "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                          "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                          "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3)
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5)
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                        "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6)))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                              "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                              "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6)
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                              "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                              "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))))))))))))))))))
  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeLam
    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                      "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                "5bf697cb0d1cdefbe881504469f6c48cc388994115b82514dfc4fb5e67ac1a87")))
          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                          "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                          "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))
            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)))
                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termLam
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofLam
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.prop))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                              "912ad2cdc2d23bb8aa0a5070945f2a90976a948b0e8308917244591f3747f099")
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))
                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                              "cb01597ac16d6df38d6f584e549edd3603cd7abc72e2a1cfcc2ba44fc649758e")
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0)))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.lam
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                  "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                        "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                    "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                              "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                              "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3)
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5)
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                            "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6)))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                  "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                  "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6)
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                  "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 7))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                  "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))))))))))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                      "07c6d5bb8b1b51acf568b644d496c3805612be5b440432b88ee69c28280f8c5d")
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                "7f6246d08629eeb16eab93529ffe4f929f43344833ab88c7786393693520e82b")
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                      "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                "07c6d5bb8b1b51acf568b644d496c3805612be5b440432b88ee69c28280f8c5d")
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                  "87fba1d2da67f06ec37e7ab47c3ef935ef8137209b42e40205afb5afd835b738")
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                            "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                            "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                          "07c6d5bb8b1b51acf568b644d496c3805612be5b440432b88ee69c28280f8c5d")
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                      "07c6d5bb8b1b51acf568b644d496c3805612be5b440432b88ee69c28280f8c5d")
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                          "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5)))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3)
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5)
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                            "07c6d5bb8b1b51acf568b644d496c3805612be5b440432b88ee69c28280f8c5d")
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))))))))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                            "22e3b03874328016e540ab23671ef8d65aedae835b5a6300a63169ce15d2cf5c")
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 2))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0)))
                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                  "7f6246d08629eeb16eab93529ffe4f929f43344833ab88c7786393693520e82b")
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                            "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                            "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2)
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                          "07c6d5bb8b1b51acf568b644d496c3805612be5b440432b88ee69c28280f8c5d")
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                      "07c6d5bb8b1b51acf568b644d496c3805612be5b440432b88ee69c28280f8c5d")
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4)
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.arr
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                          "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5)))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3)
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5)
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))))))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.all
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.base 0)
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.imp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                "b0f30dad7d3c1872475b404011e17fc1f8e58af0c6e8f60885d600892852f2be")
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                "0e7f6a08bb4627c0ddedda9151c907864644724fa34b3e850be0bfb73ba13e89")
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.typeApp
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.named
                                                            "07c6d5bb8b1b51acf568b644d496c3805612be5b440432b88ee69c28280f8c5d")
                                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 6))
                                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 5))
                                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.app
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1)
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0)))))))))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                                "1d0d22f0333064db2f7008d20316b35d84fc8bf4adc664060b8860cd94977e5f")
                                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                            (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                          (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 2))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 1))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0)))
                          (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.proofApp
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.termApp
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.typeApp
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.known
                                          "70070a87b34c9fe09d07002bd1a4cc494307f58100fa9aa1954e741d15c1d028")
                                        (Mettapedia.Languages.Megalodon.MathdataKernel.Tp.var 0))
                                      (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 4))
                                    (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 3))
                                  (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 2))
                                (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 1))
                              (Mettapedia.Languages.Megalodon.MathdataKernel.Tm.db 0))
                            (Mettapedia.Languages.Megalodon.MathdataKernel.Pf.hyp 0))))))))))))))

def items : List Item := [ncAnd, naturalClosure, ncAndIntro, ncAndLeft, ncAndRight, naturalClosureZero, naturalClosureSuccessor, naturalClosureInduction, nrFalse, nrEq, nrExists, nrEqRefl, nrEqSym, nrEqTrans, nrExistsIntro, nrGraph, nrGraphZero, nrGraphSuccessor, nrGraphNatural, nrGraphExists, nrGraphZeroUnique, nrGraphSuccessorInverse, nrGraphFunctional, nrRecursor, nrRecursorGraph, nrRecursorZero, nrRecursorSuccessor, nrGraphAgrees, nrRecursorUnique, nrRecursorChoiceIndependent, nrRecursion]

def inputBytes : Nat := 88744

end Mettapedia.Languages.Megalodon.NaturalRecursion.Evidence
