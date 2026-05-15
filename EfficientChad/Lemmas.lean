import Lean.Elab.Tactic.Omega

namespace EfficientChad

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

theorem «lemma-unit»
    (cmonad φe1 φeout : Int)
    (p1' : φeout = φe1)
    (envlen' : Int)
    (p2 : cmonad = 1 + (envlen' + 1))
    (envlen : Int)
    (p3 : envlen' = envlen) :
    5 + cmonad - (1 + 0) - φe1 + φeout - envlen ≤ 34 := by
  omega

theorem «lemma-pair-nothing»
    (crun1 crun2 czero1 czero2 ccall1 ccall2 cmonad cmonad1 cmonad2 : Int)
    (φd1 φd2 φe1 φe2 φe3 φeout evc1 evc2 : Int)
    (pzero1 : czero1 ≤ 2)
    (pzero2 : czero2 ≤ 2)
    (pφd1 : φd1 = 1)
    (pφd2 : φd2 = 1)
    (pφdenvout : φeout = φe3)
    (envlen : Int)
    (prunbind2 : cmonad = cmonad1 + 1 + cmonad2 - envlen)
    (k1 : crun1 + ccall1 + cmonad1 - φd1 - φe1 + φe2 - envlen ≤ 34 * evc1)
    (k2 : crun2 + ccall2 + cmonad2 - φd2 - φe2 + φe3 - envlen ≤ 34 * evc2) :
    1 + (1 + crun1 + crun2) + 10
      + (1 + (4 + (2 + czero2) + ccall2)
        + (1 + (4 + (2 + czero1) + ccall1) + 2))
      + cmonad - (1 + 0) - φe1 + φeout - envlen
      ≤ 34 * (1 + evc1 + evc2) := by
  omega

theorem «lemma-pair-just»
    (crun1 crun2 ccall1 ccall2 cmonad cmonad1 cmonad2 : Int)
    (φd1 φd2 φe1 φe2 φe3 φeout evc1 evc2 : Int)
    (pφdenvout : φeout = φe3)
    (envlen : Int)
    (prunbind2 : cmonad = cmonad1 + 1 + cmonad2 - envlen)
    (k1 : crun1 + ccall1 + cmonad1 - φd1 - φe1 + φe2 - envlen ≤ 34 * evc1)
    (k2 : crun2 + ccall2 + cmonad2 - φd2 - φe2 + φe3 - envlen ≤ 34 * evc2) :
    1 + (1 + crun1 + crun2) + 10
      + (1 + (6 + ccall2) + (1 + (6 + ccall1) + 2))
      + cmonad - (1 + φd1 + φd2) - φe1 + φeout - envlen
      ≤ 34 * (1 + evc1 + evc2) := by
  omega

theorem «lemma-var»
    (cmonad φd φe1 φe2 φeout : Int)
    (p1 : φeout = φe2)
    (envlen cplus envlen' : Int)
    (prunadd2 : cmonad = 2 + cplus + envlen')
    (plenmap : envlen = envlen')
    (x16 x17 : Int)
    (pφaddlet : φe2 = φe1 - x16 + x17)
    (x18 : Int)
    (pplus : cplus - φd - x16 + x18 ≤ 0)
    (paddlet : x17 = x18) :
    5 + cmonad - φd - φe1 + φeout - envlen ≤ 34 := by
  omega

theorem «lemma-let»
    (evc1 evc2 crun1 crun2 crun2p : Int)
    (equals_crun2 : crun2 = crun2p)
    (czero ccall2 cmonad cmonad2 cbp1 cbp2 : Int)
    (equals_ccall2 : ccall2 = cbp2)
    (cmonad1 cmonad2p : Int)
    (equal_cmonad2 : cmonad2 = cmonad2p)
    (envlen : Int)
    (prunbind2 : cmonad = cmonad2 + (5 + cbp1) + cmonad1 - envlen)
    (φd φe1 φeout φzerores φdx φdxp : Int)
    (equal_φdx : φdx = φdxp)
    (φdenv2 φdenv2p : Int)
    (equal_φdenv2 : φdenv2 = φdenv2p)
    (φdenv3 : Int)
    (prunbind1φ : φeout = φdenv3)
    (pczerosmall : czero ≤ 2)
    (pφzeroressmall : φzerores = 1)
    (k2 : crun2p + cbp2 + cmonad2p - φd - (φzerores + φe1)
        + (φdxp + φdenv2p) - (1 + envlen) ≤ 34 * evc2)
    (k1 : crun1 + cbp1 + cmonad1 - φdx - φdenv2 + φdenv3 - envlen ≤ 34 * evc1) :
    1 + crun1 + (3 + (1 + crun2 + 6))
      + (1 + (1 + czero + (4 + ccall2)) + 2)
      + cmonad - φd - φe1 + φeout - envlen
      ≤ 34 * (1 + evc1 + evc2) := by
  omega

theorem «lemma-prim»
    (crun1 cdprim ccall1 cmonad1 φdx φd φe1 φe2 evc1 : Int)
    (lem3 : cdprim - φd + φdx ≤ 14)
    (envlen : Int)
    (k1 : crun1 + ccall1 + cmonad1 - φdx - φe1 + φe2 - envlen ≤ 34 * evc1) :
    1 + crun1 + 6 + (3 + (3 + (2 + cdprim)) + ccall1)
      + cmonad1 - φd - φe1 + φe2 - envlen ≤ 34 * (1 + evc1) := by
  omega

theorem «lemma-fst»
    (crun1 czero ccall1 cmonad1 φd φe1 φe2 φd1 evc1 : Int)
    (pzero : czero ≤ 2)
    (pφd1 : φd1 = 1)
    (envlen : Int)
    (k1 : crun1 + ccall1 + cmonad1 - (1 + φd + φd1) - φe1 + φe2 - envlen
        ≤ 34 * evc1) :
    1 + crun1 + 6 + (3 + (2 + czero) + ccall1)
      + cmonad1 - φd - φe1 + φe2 - envlen ≤ 34 * (1 + evc1) := by
  omega

theorem «lemma-snd»
    (crun1 czero ccall1 cmonad1 φd φe1 φe2 φd1 evc1 : Int)
    (pzero : czero ≤ 2)
    (pφd1 : φd1 = 1)
    (envlen : Int)
    (k1 : crun1 + ccall1 + cmonad1 - (1 + φd1 + φd) - φe1 + φe2 - envlen
        ≤ 34 * evc1) :
    1 + crun1 + 6 + (3 + (1 + czero + 1) + ccall1)
      + cmonad1 - φd - φe1 + φe2 - envlen ≤ 34 * (1 + evc1) := by
  omega

theorem «lemma-inl-nothing»
    (crun1 czero ccall1 cmonad1 φe1 φe2 φd1 evc1 : Int)
    (pzero : φd1 = 1)
    (pφd1 : czero ≤ 2)
    (envlen : Int)
    (k1 : crun1 + ccall1 + cmonad1 - φd1 - φe1 + φe2 - envlen ≤ 34 * evc1) :
    1 + crun1 + 6 + (3 + (2 + czero) + ccall1)
      + cmonad1 - (1 + 0) - φe1 + φe2 - envlen ≤ 34 * (1 + evc1) := by
  omega

theorem «lemma-inl-inj1»
    (crun1 ccall1 cmonad1 φe1 φe2 φd1 evc1 envlen : Int)
    (k1 : crun1 + ccall1 + cmonad1 - φd1 - φe1 + φe2 - envlen ≤ 34 * evc1) :
    1 + crun1 + 6 + (5 + ccall1)
      + cmonad1 - (1 + φd1) - φe1 + φe2 - envlen ≤ 34 * (1 + evc1) := by
  omega

theorem «lemma-inl-inj2»
    (crun1 czero ccall1 cmonad1 φe1 φe2 φd1 φd2 evc1 : Int)
    (pzero : φd1 = 1)
    (pφd1 : czero ≤ 2)
    (pφd2 : 0 ≤ φd2)
    (sym_φd2 : -φd2 ≤ -φd2)
    (envlen : Int)
    (k1 : crun1 + ccall1 + cmonad1 - φd1 - φe1 + φe2 - envlen ≤ 34 * evc1) :
    1 + crun1 + 6 + (3 + (2 + czero) + ccall1)
      + cmonad1 - (1 + φd2) - φe1 + φe2 - envlen ≤ 34 * (1 + evc1) := by
  omega

theorem «lemma-case-1»
    (evc1 crun1 crun2 czero ccall2 cmonad2_B ccall1 cmonad1_B cmonad_A evc2 : Int)
    (envlen φd φdx φenvin φdenv2_A φdenv2_B φdenvout_B φzero : Int)
    (crun2_X ccall2_X cmonad2_X φdx_X φdenv2_X : Int)
    (eq_crun2 : crun2 = crun2_X)
    (eq_ccall2 : ccall2 = ccall2_X)
    (eq_cmonad2 : cmonad2_B = cmonad2_X)
    (eq_φdx : φdx = φdx_X)
    (eq_φdenv2 : φdenv2_B = φdenv2_X)
    (runbindres2 : cmonad_A = cmonad2_B + (6 + ccall1) + cmonad1_B - envlen)
    (eq_φdenv2out : φdenv2_A = φdenvout_B)
    (pczero : czero ≤ 2)
    (pφzero : φzero = 1)
    (k1 : crun1 + ccall1 + cmonad1_B - (1 + φdx) - φdenv2_B
        + φdenvout_B - envlen ≤ 34 * evc1)
    (k2 : crun2_X + ccall2_X + cmonad2_X - φd - (φzero + φenvin)
        + (φdx_X + φdenv2_X) - (1 + envlen) ≤ 34 * evc2) :
    1 + crun1 + (3 + (1 + crun2 + 6))
      + (1 + (1 + czero + (4 + ccall2)) + 2)
      + cmonad_A - φd - φenvin + φdenv2_A - envlen
      ≤ 34 * (1 + evc1 + evc2) := by
  omega

theorem «lemma-φ-less-size»
    (φx φy sσ : Int)
    (k1 : φx ≤ sσ)
    (sτ : Int)
    (k2 : φy ≤ sτ) :
    1 + φx + φy ≤ 1 + (sσ + sτ) := by
  omega

theorem «lemma-th2»
    (φd envlen czeroenv φdenvin crun1 ccall1 cmonad1 : Int)
    (crun2 ccall2 cmonad2 φdenvout2 : Int)
    (eq_crun : crun1 = crun2)
    (eq_ccall : ccall1 = ccall2)
    (eq_cmonad : cmonad1 = cmonad2)
    (bound_φenv : φdenvin ≤ φdenvout2)
    (bound_czeroenv : czeroenv ≤ 1 + 3 * envlen)
    (sym_φdenvout2 : -φdenvout2 ≤ -φdenvout2)
    (sym_result : 1 + (1 + (1 + (1 + envlen))) ≤ 1 + (1 + (1 + (1 + envlen))))
    (primal_cost codom_size : Int)
    (bound_φd : φd ≤ codom_size)
    (k1 : crun2 + ccall2 + cmonad2 - φd - φdenvin + φdenvout2 - envlen
        ≤ 34 * primal_cost) :
    1 + (1 + (1 + crun1) + 1 + ccall1) + czeroenv + cmonad1
      ≤ 5 + 34 * primal_cost + codom_size + 4 * envlen := by
  omega

end EfficientChad
