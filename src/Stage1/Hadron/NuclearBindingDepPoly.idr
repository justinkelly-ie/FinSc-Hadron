module Stage1.Hadron.NuclearBindingDepPoly

import Data.Vect
import Stage0.BoxInt
import Stage1.Polynumber

%default total

------------------------------------------------------------------------
-- 1. WEIZSÄCKER LIQUID-DROP BINDING POLYNOMIALS (DEGREE 2)
------------------------------------------------------------------------

||| Coulomb repulsion energy polynomial in proton number Z:
||| P_Coulomb(Z) = Z(Z - 1) = -Z + Z^2.
||| Coeffs in degree order [0, 1, 2]: [0, -1, 1].
public export
weizsackerCoulombDepPoly : DepPolynumber 2
weizsackerCoulombDepPoly =
  MkDepPolynumber [ intToBoxInt 0
                  , intToBoxInt (-1)
                  , intToBoxInt 1
                  ]

||| Evaluates Coulomb repulsion factor Z(Z-1) for a nucleus of atomic number Z.
public export
evalCoulombFactor : (z : Nat) -> BoxInt
evalCoulombFactor z =
  evalDepPolynumber weizsackerCoulombDepPoly (natToBoxInt z)

||| Asymmetry energy polynomial in proton number Z for a given mass number A:
||| P_Asym(Z; A) = (A - 2Z)^2 = A^2 - 4AZ + 4Z^2.
||| Coeffs in degree order [0, 1, 2]: [A^2, -4A, 4].
public export
weizsackerAsymmetryDepPoly : (a : Nat) -> DepPolynumber 2
weizsackerAsymmetryDepPoly a =
  let aBox = natToBoxInt a
      aSq = mulBox aBox aBox
      neg4A = mulBox (intToBoxInt (-4)) aBox
      four = intToBoxInt 4
  in MkDepPolynumber [ aSq, neg4A, four ]

||| Evaluates asymmetry factor (A - 2Z)^2 for nucleus with mass number A and charge Z.
public export
evalAsymmetryFactor : (a : Nat) -> (z : Nat) -> BoxInt
evalAsymmetryFactor a z =
  evalDepPolynumber (weizsackerAsymmetryDepPoly a) (natToBoxInt z)

------------------------------------------------------------------------
-- 2. GELL-MANN–OKUBO HADRON MASS MULTIPLET POLYNOMIALS
------------------------------------------------------------------------

||| Scaled Baryon Octet Gell-Mann–Okubo mass polynomial in Hypercharge Y:
||| 4 M(Y) = (4 M_0 + 4 b I(I+1)) + (4 a) Y - b Y^2
||| Coeffs in degree order [0, 1, 2]: [4 M_0 + 4 b I(I+1), 4 a, -b].
public export
gellMannOkuboOctetDepPoly : (m0 : BoxInt) -> (a : BoxInt) -> (b : BoxInt) -> (iSquared : BoxInt) -> DepPolynumber 2
gellMannOkuboOctetDepPoly m0 a b iSquared =
  let c0 = addBox (mulBox (intToBoxInt 4) m0) (mulBox (intToBoxInt 4) (mulBox b iSquared))
      c1 = mulBox (intToBoxInt 4) a
      c2 = negBox b
  in MkDepPolynumber [ c0, c1, c2 ]

||| Linear Baryon Decuplet Gell-Mann–Okubo mass polynomial in Hypercharge Y:
||| M(Y) = M_Delta - deltaM * (1 - Y) = (M_Delta - deltaM) + deltaM * Y.
||| Degree 1 polynomial in hypercharge Y reflecting equal spacing:
||| Coeffs in degree order [0, 1]: [M_Delta - deltaM, deltaM].
public export
gellMannOkuboDecupletDepPoly : (mDelta : BoxInt) -> (deltaM : BoxInt) -> DepPolynumber 1
gellMannOkuboDecupletDepPoly mDelta deltaM =
  let c0 = subBox mDelta deltaM
      c1 = deltaM
  in MkDepPolynumber [ c0, c1 ]

||| Evaluates the Decuplet mass for a given Hypercharge Y.
public export
evalDecupletMass : (mDelta : BoxInt) -> (deltaM : BoxInt) -> (y : BoxInt) -> BoxInt
evalDecupletMass mDelta deltaM y =
  evalDepPolynumber (gellMannOkuboDecupletDepPoly mDelta deltaM) y

------------------------------------------------------------------------
-- 3. COMPILE-TIME INVARIANT AUDITS (RULE 01)
------------------------------------------------------------------------

||| Audits Coulomb liquid-drop polynomial evaluation across Helium-4 (Z=2), Carbon-12 (Z=6), and Iron-56 (Z=26):
||| Z=2: 2(1) = 2
||| Z=6: 6(5) = 30
||| Z=26: 26(25) = 650
public export
auditWeizsackerCoulombDepPolyProof : Bool
auditWeizsackerCoulombDepPolyProof =
  let he = evalCoulombFactor 2
      c  = evalCoulombFactor 6
      fe = evalCoulombFactor 26
  in unwrapBox he == 2 && unwrapBox c == 30 && unwrapBox fe == 650

||| Audits Asymmetry liquid-drop polynomial evaluation for Iron-56 (A=56, Z=26):
||| (A - 2Z)^2 = (56 - 52)^2 = 4^2 = 16.
public export
auditWeizsackerAsymmetryDepPolyProof : Bool
auditWeizsackerAsymmetryDepPolyProof =
  let asymFe = evalAsymmetryFactor 56 26
      asymHe = evalAsymmetryFactor 4 2
  in unwrapBox asymFe == 16 && unwrapBox asymHe == 0

||| Audits Gell-Mann–Okubo Decuplet equal-spacing mass relation across:
||| Delta (Y = 1): 1232 MeV
||| Sigma* (Y = 0): 1385 MeV (deltaM = 153)
||| Xi* (Y = -1): 1538 MeV
||| Omega- (Y = -2): 1691 MeV
public export
auditGellMannOkuboDecupletProof : Bool
auditGellMannOkuboDecupletProof =
  let mDelta = intToBoxInt 1232
      deltaM = intToBoxInt (-153)
      mDeltaVal = evalDecupletMass mDelta deltaM (intToBoxInt 1)
      mSigmaVal = evalDecupletMass mDelta deltaM (intToBoxInt 0)
      mXiVal    = evalDecupletMass mDelta deltaM (intToBoxInt (-1))
      mOmegaVal = evalDecupletMass mDelta deltaM (intToBoxInt (-2))
  in unwrapBox mDeltaVal == 1232
  && unwrapBox mSigmaVal == 1385
  && unwrapBox mXiVal    == 1538
  && unwrapBox mOmegaVal == 1691
