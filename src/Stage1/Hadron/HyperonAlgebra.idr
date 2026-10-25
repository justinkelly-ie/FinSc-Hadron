module Stage1.Hadron.HyperonAlgebra

import Stage0.BoxInt
import Stage0.Multiset
import Stage1.Carrier.Boxel
import Stage1.Basis.Coordinate
import Stage1.UnixelFraction
import Stage1.ExclusionPrinciple
import Stage1.Hadron.HadronicConfinement
import Stage1.Hadron.QuarkHadronAlgebra
import Stage1.Hadron.TypeIndexedMultiset
import Data.List

%default total

------------------------------------------------------------------------
-- 1. PURE MULTISET HYPERON CARRIER (3-Quark Strange & Heavy Baryons)
------------------------------------------------------------------------

||| Hyperon Species Specification.
public export
data HyperonSpec = LambdaZero | SigmaPlus | SigmaZero | SigmaMinus 
                 | XiZero | XiMinus | OmegaMinus | LambdaCharmPlus

public export
Eq HyperonSpec where
  LambdaZero      == LambdaZero      = True
  SigmaPlus       == SigmaPlus       = True
  SigmaZero       == SigmaZero       = True
  SigmaMinus      == SigmaMinus      = True
  XiZero          == XiZero          = True
  XiMinus         == XiMinus         = True
  OmegaMinus      == OmegaMinus      = True
  LambdaCharmPlus == LambdaCharmPlus = True
  _               == _               = False

public export
Show HyperonSpec where
  show LambdaZero      = "Lambda0 (uds)"
  show SigmaPlus       = "Sigma+ (uus)"
  show SigmaZero       = "Sigma0 (uds)"
  show SigmaMinus      = "Sigma- (dds)"
  show XiZero          = "Xi0 (uss)"
  show XiMinus         = "Xi- (dss)"
  show OmegaMinus      = "Omega- (sss)"
  show LambdaCharmPlus = "Lambda_c+ (udc)"

------------------------------------------------------------------------
-- 2. SMART CONSTRUCTORS FOR HYPERONS
------------------------------------------------------------------------

||| Constructs a Lambda0 (uds) 27-token Hadron Boxel across Red, Green, Blue color sectors.
%inline
public export
makeLambdaZeroBoxel : HadronBoxel
makeLambdaZeroBoxel =
  MkBoxel [ (MkVoxel 0 0 0, MkBoxInt 9)   -- Red Sector (uds)
          , (MkVoxel 1 1 1, MkBoxInt 9)   -- Green Sector (uds)
          , (MkVoxel 2 2 2, MkBoxInt 9)   -- Blue Sector (uds)
          ]

------------------------------------------------------------------------
-- 3. OBSERVATIONS & COLOR NEUTRALITY
------------------------------------------------------------------------

||| Evaluates mass tokens of a Hyperon Boxel (must equal 27 tokens = 1 amu).
%inline
public export
observeHyperonMassTokens : HadronBoxel -> Stage0.BoxInt.BoxInt
observeHyperonMassTokens (MkBoxel [(v1, Stage0.BoxInt.MkBoxInt w1), (v2, Stage0.BoxInt.MkBoxInt w2), (v3, Stage0.BoxInt.MkBoxInt w3)]) =
  Stage0.BoxInt.MkBoxInt (w1 + w2 + w3)
observeHyperonMassTokens b = totalBoxelWeight b

||| Verifies SU(3) color neutrality of a Hyperon Boxel.
%inline
public export
isHyperonColorNeutral : HadronBoxel -> Bool
isHyperonColorNeutral (MkBoxel [(_, Stage0.BoxInt.MkBoxInt w1), (_, Stage0.BoxInt.MkBoxInt w2), (_, Stage0.BoxInt.MkBoxInt w3)]) =
  w1 == w2 && w2 == w3
isHyperonColorNeutral b = isHadronBoxelColorNeutral b

------------------------------------------------------------------------
-- 4. FORMAL AUDIT PROOFS
------------------------------------------------------------------------

||| Audits Hyperon Mass Token Conservation and Color Neutrality:
||| 1. Lambda0 carries 27 mass tokens.
||| 2. Lambda0 is color neutral.
public export
auditHyperonAlgebraProof : Bool
auditHyperonAlgebraProof =
  (observeHyperonMassTokens makeLambdaZeroBoxel == intToBoxInt 27) &&
  isHyperonColorNeutral makeLambdaZeroBoxel
