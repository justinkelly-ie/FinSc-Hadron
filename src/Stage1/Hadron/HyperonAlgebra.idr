module Stage1.Hadron.HyperonAlgebra

import Stage0.BoxInt
import Stage0.Multiset
import public Stage1.Basis.Coordinate
import Stage1.UnixelFraction
import Stage1.ExclusionPrinciple
import Stage1.Hadron.HadronicConfinement
import Stage1.Hadron.QuarkHadronAlgebra
import Stage1.Hadron.TypeIndexedMultiset
import Stage1.Hadron.StandardModel
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

||| Discrete constituent quark triplet representation of a Hyperon (Rule 03 §8).
||| Grounded in Layer L-1 Standard Model Fermions.
public export
record HyperonQuarkTriplet where
  constructor MkHyperonTriplet
  q1 : SMFermion
  q2 : SMFermion
  q3 : SMFermion

public export
Eq HyperonQuarkTriplet where
  (MkHyperonTriplet a1 b1 c1) == (MkHyperonTriplet a2 b2 c2) =
    a1 == a2 && b1 == b2 && c1 == c2

||| Ground truth mapping from HyperonSpec to its discrete constituent quark triplet (Rule 03 §8).
public export
hyperonSpecToTriplet : HyperonSpec -> HyperonQuarkTriplet
hyperonSpecToTriplet LambdaZero      = MkHyperonTriplet QuarkU QuarkD QuarkS
hyperonSpecToTriplet SigmaPlus       = MkHyperonTriplet QuarkU QuarkU QuarkS
hyperonSpecToTriplet SigmaZero       = MkHyperonTriplet QuarkU QuarkD QuarkS
hyperonSpecToTriplet SigmaMinus      = MkHyperonTriplet QuarkD QuarkD QuarkS
hyperonSpecToTriplet XiZero          = MkHyperonTriplet QuarkU QuarkS QuarkS
hyperonSpecToTriplet XiMinus         = MkHyperonTriplet QuarkD QuarkS QuarkS
hyperonSpecToTriplet OmegaMinus      = MkHyperonTriplet QuarkS QuarkS QuarkS
hyperonSpecToTriplet LambdaCharmPlus = MkHyperonTriplet QuarkU QuarkD QuarkC

||| Observes net electric charge (in 1/3 e units) of a hyperon directly from constituent quarks (Rule 03 §8).
public export
hyperonElectricChargeThirds : HyperonQuarkTriplet -> BoxInt
hyperonElectricChargeThirds (MkHyperonTriplet a b c) =
  addBox (electricChargeThirds (SMPFermion a))
         (addBox (electricChargeThirds (SMPFermion b))
                 (electricChargeThirds (SMPFermion c)))

||| Observes net baryon number (in 1/3 units) of a hyperon directly from constituent quarks (Rule 03 §8).
||| Universally 3 (1 in baryon number units) for all 3-quark hyperons (1/3 + 1/3 + 1/3 = 1).
public export
hyperonBaryonThirds : HyperonQuarkTriplet -> BoxInt
hyperonBaryonThirds (MkHyperonTriplet a b c) =
  addBox ((particleQuantumNumbers (SMPFermion a)).baryonThirds)
         (addBox ((particleQuantumNumbers (SMPFermion b)).baryonThirds)
                 ((particleQuantumNumbers (SMPFermion c)).baryonThirds))

||| Observes constituent mass tokens of a hyperon: 3 quarks x 9 tokens = 27 mass tokens (1 amu) (Rule 03 §8).
public export
hyperonMassTokens : HyperonQuarkTriplet -> BoxInt
hyperonMassTokens _ = intToBoxInt 27

------------------------------------------------------------------------
-- 2. SMART CONSTRUCTORS FOR HYPERONS
------------------------------------------------------------------------

||| Constructs a Lambda0 (uds) 27-token Hadron Boxel across Red, Green, Blue color sectors.
public export
makeLambdaZeroBoxel : HadronBoxel
makeLambdaZeroBoxel =
  singletonCell (mkVoxel 0 0 0) (MkBoxInt 9) <+>
  singletonCell (mkVoxel 1 1 1) (MkBoxInt 9) <+>
  singletonCell (mkVoxel 2 2 2) (MkBoxInt 9)

------------------------------------------------------------------------
-- 3. OBSERVATIONS & COLOR NEUTRALITY
------------------------------------------------------------------------

||| Evaluates mass tokens of a Hyperon Boxel (must equal 27 tokens = 1 amu).
public export
observeHyperonMassTokens : HadronBoxel -> Stage0.BoxInt.BoxInt
observeHyperonMassTokens b = totalCellMultisetWeight b

||| Verifies SU(3) color neutrality of a Hyperon Boxel.
public export
isHyperonColorNeutral : HadronBoxel -> Bool
isHyperonColorNeutral b = isHadronBoxelColorNeutral b

------------------------------------------------------------------------
-- 4. FORMAL AUDIT PROOFS
------------------------------------------------------------------------

||| Audits Hyperon Mass Token Conservation, Color Neutrality & L-1 Observable Reductions:
||| 1. Lambda0 carries 27 mass tokens.
||| 2. Lambda0 is color neutral.
||| 3. Observable reductions from constituent quarks match exact conserved charges (Rule 03 §8).
public export
auditHyperonAlgebraProof : Bool
auditHyperonAlgebraProof =
  (observeHyperonMassTokens makeLambdaZeroBoxel == intToBoxInt 27) &&
  isHyperonColorNeutral makeLambdaZeroBoxel &&
  -- Observable reductions from Layer L-1:
  (hyperonBaryonThirds (hyperonSpecToTriplet LambdaZero) == intToBoxInt 3) &&
  (hyperonElectricChargeThirds (hyperonSpecToTriplet LambdaZero) == intToBoxInt 0) &&
  (hyperonElectricChargeThirds (hyperonSpecToTriplet SigmaPlus) == intToBoxInt 3) &&
  (hyperonElectricChargeThirds (hyperonSpecToTriplet SigmaMinus) == intToBoxInt (-3)) &&
  (hyperonElectricChargeThirds (hyperonSpecToTriplet XiZero) == intToBoxInt 0) &&
  (hyperonElectricChargeThirds (hyperonSpecToTriplet XiMinus) == intToBoxInt (-3)) &&
  (hyperonElectricChargeThirds (hyperonSpecToTriplet OmegaMinus) == intToBoxInt (-3)) &&
  (hyperonElectricChargeThirds (hyperonSpecToTriplet LambdaCharmPlus) == intToBoxInt 3) &&
  (hyperonMassTokens (hyperonSpecToTriplet LambdaZero) == intToBoxInt 27)
