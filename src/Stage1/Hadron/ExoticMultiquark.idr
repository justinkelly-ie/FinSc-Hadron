module Stage1.Hadron.ExoticMultiquark

import Stage0.BoxInt
import Stage0.Multiset
import public Stage1.Basis.Coordinate
import Stage1.UnixelFraction
import Stage1.Hadron.HadronicConfinement
import Stage1.Hadron.QuarkHadronAlgebra
import Stage1.Hadron.MesonAlgebra
import Stage1.Hadron.TypeIndexedMultiset
import Stage1.Hadron.StandardModel
import Data.List

%default total

------------------------------------------------------------------------
-- 1. EXOTIC MULTIQUARK SPECIES SPECIFICATION
------------------------------------------------------------------------

||| Exotic Multiquark State Classification.
public export
data ExoticMultiquarkSpec = TetraquarkX3872 | PentaquarkPcPlus | HDibaryon

public export
Eq ExoticMultiquarkSpec where
  TetraquarkX3872  == TetraquarkX3872  = True
  PentaquarkPcPlus == PentaquarkPcPlus = True
  HDibaryon        == HDibaryon        = True
  _                == _                = False

public export
Show ExoticMultiquarkSpec where
  show TetraquarkX3872  = "Tetraquark X(3872) (c c_bar u u_bar)"
  show PentaquarkPcPlus = "Pentaquark P_c+ (u u d c c_bar)"
  show HDibaryon        = "H-Dibaryon (u u d d s s)"

||| Ground truth constituent quark multiset representation of exotic multiquarks (Rule 03 §8).
public export
exoticConstituentQuarks : ExoticMultiquarkSpec -> Carrier SMFermion
exoticConstituentQuarks TetraquarkX3872 =
  singletonCarrier QuarkC (intToBoxInt 1)
    <+> singletonCarrier AntiQuarkC (intToBoxInt 1)
    <+> singletonCarrier QuarkU (intToBoxInt 1)
    <+> singletonCarrier AntiQuarkU (intToBoxInt 1)
exoticConstituentQuarks PentaquarkPcPlus =
  singletonCarrier QuarkU (intToBoxInt 2)
    <+> singletonCarrier QuarkD (intToBoxInt 1)
    <+> singletonCarrier QuarkC (intToBoxInt 1)
    <+> singletonCarrier AntiQuarkC (intToBoxInt 1)
exoticConstituentQuarks HDibaryon =
  singletonCarrier QuarkU (intToBoxInt 2)
    <+> singletonCarrier QuarkD (intToBoxInt 2)
    <+> singletonCarrier QuarkS (intToBoxInt 2)

||| Observes net electric charge (in 1/3 e units) of an exotic multiquark via reduction over constituent quarks (Rule 03 §8).
public export
exoticElectricChargeThirds : ExoticMultiquarkSpec -> BoxInt
exoticElectricChargeThirds spec =
  foldBoxTreeL (\acc, (q, w) => addBox (mulBox w (electricChargeThirds (SMPFermion q))) acc)
               (intToBoxInt 0)
               (exoticConstituentQuarks spec)

||| Observes net baryon number (in 1/3 units) of an exotic multiquark via reduction over constituent quarks (Rule 03 §8).
public export
exoticBaryonThirds : ExoticMultiquarkSpec -> BoxInt
exoticBaryonThirds spec =
  foldBoxTreeL (\acc, (q, w) => addBox (mulBox w ((particleQuantumNumbers (SMPFermion q)).baryonThirds)) acc)
               (intToBoxInt 0)
               (exoticConstituentQuarks spec)

||| Observes mass tokens: each constituent quark carries 9 tokens (Rule 03 §8).
public export
exoticMassTokens : ExoticMultiquarkSpec -> BoxInt
exoticMassTokens spec =
  foldBoxTreeL (\acc, (_, w) => addBox (mulBox w (intToBoxInt 9)) acc)
               (intToBoxInt 0)
               (exoticConstituentQuarks spec)

------------------------------------------------------------------------
-- 1B. CERTIFIED DEPENDENT EXOTIC MULTIQUARK CARRIER (Rule 03 §7, §8)
------------------------------------------------------------------------

||| Expected valence quark count for an exotic multiquark species:
public export
expectedExoticValence : ExoticMultiquarkSpec -> BoxInt
expectedExoticValence TetraquarkX3872  = intToBoxInt 4
expectedExoticValence PentaquarkPcPlus = intToBoxInt 5
expectedExoticValence HDibaryon        = intToBoxInt 6

||| Certified Dependent Exotic Multiquark Carrier (Rule 03 §7, §8).
||| Bundles the underlying Carrier with QTT multiplicity 0 proof that
||| total constituent quarks match exact physical valence (4 for Tetraquark, 5 for Pentaquark, 6 for Dibaryon).
public export
record CertifiedExoticMultiquark (spec : ExoticMultiquarkSpec) where
  constructor MkCertifiedExotic
  quarks            : Carrier SMFermion
  0 prfValenceMatch : totalMassBox quarks = expectedExoticValence spec

||| Canonical certified Tetraquark X(3872) state (4 quarks: c c_bar u u_bar):
public export
certifiedTetraquark : CertifiedExoticMultiquark TetraquarkX3872
certifiedTetraquark = MkCertifiedExotic (exoticConstituentQuarks TetraquarkX3872) Refl

||| Canonical certified Pentaquark P_c+ state (5 quarks: u u d c c_bar):
public export
certifiedPentaquark : CertifiedExoticMultiquark PentaquarkPcPlus
certifiedPentaquark = MkCertifiedExotic (exoticConstituentQuarks PentaquarkPcPlus) Refl

||| Canonical certified H-Dibaryon state (6 quarks: u u d d s s):
public export
certifiedHDibaryon : CertifiedExoticMultiquark HDibaryon
certifiedHDibaryon = MkCertifiedExotic (exoticConstituentQuarks HDibaryon) Refl

||| Constructively observes constituent valence directly from the certified carrier in O(1) memory:
public export
exoticValenceCount : CertifiedExoticMultiquark spec -> BoxInt
exoticValenceCount (MkCertifiedExotic q _) = totalMassBox q

------------------------------------------------------------------------
-- 2. SMART CONSTRUCTORS FOR EXOTIC MULTIQUARKS
------------------------------------------------------------------------

||| Fuses 2 Meson Vexels into a 36-token Tetraquark Vexel multiset (4 * 9 = 36).
public export
fuseTetraquark : MesonVexel -> MesonVexel -> Vexel
fuseTetraquark m1 m2 = addCellMultiset m1 m2

||| Fuses a Hadron Boxel (27) and a Meson Vexel (18) into a 45-token Pentaquark (27 + 18 = 45).
public export
fusePentaquarkTokens : HadronBoxel -> MesonVexel -> BoxInt
fusePentaquarkTokens h m = totalCellMultisetWeight h + totalCellMultisetWeight m

||| Fuses 2 Hadron Boxels (27 + 27) into a 54-token H-Dibaryon (6 * 9 = 54).
public export
fuseDibaryon : HadronBoxel -> HadronBoxel -> Boxel
fuseDibaryon h1 h2 = addCellMultiset h1 h2

||| Evaluates mass tokens of a 4-term Tetraquark Vexel.
public export
observeTetraquarkMass : Vexel -> BoxInt
observeTetraquarkMass v = totalCellMultisetWeight v

||| Evaluates mass tokens of a 6-term Dibaryon Boxel.
public export
observeDibaryonMass : Boxel -> BoxInt
observeDibaryonMass b = totalCellMultisetWeight b

------------------------------------------------------------------------
-- 3. FORMAL AUDIT PROOFS
------------------------------------------------------------------------

||| Audits Exotic Multiquark Mass Token Conservation & L-1 Observable Reductions:
||| 1. Tetraquark carries 36 mass tokens (4 * 9).
||| 2. Pentaquark carries 45 mass tokens (5 * 9).
||| 3. Dibaryon carries 54 mass tokens (6 * 9).
||| 4. Observable reductions from constituent quarks match expected quantum numbers (Rule 03 §8).
public export
auditExoticMultiquarksProof : Bool
auditExoticMultiquarksProof =
  let dummyMeson = singletonCell (mkCell1 1) (intToBoxInt 9) <+> singletonCell (mkCell1 2) (intToBoxInt 9)
      dummyHadron = singletonCell (mkVoxel 0 0 0) (intToBoxInt 9) <+>
                    singletonCell (mkVoxel 1 1 1) (intToBoxInt 9) <+>
                    singletonCell (mkVoxel 2 2 2) (intToBoxInt 9)
      tetra = fuseTetraquark dummyMeson dummyMeson
      pentaTokens = fusePentaquarkTokens dummyHadron dummyMeson
      dibaryon = fuseDibaryon dummyHadron dummyHadron
  in (observeTetraquarkMass tetra == intToBoxInt 36) &&
     (pentaTokens == intToBoxInt 45) &&
     (observeDibaryonMass dibaryon == intToBoxInt 54) &&
     -- Observable reductions from Layer L-1:
     (exoticMassTokens TetraquarkX3872 == intToBoxInt 36) &&
     (exoticBaryonThirds TetraquarkX3872 == intToBoxInt 0) &&
     (exoticElectricChargeThirds TetraquarkX3872 == intToBoxInt 0) &&
     (exoticMassTokens PentaquarkPcPlus == intToBoxInt 45) &&
     (exoticBaryonThirds PentaquarkPcPlus == intToBoxInt 3) &&
     (exoticElectricChargeThirds PentaquarkPcPlus == intToBoxInt 3) &&
     (exoticMassTokens HDibaryon == intToBoxInt 54) &&
     (exoticBaryonThirds HDibaryon == intToBoxInt 6) &&
     (exoticElectricChargeThirds HDibaryon == intToBoxInt 0) &&
     -- Certified dependent multiquark valence proofs:
     (exoticValenceCount certifiedTetraquark == intToBoxInt 4) &&
     (exoticValenceCount certifiedPentaquark == intToBoxInt 5) &&
     (exoticValenceCount certifiedHDibaryon == intToBoxInt 6)
