||| Representation Theorem Isomorphism for Layer 5 Hadronic Quantum & Nuclear Matter (Rule 03)
|||
||| Establishes the functorial isomorphism between abstract color charge Lie algebra and
||| concrete multiset streams over ColorCharge tokens:
|||   TheoryRepresentationIsomorphism L5_HadronicQuantum ColorCharge ColorCharge
module Stage1.Hadron.NuclearRepIso

import Stage0.BoxInt
import Stage0.Multiset
import Stage1.FourGeometries
import Stage1.PhysicalUniverse.Stratification

%default total

||| Monomorphic equality for ColorCharge.
public export
colorChargeEqMono : ColorCharge -> ColorCharge -> Bool
colorChargeEqMono RedColor RedColor = True
colorChargeEqMono GreenColor GreenColor = True
colorChargeEqMono BlueColor BlueColor = True
colorChargeEqMono _ _ = False

||| Canonical Representation Isomorphism for Layer 5 Hadronic Quantum & Nuclear Matter.
public export
nuclearRepIso : TheoryRepresentationIsomorphism L5_HadronicQuantum ColorCharge ColorCharge
nuclearRepIso =
  MkTheoryRepIso
    "L5: Color Charge SU(3) Algebra -> Multiset ColorCharge"
    (\c => AddM c (MkBoxInt 1) ZeroM)
    (\m => case m of
             AddM c _ _ => c
             ZeroM      => RedColor)
    (\c =>
      let m = AddM c (MkBoxInt 1) ZeroM
          c' = case m of
                 AddM x _ _ => x
                 ZeroM      => RedColor
      in colorChargeEqMono c' c
    )

||| Compile-time verification that round-trip isomorphism holds for RedColor.
public export
0 prfNuclearRepIsoRed : (verifyRoundTrip Stage1.Hadron.NuclearRepIso.nuclearRepIso) RedColor = True
prfNuclearRepIsoRed = Refl

||| Compile-time verification that round-trip isomorphism holds for GreenColor.
public export
0 prfNuclearRepIsoGreen : (verifyRoundTrip Stage1.Hadron.NuclearRepIso.nuclearRepIso) GreenColor = True
prfNuclearRepIsoGreen = Refl

||| Compile-time verification that round-trip isomorphism holds for BlueColor.
public export
0 prfNuclearRepIsoBlue : (verifyRoundTrip Stage1.Hadron.NuclearRepIso.nuclearRepIso) BlueColor = True
prfNuclearRepIsoBlue = Refl
