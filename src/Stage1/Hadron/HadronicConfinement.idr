module Stage1.Hadron.HadronicConfinement

import Language.Reflection
import Stage0.UniverseState
import Stage1.MaxelTransform
import Stage1.LinAlgebra.TernaryClassifier
import Stage0.LatticeTopology
import Stage1.FourGeometries
import Data.Vect
import Data.Fin
import public Stage1.Basis.Coordinate
import Stage1.Carrier.BalanceArray
import Stage1.Hadron.StandardModel

%default total



||| Tabulator for 27-element vectors.
public export
tabulate27 : (Fin 27 -> a) -> Vect 27 a
tabulate27 = tabulate

||| A Hadronic Nucleon State (Proton / Neutron) spanning the 27-cell lattice.
||| Tracks color flux across the Red, Green, and Blue sectors.
public export
record HadronState where
  constructor MkHadronState
  latticeGrid : Vect 27 Stage0.BoxInt.BoxInt

||| Creates a balanced Hadronic Ground State at Epoch 3.
||| Injects 1 unit of Quark flux into each cell (9 Red + 9 Green + 9 Blue = 27 total flux).
public export
seedHadronEpoch3 : HadronState
seedHadronEpoch3 =
  let grid = tabulate27 (\idx => 
        case cellColorSector idx of
          RedColor   => Stage0.BoxInt.intToBoxInt 1
          GreenColor => Stage0.BoxInt.intToBoxInt 1
          BlueColor  => Stage0.BoxInt.intToBoxInt 1)
  in MkHadronState grid

||| Deforested direct vector slice sum of cells spanning one color plane (sliceColorCapacity = 9 cells).
private
sumColorSlice : Nat -> Vect 27 Stage0.BoxInt.BoxInt -> Stage0.BoxInt.BoxInt
sumColorSlice offset grid = go sliceColorCapacity offset (Stage0.BoxInt.intToBoxInt 0)
  where
    go : Nat -> Nat -> Stage0.BoxInt.BoxInt -> Stage0.BoxInt.BoxInt
    go Z _ acc = acc
    go (S k) idx acc =
      case natToFin idx 27 of
        Just finIdx => go k (S idx) (Stage0.BoxInt.addBox acc (index finIdx grid))
        Nothing     => acc

||| Computes the net color charge sum of a sector via deforested direct vector slices.
public export
sectorColorSum : ColorCharge -> HadronState -> Stage0.BoxInt.BoxInt
sectorColorSum RedColor (MkHadronState grid)   = sumColorSlice 0 grid
sectorColorSum GreenColor (MkHadronState grid) = sumColorSlice sliceColorCapacity grid
sectorColorSum BlueColor (MkHadronState grid)  = sumColorSlice (2 * sliceColorCapacity) grid

||| Color Neutrality (White / Singlet State) Predicate:
||| A hadron is confined and color-neutral if and only if Red Sum == Green Sum == Blue Sum.
public export
isColorNeutral : HadronState -> Bool
isColorNeutral hadron =
  let r = sectorColorSum RedColor hadron
      g = sectorColorSum GreenColor hadron
      b = sectorColorSum BlueColor hadron
  in r == g && g == b

||| Total Hadronic Valence Flux: Sum of all 27 cells.
public export
totalHadronFlux : HadronState -> Stage0.BoxInt.BoxInt
totalHadronFlux (MkHadronState grid) = sumField27 grid

||| Step-Up to Epoch 3 Cosmic State: UniverseState 27 128 3.
public export
hadronCosmicStateEpoch3 : UniverseState 27 128 3
hadronCosmicStateEpoch3 = seedCosmicVacuum 27 128 3

------------------------------------------------------------------------
-- 4. PURE BOXEL MULTISET QCD NUCLEONS & Z-SLICE CONFINEMENT
------------------------------------------------------------------------

||| Converts a HadronState into a 3D Boxel multiset.
public export
hadronStateToBoxel : HadronState -> Boxel
hadronStateToBoxel (MkHadronState grid) = field27ToBoxel grid

||| Converts a 3D Boxel multiset into a HadronState.
public export
boxelToHadronState : Boxel -> HadronState
boxelToHadronState b = MkHadronState (boxelToField27 b)

||| Ground-state Hadron Nucleon represented as a canonical 3D Boxel multiset.
public export
seedHadronBoxel : Boxel
seedHadronBoxel = hadronStateToBoxel seedHadronEpoch3

||| Validates QCD Color Neutrality directly on a 3D Boxel multiset:
||| Evaluates that the 3 Z-slice Maxel planes (z=0 Red, z=1 Green, z=2 Blue)
||| carry identically balanced color flux.
public export
isHadronBoxelColorNeutral : Boxel -> Bool
isHadronBoxelColorNeutral b =
  let redSlice   = sliceBoxelZ 0 b
      greenSlice = sliceBoxelZ 1 b
      blueSlice  = sliceBoxelZ 2 b
      wRed   = totalCellMultisetWeight redSlice
      wGreen = totalCellMultisetWeight greenSlice
      wBlue  = totalCellMultisetWeight blueSlice
  in wRed == wGreen && wGreen == wBlue

||| Direct bridge from UniverseState 27 de dm to a 3D Boxel multiset.
public export
stateToEpoch3Boxel : UniverseState 27 de dm -> Boxel
stateToEpoch3Boxel (MkUniverseState vm _ _) = field27ToBoxel vm

||| A 4-Vexel Balance Array representing Hadronic Color Singlet Confinement:
||| q_R + q_G + q_B = B_singlet
public export
hadronSingletBalanceArray : BalanceArray 4
hadronSingletBalanceArray = MkBalanceArray [1, 1, 1, 0] [0, 0, 0, 1]

||| QTT 0 Erased Proof: Hadron Singlet Balance (3 color components sum to 3).
public export
0 prfHadronSingletBalance : addBox (intToBoxInt 1) (addBox (intToBoxInt 1) (intToBoxInt 1)) = intToBoxInt 3
prfHadronSingletBalance = Refl

------------------------------------------------------------------------
-- 5. UNIVERSAL TRANSFORM MULTISET HADRONIC CONFINEMENT INSTANCE
------------------------------------------------------------------------

||| A Baryon Singlet Target Sector for Hadronic Confinement.
public export
data HadronSector = BaryonSinglet

public export
Eq HadronSector where
  BaryonSinglet == BaryonSinglet = True

public export
Ord HadronSector where
  compare BaryonSinglet BaryonSinglet = EQ

||| Hadronic Confinement Transform Multiset (G ⊗ Z ⊗ J):
||| G: EllipticSector (Bound State Confinement)
||| Z: 1 / [ellipticLatticeCapacity] (Exact 27-cell normalization)
||| J: ColorCharge -> BaryonSinglet (Pushforward Contraction Map)
quarkToBaryonTransform : MaxelTransform ColorCharge HadronSector
quarkToBaryonTransform = mkTransformBox EllipticSector (mkUnixelFraction (Stage0.BoxInt.intToBoxInt 1) (cast ellipticLatticeCapacity))
  [ ((RedColor, BaryonSinglet), Stage0.BoxInt.intToBoxInt 1)
  , ((GreenColor, BaryonSinglet), Stage0.BoxInt.intToBoxInt 1)
  , ((BlueColor, BaryonSinglet), Stage0.BoxInt.intToBoxInt 1)
  ]

||| QTT 0 Erased Proof: Quark To Baryon 3-to-1 Color Contraction Transform.
public export
0 prfQuarkToBaryonTransform : List.length [RedColor, GreenColor, BlueColor] = the Nat 3
prfQuarkToBaryonTransform = Refl

------------------------------------------------------------------------
-- 6. CONSTRUCTIVE NUCLEON SPECIES & VALENCE QUARK DECOMPOSITION
------------------------------------------------------------------------

||| Nucleon species: Proton or Neutron.
public export
data NucleonSpecies = ProtonSpecies | NeutronSpecies

public export
Eq NucleonSpecies where
  ProtonSpecies  == ProtonSpecies  = True
  NeutronSpecies == NeutronSpecies = True
  _              == _              = False

public export
Show NucleonSpecies where
  show ProtonSpecies  = "Proton (uud)"
  show NeutronSpecies = "Neutron (udd)"

||| Constituent valence quarks for a Nucleon:
||| Proton = (u, u, d)
||| Neutron = (u, d, d)
public export
nucleonValenceQuarks : NucleonSpecies -> Vect 3 SMFermion
nucleonValenceQuarks ProtonSpecies  = [QuarkU, QuarkU, QuarkD]
nucleonValenceQuarks NeutronSpecies = [QuarkU, QuarkD, QuarkD]

||| Net electric charge of a nucleon in fundamental units e (using exact integer thirds):
||| Proton:  (+2/3) + (+2/3) + (-1/3) = +3/3 = +1 e
||| Neutron: (+2/3) + (-1/3) + (-1/3) = 0/3  = 0 e
public export
nucleonElectricChargeThirds : NucleonSpecies -> Stage0.BoxInt.BoxInt
nucleonElectricChargeThirds n =
  foldl Stage0.BoxInt.addBox (Stage0.BoxInt.intToBoxInt 0)
    (map (\q => electricChargeThirds (SMPFermion q)) (nucleonValenceQuarks n))

||| Compile-time proof witness: Proton net electric charge is identically +1 e (+3 thirds).
public export
0 prfProtonElectricChargeThirds : Stage1.Hadron.HadronicConfinement.nucleonElectricChargeThirds ProtonSpecies = Stage0.BoxInt.intToBoxInt 3
prfProtonElectricChargeThirds = Refl

||| Compile-time proof witness: Neutron net electric charge is identically 0 e (0 thirds).
public export
0 prfNeutronElectricChargeThirds : Stage1.Hadron.HadronicConfinement.nucleonElectricChargeThirds NeutronSpecies = Stage0.BoxInt.intToBoxInt 0
prfNeutronElectricChargeThirds = Refl

||| Evaluates constituent Up-quark and Down-quark counts for any population of P protons and N neutrons:
||| u = 2P + N
||| d = P + 2N
||| Total valence quarks = u + d = 3(P + N) = 3A.
public export
nucleonsToQuarks : (protons : Nat) -> (neutrons : Nat) -> (Nat, Nat, Nat)
nucleonsToQuarks p n =
  let u = (2 * p) + n
      d = p + (2 * n)
  in (u, d, u + d)

||| Compile-time proof witness: Canonical Cosmic Baryon budget (P=125, N=50) yields exactly u=300, d=225, u+d=525.
public export
0 prfCanonicalQuarkBaryonCounts : Stage1.Hadron.HadronicConfinement.nucleonsToQuarks 125 50 = (300, 225, 525)
prfCanonicalQuarkBaryonCounts = Refl

------------------------------------------------------------------------
-- 7. CONSTITUENT QUARK MULTISETS & STREAMING NUCLEONS (Rule 03 §7 & Rule 04 §8)
------------------------------------------------------------------------

||| A Nucleon represented as a pure multiset of constituent quarks.
public export
nucleonQuarkMultiset : NucleonSpecies -> Multiset BoxInt SMFermion
nucleonQuarkMultiset ProtonSpecies  = AddM QuarkU (intToBoxInt 2) (AddM QuarkD (intToBoxInt 1) ZeroM)
nucleonQuarkMultiset NeutronSpecies = AddM QuarkU (intToBoxInt 1) (AddM QuarkD (intToBoxInt 2) ZeroM)

||| A Nuclide (Z protons, N neutrons) represented directly as a multiset of constituent valence quarks:
||| u = 2Z + N
||| d = Z + 2N
public export
nuclideQuarkMultiset : (protons : Nat) -> (neutrons : Nat) -> Multiset BoxInt SMFermion
nuclideQuarkMultiset p n =
  let u = (2 * p) + n
      d = p + (2 * n)
  in AddM QuarkU (natToBoxInt u) (AddM QuarkD (natToBoxInt d) ZeroM)

||| Total electric charge (in 1/3 e units) computed directly over a multiset of quarks:
public export
quarkMultisetElectricChargeThirds : Multiset BoxInt SMFermion -> BoxInt
quarkMultisetElectricChargeThirds ZeroM = intToBoxInt 0
quarkMultisetElectricChargeThirds (AddM q count rest) =
  addBox (mulBox (electricChargeThirds (SMPFermion q)) count) (quarkMultisetElectricChargeThirds rest)

||| Definitional proof that the Proton quark multiset carries net charge +1 e (+3 thirds).
public export
0 prfProtonMultisetCharge : Stage1.Hadron.HadronicConfinement.quarkMultisetElectricChargeThirds (Stage1.Hadron.HadronicConfinement.nucleonQuarkMultiset ProtonSpecies) = intToBoxInt 3
prfProtonMultisetCharge = Refl

||| Definitional proof that the Neutron quark multiset carries net charge 0 e (0 thirds).
public export
0 prfNeutronMultisetCharge : Stage1.Hadron.HadronicConfinement.quarkMultisetElectricChargeThirds (Stage1.Hadron.HadronicConfinement.nucleonQuarkMultiset NeutronSpecies) = intToBoxInt 0
prfNeutronMultisetCharge = Refl


