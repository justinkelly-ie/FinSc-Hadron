module Stage1.Hadron.HadronicConfinement

import Language.Reflection
import Stage0.UniverseState
import Stage1.MaxelTransform
import Stage1.LinAlgebra.TernaryClassifier
import Stage0.LatticeTopology
import Stage1.FourGeometries
import Data.Vect
import Data.Fin
import Stage1.Carrier.Boxel
import Stage1.Carrier.BalanceArray

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

||| Deforested direct vector slice sum of 9 cells from an offset.
private
sum9From : Nat -> Vect 27 Stage0.BoxInt.BoxInt -> Stage0.BoxInt.BoxInt
sum9From offset grid = go 9 offset (Stage0.BoxInt.intToBoxInt 0)
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
sectorColorSum RedColor (MkHadronState grid)   = sum9From 0 grid
sectorColorSum GreenColor (MkHadronState grid) = sum9From 9 grid
sectorColorSum BlueColor (MkHadronState grid)  = sum9From 18 grid

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
      wRed   = totalMaxelWeight redSlice
      wGreen = totalMaxelWeight greenSlice
      wBlue  = totalMaxelWeight blueSlice
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

||| Hadronic Confinement Transform Multiset (G ⊗ Z ⊗ J):
||| G: EllipticSector (Bound State Confinement)
||| Z: 1 / [27] (Exact 27-cell normalization)
||| J: ColorCharge -> BaryonSinglet (Pushforward Contraction Map)
quarkToBaryonTransform : MaxelTransform ColorCharge HadronSector
quarkToBaryonTransform = mkTransformBox EllipticSector (mkUnixelFraction (Stage0.BoxInt.intToBoxInt 1) 27)
  [ ((RedColor, BaryonSinglet), Stage0.BoxInt.intToBoxInt 1)
  , ((GreenColor, BaryonSinglet), Stage0.BoxInt.intToBoxInt 1)
  , ((BlueColor, BaryonSinglet), Stage0.BoxInt.intToBoxInt 1)
  ]

||| QTT 0 Erased Proof: Quark To Baryon 3-to-1 Color Contraction Transform.
public export
0 prfQuarkToBaryonTransform : List.length [RedColor, GreenColor, BlueColor] = the Nat 3
prfQuarkToBaryonTransform = Refl
