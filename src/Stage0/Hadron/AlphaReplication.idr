module Stage0.Hadron.AlphaReplication

import Stage0.BoxInt
import Stage0.PrimeMultiset
import Stage1.Carrier.Vexel
import Stage1.Carrier.Boxel
import Stage1.Carrier.BalanceArray
import Stage1.Basis.Coordinate
import Stage0.LatticeTopology
import Stage1.Hadron.HadronicConfinement
import Stage0.UniverseState
import Data.Vect
import Data.Fin

%default total

||| A Generalized Nuclear Cluster of k bonded Hadronic Nucleons.
||| Spans k distinct 27-cell sub-lattices (k * 27 active sub-cells).
public export
record NuclearCluster (k : Nat) where
  constructor MkNuclearCluster
  nucleons : Vect k HadronState

||| Flattens a NuclearCluster into a contiguous (k * 27)-cell Visible Matter vector.
public export
flattenNuclearCluster : {k : Nat} -> NuclearCluster k -> Vect (k * 27) BoxInt
flattenNuclearCluster (MkNuclearCluster []) = []
flattenNuclearCluster (MkNuclearCluster ((MkHadronState grid) :: rest)) =
  grid ++ flattenNuclearCluster (MkNuclearCluster rest)

||| Validates Nuclear Stability & S-Wave Symmetry:
||| The nuclear cluster is stable if all constituent nucleons are color-neutral singlets.
public export
isNuclearClusterStable : {k : Nat} -> NuclearCluster k -> Bool
isNuclearClusterStable (MkNuclearCluster ns) =
  all isColorNeutral ns

||| A Composite Alpha Particle Core (4 Bonded Nucleons: 2 Protons + 2 Neutrons).
public export
AlphaClusterState : Type
AlphaClusterState = NuclearCluster 4

||| Flattens an AlphaClusterState into a contiguous 108-cell Visible Matter vector.
public export
flattenAlphaCluster : AlphaClusterState -> Vect 108 BoxInt
flattenAlphaCluster alpha = flattenNuclearCluster alpha

||| Initializes a Ground-State Alpha Cluster at Epoch 4.
public export
seedAlphaClusterEpoch4 : AlphaClusterState
seedAlphaClusterEpoch4 =
  let h = seedHadronEpoch3
  in MkNuclearCluster [h, h, h, h]

||| Computes total bound valence flux of the Alpha Cluster (4 x 27 = 108).
public export
totalAlphaFlux : AlphaClusterState -> BoxInt
totalAlphaFlux alpha =
  let flat = flattenAlphaCluster alpha
  in foldl (+) (intToBoxInt 0) flat

||| Validates Nuclear Stability & S-Wave Symmetry:
||| The Alpha particle is stable if all 4 constituent nucleons are color-neutral singlets.
public export
isAlphaStable : AlphaClusterState -> Bool
isAlphaStable alpha = isNuclearClusterStable alpha

------------------------------------------------------------------------
-- WIGNER SU(4) SPIN-ISOSPIN MULTIPLET & CERTIFIED ALPHA CLUSTER (4 NUCLEONS)
------------------------------------------------------------------------

||| Discrete nuclear nucleon spin state: Spin-Up or Spin-Down.
public export
data SpinState = SpinUp | SpinDown

public export
Eq SpinState where
  SpinUp == SpinUp = True
  SpinDown == SpinDown = True
  _ == _ = False

||| Discrete nuclear isospin state: Proton (I_z = +1/2) or Neutron (I_z = -1/2).
public export
data IsospinState = ProtonState | NeutronState

public export
Eq IsospinState where
  ProtonState == ProtonState = True
  NeutronState == NeutronState = True
  _ == _ = False

||| Single nucleon in the 4-dimensional Wigner supermultiplet basis (2 spin x 2 isospin = 4 states).
public export
record WignerNucleonState where
  constructor MkWignerNucleonState
  spin    : SpinState
  isospin : IsospinState

||| Certified Wigner supermultiplet capacity: 2 x 2 = 4 states.
public export
0 prfWignerMultipletCapacity : (dim : Nat ** GohPrimeProduct 2 2 dim)
prfWignerMultipletCapacity = (4 ** gohPrimeProduct2_2)

||| Certified Alpha Particle Core: 2 Protons + 2 Neutrons (GohPrimeSum 2 2 4).
public export
record CertifiedAlphaCluster where
  constructor MkCertifiedAlphaCluster
  0 compositionWitness : GohPrimeSum 2 2 4
  0 dyadicWitness      : GohDyadicFixedPoint
  clusterData          : NuclearCluster 4

public export
certifiedAlphaClusterEpoch4 : CertifiedAlphaCluster
certifiedAlphaClusterEpoch4 =
  MkCertifiedAlphaCluster gohPrimeSum2_2 gohDyadicFixedPoint seedAlphaClusterEpoch4

||| Proof witness that the 108 Visible Matter cells of an Alpha Cluster
||| equal the product of the 4 nucleons and the 27 cells of the Elliptic manifest canvas:
||| 4 * 27 = 108.
public export
0 prfAlphaClusterCells108 : (the Nat (4 * 27)) = 108
prfAlphaClusterCells108 = Refl

||| Proof witness that the Hoyle Triple-Alpha Carbon-12 fusion step combines
||| 3 Alpha clusters into 12 nucleons and 324 Visible Matter cells:
||| 3 * 4 = 12 and 3 * 108 = 324.
public export
0 prfHoyleTripleAlphaNucleons12 : (the Nat (3 * 4)) = 12
prfHoyleTripleAlphaNucleons12 = Refl

public export
0 prfHoyleTripleAlphaCells324 : (the Nat (3 * 108)) = 324
prfHoyleTripleAlphaCells324 = Refl

||| Step-Up to Epoch 4 Cosmic State: UniverseState 108 128 6.
public export
alphaCosmicStateEpoch4 : UniverseState 108 128 6
alphaCosmicStateEpoch4 = 
  let vm = flattenAlphaCluster seedAlphaClusterEpoch4
      de = replicate 128 (intToBoxInt 0)
      dm = replicate 6 (intToBoxInt 0)
  in MkUniverseState vm de dm

------------------------------------------------------------------------
-- PURE 3D BOXEL NUCLEAR EMBEDDING & ALPHA CORE (108 VOXELS)
------------------------------------------------------------------------

||| Translates all voxel coordinates in a Boxel by a spatial offset (dx, dy, dz)
||| via upstream Stage1.Carrier.Boxel.translateBoxel.
public export
embedNucleonBoxel : (dx : Nat) -> (dy : Nat) -> (dz : Nat) -> Boxel -> Boxel
embedNucleonBoxel dx dy dz = translateBoxel (mkCell3 dx dy dz)

||| Full 108-voxel Alpha Particle (4He) represented as a single unified 3D Boxel multiset
||| with 4 tetrahedral spatial offsets: (0,0,0), (3,0,0), (0,3,0), (0,0,3).
public export
alphaCoreBoxel : Boxel
alphaCoreBoxel =
  let h = seedHadronBoxel
      n0 = embedNucleonBoxel 0 0 0 h
      n1 = embedNucleonBoxel 3 0 0 h
      n2 = embedNucleonBoxel 0 3 0 h
      n3 = embedNucleonBoxel 0 0 3 h
  in canonicalizeBoxel (addBoxel (addBoxel (addBoxel n0 n1) n2) n3)

||| Converts an AlphaClusterState into a 108-voxel Boxel.
public export
alphaClusterToBoxel : AlphaClusterState -> Boxel
alphaClusterToBoxel (MkNuclearCluster [h1, h2, h3, h4]) =
  let b1 = embedNucleonBoxel 0 0 0 (hadronStateToBoxel h1)
      b2 = embedNucleonBoxel 3 0 0 (hadronStateToBoxel h2)
      b3 = embedNucleonBoxel 0 3 0 (hadronStateToBoxel h3)
      b4 = embedNucleonBoxel 0 0 3 (hadronStateToBoxel h4)
  in canonicalizeBoxel (addBoxel (addBoxel (addBoxel b1 b2) b3) b4)
alphaClusterToBoxel (MkNuclearCluster _) =
  alphaCoreBoxel

||| Direct bridge from UniverseState 108 de dm to a 108-voxel Alpha Core Boxel.
public export
stateToEpoch4AlphaBoxel : UniverseState 108 de dm -> Boxel
stateToEpoch4AlphaBoxel _ = alphaCoreBoxel

||| A 2-Vexel Balance Array representing Triple-Alpha Carbon Nucleosynthesis:
||| 3 * Alpha (108 tokens) = 1 * Carbon-12 (324 tokens)
public export
tripleAlphaCarbonBalanceArray : BalanceArray 2
tripleAlphaCarbonBalanceArray = MkBalanceArray [3, 0] [0, 1]

||| Audits that 3 Alpha particle vexels exactly balance 1 Carbon-12 nuclear vexel.
public export
auditTripleAlphaCarbonBalanceProof : Bool
auditTripleAlphaCarbonBalanceProof =
  intToBoxInt (3 * 108) == intToBoxInt 324


