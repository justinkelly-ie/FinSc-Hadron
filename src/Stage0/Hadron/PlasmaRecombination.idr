module Stage0.Hadron.PlasmaRecombination

import Stage0.BoxInt
import Stage0.Multiset
import Stage0.Token
import Stage0.Bit
import Stage0.FieldStream
import Stage0.FluctuationStream
import Stage0.StructuralFuel
import Stage1.Hadron.HadronicConfinement
import Stage0.OnSeq.FusedStream
import Data.Vect

%default total

------------------------------------------------------------------------
-- 1. PRIMORDIAL PLASMA TO NEUTRAL RECOMBINATION (EPOCHS 5 TO 10)
------------------------------------------------------------------------

||| Charge state of matter in the early cosmological plasma.
public export
data ParticleCharge = ProtonPositive | ElectronNegative | NeutralHydrogen

public export
Eq ParticleCharge where
  ProtonPositive   == ProtonPositive   = True
  ElectronNegative == ElectronNegative = True
  NeutralHydrogen  == NeutralHydrogen  = True
  _                == _                = False

public export
Show ParticleCharge where
  show ProtonPositive   = "p+"
  show ElectronNegative = "e-"
  show NeutralHydrogen  = "H0 (Neutral)"

||| Electric charge value in elementary charge units.
public export
elementaryCharge : ParticleCharge -> BoxInt
elementaryCharge ProtonPositive   = intToBoxInt 1
elementaryCharge ElectronNegative = intToBoxInt (-1)
elementaryCharge NeutralHydrogen  = intToBoxInt 0

||| An ionized Plasma State Cell with proton and electron populations.
public export
record PlasmaCell where
  constructor MkPlasmaCell
  protons   : Nat
  electrons : Nat

public export
Eq PlasmaCell where
  (MkPlasmaCell p1 e1) == (MkPlasmaCell p2 e2) =
    p1 == p2 && e1 == e2

public export
Show PlasmaCell where
  show (MkPlasmaCell p e) =
    "PlasmaCell(p=" ++ show p ++ ", e=" ++ show e ++ ")"

||| Computes net charge of a plasma cell.
public export
netPlasmaCharge : PlasmaCell -> BoxInt
netPlasmaCharge (MkPlasmaCell p e) =
  addBox (mulBox (natToBoxInt p) (intToBoxInt 1)) (mulBox (natToBoxInt e) (intToBoxInt (-1)))

------------------------------------------------------------------------
-- 2. RECOMBINATION & PHOTON DECOUPLING TRANSITION
------------------------------------------------------------------------

||| Result of cosmological recombination:
||| Produces neutral Hydrogen atoms and emitted decoupling photons.
public export
record DecoupledGas where
  constructor MkDecoupledGas
  neutralAtoms     : Nat
  decoupledPhotons : Nat
  residualProtons  : Nat
  residualElectrons: Nat

public export
Eq DecoupledGas where
  (MkDecoupledGas n1 ph1 rp1 re1) == (MkDecoupledGas n2 ph2 rp2 re2) =
    n1 == n2 && ph1 == ph2 && rp1 == rp2 && re1 == re2

public export
Show DecoupledGas where
  show (MkDecoupledGas n ph rp re) =
    "DecoupledGas(H0=" ++ show n ++ ", Photons=" ++ show ph ++ 
    ", p+=" ++ show rp ++ ", e-=" ++ show re ++ ")"

||| Executes Recombination Transition:
||| min(p, e) pairs bind into neutral H0 atoms, emitting 1 photon per binding.
public export
recombinePlasma : PlasmaCell -> DecoupledGas
recombinePlasma (MkPlasmaCell p e) =
  let bound = min p e
      remP = p `minus` bound
      remE = e `minus` bound
  in MkDecoupledGas bound bound remP remE

||| Deforested stream transducer executing plasma recombination across spatial cells in O(1) memory.
public export
streamPlasmaRecombination : FusedStream PlasmaCell -> FusedStream DecoupledGas
streamPlasmaRecombination = mapStream recombinePlasma

------------------------------------------------------------------------
-- 2b. MULTISET CHARGE OBSERVABLES & CMB PHOTON STREAMING (FINSC-ELECTROMAGNETISM)
------------------------------------------------------------------------

||| Observes net electric charge across a plasma multiset directly (Rule 03 §8):
public export
observePlasmaBagCharge : Multiset BoxInt ParticleCharge -> BoxInt
observePlasmaBagCharge ZeroM = intToBoxInt 0
observePlasmaBagCharge (AddM p w rest) =
  addBox (mulBox (elementaryCharge p) w) (observePlasmaBagCharge rest)

||| Converts a PlasmaCell into an authentic Multiset carrier (Rule 03 §8):
public export
plasmaCellToMultiset : PlasmaCell -> Multiset BoxInt ParticleCharge
plasmaCellToMultiset (MkPlasmaCell p e) =
  AddM ProtonPositive (natToBoxInt p) (AddM ElectronNegative (natToBoxInt e) ZeroM)

||| Streams emitted CMB decoupling photons directly as PhotonStateToken into FusedStream (FinSc-Electromagnetism):
public export
streamDecoupledPhotons : DecoupledGas -> FusedStream PhotonStateToken
streamDecoupledPhotons gas =
  unfoldStream (\k => if k < gas.decoupledPhotons
                        then Yield (MkPhotonToken One (intToBoxInt 1)) (S k)
                        else Done) 0

||| Evaluates total energy of CMB decoupling photon stream in O(1) registers (FinSc-Electromagnetism):
%spec fuel
public export
evaluateDecouplingPhotonEnergy : (fuel : Nat) -> DecoupledGas -> BoxInt
evaluateDecouplingPhotonEnergy fuel gas =
  fusedComputePhotonStreamEnergyDirect (limit fuel) (fusedPhotonStateStream (streamDecoupledPhotons gas))

||| Thermodynamic fluctuation step representing binding energy release and photon decoupling during recombination:
public export
recombinationThermodynamicFluctuation : DecoupledGas -> FluctuationStep
recombinationThermodynamicFluctuation gas =
  let bindWork = mulBox (natToBoxInt gas.neutralAtoms) (intToBoxInt 1)
      photHeat = mulBox (natToBoxInt gas.decoupledPhotons) (intToBoxInt 1)
  in MkFluctuation 1 bindWork photHeat

||| Streams concurrent (binding work, radiative heat) fluctuation steps from plasma recombination
||| via FinSc-Thermodynamics zipSystemBathFluctuations (Rule 03 §8):
public export
streamRecombinationFluctuations : FusedStream DecoupledGas -> FusedStream FluctuationStep
streamRecombinationFluctuations gases =
  let workStrm = mapStream (\g => mulBox (natToBoxInt g.neutralAtoms) (intToBoxInt 1)) gases
      heatStrm = mapStream (\g => mulBox (natToBoxInt g.decoupledPhotons) (intToBoxInt 1)) gases
  in zipSystemBathFluctuations workStrm heatStrm

------------------------------------------------------------------------
-- 3. CONSTRUCTIVE FORMAL AUDIT PROOFS
------------------------------------------------------------------------

||| Audits Plasma Recombination & Decoupling Invariant:
||| Proves that an equal plasma cell (100 p+, 100 e-) recombines into 100 neutral H0 atoms
||| and 100 decoupling photons with zero net charge and zero particle leakage.
public export
auditPlasmaRecombinationDecouplingProof : Bool
auditPlasmaRecombinationDecouplingProof =
  let initial = MkPlasmaCell 100 100
      initialCharge = netPlasmaCharge initial
      result = recombinePlasma initial
      strm = streamPlasmaRecombination (stream [initial])
      streamOk = case foldStreamNat 1 (\_, g => neutralAtoms g == 100) False strm of
                   True => True
                   False => False
  in initialCharge == intToBoxInt 0 &&
     neutralAtoms result == 100 &&
     decoupledPhotons result == 100 &&
     residualProtons result == 0 &&
     residualElectrons result == 0 &&
     streamOk

||| Audits that plasma recombination multiset charge neutrality fold Q = 0 matches and emitted CMB photons stream valid energy tokens:
public export
auditPlasmaMultisetDecouplingProof : Bool
auditPlasmaMultisetDecouplingProof =
  let initial = MkPlasmaCell 100 100
      bag = plasmaCellToMultiset initial
      qNet = observePlasmaBagCharge bag
      result = recombinePlasma initial
      gasEnergy = evaluateDecouplingPhotonEnergy 120 result
      recombFlucts = runFueledStreamNat 5 (streamRecombinationFluctuations (stream [result]))
  in qNet == intToBoxInt 0 && gasEnergy == intToBoxInt 200 && (length recombFlucts == 1)

