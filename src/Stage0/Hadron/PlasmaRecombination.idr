module Stage0.Hadron.PlasmaRecombination

import Stage0.BoxInt
import Stage1.Hadron.HadronicConfinement
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
  (natToBoxInt p * intToBoxInt 1) + (natToBoxInt e * intToBoxInt (-1))

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
  in initialCharge == intToBoxInt 0 &&
     neutralAtoms result == 100 &&
     decoupledPhotons result == 100 &&
     residualProtons result == 0 &&
     residualElectrons result == 0

