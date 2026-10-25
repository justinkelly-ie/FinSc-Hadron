module Stage1.Hadron.StellarNuclei

import Stage0.BoxInt
import Stage0.Multiset
import Stage1.Carrier.Boxel
import Stage1.UnixelFraction
import Stage1.Hadron.HadronicConfinement
import Stage1.Hadron.QuarkHadronAlgebra
import Stage0.Hadron.AlphaReplication
import Stage0.Hadron.StellarNucleosynthesis
import Data.List

%default total

------------------------------------------------------------------------
-- 1. STELLAR FUSION CHAIN HEAVY NUCLEI
------------------------------------------------------------------------

||| Heavy Stellar Nucleus Species Specification.
public export
data StellarNucleusSpec = Beryllium7 | Boron8 | Neon20 | Magnesium24 | Silicon28 | Iron56

public export
Eq StellarNucleusSpec where
  Beryllium7  == Beryllium7  = True
  Boron8      == Boron8      = True
  Neon20      == Neon20      = True
  Magnesium24 == Magnesium24 = True
  Silicon28   == Silicon28   = True
  Iron56      == Iron56      = True
  _           == _           = False

public export
Show StellarNucleusSpec where
  show Beryllium7  = "7Be (Beryllium-7)"
  show Boron8      = "8B (Boron-8)"
  show Neon20      = "20Ne (Neon-20)"
  show Magnesium24 = "24Mg (Magnesium-24)"
  show Silicon28   = "28Si (Silicon-28)"
  show Iron56      = "56Fe (Iron-56)"

||| Evaluates mass number A (nucleon count) of a stellar nucleus.
public export
stellarNucleusMassNumber : StellarNucleusSpec -> Nat
stellarNucleusMassNumber Beryllium7  = 7
stellarNucleusMassNumber Boron8      = 8
stellarNucleusMassNumber Neon20      = 20
stellarNucleusMassNumber Magnesium24 = 24
stellarNucleusMassNumber Silicon28   = 28
stellarNucleusMassNumber Iron56      = 56

||| Evaluates fundamental mass token count (A * 27) of a stellar nucleus.
public export
stellarNucleusMassTokens : StellarNucleusSpec -> Stage0.BoxInt.BoxInt
stellarNucleusMassTokens spec = Stage0.BoxInt.natToBoxInt (stellarNucleusMassNumber spec * 27)

------------------------------------------------------------------------
-- 2. SMART CONSTRUCTORS FOR STELLAR NUCLEI
------------------------------------------------------------------------

||| Fuses 5 Alpha Cores (5 * 108) into a Neon-20 nucleus (540 mass tokens).
public export
fuseNeon20 : List Boxel -> Boxel
fuseNeon20 alphaCores = foldl addBoxel neutral alphaCores

||| Fuses 56 Nucleons (56 * 27) into an Iron-56 peak binding nucleus (1512 mass tokens).
public export
fuseIron56Tokens : List HadronBoxel -> Stage0.BoxInt.BoxInt
fuseIron56Tokens nucleons = foldl (+) (Stage0.BoxInt.intToBoxInt 0) (map totalBoxelWeight nucleons)

------------------------------------------------------------------------
-- 3. FORMAL AUDIT PROOFS
------------------------------------------------------------------------

||| Audits Stellar Fusion Chain Mass Token Conservation:
||| 1. Beryllium-7 = 7 * 27 = 189 tokens.
||| 2. Boron-8 = 8 * 27 = 216 tokens.
||| 3. Neon-20 = 20 * 27 = 540 tokens.
||| 4. Magnesium-24 = 24 * 27 = 648 tokens.
||| 5. Silicon-28 = 28 * 27 = 756 tokens.
||| 6. Iron-56 = 56 * 27 = 1512 tokens.
public export
auditStellarNucleiProof : Bool
auditStellarNucleiProof =
  stellarNucleusMassTokens Beryllium7  == intToBoxInt 189 &&
  stellarNucleusMassTokens Boron8      == intToBoxInt 216 &&
  stellarNucleusMassTokens Neon20      == intToBoxInt 540 &&
  stellarNucleusMassTokens Magnesium24 == intToBoxInt 648 &&
  stellarNucleusMassTokens Silicon28   == intToBoxInt 756 &&
  stellarNucleusMassTokens Iron56      == intToBoxInt 1512
