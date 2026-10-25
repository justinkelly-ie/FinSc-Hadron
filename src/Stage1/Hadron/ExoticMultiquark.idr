module Stage1.Hadron.ExoticMultiquark

import Stage0.BoxInt
import Stage0.Multiset
import Stage1.Carrier.Vexel
import Stage1.Carrier.Boxel
import Stage1.Basis.Coordinate
import Stage1.UnixelFraction
import Stage1.Hadron.HadronicConfinement
import Stage1.Hadron.QuarkHadronAlgebra
import Stage1.Hadron.MesonAlgebra
import Stage1.Hadron.TypeIndexedMultiset
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
  TetraquarkX3872 == TetraquarkX3872 = True
  PentaquarkPcPlus == PentaquarkPcPlus = True
  HDibaryon        == HDibaryon        = True
  _                == _                = False

public export
Show ExoticMultiquarkSpec where
  show TetraquarkX3872  = "Tetraquark X(3872) (c c_bar u u_bar)"
  show PentaquarkPcPlus = "Pentaquark P_c+ (u u d c c_bar)"
  show HDibaryon        = "H-Dibaryon (u u d d s s)"

------------------------------------------------------------------------
-- 2. SMART CONSTRUCTORS FOR EXOTIC MULTIQUARKS
------------------------------------------------------------------------

||| Fuses 2 Meson Vexels into a 36-token Tetraquark Vexel multiset (4 * 9 = 36).
%inline
public export
fuseTetraquark : MesonVexel -> MesonVexel -> Vexel
fuseTetraquark m1 m2 = addVexel m1 m2

||| Fuses a Hadron Boxel (27) and a Meson Vexel (18) into a 45-token Pentaquark (27 + 18 = 45).
%inline
public export
fusePentaquarkTokens : HadronBoxel -> MesonVexel -> BoxInt
fusePentaquarkTokens h m = totalBoxelWeight h + totalVexelMass m

||| Fuses 2 Hadron Boxels (27 + 27) into a 54-token H-Dibaryon (6 * 9 = 54).
%inline
public export
fuseDibaryon : HadronBoxel -> HadronBoxel -> Boxel
fuseDibaryon (MkBoxel [(v1, MkBoxInt w1), (v2, MkBoxInt w2), (v3, MkBoxInt w3)]) (MkBoxel [(v4, MkBoxInt w4), (v5, MkBoxInt w5), (v6, MkBoxInt w6)]) =
  MkBoxel [(v1, MkBoxInt w1), (v2, MkBoxInt w2), (v3, MkBoxInt w3), (v4, MkBoxInt w4), (v5, MkBoxInt w5), (v6, MkBoxInt w6)]
fuseDibaryon h1 h2 = addBoxel h1 h2

||| Evaluates mass tokens of a 4-term Tetraquark Vexel.
%inline
public export
observeTetraquarkMass : Vexel -> BoxInt
observeTetraquarkMass v = totalVexelMass v

||| Evaluates mass tokens of a 6-term Dibaryon Boxel.
%inline
public export
observeDibaryonMass : Boxel -> BoxInt
observeDibaryonMass (MkBoxel [(v1, MkBoxInt w1), (v2, MkBoxInt w2), (v3, MkBoxInt w3), (v4, MkBoxInt w4), (v5, MkBoxInt w5), (v6, MkBoxInt w6)]) =
  MkBoxInt (w1 + w2 + w3 + w4 + w5 + w6)
observeDibaryonMass b = totalBoxelWeight b

------------------------------------------------------------------------
-- 3. FORMAL AUDIT PROOFS
------------------------------------------------------------------------

||| Audits Exotic Multiquark Mass Token Conservation:
||| 1. Tetraquark carries 36 mass tokens (4 * 9).
||| 2. Pentaquark carries 45 mass tokens (5 * 9).
||| 3. Dibaryon carries 54 mass tokens (6 * 9).
%inline
public export
auditExoticMultiquarksProof : Bool
auditExoticMultiquarksProof =
  let dummyMeson = MkVexel [(MkUnixel 1, MkBoxInt 9), (MkUnixel 2, MkBoxInt 9)]
      dummyHadron = MkBoxel [(MkVoxel 0 0 0, MkBoxInt 9), (MkVoxel 1 1 1, MkBoxInt 9), (MkVoxel 2 2 2, MkBoxInt 9)]
      tetra = fuseTetraquark dummyMeson dummyMeson
      pentaTokens = fusePentaquarkTokens dummyHadron dummyMeson
      dibaryon = fuseDibaryon dummyHadron dummyHadron
  in (observeTetraquarkMass tetra == intToBoxInt 36) &&
     (pentaTokens == intToBoxInt 45) &&
     (observeDibaryonMass dibaryon == intToBoxInt 54)
