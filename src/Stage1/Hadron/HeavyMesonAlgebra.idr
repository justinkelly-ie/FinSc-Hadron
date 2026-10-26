module Stage1.Hadron.HeavyMesonAlgebra

import Stage0.BoxInt
import Stage0.Multiset
import public Stage1.Basis.Coordinate
import Stage1.UnixelFraction
import Stage1.ExclusionPrinciple
import Stage1.Hadron.TypeIndexedMultiset
import Stage1.Hadron.MesonAlgebra
import Data.List

%default total

------------------------------------------------------------------------
-- 1. HEAVY MESON SPECIES SPECIFICATION
------------------------------------------------------------------------

||| Heavy Meson & Quarkonium Species Specification.
public export
data HeavyMesonSpec = JPsiCharmonium | UpsilonBottomonium 
                     | DPlus | DZero | DsPlus 
                     | BPlus | BZero | BsZero

public export
Eq HeavyMesonSpec where
  JPsiCharmonium     == JPsiCharmonium     = True
  UpsilonBottomonium == UpsilonBottomonium = True
  DPlus              == DPlus              = True
  DZero              == DZero              = True
  DsPlus             == DsPlus             = True
  BPlus              == BPlus              = True
  BZero              == BZero              = True
  BsZero             == BsZero             = True
  _                  == _                  = False

public export
Show HeavyMesonSpec where
  show JPsiCharmonium     = "J/psi (c c_bar)"
  show UpsilonBottomonium = "Upsilon (b b_bar)"
  show DPlus              = "D+ (c d_bar)"
  show DZero              = "D0 (c u_bar)"
  show DsPlus             = "Ds+ (c s_bar)"
  show BPlus              = "B+ (u b_bar)"
  show BZero              = "B0 (d b_bar)"
  show BsZero             = "Bs0 (s b_bar)"

------------------------------------------------------------------------
-- 2. SMART CONSTRUCTORS FOR HEAVY MESONS
------------------------------------------------------------------------

||| Constructs a J/psi Charmonium (c c_bar) 18-token Meson Vexel.
%inline
public export
makeJPsiCharmoniumVexel : MesonVexel
makeJPsiCharmoniumVexel =
  singletonCell (mkCell1 4) (intToBoxInt 9) <+>
  singletonCell (mkCell1 4) (intToBoxInt 9)

||| Constructs a Upsilon Bottomonium (b b_bar) 18-token Meson Vexel.
%inline
public export
makeUpsilonBottomoniumVexel : MesonVexel
makeUpsilonBottomoniumVexel =
  singletonCell (mkCell1 5) (intToBoxInt 9) <+>
  singletonCell (mkCell1 5) (intToBoxInt 9)

------------------------------------------------------------------------
-- 3. OBSERVATIONS & AUDIT
------------------------------------------------------------------------

||| Evaluates mass tokens of a Heavy Meson Vexel (must equal 18 tokens).
%inline
public export
observeHeavyMesonMassTokens : MesonVexel -> Stage0.BoxInt.BoxInt
observeHeavyMesonMassTokens m = totalCellMultisetWeight m

||| Audits Heavy Meson Mass Token Conservation:
||| 1. J/psi carries 18 mass tokens.
||| 2. Upsilon carries 18 mass tokens.
public export
auditHeavyMesonAlgebraProof : Bool
auditHeavyMesonAlgebraProof =
  (observeHeavyMesonMassTokens makeJPsiCharmoniumVexel == intToBoxInt 18) &&
  (observeHeavyMesonMassTokens makeUpsilonBottomoniumVexel == intToBoxInt 18)
