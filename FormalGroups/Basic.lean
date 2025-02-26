/-
Copyright (c) 2025 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Basic

/-!

## One Dimensional Formal Group
This file defines one dimensional formal group law over a ring `A`, homomorphism and isomorphism between two formal group.

## Adivisor : María Inés de Frutos-Fernández

## Reference:
· Silverman, The Arithmetic of Elliptic Curves (2nd edition) - Chapter 4.
· Lubin--Tate, Formal Complex Multiplication in Local Fields.
· Hazewinkel, Formal Groups and Applications. Start with Chapters 1 and 2. Later you can look at some parts of Chapters 4 and 6.

-/

open Classical MvPowerSeries PowerSeries

-- Definition of Formal Group

-- Assume the coeffiecient ring `R` to be commutative ring.
variable {R : Type*} [CommRing R] {σ : Type*} {G : MvPowerSeries (Fin 2) R} {x y : R}

#check Fin 2
#check (1 : Fin 2)
#check MvPowerSeries (Fin 2) R




def PowerSeries2 (R : Type*) [CommRing R] := PowerSeries (PowerSeries R)

noncomputable def X : MvPowerSeries (Fin 2) R := MvPowerSeries.X (0 : Fin 2)

noncomputable def Y : MvPowerSeries (Fin 2) R := MvPowerSeries.X (1: Fin 2)



-- A structure for a 1-dimensional formal group law over `R`
structure FormalGroup (R : Type*) [CommRing R] where
  F : MvPowerSeries (Fin 2) R  -- A formal power series in two variables
  assoc : sorry

namespace FormalGroup

end FormalGroup
