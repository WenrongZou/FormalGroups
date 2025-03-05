/-
Copyright (c) 2025 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/


import FormalGroups.MvPowerSeries.Substitution

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

def coeff_X : Fin 2 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 0

def coeff_Y : Fin 2 → ℕ
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1

#check Finsupp.equivFunOnFinite.invFun coeff_X
#check subst

-- noncomputable def X : MvPowerSeries (Fin 2) R := MvPowerSeries.X (0 : Fin 2)

-- noncomputable def Y : MvPowerSeries (Fin 2) R := MvPowerSeries.X (1 : Fin 2)


noncomputable def sub_fir_aux {A : Type*} [CommRing A]: Fin 2 → MvPowerSeries (Fin 3) A
  | ⟨0, _⟩ => MvPowerSeries.X (0 : Fin 3)
  | ⟨1, _⟩ => MvPowerSeries.X (1 : Fin 3)

noncomputable def sub_sec_aux {A : Type*} [CommRing A]: Fin 2 → MvPowerSeries (Fin 3) A
  | ⟨0, _⟩ => MvPowerSeries.X (0 : Fin 3)
  | ⟨1, _⟩ => MvPowerSeries.X (1 : Fin 3)


-- (0 : Fin 2) ↦ F(X, Y), (1 : Fin 2) ↦ Z
noncomputable def sub_fir {A : Type*} [CommRing A] (F : MvPowerSeries (Fin 2) A): Fin 2 → MvPowerSeries (Fin 3) A
  | ⟨0, _⟩ => @MvPowerSeries.subst _ A _ _ A _  _ (sub_fir_aux) F
  | ⟨1, _⟩ => MvPowerSeries.X (2 : Fin 3)

-- (0 : Fin 2) ↦ X, (1 : Fin 2) ↦ F (Y, Z)
noncomputable def sub_sec {A : Type*} [CommRing A] (F : MvPowerSeries (Fin 2) A): Fin 2 → MvPowerSeries (Fin 3) A
  | ⟨0, _⟩ => MvPowerSeries.X (0 : Fin 3)
  | ⟨1, _⟩ => @MvPowerSeries.subst _ A _ _ A _  _ (sub_sec_aux) F

-- (0 : Fin 2) ↦ Y, (1 : Fin 2) ↦ X
noncomputable def sub_symm {A : Type*} [CommRing A] : Fin 2 → MvPowerSeries (Fin 2) A
  | ⟨0, _⟩ => MvPowerSeries.X (1 : Fin 2)
  | ⟨1, _⟩ => MvPowerSeries.X (0 : Fin 2)



#check subst (sub_fir G) G
#check subst (sub_sec G) G


structure MvPowerSeries_coeff (A : Type*) [CommRing A] where
  F : MvPowerSeries (Fin 2) A
  zero_coeff : MvPowerSeries.coeff A 0 F = 0
  lin_coeff_X : MvPowerSeries.coeff A (Finsupp.equivFunOnFinite.invFun coeff_X) F = 1
  lin_coeff_Y : MvPowerSeries.coeff A (Finsupp.equivFunOnFinite.invFun coeff_Y) F = 1


-- A structure for a 1-dimensional formal group law over `R`
structure FormalGroup (A : Type*) [CommRing A] extends MvPowerSeries_coeff A where
  assoc : @MvPowerSeries.subst _ A _ _ A _  _ (sub_fir F) F = @MvPowerSeries.subst _ A _ _ A _  _ (sub_sec F) F
  --  Associativity of the Formal Group : `F (F (X, Y), Z) = F (X, F (Y, Z))`.

structure CommFormalGroup (A : Type*) [CommRing A] extends FormalGroup A where
  comm : F = @MvPowerSeries.subst _ A _ _ A _  _ (sub_symm) F
-- Commutativity F (X, Y) = F (Y, X)


-- Definition of homomorphism between Formal Group Law
structure PowerSeries_coeff (A : Type*) [CommRing A] where
  F : MvPowerSeries (Fin 1) A
  zero_coeff : MvPowerSeries.coeff A 0 F = 0

-- a (F (X, Y))
noncomputable def sub_hom₁ {A : Type*} [CommRing A]  (F : MvPowerSeries (Fin 2) A): Fin 1 → MvPowerSeries (Fin 2) A
  | ⟨0, _⟩ => F

-- G (a (X), a (Y))
noncomputable def sub_hom₂ {A : Type*} [CommRing A] (a : PowerSeries_coeff A): Fin 2 → MvPowerSeries (Fin 2) A
  | ⟨0, _⟩ => @MvPowerSeries.subst _ A _ _ A _  _ (sub_hom₁ (MvPowerSeries.X (0 : Fin 2))) a.F
  | ⟨1, _⟩ => @MvPowerSeries.subst _ A _ _ A _  _ (sub_hom₁ (MvPowerSeries.X (1 : Fin 2))) a.F

structure FormalGroupHom {A : Type*} [CommRing A] {G₁ G₂ : FormalGroup A} (a : PowerSeries_coeff A) where
  hom : MvPowerSeries.subst (sub_hom₁ G₁.F) a.F = @MvPowerSeries.subst _ A _ _ A _  _ (sub_hom₂ a) G₂.F
  --         a (F (X, Y))                    =          G (a (X), a (Y))


#check MvPowerSeries_coeff.F
#check FormalGroup

#check FormalGroup R


namespace FormalGroup

-- def AddFormaGroup {A : Type*} [CommRing A] : FormalGroup A where
--   F := MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2)
--   zero_coeff := by simp
--   lin_coeff_X := by sorry
--   lin_coeff_Y := by sorry
--   assoc := by
--     classical
--     simp
--     unfold MvPowerSeries.subst
--     simp [MvPowerSeries.eval₂]
--     unfold sub_fir sub_sec
--     sorry

-- def MulFormalGroup {A : Type*} [CommRing A] : FormalGroup A where
--   F := MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2) + MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2)
--   zero_coeff := by simp
--   lin_coeff_X := by sorry
--   lin_coeff_Y := by sorry
--   assoc := by sorry


-- X ↦ X, Y ↦ ι (X)
noncomputable def sub_sec' {A : Type*} [CommRing A] (a : PowerSeries_coeff A) : Fin 2 → MvPowerSeries (Fin 1) A
  | ⟨0, _⟩ => MvPowerSeries.X (0 : Fin 1)
  | ⟨1, _⟩ => a.F
  -- cast a one variable power series to multivariable power series


theorem inv_exist {A : Type*} [CommRing A] {F : FormalGroup A} : ∃ (ι : PowerSeries_coeff A), @MvPowerSeries.coeff (Fin 1) A _ (Finsupp.equivFunOnFinite.invFun (1 : Fin 1 → ℕ)) ι.F = - 1 ∧ @MvPowerSeries.subst _ A _ _ A _  _ (sub_sec' ι) F.F  = 0 := sorry


end FormalGroup
