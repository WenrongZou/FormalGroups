-- import FormalGroups.MvPowerSeries.Substitution
-- import Mathlib.LinearAlgebra.TensorProduct.Basic
-- import Mathlib.Data.Nat.Factors
-- import Mathlib.RingTheory.DiscreteValuationRing.Basic
-- import Mathlib.RingTheory.LocalRing.ResidueField.Defs
-- import Mathlib.RingTheory.Ideal.Basic
-- import Mathlib.Logic.Function.Iterate
-- import Mathlib.Data.Nat.PartENat

-- open MvPowerSeries

-- noncomputable def sub_fir_aux {A : Type*} [CommRing A]: Fin 2 → MvPowerSeries (Fin 3) A
--   | ⟨0, _⟩ => MvPowerSeries.X (0 : Fin 3)
--   | ⟨1, _⟩ => MvPowerSeries.X (1 : Fin 3)

-- noncomputable def sub_sec_aux {A : Type*} [CommRing A]: Fin 2 → MvPowerSeries (Fin 3) A
--   | ⟨0, _⟩ => MvPowerSeries.X (1 : Fin 3)
--   | ⟨1, _⟩ => MvPowerSeries.X (2 : Fin 3)


-- noncomputable def sub_fir {A : Type*} [CommRing A] (F : MvPowerSeries (Fin 2) A): Fin 2 → MvPowerSeries (Fin 3) A
--   | ⟨0, _⟩ => @MvPowerSeries.subst _ A _ _ A _  _ (sub_fir_aux) F
--   | ⟨1, _⟩ => MvPowerSeries.X (2 : Fin 3)

-- noncomputable def map_aux : Fin 2 → ℤ
--   | ⟨0, _⟩ => 1
--   | ⟨1, _⟩ => 2

-- noncomputable def F_test : MvPolynomial (Fin 2) ℤ := MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2)

-- theorem subst_two : MvPolynomial.eval map_aux F_test (R := ℤ )= 3 := by
--   -- unfold MvPolynomial.eval
--   -- unfold MvPolynomial.eval₂Hom
--   unfold F_test
--   simp only [Fin.isValue, map_add, MvPolynomial.eval_X]
--   unfold map_aux
--   simp

/-
Copyright (c) 2025 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/


import FormalGroups.MvPowerSeries.Substitution
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.PartENat

/-!

## One Dimensional Formal Group
This file defines one dimensional formal group law over a ring `A`, homomorphism and isomorphism between two formal group.

## Adivisor : María Inés de Frutos-Fernández

## Reference:
· Silverman, The Arithmetic of Elliptic Curves (2nd edition) - Chapter 4.
· Lubin--Tate, Formal Complex Multiplication in Local Fields.
· Hazewinkel, Formal Groups and Applications. Start with Chapters 1 and 2. Later you can look at some parts of Chapters 4 and 6.

-/

open Classical MvPowerSeries

-- Definition of Formal Group

-- Assume the coeffiecient ring `R` to be commutative ring.
variable {R : Type*} [CommRing R] {σ : Type*} {G : MvPowerSeries (Fin 2) R} {x y : R}

#check Fin 2
#check (1 : Fin 2)
#check MvPowerSeries (Fin 2) R

/-- `coeff_X : Fin 2 → ℕ` is used to get the linear coefficient in two variable of `X`. -/
def coeff_X : Fin 2 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 0

/-- `coeff_Y : Fin 2 → ℕ` is used to get the linear coefficient in two variable of `Y`. -/
def coeff_Y : Fin 2 → ℕ
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1

#check Finsupp.equivFunOnFinite.invFun coeff_X
#check subst

-- noncomputable def X : MvPowerSeries (Fin 2) R := MvPowerSeries.X (0 : Fin 2)

-- noncomputable def Y : MvPowerSeries (Fin 2) R := MvPowerSeries.X (1 : Fin 2)
-- make them as abbrev

noncomputable def sub_fir_aux {A : Type*} [CommRing A]: Fin 2 → MvPowerSeries (Fin 3) A
  | ⟨0, _⟩ => MvPowerSeries.X (0 : Fin 3)
  | ⟨1, _⟩ => MvPowerSeries.X (1 : Fin 3)

noncomputable def sub_sec_aux {A : Type*} [CommRing A]: Fin 2 → MvPowerSeries (Fin 3) A
  | ⟨0, _⟩ => MvPowerSeries.X (1 : Fin 3)
  | ⟨1, _⟩ => MvPowerSeries.X (2 : Fin 3)

-- instance : MvPowerSeries.SubstDomain sub_fir_aux (S := A):= sorry


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


-- structure MvPowerSeries_coeff (A : Type*) [CommRing A] where
--   toFun : MvPowerSeries (Fin 2) A
--   zero_coeff : MvPowerSeries.coeff A 0 toFun = 0
--   lin_coeff_X : MvPowerSeries.coeff A (Finsupp.equivFunOnFinite.invFun coeff_X) toFun = 1
--   lin_coeff_Y : MvPowerSeries.coeff A (Finsupp.equivFunOnFinite.invFun coeff_Y) toFun = 1


/-- A structure for a 1-dimensional formal group law over `R`-/
structure FormalGroup (A : Type*) [CommRing A]  where
  toFun : MvPowerSeries (Fin 2) A
  zero_coeff : MvPowerSeries.coeff A 0 toFun = 0
  lin_coeff_X : MvPowerSeries.coeff A (Finsupp.single 0 1) toFun = 1
  lin_coeff_Y : MvPowerSeries.coeff A (Finsupp.single 1 1) toFun = 1
  assoc : @MvPowerSeries.subst _ A _ _ A _  _ (sub_fir toFun) toFun = @MvPowerSeries.subst _ A _ _ A _  _ (sub_sec toFun) toFun
  --  Associativity of the Formal Group : `F (F (X, Y), Z) = F (X, F (Y, Z))`.

structure CommFormalGroup (A : Type*) [CommRing A] extends FormalGroup A where
  comm : toFun = @MvPowerSeries.subst _ A _ _ A _  _ (sub_symm) toFun
-- Commutativity F (X, Y) = F (Y, X)


-- Definition of homomorphism between Formal Group Law

/-- Formal Power Series with zero constant term. -/
structure PowerSeriesZeroConst (A : Type*) [CommRing A] where
  toFun : MvPowerSeries (Fin 1) A
  zero_coeff : MvPowerSeries.coeff A 0 toFun = 0
-- change all MvPowerSeries (Fin 1) A = PowerSeries

-- a (F (X, Y))
noncomputable def sub_hom₁ {A : Type*} [CommRing A]  (F : MvPowerSeries (Fin 2) A): Fin 1 → MvPowerSeries (Fin 2) A
  | ⟨0, _⟩ => F

-- G (a (X), a (Y))
noncomputable def sub_hom₂ {A : Type*} [CommRing A] (a : MvPowerSeries (Fin 1) A):
  Fin 2 → MvPowerSeries (Fin 2) A
  | ⟨0, _⟩ => @MvPowerSeries.subst _ A _ _ A _  _ (sub_hom₁ (MvPowerSeries.X (0 : Fin 2))) a
  | ⟨1, _⟩ => @MvPowerSeries.subst _ A _ _ A _  _ (sub_hom₁ (MvPowerSeries.X (1 : Fin 2))) a

/-- Let `G₁, G₂` be two formal group laws over `CommRing A`. A homomorphism (over `A`)
  `F (X, Y) → G (X, Y)` is a power series `α(X) = b₁ * X + b₂ * X ^ 2 + ⋯` with coefficients
  in `A` without constant term such that `α(F (X, Y)) = G (α (X), α (Y))`. -/
structure FormalGroupHom {A : Type*} [CommRing A] (G₁ G₂ : FormalGroup A) extends
  PowerSeriesZeroConst A where
  hom : MvPowerSeries.subst (sub_hom₁ G₁.toFun) toFun = @MvPowerSeries.subst _ A _ _ A _  _ (sub_hom₂ toFun) G₂.toFun
  --         a (F (X, Y))                    =          G (a (X), a (Y))

namespace FormalGroups

/-- The homomorphism `α(X) : F (X, Y) → G (X, Y)` is an isomorphism if there exists a
  homomorphism `β(X) : G (X, Y) → F (X, Y)` such that `α(β(X)) = X = β(α(X))`. -/

def IsIso {A : Type*} [CommRing A] {G₁ G₂ : FormalGroup A} (α : FormalGroupHom G₁ G₂) : Prop :=
  ∃ (β : FormalGroupHom G₂ G₁), @MvPowerSeries.subst _ A _ _ A _  _ (fun _ => β.toFun) α.toFun = MvPowerSeries.X (0 : Fin 1)
  ∧ @MvPowerSeries.subst _ A _ _ A _  _ (fun _ => α.toFun) β.toFun = MvPowerSeries.X (0 : Fin 1)
-- define it to be Equiv.

/-- An isomorphism `α(X) : F (X, Y) → G (X, Y)`, `α(X) = b₁ * X + b₂ * X ^ 2 + ⋯` is called strict isomorphism if `b₁ = 1`.-/
def IsStrictIso {A : Type*} [CommRing A] {G₁ G₂ : FormalGroup A} {α : FormalGroupHom G₁ G₂} : Prop := IsIso α
  ∧ MvPowerSeries.coeff A (Finsupp.equivFunOnFinite.invFun 1) α.toFun = 1


/-- The homomorphism `α(X) : F (X, Y) → G (X, Y)` is an isomorphism if and only if
  `b₁ ∈ U(A)`, the group units of `A`.-/

theorem isIso_iff_UnitCoeff {A : Type*} [CommRing A] {G₁ G₂ : FormalGroup A} (α : FormalGroupHom G₁ G₂) :
  IsIso α ↔ IsUnit (MvPowerSeries.coeff A (Finsupp.equivFunOnFinite.invFun 1) α.toFun) := sorry



#check FormalGroup R

noncomputable instance {A : Type*} [CommRing A] [UniformSpace A] : FormalGroup A where
  toFun := MvPolynomial.toMvPowerSeries (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2))
  zero_coeff := by
    simp only [Fin.isValue, MvPolynomial.coe_add, MvPolynomial.coe_X,
    MvPowerSeries.coeff_zero_eq_constantCoeff, map_add, MvPowerSeries.constantCoeff_X, add_zero]
  lin_coeff_X := by
    rw [MvPolynomial.coeff_coe, MvPolynomial.coeff_add]
    calc
      _ = (1 : A) + (0 : A) := by
        simp only [Fin.isValue, MvPolynomial.coeff_single_X, and_self, ↓reduceIte, one_ne_zero,
          and_false, add_zero]
      _ = 1 := by norm_num
  lin_coeff_Y := by
    rw [MvPolynomial.coeff_coe, MvPolynomial.coeff_add]
    calc
      _ = (0 : A) + (1 : A) := by
        simp only [Fin.isValue, MvPolynomial.coeff_single_X, zero_ne_one, and_false, ↓reduceIte,
          and_self, zero_add]
      _ = 1 := by norm_num
  assoc := by
    unfold MvPowerSeries.subst
    let f : MvPolynomial (Fin 2) A := (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2))
    have hf := Classical.epsilon_spec
      (p := fun (p : MvPolynomial (Fin 2) A) ↦ p = (f : MvPowerSeries (Fin 2) A)) ⟨f, rfl⟩
    unfold eval₂
    rw [if_pos hf]
    rw [if_pos hf]
    unfold sub_fir
    unfold sub_sec
    simp
    have eq_aux : MvPowerSeries.subst sub_fir_aux (MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2)) (R := A)
      = MvPowerSeries.X (0 : Fin 3) + MvPowerSeries.X (1 : Fin 3) (R := A):= by
      unfold MvPowerSeries.subst
      have poly_eq_powerseries : MvPolynomial.eval₂ (algebraMap A (MvPowerSeries (Fin 3) A)) sub_fir_aux (MvPolynomial.X 0 + MvPolynomial.X 1) =
        MvPowerSeries.X 0 + MvPowerSeries.X 1 := by
        simp only [Fin.isValue, MvPolynomial.eval₂_add, MvPolynomial.eval₂_X]
        unfold sub_fir_aux
        simp only [Fin.isValue]
      unfold MvPowerSeries.eval₂

      rw [if_pos]
      rw [←poly_eq_powerseries]
      congr
      rw [←MvPolynomial.coe_X 0,← MvPolynomial.coe_X 1]
      unfold f at hf
      apply MvPolynomial.coe_inj.mp
      exact hf
      rw [←MvPolynomial.coe_X 0,← MvPolynomial.coe_X 1]
      unfold f at hf
      exact hf
    have eq_aux' : MvPowerSeries.subst sub_sec_aux (MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2)) (R := A)
      = MvPowerSeries.X (1 : Fin 3) + MvPowerSeries.X (2 : Fin 3) (R := A):= by
      unfold MvPowerSeries.subst
      have poly_eq_powerseries : MvPolynomial.eval₂ (algebraMap A (MvPowerSeries (Fin 3) A)) sub_sec_aux (MvPolynomial.X 0 + MvPolynomial.X 1) =
        MvPowerSeries.X 1 + MvPowerSeries.X 2 := by
        simp only [Fin.isValue, MvPolynomial.eval₂_add, MvPolynomial.eval₂_X]
        unfold sub_sec_aux
        simp only [Fin.isValue]
      unfold MvPowerSeries.eval₂

      rw [if_pos]
      rw [←poly_eq_powerseries]
      congr
      rw [←MvPolynomial.coe_X 0,← MvPolynomial.coe_X 1]
      unfold f at hf
      apply MvPolynomial.coe_inj.mp
      exact hf
      rw [←MvPolynomial.coe_X 0,← MvPolynomial.coe_X 1]
      unfold f at hf
      exact hf
    rw [eq_aux', eq_aux]
    have epsilon_aux : (epsilon fun (p : MvPolynomial (Fin 2) A) ↦ ↑p = MvPowerSeries.X (0 : Fin 2) (R := A) + MvPowerSeries.X (1 : Fin 2) (R := A)) =
      MvPolynomial.X (0 : Fin 2) (R := A) + MvPolynomial.X (1 : Fin 2) (R := A) := by
      rw [←MvPolynomial.coe_X 0,← MvPolynomial.coe_X 1]
      norm_cast
      unfold f at hf
      norm_cast at hf
    rw [epsilon_aux]
    simp only [Fin.isValue, MvPolynomial.eval₂_add, MvPolynomial.eval₂_X]
    ring

open MvPowerSeries

theorem sub_self {A : Type*} [CommRing A] (f : MvPowerSeries (Fin 2) A):
  f =
  MvPowerSeries.subst
    (fun x ↦
      match x with
      | ⟨0, _⟩ => MvPowerSeries.X (0 : Fin 2)
      | ⟨1, _⟩ => MvPowerSeries.X (1 : Fin 2))
    f := by
  have eq_aux : X = (fun (x : Fin 2) ↦
      match x with
      | ⟨0, isLt⟩ => MvPowerSeries.X (0 : Fin 2)
      | ⟨1, isLt⟩ => MvPowerSeries.X (1 : Fin 2) (R := A)) := by
    funext x
    by_cases hx : x = 0
    simp [hx]
    have hx' : x = 1 := by omega
    simp [hx']
  rw [←eq_aux]
  simp [←map_algebraMap_eq_subst_X f]


theorem sub_self' {A : Type*} [CommRing A] (f : PowerSeries A):
  PowerSeries.subst (PowerSeries.X) f = f := by
  simp [←PowerSeries.map_algebraMap_eq_subst_X f]

theorem sub_self₁ {A : Type*} [CommRing A] (f : MvPowerSeries (Fin 2) A):
  f =
  MvPowerSeries.subst
    X
    f := by
  rw [←map_algebraMap_eq_subst_X f]
  simp

theorem sub_assoc {A : Type*} [CommRing A] (f g h: PowerSeries  A) :
  PowerSeries.subst (PowerSeries.subst h g) f
    = PowerSeries.subst h (PowerSeries.subst g f) := by

  sorry
