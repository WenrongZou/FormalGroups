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
import FormalGroups.TruncP

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

-- noncomputable instance {A : Type*} [CommRing A] [UniformSpace A] : FormalGroup A where
--   toFun := MvPolynomial.toMvPowerSeries (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2))
--   zero_coeff := by
--     simp only [Fin.isValue, MvPolynomial.coe_add, MvPolynomial.coe_X,
--     MvPowerSeries.coeff_zero_eq_constantCoeff, map_add, MvPowerSeries.constantCoeff_X, add_zero]
--   lin_coeff_X := by
--     rw [MvPolynomial.coeff_coe, MvPolynomial.coeff_add]
--     calc
--       _ = (1 : A) + (0 : A) := by
--         simp only [Fin.isValue, MvPolynomial.coeff_single_X, and_self, ↓reduceIte, one_ne_zero,
--           and_false, add_zero]
--       _ = 1 := by norm_num
--   lin_coeff_Y := by
--     rw [MvPolynomial.coeff_coe, MvPolynomial.coeff_add]
--     calc
--       _ = (0 : A) + (1 : A) := by
--         simp only [Fin.isValue, MvPolynomial.coeff_single_X, zero_ne_one, and_false, ↓reduceIte,
--           and_self, zero_add]
--       _ = 1 := by norm_num
--   assoc := by
--     unfold MvPowerSeries.subst
--     let f : MvPolynomial (Fin 2) A := (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2))
--     have hf := Classical.epsilon_spec
--       (p := fun (p : MvPolynomial (Fin 2) A) ↦ p = (f : MvPowerSeries (Fin 2) A)) ⟨f, rfl⟩
--     unfold eval₂
--     rw [if_pos hf]
--     rw [if_pos hf]
--     unfold sub_fir
--     unfold sub_sec
--     simp
--     have eq_aux : MvPowerSeries.subst sub_fir_aux (MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2)) (R := A)
--       = MvPowerSeries.X (0 : Fin 3) + MvPowerSeries.X (1 : Fin 3) (R := A):= by
--       unfold MvPowerSeries.subst
--       have poly_eq_powerseries : MvPolynomial.eval₂ (algebraMap A (MvPowerSeries (Fin 3) A)) sub_fir_aux (MvPolynomial.X 0 + MvPolynomial.X 1) =
--         MvPowerSeries.X 0 + MvPowerSeries.X 1 := by
--         simp only [Fin.isValue, MvPolynomial.eval₂_add, MvPolynomial.eval₂_X]
--         unfold sub_fir_aux
--         simp only [Fin.isValue]
--       unfold MvPowerSeries.eval₂

--       rw [if_pos]
--       rw [←poly_eq_powerseries]
--       congr
--       rw [←MvPolynomial.coe_X 0,← MvPolynomial.coe_X 1]
--       unfold f at hf
--       apply MvPolynomial.coe_inj.mp
--       exact hf
--       rw [←MvPolynomial.coe_X 0,← MvPolynomial.coe_X 1]
--       unfold f at hf
--       exact hf
--     have eq_aux' : MvPowerSeries.subst sub_sec_aux (MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2)) (R := A)
--       = MvPowerSeries.X (1 : Fin 3) + MvPowerSeries.X (2 : Fin 3) (R := A):= by
--       unfold MvPowerSeries.subst
--       have poly_eq_powerseries : MvPolynomial.eval₂ (algebraMap A (MvPowerSeries (Fin 3) A)) sub_sec_aux (MvPolynomial.X 0 + MvPolynomial.X 1) =
--         MvPowerSeries.X 1 + MvPowerSeries.X 2 := by
--         simp only [Fin.isValue, MvPolynomial.eval₂_add, MvPolynomial.eval₂_X]
--         unfold sub_sec_aux
--         simp only [Fin.isValue]
--       unfold MvPowerSeries.eval₂

--       rw [if_pos]
--       rw [←poly_eq_powerseries]
--       congr
--       rw [←MvPolynomial.coe_X 0,← MvPolynomial.coe_X 1]
--       unfold f at hf
--       apply MvPolynomial.coe_inj.mp
--       exact hf
--       rw [←MvPolynomial.coe_X 0,← MvPolynomial.coe_X 1]
--       unfold f at hf
--       exact hf
--     rw [eq_aux', eq_aux]
--     have epsilon_aux : (epsilon fun (p : MvPolynomial (Fin 2) A) ↦ ↑p = MvPowerSeries.X (0 : Fin 2) (R := A) + MvPowerSeries.X (1 : Fin 2) (R := A)) =
--       MvPolynomial.X (0 : Fin 2) (R := A) + MvPolynomial.X (1 : Fin 2) (R := A) := by
--       rw [←MvPolynomial.coe_X 0,← MvPolynomial.coe_X 1]
--       norm_cast
--       unfold f at hf
--       norm_cast at hf
--     rw [epsilon_aux]
--     simp only [Fin.isValue, MvPolynomial.eval₂_add, MvPolynomial.eval₂_X]
--     ring

-- open MvPowerSeries

-- theorem sub_self {A : Type*} [CommRing A] (f : MvPowerSeries (Fin 2) A):
--   f =
--   MvPowerSeries.subst
--     (fun x ↦
--       match x with
--       | ⟨0, _⟩ => MvPowerSeries.X (0 : Fin 2)
--       | ⟨1, _⟩ => MvPowerSeries.X (1 : Fin 2))
--     f := by
--   have eq_aux : X = (fun (x : Fin 2) ↦
--       match x with
--       | ⟨0, isLt⟩ => MvPowerSeries.X (0 : Fin 2)
--       | ⟨1, isLt⟩ => MvPowerSeries.X (1 : Fin 2) (R := A)) := by
--     funext x
--     by_cases hx : x = 0
--     simp [hx]
--     have hx' : x = 1 := by omega
--     simp [hx']
--   rw [←eq_aux]
--   simp [←map_algebraMap_eq_subst_X f]


-- theorem sub_self' {A : Type*} [CommRing A] (f : PowerSeries A):
--   PowerSeries.subst (PowerSeries.X) f = f := by
--   simp only [← PowerSeries.map_algebraMap_eq_subst_X f, Algebra.id.map_eq_id, PowerSeries.map_id,
--     id_eq]

-- theorem sub_self₁ {A : Type*} [CommRing A] (f : MvPowerSeries (Fin 2) A):
--   f =
--   MvPowerSeries.subst
--     X
--     f := by
--   rw [←map_algebraMap_eq_subst_X f]
--   simp

-- theorem sub_assoc {A : Type*} [CommRing A] (f g h: PowerSeries  A) :
--   PowerSeries.subst (PowerSeries.subst h g) f
--     = PowerSeries.subst h (PowerSeries.subst g f) := by

--   sorry

noncomputable def invFun_aux {A : Type*} [CommRing A] (f : PowerSeries A)
  (h : IsUnit (PowerSeries.coeff A 1 f)) (hc : PowerSeries.constantCoeff A f = 0):
  -- b₁ := a₁⁻¹
  ℕ → A × (PowerSeries A)
  | 0 => (0, 0)
  | 1 => ( (h.unit⁻¹ : Units A), PowerSeries.C A ((h.unit⁻¹ : Units A) : A) * PowerSeries.X (R := A))
  | n + 1 =>  (- (h.unit⁻¹) * PowerSeries.coeff A (n + 1) (PowerSeries.subst ((invFun_aux f h hc n).2) f) , (invFun_aux f h hc n).2 + PowerSeries.C A (- (h.unit⁻¹) * PowerSeries.coeff A (n + 1) (PowerSeries.subst ((invFun_aux f h hc n).2) f)) * (PowerSeries.X) ^ (n + 1))


lemma coeff_zero_aux {A : Type*} [CommRing A] (f : PowerSeries A)
 (h : IsUnit (PowerSeries.coeff A 1 f)) (hc : PowerSeries.constantCoeff A f = 0)
  : invFun_aux f h hc 0 = (0, 0) := by
  rfl

lemma coeff_one_aux {A : Type*} [CommRing A] (f : PowerSeries A)
 (h : IsUnit (PowerSeries.coeff A 1 f)) (hc : PowerSeries.constantCoeff A f = 0)
  : invFun_aux f h hc 1 =
    (((h.unit⁻¹ : Units A) : A), PowerSeries.C A ((h.unit⁻¹ : Units A) : A) * PowerSeries.X (R := A))
    := by
  rfl

lemma coeff_aux' {A : Type*} [CommRing A] (f : PowerSeries A)
 (h : IsUnit (PowerSeries.coeff A 1 f)) (hc : PowerSeries.constantCoeff A f = 0)
  {n : ℕ } (hn : n ≠ 0): invFun_aux f h hc (n + 1) =
    (- (h.unit⁻¹) * PowerSeries.coeff A (n + 1) (PowerSeries.subst ((invFun_aux f h hc n).2) f) , (invFun_aux f h hc n).2 + PowerSeries.C A (- (h.unit⁻¹) * PowerSeries.coeff A (n + 1) (PowerSeries.subst ((invFun_aux f h hc n).2) f)) * (PowerSeries.X) ^ (n + 1))
    := by
  conv =>
    lhs
    unfold invFun_aux
  simp


lemma trunc'_of_mk {A : Type*} [CommRing A] (f : ℕ → A) (n : ℕ) :
  PowerSeries.trunc' (n + 1) (PowerSeries.mk f) = PowerSeries.trunc'
  n (PowerSeries.mk f) + (Polynomial.C (f (n + 1))) * (Polynomial.X) ^ (n + 1) := by
  unfold PowerSeries.trunc'
  simp
  unfold PowerSeries.truncFun'
  have finset_aux : Finset.Iic (n + 1) = insert (n + 1) (Finset.Iic (n)) := by
    refine (Finset.erase_eq_iff_eq_insert ?_ ?_).mp ?_
    all_goals simp
    exact rfl
  rw [finset_aux]
  simp [Finset.sum_insert]
  conv =>
    lhs
    rw [add_comm]
  congr
  exact Eq.symm Polynomial.C_mul_X_pow_eq_monomial



theorem subst_inv_aux₀ {A : Type*} [CommRing A] (f : PowerSeries A)
 (h : IsUnit (PowerSeries.coeff A 1 f)) (hc : PowerSeries.constantCoeff A f = 0)
 {n : ℕ}
: let g : PowerSeries A := PowerSeries.mk (fun n => (invFun_aux f h hc n).1)
  PowerSeries.trunc' n g = ((invFun_aux f h hc n).2) := by
induction n with
| zero =>
  rw [coeff_zero_aux]
  simp [PowerSeries.trunc']
  ext d
  simp [PowerSeries.coeff_truncFun']
  intro hd
  rw [hd]
  rw [coeff_zero_aux]
| succ k ih =>
  by_cases hk : k = 0
  rw [hk]
  simp
  rw [coeff_one_aux]
  simp [PowerSeries.trunc']
  ext d
  simp [PowerSeries.coeff_truncFun']
  by_cases hd : d = 0
  simp [hd, coeff_zero_aux]
  by_cases hd1 : d = 1
  simp [hd1, coeff_one_aux]
  have hd2 : ¬ d ≤ 1 := by
    omega
  simp [hd2, PowerSeries.coeff_X, if_neg hd1]
  rw [coeff_aux' f h hc hk]
  simp
  rw [trunc'_of_mk]
  nth_rw 1 [← ih]
  norm_num
  rw [coeff_aux' f h hc hk]
  simp

-- (PowerSeries.constantCoeff A) (invFun_aux f h hc k).2 = 0
lemma subst_inv_aux₂ {A : Type*} [CommRing A] (f : PowerSeries A)
 (h : IsUnit (PowerSeries.coeff A 1 f)) (hc : PowerSeries.constantCoeff A f = 0)
 {n : ℕ}
: (PowerSeries.constantCoeff A) (invFun_aux f h hc n).2 = 0 := by
  rw [←subst_inv_aux₀]
  induction n with
  | zero =>
    unfold PowerSeries.trunc'
    unfold PowerSeries.truncFun'
    simp
    have set_eq : Finset.Iic 0 = {0} := rfl
    rw [set_eq, Finset.sum_singleton, coeff_zero_aux]
    simp
  | succ k ih =>
    rw [trunc'_of_mk]
    simp [ih]


lemma substDomain_inv {A : Type*} [CommRing A] (f : PowerSeries A)
 (h : IsUnit (PowerSeries.coeff A 1 f)) : PowerSeries.SubstDomain ((PowerSeries.C A) ↑h.unit⁻¹ * PowerSeries.X) := by
  refine PowerSeries.substDomain_of_constantCoeff_zero ?_
  have eq_aux : (PowerSeries.C A) (↑h.unit⁻¹ : A) * PowerSeries.X = (↑h.unit⁻¹ : A) • PowerSeries.X := by
    exact Eq.symm (PowerSeries.smul_eq_C_mul PowerSeries.X (↑h.unit⁻¹ : A))
  rw [eq_aux, constantCoeff_smul (PowerSeries.X (R := A)) (↑h.unit⁻¹ : A)]
  unfold PowerSeries.X
  simp

lemma subst_pow_add {A : Type*} [CommRing A] (f g: PowerSeries A) (n : ℕ)
  (hn₀ : n ≠ 0) (a : A) (hg : PowerSeries.constantCoeff A g = 0):
  PowerSeries.coeff A n (PowerSeries.subst (g + (PowerSeries.C A) a * PowerSeries.X ^ n) f) = PowerSeries.coeff A n (PowerSeries.subst g f) + (PowerSeries.coeff A 1) f * a := by
  rw [PowerSeries.coeff_subst', PowerSeries.coeff_subst']
  have aux : ∑ᶠ (d : ℕ), (PowerSeries.coeff A d) f • (PowerSeries.coeff A n) ((g + (PowerSeries.C A) a * PowerSeries.X ^ n) ^ d) -
  ∑ᶠ (d : ℕ), (PowerSeries.coeff A d) f • (PowerSeries.coeff A n) (g ^ d) = (PowerSeries.coeff A 1) f * a := by
    rw [←finsum_sub_distrib, finsum_eq_single _ 1]
    simp; ring
    intro m hm
    have eq_aux : (PowerSeries.coeff A n) ((g + (PowerSeries.C A) a * PowerSeries.X ^ n) ^ m) =
      (PowerSeries.coeff A n) (g ^ m) := by
      by_cases hm₀ : m = 0
      rw [hm₀]
      simp
      have hm₂ : m ≥ 2 := by omega
      rw [PowerSeries.coeff_pow, PowerSeries.coeff_pow]
      have coeff_aux : ∀ l ∈ (Finset.range m).finsuppAntidiag n, ∏ i ∈ Finset.range m, (PowerSeries.coeff A (l i)) (g + (PowerSeries.C A) a * PowerSeries.X ^ n) =  ∏ i ∈ Finset.range m, (PowerSeries.coeff A (l i)) g := by
        intro l hl
        by_cases hi : ∃ i₀ ∈ Finset.range m, l i₀ = n
        obtain ⟨i₀, hi₀, hi₁⟩ := hi
        have ljzero : ∃ j ∈ (Finset.range m), l j = 0 := by
          by_contra hc
          simp at hc
          have geone : ∀ x < m, l x ≥ 1 := by
            intro x hx
            obtain hc' := hc x hx
            omega
          simp at hl
          obtain ⟨hl₁, hl₂⟩ := hl
          have set_eq : (Finset.range m) = insert i₀ ((Finset.range m).erase i₀) := by
            exact Eq.symm (Finset.insert_erase hi₀)
          rw [set_eq, Finset.sum_insert, hi₁] at hl₁
          have sum_ge_one : ∑ x ∈ (Finset.range m).erase i₀, l x ≥ 1 := by
            calc
              _ ≥ ∑ x ∈ (Finset.range m).erase i₀, 1 := by
                refine Finset.sum_le_sum ?_
                intro i hi
                simp at hi
                obtain ⟨hineq, hile⟩ := hi
                exact geone i hile
              _ = m - 1 := by
                simp
                have meq : m = (Finset.range m).card := by simp
                nth_rw 2 [meq]
                exact Finset.card_erase_of_mem hi₀
              _ ≥ 1 := by omega
          linarith
          simp
        obtain ⟨j, hj₀, hj⟩ := ljzero
        have zero_aux₁ : (PowerSeries.coeff A (l j)) (g + (PowerSeries.C A) a * PowerSeries.X ^ n) = 0 := by
          rw [hj]
          simp [hg, zero_pow hn₀]
        have zero_aux₂ : (PowerSeries.coeff A (l j)) (g) = 0 := by
          rw [hj]
          simp [hg]
        rw [Finset.prod_eq_zero hj₀ zero_aux₁, Finset.prod_eq_zero hj₀ zero_aux₂]
        have hi' : ∀ i ∈ (Finset.range m), l i < n := by
          simp at hi
          have hile : ∀ i < m, l i ≤ n := by
            by_contra hc
            simp at hc
            obtain ⟨x, xle, hx⟩ := hc
            simp at hl
            obtain ⟨hl₁, hl₂⟩ := hl
            have lt_aux : (Finset.range m).sum ⇑l > n := by
              calc
                _ ≥ l x := by
                  refine Finset.single_le_sum ?_ ?_
                  intro i hi_in
                  linarith
                  simp [xle]
                _ > n := hx
            linarith
          intro i hi_in
          simp at hi_in
          obtain h₁ := hi i hi_in
          obtain h₂ := hile i hi_in
          exact lt_of_le_of_ne h₂ h₁
        apply Finset.prod_congr
        simp
        simp [map_add]
        intro i hile
        rw [PowerSeries.coeff_X_pow, if_neg]
        simp
        obtain hi2 := hi' i (by simp [hile])
        linarith
      refine Finset.sum_congr (by simp) coeff_aux
    rw [eq_aux]
    ring
    refine PowerSeries.coeff_subst_finite (PowerSeries.substDomain_of_constantCoeff_zero ?_) f (Finsupp.single () n)
    unfold PowerSeries.constantCoeff at hg
    unfold PowerSeries.X
    simp [hg, constantCoeff_X, zero_pow hn₀]
    refine PowerSeries.coeff_subst_finite (PowerSeries.substDomain_of_constantCoeff_zero ?_) f (Finsupp.single () n)
    unfold PowerSeries.constantCoeff at hg
    exact hg
  conv =>
    rhs
    rw [← aux]
  ring
  exact PowerSeries.substDomain_of_constantCoeff_zero hg
  refine PowerSeries.substDomain_of_constantCoeff_zero ?_
  unfold PowerSeries.constantCoeff at hg
  unfold PowerSeries.X
  simp [hg, constantCoeff_X, zero_pow hn₀]



theorem subst_inv_aux₁ {A : Type*} [CommRing A] (f : PowerSeries A)
 (h : IsUnit (PowerSeries.coeff A 1 f)) (hc : PowerSeries.constantCoeff A f = 0)
 {n : ℕ}
:
  (PowerSeries.trunc' n) (PowerSeries.subst (invFun_aux f h hc n).2 f) = (PowerSeries.trunc' n) PowerSeries.X := by
  induction n with
  | zero =>
    rw [coeff_zero_aux]
    have subst_zero : (PowerSeries.subst (0 : PowerSeries A) f) = 0 := by
      refine PowerSeries.ext ?_
      intro n
      rw [PowerSeries.coeff_subst']
      simp
      apply finsum_eq_zero_of_forall_eq_zero
      intro d
      by_cases hd : d = 0
      rw [hd]
      simp
      intro hn
      exact hc
      rw [zero_pow]
      simp [hd]
      exact hd
      exact PowerSeries.substDomain_of_constantCoeff_zero rfl
    rw [subst_zero]
    simp
    unfold PowerSeries.trunc'
    simp
    ext d
    simp [PowerSeries.coeff_truncFun']
    by_cases hd : d = 0
    rw [if_pos hd, PowerSeries.coeff_X, if_neg]
    simp [hd]
    rw [if_neg hd]
  | succ k ih =>
    by_cases hk : k = 0
    simp [hk]
    rw [coeff_one_aux]
    simp
    unfold PowerSeries.trunc'
    simp
    ext d
    simp [PowerSeries.coeff_truncFun']
    by_cases hd0 : d = 0
    rw [if_pos (by linarith), if_pos (by linarith), PowerSeries.coeff_subst']
    simp [hd0]
    apply finsum_eq_zero_of_forall_eq_zero
    intro x
    by_cases hx : x = 0
    simp [hx, hc]
    simp [zero_pow hx]
    refine PowerSeries.substDomain_of_constantCoeff_zero ?_
    have eq_aux : (PowerSeries.C A) (↑h.unit⁻¹ : A) * PowerSeries.X = (↑h.unit⁻¹ : A) • PowerSeries.X := by
      exact Eq.symm (PowerSeries.smul_eq_C_mul PowerSeries.X (↑h.unit⁻¹ : A))
    rw [eq_aux, constantCoeff_smul (PowerSeries.X (R := A)) (↑h.unit⁻¹ : A)]
    unfold PowerSeries.X
    simp
    by_cases hd1 : d = 1
    simp [hd1]
    rw [PowerSeries.coeff_subst', finsum_eq_single _ 1]
    simp
    intro m hm
    -- to prove (PowerSeries.coeff A m) f • (PowerSeries.coeff A 1) (((PowerSeries.C A) ↑h.unit⁻¹ * PowerSeries.X) ^ m) = 0
    have coeff_zero : (PowerSeries.coeff A 1) (((PowerSeries.C A) ↑h.unit⁻¹ * PowerSeries.X) ^ m) = 0 := by
      rw [mul_pow, ←map_pow, PowerSeries.coeff_C_mul_X_pow, if_neg (Ne.symm hm)]
    simp [coeff_zero]
    -- substDomain
    exact (substDomain_inv f h)
    have dgetwo : ¬ d ≤ 1 := by
      omega
    rw [if_neg dgetwo, if_neg dgetwo]
    unfold invFun_aux
    simp
    have aux : (PowerSeries.trunc' k) (-((PowerSeries.C A) ↑h.unit⁻¹ *
      (PowerSeries.C A) ((PowerSeries.coeff A (k + 1)) (PowerSeries.subst (invFun_aux f h hc k).2 f)) *
      PowerSeries.X ^ (k + 1))) = 0 := by
      simp
      unfold PowerSeries.trunc'
      simp
      ext d
      by_cases hd : d ≤ k
      have eq_aux : ((PowerSeries.C A) (↑h.unit⁻¹ : A) *
              (PowerSeries.C A) ((PowerSeries.coeff A (k + 1)) (PowerSeries.subst (invFun_aux f h hc k).2 f)) *
            PowerSeries.X ^ (k + 1)) = (PowerSeries.C A) ((↑h.unit⁻¹ : A) * ((PowerSeries.coeff A (k + 1)) (PowerSeries.subst (invFun_aux f h hc k).2 f))) * PowerSeries.X ^ (k + 1) := by
        simp
      rw [PowerSeries.coeff_truncFun', if_pos hd, eq_aux, PowerSeries.coeff_C_mul_X_pow, if_neg]
      simp
      linarith
      rw [PowerSeries.coeff_truncFun', if_neg hd]
      simp
    rw [PowerSeries.trunc'_of_succ, PowerSeries.trunc'_of_subst k, map_add, aux, add_zero, ←PowerSeries.trunc'_of_subst k, ih]
    have zero_aux : (Polynomial.monomial (k + 1))
      ((PowerSeries.coeff A (k + 1))
        (PowerSeries.subst
          ((invFun_aux f h hc k).2 +
            -((PowerSeries.C A) ↑h.unit⁻¹ *
                  (PowerSeries.C A) ((PowerSeries.coeff A (k + 1)) (PowerSeries.subst (invFun_aux f h hc k).2 f)) *
                PowerSeries.X ^ (k + 1)))
          f)) = 0 := by
      simp
      have eq_aux : -((PowerSeries.C A) (↑h.unit⁻¹ : A) *
              (PowerSeries.C A) ((PowerSeries.coeff A (k + 1)) (PowerSeries.subst (invFun_aux f h hc k).2 f)) *
            PowerSeries.X ^ (k + 1)) = (PowerSeries.C A) (-(↑h.unit⁻¹ : A) * ((PowerSeries.coeff A (k + 1)) (PowerSeries.subst (invFun_aux f h hc k).2 f))) * PowerSeries.X ^ (k + 1) := by
        simp
      rw [eq_aux, subst_pow_add]
      simp [←mul_assoc]
      linarith
      exact subst_inv_aux₂ f h hc
    rw [zero_aux, add_zero, PowerSeries.trunc'_of_succ, PowerSeries.coeff_X, if_neg]
    simp
    simp [hk]
    exact subst_inv_aux₂ f h hc
    simp
    exact subst_inv_aux₂ f h hc

theorem subst_inv_aux {A : Type*} [CommRing A] (f : PowerSeries A)
  (h : IsUnit (PowerSeries.coeff A 1 f)) (hc : PowerSeries.constantCoeff A f = 0)
   : ∃ (g : PowerSeries A), PowerSeries.subst g f = PowerSeries.X
    ∧ PowerSeries.constantCoeff A g = 0 ∧ IsUnit (PowerSeries.coeff A 1 g) := by
  let g : PowerSeries A := PowerSeries.mk (fun n => (invFun_aux f h hc n).1)
  use g
  have substDomain_g : PowerSeries.SubstDomain g := by
    apply PowerSeries.substDomain_of_constantCoeff_nilpotent
    have zero_coeff : (PowerSeries.constantCoeff) A g = 0 := by
      unfold g
      unfold invFun_aux
      simp
    unfold PowerSeries.constantCoeff at zero_coeff
    simp [zero_coeff]
  constructor
  · apply PowerSeries.eq_of_forall_trunc'_eq
    intro n
    rw [PowerSeries.trunc'_of_subst, subst_inv_aux₀, subst_inv_aux₁]
    unfold g
    unfold invFun_aux
    simp
  constructor
  · unfold g
    unfold invFun_aux
    simp
  unfold g
  unfold invFun_aux
  simp
