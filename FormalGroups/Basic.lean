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


/-- `coeff_X : Fin 2 → ℕ` is used to get the linear coefficient in two variable of `X`. -/
def coeff_X : Fin 2 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 0

/-- `coeff_Y : Fin 2 → ℕ` is used to get the linear coefficient in two variable of `Y`. -/
def coeff_Y : Fin 2 → ℕ
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1


noncomputable abbrev X₀ : MvPowerSeries (Fin 2) R := MvPowerSeries.X (0 : Fin 2)

noncomputable abbrev X₁ : MvPowerSeries (Fin 2) R := MvPowerSeries.X (1 : Fin 2)


noncomputable def sub_fir_aux {A : Type*} [CommRing A]: Fin 2 → MvPowerSeries (Fin 3) A
  | ⟨0, _⟩ => MvPowerSeries.X (0 : Fin 3)
  | ⟨1, _⟩ => MvPowerSeries.X (1 : Fin 3)

noncomputable def sub_sec_aux {A : Type*} [CommRing A]: Fin 2 → MvPowerSeries (Fin 3) A
  | ⟨0, _⟩ => MvPowerSeries.X (1 : Fin 3)
  | ⟨1, _⟩ => MvPowerSeries.X (2 : Fin 3)

-- instance : MvPowerSeries.SubstDomain sub_fir_aux (S := A):= sorry


-- (0 : Fin 2) ↦ F(X, Y), (1 : Fin 2) ↦ Z
noncomputable def sub_fir {A : Type*} [CommRing A] (F : MvPowerSeries (Fin 2) A): Fin 2 → MvPowerSeries (Fin 3) A
  | ⟨0, _⟩ => MvPowerSeries.subst (sub_fir_aux) F
  | ⟨1, _⟩ => MvPowerSeries.X (2 : Fin 3)

-- (0 : Fin 2) ↦ X, (1 : Fin 2) ↦ F (Y, Z)
noncomputable def sub_sec {A : Type*} [CommRing A] (F : MvPowerSeries (Fin 2) A): Fin 2 → MvPowerSeries (Fin 3) A
  | ⟨0, _⟩ => MvPowerSeries.X (0 : Fin 3)
  | ⟨1, _⟩ => MvPowerSeries.subst (sub_sec_aux) F

-- (0 : Fin 2) ↦ Y, (1 : Fin 2) ↦ X
noncomputable def sub_symm {A : Type*} [CommRing A] : Fin 2 → MvPowerSeries (Fin 2) A
  | ⟨0, _⟩ => X₁
  | ⟨1, _⟩ => X₀

noncomputable def sub_X {A : Type*} [CommRing A] : Fin 2 → MvPowerSeries (Fin 2) A
  | ⟨0, _⟩ => X₀
  | ⟨1, _⟩ => 0

noncomputable def sub_Y {A : Type*} [CommRing A] : Fin 2 → MvPowerSeries (Fin 2) A
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => X₁

#check subst (sub_fir G) G
#check subst (sub_sec G) G


/-- A structure for a 1-dimensional formal group law over `R`-/
structure FormalGroup (A : Type*) [CommRing A]  where
  toFun : MvPowerSeries (Fin 2) A
  zero_coeff : constantCoeff (Fin 2) A toFun = 0
  lin_coeff_X : subst sub_X toFun = X₀ (R := A)
  lin_coeff_Y : subst sub_Y toFun = X₁ (R := A)
  assoc : subst (sub_fir toFun) toFun = subst (sub_sec toFun) toFun
  --  Associativity of the Formal Group : `F (F (X, Y), Z) = F (X, F (Y, Z))`.

structure CommFormalGroup (A : Type*) [CommRing A] extends FormalGroup A where
  comm : toFun = MvPowerSeries.subst (sub_symm) toFun
-- Commutativity F (X, Y) = F (Y, X)


-- Definition of homomorphism between Formal Group Law

/-- Formal Power Series with zero constant term. -/
structure PowerSeriesZeroConst (A : Type*) [CommRing A] where
  toFun : PowerSeries A
  zero_coeff : PowerSeries.constantCoeff A toFun = 0

theorem SubstDomain_ZeroConst {A : Type*} [CommRing A] (α : PowerSeriesZeroConst A) :
  PowerSeries.SubstDomain α.toFun :=
  {
    const_coeff := by
      obtain h1 := α.zero_coeff
      unfold PowerSeries.constantCoeff at h1
      rw [h1]
      simp
  }


-- a (F (X, Y))
-- noncomputable def sub_hom₁ {A : Type*} [CommRing A]  (F : MvPowerSeries (Fin 2) A): MvPowerSeries (Fin 2) A
--   | ⟨0, _⟩ => F

-- G (a (X), a (Y))
noncomputable def sub_hom {A : Type*} [CommRing A] (a : PowerSeries  A):
  Fin 2 → MvPowerSeries (Fin 2) A
  | ⟨0, _⟩ => PowerSeries.subst  X₀ a
  | ⟨1, _⟩ => PowerSeries.subst  X₁ a

/-- Let `G₁, G₂` be two formal group laws over `CommRing A`. A homomorphism (over `A`)
  `F (X, Y) → G (X, Y)` is a power series `α(X) = b₁ * X + b₂ * X ^ 2 + ⋯` with coefficients
  in `A` without constant term such that `α(F (X, Y)) = G (α (X), α (Y))`. -/
structure FormalGroupHom {A : Type*} [CommRing A] (G₁ G₂ : FormalGroup A) extends
  PowerSeriesZeroConst A where
  hom : PowerSeries.subst (G₁.toFun) toFun = MvPowerSeries.subst (R := A) (sub_hom toFun) G₂.toFun
  --         a (F (X, Y))                    =          G (a (X), a (Y))

namespace FormalGroups

open MvPowerSeries

/-- The homomorphism `α(X) : F (X, Y) → G (X, Y)` is an isomorphism if there exists a
  homomorphism `β(X) : G (X, Y) → F (X, Y)` such that `α(β(X)) = X = β(α(X))`. -/

def IsIso {A : Type*} [CommRing A] {G₁ G₂ : FormalGroup A} (α : FormalGroupHom G₁ G₂) : Prop :=
  ∃ (β : FormalGroupHom G₂ G₁), PowerSeries.subst β.toFun α.toFun = PowerSeries.X
  ∧ PowerSeries.subst α.toFun β.toFun = PowerSeries.X
-- can not define it to be Equiv.

/-- An isomorphism `α(X) : F (X, Y) → G (X, Y)`, `α(X) = b₁ * X + b₂ * X ^ 2 + ⋯` is called strict isomorphism if `b₁ = 1`.-/
def IsStrictIso {A : Type*} [CommRing A] {G₁ G₂ : FormalGroup A} {α : FormalGroupHom G₁ G₂} : Prop := IsIso α
  ∧ coeff A (Finsupp.equivFunOnFinite.invFun 1) α.toFun = 1


/-- The homomorphism `α(X) : F (X, Y) → G (X, Y)` is an isomorphism if and only if
  `b₁ ∈ U(A)`, the group units of `A`.-/

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



-- prove the following theorem by inductively construct the coefficient
theorem PowerSeries_subst_inv {A : Type*} [CommRing A] (f : PowerSeries A)
  (h : IsUnit (PowerSeries.coeff A 1 f)) (hc : PowerSeries.constantCoeff A f = 0): ∃ (g : PowerSeries A),
  PowerSeries.subst f g = PowerSeries.X
  ∧ PowerSeries.subst g f = PowerSeries.X ∧ PowerSeries.constantCoeff A g = 0 := by
  obtain ⟨g, hg₁, hg₂, hg₃⟩ := subst_inv_aux f h hc
  use g
  constructor
  · obtain ⟨g', hg₁', hg₂', hg₃'⟩ := subst_inv_aux g hg₃ hg₂
    have eq_aux : f = g' := by
      have subst_aux₁ : PowerSeries.subst g' (PowerSeries.subst g f) = g' := by
        rw [hg₁, PowerSeries.subst_X]
        apply PowerSeries.substDomain_of_constantCoeff_nilpotent
        unfold PowerSeries.constantCoeff at hg₂'
        rw [hg₂']
        simp
      have subst_aux₂ : PowerSeries.subst g' (PowerSeries.subst g f) =
        PowerSeries.subst (PowerSeries.subst g' g) f := by
        rw [←PowerSeries.subst_comp_subst]
        simp
        apply PowerSeries.substDomain_of_constantCoeff_nilpotent
        unfold PowerSeries.constantCoeff at hg₂
        rw [hg₂]
        simp only [IsNilpotent.zero]
        apply PowerSeries.substDomain_of_constantCoeff_nilpotent
        unfold PowerSeries.constantCoeff at hg₂'
        rw [hg₂']
        simp
      rw [←subst_aux₁, subst_aux₂, hg₁']
      simp [←PowerSeries.map_algebraMap_eq_subst_X f]
    simpa [eq_aux]
  constructor
  · exact hg₁
  · exact hg₂



lemma subst_self {A : Type*} [CommRing A] (f : MvPowerSeries (Fin 2) A):
  f =
  MvPowerSeries.subst
    (fun x ↦
      match x with
      | ⟨0, _⟩ => X₀
      | ⟨1, _⟩ => X₁)
    f := by
  have eq_aux : X = (fun (x : Fin 2) ↦
      match x with
      | ⟨0, isLt⟩ => X₀
      | ⟨1, isLt⟩ => X₁ (R := A)) := by
    funext x
    by_cases hx : x = 0
    simp [hx]
    have hx' : x = 1 := by omega
    simp [hx']
  rw [←eq_aux]
  simp [←map_algebraMap_eq_subst_X f]


-- need some theorem like associativity of substitution
theorem subst_assoc {A : Type*} [CommRing A] {σ : Type*} (f g: PowerSeries  A)
  (h : MvPowerSeries σ A) (hg : PowerSeries.SubstDomain g) (hh : PowerSeries.SubstDomain h) :
  PowerSeries.subst (PowerSeries.subst h g) f
    = PowerSeries.subst h (PowerSeries.subst g f) := by
  rw [←PowerSeries.subst_comp_subst]
  simp only [Function.comp_apply]
  exact hg
  exact hh

lemma substDomain_aux {A : Type*} [CommRing A]   {g : PowerSeries A}
 (hb3 : (PowerSeries.constantCoeff A) g = 0) (G₁ : FormalGroup A)
  : PowerSeries.SubstDomain (subst (sub_hom g) G₁.toFun) :=
  {
    const_coeff := by
      have eq_zero : ((constantCoeff (Fin 2) A) (subst (sub_hom g) G₁.toFun)) = 0 := by
        unfold sub_hom
        rw [constantCoeff_subst]
        simp
        have eq_zero_aux : ∀ (d : Fin 2 →₀ ℕ), (coeff A d) G₁.toFun *
            ((constantCoeff (Fin 2) A) (PowerSeries.subst (X 0) g) ^ d 0 *
          (constantCoeff (Fin 2) A) (PowerSeries.subst (X 1) g) ^ d 1) =
          0 := by
          intro d
          by_cases hd : d = 0
          · simp [hd, G₁.zero_coeff]
          · by_cases hd₀ : d 0 ≠ 0
            · have zero_aux : (constantCoeff (Fin 2) A) (PowerSeries.subst (X 0) g) ^ d 0 = 0 := by
                rw [PowerSeries.constantCoeff_subst]
                have zero_aux : ∀ (n : ℕ), (n ≠ 0) →  (constantCoeff (Fin 2) A) (X 0 ^ n) = 0 := by
                  intro n hn
                  simp [hn]
                have zero_aux' : ∑ᶠ (d : ℕ), (PowerSeries.coeff A d) g • (constantCoeff (Fin 2) A) (X 0 ^ d) = 0 := by
                  conv =>
                    rhs
                    rw [←finsum_zero (α := ℕ)]
                  congr
                  funext n
                  simp [zero_aux n]
                  by_cases hn : n = 0
                  simp [hn, hb3]
                  simp [hn]
                rw [zero_aux']
                exact (zero_pow hd₀)
                apply PowerSeries.substDomain_of_constantCoeff_nilpotent
                simp
              simp [zero_aux]
            ·
              have hd₁ : d 1 ≠ 0 := by
                by_contra h'
                simp at hd₀
                apply hd
                refine Eq.symm (Finsupp.ext ?_)
                intro a
                by_cases ha : a = 0
                simp [ha, hd₀]
                have ha' : a = 1 := by omega
                simp [ha', h']
              have zero_aux : (constantCoeff (Fin 2) A) (PowerSeries.subst (X 1) g) ^ d 1 = 0 := by
                rw [PowerSeries.constantCoeff_subst]
                have zero_aux : ∀ (n : ℕ), (n ≠ 0) →  (constantCoeff (Fin 2) A) (X 1 ^ n) = 0 := by
                  intro n hn
                  simp [hn]
                have zero_aux' : ∑ᶠ (d : ℕ), (PowerSeries.coeff A d) g • (constantCoeff (Fin 2) A) (X 1 ^ d) = 0 := by
                  conv =>
                    rhs
                    rw [←finsum_zero (α := ℕ)]
                  congr
                  funext n
                  simp [zero_aux n]
                  by_cases hn : n = 0
                  simp [hn, hb3]
                  simp [hn]
                rw [zero_aux']
                exact (zero_pow hd₁)
                apply PowerSeries.substDomain_of_constantCoeff_nilpotent
                simp
              simp [zero_aux]
        conv =>
          rhs
          rw [←finsum_zero (α := Fin 2 →₀ ℕ)]
        congr
        funext d
        exact (eq_zero_aux d)
        apply substDomain_of_constantCoeff_nilpotent
        intro x
        by_cases hx : x = 0
        simp [hx]
        have const_zero : ((constantCoeff (Fin 2) A) (PowerSeries.subst (X 0) g)) = 0 := by
          rw [PowerSeries.constantCoeff_subst]
          simp
          conv =>
            rhs
            rw [←finsum_zero (α := ℕ)]
          congr
          funext d
          by_cases hd : d = 0
          simp [hd, hb3]
          simp [hd]
          apply PowerSeries.substDomain_of_constantCoeff_nilpotent
          simp
        simp [const_zero]
        have hx' : x = 1 := by omega
        simp [hx']
        have const_zero : ((constantCoeff (Fin 2) A) (PowerSeries.subst (X 1) g)) = 0 := by
          rw [PowerSeries.constantCoeff_subst]
          simp
          conv =>
            rhs
            rw [←finsum_zero (α := ℕ)]
          congr
          funext d
          by_cases hd : d = 0
          simp [hd, hb3]
          simp [hd]
          apply PowerSeries.substDomain_of_constantCoeff_nilpotent
          simp
        simp [const_zero]
      rw [eq_zero]
      simp
  }

lemma isIso_iff_substDomain_aux {A : Type*} [CommRing A] {g : PowerSeries A}
  (hb3 : (PowerSeries.constantCoeff A) g = 0)
  : SubstDomain (sub_hom g) := by
  apply substDomain_of_constantCoeff_nilpotent
  intro x
  by_cases hx : x = 0
  · rw [hx]
    have zero_aux : ((constantCoeff (Fin 2) A) (sub_hom g 0)) = 0 := by
      unfold sub_hom
      simp
      rw [PowerSeries.constantCoeff_subst]
      conv =>
        rhs; rw [←finsum_zero (α := ℕ)]
      congr; funext d
      by_cases hd : d = 0
      simp [hd, hb3]
      simp [hd]
      apply PowerSeries.substDomain_of_constantCoeff_nilpotent
      simp
    simp [zero_aux]
  · have hx' : x = 1 := by omega
    rw [hx']
    have zero_aux : ((constantCoeff (Fin 2) A) (sub_hom g 1)) = 0 := by
      unfold sub_hom
      simp
      rw [PowerSeries.constantCoeff_subst]
      conv =>
        rhs; rw [←finsum_zero (α := ℕ)]
      congr; funext d
      by_cases hd : d = 0
      simp [hd, hb3]
      simp [hd]
      apply PowerSeries.substDomain_of_constantCoeff_nilpotent
      simp
    simp [zero_aux]

lemma isIso_iff_substDomain_aux2 {A : Type*} [CommRing A]
  {g : PowerSeries A} (hb3 : (PowerSeries.constantCoeff A) g = 0): SubstDomain (S := A) fun (x : Fin 2) ↦
  match x with
  | ⟨0, _⟩ => subst (fun _ ↦ X (0 : Fin 2)) g
  | ⟨1, _⟩ => subst (fun _ ↦ X 1) g := by
  apply substDomain_of_constantCoeff_nilpotent
  intro t
  by_cases ht : t = 0
  simp [ht]
  have subst_aux : SubstDomain (fun (x : Unit) ↦ X (0 : Fin 2)) (S := A) := by
    apply substDomain_of_constantCoeff_nilpotent
    simp
  rw [←coe_substAlgHom subst_aux]
  apply IsNilpotent_subst
  have zero_aux : (constantCoeff Unit A) g = 0 := by
    unfold PowerSeries.constantCoeff at hb3
    exact hb3
  simp [zero_aux]
  have ht' : t = 1 := by omega
  simp [ht']
  have subst_aux : SubstDomain (fun (x : Unit) ↦ X (1 : Fin 2)) (S := A) := by
    apply substDomain_of_constantCoeff_nilpotent
    simp
  rw [←coe_substAlgHom subst_aux]
  apply IsNilpotent_subst
  have zero_aux : (constantCoeff Unit A) g = 0 := by
    unfold PowerSeries.constantCoeff at hb3
    exact hb3
  simp [zero_aux]

lemma isIso_iff_aux {A : Type*} [CommRing A] {G₁ G₂ : FormalGroup A}
  (α : FormalGroupHom G₁ G₂)  {g : PowerSeries A}
  (hb3 : (PowerSeries.constantCoeff A) g = 0):
  MvPowerSeries.subst (sub_hom (PowerSeries.subst g α.toFun)) G₂.toFun =
  PowerSeries.subst (subst (sub_hom g) G₁.toFun) α.toFun := by
  obtain h1 := α.hom
  have eq_aux : subst (sub_hom g) (PowerSeries.subst G₁.toFun α.toFun)
    = subst (sub_hom g) (subst (sub_hom α.toFun) G₂.toFun) := by
    rw [h1]
  -- rw [←subst_comp_subst (b := (sub_hom₂ g))] at eq_aux
  unfold PowerSeries.subst
  -- α (F (β (X), β(Y)))
  have eq_aux1 : subst (sub_hom g) (PowerSeries.subst G₁.toFun α.toFun)
    = (PowerSeries.subst (subst (sub_hom g) G₁.toFun) α.toFun) := by
    unfold PowerSeries.subst
    rw [←subst_comp_subst]
    simp only [Function.comp_apply]
    apply substDomain_of_constantCoeff_nilpotent
    simp [←MvPowerSeries.coeff_zero_eq_constantCoeff, G₁.zero_coeff]
    apply substDomain_of_constantCoeff_nilpotent
    intro x
    by_cases hx : x = 0
    · rw [hx]
      have zero_aux : ((constantCoeff (Fin 2) A) (sub_hom g 0)) = 0 := by
        unfold sub_hom
        simp
        rw [PowerSeries.constantCoeff_subst]
        conv =>
          rhs; rw [←finsum_zero (α := ℕ)]
        congr; funext d
        by_cases hd : d = 0
        simp [hd, hb3]
        simp [hd]
        apply PowerSeries.substDomain_of_constantCoeff_nilpotent
        simp
      simp [zero_aux]
    · have hx' : x = 1 := by omega
      rw [hx']
      have zero_aux : ((constantCoeff (Fin 2) A) (sub_hom g 1)) = 0 := by
        unfold sub_hom
        simp
        rw [PowerSeries.constantCoeff_subst]
        conv =>
          rhs; rw [←finsum_zero (α := ℕ)]
        congr; funext d
        by_cases hd : d = 0
        simp [hd, hb3]
        simp [hd]
        apply PowerSeries.substDomain_of_constantCoeff_nilpotent
        simp
      simp [zero_aux]
  have eq_aux2 : subst (sub_hom g) (subst (sub_hom α.toFun) G₂.toFun) =
    subst (sub_hom (PowerSeries.subst g α.toFun)) G₂.toFun := by
    rw [subst_comp_subst_apply]
    unfold PowerSeries.subst
    have eq_aux' : (fun s ↦ subst (sub_hom g) (sub_hom α.toFun s)) =
      (sub_hom (subst (fun x ↦ g) α.toFun)) := by
      unfold sub_hom
      funext x
      by_cases hx : x = 0
      simp [hx]
      unfold PowerSeries.subst
      rw [subst_comp_subst_apply, subst_comp_subst_apply]
      have aux : (fun (s : Unit) ↦ subst
        (fun (x : Fin 2) ↦
          match x with
          | ⟨0, isLt⟩ => subst (fun x ↦ X (0 : Fin 2)) g
          | ⟨1, isLt⟩ => subst (fun x ↦ X 1) g)
        (X 0) (R := A))  = (fun (s : Unit) ↦ subst (fun x ↦ X (0 : Fin 2)) g (S := A))  := by
        funext s
        rw [subst_X]
        exact (isIso_iff_substDomain_aux2 hb3)
      rw [aux]
      apply substDomain_of_constantCoeff_nilpotent
      simp
      unfold PowerSeries.constantCoeff at hb3
      simp [hb3]
      exact substDomain_of_constantCoeff_nilpotent (by simp)
      exact substDomain_of_constantCoeff_nilpotent (by simp)
      exact (isIso_iff_substDomain_aux2 hb3)

      have hx' : x = 1 := by omega
      simp [hx']
      unfold PowerSeries.subst
      rw [subst_comp_subst_apply (substDomain_of_constantCoeff_nilpotent (by simp)) (isIso_iff_substDomain_aux2 hb3) , subst_comp_subst_apply]
      have aux : (fun (s : Unit) ↦ subst
        (fun (x : Fin 2) ↦
          match x with
          | ⟨0, isLt⟩ => subst (fun x ↦ X (0 : Fin 2)) g
          | ⟨1, isLt⟩ => subst (fun x ↦ X 1) g)
        (X 1) (R := A))  = (fun (s : Unit) ↦ subst (fun x ↦ X (1 : Fin 2)) g (S := A))  := by
        funext s
        rw [subst_X]
        exact (isIso_iff_substDomain_aux2 hb3)
      rw [aux]
      apply substDomain_of_constantCoeff_nilpotent
      simp
      unfold PowerSeries.constantCoeff at hb3
      simp [hb3]
      exact substDomain_of_constantCoeff_nilpotent (by simp)
    rw [eq_aux']
    exact (isIso_iff_substDomain_aux (α.zero_coeff))
    exact (isIso_iff_substDomain_aux hb3)
  rw [eq_aux1, eq_aux2] at eq_aux
  unfold PowerSeries.subst at eq_aux
  rw [←subst_comp_subst] at eq_aux
  rw [←subst_comp_subst, eq_aux]
  apply substDomain_of_constantCoeff_nilpotent
  simp [←MvPowerSeries.coeff_zero_eq_constantCoeff, G₁.zero_coeff]
  exact (isIso_iff_substDomain_aux hb3)
  apply substDomain_of_constantCoeff_nilpotent
  simp [←MvPowerSeries.coeff_zero_eq_constantCoeff, G₁.zero_coeff]
  exact (isIso_iff_substDomain_aux hb3)




theorem isIso_iff_UnitCoeff {A : Type*} [CommRing A] {G₁ G₂ : FormalGroup A} (α : FormalGroupHom G₁ G₂) :
  IsIso α ↔ IsUnit (PowerSeries.coeff A 1 α.toFun) := by
  constructor
  -- forward direction
  · intro h
    unfold IsIso at h
    obtain ⟨β, h₁, h₂⟩ := h
    obtain coeff_eq := PowerSeries.ext_iff.mp h₁ 1
    simp at coeff_eq
    have subdomain_a : PowerSeries.SubstDomain α.toFun := by
      apply SubstDomain_ZeroConst
    have subdomain_b : PowerSeries.SubstDomain β.toFun := by
      apply SubstDomain_ZeroConst
    have coeff_eq_mul : (PowerSeries.coeff A 1) (PowerSeries.subst β.toFun α.toFun) = (PowerSeries.coeff A 1 α.toFun) • (PowerSeries.coeff A 1 β.toFun) := by
      unfold PowerSeries.coeff
      rw [PowerSeries.coeff_subst subdomain_b α.toFun (Finsupp.single (Unit.unit : Unit) 1)]
      have supp_aux : ∑ᶠ (d : ℕ), (PowerSeries.coeff A d) α.toFun • (coeff A (Finsupp.single () 1)) (β.toFun ^ d) = (PowerSeries.coeff A 1) α.toFun • (coeff A (Finsupp.single () 1)) (β.toFun ^ 1) := by
        apply finsum_eq_single
        intro n hn
        by_cases hn_zero : n = 0
        simp [hn_zero, (α).zero_coeff]
        have coeff_zero : (coeff A (Finsupp.single () 1)) (β.toFun ^ n) = 0 := by
          have aux : (Finsupp.single () 1) () = 1 := by simp
          rw [←PowerSeries.coeff_def]
          have hn_ge : n ≥ 2 := by omega
          rw [PowerSeries.coeff_pow]
          have zero_aux : ∀ l ∈ (Finset.range n).finsuppAntidiag 1, ∏ i ∈ Finset.range n, (PowerSeries.coeff A (l i)) β.toFun = 0 := by
            intro l hl
            have exist_zero : ∃ i ∈ (Finset.range n), l i = 0 := by
              by_contra h'
              simp at h'
              have : ∀ x < n, l x ≥ 1 := by
                intro x hx
                obtain hx' := h' x hx
                omega
              simp at hl
              obtain ⟨hl₁, hl₂⟩ := hl
              have ineq_aux : (Finset.range n).sum ⇑l ≥ n := by
                calc
                  _ ≥ (Finset.range n).sum 1 := by
                    refine Finset.sum_le_sum ?_
                    intro i hi
                    simp at hi
                    obtain ineq := this i hi
                    simpa
                  _ = n := by
                    simp
              nlinarith
            obtain ⟨i, hi, exist_zero⟩ := exist_zero
            apply (Finset.prod_eq_zero hi)
            rw [exist_zero]
            simp [β.zero_coeff]
          exact (Finset.sum_eq_zero zero_aux)
          simp
        simp [coeff_zero]
      rw [supp_aux]
      simp
      congr
    rw [coeff_eq] at coeff_eq_mul
    unfold IsUnit
    let u : Aˣ :=
      {
        val := (PowerSeries.coeff A 1) α.toFun
        inv := (PowerSeries.coeff A 1) β.toFun
        val_inv := by
          simp [coeff_eq_mul]
        inv_val := by
          simp [coeff_eq_mul]
          ring_nf
      }
    use u
  -- backward direction
  · intro h
    unfold IsIso
    obtain ⟨g, hb1, hb2, hb3⟩ := PowerSeries_subst_inv α.toFun h α.zero_coeff
    let β : FormalGroupHom G₂ G₁ :=
    {
      toFun := g
      zero_coeff := hb3
      hom := by
        simp
        -- G (X, Y) = G (α(β(X)), α(β(Y)))
        have eq_aux : G₂.toFun =
          MvPowerSeries.subst (sub_hom (PowerSeries.subst g α.toFun)) G₂.toFun := by
          rw [hb2]
          unfold sub_hom
          rw [PowerSeries.subst_X, PowerSeries.subst_X]
          exact (subst_self G₂.toFun)
          refine PowerSeries.substDomain_of_constantCoeff_zero ?_
          simp
          refine PowerSeries.substDomain_of_constantCoeff_zero ?_
          simp
        -- G(α(g(X)), α(g(Y))) = α(F (β(X), β(Y)))
        have eq_aux' : G₂.toFun
          = PowerSeries.subst (subst (sub_hom g) G₁.toFun) α.toFun := by
          rw [eq_aux]
          obtain h' := α.hom
          exact (isIso_iff_aux α hb3)
        rw [eq_aux']
        -- maybe need to change f here to satisfies some property that f ∈ PowerSeries.SubstDomain
        have subst_aux : ∀ (f : MvPowerSeries (Fin 2) A), PowerSeries.SubstDomain f →
          PowerSeries.subst (PowerSeries.subst f α.toFun) g = f := by
          intro f hf
          rw [subst_assoc g α.toFun f, hb1, PowerSeries.subst_X]
          exact hf
          exact SubstDomain_ZeroConst α.toPowerSeriesZeroConst
          exact hf
        refine (subst_aux (MvPowerSeries.subst (sub_hom g) G₁.toFun) ?_)
        -- need to prove SubstDomain namely, `PowerSeries.SubstDomain (subst (sub_hom₂ g) G₁.toFun)`
        -- make this to be a lemma
        exact (substDomain_aux hb3 G₁ )
    }
    use β


lemma SubstDomain_Add_aux₁ {A : Type*} [CommRing A] [UniformSpace A] : MvPowerSeries.SubstDomain sub_fir_aux (S := A) :=
  { const_coeff := by
      intro s
      unfold sub_fir_aux
      by_cases hs : s = 0
      simp only [hs, Fin.isValue, MvPowerSeries.constantCoeff_X, IsNilpotent.zero]
      have hs' : s = 1 := by omega
      simp only [hs', Fin.isValue, MvPowerSeries.constantCoeff_X, IsNilpotent.zero]
    tendsto_zero := by
      simp only [Filter.cofinite_eq_bot, Filter.tendsto_bot] }


lemma SubstDomain_Add_aux₂ {A : Type*} [CommRing A] [UniformSpace A] : MvPowerSeries.SubstDomain sub_sec_aux (S := A) :=
  { const_coeff := by
      intro s
      unfold sub_sec_aux
      by_cases hs : s = 0
      simp only [hs, Fin.isValue, MvPowerSeries.constantCoeff_X, IsNilpotent.zero]
      have hs' : s = 1 := by omega
      simp only [hs', Fin.isValue, MvPowerSeries.constantCoeff_X, IsNilpotent.zero]
    tendsto_zero := by
      simp only [Filter.cofinite_eq_bot, Filter.tendsto_bot] }

lemma SubstDomain_Add_aux₃ {A : Type*} [CommRing A] [UniformSpace A] : MvPowerSeries.SubstDomain (sub_fir (MvPowerSeries.X 0 + MvPowerSeries.X 1)) (S:= A) :=
  { const_coeff := by
      intro s
      unfold sub_fir
      by_cases hs : s = 0
      simp only [hs, Fin.isValue]
      rw [MvPowerSeries.subst_add SubstDomain_Add_aux₁, MvPowerSeries.subst_X SubstDomain_Add_aux₁, MvPowerSeries.subst_X SubstDomain_Add_aux₁]
      unfold sub_fir_aux
      simp only [Fin.isValue, map_add, MvPowerSeries.constantCoeff_X, add_zero,
        IsNilpotent.zero]
      have hs' : s = 1 := by omega
      simp only [hs', Fin.isValue, MvPowerSeries.constantCoeff_X, IsNilpotent.zero]
    tendsto_zero := by
      simp only [Fin.isValue, Filter.cofinite_eq_bot, Filter.tendsto_bot]
      }

lemma SubstDomain_Add_aux₄ {A : Type*} [CommRing A] [UniformSpace A] : MvPowerSeries.SubstDomain (sub_sec (MvPowerSeries.X 0 + MvPowerSeries.X 1)) (S:= A):=
  { const_coeff := by
      intro s
      unfold sub_sec
      by_cases hs : s = 0
      simp only [hs, Fin.isValue]
      simp only [Fin.isValue, MvPowerSeries.constantCoeff_X, IsNilpotent.zero]
      have hs' : s = 1 := by omega
      rw [MvPowerSeries.subst_add SubstDomain_Add_aux₂, MvPowerSeries.subst_X SubstDomain_Add_aux₂, MvPowerSeries.subst_X SubstDomain_Add_aux₂]
      unfold sub_sec_aux
      simp only [hs', Fin.isValue, map_add, MvPowerSeries.constantCoeff_X, add_zero,
        IsNilpotent.zero]
    tendsto_zero := by
      simp only [Fin.isValue, Filter.cofinite_eq_bot, Filter.tendsto_bot]
      }

noncomputable instance {A : Type*} [CommRing A] [UniformSpace A] : CommFormalGroup A where
  toFun := (X₀ + X₁)
  zero_coeff := by
    simp only [Fin.isValue, MvPolynomial.coe_add, MvPolynomial.coe_X,
    MvPowerSeries.coeff_zero_eq_constantCoeff, map_add, MvPowerSeries.constantCoeff_X, add_zero]
  lin_coeff_X := by
    sorry
  lin_coeff_Y := by
    sorry
  assoc := by
    rw [MvPowerSeries.subst_add SubstDomain_Add_aux₃, MvPowerSeries.subst_add SubstDomain_Add_aux₄,
      MvPowerSeries.subst_X SubstDomain_Add_aux₃, MvPowerSeries.subst_X SubstDomain_Add_aux₃,
      MvPowerSeries.subst_X SubstDomain_Add_aux₄, MvPowerSeries.subst_X SubstDomain_Add_aux₄]
    unfold sub_fir
    unfold sub_sec
    simp only [Fin.isValue]
    rw [MvPowerSeries.subst_add SubstDomain_Add_aux₁, MvPowerSeries.subst_add SubstDomain_Add_aux₂, MvPowerSeries.subst_X SubstDomain_Add_aux₁,
      MvPowerSeries.subst_X SubstDomain_Add_aux₁, MvPowerSeries.subst_X SubstDomain_Add_aux₂, MvPowerSeries.subst_X SubstDomain_Add_aux₂]
    unfold sub_fir_aux
    unfold sub_sec_aux
    simp only [Fin.isValue]
    ring
  comm := by sorry
    -- simp only [Fin.isValue, MvPolynomial.coe_add, MvPolynomial.coe_X]
    -- unfold MvPowerSeries.subst
    -- unfold MvPowerSeries.eval₂
    -- let f : MvPolynomial (Fin 2) A := (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2))
    -- have hf := Classical.epsilon_spec
    --   (p := fun (p : MvPolynomial (Fin 2) A) ↦ p = (f : MvPowerSeries (Fin 2) A)) ⟨f, rfl⟩
    -- rw [if_pos]
    -- conv =>
    --   rhs
    --   rw [←MvPolynomial.coe_X 0,← MvPolynomial.coe_X 1]
    --   norm_cast
    -- have epsilon_aux : (epsilon fun (p : MvPolynomial (Fin 2) A) ↦ ↑p = MvPolynomial.X (0 : Fin 2) (R := A) + MvPolynomial.X (1 : Fin 2) (R := A)) =
    --   MvPolynomial.X (0 : Fin 2) (R := A) + MvPolynomial.X (1 : Fin 2) (R := A) := by
    --   unfold f at hf
    --   norm_cast at hf
    -- rw [epsilon_aux]
    -- unfold sub_symm
    -- simp only [Fin.isValue, MvPolynomial.eval₂_add, MvPolynomial.eval₂_X]
    -- ring
    -- rw [←MvPolynomial.coe_X 0,← MvPolynomial.coe_X 1]
    -- norm_cast
    -- unfold f at hf
    -- norm_cast at hf

noncomputable instance MulFormalGroup {A : Type*} [CommRing A] : CommFormalGroup A where
  toFun := MvPolynomial.toMvPowerSeries (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) + MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2))
  zero_coeff := by simp only [Fin.isValue, MvPolynomial.coe_add, MvPolynomial.coe_X,
    MvPolynomial.coe_mul, MvPowerSeries.coeff_zero_eq_constantCoeff, map_add,
    MvPowerSeries.constantCoeff_X, add_zero, map_mul, mul_zero]
  lin_coeff_X := by
    sorry
  lin_coeff_Y := by
    sorry
  assoc := by
    let f : MvPolynomial (Fin 2) A := (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) + MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2))
    have hf := Classical.epsilon_spec
      (p := fun (p : MvPolynomial (Fin 2) A) ↦ p = (f : MvPowerSeries (Fin 2) A)) ⟨f, rfl⟩
    unfold MvPowerSeries.subst
    unfold eval₂
    rw [if_pos hf]
    rw [if_pos hf]
    unfold sub_fir
    unfold sub_sec
    have epsilon_aux : (epsilon fun (p : MvPolynomial (Fin 2) A) ↦ ↑p = (((MvPolynomial.X (0 : Fin 2) (R := A) + MvPolynomial.X 1 +
      MvPolynomial.X 0 * MvPolynomial.X 1)) : MvPolynomial (Fin 2) A)) = (MvPolynomial.X (0 : Fin 2) (R := A) + MvPolynomial.X (1 : Fin 2) (R := A) +
      MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) (R := A))  := by
      unfold f at hf
      norm_cast at hf
    have eq_aux : MvPowerSeries.subst sub_fir_aux ((MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) + MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) (R := A)) : MvPolynomial (Fin 2) A) (R := A)
      = MvPowerSeries.X (0 : Fin 3) + MvPowerSeries.X (1 : Fin 3) + MvPowerSeries.X (0 : Fin 3) * MvPowerSeries.X (1 : Fin 3) (R := A) := by
      unfold MvPowerSeries.subst
      unfold MvPowerSeries.eval₂
      rw [if_pos]
      unfold sub_fir_aux
      norm_cast
      rw [epsilon_aux]
      simp
      norm_cast
    have eq_aux' : MvPowerSeries.subst sub_sec_aux ((MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) + MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) (R := A)) : MvPolynomial (Fin 2) A) (R := A)
      = MvPowerSeries.X (1 : Fin 3) + MvPowerSeries.X (2 : Fin 3) + MvPowerSeries.X (1 : Fin 3) * MvPowerSeries.X (2 : Fin 3) (R := A) := by
      unfold MvPowerSeries.subst
      unfold MvPowerSeries.eval₂
      rw [if_pos]
      unfold sub_sec_aux
      norm_cast
      rw [epsilon_aux]
      simp
      norm_cast
    rw [eq_aux, eq_aux']
    norm_cast
    rw [epsilon_aux]
    simp only [Fin.isValue, MvPolynomial.eval₂_add, MvPolynomial.eval₂_X, MvPolynomial.eval₂_mul]
    ring
  comm := by
    simp only [Fin.isValue, MvPolynomial.coe_add, MvPolynomial.coe_X, MvPolynomial.coe_mul]
    unfold MvPowerSeries.subst
    unfold MvPowerSeries.eval₂
    let f : MvPolynomial (Fin 2) A := (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) + MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2))
    have hf := Classical.epsilon_spec
      (p := fun (p : MvPolynomial (Fin 2) A) ↦ p = (f : MvPowerSeries (Fin 2) A)) ⟨f, rfl⟩
    rw [if_pos]
    conv =>
      rhs
      rw [←MvPolynomial.coe_X 0,← MvPolynomial.coe_X 1]
      norm_cast
    have epsilon_aux : (epsilon fun (p : MvPolynomial (Fin 2) A) ↦ ↑p = (((MvPolynomial.X (0 : Fin 2) (R := A) + MvPolynomial.X 1 +
      MvPolynomial.X 0 * MvPolynomial.X 1)) : MvPolynomial (Fin 2) A)) = (MvPolynomial.X (0 : Fin 2) (R := A) + MvPolynomial.X (1 : Fin 2) (R := A) +
      MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) (R := A))  := by
      unfold f at hf
      norm_cast at hf
    rw [epsilon_aux]
    unfold sub_symm
    simp only [Fin.isValue, MvPolynomial.eval₂_add, MvPolynomial.eval₂_X, MvPolynomial.eval₂_mul]
    ring
    rw [←MvPolynomial.coe_X 0,← MvPolynomial.coe_X 1]
    norm_cast
    unfold f at hf
    norm_cast at hf

-- X ↦ X, Y ↦ a (X)
noncomputable def sub_sec' {A : Type*} [CommRing A] (a : PowerSeriesZeroConst A) : Fin 2 → PowerSeries A
  | ⟨0, _⟩ => PowerSeries.X
  | ⟨1, _⟩ => a.toFun
  -- cast a one variable power series to multivariable power series

noncomputable def subst_sec {A : Type*} [CommRing A] (p : PowerSeries A) : Fin 2 → PowerSeries A
  | ⟨0, _⟩ => PowerSeries.X
  | ⟨1, _⟩ => p

noncomputable def io_aux {A : Type*} [CommRing A] (F : FormalGroup A) : ℕ → A × (Polynomial A)
  | 0 => (0, 0)
  | 1 => (-1, -Polynomial.X)
  | n + 1 => (- (PowerSeries.coeff A (n + 1 : ℕ) (MvPowerSeries.subst (subst_sec (Polynomial.toPowerSeries (io_aux F n).2)) F.toFun)),
    (io_aux F n ).2 + Polynomial.monomial (n + 1) (- (PowerSeries.coeff A (n + 1 : ℕ) (MvPowerSeries.subst (subst_sec (Polynomial.toPowerSeries (io_aux F n).2)) F.toFun))))



theorem inv_exist {A : Type*} [CommRing A] {F : FormalGroup A} :
∃! (ι : PowerSeriesZeroConst A), PowerSeries.coeff  A 1 ι.toFun = - 1 ∧
MvPowerSeries.subst (sub_sec' ι) F.toFun  = 0 := by
  let ι : PowerSeriesZeroConst A :=
    { toFun :=
      PowerSeries.mk (fun n => (io_aux F n).1)
      zero_coeff := by
        unfold io_aux
        simp [PowerSeries.coeff_mk]
    }
  use ι
  constructor
  -- prove `ι` satisfies the property
  ·
    sorry
  -- prove the uniqueness of `ι`.
  ·
    sorry

/-- A formal Group law `F (X, Y)` over a ring `L` is a universal formal group law if and only if for every formal group law
  `G (X, Y)` over a ring `A` there is a unique ring homomorphism `ϕ L → A` such that `ϕ F (X, Y) = G (X, Y)`.-/
def IsUniversal {A : Type*} {L : Type*} [CommRing A] [CommRing L] (F : FormalGroup L) : Prop
:= ∀ (G : FormalGroup A), ∃! (ϕ : L →+* A), MvPowerSeries.map (Fin 2) ϕ F.toFun = G.toFun

/- The ring `L` is (up to isomorphism) uniquely determined by this definition.-/
-- todo : page 5

/- Existence of universal formal group laws.-/


end FormalGroups

namespace FormalGroupsWithCharZero

open TensorProduct MvPolynomial

/-! This section discuss a general method for constructing formal group law over
characteristic zero rings. -/

variable {A : Type*} [CommRing A] [CommSemiring A]

-- `A ⊗[ℤ] ℚ` is equivalent to `TensorProduct ℤ A ℚ`.

/-- `K = A ⊗[ℤ] ℚ`-/
def K := TensorProduct ℤ A ℚ
#check K

instance : CommRing (K (A := A)) := sorry


-- `--------------------------------------------------`
-- `ASK` why `instance : CommRing K` doesn't works
-- `--------------------------------------------------`


instance : CommRing (A ⊗[ℤ] ℚ) := sorry



/-- For every power series `f ∈ A⟦X⟧` with zero constant term, if `f(X) = u * X + ⋯`
  where `u ∈ Aˣ`, then there is `g ∈ A ⟦X⟧`, such that `f(g(X)) = g(f(X)) = X`. -/
theorem exist_subst_inv {u : Aˣ} {f : PowerSeriesZeroConst A}
  (hf : MvPowerSeries.coeff A (Finsupp.equivFunOnFinite.invFun 1) f.toFun = u) :
  ∃ (g :PowerSeriesZeroConst A), PowerSeries.subst (fun _ => f.toFun) g.toFun = PowerSeries.X
  ∧ PowerSeries.subst (fun _ => g.toFun) f.toFun = PowerSeries.X
  := sorry

theorem exist_subst_inv' {u : Aˣ} {f : PowerSeries A}
  (hf : PowerSeries.coeff A 1 f = u) :
  ∃ (g : PowerSeries  A), PowerSeries.subst f g = PowerSeries.X
  ∧ PowerSeries.subst g f = PowerSeries.X
  := sorry

-- todo: general case of the above theorem for `n` dimensional case.

/-- The following definition is used to get the substitution inverse of
  `f ∈ A⟦X⟧` with zero constant term and the linear coefficient is invertible element
  in ring `A`, with the equation `(subst_inv f hf) ∘ f = id`. -/
noncomputable def subst_inv {u : Aˣ} (f : PowerSeriesZeroConst A)
  (hf : MvPowerSeries.coeff A (Finsupp.equivFunOnFinite.invFun 1) f.toFun = u) :
  PowerSeriesZeroConst A := by
    choose g hg using exist_subst_inv hf
    exact g

noncomputable def subst_inv' {u : Aˣ} (f : PowerSeries A)
  (hf : PowerSeries.coeff A 1 f = u) :
  PowerSeries A:= by
    choose g hg using exist_subst_inv' hf
    exact g

-- Why the following doesn't work. `ask`

-- def subst_inv_prop {u : Aˣ} (f : PowerSeriesZeroConst A)
--   (hf : MvPowerSeries.coeff A (Finsupp.equivFunOnFinite.invFun 1) f.toFun = u) : Prop :=

--   Classical.choose_spec (exist_subst_inv hf)

def subst_inv_prop {u : Aˣ} (f : PowerSeriesZeroConst A)
  (hf : MvPowerSeries.coeff A (Finsupp.equivFunOnFinite.invFun 1) f.toFun = u) :=
  Classical.choose_spec (exist_subst_inv hf)

/--  `F_add_inv` is defined to be `F(X, Y) = f⁻¹(f(X) + f(Y))`, next we will prove it is a commutative formal group law.-/
noncomputable def F_add_inv (f : PowerSeriesZeroConst A)
  (hf : MvPowerSeries.coeff A (Finsupp.equivFunOnFinite.invFun 1) f.toFun = (1 : Aˣ))
  : MvPowerSeries (Fin 2) A :=
  MvPowerSeries.subst (fun _ => ((MvPowerSeries.subst (fun _ => X₀) f.toFun) + (MvPowerSeries.subst (fun _ => X₁) f.toFun))) (subst_inv f hf).toFun

  -- zero_coeff : MvPowerSeries.coeff A 0 toFun = 0
  -- lin_coeff_X : MvPowerSeries.coeff A (Finsupp.equivFunOnFinite.invFun coeff_X) toFun = 1
  -- lin_coeff_Y : MvPowerSeries.coeff A (Finsupp.equivFunOnFinite.invFun coeff_Y) toFun = 1
  -- assoc : @MvPowerSeries.subst _ A _ _ A _  _ (sub_fir toFun) toFun = @MvPowerSeries.subst _ A _ _ A _  _ (sub_sec toFun) toFun


theorem F_add_inv.zero_coeff (f : PowerSeriesZeroConst A)
  (hf : MvPowerSeries.coeff A (Finsupp.equivFunOnFinite.invFun 1) f.toFun = (1 : Aˣ))
  : MvPowerSeries.coeff A 0 (F_add_inv f hf) = 0 := sorry


theorem F_add_inv.lin_coeff_X (f : PowerSeriesZeroConst A)
  (hf : MvPowerSeries.coeff A (Finsupp.equivFunOnFinite.invFun 1) f.toFun = (1 : Aˣ))
  : MvPowerSeries.coeff A (Finsupp.equivFunOnFinite.invFun coeff_X) (F_add_inv f hf) = 1 := sorry


theorem F_add_inv.lin_coeff_Y (f : PowerSeriesZeroConst A)
  (hf : MvPowerSeries.coeff A (Finsupp.equivFunOnFinite.invFun 1) f.toFun = (1 : Aˣ))
  : MvPowerSeries.coeff A (Finsupp.equivFunOnFinite.invFun coeff_Y) (F_add_inv f hf) = 1 := sorry


theorem F_add_inv.assoc (f : PowerSeriesZeroConst A)
  (hf : MvPowerSeries.coeff A (Finsupp.equivFunOnFinite.invFun 1) f.toFun = (1 : Aˣ))
  : MvPowerSeries.subst  (sub_fir (F_add_inv f hf) ) (F_add_inv f hf)  = MvPowerSeries.subst (sub_sec (F_add_inv f hf) ) (F_add_inv f hf) := sorry


-- /-- `F(X, Y) = f⁻¹(f(X) + f(Y))` is a Formal Group Law. -/
-- -- noncomputable instance F_add_inv_FG (f : PowerSeriesZeroConst A)
-- --   (hf : MvPowerSeries.coeff A (Finsupp.equivFunOnFinite.invFun 1) f.toFun = (1 : Aˣ))
-- --   : FormalGroup A where
-- --   toFun := F_add_inv f hf
-- --   zero_coeff := F_add_inv.zero_coeff f hf
-- --   lin_coeff_X := F_add_inv.lin_coeff_X f hf
-- --   lin_coeff_Y := F_add_inv.lin_coeff_Y f hf
-- --   assoc := F_add_inv.assoc f hf



variable {σ : Type*} [Fintype σ]


/- `Definition 1` Truncate a multivariate power series to a polynomial of total degree < m -/
-- def truncate (m : ℕ) (f : MvPowerSeries σ A) : MvPolynomial σ A :=
--   ∑ d ∈ Finset.filter (fun d => d.sum (fun _ n => n) < m) f.support,
--     MvPolynomial.monomial d (coeff A d f)


/-- This is defined to be the constant map which send all element of `σ` to `m : ℕ`.-/
noncomputable def const_map (m : ℕ) : σ →₀ ℕ := Finsupp.equivFunOnFinite.invFun (fun _ => m)


/-- `Definition 2` Truncate a multivariate power series to a polynomial of total degree < m -/
noncomputable def truncateFun (m : ℕ) (f : MvPowerSeries σ A) : MvPolynomial σ A :=
  ∑ d ∈ Finset.filter (fun d => d.sum (fun _ n => n) < m) (Finset.Iic (const_map m)),
    MvPolynomial.monomial d (coeff A d f)

-- TODO : Imitate the prove in MvPowerSeries.Trunc to give the following prove
-- def truncate (m : ℕ): MvPowerSeries σ R →+ MvPolynomial σ R where
--   toFun := truncateFun m
--   map_zero' := by
--     classical
--     ext
--     sorry
--     -- simp [coeff_truncFun]
--   map_add' := by
--     classical
--     intros x y
--     ext m
--     sorry
--     -- simp only [coeff_truncFun, MvPolynomial.coeff_add, ite_add_ite, ← map_add, add_zero]

/-- A polynomial of total degree less than `m`,
  `F_m (X, Y) = X + Y + ∑ i, j ≥ 1, c_ij * X ^ i * Y ^ j` is called a commutative one
  dimensional formal group law chunk of order `m` if
  `F_m (X, F_m(Y, Z)) ≡ F_m (F_m (X, Y), Z) mod (degree m + 1)` and `F_m (X, Y) = F_m (Y, X)`.
  -/

def Chunk (m : ℕ) (F_m : MvPolynomial (Fin 2) A) {h : totalDegree F_m ≤ m}
  {hX : coeff (Finsupp.equivFunOnFinite.invFun coeff_X) F_m = 1}
  {hY : coeff (Finsupp.equivFunOnFinite.invFun coeff_Y) F_m = 1} : Prop :=
  truncateFun (m + 1) (@MvPowerSeries.subst _ A _ _ A _  _ (sub_fir F_m) F_m )
  = truncateFun (m + 1) (@MvPowerSeries.subst _ A _ _ A _  _ (sub_sec F_m) F_m)
  ∧ F_m = @MvPowerSeries.subst _ A _ _ A _  _ (sub_symm) F_m

/--Every one dimensional commutative formal group law chunk of order `m, 1 ≤ m`, comes from
  a one dimensional commutative formal group. Specificly, If `F_m (X, Y)` is a one
  dimensional commutative formal group law chunk over a ring `A`, then there is a
  one dimensional commutative formal group  `F(X, Y)` over `A` such that
  `F_m (X, Y) ≡ F (X, Y) mod (degree (m + 1))`.-/
theorem chunk_iff_exist_trunc {m : ℕ} {F_m : MvPolynomial (Fin 2) A}
  {h : totalDegree F_m ≤ m}
  {hX : coeff (Finsupp.equivFunOnFinite.invFun coeff_X) F_m = 1}
  {hY : coeff (Finsupp.equivFunOnFinite.invFun coeff_Y) F_m = 1}
  (h_chunk : @Chunk A _ _ m F_m h hX hY) :
  ∃ (F : FormalGroup A), truncateFun (m + 1) F.toFun = F_m  := sorry


/-- A function such that if `n = p ^ k`, where `p` is a prime number,
  then returns `p`, otherwise returns `1`.  -/
def primeBase : ℕ → ℕ
  | 0       => 1
  | 1       => 1  -- 1 is not a prime power
  | n       =>
    match Nat.primeFactorsList n with
    | []      => 1  -- Should never happen for n ≥ 1
    | p :: ps => if ps.all (· = p) then p else 1

#eval primeBase 1024

-- we will define a polynomial `C_n (X, Y) = (primeBase n)⁻¹ (- (X + Y) ^ n + X ^n + Y ^ n)`
-- `------------------------------------------------------------`
-- `how to express the coefficient of the polynomial is all integer`
-- `------------------------------------------------------------`

/-- Every one dimensional formal group law over a ring `A` is commutative if and only
  if `A` contains no elements `a ≠ 0` that are both torsion and nilpotent.-/
theorem comm_iff_NoTorsion_NoNilpotent {F : FormalGroup A} :
  (F.toFun = @MvPowerSeries.subst _ A _ _ A _  _ (sub_symm) F.toFun) ↔
  ¬ ∃ (a : A), ((a ≠ 0) ∧ (IsNilpotent a) ∧ (∃ (n : ℕ), n * a = 0)) := sorry


end FormalGroupsWithCharZero

namespace LubinTateFormalGroup

open FormalGroupsWithCharZero TensorProduct

variable {A : Type*} [CommRing A] [CharZero A] [IsDomain A] [IsDiscreteValuationRing A]
variable {ϖ : A} (h : Irreducible ϖ)

/- Let `A` be a nontrivial discrete valuation ring with residue field `k` of `q` elements.
  Choose a uniformizer `π`. Let `K` be the quotient field of `A`, namely `K = A ⊗ ℚ`, let
  `f(X) ∈ K⟦X⟧` be the power series
  `f(X) = X + π⁻¹X^q + π⁻²X^{q^2} + ⋯`
  and define `F(X,Y) = f⁻¹(f(X) + f(Y))`, `[a]_{F}(X) = f⁻¹(af(X))` for `a ∈ A`, then by the
  discusstion in the previous section, `F(X,Y)` is a formal group law, and `[a]_{F}(X)` defines
  a homomorphism of Formal Groups.-/

-- need nonarchimedean
instance : Fintype (IsLocalRing.ResidueField A):= sorry

def card_residue : ℕ := Fintype.card (IsLocalRing.ResidueField A)

-- `problem here ----------------------------------  ---------------- ASK`
-- noncomputable def LubinTate_f: PowerSeries (A ⊗[ℤ] ℚ) :=
--   fun e =>
--     if ∃ (n : ℕ), (e 0) = (card_residue : ℕ) ^ n then ϖ ^ (-n)
--     else 0


end LubinTateFormalGroup

namespace FunctionalEquationIntegralityLemma

open Pointwise FormalGroup

/- The basic ingredients in this section are `A ⊆ K, σ : K → K, 𝔞 ⊆ A, p, q, s₁, s₂ ⋯`,
  where `A` is a subring of `K`, `σ` is a ring homomorphism of `K`, which stablize `A`,
  `𝔞` is an ideal of `A`, `p` is a prime number and `q` is a power of `p`, `s_i` are
  elements of `K`. -/
variable {K : Type*} [CommRing K] {A : Subring K} [CommRing A] {𝔞 : Ideal A}
variable {p n q: ℕ} (hp : Nat.Prime p) (hn : n ≥ 1) (hq : q = p ^ n)
variable {σ : K →+* K}  (hs : ∀ (a : A), σ a ∈ A) {x : A} (hs_mod : ∀ (a : A), (⟨σ a, hs a⟩) ≡ a ^ q  [SMOD 𝔞])
variable (hp : (p : A) ∈ 𝔞) {s : ℕ → K} (hs_i : ∀ (i : ℕ), ∀ (a : 𝔞), (s i) * a ∈ A)

-- variable (ha : ∀ (r : ℕ), ∀ (b : K), b • 𝔞 ^ r ⊆ 𝔞 → (σ b) • (𝔞 ^ r) ⊆ 𝔞)
-- variable (ha : ∀ (r : ℕ), ∀ (b : K),  (∀ (x : (𝔞 ^ r)),  b * x ∈ (𝔞 ^ r)) → (∀ (x : (𝔞 ^ r)), (σ b) * x ∈ 𝔞 ^ r) )
-- Why the above does not work.
-- how to express this condition using the notation like `(s i) • 𝔞 ⊆ A`
-- Does this section need `[CharZero A]`
-- variable [CharZero ↥A] [Algebra (↥A) K]


-- `___________________________________ ASK ABOVE _____________________________________`

#check x • 𝔞 -- this need  `open Pointwise`
-- Alternative expression (hs_mod : ∀ (a : A), (⟨σ a, hs a⟩) - a ^ q ∈ 𝔞)
-- `⟨σ a, hs a⟩` use to express `σ a` together with the assumption `∀ (a : A), σ a ∈ A)`.


/- Given a function `g(X) = ∑_{i=0}^∞ b_i X^i` be a power series in one variable with
  coefficients in `A`, construct a new power series `f_g(X)` by means of the recursion
  formula.
  `f_g(X) = g(X) + ∑_{i=1}^∞ s_i σ_* ^ i f_g(X^{q^i})`
  the coefficient of `f_g(X)` can be expressed explicitly as follow,
  `f_g(X) = ∑_{i=0}^∞ d_i X^i`
  if `n = q ^ r * m` where `¬ q ∣ m`, then
  `d_n = b_n + s_1 σ (d_{n/q}) + ⋯ + s_r σ^r (d_{n/q^r})`.
  if `¬ q ∣ n`, then `d_n = b_n`. -/

-- variable {n : ℕ} (hq : q ≠ 1) (hqn : q ∣ n)

-- noncomputable def r : ℕ := multiplicity q n

-- `______________________________ ASK ________________________________`
-- `__________________ Why the coefficient here is in A __________________`
noncomputable def RecurFun_aux (g : PowerSeriesZeroConst A) (n : ℕ): K :=
  if multiplicity q n = 0 then MvPowerSeries.coeff A (Finsupp.equivFunOnFinite.invFun n) g.toFun
  else ∑ (i : Fin (multiplicity q n)), ((s i) * (σ^[i] (MvPowerSeries.coeff A (Finsupp.equivFunOnFinite.invFun (n / (q ^ (i : ℕ)))) g.toFun)))

-- need to change here, about the coefficient of the MvPowerSeries, in A or in K
noncomputable def RecurFun (g : PowerSeriesZeroConst A) : PowerSeries K :=
  fun coeff =>
    if multiplicity q n = 0 then MvPowerSeries.coeff A (Finsupp.equivFunOnFinite.invFun (coeff 0)) g.toFun
    else
      ∑ (i : Fin (multiplicity q n)), ((s i) * (σ^[i] (MvPowerSeries.coeff A (Finsupp.equivFunOnFinite.invFun (n / (q ^ (i : ℕ)))) g.toFun)))

/- Functional equation lemma.
  Let the notation defined as above, let `g(X) = ∑_{i=1}^∞ b_i X^i`, `g_bar (X) = ∑_{i=1}^∞ (b_bar i) X^i`.
  be two power series in one variable over `A`, and suppose that `b₁` is invertible in `A`. Then we have:
  (i) the power series F_g(X,Y)=f_g⁻¹(f_g(X)+f_g(Y)) has its coefficients in `A`.
  (ii) the power series `f_g⁻¹ (f_g_bar (X))` has its coefficient in `A`.
  (iii) if `h(X)=∑_{n=1}^∞ c_n X^n` is a power series with coefficients in `A`, then there is a
  power series `h^hat (X) = ∑_{n=1}^∞ c_n^hat X^n` with `c_n^hat ∈ A`, `n=1,2,…`, such that
  `f_g(h(X))=f_{h^hat}(X)`.
  (iv) if `α(X) ∈ A⟦X⟧, β(X) ∈ K⟦X⟧` are two power series, and `r ∈ ℕ, r ≥ 1`, then we have
  `α(X) ≡ β(X) [MOD 𝔞^r • A⟦X⟧] ↔ f_g(α(X)) ≡ f_g (β(X) [MOD 𝔞^r • A⟦X⟧])`.

  If `f_g(X)` and `f_{g_bar}(X)` are power series obtained by the recursion equation with
  everything the same except possibly `g(X) ≠ g_bar(X)`, then we shall say that
  `f_g(X)` and `f_{g_bar}(X)` satisfy the same type of functional equation.-/

/-- If `f_g(X)` and `f_{g_bar}(X)` are power series obtained by the recursion equation with
  everything the same except possibly `g(X) ≠ g_bar(X)`, then we shall say that
  `f_g(X)` and `f_{g_bar}(X)` satisfy the same type of functional equation. -/
def IsSameType (g : PowerSeriesZeroConst A) (g_bar : PowerSeriesZeroConst A) : Prop :=
  g.toFun ≠ g_bar.toFun ∧ (@RecurFun K _ A _ n q σ s g = @RecurFun K _ A _ n q σ s g_bar)

def Coeff_cast (g : PowerSeriesZeroConst A) :  PowerSeries K :=
  PowerSeries.map  (Subring.subtype A) g.toFun

noncomputable def F_g (g : PowerSeriesZeroConst A)
  (hg : PowerSeries.coeff K 1 (@RecurFun K _ A _ n q σ s g) = (1 : Kˣ))
  : MvPowerSeries (Fin 2) K :=
  PowerSeries.subst (((PowerSeries.subst X₀ (@RecurFun K _ A _ n q σ s g)) + (PowerSeries.subst X₁ (@RecurFun K _ A _ n q σ s g)))) ((FormalGroupsWithCharZero.subst_inv' (@RecurFun K _ A _ n q σ s g) hg))


theorem FunEqLem_one (g : PowerSeriesZeroConst A)
  (hg : PowerSeries.coeff K 1 (@RecurFun K _ A _ n q σ s g) = (1 : Kˣ)) :
  ∀ (n : (Fin 2) →₀ ℕ), MvPowerSeries.coeff K n (F_g g hg) ∈ A := sorry

noncomputable def inv_comp_bar (g : PowerSeriesZeroConst A) (g_bar : PowerSeriesZeroConst A)
  : PowerSeries K :=
  MvPowerSeries.subst (fun _ => (@RecurFun K _ A _ n q σ s g)) (@RecurFun K _ A _ n q σ s g_bar)

theorem FunEqLem_two (g : PowerSeriesZeroConst A) (g_bar : PowerSeriesZeroConst A) :
  ∀ (n' :ℕ), PowerSeries.coeff K n' (@inv_comp_bar K _ A _ n q σ s  g g_bar) ∈ A := sorry

theorem FunEqLem_three (g : PowerSeriesZeroConst A) (h : PowerSeriesZeroConst A)
  : ∃ (h_hat : PowerSeriesZeroConst A), PowerSeries.subst ((Coeff_cast h)) (@RecurFun K _ A _ n q σ s g) = (@RecurFun K _ A _ n q σ s h_hat) := sorry

-- Ideal.Quotient.mk

def coeff_mod (g : PowerSeries A) (I : Ideal A)
  : PowerSeries (A ⧸ (I)):=
  PowerSeries.map (Ideal.Quotient.mk (I)) g

def coeff_mod' (g : PowerSeries  A) (I : Ideal A) {r : ℕ}
  : PowerSeries (A ⧸ (I ^ r)):=
  PowerSeries.map (Ideal.Quotient.mk (I ^ r)) g
-- def coeff_mod' (g : PowerSeries  K) (I : Ideal A)
--   : PowerSeries  (K ⧸ (I)):=
--   PowerSeries.map  (Ideal.Quotient.mk (I)) g

-- theorem FunEqLem_four {α : MvPowerSeries A} {β : PowerSeries  K} {r : ℕ}
--   {hr : r ≥ 1}
--   : coeff_mod α (𝔞 ^ r) = coeff_mod β (𝔞 ^ r) := sorry


-- (hs_mod : ∀ (a : A), σ a - a ^ q ∈ 𝔞)
-- variable (hp_in : (p : ℤ) ∈ 𝔞)
--


end FunctionalEquationIntegralityLemma
