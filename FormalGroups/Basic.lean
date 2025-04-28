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

open Classical MvPowerSeries PowerSeries

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
  | ⟨0, _⟩ => MvPowerSeries.X (1 : Fin 2)
  | ⟨1, _⟩ => MvPowerSeries.X (0 : Fin 2)



#check subst (sub_fir G) G
#check subst (sub_sec G) G


/-- A structure for a 1-dimensional formal group law over `R`-/
structure FormalGroup (A : Type*) [CommRing A]  where
  toFun : MvPowerSeries (Fin 2) A
  zero_coeff : MvPowerSeries.coeff A 0 toFun = 0
  lin_coeff_X : MvPowerSeries.coeff A (Finsupp.single 0 1) toFun = 1
  lin_coeff_Y : MvPowerSeries.coeff A (Finsupp.single 1 1) toFun = 1
  assoc : MvPowerSeries.subst (sub_fir toFun) toFun = MvPowerSeries.subst (sub_sec toFun) toFun
  --  Associativity of the Formal Group : `F (F (X, Y), Z) = F (X, F (Y, Z))`.

structure CommFormalGroup (A : Type*) [CommRing A] extends FormalGroup A where
  comm : toFun = MvPowerSeries.subst (sub_symm) toFun
-- Commutativity F (X, Y) = F (Y, X)


-- Definition of homomorphism between Formal Group Law

/-- Formal Power Series with zero constant term. -/
structure PowerSeriesZeroConst (A : Type*) [CommRing A] where
  toFun : PowerSeries A
  zero_coeff : PowerSeries.coeff A 0 toFun = 0

theorem SubstDomain_ZeroConst {A : Type*} [CommRing A] (α : PowerSeriesZeroConst A) :
  SubstDomain α.toFun :=
  {
    const_coeff := by
      obtain h1 := α.zero_coeff
      unfold PowerSeries.coeff at h1
      simp only [Finsupp.single_zero, MvPowerSeries.coeff_zero_eq_constantCoeff] at h1
      rw [h1]
      simp
  }


-- a (F (X, Y))
-- noncomputable def sub_hom₁ {A : Type*} [CommRing A]  (F : MvPowerSeries (Fin 2) A): MvPowerSeries (Fin 2) A
--   | ⟨0, _⟩ => F

-- G (a (X), a (Y))
noncomputable def sub_hom₂ {A : Type*} [CommRing A] (a : PowerSeries  A):
  Fin 2 → MvPowerSeries (Fin 2) A
  | ⟨0, _⟩ => PowerSeries.subst  ((MvPowerSeries.X (0 : Fin 2))) a
  | ⟨1, _⟩ => PowerSeries.subst  ((MvPowerSeries.X (1 : Fin 2))) a

/-- Let `G₁, G₂` be two formal group laws over `CommRing A`. A homomorphism (over `A`)
  `F (X, Y) → G (X, Y)` is a power series `α(X) = b₁ * X + b₂ * X ^ 2 + ⋯` with coefficients
  in `A` without constant term such that `α(F (X, Y)) = G (α (X), α (Y))`. -/
structure FormalGroupHom {A : Type*} [CommRing A] (G₁ G₂ : FormalGroup A) extends
  PowerSeriesZeroConst A where
  hom : PowerSeries.subst (G₁.toFun) toFun = MvPowerSeries.subst (R := A) (sub_hom₂ toFun) G₂.toFun
  --         a (F (X, Y))                    =          G (a (X), a (Y))

namespace FormalGroups

open MvPowerSeries

/-- The homomorphism `α(X) : F (X, Y) → G (X, Y)` is an isomorphism if there exists a
  homomorphism `β(X) : G (X, Y) → F (X, Y)` such that `α(β(X)) = X = β(α(X))`. -/

def IsIso {A : Type*} [CommRing A] {G₁ G₂ : FormalGroup A} (α : FormalGroupHom G₁ G₂) : Prop :=
  ∃ (β : FormalGroupHom G₂ G₁), PowerSeries.subst β.toFun α.toFun = PowerSeries.X
  ∧ PowerSeries.subst α.toFun β.toFun = PowerSeries.X
-- define it to be Equiv.

/-- An isomorphism `α(X) : F (X, Y) → G (X, Y)`, `α(X) = b₁ * X + b₂ * X ^ 2 + ⋯` is called strict isomorphism if `b₁ = 1`.-/
def IsStrictIso {A : Type*} [CommRing A] {G₁ G₂ : FormalGroup A} {α : FormalGroupHom G₁ G₂} : Prop := IsIso α
  ∧ coeff A (Finsupp.equivFunOnFinite.invFun 1) α.toFun = 1


/-- The homomorphism `α(X) : F (X, Y) → G (X, Y)` is an isomorphism if and only if
  `b₁ ∈ U(A)`, the group units of `A`.-/


-- prove the following theorem by inductively construct the coefficient
theorem PowerSeries_subst_inv {A : Type*} [CommRing A] (f : PowerSeries A)
  (h : IsUnit (PowerSeries.coeff A 1 f)) (hc : PowerSeries.coeff A 0 f = 0): ∃ (g : PowerSeries A),
  PowerSeries.subst f g = PowerSeries.X
  ∧ PowerSeries.subst g f = PowerSeries.X ∧ PowerSeries.coeff A 0 g = 0 := sorry


theorem isIso_iff_UnitCoeff {A : Type*} [CommRing A] {G₁ G₂ : FormalGroup A} (α : FormalGroupHom G₁ G₂) :
  IsIso α ↔ IsUnit (PowerSeries.coeff A 1 α.toFun) := by
  constructor
  -- forward direction
  · intro h
    unfold IsIso at h
    obtain ⟨β, h₁, h₂⟩ := h
    obtain coeff_eq := PowerSeries.ext_iff.mp h₁ 1
    simp at coeff_eq
    have subdomain_a : SubstDomain α.toFun := by
      apply SubstDomain_ZeroConst
    have subdomain_b : SubstDomain β.toFun := by
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
            exact β.zero_coeff
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
    obtain ⟨g, hb1, hb2, hb3⟩ := PowerSeries_subst_inv α.toFun h (by simp [α.zero_coeff])
    let β : FormalGroupHom G₂ G₁ :=
    {
      toFun := g
      zero_coeff := hb3
      hom := by
        simp
        have eq_aux : G₂.toFun =
          MvPowerSeries.subst (sub_hom₂ (PowerSeries.subst g α.toFun)) G₂.toFun := by
          rw [hb2]
          unfold sub_hom₂
          rw [PowerSeries.subst_X, PowerSeries.subst_X]

          sorry
          refine PowerSeries.substDomain_of_constantCoeff_zero ?_
          simp
          refine PowerSeries.substDomain_of_constantCoeff_zero ?_
          simp

        have eq_aux' : G₂.toFun
          = PowerSeries.subst (subst (sub_hom₂ g) G₁.toFun) α.toFun := by
          rw [eq_aux]

          sorry
        rw [eq_aux']
        -- maybe need to change f here to satisfies some property that f ∈ PowerSeries.SubstDomain
        have subst_aux : ∀ (f : MvPowerSeries (Fin 2) A), PowerSeries.subst (PowerSeries.subst f α.toFun) g = f := by
          intro f
          sorry
        exact (subst_aux (MvPowerSeries.subst (sub_hom₂ g) G₁.toFun))
    }
    use β


#check FormalGroup R

-- change toFun to be MvPowerSeries
-- use subst_add

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
  toFun := (MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2))
  zero_coeff := by
    simp only [Fin.isValue, MvPolynomial.coe_add, MvPolynomial.coe_X,
    MvPowerSeries.coeff_zero_eq_constantCoeff, map_add, MvPowerSeries.constantCoeff_X, add_zero]
  lin_coeff_X := by
    simp only [Fin.isValue, map_add, coeff_index_single_self_X, add_right_eq_self]
    rw [MvPowerSeries.coeff_index_single_X]
    simp only [Fin.isValue, zero_ne_one, ↓reduceIte]
  lin_coeff_Y := by
    simp only [Fin.isValue, map_add, coeff_index_single_self_X, add_right_eq_self]
    rw [MvPowerSeries.coeff_index_single_X]
    simp only [Fin.isValue, one_ne_zero, ↓reduceIte, zero_add]
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
  comm := by
    simp only [Fin.isValue, MvPolynomial.coe_add, MvPolynomial.coe_X]
    unfold MvPowerSeries.subst
    unfold MvPowerSeries.eval₂
    let f : MvPolynomial (Fin 2) A := (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2))
    have hf := Classical.epsilon_spec
      (p := fun (p : MvPolynomial (Fin 2) A) ↦ p = (f : MvPowerSeries (Fin 2) A)) ⟨f, rfl⟩
    rw [if_pos]
    conv =>
      rhs
      rw [←MvPolynomial.coe_X 0,← MvPolynomial.coe_X 1]
      norm_cast
    have epsilon_aux : (epsilon fun (p : MvPolynomial (Fin 2) A) ↦ ↑p = MvPolynomial.X (0 : Fin 2) (R := A) + MvPolynomial.X (1 : Fin 2) (R := A)) =
      MvPolynomial.X (0 : Fin 2) (R := A) + MvPolynomial.X (1 : Fin 2) (R := A) := by
      unfold f at hf
      norm_cast at hf
    rw [epsilon_aux]
    unfold sub_symm
    simp only [Fin.isValue, MvPolynomial.eval₂_add, MvPolynomial.eval₂_X]
    ring
    rw [←MvPolynomial.coe_X 0,← MvPolynomial.coe_X 1]
    norm_cast
    unfold f at hf
    norm_cast at hf

noncomputable instance MulFormalGroup {A : Type*} [CommRing A] : CommFormalGroup A where
  toFun := MvPolynomial.toMvPowerSeries (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) + MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2))
  zero_coeff := by simp only [Fin.isValue, MvPolynomial.coe_add, MvPolynomial.coe_X,
    MvPolynomial.coe_mul, MvPowerSeries.coeff_zero_eq_constantCoeff, map_add,
    MvPowerSeries.constantCoeff_X, add_zero, map_mul, mul_zero]
  lin_coeff_X := by
    rw [MvPolynomial.coeff_coe, MvPolynomial.coeff_add, MvPolynomial.coeff_add]
    calc
      _ = (1 : A) + (0 : A) + (0 : A) := by
        rw [MvPolynomial.coeff_mul]
        simp only [Fin.isValue, MvPolynomial.coeff_single_X, and_self, ↓reduceIte, one_ne_zero,
          and_false, add_zero, Finsupp.antidiagonal_single, Finset.sum_map,
          Function.Embedding.coe_prodMap, Function.Embedding.coeFn_mk, Prod.map_fst, and_true,
          Prod.map_snd, mul_zero, Finset.sum_const_zero]
      _ = (1 : A) := by norm_num
  lin_coeff_Y := by
    rw [MvPolynomial.coeff_coe, MvPolynomial.coeff_add, MvPolynomial.coeff_add]
    calc
      _ = (0 : A) + (1 : A) + (0 : A) := by
          rw [MvPolynomial.coeff_mul]
          simp only [Fin.isValue, MvPolynomial.coeff_single_X, zero_ne_one, and_false, ↓reduceIte,
            and_self, zero_add, Finsupp.antidiagonal_single, Finset.sum_map,
            Function.Embedding.coe_prodMap, Function.Embedding.coeFn_mk, Prod.map_fst, Prod.map_snd,
            and_true, mul_ite, mul_one, mul_zero, ite_self, Finset.sum_const_zero, add_zero]
        _ = (1 : A) := by norm_num
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
        simp only [coeff_mk]
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
  MvPowerSeries.subst (fun _ => ((MvPowerSeries.subst (fun _ => MvPowerSeries.X (0 : Fin 2)) f.toFun) + (MvPowerSeries.subst (fun _ => MvPowerSeries.X (1 : Fin 2)) f.toFun))) (subst_inv f hf).toFun

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
  PowerSeries.subst (((PowerSeries.subst (MvPowerSeries.X (0 : Fin 2))  (@RecurFun K _ A _ n q σ s g)) + (PowerSeries.subst (MvPowerSeries.X (1 : Fin 2)) (@RecurFun K _ A _ n q σ s g)))) ((FormalGroupsWithCharZero.subst_inv' (@RecurFun K _ A _ n q σ s g) hg))


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


end FunctionalEquationIntegralityLemma
