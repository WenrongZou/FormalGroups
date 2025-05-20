import FormalGroups.MvPowerSeries.Substitution
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.PartENat
import FormalGroups.MvPowerSeries.Trunc


namespace MvPowerSeries

variable {A : Type*} [CommRing A] (n : ℕ)


theorem trunc'_of_subst {A : Type*} [CommRing A] (f g: PowerSeries A)
  (hg : PowerSeries.constantCoeff A g = 0)
  : trunc' A ((Finsupp.single () n)) (PowerSeries.subst g f) = trunc' A (Finsupp.single () n)
    (PowerSeries.subst (trunc' A (Finsupp.single () n) g) f) := by
  ext m
  by_cases hm : m ≤ (Finsupp.single () n)
  have subst_aux : PowerSeries.SubstDomain g := by
    apply PowerSeries.substDomain_of_constantCoeff_nilpotent
    unfold PowerSeries.constantCoeff at hg
    simp [hg]
  have subst_aux' : PowerSeries.SubstDomain ((truncFun' (Finsupp.single () n) g) : PowerSeries A):= by
    apply PowerSeries.substDomain_of_constantCoeff_nilpotent
    unfold PowerSeries.constantCoeff at hg
    have aux : ((constantCoeff Unit A) ↑(truncFun' (Finsupp.single () n) g))
      = (constantCoeff Unit A) g := by
      calc
        _ = MvPolynomial.coeff 0 ((truncFun' (Finsupp.single () n) g)) := by
          exact rfl
        _ = coeff A 0 g := by
          rw [coeff_truncFun' (Finsupp.single () n) 0 ↑g]
          simp
        _ = (constantCoeff Unit A) g := by
          simp
    simp [aux, hg]
  unfold trunc'
  simp [coeff_truncFun']
  rw [if_pos hm, if_pos hm, PowerSeries.coeff_subst subst_aux, PowerSeries.coeff_subst subst_aux']
  congr
  funext d
  have aux : (coeff A m) (g ^ d) = (coeff A m) (↑(truncFun' (Finsupp.single () n) g) ^ d)
   := by
    rw [MvPowerSeries.coeff_pow, MvPowerSeries.coeff_pow]
    have eq_aux0 : ∀ l, l ∈ (Finset.range d).finsuppAntidiag m
      → ∏ i ∈ Finset.range d, (MvPowerSeries.coeff A (l i)) g =
      ∏ i ∈ Finset.range d, (MvPowerSeries.coeff A (l i)) ↑(truncFun' (Finsupp.single () n) g) := by
      intro l hl
      congr
      funext i
      have le_aux : l i ≤ m := by
        simp at hl
        obtain ⟨h1, h2⟩ := hl
        have : ∀ j, (j ∈ (Finset.range d)) → l j ≥ 0 := by
          intro j hj
          norm_num
        by_contra hc
        simp at hc
        by_cases hi : i ∈ Finset.range d
        rw [←Finset.sum_erase_add _ _ hi] at h1
        have ge_aux : ∑ x ∈ (Finset.range d).erase i, l x ≥ 0 := by
          apply Finset.sum_nonneg
          intro j hj
          simp at hj
          obtain ⟨hj1, hj2⟩ := hj
          obtain this := this j (by simp [hj2])
          exact this
        have ge_aux2 : m ≥ l i := by
          rw [←h1]
          calc
            _ ≥ 0 + l i := by
              simp only [zero_add, ge_iff_le, le_add_iff_nonneg_left, zero_le]
            _ = l i := by simp
        exact hc ge_aux2
        simp at hi
        have li_eq_zero : l i = 0 := by
          by_contra hi'
          have supp_l : i ∈ l.support := by
            simp [hi']
          have aux : i ∈ Finset.range d := by
            exact h2 supp_l
          simp at aux
          obtain aux' := (lt_iff_not_ge i d).mp aux
          exact aux' hi
        rw [li_eq_zero] at hc
        apply hc
        simp
      have le_aux' : l i ≤  (Finsupp.single () n) := by
        calc
          _ ≤ m := le_aux
          _ ≤  (Finsupp.single () n)  := by
            exact hm
      have eq_aux : MvPolynomial.coeff (l i) (truncFun' (Finsupp.single () n) g)
        = (coeff A (l i)) ↑(truncFun' (Finsupp.single () n) g) := by
        simp
      have eq_aux' : (coeff A (l i)) ↑(truncFun' (Finsupp.single () n) g)
        = MvPolynomial.coeff (l i) (trunc' A (Finsupp.single () n) g) := by
          unfold trunc'
          simp
      rw [eq_aux']
      rw [MvPowerSeries.coeff_trunc' _ _ g, if_pos le_aux']
    apply Finset.sum_congr
    simp
    intro x hx
    exact eq_aux0 x hx
  rw [aux]
  unfold trunc'
  simp [coeff_truncFun']
  rw [if_neg hm, if_neg hm]


theorem eq_of_forall_trunc'_eq {σ : Type*} (f g: MvPowerSeries σ A)
  (h : ∀ n, trunc' A n f = trunc' A n g) : f = g := by
  ext n
  obtain hn := h n
  have eq_aux : truncFun' n f = truncFun' n g := by
    unfold trunc' at hn
    exact hn
  calc
    _ = (truncFun' n f).coeff n := by
      simp [coeff_truncFun']
    _ = (truncFun' n g).coeff n := by
      rw [eq_aux]
    _ = _ := by
      simp [coeff_truncFun']
  -- trunc i need m > n, m ≥ n

end MvPowerSeries


namespace PowerSeries

variable {A : Type*} [CommRing A] (n : ℕ)

noncomputable def truncFun (f : PowerSeries A) : Polynomial A :=
  ∑ m ∈ Finset.Iio n, Polynomial.monomial m (PowerSeries.coeff A m f)


theorem coeff_truncFun (m : ℕ) (f : PowerSeries A) :
    (truncFun n f).coeff m = if m < n then PowerSeries.coeff A m f else 0 := by
  classical
  unfold truncFun
  by_cases hm : m < n
  simp [hm]
  have sum_single : ∑ b ∈ Finset.Iio n, ((Polynomial.monomial b) ((PowerSeries.coeff A b) f)).coeff m = ((Polynomial.monomial m) ((PowerSeries.coeff A m) f)).coeff m := by
    apply Finset.sum_eq_single_of_mem
    simp [hm]
    intro b hb hb'
    exact (Polynomial.coeff_monomial_of_ne _ hb')
  rw [sum_single]
  simp
  simp [hm]
  refine (Finset.sum_eq_zero ?_)
  intro b hb
  simp at hm
  simp at hb
  apply Polynomial.coeff_monomial_of_ne
  linarith

noncomputable def truncFun' (f : PowerSeries A) : Polynomial A :=
  ∑ m ∈ Finset.Iic n, Polynomial.monomial m (PowerSeries.coeff A m f)

theorem coeff_truncFun' (m : ℕ) (f : PowerSeries A) :
    (truncFun' n f).coeff m = if m ≤ n then PowerSeries.coeff A m f else 0 := by
  classical
  unfold truncFun'
  by_cases hm : m ≤ n
  simp [hm]
  have sum_single : ∑ b ∈ Finset.Iic n, ((Polynomial.monomial b) ((PowerSeries.coeff A b) f)).coeff m = ((Polynomial.monomial m) ((PowerSeries.coeff A m) f)).coeff m := by
    apply Finset.sum_eq_single_of_mem
    simp [hm]
    intro b hb hb'
    exact (Polynomial.coeff_monomial_of_ne _ hb')
  rw [sum_single]
  simp
  simp [hm]
  refine (Finset.sum_eq_zero ?_)
  intro b hb
  simp at hm
  simp at hb
  apply Polynomial.coeff_monomial_of_ne
  linarith


noncomputable def trunc : PowerSeries A →+ Polynomial A where
  toFun := truncFun n
  map_zero' := by
    classical
    ext x
    simp [coeff_truncFun]
  map_add' := by
    classical
    intros x y
    ext m
    simp only [coeff_truncFun, Polynomial.coeff_add, ite_add_ite, ← map_add, add_zero]

noncomputable def trunc' : PowerSeries A →+ Polynomial A where
  toFun := truncFun' n
  map_zero' := by
    classical
    ext x
    simp [coeff_truncFun']
  map_add' := by
    classical
    intros x y
    ext m
    simp only [coeff_truncFun', Polynomial.coeff_add, ite_add_ite, ← map_add, add_zero]

theorem coeff_trunc m (φ : PowerSeries A) :
    (trunc n φ).coeff m = if m < n then coeff A m φ else 0 := by
  classical simp [trunc, coeff_truncFun]


theorem eq_of_forall_trunc_eq (f g: PowerSeries A)
  (h : ∀ (n : ℕ), trunc n f = trunc n g) : f = g := by
  ext n
  obtain hn := h (n + 1)
  have eq_aux : truncFun (n + 1) f = truncFun (n + 1) g := by
    unfold trunc at hn
    exact hn
  calc
    _ = (truncFun (n + 1) f).coeff n := by
      simp [coeff_truncFun]
    _ = (truncFun (n + 1) g).coeff n := by
      rw [eq_aux]
    _ = _ := by
      simp [coeff_truncFun]

theorem eq_of_forall_trunc'_eq (f g: PowerSeries A)
  (h : ∀ (n : ℕ), trunc' n f = trunc' n g) : f = g := by
  ext n
  obtain hn := h n
  have eq_aux : truncFun' n f = truncFun' n g := by
    unfold trunc' at hn
    simp at hn
    exact hn
  calc
    _ = (truncFun' n f).coeff n := by
      simp [coeff_truncFun']
    _ = (truncFun' n g).coeff n := by
      rw [eq_aux]
    _ = _ := by
      simp [coeff_truncFun']

variable {R : Type*} [CommRing R] [Algebra A R]
  {τ : Type*} -- [DecidableEq τ]
  {S : Type*} [CommRing S]

theorem coeff_subst' [Algebra R S] (a : PowerSeries S) (ha : SubstDomain a) (f : PowerSeries R) (n : ℕ):
    PowerSeries.coeff S n (subst a f) =
      finsum (fun (d : ℕ) ↦
        (coeff R d f) • (PowerSeries.coeff S n (a ^ d))) := by
  erw [MvPowerSeries.coeff_subst ha.const f (Finsupp.single () n) ]
  rw [← finsum_comp_equiv (Finsupp.LinearEquiv.finsuppUnique ℕ ℕ Unit).toEquiv.symm]
  apply finsum_congr
  intro d
  congr
  · ext; simp
  · simp

-- write the lemma below

theorem trunc'_of_subst {A : Type*} [CommRing A] (f g: PowerSeries A)
  (hg : PowerSeries.constantCoeff A g = 0)
  : trunc' n (subst g f) = trunc' n (subst (trunc' n g) f) := by
  -- calc
  --   _  = MvPowerSeries.trunc' A ((Finsupp.single () n)) (PowerSeries.subst g f) := by sorry
  --   _ = MvPowerSeries.trunc' A (Finsupp.single () n) (PowerSeries.subst (MvPowerSeries.trunc' A (Finsupp.single () n) g) f) := by sorry
  --   _ = _ := by sorry
  sorry

theorem trunc'_of_succ {A : Type*} [CommRing A] (f: PowerSeries A) (n : ℕ) :
  trunc' (n + 1) f = trunc' n f + Polynomial.monomial (n + 1) (PowerSeries.coeff A (n + 1) f) := by
  unfold trunc'
  simp
  unfold truncFun'
  have finset_aux : Finset.Iic (n + 1) = insert (n + 1) (Finset.Iic (n)) := by
    refine (Finset.erase_eq_iff_eq_insert ?_ ?_).mp ?_
    all_goals simp
    exact rfl
  rw [finset_aux]
  simp [Finset.sum_insert]
  conv =>
    lhs
    rw [add_comm]


-- under namespace PowerSeries
theorem trunc_of_subst {A : Type*} [CommRing A] (f g: PowerSeries A)
  (hg : PowerSeries.constantCoeff A g = 0)
  : trunc n (subst g f) = trunc n (subst (trunc n g) f) := by
  ext m
  by_cases hm : m < n
  have subst_aux : PowerSeries.SubstDomain g := by
    apply PowerSeries.substDomain_of_constantCoeff_nilpotent
    unfold PowerSeries.constantCoeff at hg
    simp [hg]
  have subst_aux' : PowerSeries.SubstDomain ((truncFun n g) : PowerSeries A):= by
    apply PowerSeries.substDomain_of_constantCoeff_nilpotent
    unfold PowerSeries.constantCoeff at hg
    have aux : ((MvPowerSeries.constantCoeff Unit A) ↑(truncFun n g))
      = (MvPowerSeries.constantCoeff Unit A) g := by
      calc
        _ = MvPolynomial.coeff 0 ((MvPowerSeries.truncFun (Finsupp.single () n) g)) := by
          have aux' : (MvPowerSeries.constantCoeff Unit A) ↑(truncFun n g)
            = (MvPowerSeries.constantCoeff Unit A) (MvPowerSeries.truncFun (Finsupp.single () n) g) := by
            congr
            ext d
            have this : (coeff A d) ↑(MvPowerSeries.truncFun (Finsupp.single () n) g) = (MvPowerSeries.coeff A (Finsupp.single () d)) (MvPowerSeries.truncFun (Finsupp.single () n) g) := by
              norm_cast
            by_cases hd : d < n
            simp [coeff_truncFun, if_pos hd]
            rw [this]
            have lt_aux : (Finsupp.single () d) < (Finsupp.single () n) := by
              rw [Finsupp.lt_def]
              constructor
              simp
              linarith
              simp [hd]
            simp [MvPowerSeries.coeff_truncFun]
            rw [if_pos lt_aux]
            exact rfl
            simp [coeff_truncFun, if_neg hd]
            rw [this]
            have lt_aux : ¬ (Finsupp.single () d) < (Finsupp.single () n) := by
              by_contra hc
              rw [Finsupp.lt_def] at hc
              obtain ⟨hc1, hc2⟩ := hc
              simp at hc1 hd
              have neqd : n = d := by linarith
              rw [neqd] at hc2
              simp at hc2
            simp [MvPowerSeries.coeff_truncFun]
            rw [if_neg lt_aux]
          rw [aux']
          exact rfl
        _ = MvPowerSeries.coeff A 0 g := by
          rw [MvPowerSeries.coeff_truncFun (Finsupp.single () n) 0 ↑g]
          simp
          intro h
          exact Eq.symm hg
        _ = (MvPowerSeries.constantCoeff Unit A) g := by
          simp
    simp [aux, hg]
  unfold trunc
  simp [coeff_truncFun]
  rw [if_pos hm, if_pos hm, coeff_subst' g subst_aux, coeff_subst' ((truncFun n g)  : PowerSeries A) subst_aux']
  congr
  funext d
  have aux : (coeff A m) (g ^ d) = (coeff A m) (↑(truncFun n g) ^ d) := by
    rw [coeff_pow, coeff_pow]
    have eq_aux0 : ∀ l, l ∈ (Finset.range d).finsuppAntidiag m
      → ∏ i ∈ Finset.range d, (PowerSeries.coeff A (l i)) g =
      ∏ i ∈ Finset.range d, (PowerSeries.coeff A (l i)) ↑(truncFun n g) := by
      intro l hl
      congr
      funext i
      have le_aux : l i ≤ m := by
        simp at hl
        obtain ⟨h1, h2⟩ := hl
        have : ∀ j, (j ∈ (Finset.range d)) → l j ≥ 0 := by
          intro j hj
          norm_num
        by_contra hc
        simp at hc
        by_cases hi : i ∈ Finset.range d
        rw [←Finset.sum_erase_add _ _ hi] at h1
        have ge_aux : ∑ x ∈ (Finset.range d).erase i, l x ≥ 0 := by
          apply Finset.sum_nonneg
          intro j hj
          simp at hj
          obtain ⟨hj1, hj2⟩ := hj
          obtain this := this j (by simp [hj2])
          exact this
        have ge_aux2 : m ≥ l i := by
          rw [←h1]
          calc
            _ ≥ 0 + l i := by
              simp only [zero_add, ge_iff_le, le_add_iff_nonneg_left, zero_le]
            _ = l i := by simp
        linarith
        simp at hi
        have li_eq_zero : l i = 0 := by
          by_contra hi'
          have supp_l : i ∈ l.support := by
            simp [hi']
          have aux : i ∈ Finset.range d := by
            exact h2 supp_l
          simp at aux
          obtain aux' := (lt_iff_not_ge i d).mp aux
          exact aux' hi
        rw [li_eq_zero] at hc
        linarith
      have le_aux' : l i < n := by
        linarith
      have eq_aux : Polynomial.coeff (truncFun n g) (l i)
        = (coeff A (l i)) ↑(truncFun n g) := by
        simp
      have eq_aux' : (coeff A (l i)) ↑(truncFun n g)
        = Polynomial.coeff (trunc n g) (l i) := by
          unfold trunc
          simp
      rw [eq_aux']
      rw [PowerSeries.coeff_trunc _ _ g, if_pos le_aux']
    apply Finset.sum_congr
    simp
    intro x hx
    exact eq_aux0 x hx
  rw [aux]
  unfold trunc
  simp [coeff_truncFun]
  rw [if_neg hm, if_neg hm]

end PowerSeries
