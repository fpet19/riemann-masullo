module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Comparison and cancellation for a jump energy

These are the two form arguments in the zero-width, fractional-order estimate
for the geometric blocks of Theorem 10.4.3.5(2), pp. 471–473. The pair measure
is arbitrary, so the proofs do not depend on a construction of the Bessel kernel.
-/

public noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace RiemannMasullo

variable {X : Type*} [MeasurableSpace X]

/-- The real part of a mass and jump pairing. The measure on pairs includes the jump kernel. -/
def jumpPairing (μ : Measure X) (ν : Measure (X × X)) (f g : X → ℂ) : ℝ :=
  (∫ x, (conj (f x) * g x).re ∂μ) +
    (1 / 2) * ∫ p, (conj (f p.1 - f p.2) * (g p.1 - g p.2)).re ∂ν

private theorem jumpPairing_ofReal (μ : Measure X) (ν : Measure (X × X))
    (f g : X → ℝ) :
    jumpPairing μ ν (fun x ↦ (f x : ℂ)) (fun x ↦ (g x : ℂ)) =
      (∫ x, f x * g x ∂μ) + (1 / 2) * ∫ p, (f p.1 - f p.2) * (g p.1 - g p.2) ∂ν := by
  simp [jumpPairing, Complex.mul_re, Complex.sub_re, Complex.sub_im]

private theorem jumpPairing_posPart_sq_le (a b : ℝ) :
    (max a 0 - max b 0) ^ 2 ≤ (a - b) * (max a 0 - max b 0) := by
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb
  · simp [max_eq_right ha, max_eq_right hb]
  · simp only [max_eq_right ha, max_eq_left hb]
    nlinarith only [mul_nonneg (neg_nonneg.mpr ha) hb]
  · simp only [max_eq_left ha, max_eq_right hb]
    nlinarith only [mul_nonneg ha (neg_nonneg.mpr hb)]
  · simp [max_eq_left ha, max_eq_left hb, pow_two]

/-- A real function with zero pairing against its positive part is nonpositive almost
everywhere for the mass measure. Apply this to the difference of two interpolants. -/
theorem ae_nonpos_of_jumpPairing_posPart_eq_zero (μ : Measure X) (ν : Measure (X × X))
    (u : X → ℝ)
    (hMass : Integrable (fun x ↦ u x * max (u x) 0) μ)
    (horth : jumpPairing μ ν (fun x ↦ (u x : ℂ)) (fun x ↦ ((max (u x) 0 : ℝ) : ℂ)) = 0) :
    ∀ᵐ x ∂μ, u x ≤ 0 := by
  let v (x : X) := max (u x) 0
  have hm (x : X) : u x * v x = v x ^ 2 := by
    rcases le_total (u x) 0 with hx | hx
    · simp [v, max_eq_right hx]
    · simp [v, max_eq_left hx, pow_two]
  have hv : Integrable (fun x ↦ v x ^ 2) μ := hMass.congr (ae_of_all _ hm)
  have hj : 0 ≤ ∫ p, (u p.1 - u p.2) * (v p.1 - v p.2) ∂ν :=
    integral_nonneg fun p ↦ (sq_nonneg _).trans (jumpPairing_posPart_sq_le (u p.1) (u p.2))
  rw [jumpPairing_ofReal, integral_congr_ae (ae_of_all _ hm)] at horth
  have hzero : (∫ x, v x ^ 2 ∂μ) = 0 := by
    have hnonneg : 0 ≤ ∫ x, v x ^ 2 ∂μ := integral_nonneg fun _ ↦ sq_nonneg _
    linarith only [hnonneg, hj, horth]
  filter_upwards [(integral_eq_zero_iff_of_nonneg (fun _ ↦ sq_nonneg _) hv).mp hzero] with x hx
  have hx' : v x ^ 2 = 0 := hx
  have hvx : v x = 0 := by simpa using hx'
  exact hvx ▸ le_max_left (u x) 0

private theorem jumpPairing_mul_identity (a c : ℝ) (b d : ℂ) :
    (conj (b * a - d * c) * (b * a - d * c)).re -
      (conj ((a : ℂ) - c) * ((Complex.normSq b * a : ℝ) - (Complex.normSq d * c : ℝ))).re =
      a * c * Complex.normSq (b - d) := by
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]
  ring

/-- If a real interpolant is orthogonal to its product with the squared modulus of a
multiplier, the energy of the multiplied interpolant depends only on multiplier differences. -/
theorem jumpPairing_mul_self_eq_of_orthogonal (μ : Measure X) (ν : Measure (X × X))
    (h : X → ℝ) (b : X → ℂ)
    (hEnergy : Integrable (fun p ↦ (conj (b p.1 * h p.1 - b p.2 * h p.2) *
      (b p.1 * h p.1 - b p.2 * h p.2)).re) ν)
    (hCross : Integrable (fun p ↦ (conj ((h p.1 : ℂ) - h p.2) *
      (((Complex.normSq (b p.1) * h p.1 : ℝ) : ℂ) -
        ((Complex.normSq (b p.2) * h p.2 : ℝ) : ℂ))).re) ν)
    (horth : jumpPairing μ ν (fun x ↦ (h x : ℂ))
      (fun x ↦ (Complex.normSq (b x) * h x : ℝ)) = 0) :
    jumpPairing μ ν (fun x ↦ b x * h x) (fun x ↦ b x * h x) =
      (1 / 2) * ∫ p, h p.1 * h p.2 * Complex.normSq (b p.1 - b p.2) ∂ν := by
  have hm (x : X) :
      (conj (b x * h x) * (b x * h x)).re =
        (conj (h x : ℂ) * (Complex.normSq (b x) * h x : ℝ)).re := by
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  unfold jumpPairing at horth ⊢
  rw [integral_congr_ae (ae_of_all _ hm)]
  have hj :
      (∫ p, (conj (b p.1 * h p.1 - b p.2 * h p.2) * (b p.1 * h p.1 - b p.2 * h p.2)).re ∂ν) -
        (∫ p, (conj ((h p.1 : ℂ) - h p.2) *
          (((Complex.normSq (b p.1) * h p.1 : ℝ) : ℂ) -
            ((Complex.normSq (b p.2) * h p.2 : ℝ) : ℂ))).re ∂ν) =
        ∫ p, h p.1 * h p.2 * Complex.normSq (b p.1 - b p.2) ∂ν := by
    rw [← integral_sub hEnergy hCross]
    exact integral_congr_ae (ae_of_all _ fun p ↦ jumpPairing_mul_identity (h p.1) (h p.2) (b p.1) (b p.2))
  dsimp only at horth ⊢
  linarith only [horth, hj]

end RiemannMasullo
