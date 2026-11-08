/-
# Watson (1963): values of the part with even Hessian

For a form $\psi$ over $\mathbb Z_2$ with even Hessian that is square-free at $2$ (`SqFreePsi`):

* (ψ1) `psi_represents_two_mul_unit`: if $\psi$ has only even values and $m \ge 2$, then $\psi$ represents $2u$ for
  every unit $u$ (some Hessian entry is $\not\equiv 0 \pmod 4$, giving a binary subform $2\,b$ with $b$ unimodular
  of odd discriminant);
* (ψ2) `psi_exists_three_mod_four`: if $\psi$ has an odd value and $m \ge 3$, then $\psi$ has a value
  $\equiv 3 \pmod 4$ (otherwise a nonzero $\mathbb F_2$-solution of two linear conditions contradicts `SqFreePsi`).
-/
import QuadFormsKB.Literature.Watson1963.PsiFacts

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Watson1963

open Siegel DefiniteForms QuadFormsKB.Hanke2011Structure

variable {m : ℕ}

/-- Helper: polarization in the form $\psi(x+y) = \psi(x) + \psi(y) + x^{\mathsf T} H y$. -/
theorem psi_eval_add (ψ : QuadForm ℤ_[2] m) (x y : Fin m → ℤ_[2]) :
    ψ.eval (x + y) = ψ.eval x + ψ.eval y + x ⬝ᵥ (ψ.hessian *ᵥ y) := by
  have := QuadForm.eval_polar ψ x y
  linear_combination this

/-- Helper: a form with even Hessian has even pairings. -/
theorem psi_pair_even (ψ : QuadForm ℤ_[2] m) (hpsi : ∀ i j, (2 : ℤ_[2]) ∣ ψ.hessian i j)
    (c' c : Fin m → ℤ_[2]) : (2 : ℤ_[2]) ∣ c' ⬝ᵥ (ψ.hessian *ᵥ c) := by
  simp only [dotProduct, mulVec]
  exact Finset.dvd_sum fun a _ => Dvd.dvd.mul_left (Finset.dvd_sum fun b _ => Dvd.dvd.mul_right (hpsi a b) _) _

/-- Helper: pairing of unit vectors is a Hessian entry. -/
theorem single_dot_psi (w : Fin m → ℤ_[2]) (i : Fin m) : (Pi.single i (1 : ℤ_[2]) : Fin m → ℤ_[2]) ⬝ᵥ w = w i := by
  simp [dotProduct, Pi.single_apply]

theorem single_hess_single (ψ : QuadForm ℤ_[2] m) (i j : Fin m) :
    (Pi.single i (1 : ℤ_[2]) : Fin m → ℤ_[2]) ⬝ᵥ (ψ.hessian *ᵥ (Pi.single j (1 : ℤ_[2]))) = ψ.hessian i j := by
  rw [single_dot_psi]
  simp [mulVec, dotProduct, Pi.single_apply]

theorem not_two_dvd_one' : ¬ (2 : ℤ_[2]) ∣ 1 := fun h => by
  have := toZMod_eq_zero_of_two_dvd h
  rw [map_one] at this
  revert this
  decide

theorem two_dvd_of_toZMod' {x : ℤ_[2]} (h : PadicInt.toZMod x = 0) : (2 : ℤ_[2]) ∣ x := by
  have := (toZMod_eq_zero_iff_dvd 2 x).1 h
  simpa using this

theorem odd_eq_one_add {a : ℤ_[2]} (h : ¬ (2 : ℤ_[2]) ∣ a) : ∃ k, a = 1 + 2 * k := by
  have hu : IsUnit a := isUnit_of_toZMod_ne_zero (toZMod_ne_zero_of_not_dvd h)
  obtain ⟨k, hk⟩ := Composition.two_dvd_sub_one_of_isUnit hu
  exact ⟨k, by linear_combination hk⟩

theorem odd_cases' {x : ℤ_[2]} (hx : ¬ (2 : ℤ_[2]) ∣ x) : (4 : ℤ_[2]) ∣ x - 1 ∨ (4 : ℤ_[2]) ∣ x - 3 := by
  obtain ⟨k, hk⟩ := odd_eq_one_add hx
  by_cases h : (2 : ℤ_[2]) ∣ k
  · obtain ⟨n, hn⟩ := h
    left
    exact ⟨n, by linear_combination hk + 2 * hn⟩
  · obtain ⟨l, hl⟩ := odd_eq_one_add h
    right
    exact ⟨l, by linear_combination hk + 2 * hl⟩

/-- **(ψ1)** A form with even Hessian and only even values, square-free at $2$, in at least $2$ variables,
represents $2u$ for every unit $u$. -/
theorem psi_represents_two_mul_unit {m : ℕ} (ψ : QuadForm ℤ_[2] m)
    (hpsi : ∀ i j, (2 : ℤ_[2]) ∣ ψ.hessian i j) (hSF : SqFreePsi ψ) (hev : ∀ c, (2 : ℤ_[2]) ∣ ψ.eval c)
    (hm : 2 ≤ m) {u : ℤ_[2]} (hu : IsUnit u) : ∃ c, ψ.eval c = 2 * u := by
  have hP2 := psi_pair_even ψ hpsi
  have hdiag : ∀ i, (4 : ℤ_[2]) ∣ ψ.hessian i i := by
    intro i
    have h := QuadForm.dotProduct_hessian_self ψ (Pi.single i (1 : ℤ_[2]))
    rw [single_hess_single] at h
    obtain ⟨a, ha⟩ := hev (Pi.single i (1 : ℤ_[2]))
    exact ⟨a, by rw [h, ha]; ring⟩
  obtain ⟨i0, i1, h01⟩ : ∃ i0 i1 : Fin m, i0 ≠ i1 :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩
  have key : ∃ i j, ¬ (4 : ℤ_[2]) ∣ ψ.hessian i j := by
    by_contra hcon
    push_neg at hcon
    have hP4 : ∀ c' c : Fin m → ℤ_[2], (4 : ℤ_[2]) ∣ c' ⬝ᵥ (ψ.hessian *ᵥ c) := fun c' c => by
      simp only [dotProduct, mulVec]
      exact Finset.dvd_sum fun a _ => Dvd.dvd.mul_left
        (Finset.dvd_sum fun b _ => Dvd.dvd.mul_right (hcon a b) _) _
    have hn4 : ∀ i, ¬ (4 : ℤ_[2]) ∣ ψ.eval (Pi.single i (1 : ℤ_[2])) := by
      intro i h4
      have := hSF _ h4 (fun c' _ => hP4 _ _) i
      simp only [Pi.single_eq_same] at this
      exact not_two_dvd_one' this
    have hodd : ∀ i, ∃ k, ψ.eval (Pi.single i (1 : ℤ_[2])) = 2 * (1 + 2 * k) := by
      intro i
      obtain ⟨a, ha⟩ := hev (Pi.single i (1 : ℤ_[2]))
      have hna : ¬ (2 : ℤ_[2]) ∣ a := fun ⟨b, hb⟩ => hn4 i ⟨b, by rw [ha, hb]; ring⟩
      obtain ⟨k, hk⟩ := odd_eq_one_add hna
      exact ⟨k, by rw [ha, hk]⟩
    obtain ⟨k, hk⟩ := hodd i0
    obtain ⟨l, hl⟩ := hodd i1
    obtain ⟨h, hh⟩ := hcon i0 i1
    have hsum : ψ.eval (Pi.single i0 (1 : ℤ_[2]) + Pi.single i1 1) = 4 * (1 + k + l + h) := by
      rw [psi_eval_add, hk, hl, single_hess_single, hh]; ring
    have := hSF _ ⟨_, hsum⟩ (fun c' _ => hP4 _ _) i0
    simp [Pi.single_apply, h01] at this
    exact not_two_dvd_one' this
  obtain ⟨i, j, hij⟩ := key
  have hne : i ≠ j := by
    rintro rfl
    exact hij (hdiag i)
  obtain ⟨β, hβ⟩ := hP2 (Pi.single i (1 : ℤ_[2])) (Pi.single j 1)
  rw [single_hess_single] at hβ
  obtain ⟨α, hα⟩ := hev (Pi.single i (1 : ℤ_[2]))
  obtain ⟨γ, hγ⟩ := hev (Pi.single j (1 : ℤ_[2]))
  have hβo : ¬ (2 : ℤ_[2]) ∣ β := fun ⟨b, hb⟩ => hij ⟨b, by rw [hβ, hb]; ring⟩
  have hunit : IsUnit (β ^ 2 - 4 * α * γ) := by
    apply isUnit_of_toZMod_ne_zero
    rw [show β ^ 2 - 4 * α * γ = β ^ 2 + 2 * (-(2 * α * γ)) by ring, map_add, map_mul,
      toZMod_eq_zero_of_two_dvd (dvd_refl (2 : ℤ_[2])), zero_mul, add_zero, map_pow]
    exact pow_ne_zero _ (toZMod_ne_zero_of_not_dvd hβo)
  have hdet : IsUnit (Composition.bq α β γ).hessian.det := by
    have h := Composition.neg_det_bq α β γ
    have : (Composition.bq α β γ).hessian.det = -(β ^ 2 - 4 * α * γ) := by linear_combination -h
    rw [this]
    exact hunit.neg
  obtain ⟨x, hx⟩ := exists_eval_eq_unit (k := 1) (Composition.bq α β γ) hdet le_rfl hu
  have hx' : (Composition.bq α β γ).eval ![x 0, x 1] = u := by
    have e : ![x 0, x 1] = x := by
      ext k; fin_cases k <;> rfl
    rw [e]; exact hx
  rw [Composition.bq_eval] at hx'
  refine ⟨x 0 • (Pi.single i (1 : ℤ_[2])) + x 1 • (Pi.single j (1 : ℤ_[2])), ?_⟩
  rw [psi_eval_add, eval_smul_sq, eval_smul_sq, mulVec_smul, dotProduct_smul, smul_dotProduct,
    single_hess_single, smul_eq_mul, smul_eq_mul]
  linear_combination 2 * hx' + (x 0) ^ 2 * hα + (x 1) ^ 2 * hγ + x 0 * x 1 * hβ

theorem key3_check : ∀ a0 a1 a2 b0 b1 b2 : ZMod 2, ∃ e0 e1 e2 : ZMod 2,
    (e0 ≠ 0 ∨ e1 ≠ 0 ∨ e2 ≠ 0) ∧ a0 * e0 + a1 * e1 + a2 * e2 = 0 ∧ b0 * e0 + b1 * e1 + b2 * e2 = 0 := by
  decide

theorem zmod2_sq : ∀ x : ZMod 2, x ^ 2 = x := by decide

theorem toZMod_lift (x : ZMod 2) : PadicInt.toZMod ((x.val : ℕ) : ℤ_[2]) = x := by
  rw [map_natCast]; exact ZMod.natCast_zmod_val x

/-- **(ψ2)** A form with even Hessian, square-free at $2$, with an odd value, in at least $3$ variables, has a
value $\equiv 3 \pmod 4$. -/
theorem psi_exists_three_mod_four {m : ℕ} (ψ : QuadForm ℤ_[2] m)
    (hpsi : ∀ i j, (2 : ℤ_[2]) ∣ ψ.hessian i j) (hSF : SqFreePsi ψ) (c₀ : Fin m → ℤ_[2])
    (hc₀ : ¬ (2 : ℤ_[2]) ∣ ψ.eval c₀) (hm : 3 ≤ m) : ∃ c, (4 : ℤ_[2]) ∣ ψ.eval c - 3 := by
  by_contra hcon
  push_neg at hcon
  have hP2 := psi_pair_even ψ hpsi
  have h1 : ∀ c, ¬ (2 : ℤ_[2]) ∣ ψ.eval c → (4 : ℤ_[2]) ∣ ψ.eval c - 1 :=
    fun c hc => (odd_cases' hc).resolve_right (hcon c)
  have hc1 := h1 c₀ hc₀
  have hstar : ∀ d, (2 : ℤ_[2]) ∣ ψ.eval d → (4 : ℤ_[2]) ∣ ψ.eval d + c₀ ⬝ᵥ (ψ.hessian *ᵥ d) := by
    intro d hd
    have hodd : ¬ (2 : ℤ_[2]) ∣ ψ.eval (c₀ + d) := by
      rw [psi_eval_add]
      intro h
      obtain ⟨k, hk⟩ := dvd_sub (dvd_sub h hd) (hP2 c₀ d)
      exact hc₀ ⟨k, by linear_combination hk⟩
    have h2 := h1 _ hodd
    rw [psi_eval_add] at h2
    obtain ⟨k, hk⟩ := dvd_sub h2 hc1
    exact ⟨k, by linear_combination hk⟩
  have hstar' : ∀ d d', (2 : ℤ_[2]) ∣ ψ.eval d → (2 : ℤ_[2]) ∣ ψ.eval d' →
      (4 : ℤ_[2]) ∣ d ⬝ᵥ (ψ.hessian *ᵥ d') := by
    intro d d' hd hd'
    have hdd : (2 : ℤ_[2]) ∣ ψ.eval (d + d') := by
      rw [psi_eval_add]; exact dvd_add (dvd_add hd hd') (hP2 d d')
    obtain ⟨k1, e1⟩ := hstar d hd
    obtain ⟨k2, e2⟩ := hstar d' hd'
    obtain ⟨k3, e3⟩ := hstar _ hdd
    rw [psi_eval_add, mulVec_add, dotProduct_add] at e3
    exact ⟨k3 - k1 - k2, by linear_combination e3 - e1 - e2⟩
  obtain ⟨i0, i1, i2, h01, h02, h12⟩ : ∃ i0 i1 i2 : Fin m, i0 ≠ i1 ∧ i0 ≠ i2 ∧ i1 ≠ i2 :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, by simp [Fin.ext_iff], by simp [Fin.ext_iff],
      by simp [Fin.ext_iff]⟩
  have h10 := h01.symm
  have h20 := h02.symm
  have h21 := h12.symm
  have hHc : ∀ k, (2 : ℤ_[2]) ∣ (ψ.hessian *ᵥ c₀) k := fun k => by
    simp only [mulVec, dotProduct]
    exact Finset.dvd_sum fun b _ => Dvd.dvd.mul_right (hpsi k b) _
  choose g hg using hHc
  obtain ⟨e0, e1, e2, hne, hl1, hl2⟩ := key3_check (PadicInt.toZMod (ψ.eval (Pi.single i0 1)))
    (PadicInt.toZMod (ψ.eval (Pi.single i1 1))) (PadicInt.toZMod (ψ.eval (Pi.single i2 1)))
    (PadicInt.toZMod (g i0)) (PadicInt.toZMod (g i1)) (PadicInt.toZMod (g i2))
  obtain ⟨s0, hs0⟩ : ∃ s : ℤ_[2], PadicInt.toZMod s = e0 := ⟨_, toZMod_lift e0⟩
  obtain ⟨s1, hs1⟩ : ∃ s : ℤ_[2], PadicInt.toZMod s = e1 := ⟨_, toZMod_lift e1⟩
  obtain ⟨s2, hs2⟩ : ∃ s : ℤ_[2], PadicInt.toZMod s = e2 := ⟨_, toZMod_lift e2⟩
  obtain ⟨y, hy⟩ : ∃ y : Fin m → ℤ_[2],
      y = s0 • (Pi.single i0 (1 : ℤ_[2])) + s1 • (Pi.single i1 (1 : ℤ_[2])) + s2 • (Pi.single i2 (1 : ℤ_[2])) :=
    ⟨_, rfl⟩
  have hyd : ∀ w : Fin m → ℤ_[2], y ⬝ᵥ w = s0 * w i0 + s1 * w i1 + s2 * w i2 := by
    intro w
    rw [hy]
    simp only [add_dotProduct, smul_dotProduct, single_dot_psi, smul_eq_mul]
  have hyi0 : y i0 = s0 := by rw [hy]; simp [Pi.single_apply, h01, h02, h10, h20]
  have hyi1 : y i1 = s1 := by rw [hy]; simp [Pi.single_apply, h01, h12, h10, h21]
  have hyi2 : y i2 = s2 := by rw [hy]; simp [Pi.single_apply, h02, h12, h20, h21]
  have hψy : (2 : ℤ_[2]) ∣ ψ.eval y := by
    apply two_dvd_of_toZMod'
    have e : ψ.eval y = s0 ^ 2 * ψ.eval (Pi.single i0 1) + s1 ^ 2 * ψ.eval (Pi.single i1 1)
        + s2 ^ 2 * ψ.eval (Pi.single i2 1)
        + ((s0 • (Pi.single i0 (1 : ℤ_[2]))) ⬝ᵥ (ψ.hessian *ᵥ (s1 • (Pi.single i1 (1 : ℤ_[2])))))
        + ((s0 • (Pi.single i0 (1 : ℤ_[2])) + s1 • (Pi.single i1 (1 : ℤ_[2]))) ⬝ᵥ
            (ψ.hessian *ᵥ (s2 • (Pi.single i2 (1 : ℤ_[2]))))) := by
      rw [hy, psi_eval_add, psi_eval_add, eval_smul_sq, eval_smul_sq, eval_smul_sq]; ring
    have z1 := toZMod_eq_zero_of_two_dvd
      (hP2 (s0 • (Pi.single i0 (1 : ℤ_[2]))) (s1 • (Pi.single i1 (1 : ℤ_[2]))))
    have z2 := toZMod_eq_zero_of_two_dvd
      (hP2 (s0 • (Pi.single i0 (1 : ℤ_[2])) + s1 • (Pi.single i1 (1 : ℤ_[2]))) (s2 • (Pi.single i2 (1 : ℤ_[2]))))
    rw [e, map_add, map_add, map_add, map_add, z1, z2, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow,
      hs0, hs1, hs2, zmod2_sq, zmod2_sq, zmod2_sq]
    linear_combination hl1
  have hP4 : (4 : ℤ_[2]) ∣ c₀ ⬝ᵥ (ψ.hessian *ᵥ y) := by
    rw [dot_symm, hyd, hg, hg, hg]
    have hz : PadicInt.toZMod (s0 * g i0 + s1 * g i1 + s2 * g i2) = 0 := by
      rw [map_add, map_add, map_mul, map_mul, map_mul, hs0, hs1, hs2]
      linear_combination hl2
    obtain ⟨t, ht⟩ := two_dvd_of_toZMod' hz
    exact ⟨t, by linear_combination 2 * ht⟩
  have h4 : (4 : ℤ_[2]) ∣ ψ.eval y := (dvd_add_left hP4).1 (hstar y hψy)
  have hall := hSF y h4 (fun c' hc' => hstar' c' y hc' hψy)
  rcases hne with h | h | h
  · have := toZMod_eq_zero_of_two_dvd (hall i0)
    rw [hyi0, hs0] at this
    exact h this
  · have := toZMod_eq_zero_of_two_dvd (hall i1)
    rw [hyi1, hs1] at this
    exact h this
  · have := toZMod_eq_zero_of_two_dvd (hall i2)
    rw [hyi2, hs2] at this
    exact h this

end QuadFormsKB.Watson1963
