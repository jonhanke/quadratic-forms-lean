/-
# Cassels, Chapter 6, Lemma 4.3: the conditions at $2$ for a ternary zero

**Setting.** Cassels, *Rational Quadratic Forms*, Ch. 6, §4 (the Strong Hasse Principle for $n = 3$): by Lemma 4.1 a
regular ternary rational form is, up to a factor, $g(\vec x) = a_0x_0^2 + a_1x_1^2 + a_2x_2^2$ with integers $a_j$
and $a_0a_1a_2$ squarefree (Cassels' $a_1, a_2, a_3$ are $a_0, a_1, a_2$ here). Isotropy over $\mathbb Q_2$ is
`(QuadForm.diag ![(a₀ : ℚ), a₁, a₂]).IsotropicIn ℚ_[2]`.

**Proves** Lemma 4.3 (p. 79): if $g$ is isotropic over $\mathbb Q_2$ then
* (i) when $a_0a_1a_2$ is odd, $a_i + a_j \equiv 0 \pmod 4$ for some $i \ne j$ (`lemma_4_3_i`; Cassels: "after
  permuting the suffixes, $a_1 + a_2 \equiv 0 \pmod 4$"; the squarefree hypothesis is not needed);
* (ii) when $2 \mid a_0$, there is $s \in \{0, 1\}$ with $a_1 + a_2 + sa_0 \equiv 0 \pmod 8$ (`lemma_4_3_ii`).

**Proof notes.** Cassels argues with a $2$-adic zero normalized by $\max\lvert a_jt_j^2\rvert_2$ and $t^2 \equiv 1
\pmod 8$ for units. Here isotropy is turned into the Hilbert symbol $(-a_0a_1, -a_0a_2)_2 = 1$
(`HM3.isotropic_diag_three_iff`, square classes) and evaluated by the explicit formula
$(2^\alpha u, 2^\beta v)_2 = (-1)^{\varepsilon(u)\varepsilon(v) + \alpha\omega(v) + \beta\omega(u)}$
(`ConwaySloane.hilbert_two_int`); the remaining statement about residues modulo $8$ is checked by `decide`.
-/
import QuadFormsKB.Literature.LocalGlobal.ConwaySloane
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowskiThree

namespace QuadFormsKB.Cassels

open QuadFormsKB.HilbertLocal

/-- Reduction $\mathbb Z/8 \to \mathbb Z/4$. -/
private abbrev r84 : ZMod 8 →+* ZMod 4 := ZMod.castHom (by norm_num) (ZMod 4)
/-- Reduction $\mathbb Z/8 \to \mathbb Z/2$. -/
private abbrev r82 : ZMod 8 →+* ZMod 2 := ZMod.castHom (by norm_num) (ZMod 2)

/-- An odd integer is $1$ modulo $2$. -/
private theorem odd_res (a : ℤ) (h : ¬ (2 : ℤ) ∣ a) : r82 (a : ZMod 8) = 1 := by
  rw [map_intCast]
  have : (a : ZMod 2) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  generalize (a : ZMod 2) = x at this
  fin_cases x
  · exact absurd rfl this
  · rfl

/-- Lemma 4.3 (i) modulo $8$ (finite check). -/
private theorem key_i : ∀ x y z : ZMod 8, r82 x = 1 → r82 y = 1 → r82 z = 1 →
    (twoEps (-(x * y)) * twoEps (-(x * z))) % 2 = 0 →
    r84 (x + y) = 0 ∨ r84 (x + z) = 0 ∨ r84 (y + z) = 0 := by
  intro x; fin_cases x <;> decide

/-- Lemma 4.3 (ii) modulo $8$ (finite check). -/
private theorem key_ii : ∀ b x y : ZMod 8, r82 b = 1 → r82 x = 1 → r82 y = 1 →
    (twoEps (-(b * x)) * twoEps (-(b * y)) + 1 * twoOmega (-(b * y)) + 1 * twoOmega (-(b * x))) % 2 = 0 →
    x + y = 0 ∨ x + y + 2 * b = 0 := by
  intro x; fin_cases x <;> decide

/-- Isotropy of $\langle a_0, a_1, a_2\rangle$ over $\mathbb Q_2$ through the Hilbert symbol of $-a_0a_1$, $-a_0a_2$. -/
private theorem hilbert_of_isotropic (a₀ a₁ a₂ : ℤ) (h₀ : a₀ ≠ 0) (h₁ : a₁ ≠ 0) (h₂ : a₂ ≠ 0)
    (hiso : (QuadForm.diag ![(a₀ : ℚ), a₁, a₂]).IsotropicIn ℚ_[2]) :
    (RatPlace.finite ⟨2, Nat.prime_two⟩).hilbert ((-(a₀ * a₁) : ℤ) : ℚ) ((-(a₀ * a₂) : ℤ) : ℚ) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h₀' : (a₀ : ℚ) ≠ 0 := by exact_mod_cast h₀
  rw [HM3.isotropic_diag_three_iff ℚ_[2] _ _ _ h₀' (by exact_mod_cast h₁) (by exact_mod_cast h₂)] at hiso
  have hc : ((1 / a₀ : ℚ) : ℚ_[2]) ≠ 0 := by
    have : (1 / a₀ : ℚ) ≠ 0 := by simp [h₀']
    exact_mod_cast this
  have e : ∀ x : ℤ, algebraMap ℚ ℚ_[2] (-x / a₀) = (((-(a₀ * x) : ℤ) : ℚ) : ℚ_[2]) * ((1 / a₀ : ℚ) : ℚ_[2]) ^ 2 := by
    intro x
    rw [eq_ratCast]
    push_cast
    field_simp
  rw [e, e, HM3.hilbertSymbol_mul_sq_left _ _ _ _ hc, hilbertSymbol_comm,
    HM3.hilbertSymbol_mul_sq_left _ _ _ _ hc, hilbertSymbol_comm] at hiso
  exact hiso

/-- Parity of $(-1)^k$. -/
private theorem even_of_neg_one_pow {k : ℕ} (h : ((-1 : ℤ)) ^ k = 1) : k % 2 = 0 := by
  rcases Nat.even_or_odd k with he | ho
  · exact Nat.even_iff.1 he
  · rw [ho.neg_one_pow] at h; norm_num at h

/-- **Cassels, Ch. 6, Lemma 4.3 (i)**: *let $g = a_0x_0^2 + a_1x_1^2 + a_2x_2^2$ (integers $a_j$) be isotropic over
$\mathbb Q_2$ and suppose $2 \nmid a_0a_1a_2$; then after permuting the indices $a_0 + a_1 \equiv 0 \pmod 4$*, i.e.
$4 \mid a_i + a_j$ for some pair $i \ne j$. (Cassels assumes $g$ as in Lemma 4.1, $a_0a_1a_2$ squarefree; that is not
needed here.) -/
@[kb "cassels1978" "Ch. 6, Lemma 4.3 (i), p. 79"]
theorem lemma_4_3_i (a₀ a₁ a₂ : ℤ) (hodd : ¬ (2 : ℤ) ∣ a₀ * a₁ * a₂)
    (hiso : (QuadForm.diag ![(a₀ : ℚ), a₁, a₂]).IsotropicIn ℚ_[2]) :
    (4 : ℤ) ∣ a₀ + a₁ ∨ (4 : ℤ) ∣ a₀ + a₂ ∨ (4 : ℤ) ∣ a₁ + a₂ := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have o₀ : ¬ (2 : ℤ) ∣ a₀ := fun h => hodd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _)
  have o₁ : ¬ (2 : ℤ) ∣ a₁ := fun h => hodd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _)
  have o₂ : ¬ (2 : ℤ) ∣ a₂ := fun h => hodd (dvd_mul_of_dvd_right h _)
  have nz : ∀ a : ℤ, ¬ (2 : ℤ) ∣ a → a ≠ 0 := fun a h h0 => h (h0 ▸ dvd_zero _)
  have hH := hilbert_of_isotropic a₀ a₁ a₂ (nz _ o₀) (nz _ o₁) (nz _ o₂) hiso
  rw [ConwaySloane.hilbert_two_int 0 0 (-(a₀ * a₁)) (-(a₀ * a₂)) _ _
    (by rw [dvd_neg]; exact fun h => hodd (dvd_mul_of_dvd_left h _))
    (by rw [dvd_neg]; intro h; exact o₂ ((Int.prime_two.dvd_or_dvd h).resolve_left o₀))
    (by simp) (by simp)] at hH
  have hk := even_of_neg_one_pow hH
  simp only [zero_mul, add_zero] at hk
  have hr : ∀ x y : ℤ, (4 : ℤ) ∣ x + y ↔ r84 ((x + y : ℤ) : ZMod 8) = 0 := fun x y => by
    rw [map_intCast]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).symm
  rw [hr, hr, hr]
  push_cast at hk ⊢
  exact key_i _ _ _ (odd_res _ o₀) (odd_res _ o₁) (odd_res _ o₂) hk

/-- **Cassels, Ch. 6, Lemma 4.3 (ii)**: *let $g = a_0x_0^2 + a_1x_1^2 + a_2x_2^2$ with integers $a_j$ and $a_0a_1a_2$
squarefree be isotropic over $\mathbb Q_2$, and suppose $2 \mid a_0$; then there is $s = 0$ or $1$ with
$a_1 + a_2 + sa_0 \equiv 0 \pmod 8$.* (Cassels' $a_1$ is $a_0$ here.) -/
@[kb "cassels1978" "Ch. 6, Lemma 4.3 (ii), p. 79"]
theorem lemma_4_3_ii (a₀ a₁ a₂ : ℤ) (hsq : Squarefree (a₀ * a₁ * a₂)) (h2 : (2 : ℤ) ∣ a₀)
    (hiso : (QuadForm.diag ![(a₀ : ℚ), a₁, a₂]).IsotropicIn ℚ_[2]) :
    (8 : ℤ) ∣ a₁ + a₂ ∨ (8 : ℤ) ∣ a₁ + a₂ + a₀ := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, rfl⟩ := h2
  have h4 : ∀ c : ℤ, (2 : ℤ) * 2 ∣ c → (2 : ℤ) * b * a₁ * a₂ = c → False := by
    intro c hc he
    have := hsq 2 (by rw [he]; exact hc)
    exact absurd (Int.isUnit_iff.1 this) (by omega)
  have ob : ¬ (2 : ℤ) ∣ b := fun ⟨c, hc⟩ => h4 _ ⟨c * a₁ * a₂, by rw [hc]; ring⟩ rfl
  have o₁ : ¬ (2 : ℤ) ∣ a₁ := fun ⟨c, hc⟩ => h4 _ ⟨b * c * a₂, by rw [hc]; ring⟩ rfl
  have o₂ : ¬ (2 : ℤ) ∣ a₂ := fun ⟨c, hc⟩ => h4 _ ⟨b * a₁ * c, by rw [hc]; ring⟩ rfl
  have nz : ∀ a : ℤ, ¬ (2 : ℤ) ∣ a → a ≠ 0 := fun a h h0 => h (h0 ▸ dvd_zero _)
  have hb0 : 2 * b ≠ 0 := mul_ne_zero two_ne_zero (nz _ ob)
  have hH := hilbert_of_isotropic (2 * b) a₁ a₂ hb0 (nz _ o₁) (nz _ o₂) hiso
  have hm : ¬ (2 : ℤ) ∣ -(b * a₁) := by
    rw [dvd_neg]; intro h; exact o₁ ((Int.prime_two.dvd_or_dvd h).resolve_left ob)
  have hn : ¬ (2 : ℤ) ∣ -(b * a₂) := by
    rw [dvd_neg]; intro h; exact o₂ ((Int.prime_two.dvd_or_dvd h).resolve_left ob)
  rw [ConwaySloane.hilbert_two_int 1 1 (-(b * a₁)) (-(b * a₂)) _ _ hm hn (by push_cast; ring)
    (by push_cast; ring)] at hH
  have hk := even_of_neg_one_pow hH
  have hr : ∀ x : ℤ, (8 : ℤ) ∣ x ↔ ((x : ℤ) : ZMod 8) = 0 := fun x =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).symm
  rw [hr, hr]
  push_cast at hk ⊢
  have := key_ii _ _ _ (odd_res _ ob) (odd_res _ o₁) (odd_res _ o₂) hk
  rcases this with h | h
  · exact Or.inl h
  · right; rw [← h]

end QuadFormsKB.Cassels
