/-
# Cassels, Chapter 11, proof of Lemma 9.2: local conditions on $b$

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 11, proof of Lemma 9.2, p. 248 ("we have
$q \nmid a$ and so may choose $k(q) = 1$ or $2$ so that $a \in gU_q^2$ … Then there is a $b \in \mathbb Z$ such that $b \in U_p$
($p \in P^*$), $c = a - gb^2 \equiv 0$ ($q^{2m}$)").

**Proves.** `exists_residue_of_sq`: if $a = g\beta^2$ with $\beta \in \mathbb Z_p$, then for every $N$ there is $b_0 \in \mathbb Z$ with
$p^N \mid a - gb^2$ for all $b \equiv b_0 \pmod{p^N}$ (the condition at $q$; also used in case (b)).
-/
import QuadFormsKB.Literature.Cassels.Ch11Lemma92Assembly

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels.Ch11L92

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

/-- **The condition at $q$** (Cassels, p. 248): if $a = g\beta^2$ in $\mathbb Z_p$, then for every $N$ there is $b_0 \in \mathbb Z$ such
that $p^N \mid a - gb^2$ for every $b \equiv b_0 \pmod{p^N}$. *Proof:* $b_0$ is an integer approximation of $\beta$. -/
theorem exists_residue_of_sq (p : ℕ) [Fact p.Prime] (a g : ℤ) (β : ℤ_[p]) (h : (a : ℤ_[p]) = g * β ^ 2) (N : ℕ) :
    ∃ b0 : ℤ, ∀ b : ℤ, b ≡ b0 [ZMOD ((p ^ N : ℕ) : ℤ)] → (p : ℤ) ^ N ∣ a - b ^ 2 * g := by
  refine ⟨(PadicInt.appr β N : ℤ), fun b hb => ?_⟩
  have h1 : (p : ℤ_[p]) ^ N ∣ β - (PadicInt.appr β N : ℤ_[p]) :=
    Ideal.mem_span_singleton.mp (PadicInt.appr_spec N β)
  have h2 : (p : ℤ_[p]) ^ N ∣ ((b : ℤ) : ℤ_[p]) - ((PadicInt.appr β N : ℤ) : ℤ_[p]) := by
    have : ((p ^ N : ℕ) : ℤ) ∣ b - (PadicInt.appr β N : ℤ) := (Int.ModEq.dvd hb.symm)
    have := Int.cast_dvd_cast (α := ℤ_[p]) _ _ this
    simpa using this
  have h3 : (p : ℤ_[p]) ^ N ∣ ((a - b ^ 2 * g : ℤ) : ℤ_[p]) := by
    have hbβ : (p : ℤ_[p]) ^ N ∣ β - (b : ℤ_[p]) := by
      have := dvd_sub h1 h2; simpa using this
    obtain ⟨t, ht⟩ := hbβ
    have e : ((a - b ^ 2 * g : ℤ) : ℤ_[p]) = g * (β - b) * (β + b) := by push_cast; rw [h]; ring
    rw [e, ht]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_mul_right _ _) _) _
  exact_mod_cast (PadicInt.pow_p_dvd_int_iff N _).mp h3

open QuadFormsKB.Lattices in
/-- **$U_p \subseteq \theta(\Gamma_p)$ from scaled unit values** (Cassels, p. 244: "f represents all of $p^\mu U_p$ … This
implies (iii)"; the same argument for (9.43), (9.60)): if all values $B(x, y)$, $x, y \in L_v$, have valuation at most that
of $\pi_0 \ne 0$, and for every unit $w$ some $x \in L_v$ has $Q(x) = \pi_0w$, then every unit is in $\theta(O^+(L_v))$: the
reflections in $x_1$, $x_2$ with $Q(x_1) = \pi_0$, $Q(x_2) = \pi_0w$ map $L_v$ onto itself and $\theta(\tau_{x_1}\tau_{x_2}) =
w\pi_0^2$. -/
theorem units_mem_of_scaled_values {n : ℕ} {Q : QuadForm ℚ n} (hQ : Q.Nondegenerate) {v : HeightOneSpectrum (𝓞 ℚ)}
    (L : Lat ℚ n) {π0 : v.adicCompletion ℚ} (hπ0 : π0 ≠ 0)
    (hbil : ∀ x ∈ loc v L.1, ∀ y ∈ loc v L.1,
      Valued.v (qbil Q (v.adicCompletion ℚ) x y) ≤ Valued.v π0)
    (hval : ∀ w : (v.adicCompletion ℚ)ˣ, Valued.v (w : v.adicCompletion ℚ) = 1 →
      ∃ x ∈ loc v L.1, Q.evalIn (v.adicCompletion ℚ) x = π0 * w)
    (w : (v.adicCompletion ℚ)ˣ) (hw : Valued.v (w : v.adicCompletion ℚ) = 1) :
    w ∈ localSpinorNormGroup Q hQ v L := by
  have hstab : ∀ (w' : (v.adicCompletion ℚ)ˣ) (x : Fin n → v.adicCompletion ℚ), Valued.v (w' : v.adicCompletion ℚ) = 1 →
      x ∈ loc v L.1 → Q.evalIn _ x = π0 * w' → symm Q (v.adicCompletion ℚ) x ∈ locStabV Q v L := by
    intro w' x hw' hx hQx
    have hx0 : Q.evalIn _ x ≠ 0 := by rw [hQx]; exact mul_ne_zero hπ0 w'.ne_zero
    show locAct v _ (loc v L.1) = loc v L.1
    refine locAct_symm_eq hx hx0 fun y hy => ?_
    rw [hQx, map_mul, hw', mul_one]
    exact hbil x hx y hy
  obtain ⟨x1, hx1, hQ1⟩ := hval 1 (by simp)
  obtain ⟨x2, hx2, hQ2⟩ := hval w hw
  refine mem_localSpinorNormGroup_of_symm_pair hQ L (y := x1) (by rw [hQ2]; exact mul_ne_zero hπ0 w.ne_zero)
    (by rw [hQ1]; simpa using hπ0) (hstab w x2 hw hx2 hQ2) (hstab 1 x1 (by simp) hx1 hQ1) w ?_
  rw [hQ1, hQ2]
  have : π0 * (w : v.adicCompletion ℚ) * (π0 * ((1 : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) =
      (w : v.adicCompletion ℚ) * π0 ^ 2 := by simp; ring
  rw [this]
  exact sqClassOf_mul_sq w hπ0

end QuadFormsKB.Cassels.Ch11L92
