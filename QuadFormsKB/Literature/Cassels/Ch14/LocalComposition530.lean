/-
# Cassels, Chapter 14, §3: composition is well defined on $\mathbb Z_p$-classes

Cassels, *Rational Quadratic Forms* (1978), Ch. 14, §3, p. 339, (3.1).

* `localCompositionWellDefined`: the named statement `LocalCompositionWellDefined p D`, proved for every prime $p$
  and every `[NonzeroDisc D]` (purely local: concordant representatives with first coefficients prime to $p$, then the
  square class of the first coefficients for $p$ odd and the norm form $s^2 - dt^2 \bmod 8$ for $p = 2$, $D = 4d$);
* `isometricGL_principal_of_sq_proved`: the unconditional version of `isometricGL_principal_of_sq`.
-/
import QuadFormsKB.Literature.Cassels.Ch14.NamedStatements
import QuadFormsKB.Literature.Cassels.Ch14.LocalClassesTwo
import QuadFormsKB.Literature.Cassels.Ch14.LocalImproper
import QuadFormsKB.Literature.Cassels.Ch14.ExistenceImage

namespace QuadFormsKB.Composition

open BinQF Binary FormClass Siegel

section Approx

variable {p : ℕ} [Fact p.Prime]

/-- Helper: a $p$-adic integer is congruent modulo $p^k$ to a rational integer. -/
theorem exists_int_approx (k : ℕ) (x : ℤ_[p]) : ∃ X : ℤ, PadicInt.toZModPow k x = (X : ZMod (p ^ k)) :=
  (ZMod.intCast_surjective (PadicInt.toZModPow k x)).imp fun _ h => h.symm

/-- Helper: if $f \cong g$ over $\mathbb Z_p$, then $g$ represents $a_f$ modulo $p^k$ by an integer vector. -/
theorem exists_int_rep_of_isometricGL (k : ℕ) {f g : BinQF}
    (h : IsometricGL (f.map (Int.castRingHom ℤ_[p])) (g.map (Int.castRingHom ℤ_[p]))) :
    ∃ X Y : ℤ, ((p : ℤ) ^ k) ∣ g.eval X Y - f.a := by
  obtain ⟨T, hT⟩ := h.symm
  have h1 := hT ![1, 0]
  rw [eval_map_two, eval_map_two] at h1
  set v : Fin 2 → ℤ_[p] := T.val.mulVec ![1, 0]
  obtain ⟨X, hX⟩ := exists_int_approx k (v 0)
  obtain ⟨Y, hY⟩ := exists_int_approx k (v 1)
  refine ⟨X, Y, ?_⟩
  have h2 := congrArg (PadicInt.toZModPow (p := p) k) h1
  simp only [map_add, map_mul, map_pow, hX, hY] at h2
  simp at h2
  have h3 : (((g.eval X Y - f.a : ℤ)) : ZMod (p ^ k)) = 0 := by
    rw [BinQF.eval_eq]
    push_cast
    linear_combination h2
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p ^ k)).mp h3
  exact_mod_cast this

end Approx

/-! ### From a value to an equivalence -/

section Conv

variable {p : ℕ} [Fact p.Prime]

/-- Helper: if $g$ represents (by integers, not necessarily coprime) a value $n$ prime to $p$ with $a_f n$ a square
in $\mathbb Z_p$, and $p \nmid a_f$, and $f, g$ have the same discriminant, then $f \cong g$ over $\mathbb Z_p$.
(Divide $(x, y)$ by its gcd $c$, a $p$-adic unit, which divides $n$ by $c^2$, and use `isometricGL_padic_of_sq`.) -/
theorem isometricGL_of_rep {f g : BinQF} (hdisc : f.disc = g.disc) (hf : ¬ (p : ℤ) ∣ f.a) {x y : ℤ}
    (hn : ¬ (p : ℤ) ∣ g.eval x y) {z : ℤ_[p]} (hz : z ^ 2 = ((f.a * g.eval x y : ℤ) : ℤ_[p])) :
    IsometricGL (f.map (Int.castRingHom ℤ_[p])) (g.map (Int.castRingHom ℤ_[p])) := by
  have hg0 : 0 < Int.gcd x y := by
    rcases Nat.eq_zero_or_pos (Int.gcd x y) with h0 | h0
    · obtain ⟨rfl, rfl⟩ := Int.gcd_eq_zero_iff.mp h0
      exact absurd (by simp [BinQF.eval_eq]) hn
    · exact h0
  set c : ℤ := (Int.gcd x y : ℤ) with hcdef
  have hcne : c ≠ 0 := by simp only [hcdef]; exact_mod_cast hg0.ne'
  obtain ⟨x', hx⟩ := Int.gcd_dvd_left (a := x) (b := y)
  obtain ⟨y', hy⟩ := Int.gcd_dvd_right (a := x) (b := y)
  have hxy : IsCoprime x' y' := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have := Int.gcd_div_gcd_div_gcd (i := x) (j := y) hg0
    have e1 : x / c = x' := by rw [hx]; exact Int.mul_ediv_cancel_left _ hcne
    have e2 : y / c = y' := by rw [hy]; exact Int.mul_ediv_cancel_left _ hcne
    rw [← e1, ← e2]; exact this
  have hsc : g.eval x y = c ^ 2 * g.eval x' y' := by
    have hx2 : x = c * x' := hx
    have hy2 : y = c * y' := hy
    have : g.eval x y = g.eval (c * x') (c * y') := congrArg₂ g.eval hx2 hy2
    rw [this, BinQF.eval_eq, BinQF.eval_eq]; ring
  have hpc : ¬ (p : ℤ) ∣ c := fun h => hn (by rw [hsc]; exact dvd_mul_of_dvd_left (dvd_pow h two_ne_zero) _)
  have hn' : ¬ (p : ℤ) ∣ g.eval x' y' := fun h => hn (by rw [hsc]; exact dvd_mul_of_dvd_right h _)
  obtain ⟨g', hI, ha, hd⟩ := exists_intEquiv_a_eq g hxy
  obtain ⟨ci, hci⟩ := (isUnit_intCast_padic (p := p) hpc).exists_right_inv
  have hz2 : z ^ 2 = (f.a : ℤ_[p]) * ((c : ℤ_[p]) ^ 2 * (g.eval x' y' : ℤ_[p])) := by
    rw [hz, hsc]; push_cast; ring
  have key := isometricGL_padic_of_sq (p := p) (f := f) (g := g') (hdisc.trans hd.symm) hf
    (by rw [ha]; exact hn') (z := z * ci) (by
      rw [ha]; push_cast
      linear_combination ci ^ 2 * hz2 + (f.a : ℤ_[p]) * (g.eval x' y' : ℤ_[p]) * ((c : ℤ_[p]) * ci + 1) * hci)
  exact key.trans (IsometricGL.map (Int.castRingHom ℤ_[p]) hI).symm

end Conv

/-! ### Odd $p \mid D$: the square class of the first coefficients -/

section Odd

variable {p : ℕ} [Fact p.Prime]

/-- Helper: for $p$ odd with $p \mid D$, if $f \cong g$ over $\mathbb Z_p$ and $p \nmid a_f a_g$, then $a_f a_g$ is a
square in $\mathbb Z_p$. (Reducing $4a_g\, g(X, Y) = (2a_gX + bY)^2 - DY^2$ modulo $p$, where
$g(X, Y) \equiv a_f$ by `exists_int_rep_of_isometricGL`.) -/
theorem exists_sq_of_isometricGL_odd (hp2 : p ≠ 2) {f g : BinQF} (hdisc : f.disc = g.disc)
    (hpD : (p : ℤ) ∣ f.disc) (hf : ¬ (p : ℤ) ∣ f.a) (hg : ¬ (p : ℤ) ∣ g.a)
    (h : IsometricGL (f.map (Int.castRingHom ℤ_[p])) (g.map (Int.castRingHom ℤ_[p]))) :
    ∃ z : ℤ_[p], z ^ 2 = ((f.a * g.a : ℤ) : ℤ_[p]) := by
  obtain ⟨X, Y, hXY⟩ := exists_int_rep_of_isometricGL (p := p) 1 h
  rw [pow_one] at hXY
  have h1 : ((g.eval X Y : ℤ) : ZMod p) = (f.a : ZMod p) := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (g.eval X Y - f.a) p).mpr hXY
    push_cast at this
    exact sub_eq_zero.mp this
  have h0 : ((f.disc : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hpD
  have hfa0 : (f.a : ZMod p) ≠ 0 := fun h => hf ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h)
  have hga0 : (g.a : ZMod p) ≠ 0 := fun h => hg ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h)
  have h2 : (2 : ZMod p) ≠ 0 := by
    have := Siegel.Kneser.toZMod_two_ne_zero hp2
    rwa [map_ofNat] at this
  have hD : ((g.disc : ℤ) : ZMod p) = 0 := by rw [← hdisc]; exact h0
  have key : (4 : ZMod p) * ((g.a : ZMod p) * (f.a : ZMod p)) =
      (2 * (g.a : ZMod p) * X + (g.b : ZMod p) * Y) ^ 2 := by
    have e : ((g.a * g.eval X Y : ℤ) : ZMod p) * 4 =
        ((2 * g.a * X + g.b * Y : ℤ) : ZMod p) ^ 2 - ((g.disc : ℤ) : ZMod p) * (Y : ZMod p) ^ 2 := by
      rw [BinQF.eval_eq]; simp only [BinQF.disc]; push_cast; ring
    rw [hD, zero_mul, sub_zero] at e
    push_cast at e
    rw [h1] at e
    linear_combination e
  set s : ZMod p := (2 * (g.a : ZMod p) * X + (g.b : ZMod p) * Y) * 2⁻¹ with hs
  have hs2 : s ^ 2 = (g.a : ZMod p) * (f.a : ZMod p) := by
    have h4 : (4 : ZMod p) ≠ 0 := by
      have : (4 : ZMod p) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero h2 h2
    apply mul_left_cancel₀ h4
    rw [key, hs]
    field_simp
    norm_num
  have hs0 : s ≠ 0 := by
    intro h0'
    rw [h0'] at hs2
    exact mul_ne_zero hga0 hfa0 (by rw [← hs2]; ring)
  refine Siegel.Kneser.exists_sq_eq_of_toZMod hp2 _ hs0 ?_
  rw [map_intCast, hs2]; push_cast; ring

end Odd

/-! ### $p = 2$, $D = 4d$: the norm form $s^2 - dt^2$ modulo $8$ -/

section Two

/-- Helper: a form of discriminant $4d$ has even middle coefficient $b = 2b'$ with $b'^2 - ac = d$. -/
theorem exists_half_b {f : BinQF} {d : ℤ} (hf : f.disc = 4 * d) :
    ∃ b' : ℤ, f.b = 2 * b' ∧ b' ^ 2 - f.a * f.c = d := by
  have hd : f.b ^ 2 - 4 * f.a * f.c = 4 * d := hf
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' f.b
  · refine ⟨m, hm, ?_⟩
    rw [hm] at hd
    linarith
  · exfalso
    rw [hm] at hd
    obtain ⟨X, hX⟩ : ∃ X : ℤ, 4 * X = 1 := ⟨d - m ^ 2 - m + f.a * f.c, by linear_combination -hd⟩
    omega

/-- Helper: for $b = 2b'$, $b'^2 - ac = d$: $a f(X, Y) = (aX + b'Y)^2 - dY^2$. -/
theorem mul_eval_eq {f : BinQF} {b' d : ℤ} (hb : f.b = 2 * b') (hd : b' ^ 2 - f.a * f.c = d) (X Y : ℤ) :
    f.a * f.eval X Y = (f.a * X + b' * Y) ^ 2 - d * Y ^ 2 := by
  rw [BinQF.eval_eq, hb, ← hd]; ring

/-- Helper ($p = 2$, necessity): if $f \cong g$ over $\mathbb Z_2$ (disc $4d$), then $a_fa_g \equiv s^2 - dt^2
\pmod 8$ for some integers $s, t$. -/
theorem exists_norm_of_isometricGL_two {f g : BinQF} {d : ℤ} (hg : g.disc = 4 * d)
    (h : IsometricGL (f.map (Int.castRingHom ℤ_[2])) (g.map (Int.castRingHom ℤ_[2]))) :
    ∃ s t : ℤ, (8 : ℤ) ∣ f.a * g.a - (s ^ 2 - d * t ^ 2) := by
  obtain ⟨X, Y, hXY⟩ := exists_int_rep_of_isometricGL (p := 2) 3 h
  obtain ⟨b', hb, hd⟩ := exists_half_b hg
  refine ⟨g.a * X + b' * Y, Y, ?_⟩
  have := mul_eval_eq hb hd X Y
  have e : f.a * g.a - ((g.a * X + b' * Y) ^ 2 - d * Y ^ 2) = -(g.a * (g.eval X Y - f.a)) := by
    rw [← this]; ring
  rw [e]
  have h8 : (8 : ℤ) ∣ g.eval X Y - f.a := by exact_mod_cast hXY
  exact (Dvd.dvd.mul_left h8 _).neg_right

/-- Helper ($p = 2$, sufficiency): if $a_f, a_g$ are odd, both forms have discriminant $4d$, and
$a_fa_g \equiv s^2 - dt^2 \pmod 8$, then $f \cong g$ over $\mathbb Z_2$. (The form $g$ represents
$n = g(a_g(s - b't), t) \equiv a_f \pmod 8$, so $a_f n \equiv 1 \pmod 8$ is a $2$-adic square.) -/
theorem isometricGL_two_of_norm {f g : BinQF} {d : ℤ} (hf : f.disc = 4 * d) (hg : g.disc = 4 * d)
    (hfa : ¬ (2 : ℤ) ∣ f.a) (hga : ¬ (2 : ℤ) ∣ g.a) {s t : ℤ}
    (h8 : (8 : ℤ) ∣ f.a * g.a - (s ^ 2 - d * t ^ 2)) :
    IsometricGL (f.map (Int.castRingHom ℤ_[2])) (g.map (Int.castRingHom ℤ_[2])) := by
  obtain ⟨b', hb, hd⟩ := exists_half_b hg
  set x : ℤ := g.a * (s - b' * t) with hx
  have hid := mul_eval_eq hb hd x t
  have hga2 : ((g.a : ℤ) : ZMod 8) ^ 2 = 1 := sq_odd_zmod8 hga
  have hfa2 : ((f.a : ℤ) : ZMod 8) ^ 2 = 1 := sq_odd_zmod8 hfa
  have h8' : ((f.a : ZMod 8)) * (g.a : ZMod 8) = (s : ZMod 8) ^ 2 - (d : ZMod 8) * (t : ZMod 8) ^ 2 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (f.a * g.a - (s ^ 2 - d * t ^ 2)) 8).mpr (by exact_mod_cast h8)
    push_cast at this
    exact sub_eq_zero.mp this
  have hn8 : ((g.eval x t : ℤ) : ZMod 8) = (f.a : ZMod 8) := by
    have h1 : (g.a : ZMod 8) * ((g.eval x t : ℤ) : ZMod 8) = (s : ZMod 8) ^ 2 - (d : ZMod 8) * (t : ZMod 8) ^ 2 := by
      have := congrArg (Int.cast : ℤ → ZMod 8) hid
      push_cast at this
      rw [this, hx]; push_cast
      linear_combination (((s : ZMod 8) - b' * t) * (2 * s + ((g.a : ZMod 8) ^ 2 - 1) * ((s : ZMod 8) - b' * t))) *
        hga2
    linear_combination (g.a : ZMod 8) * h1 - (g.a : ZMod 8) * h8' - ((g.eval x t : ℤ) : ZMod 8) * hga2 +
      (f.a : ZMod 8) * hga2
  have hdiv : (8 : ℤ) ∣ f.a - g.eval x t := by
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub (g.eval x t) f.a 8).mp hn8
    exact_mod_cast this
  have hn : ¬ (2 : ℤ) ∣ g.eval x t := by omega
  have hc : ((f.a * g.eval x t : ℤ) : ZMod 8) = 1 := by
    push_cast; rw [hn8, ← sq]; exact hfa2
  obtain ⟨z, hz⟩ := exists_sq_padic_two hc
  exact isometricGL_of_rep (p := 2) (hf.trans hg.symm) (by exact_mod_cast hfa) (by exact_mod_cast hn) hz

/-- Helper: the norm forms $s^2 - dt^2$ are multiplicative modulo $8$ (exactly, in fact). -/
theorem norm_mul_mod {d α₁ β₁ α₂ β₂ s₁ t₁ s₂ t₂ : ℤ} (h₁ : (8 : ℤ) ∣ α₁ * β₁ - (s₁ ^ 2 - d * t₁ ^ 2))
    (h₂ : (8 : ℤ) ∣ α₂ * β₂ - (s₂ ^ 2 - d * t₂ ^ 2)) :
    (8 : ℤ) ∣ (α₁ * α₂) * (β₁ * β₂) - ((s₁ * s₂ + d * t₁ * t₂) ^ 2 - d * (s₁ * t₂ + s₂ * t₁) ^ 2) := by
  obtain ⟨u, hu⟩ := h₁
  obtain ⟨v, hv⟩ := h₂
  exact ⟨u * (α₂ * β₂) + (s₁ ^ 2 - d * t₁ ^ 2) * v, by
    linear_combination (α₂ * β₂) * hu + (s₁ ^ 2 - d * t₁ ^ 2) * hv⟩

end Two

/-! ### Assembly -/

section Assembly

variable {D : ℤ} [NonzeroDisc D]

/-- Helper: an integer coprime to the prime $p$ is not divisible by $p$. -/
theorem not_dvd_of_isCoprime {p : ℕ} [Fact p.Prime] {n : ℤ} (h : IsCoprime n (p : ℤ)) : ¬ (p : ℤ) ∣ n := by
  intro hd
  have hu := h.isUnit_of_dvd' hd (dvd_refl _)
  rw [Int.isUnit_iff] at hu
  have := (Fact.out : p.Prime).one_lt
  omega

/-- Helper ($p = 2$, $D$ odd): any two integral forms of the odd discriminant $D$ with odd first coefficients are
$\mathbb Z_2$-equivalent (Cassels, Ch. 14, Lemma 3.3 (i): $\mathcal G_2$ is trivial for $D$ odd, `card_two_odd`). -/
theorem isometricGL_two_of_odd_disc (hD : D % 2 = 1) {f g : BinQF} (hf : f.disc = D) (hg : g.disc = D)
    (hfa : ¬ (2 : ℤ) ∣ f.a) (hga : ¬ (2 : ℤ) ∣ g.a) :
    IsometricGL (f.map (Int.castRingHom ℤ_[2])) (g.map (Int.castRingHom ℤ_[2])) := by
  have hcard := card_two_odd (NonzeroDisc.mod_four (D := D)) hD
  have hsub : Subsingleton (LocalClasses 2 D) := (Nat.card_eq_one_iff_unique.mp hcard).1
  let mkL : ∀ h : BinQF, h.disc = D → ¬ (2 : ℤ) ∣ h.a → LocalPrimForm 2 D := fun h hh hha =>
    ⟨h.map (Int.castRingHom ℤ_[2]), Or.inl (isUnit_intCast_padic (p := 2) (by exact_mod_cast hha)), by
      rw [neg_det_map_int h (Int.castRingHom ℤ_[2]), hh]; simp⟩
  exact Quotient.exact (hsub.elim (Quotient.mk (localSetoid 2 D) (mkL f hf hfa) : LocalClasses 2 D)
    (Quotient.mk (localSetoid 2 D) (mkL g hg hga) : LocalClasses 2 D))

/-- Helper: the key local step. Let $(f_1, f_2)$ and $(g_1, g_2)$ be concordant pairs of primitive forms of
discriminant $D$ with $a_1a_2$ and $b_1b_2$ prime to $p$ (the first coefficients), and $f_j \cong g_j$ over
$\mathbb Z_p$. Then the compositions are $\mathbb Z_p$-equivalent. -/
theorem isometricGL_comp_local (p : ℕ) [Fact p.Prime] (f₁ f₂ g₁ g₂ : PrimForm D)
    (hf : Concordant f₁.1 f₂.1) (hg : Concordant g₁.1 g₂.1)
    (hpf : ¬ (p : ℤ) ∣ f₁.1.a * f₂.1.a) (hpg : ¬ (p : ℤ) ∣ g₁.1.a * g₂.1.a)
    (h₁ : IsometricGL (f₁.1.map (Int.castRingHom ℤ_[p])) (g₁.1.map (Int.castRingHom ℤ_[p])))
    (h₂ : IsometricGL (f₂.1.map (Int.castRingHom ℤ_[p])) (g₂.1.map (Int.castRingHom ℤ_[p]))) :
    IsometricGL ((PrimForm.comp f₁ f₂ hf).1.map (Int.castRingHom ℤ_[p]))
      ((PrimForm.comp g₁ g₂ hg).1.map (Int.castRingHom ℤ_[p])) := by
  have hf1 : ¬ (p : ℤ) ∣ f₁.1.a := fun h => hpf (dvd_mul_of_dvd_left h _)
  have hf2 : ¬ (p : ℤ) ∣ f₂.1.a := fun h => hpf (dvd_mul_of_dvd_right h _)
  have hg1 : ¬ (p : ℤ) ∣ g₁.1.a := fun h => hpg (dvd_mul_of_dvd_left h _)
  have hg2 : ¬ (p : ℤ) ∣ g₂.1.a := fun h => hpg (dvd_mul_of_dvd_right h _)
  have haF : (PrimForm.comp f₁ f₂ hf).1.a = f₁.1.a * f₂.1.a := primComp_a _ _ _
  have haG : (PrimForm.comp g₁ g₂ hg).1.a = g₁.1.a * g₂.1.a := primComp_a _ _ _
  have hdF : (PrimForm.comp f₁ f₂ hf).1.disc = D := (PrimForm.comp f₁ f₂ hf).2.2
  have hdG : (PrimForm.comp g₁ g₂ hg).1.disc = D := (PrimForm.comp g₁ g₂ hg).2.2
  rcases eq_or_ne p 2 with rfl | hp2
  · have o1 : ¬ (2 : ℤ) ∣ f₁.1.a := by exact_mod_cast hf1
    have o2 : ¬ (2 : ℤ) ∣ f₂.1.a := by exact_mod_cast hf2
    have o3 : ¬ (2 : ℤ) ∣ g₁.1.a := by exact_mod_cast hg1
    have o4 : ¬ (2 : ℤ) ∣ g₂.1.a := by exact_mod_cast hg2
    have oF : ¬ (2 : ℤ) ∣ (PrimForm.comp f₁ f₂ hf).1.a := by
      rw [haF]; exact fun h => (Int.prime_two.dvd_mul.mp h).elim o1 o2
    have oG : ¬ (2 : ℤ) ∣ (PrimForm.comp g₁ g₂ hg).1.a := by
      rw [haG]; exact fun h => (Int.prime_two.dvd_mul.mp h).elim o3 o4
    by_cases hD : D % 2 = 1
    · exact isometricGL_two_of_odd_disc hD hdF hdG oF oG
    · obtain ⟨d, hd⟩ : ∃ d, D = 4 * d := ⟨D / 4, by have := NonzeroDisc.mod_four (D := D); omega⟩
      obtain ⟨s₁, t₁, e₁⟩ := exists_norm_of_isometricGL_two (d := d) (by rw [g₁.2.2, hd]) h₁
      obtain ⟨s₂, t₂, e₂⟩ := exists_norm_of_isometricGL_two (d := d) (by rw [g₂.2.2, hd]) h₂
      exact isometricGL_two_of_norm (hdF.trans hd) (hdG.trans hd) oF oG (by
        rw [haF, haG]; exact norm_mul_mod e₁ e₂)
  · by_cases hpD : (p : ℤ) ∣ D
    · obtain ⟨z₁, hz₁⟩ := exists_sq_of_isometricGL_odd hp2 (f₁.2.2.trans g₁.2.2.symm)
        (by rw [f₁.2.2]; exact hpD) hf1 hg1 h₁
      obtain ⟨z₂, hz₂⟩ := exists_sq_of_isometricGL_odd hp2 (f₂.2.2.trans g₂.2.2.symm)
        (by rw [f₂.2.2]; exact hpD) hf2 hg2 h₂
      refine isometricGL_padic_of_sq (hdF.trans hdG.symm) (by rw [haF]; exact hpf) (by rw [haG]; exact hpg)
        (z := z₁ * z₂) ?_
      rw [mul_pow, hz₁, hz₂, haF, haG]; push_cast; ring
    · exact isometricGL_padic_of_not_dvd hp2 (hdF.trans hdG.symm) (by rw [hdF]; exact hpD)

/-- **Cassels, Ch. 14, §3, p. 339, (3.1): the $\mathbb Z_p$-class of a composition depends only on the
$\mathbb Z_p$-classes of the factors.** For every prime $p$ and every $D$ with `[NonzeroDisc D]`: if $f_1 \sim g_1$ and
$f_2 \sim g_2$ over $\mathbb Z_p$ (primitive forms of discriminant $D$) and $F, G$ represent the compositions of the
classes of $f_1, f_2$ and of $g_1, g_2$, then $F \sim G$ over $\mathbb Z_p$.

Proof (local, following Cassels' "mimicking the argument of Section 2"): choose concordant representatives
$[a_1, b, *], [a_2, b, *] \in \mathfrak C(f_1)\mathfrak C(f_2)$ with $a_1a_2$ prime to $p$ (Lemma 2.3), and likewise
$[\alpha_1, \beta, *], [\alpha_2, \beta, *]$ for $g_1, g_2$. The compositions are $[a_1a_2, b, *]$ and
$[\alpha_1\alpha_2, \beta, *]$. For $p$ odd with $p \nmid D$ all forms are equivalent (Lemma 3.1 (i)); for $p$ odd with
$p \mid D$, $f_j \sim g_j$ forces $a_j\alpha_j$ to be a $p$-adic square (reduce $4\alpha_j\, g_j(X, Y) = (2\alpha_jX +
\beta Y)^2 - DY^2$ modulo $p$), hence so is $a_1a_2\alpha_1\alpha_2$, which gives the equivalence of the compositions
(`Binary.isometricGL_padic_of_sq`). For $p = 2$ with $D$ odd all forms are equivalent (Lemma 3.3 (i)); for
$D = 4d$, $f \sim g$ with odd first coefficients holds iff $a_f a_g \equiv s^2 - dt^2 \pmod 8$ for some integers
$s, t$ (`exists_norm_of_isometricGL_two`, `isometricGL_two_of_norm`), and the norm forms $s^2 - dt^2$ are closed under
multiplication. -/
@[kb "cassels1978" "Ch. 14, §3, p. 339, (3.1) (proved: composition is well defined on ℤ_p-classes)"]
theorem localCompositionWellDefined (p : ℕ) [Fact p.Prime] (D : ℤ) [NonzeroDisc D] :
    LocalCompositionWellDefined p D where
  compat := by
    intro f₁ f₂ g₁ g₂ F G h₁ h₂ hF hG
    have hp0 : ((p : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hD0 : f₁.1.disc ≠ 0 := by rw [f₁.2.2]; exact NonzeroDisc.ne_zero
    have hD0' : g₁.1.disc ≠ 0 := by rw [g₁.2.2]; exact NonzeroDisc.ne_zero
    obtain ⟨a₁, a₂, e₁, e₂, hc, -, hcop⟩ := exists_concordant f₁.2.1 f₂.2.1 (f₁.2.2.trans f₂.2.2.symm) hD0 hp0
    obtain ⟨b₁, b₂, e₃, e₄, hc', -, hcop'⟩ := exists_concordant g₁.2.1 g₂.2.1 (g₁.2.2.trans g₂.2.2.symm) hD0' hp0
    set f₁' : PrimForm D := ofEquiv f₁ e₁ with hf₁'
    set f₂' : PrimForm D := ofEquiv f₂ e₂ with hf₂'
    set g₁' : PrimForm D := ofEquiv g₁ e₃ with hg₁'
    set g₂' : PrimForm D := ofEquiv g₂ e₄ with hg₂'
    have v₁ : f₁'.1 = a₁ := val_ofEquiv f₁ e₁
    have v₂ : f₂'.1 = a₂ := val_ofEquiv f₂ e₂
    have v₃ : g₁'.1 = b₁ := val_ofEquiv g₁ e₃
    have v₄ : g₂'.1 = b₂ := val_ofEquiv g₂ e₄
    have hcf : Concordant f₁'.1 f₂'.1 := by rw [v₁, v₂]; exact hc
    have hcg : Concordant g₁'.1 g₂'.1 := by rw [v₃, v₄]; exact hc'
    have hpf : ¬ (p : ℤ) ∣ f₁'.1.a * f₂'.1.a := by
      rw [v₁, v₂]; exact not_dvd_of_isCoprime hcop
    have hpg : ¬ (p : ℤ) ∣ g₁'.1.a * g₂'.1.a := by
      rw [v₃, v₄]; exact not_dvd_of_isCoprime hcop'
    have toGL : ∀ {u v : BinQF}, SLEquiv u v →
        IsometricGL (u.map (Int.castRingHom ℤ_[p])) (v.map (Int.castRingHom ℤ_[p])) :=
      fun h => IsometricGL.map (Int.castRingHom ℤ_[p]) (SLEquiv.intEquiv h)
    have k₁ : IsometricGL (f₁'.1.map (Int.castRingHom ℤ_[p])) (g₁'.1.map (Int.castRingHom ℤ_[p])) := by
      refine (toGL (v₁ ▸ e₁)).symm.trans (h₁.trans ?_)
      exact toGL (v₃ ▸ e₃)
    have k₂ : IsometricGL (f₂'.1.map (Int.castRingHom ℤ_[p])) (g₂'.1.map (Int.castRingHom ℤ_[p])) := by
      refine (toGL (v₂ ▸ e₂)).symm.trans (h₂.trans ?_)
      exact toGL (v₄ ▸ e₄)
    have hF' : mk F = mk (PrimForm.comp f₁' f₂' hcf) :=
      calc mk F = mk f₁ * mk f₂ := hF
        _ = mk f₁' * mk f₂' := by rw [hf₁', hf₂', mk_ofEquiv, mk_ofEquiv]
        _ = _ := mk_mul_mk _ _ hcf
    have hG' : mk G = mk (PrimForm.comp g₁' g₂' hcg) :=
      calc mk G = mk g₁ * mk g₂ := hG
        _ = mk g₁' * mk g₂' := by rw [hg₁', hg₂', mk_ofEquiv, mk_ofEquiv]
        _ = _ := mk_mul_mk _ _ hcg
    exact (toGL (mk_eq_mk.1 hF')).trans
      ((isometricGL_comp_local p f₁' f₂' g₁' g₂' hcf hcg hpf hpg k₁ k₂).trans (toGL (mk_eq_mk.1 hG')).symm)

/-- **The $\mathbb Z_p$-class of a square is the principal class** (Cassels, Ch. 14, §3, p. 339: every element of
$\mathcal G_p$ in the image of $\mathcal G$ has order at most $2$), *unconditionally*: if $\mathfrak C(F) =
\mathfrak C(f)^2$ then $F \sim$ the principal form of discriminant $D$ over $\mathbb Z_p$. This is
`isometricGL_principal_of_sq` with its hypothesis `LocalCompositionWellDefined p D` discharged by
`localCompositionWellDefined`. -/
@[kb "cassels1978" "Ch. 14, §3, p. 339 (elements of 𝒢_p have order ≤ 2; proved)"]
theorem isometricGL_principal_of_sq_proved {p : ℕ} [Fact p.Prime] {D : ℤ} [NonzeroDisc D] (f F : PrimForm D)
    (hF : mk F = mk f ^ 2) :
    IsometricGL (F.1.map (Int.castRingHom ℤ_[p])) ((principal D).1.map (Int.castRingHom ℤ_[p])) :=
  isometricGL_principal_of_sq (localCompositionWellDefined p D) f F hF

end Assembly

end QuadFormsKB.Composition
