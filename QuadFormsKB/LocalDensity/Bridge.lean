/-
# Bridge: the $\mathbb{Q}$ layer is the DVR layer at $R = \mathbb{Z}_p$

**Layer:** bridge between the $\mathbb{Q}$ layer ($\mathbb{Z}/p^k$ counts, printed Lemma 2.1) and the DVR layer
(general normal form `DVR.IsJordanFormW`). **Proves**, for $Q$ integral and $p$ prime, with
$Q_p = $ `Q.map (Int.castRingHom ℤ_[p])`:
- `isJordanForm_iff_padic`: `IsJordanForm Q p P ν ↔ DVR.IsJordanForm Q_p p P ν` (Hanke 2004, (2.3), p. 355);
- `isJordanForm_iff_isJordanFormW_padic`: `IsJordanForm Q p P ν ↔ DVR.IsJordanFormW Q_p p P ν`;
- `localDensity_eq_padic`: $\beta_p(m)$ over $\mathbb{Z}/p^k$ equals the DVR density over $\mathbb{Z}_p$ ((5.2), p. 368).
So a reader of the $\mathbb{Q}$ layer never needs the general machinery, and the general theory provably
specializes to it. **Depends on** `Padic.lean` (`repCount_eq_padic`, `q_padicInt`) and `DyadicJordan.lean`.
-/
import QuadFormsKB.LocalDensity.Padic

namespace QuadFormsKB.LocalDensity

open QuadForm

variable {n : ℕ}

/-- In $\mathbb{Z}_p$, for an integer $a$: $p^k \mid a$ in $\mathbb{Z}_p$ iff $p^k \mid a$ in $\mathbb{Z}$. -/
theorem padic_pow_dvd_int_iff (p : ℕ) [Fact p.Prime] (k : ℕ) (a : ℤ) :
    (p : ℤ_[p]) ^ k ∣ (a : ℤ_[p]) ↔ (p : ℤ) ^ k ∣ a := by
  rw [PadicInt.pow_p_dvd_int_iff]

/-- In $\mathbb{Z}_p$: $c = p^k b$ with $b$ a unit of $\mathbb{Z}_p$ iff, in $\mathbb{Z}$, $c = p^k b'$ with
$p \nmid b'$ (for an integer $c$). -/
theorem padic_eq_pow_mul_unit_iff (p : ℕ) [Fact p.Prime] (k : ℕ) (c : ℤ) :
    (∃ b : ℤ_[p], (c : ℤ_[p]) = (p : ℤ_[p]) ^ k * b ∧ IsUnit b) ↔
      ∃ b : ℤ, c = (p : ℤ) ^ k * b ∧ ¬ (p : ℤ) ∣ b := by
  have hπ := PadicInt.irreducible_p (p := p)
  constructor
  · rintro ⟨b, hb, hbu⟩
    obtain ⟨b', hb'⟩ := (padic_pow_dvd_int_iff p k c).1 ⟨b, hb⟩
    refine ⟨b', hb', fun hd => ?_⟩
    have hbb : (b' : ℤ_[p]) = b := by
      apply mul_left_cancel₀ (pow_ne_zero k hπ.ne_zero)
      rw [← hb]; exact_mod_cast hb'.symm
    apply DVR.dvr_not_dvd_of_isUnit hπ hbu
    rw [← hbb]
    simpa using (padic_pow_dvd_int_iff p 1 b').2 (by simpa using hd)
  · rintro ⟨b, hb, hbp⟩
    refine ⟨(b : ℤ_[p]), by rw [hb]; push_cast; ring, DVR.dvr_isUnit_of_not_dvd hπ fun hd => hbp ?_⟩
    simpa using (padic_pow_dvd_int_iff p 1 b).1 (by simpa using hd)

/-- **The local normal form over $\mathbb{Z}$ is the one over $\mathbb{Z}_p$** (Hanke 2004, (2.3), p. 355):
`IsJordanForm Q p P ν ↔ DVR.IsJordanForm (Q.map (Int.castRingHom ℤ_[p])) p P ν`. ($\Rightarrow$ is
`isJordanForm_padic`; $\Leftarrow$ uses that $p^k \mid a$ and "$p \nmid a$" mean the same in $\mathbb{Z}$ and
$\mathbb{Z}_p$ for integers $a$, and that $p \mid 2$ in $\mathbb{Z}_p$ forces $p = 2$.) -/
@[kb "hanke2004" "(2.3), p. 355"]
theorem isJordanForm_iff_padic (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] (P : Finset (Fin n × Fin n))
    (ν : Fin n → ℕ) :
    IsJordanForm Q p P ν ↔ DVR.IsJordanForm (Q.map (Int.castRingHom ℤ_[p])) (p : ℤ_[p]) P ν := by
  refine ⟨isJordanForm_padic Q p P ν, fun h => ?_⟩
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  have hc : ∀ i j, (Q.map (Int.castRingHom ℤ_[p])).coeff i j = (Q.coeff i j : ℤ_[p]) := fun i j => by
    simp [QuadForm.map]
  refine ⟨fun hP => ?_, h1, h2, fun i j hij hP => ?_, fun e he => ?_, fun i hi => ?_⟩
  · have h2p : (p : ℤ) ∣ 2 := by
      have := (padic_pow_dvd_int_iff p 1 2).1 (by simpa using h0 hP)
      simpa using this
    have : p ∣ 2 := by exact_mod_cast h2p
    exact (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this
  · have := h3 i j hij hP
    rw [hc] at this
    exact_mod_cast this
  · obtain ⟨hν, hb, d1, d2⟩ := h4 e he
    rw [hc] at hb d1 d2
    exact ⟨hν, (padic_eq_pow_mul_unit_iff p _ _).1 hb, (padic_pow_dvd_int_iff p _ _).1 d1,
      (padic_pow_dvd_int_iff p _ _).1 d2⟩
  · have := h5 i hi
    rw [hc] at this
    exact (padic_eq_pow_mul_unit_iff p _ _).1 this

/-- $p^2 \nmid 2$ in $\mathbb{Z}_p$ (every prime of $\mathbb{Q}$ is at worst unramified dyadic). -/
theorem padicInt_not_sq_dvd_two (p : ℕ) [Fact p.Prime] : ¬ (p : ℤ_[p]) ^ 2 ∣ 2 := fun h =>
  (padicInt_pow_dvd_two p).2 ((pow_dvd_pow _ (by split_ifs <;> omega)).trans h)

/-- **The $\mathbb{Q}$-layer normal form is the general normal form at $\mathbb{Z}_p$** (Hanke 2004, Lemma 2.1,
p. 355): `IsJordanForm Q p P ν ↔ DVR.IsJordanFormW (Q.map (Int.castRingHom ℤ_[p])) p P ν`, with the same
blocks and $\nu = w$ (and $\mu = w$ in every 2-dimensional block). Hence Good, Bad and Zero type
(Def. 3.1), all defined from $S_0 = $ `unimodularCoords ν`, agree in the two layers. -/
@[kb "hanke2004" "Lemma 2.1, p. 355"]
theorem isJordanForm_iff_isJordanFormW_padic (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime]
    (P : Finset (Fin n × Fin n)) (ν : Fin n → ℕ) :
    IsJordanForm Q p P ν ↔ DVR.IsJordanFormW (Q.map (Int.castRingHom ℤ_[p])) (p : ℤ_[p]) P ν :=
  (isJordanForm_iff_padic Q p P ν).trans
    (DVR.isJordanForm_iff_isJordanFormW PadicInt.irreducible_p (padicInt_not_sq_dvd_two p))

/-- **The local density over $\mathbb{Z}/p^k$ is the DVR local density over $\mathbb{Z}_p$** (Hanke 2004, (5.2),
p. 368, corrected): `localDensity Q p m = DVR.localDensity (Q.map (Int.castRingHom ℤ_[p])) p m`. *Proof:* the
sequences agree term by term, $r_{p^k}(m)$ by `repCount_eq_padic` and $q = p$ by `q_padicInt`. -/
@[kb "hanke2004" "(5.2), p. 368"]
theorem localDensity_eq_padic (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] (m : ℤ) :
    localDensity Q p m =
      DVR.localDensity (Q.map (Int.castRingHom ℤ_[p])) (p : ℤ_[p]) (m : ℤ_[p]) := by
  unfold localDensity DVR.localDensity
  congr 1
  funext k
  rw [(repCount_eq_padic Q p ∅ k m).1, q_padicInt]

end QuadFormsKB.LocalDensity
