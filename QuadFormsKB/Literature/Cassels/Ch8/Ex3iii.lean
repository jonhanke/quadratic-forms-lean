/-
# Cassels, Chapter 8, Example 3 (iii): improperly primitive $\mathbb Z_2$-forms with $d(f) = c_2(f) = 1$

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 8, *Examples*, Ex. 3 (iii), p. 125.

**Setting** (as in `Ch8/ExamplesDyadic.lean`, Example 3 (ii)). A form over $\mathbb Z_2$ in $n$ variables
$x_0, \dots, x_{n-1}$ is given by its symmetric matrix $F \in M_n(\mathbb Q_2)$ (classically integral:
$\lvert f_{ij}\rvert_2 \le 1$); `IsImproperlyPrimitive F` says that $f$ is primitive with every diagonal coefficient
$f_{ii} \in 2\mathbb Z_2$.  "$d(f) = 1$" means that $\lvert\det F\rvert_2 = 1$ (the unit-determinant hypothesis of
Example 3 (i)) and that $\det F$ is a square in $\mathbb Q_2$.  "$c_2(f)$" is the Hasse invariant
$\prod_{i<j}(a_i, a_j)_2$ (`PadicClass.hasseVec`) of any diagonalization $F \sim \langle a_0, \dots, a_{n-1}\rangle$
over $\mathbb Q_2$ (`Ex5.QDiag F a`).

**Proves**
* `hasseVec_eq_of_qdiag`: $c_2$ is well defined, i.e. two diagonalizations $a, a'$ of the same $F$ have the same
  Hasse invariant (from `Ex5.qequiv_iff_invariants` applied to `QEquiv.refl`);
* `ex3_iii` (**Example 3 (iii)**): if $f$ is improperly primitive, $d(f) = 1$ and $c_2(f) = 1$, then $8 \mid n$.

**Proof outline.** Lift $F$ to a symmetric $F_z \in M_n(\mathbb Z_2)$ with $\det F_z \in \mathbb Z_2^{\times}$.  Since
every diagonal entry of $F_z$ is even, $\vec 0$ is a characteristic vector ($\vec a^{t}F_z\vec a$ is even for all
$\vec a$, as the off-diagonal terms cancel in pairs mod $2$).  Example 4 (iv) (`Ex5.ex4_iv`) with $\vec b = \vec 0$
gives a diagonalization $a_0$ of $F$ and $s \in \mathbb N$ with $c_2 = (-1)^{s}$ and
$8 \mid -\det F_z - n + 1 - 4s$.  As $\det F_z$ is a unit which is a square in $\mathbb Q_2$, $\det F_z \equiv 1
\pmod 8$.  By well-definedness $(-1)^{s} = c_2(f) = 1$, so $s$ is even, whence $8 \mid n$.  (Example 3 (ii),
$4 \mid n$, is not needed for this route.)
-/
import QuadFormsKB.Literature.Cassels.Ch8.Ex5

open Matrix QuadFormsKB QuadFormsKB.PadicClass

noncomputable section

namespace QuadFormsKB.Cassels

variable {n : ℕ}

/-- **$c_2$ is well defined.** Two diagonalizations $\langle a_i\rangle$, $\langle a'_i\rangle$ of the same
$\mathbb Q_2$-form $F$ have the same Hasse invariant $\prod_{i<j}(a_i,a_j)_2$. -/
theorem hasseVec_eq_of_qdiag {F : Matrix (Fin n) (Fin n) ℚ_[2]} {a a' : Fin n → ℚ_[2]}
    (ha : Ex5.QDiag F a) (ha' : Ex5.QDiag F a') : hasseVec a = hasseVec a' :=
  ((Ex5.qequiv_iff_invariants ha ha').1 (Ex5.QEquiv.refl F)).2

/-- Helper: for a symmetric matrix over $\mathbb Z_2$ with even diagonal, $\vec a^{t}F\vec a$ is even. -/
theorem even_quad_of_even_diag {Fz : Matrix (Fin n) (Fin n) ℤ_[2]} (hs : Fzᵀ = Fz)
    (hd : ∀ i, (2 : ℤ_[2]) ∣ Fz i i) (a : Fin n → ℤ_[2]) : (2 : ℤ_[2]) ∣ a ⬝ᵥ (Fz *ᵥ a) := by
  rw [Ex5.two_dvd_iff_toZMod]
  have e : PadicInt.toZMod (a ⬝ᵥ (Fz *ᵥ a)) =
      ∑ i, ∑ j, PadicInt.toZMod (a i) * PadicInt.toZMod (Fz i j) * PadicInt.toZMod (a j) := by
    simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  set g : Fin n → Fin n → ZMod 2 := fun i j =>
    PadicInt.toZMod (a i) * PadicInt.toZMod (Fz i j) * PadicInt.toZMod (a j) with hg
  have hgs : ∀ i j, g i j = g j i := by
    intro i j
    have : Fz i j = Fz j i := by
      have := congrFun (congrFun hs j) i
      simpa using this
    simp only [hg, this]; ring
  have hgd : ∀ i, g i i = 0 := by
    intro i
    simp only [hg]
    rw [(Ex5.two_dvd_iff_toZMod _).1 (hd i)]; simp
  rw [← Fintype.sum_prod_type' (f := g)]
  have hsplit : ∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)), g p.1 p.2 =
      ∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≠ p.2), g p.1 p.2 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h : p.1 = p.2
    · simp [h, hgd]
    · simp [h]
  rw [hsplit]
  refine Finset.sum_involution (fun p _ => p.swap) ?_ ?_ ?_ ?_
  · intro p _
    have : g p.2 p.1 = g p.1 p.2 := hgs _ _
    simp only [Prod.fst_swap, Prod.snd_swap, this]
    exact CharTwo.add_self_eq_zero _
  · intro p hp _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    intro h
    exact hp (by simpa using (congrArg Prod.fst h).symm)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.fst_swap, Prod.snd_swap] at hp ⊢
    exact fun h => hp h.symm
  · intro p _
    simp

/-- **Cassels, Ch. 8, Example 3 (iii) (p. 125).** Let $f$ be an improperly primitive $\mathbb Z_2$-form in $n$
variables, with symmetric matrix $F$.  If $d(f) = 1$ (that is, $\det F$ is a $2$-adic unit and a square in
$\mathbb Q_2$) and $c_2(f) = 1$ (the Hasse invariant $\prod_{i<j}(a_i,a_j)_2$ of a diagonalization
$F \sim \langle a_0, \dots, a_{n-1}\rangle$ over $\mathbb Q_2$ equals $1$; it is independent of the diagonalization by
`hasseVec_eq_of_qdiag`), then $8 \mid n$. -/
@[kb "cassels1978" "Ch. 8, Ex. 3 (iii), p. 125"]
theorem ex3_iii {F : Matrix (Fin n) (Fin n) ℚ_[2]} (hF : Fᵀ = F) (hFi : IsImproperlyPrimitive F)
    (hu : ‖F.det‖ = 1) (hsq : IsSquare F.det)
    (hc : ∃ a : Fin n → ℚ_[2], Ex5.QDiag F a ∧ hasseVec a = 1) : 8 ∣ n := by
  obtain ⟨Fz, hFz⟩ := dyadic_lift_mat hFi.1.1
  have hdiag : ∀ i, (2 : ℤ_[2]) ∣ Fz i i := by
    intro i
    apply dyadic_two_dvd_of_norm_lt
    have hlt : ‖F i i‖ < 1 :=
      lt_of_le_of_ne (hFi.1.1 i i) (fun hi => hFi.2 ⟨hFi.1, i, hi⟩)
    have : F i i = ((Fz i i : ℤ_[2]) : ℚ_[2]) := by rw [← hFz]; rfl
    rwa [← this]
  have hFzs : Fzᵀ = Fz := by
    ext i j
    have := congrFun (congrFun hF j) i
    rw [← hFz] at this
    exact (by simpa using this.symm)
  have hdet : F.det = ((Fz.det : ℤ_[2]) : ℚ_[2]) := by rw [← hFz, dyadic_det_map_coe]
  have hunit : IsUnit Fz.det := by
    refine PadicInt.isUnit_iff.2 ?_
    rw [hdet] at hu
    simpa using hu
  have hb : ∀ a, (2 : ℤ_[2]) ∣ a ⬝ᵥ (Fz *ᵥ a) - a ⬝ᵥ (Fz *ᵥ (0 : Fin n → ℤ_[2])) := by
    intro a
    simpa using even_quad_of_even_diag hFzs hdiag a
  obtain ⟨a₀, hQ, s, h8, hh⟩ := Ex5.ex4_iv.exists_diag n Fz hFzs hunit 0 hb
  rw [hFz] at hQ
  obtain ⟨a, hQa, hha⟩ := hc
  have hs1 : ((-1 : ℤ)) ^ s = 1 := by
    rw [← hh, hasseVec_eq_of_qdiag hQ hQa, hha]
  obtain ⟨k, hk⟩ : Even s := by
    rcases Nat.even_or_odd s with h | ⟨k, rfl⟩
    · exact h
    · exfalso
      rw [pow_succ, pow_mul] at hs1
      norm_num at hs1
  -- `det Fz ≡ 1 mod 8`
  have hd8 : (8 : ℤ_[2]) ∣ Fz.det - 1 := by
    rw [hdet] at hsq
    have h1 : IsSquare (((hunit.unit : ℤ_[2]) : ℚ_[2])) := by simpa using hsq
    have h2 := (HilbertLocal.isSquare_two_adic_unit_iff hunit.unit).1 h1
    rw [Ex5.eight_dvd_iff, map_sub, map_one, sub_eq_zero]
    simpa using h2
  obtain ⟨c1, hc1⟩ := h8
  obtain ⟨c2, hc2⟩ := hd8
  have hs : (s : ℤ_[2]) = 2 * (k : ℤ_[2]) := by rw [hk]; push_cast; ring
  have e0 : (0 : Fin n → ℤ_[2]) ⬝ᵥ (Fz *ᵥ (0 : Fin n → ℤ_[2])) = 0 := by simp
  rw [e0] at hc1
  have hn : (n : ℤ_[2]) = 8 * (-(c1 + c2 + k)) := by
    linear_combination (-1) * hc1 + (-1) * hc2 + (-4) * hs
  have h8n : (2 : ℤ_[2]) ^ 3 ∣ (n : ℤ_[2]) := ⟨-(c1 + c2 + k), by rw [hn]; norm_num⟩
  have hker : (n : ℤ_[2]) ∈ RingHom.ker (PadicInt.toZModPow (p := 2) 3) := by
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton]; exact h8n
  rw [RingHom.mem_ker, map_natCast] at hker
  have := (ZMod.natCast_eq_zero_iff n (2 ^ 3)).1 hker
  simpa using this

end QuadFormsKB.Cassels

end
