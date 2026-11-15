/-
# Chenevier–Lannes, §5.2–§5.3: the eigenvalue on $[E_8 \oplus E_8] - [E_{16}]$ and proper neighbours of Leech


Source: Chenevier–Lannes 2019 (`chenevierlannes2019`), §5.2, Theorem 5.2.2 (i), p. 127; §5.3, the definition of proper
neighbours and Corollary 5.3.2, p. 130, with the remark on Lehmer's conjecture after it. Printed page numbers.

**Layer.** Lattices are integral forms on $\mathbb{Z}^n$; the $p$-neighbours of $L = \mathbb{Z}^n$ (for $p$ prime) are
the lattices of `neighbors Q p`, their classes `nbClass`, and $N_p(L, M)$ is `nbCount Q p (classOf M)` (the library's
Kneser neighbours, `Siegel/Neighbors.lean`); $\tau$ is `ramanujanTau` (the coefficients of $\Delta$);
`TheoremA` is the matrix of $T_p$ on $\mathbb{Z}[X_{16}]$.

**Proves.**
- `thm_5_2_2_i` (Theorem 5.2.2 (i)): **conditional** on `TheoremA`, $[E_8 \oplus E_8] - [E_{16}]$ is an eigenvector of
  $T_p$ with eigenvalue $p^4\frac{p^7 - 1}{p - 1} + p^7 + \tau(p)\frac{p^4 - 1}{p - 1}$. (The book proves (i) and (ii)
  equivalent by the Eichler relations and gets (ii) from Ikeda's lift; both are out of reach here. Theorem A is the
  book's Chapter 1 form of the same fact.)
- `IsProperNbr`, `properNbNum`, `improperNbNum` (§5.3, p. 130: proper $p$-neighbours and $N_p^{\pm}$), and
  `isProperNbr_of_improper_aut` (p. 130: if $L$ has an isometry of determinant $-1$, every $p$-neighbour isometric to
  $L$ by an isometry of $V$ is proper), unconditional.
- `lehmer_iff_proper_ne` (p. 130): **conditional** on `LeechProperNeighbors` (Corollary 5.3.2, stated),
  $\tau(p) \ne 0$ for every prime $p$ if and only if $N_p^+(\mathrm{Leech}, \mathrm{Leech}) \ne
  N_p^-(\mathrm{Leech}, \mathrm{Leech})$ for every prime $p$.

**States** `LeechProperNeighbors` (Corollary 5.3.2): $N_p^+ - N_p^- = \tau(p)\frac{p^{12} - 1}{p - 1}$ for the Leech
lattice; the book deduces it from Proposition 5.3.1 (the eigenvalue of $T_p$ on $M_{\det}(\mathrm{O}_{24})$, proved in
§7.5 with Arthur's multiplicity formula), which is out of reach.
-/
import QuadFormsKB.Literature.ChenevierLannes.TheoremsAB

open Matrix

namespace QuadFormsKB.ChenevierLannes

open QuadFormsKB.Siegel QuadFormsKB.Siegel.Kneser QuadFormsKB.Lattices

variable {n : ℕ}

/-! ### Theorem 5.2.2 (i) -/

/-- The eigenvalue of Theorem 5.2.2 (i): $p^4\frac{p^7 - 1}{p - 1} + p^7 + \tau(p)\frac{p^4 - 1}{p - 1}$, written
without division as $\sum_{m=4}^{10} p^m + p^7 + \tau(p)(1 + p + p^2 + p^3)$. -/
noncomputable def thm522Eigen (p : ℕ) : ℂ :=
  ∑ m ∈ Finset.Ico 4 11, (p : ℂ) ^ m + (p : ℂ) ^ 7 + ramanujanTau p * (1 + p + p ^ 2 + p ^ 3)

/-- **Theorem 5.2.2 (i)** (Chenevier–Lannes, p. 127): **conditional** on `TheoremA`. For every prime $p$, the element
$[E_8 \oplus E_8] - [E_{16}]$ of $\mathbb{Z}[X_{16}]$ is an eigenvector of $T_p$ ($T_p[x] = \sum_y N_p(x, y)[y]$) with
eigenvalue $\lambda_p = p^4\frac{p^7 - 1}{p - 1} + p^7 + \tau(p)\frac{p^4 - 1}{p - 1}$ (`thm522Eigen`): the coefficient
of $[E_8 \oplus E_8]$ in $T_p([E_8 \oplus E_8] - [E_{16}])$ is $N_p(E_8^2, E_8^2) - N_p(E_{16}, E_8^2) = \lambda_p$ and
that of $[E_{16}]$ is $N_p(E_8^2, E_{16}) - N_p(E_{16}, E_{16}) = -\lambda_p$. -/
@[kb "chenevierlannes2019" "Thm. 5.2.2 (i), p. 127 (conditional on Thm. A)"]
theorem thm_5_2_2_i (hA : TheoremA) (p : ℕ) [Fact p.Prime] :
    (nbCount twoE8 p (classOf twoE8) : ℂ) - nbCount gamma16 p (classOf twoE8) = thm522Eigen p ∧
      (nbCount twoE8 p (classOf gamma16) : ℂ) - nbCount gamma16 p (classOf gamma16) = -thm522Eigen p := by
  obtain ⟨h1, h2, h3, h4⟩ := hA p
  have hc : (cn 16 p : ℂ) - 691 * thmAScalar p = thm522Eigen p := by
    simp only [cn, thmAScalar, thm522Eigen, Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ,
      Finset.sum_range_zero]
    push_cast
    ring
  constructor
  · rw [h1, h3, ← hc]; ring
  · rw [h2, h4, ← hc]; ring

/-! ### Proper neighbours and Corollary 5.3.2 -/

/-- The image $g(M)$ of a lattice $M \subset \mathbb{Q}^n$ under a rational matrix $g$. -/
def latImage (g : Matrix (Fin n) (Fin n) ℚ) (M : Submodule ℤ (Fin n → ℚ)) : Submodule ℤ (Fin n → ℚ) :=
  M.map ((Matrix.toLin' g).restrictScalars ℤ)

/-- $g$ is an isometry of $V = \mathbb{Q}^n$ for $Q$: $q(gx) = q(x)$. -/
def IsIsometryQ (Q : QuadForm ℤ n) (g : Matrix (Fin n) (Fin n) ℚ) : Prop := ∀ x, Q.evalIn ℚ (g *ᵥ x) = Q.evalIn ℚ x

/-- **Proper neighbours** (Chenevier–Lannes, §5.3, p. 130): a $p$-neighbour $M$ of $L = \mathbb{Z}^n$ is *proper* if
some $g \in \mathrm{SO}(V)$ has $g(M) = L$. (An isometry $g$ with $g(M) = L$ is rational, since $M$ spans
$V = \mathbb{Q}^n$; so $V = \mathbb{Q}^n$ is used instead of $\mathbb{R}^n$.) -/
@[kb "chenevierlannes2019" "§5.3, p. 130 (proper p-neighbours)"]
def IsProperNbr (Q : QuadForm ℤ n) (M : Submodule ℤ (Fin n → ℚ)) : Prop :=
  ∃ g : Matrix (Fin n) (Fin n) ℚ, g.det = 1 ∧ IsIsometryQ Q g ∧ latImage g M = stdLat n

/-- **$N_p^+(L, L)$** (Chenevier–Lannes, p. 130): the number of proper $p$-neighbours of $L = \mathbb{Z}^n$ isometric to
$L$. -/
@[kb "chenevierlannes2019" "§5.3, p. 130 (N_p^+)"]
noncomputable def properNbNum (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] : ℕ := by
  classical
  exact ((neighbors Q p).filter fun M => nbClass Q M = classOf Q ∧ IsProperNbr Q M).card

/-- **$N_p^-(L, L) = N_p(L, L) - N_p^+(L, L)$** (Chenevier–Lannes, p. 130). -/
@[kb "chenevierlannes2019" "§5.3, p. 130 (N_p^-)"]
noncomputable def improperNbNum (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] : ℕ :=
  nbCount Q p (classOf Q) - properNbNum Q p

theorem latImage_mul (g h : Matrix (Fin n) (Fin n) ℚ) (M : Submodule ℤ (Fin n → ℚ)) :
    latImage (g * h) M = latImage g (latImage h M) := by
  unfold latImage
  rw [← Submodule.map_comp]
  congr 1
  ext x
  simp [Matrix.toLin'_mul]

/-- **Neighbours of a lattice with an improper automorphism** (Chenevier–Lannes, p. 130: "If $L$ has an isometry of
determinant $-1$, all its $p$-neighbors are proper"): if some $\sigma$ with $\det\sigma = -1$ is an isometry of $V$
with $\sigma(L) = L$, then every lattice $M$ with $g(M) = L$ for an isometry $g$ of determinant $\pm 1$ is a proper
neighbour. Unconditional. -/
@[kb "chenevierlannes2019" "§5.3, p. 130 (improper automorphism: all neighbours proper)"]
theorem isProperNbr_of_improper_aut {Q : QuadForm ℤ n} {σ : Matrix (Fin n) (Fin n) ℚ} (hσ : σ.det = -1)
    (hσQ : IsIsometryQ Q σ) (hσL : latImage σ (stdLat n) = stdLat n) {M : Submodule ℤ (Fin n → ℚ)}
    {g : Matrix (Fin n) (Fin n) ℚ} (hg : g.det = 1 ∨ g.det = -1) (hgQ : IsIsometryQ Q g)
    (hgM : latImage g M = stdLat n) : IsProperNbr Q M := by
  rcases hg with hg | hg
  · exact ⟨g, hg, hgQ, hgM⟩
  · refine ⟨σ * g, by rw [det_mul, hσ, hg]; norm_num, fun x => by rw [← mulVec_mulVec, hσQ, hgQ], ?_⟩
    rw [latImage_mul, hgM, hσL]

/-- $\frac{p^{12} - 1}{p - 1} = \sum_{m < 12} p^m$. -/
noncomputable def geom12 (p : ℕ) : ℂ := ∑ m ∈ Finset.range 12, (p : ℂ) ^ m

/-- **Corollary 5.3.2** (Chenevier–Lannes, p. 130; named statement): for every prime $p$ and the Leech lattice
$L$ (any Niemeier lattice without roots, `IsLeechType`),
$$N_p^+(\mathrm{Leech}, \mathrm{Leech}) - N_p^-(\mathrm{Leech}, \mathrm{Leech}) = \tau(p)\,\frac{p^{12} - 1}{p - 1}.$$
The book deduces it from Proposition 5.3.1 (the eigenvalue of $T_p$ on the line $M_{\det}(\mathrm{O}_{24})$), proved in
§7.5 from Arthur's theory; out of reach here. -/
@[kb "chenevierlannes2019" "Cor. 5.3.2, p. 130"]
def LeechProperNeighbors : Prop :=
  ∀ Q : QuadForm ℤ 24, IsLeechType Q → ∀ (p : ℕ) [Fact p.Prime],
    (properNbNum Q p : ℂ) - improperNbNum Q p = ramanujanTau p * geom12 p

theorem geom12_ne_zero (p : ℕ) : geom12 p ≠ 0 := by
  have : (0 : ℝ) < ∑ m ∈ Finset.range 12, (p : ℝ) ^ m :=
    Finset.sum_pos' (fun m _ => by positivity) ⟨0, by simp, by simp⟩
  intro h
  have h' : ((∑ m ∈ Finset.range 12, (p : ℝ) ^ m : ℝ) : ℂ) = 0 := by
    rw [← h, geom12]; push_cast; rfl
  exact this.ne' (by exact_mod_cast h')

/-- **Lehmer's conjecture and proper neighbours of Leech** (Chenevier–Lannes, p. 130, after Corollary 5.3.2):
**conditional** on `LeechProperNeighbors`. For the Leech lattice, $\tau(p) \ne 0$ for every prime $p$ (Lehmer's
conjecture, restricted to primes) if and only if $N_p^+(\mathrm{Leech}, \mathrm{Leech}) \ne
N_p^-(\mathrm{Leech}, \mathrm{Leech})$ for every prime $p$. -/
@[kb "chenevierlannes2019" "§5.3, p. 130 (Lehmer's conjecture; conditional on Cor. 5.3.2)"]
theorem lehmer_iff_proper_ne (hC : LeechProperNeighbors) {Q : QuadForm ℤ 24} (hQ : IsLeechType Q) :
    (∀ (p : ℕ) [Fact p.Prime], ramanujanTau p ≠ 0) ↔
      ∀ (p : ℕ) [Fact p.Prime], properNbNum Q p ≠ improperNbNum Q p := by
  constructor
  · intro hτ p _ heq
    have h := hC Q hQ p
    rw [heq, sub_self] at h
    exact mul_ne_zero (hτ p) (geom12_ne_zero p) h.symm
  · intro hN p _ hτ
    have h := hC Q hQ p
    rw [hτ, zero_mul, sub_eq_zero] at h
    exact hN p (by exact_mod_cast h)

end QuadFormsKB.ChenevierLannes
