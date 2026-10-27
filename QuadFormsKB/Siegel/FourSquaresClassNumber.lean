/-
# Class number one for sums of at most five squares

**Proves** the former cited input `FourSquaresClassNumberOne` (`Siegel/FourSquares.lean`): the genus of
$I_4 = x_0^2 + x_1^2 + x_2^2 + x_3^2$ contains exactly one $\mathrm{GL}_4(\mathbb{Z})$-class (`fourSquaresClassNumberOne`), and
more generally the genus of $I_n = x_0^2 + \dots + x_{n-1}^2$ has one class for $n \le 5$ (`genusClasses_sumSq`).
Consequences: `genusRepAvg_Q4'` and `siegelFormula_Q4'` (unconditional versions of `genusRepAvg_Q4`, `siegelFormula_Q4`).

**Proof (elementary).**
1. *Hermite's bound with the classical constant* (`Hermite.exists_hermite_bound`): a positive definite integral symmetric
   $(m+1)\times(m+1)$ matrix $A$ is $\mathrm{GL}_{m+1}(\mathbb{Z})$-congruent to one whose corner entry $h$ satisfies
   $3^{T_m}h^{m+1} \le 4^{T_m}\det A$, $T_m = m(m+1)/2$ (`Hermite.tri`), i.e. $h \le (4/3)^{m/2}(\det A)^{1/(m+1)}$.
   Same induction as `Hermite.exists_reduced` (minimal corner, scaled Schur complement, size reduction), with the sharp
   step $3h^2 \le 4S_{00}$ kept instead of the crude constant `hermC`.
2. *Unimodular lattices of rank $\le 5$* (`Hermite.unimodular_posDef_equiv_one`): if moreover $\det A = 1$ and
   $m + 1 \le 5$, the bound forces $h = 1$; a vector of norm $1$ splits off, $A \cong (1) \oplus S$ with $S$ the Schur
   complement (again unimodular), and induction gives $A \cong I$.
3. *The genus of $I_n$* (`sameGenus_sumSq_intEquiv`): for $Q'$ in the genus of $I_n$, the Hessian $H'$ is
   $\equiv 0 \bmod 2$ (equivalence modulo $2$, `SameGenus.isometricGL_zmod`), so $H' = 2A'$ with $A'$ integral; $\det H'
   = 2^n$ (`SameGenus.det_hessian_eq`) gives $\det A' = 1$, and $Q'$ is positive definite (`SameGenus.posDef`). By step 2,
   $g^{\mathsf T}A'g = I$, i.e. $Q'(g\vec{x}) = I_n(\vec{x})$.

*Sources:* Hermite's bound: Cassels, *Rational Quadratic Forms*, Ch. 9, Lemma 3.2, p. 136 (with $s = 0$ its
constant (3.10) is $\theta^n = (4/3)^{n(n-1)/2}$, the bound of step 1) and Cor. 1, p. 138; Ch. 5, (3.9), p. 73 (Hermite's
constant). Step 2 is Cassels, Ch. 9, Lemma 3.2, Cor. 2, p. 138 (positive definite, $d(f) = 1$, $n \le 5$: $f \cong
x_1^2 + \dots + x_n^2$), with the same proof (*correction:* the locator "Ch. 12, Lemma 1.1" cited earlier is the pair of
inequalities satisfied by a Minkowski-reduced form, p. 255, not Hermite's bound); Conway–Sloane,
*Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15 does **not** state Hermite's bound (checked 2026-10-21); the nearest is §10.1,
pp. 396–397, the Minkowski reduction conditions (46)–(47) ($0 < a_{11} \le a_{22} \le \cdots$, $2|a_{st}| \le a_{ss}$ for $s < t$),
which are the size-reduction inequalities of step 1. Unimodular lattices of small rank: Serre, *A Course in Arithmetic*, Ch. V, §2 [unverified];
Milnor–Husemoller, *Symmetric Bilinear Forms*, Ch. II [unverified]. (The true range of $I_n$ being alone in its genus
is $n \le 7$; the constant here gives $n \le 5$.)
-/
import QuadFormsKB.Siegel.FourSquaresSiegel
import QuadFormsKB.Siegel.GenusFinite

open Matrix

namespace QuadFormsKB.Siegel.Hermite

/-- **Triangular numbers** $T_0 = 0$, $T_{m+1} = T_m + (m+1)$, so $T_m = m(m+1)/2$: the exponent in Hermite's bound. -/
def tri : ℕ → ℕ
  | 0 => 0
  | m + 1 => tri m + (m + 1)

/-- **Hermite's bound with the classical constant $4/3$.** Every positive definite integral symmetric
$(m+1)\times(m+1)$ matrix $A$ (`IsPosDefInt`) is $\mathrm{GL}_{m+1}(\mathbb{Z})$-congruent to $B = g^{\mathsf T}Ag$ with
$$3^{T_m}\,B_{00}^{\,m+1} \le 4^{T_m}\det A, \qquad T_m = \tfrac{m(m+1)}{2}\ (\texttt{tri}),$$
i.e. $B_{00} \le (4/3)^{m/2}(\det A)^{1/(m+1)}$: Cassels, Ch. 9, Lemma 3.2 with $s = 0$, (3.10), p. 136 ($A$ is his
$F = (f_{ij})$, $\det A = d(f)$). ($B_{00}$ is the minimum of $(g^{\mathsf T}Ag)_{00}$ over $\mathrm{GL}_{m+1}(\mathbb{Z})$.)

*Proof:* induction on $m$. Take $h = B_{00}$ minimal (`exists_min`), apply the induction hypothesis to the scaled Schur
complement $S = S(B)$ of size $m$ (with $h^{m}\det A = h\det S$, `det_schur`), and size-reduce: after $B \mapsto
g^{\mathsf T}Bg$, $g = \begin{pmatrix}1 & t^{\mathsf T}\\ 0 & u\end{pmatrix}$, one has $|2B_{01}| \le h \le B_{11}$ and
$hB_{11} - B_{01}^2 = S'_{00}$, so $3h^2 \le 4S'_{00}$. -/
@[kb "cassels1978" "Ch. 9, Lemma 3.2 (s = 0, (3.10)), p. 136, and Cor. 1, p. 138; Ch. 5, (3.9), p. 73; Ch. 12, §2, Thm. 2.1, proof (i), pp. 260–261 (integral matrices)"]
theorem exists_hermite_bound : ∀ (m : ℕ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ), IsPosDefInt A →
    ∃ g : GL (Fin (m + 1)) ℤ, 3 ^ tri m * ((g.valᵀ * A * g.val) 0 0) ^ (m + 1) ≤ 4 ^ tri m * A.det
  | 0, A, _ => ⟨1, by simp [tri]⟩
  | m + 1, A, hA => by
    obtain ⟨g0, hg0⟩ := exists_min A hA
    refine ⟨g0, ?_⟩
    have hA1 : IsPosDefInt (g0.valᵀ * A * g0.val) := hA.conj g0
    have hdet1 : (g0.valᵀ * A * g0.val).det = A.det := det_conj A g0
    have hmin : ∀ g : GL (Fin (m + 1 + 1)) ℤ,
        (g0.valᵀ * A * g0.val) 0 0 ≤ (g.valᵀ * (g0.valᵀ * A * g0.val) * g.val) 0 0 := by
      intro g
      have := hg0 (g0 * g)
      rwa [conj_mul] at this
    rw [← hdet1]
    generalize g0.valᵀ * A * g0.val = A1 at hmin hA1 ⊢
    clear hdet1 hg0
    have hh : 0 < A1 0 0 := hA1.pos00
    have hdS := det_schur A1
    obtain ⟨u, hu⟩ := exists_hermite_bound m (schur A1) hA1.schur
    obtain ⟨t0, ht0⟩ := exists_round (rowT A1 ⬝ᵥ (fun k => u.val k 0)) hh
    have hdetg : IsUnit (blk (fun _ => t0) u.val).det := by
      rw [det_blk]; exact (Matrix.isUnit_iff_isUnit_det _).mp u.isUnit
    set g : GL (Fin (m + 1 + 1)) ℤ := Matrix.nonsingInvUnit _ hdetg with hgdef
    have hgv : g.val = blk (fun _ => t0) u.val := rfl
    have hB := hA1.conj g
    have hB0j : (g.valᵀ * A1 * g.val) 0 (0 : Fin (m + 1)).succ =
        A1 0 0 * t0 + rowT A1 ⬝ᵥ (fun k => u.val k 0) := by
      rw [conj_apply, hgv, blk_col0, blk_colSucc, cons_bilin]; simp
    have hBi0 : (g.valᵀ * A1 * g.val) (0 : Fin (m + 1)).succ 0 =
        A1 0 0 * t0 + (fun k => u.val k 0) ⬝ᵥ colT A1 := by
      rw [conj_apply, hgv, blk_col0, blk_colSucc, cons_bilin]; simp
    have hBij : A1 0 0 * (g.valᵀ * A1 * g.val) (0 : Fin (m + 1)).succ (0 : Fin (m + 1)).succ -
        (g.valᵀ * A1 * g.val) (0 : Fin (m + 1)).succ 0 * (g.valᵀ * A1 * g.val) 0 (0 : Fin (m + 1)).succ =
          (u.valᵀ * schur A1 * u.val) 0 0 := by
      rw [hBi0, hB0j, conj_apply g.val A1 (0 : Fin (m + 1)).succ (0 : Fin (m + 1)).succ, hgv,
        blk_colSucc, cons_bilin, conj_apply u.val, schur_bilin]
      ring
    have hsym : (g.valᵀ * A1 * g.val) (0 : Fin (m + 1)).succ 0 =
        (g.valᵀ * A1 * g.val) 0 (0 : Fin (m + 1)).succ := hB.1.apply 0 (0 : Fin (m + 1)).succ
    clear_value g
    set B := g.valᵀ * A1 * g.val with hBdef
    set U := u.valᵀ * schur A1 * u.val with hUdef
    set h := A1 0 0 with hhdef
    have h11 : h ≤ B (0 : Fin (m + 1)).succ (0 : Fin (m + 1)).succ := by
      have hP : IsUnit ((Equiv.swap (0 : Fin (m + 2)) 1).permMatrix ℤ).det := by
        rw [det_permutation]
        rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap (0 : Fin (m + 2)) 1)) with e | e <;>
          simp [e]
      have := hmin (g * Matrix.nonsingInvUnit _ hP)
      rw [conj_mul, conj_apply] at this
      have e2 : (fun i => (Matrix.nonsingInvUnit _ hP).val i 0) = Pi.single 1 1 := swap_col0 m
      rw [e2, mulVec_single_one] at this
      simpa using this
    have hb : |2 * B 0 (0 : Fin (m + 1)).succ| ≤ h := by rw [hB0j]; exact ht0
    have hsq : (2 * B 0 (0 : Fin (m + 1)).succ) ^ 2 ≤ h ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    have h3 : 3 * h ^ 2 ≤ 4 * U 0 0 := by
      rw [hsym] at hBij
      nlinarith [mul_le_mul_of_nonneg_left h11 hh.le]
    have hp1 : (3 * h ^ 2) ^ (m + 1) ≤ (4 * U 0 0) ^ (m + 1) :=
      pow_le_pow_left₀ (by positivity) h3 _
    rw [mul_pow, mul_pow] at hp1
    have hp2 : 3 ^ tri m * (4 ^ (m + 1) * U 0 0 ^ (m + 1)) ≤ 4 ^ (m + 1) * (4 ^ tri m * (schur A1).det) := by
      nlinarith [hu, pow_pos (show (0 : ℤ) < 4 by norm_num) (m + 1)]
    have key : h ^ (m + 1) * (3 ^ tri (m + 1) * h ^ (m + 1 + 1)) ≤
        h ^ (m + 1) * (4 ^ tri (m + 1) * A1.det) := by
      have q1 : h ^ (m + 1) * (3 ^ tri (m + 1) * h ^ (m + 1 + 1)) =
          h * (3 ^ tri m * (3 ^ (m + 1) * (h ^ 2) ^ (m + 1))) := by
        simp only [tri, pow_add]; ring
      have q2 : h ^ (m + 1) * (4 ^ tri (m + 1) * A1.det) =
          h * (4 ^ (m + 1) * (4 ^ tri m * (schur A1).det)) := by
        simp only [tri, pow_add]
        linear_combination (4 ^ tri m * 4 ^ (m + 1)) * hdS
      rw [q1, q2]
      refine mul_le_mul_of_nonneg_left ?_ hh.le
      calc 3 ^ tri m * (3 ^ (m + 1) * (h ^ 2) ^ (m + 1))
          ≤ 3 ^ tri m * (4 ^ (m + 1) * U 0 0 ^ (m + 1)) :=
            mul_le_mul_of_nonneg_left hp1 (by positivity)
        _ ≤ _ := hp2
    exact le_of_mul_le_mul_left key (by positivity)

/-- **For $\det A = 1$ and size $\le 5$, the minimum is $1$:** some $g \in \mathrm{GL}_{m+1}(\mathbb{Z})$ has
$(g^{\mathsf T}Ag)_{00} = 1$ ($m \le 4$). From Hermite's bound, $3^{T_m}h^{m+1} \le 4^{T_m}$, which fails for $h \ge 2$
when $m \le 4$ ($3^{10}\cdot 2^5 > 4^{10}$). -/
theorem exists_corner_eq_one {m : ℕ} (hm : m ≤ 4) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ)
    (hA : IsPosDefInt A) (hd : A.det = 1) : ∃ g : GL (Fin (m + 1)) ℤ, (g.valᵀ * A * g.val) 0 0 = 1 := by
  obtain ⟨g, hg⟩ := exists_hermite_bound m A hA
  refine ⟨g, ?_⟩
  have hpos := (hA.conj g).pos00
  rw [hd, mul_one] at hg
  by_contra hne
  have h2 : 2 ≤ (g.valᵀ * A * g.val) 0 0 := by omega
  have h3 : (3 : ℤ) ^ tri m * 2 ^ (m + 1) ≤ 4 ^ tri m :=
    le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) h2 _) (by positivity)) hg
  interval_cases m <;> norm_num [tri] at h3

/-- **Unimodular positive definite integral matrices of size $n \le 5$ are trivial:** if $A \in M_n(\mathbb{Z})$ is symmetric,
positive definite (`IsPosDefInt`) and $\det A = 1$, then $g^{\mathsf T}Ag = I_n$ for some $g \in \mathrm{GL}_n(\mathbb{Z})$.
Equivalently, every positive definite unimodular $\mathbb{Z}$-lattice of rank $\le 5$ is $\mathbb{Z}^n$ with the standard
inner product (classically true for $n \le 7$).

*Proof:* induction on $n$. By `exists_corner_eq_one` move a vector of norm $1$ to $e_0$; then the scaled Schur complement
$S$ is the Schur complement itself, $\det S = \det A = 1$ (`det_schur`) and $S$ is positive definite; by induction
$u^{\mathsf T}Su = I$, and $g = \begin{pmatrix}1 & t^{\mathsf T}\\ 0 & u\end{pmatrix}$ with $t_j = -r^{\mathsf T}u_{\ast j}$ clears
the first row and column. -/
@[kb "serre1973" "Ch. V, §2 (unimodular lattices of small rank) [unverified]; omeara1963 §106D, 106:10, p. 330; cassels1978 Ch. 9, Lemma 3.2, Cor. 2, p. 138"]
theorem unimodular_posDef_equiv_one : ∀ (n : ℕ), n ≤ 5 → ∀ (A : Matrix (Fin n) (Fin n) ℤ), IsPosDefInt A →
    A.det = 1 → ∃ g : GL (Fin n) ℤ, g.valᵀ * A * g.val = 1
  | 0, _, A, _, _ => ⟨1, Subsingleton.elim _ _⟩
  | m + 1, hn, A, hA, hd => by
    obtain ⟨g0, hg0⟩ := exists_corner_eq_one (by omega) A hA hd
    have hA1 : IsPosDefInt (g0.valᵀ * A * g0.val) := hA.conj g0
    have hdet1 : (g0.valᵀ * A * g0.val).det = 1 := (det_conj A g0).trans hd
    suffices H : ∃ g : GL (Fin (m + 1)) ℤ, g.valᵀ * (g0.valᵀ * A * g0.val) * g.val = 1 by
      obtain ⟨g, hg⟩ := H
      exact ⟨g0 * g, by rw [conj_mul]; exact hg⟩
    generalize g0.valᵀ * A * g0.val = A1 at hA1 hdet1 hg0
    have hdS := det_schur A1
    rw [hg0, hdet1, one_pow, one_mul, one_mul] at hdS
    obtain ⟨u, hu⟩ := unimodular_posDef_equiv_one m (by omega) (schur A1) hA1.schur hdS.symm
    have hcr := hA1.colT_eq
    set t : Fin m → ℤ := fun j => -(rowT A1 ⬝ᵥ (fun k => u.val k j)) with htdef
    have hdetg : IsUnit (blk t u.val).det := by
      rw [det_blk]; exact (Matrix.isUnit_iff_isUnit_det _).mp u.isUnit
    refine ⟨Matrix.nonsingInvUnit _ hdetg, ?_⟩
    have hgv : (Matrix.nonsingInvUnit _ hdetg).val = blk t u.val := rfl
    generalize Matrix.nonsingInvUnit _ hdetg = g at hgv
    have hB00 : (g.valᵀ * A1 * g.val) 0 0 = 1 := by
      rw [conj_apply, hgv, blk_col0, cons_bilin]; simp [hg0]
    have hB0j : ∀ j : Fin m, (g.valᵀ * A1 * g.val) 0 j.succ = 0 := by
      intro j; rw [conj_apply, hgv, blk_col0, blk_colSucc, cons_bilin]; simp [hg0, htdef]
    have hBi0 : ∀ i : Fin m, (g.valᵀ * A1 * g.val) i.succ 0 = 0 := by
      intro i; rw [conj_apply, hgv, blk_col0, blk_colSucc, cons_bilin]
      simp [hg0, htdef, hcr, dotProduct_comm]
    have hBij : ∀ i j : Fin m, A1 0 0 * (g.valᵀ * A1 * g.val) i.succ j.succ -
        (g.valᵀ * A1 * g.val) i.succ 0 * (g.valᵀ * A1 * g.val) 0 j.succ =
          (u.valᵀ * schur A1 * u.val) i j := by
      intro i j
      rw [conj_apply g.val A1 i.succ 0, conj_apply g.val A1 0 j.succ,
        conj_apply g.val A1 i.succ j.succ, hgv, blk_col0, blk_colSucc, blk_colSucc, cons_bilin,
        cons_bilin, cons_bilin, conj_apply u.val, schur_bilin]
      simp only [dotProduct_zero, zero_dotProduct, mulVec_zero, mul_zero]
      ring
    ext i j
    cases i using Fin.cases with
    | zero => cases j using Fin.cases with
      | zero => rw [hB00, Matrix.one_apply_eq]
      | succ j => rw [hB0j j, Matrix.one_apply_ne (Fin.succ_ne_zero j).symm]
    | succ i => cases j using Fin.cases with
      | zero => rw [hBi0 i, Matrix.one_apply_ne (Fin.succ_ne_zero i)]
      | succ j =>
        have e := hBij i j
        rw [hg0, hB0j, hu, one_mul, mul_zero, sub_zero] at e
        rw [e, Matrix.one_apply, Matrix.one_apply]
        simp [Fin.succ_inj]

end QuadFormsKB.Siegel.Hermite

namespace QuadFormsKB.Siegel

open Hermite

variable {n : ℕ}

/-- **Forms in the genus of $I_n$ are classically integral:** every entry of the Hessian $H'$ of $Q'$ is even. *Proof:*
$Q'$ is equivalent to $I_n$ modulo $2$ (`SameGenus.isometricGL_zmod`), so $H' \equiv g^{\mathsf T}(2I)g \equiv 0 \pmod 2$. -/
theorem SameGenus.two_dvd_hessian_sumSq {Q' : QuadForm ℤ n} (h : SameGenus (sumSq n) Q') (i j : Fin n) :
    2 ∣ Q'.hessian i j := by
  obtain ⟨g, hg⟩ := (h.isometricGL_zmod (c := 2) (by norm_num)).hessian_eq
  rw [hessian_map, hessian_map, hessian_sumSq] at hg
  have h0 : ((2 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)).map (Int.castRingHom (ZMod 2)) = 0 := by
    ext a b
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul, map_mul]
    have h2 : (Int.castRingHom (ZMod 2)) 2 = 0 := by decide
    rw [h2, zero_mul]
  rw [h0, Matrix.mul_zero, Matrix.zero_mul] at hg
  have := congrFun (congrFun hg i) j
  simp only [Matrix.map_apply, Matrix.zero_apply, eq_intCast] at this
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp this.symm

/-- **The genus of $I_n$ is one class for $n \le 5$ (pointwise form):** every $Q'$ in the genus of
$I_n = x_0^2 + \dots + x_{n-1}^2$ is $\mathbb{Z}$-equivalent to $I_n$. *Proof:* $H' = 2A'$ with $A'$ integral
(`SameGenus.two_dvd_hessian_sumSq`), positive definite (`SameGenus.posDef`) and $\det A' = 2^{-n}\det H' = 1$
(`SameGenus.det_hessian_eq`); then `unimodular_posDef_equiv_one` gives $g^{\mathsf T}A'g = I$, i.e. $g^{\mathsf T}H'g = 2I$. -/
theorem sameGenus_sumSq_intEquiv (hn : n ≤ 5) {Q' : QuadForm ℤ n} (h : SameGenus (sumSq n) Q') :
    IntEquiv (sumSq n) Q' := by
  have hQ' : IntQF.PosDef Q' := h.posDef posDef_sumSq
  have hdet : Q'.hessian.det = 2 ^ n := by
    rw [← h.det_hessian_eq posDef_sumSq, hessian_sumSq, det_smul, det_one, Fintype.card_fin, mul_one]
  set A' : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => Q'.hessian i j / 2 with hA'def
  have hHA : Q'.hessian = (2 : ℤ) • A' := by
    ext i j
    simp only [hA'def, Matrix.smul_apply, of_apply, smul_eq_mul]
    exact (Int.mul_ediv_cancel' (h.two_dvd_hessian_sumSq i j)).symm
  have hHp := hessian_isPosDefInt hQ'
  have hApd : IsPosDefInt A' := by
    refine ⟨IsSymm.ext fun i j => ?_, fun x hx => ?_⟩
    · simp only [hA'def, of_apply]; rw [hHp.1.apply i j]
    · have := hHp.2 x hx
      rw [hHA, smul_mulVec, dotProduct_smul, smul_eq_mul] at this
      omega
  have hAd : A'.det = 1 := by
    have := hdet
    rw [hHA, det_smul, Fintype.card_fin] at this
    have h2 : (2 : ℤ) ^ n ≠ 0 := by positivity
    have := mul_left_cancel₀ h2 (this.trans (mul_one _).symm)
    exact this
  obtain ⟨g, hg⟩ := unimodular_posDef_equiv_one n hn A' hApd hAd
  have hgH : g.valᵀ * Q'.hessian * g.val = (sumSq n).hessian := by
    rw [hHA, hessian_sumSq, Matrix.mul_smul, Matrix.smul_mul, hg]
  exact (show IsometricGL Q' (sumSq n) from ⟨g, (eval_mulVec_eq_iff_hessian Q' (sumSq n) g.val).mpr hgH⟩).symm

/-- **Class number one for $x_0^2 + \dots + x_{n-1}^2$, $n \le 5$:** the genus of $I_n$ contains exactly one
$\mathrm{GL}_n(\mathbb{Z})$-class, `genusClasses (sumSq n)` $= \{[I_n]\}$. -/
@[kb "serre1973" "Ch. V, §2 (unimodular lattices of small rank) [unverified]; cassels1978 Ch. 9, Lemma 3.2, Cor. 2, p. 138"]
theorem genusClasses_sumSq (hn : n ≤ 5) : genusClasses (sumSq n) = {classOf (sumSq n)} := by
  ext c
  induction c using Quotient.inductionOn with
  | h Q' =>
    change classOf Q' ∈ _ ↔ classOf Q' ∈ _
    rw [classOf_mem_genusClasses_iff, Set.mem_singleton_iff]
    constructor
    · intro hg
      exact classOf_eq_classOf_iff.mpr (sameGenus_sumSq_intEquiv hn hg).symm
    · intro he
      exact (classOf_mem_genusClasses_iff).mp (he ▸ classOf_self_mem_genusClasses _)

/-- **The sum of four squares has class number one** (proved; discharges the input `FourSquaresClassNumberOne`):
`genusClasses Q4` $= \{[Q_4]\}$ for $Q_4 = x_0^2 + x_1^2 + x_2^2 + x_3^2$. -/
@[kb "hanke2011aws" "§2.7.2, p. 36"]
theorem fourSquaresClassNumberOne : FourSquaresClassNumberOne :=
  ⟨by rw [← sumSq_four]; exact genusClasses_sumSq (by norm_num)⟩

/-- **$a_E(m) = r_{I_4}(m)$ unconditionally** for the sum of four squares (`genusRepAvg_Q4` with
`fourSquaresClassNumberOne`). -/
@[kb "hanke2011aws" "§2.7.2, p. 36"]
theorem genusRepAvg_Q4' (m : ℤ) : genusRepAvg AWS.Q4 m = repNum AWS.Q4 m :=
  genusRepAvg_Q4 fourSquaresClassNumberOne m

/-- **Siegel's formula for $I_4$, unconditionally:** `SiegelFormula AWS.Q4` (`siegelFormula_Q4` with
`fourSquaresClassNumberOne`). -/
@[kb "siegel1935" "Hauptsatz, for x_0^2+x_1^2+x_2^2+x_3^2"]
theorem siegelFormula_Q4' : SiegelFormula AWS.Q4 :=
  siegelFormula_Q4 fourSquaresClassNumberOne

end QuadFormsKB.Siegel
