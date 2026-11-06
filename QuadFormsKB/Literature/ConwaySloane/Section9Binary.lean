/-
# Conway–Sloane, Ch. 15, §9.7, proof of Theorem 21: the case $n = 2$

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.7, p. 395
(`conwaysloane1999`).

**Layer:** symmetric integer Gram matrices $A$ of size $2$, congruence over $\mathbb Z$ (`CongrIn ℤ`), the genus
`Siegel.SameGenus` and the class `Siegel.IntEquiv`.

**Proves**
* `congrIn_normal_of_det_eq_neg_one`: a symmetric integral $2 \times 2$ matrix of determinant $-1$ is congruent over
  $\mathbb Z$ to $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ if both diagonal entries are even, and to
  $\mathrm{diag}(1,-1)$ otherwise (Euclidean descent on $\lvert a\rvert$);
* `even_diag_of_sameGenus`: "both diagonal entries even" (the form takes only even values) is a genus invariant
  (use of the $\mathbb Z_2$ component);
* `not_moreThanOneClass_of_det_eq_neg_one`: a binary form of determinant $-1$ has only one class in its genus. This
  is the case $n = 2$, $d = -1$ of the proof of Theorem 21, where the book says that for $n = 2$ one has $d \neq \pm1$
  "or else there is only one class in the genus";
* `det_neg_of_isIndefinite`: an indefinite binary form with $\det A \neq 0$ has $\det A < 0$;
  `not_isIndefinite_of_le_one`: a nondegenerate form in at most one variable is not indefinite.
-/
import QuadFormsKB.Literature.ConwaySloane.Spinor

namespace QuadFormsKB.ConwaySloane

open Siegel Lattices Matrix

/-! ### Elementary congruences of binary matrices -/

section Elementary

/-- Congruence by an integer matrix $g$ with $\det g$ a unit. -/
theorem congrIn_of_mul {A B : Matrix (Fin 2) (Fin 2) ℤ} (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : IsUnit g.det)
    (h : gᵀ * A * g = B) : CongrIn ℤ A B :=
  ⟨((Matrix.isUnit_iff_isUnit_det g).2 hg).unit, by rw [IsUnit.unit_spec]; exact h⟩

/-- The shear $e_2 \mapsto e_2 + k e_1$: $\begin{pmatrix}a&b\\b&c\end{pmatrix} \sim
\begin{pmatrix}a&b+ka\\b+ka&c+2kb+k^2a\end{pmatrix}$. -/
theorem congrIn_shear (a b c k b' c' : ℤ) (h1 : b' = b + k * a) (h2 : c' = c + 2 * k * b + k ^ 2 * a) :
    CongrIn ℤ !![a, b; b, c] !![a, b'; b', c'] := by
  subst h1 h2
  refine congrIn_of_mul !![1, k; 0, 1] (by simp [Matrix.det_fin_two_of]) ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The swap $e_1 \leftrightarrow e_2$: $\begin{pmatrix}a&b\\b&c\end{pmatrix} \sim
\begin{pmatrix}c&b\\b&a\end{pmatrix}$. -/
theorem congrIn_swap (a b c : ℤ) : CongrIn ℤ !![a, b; b, c] !![c, b; b, a] := by
  refine congrIn_of_mul !![0, 1; 1, 0] (by simp [Matrix.det_fin_two_of]) ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The sign change $e_1 \mapsto -e_1$: $\begin{pmatrix}a&b\\b&c\end{pmatrix} \sim
\begin{pmatrix}a&-b\\-b&c\end{pmatrix}$. -/
theorem congrIn_neg (a b c : ℤ) : CongrIn ℤ !![a, b; b, c] !![a, -b; -b, c] := by
  refine congrIn_of_mul !![-1, 0; 0, 1] (by simp [Matrix.det_fin_two_of]) ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- A symmetric $2 \times 2$ matrix is $\begin{pmatrix}a&b\\b&c\end{pmatrix}$. -/
theorem eq_of_transpose_eq {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : Aᵀ = A) :
    A = !![A 0 0, A 0 1; A 0 1, A 1 1] := by
  have h : A 1 0 = A 0 1 := by
    have := congrFun (congrFun hA 0) 1
    simpa using this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h]

/-- $\begin{pmatrix}0&1\\1&1\end{pmatrix} \sim \mathrm{diag}(1,-1)$, since $(x+y)^2 - x^2 = 2xy + y^2$. -/
theorem congrIn_odd_hyperbolic : CongrIn ℤ !![0, 1; 1, 1] !![1, 0; 0, -1] := by
  refine congrIn_of_mul !![0, 1; 1, -1] (by simp [Matrix.det_fin_two_of]) ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- $\mathrm{diag}(-1,1) \sim \mathrm{diag}(1,-1)$ (swap). -/
theorem congrIn_diag_neg : CongrIn ℤ !![-1, 0; 0, 1] !![1, 0; 0, -1] := congrIn_swap (-1) 0 1

/-- **Parity of the diagonal is a congruence invariant:** if $A \sim B$ over $\mathbb Z$ (symmetric $A$) and both
diagonal entries of $A$ are even, so are those of $B$. -/
theorem even_diag_of_congrIn {A B : Matrix (Fin 2) (Fin 2) ℤ} (hA : Aᵀ = A) (h : CongrIn ℤ A B)
    (hev : Even (A 0 0) ∧ Even (A 1 1)) : Even (B 0 0) ∧ Even (B 1 1) := by
  obtain ⟨g, rfl⟩ := h
  have h10 : A 1 0 = A 0 1 := by simpa using congrFun (congrFun hA 0) 1
  obtain ⟨⟨m, hm⟩, ⟨l, hl⟩⟩ := hev
  constructor
  · refine ⟨m * (g.val 0 0) ^ 2 + A 0 1 * g.val 0 0 * g.val 1 0 + l * (g.val 1 0) ^ 2, ?_⟩
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, h10, hm, hl]
    ring
  · refine ⟨m * (g.val 0 1) ^ 2 + A 0 1 * g.val 0 1 * g.val 1 1 + l * (g.val 1 1) ^ 2, ?_⟩
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, h10, hm, hl]
    ring

/-- **Euclidean descent.** A binary integral form of determinant $-1$ is congruent to one of
$\begin{pmatrix}0&1\\1&0\end{pmatrix}$, $\begin{pmatrix}0&1\\1&1\end{pmatrix}$, $\mathrm{diag}(1,-1)$,
$\mathrm{diag}(-1,1)$. -/
theorem reduce_det_neg_one (n : ℕ) : ∀ a b c : ℤ, a.natAbs = n → a * c - b ^ 2 = -1 →
    CongrIn ℤ !![a, b; b, c] !![0, 1; 1, 0] ∨ CongrIn ℤ !![a, b; b, c] !![0, 1; 1, 1] ∨
      CongrIn ℤ !![a, b; b, c] !![1, 0; 0, -1] ∨ CongrIn ℤ !![a, b; b, c] !![-1, 0; 0, 1] := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b c hn hd
  by_cases ha : a = 0
  · subst ha
    have hb : b = 1 ∨ b = -1 := by
      have h : (b - 1) * (b + 1) = 0 := by nlinarith
      rcases mul_eq_zero.1 h with h | h
      · left; omega
      · right; omega
    -- reduce to b = 1
    have h1 : CongrIn ℤ !![(0 : ℤ), b; b, c] !![0, 1; 1, c] := by
      rcases hb with rfl | rfl
      · exact CongrIn.refl _
      · simpa using congrIn_neg 0 (-1) c
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' c
    · left
      exact h1.trans (congrIn_shear 0 1 c (-m) 1 0 (by ring) (by subst hm; ring))
    · right; left
      exact h1.trans (congrIn_shear 0 1 c (-m) 1 1 (by ring) (by subst hm; ring))
  · obtain ⟨b', hb'⟩ : ∃ b', b' = b % a := ⟨_, rfl⟩
    have hb'eq : b' = b + (-(b / a)) * a := by rw [hb', Int.emod_def]; ring
    have hb'0 : 0 ≤ b' := hb' ▸ Int.emod_nonneg b ha
    have hb'lt : b' < |a| := by
      rw [hb', Int.abs_eq_natAbs]; exact Int.emod_lt b ha
    obtain ⟨c', hc'⟩ : ∃ c', c' = c + 2 * (-(b / a)) * b + (-(b / a)) ^ 2 * a := ⟨_, rfl⟩
    have hd' : a * c' - b' ^ 2 = -1 := by rw [hc', hb'eq]; linear_combination hd
    have hsh := congrIn_shear a b c (-(b / a)) b' c' hb'eq hc'
    by_cases hlt : c'.natAbs < a.natAbs
    · have key := ih c'.natAbs (hn ▸ hlt) c' b' a rfl (by rw [mul_comm]; exact hd')
      have hchain := hsh.trans (congrIn_swap a b' c')
      rcases key with h | h | h | h
      exacts [Or.inl (hchain.trans h), Or.inr (Or.inl (hchain.trans h)),
        Or.inr (Or.inr (Or.inl (hchain.trans h))), Or.inr (Or.inr (Or.inr (hchain.trans h)))]
    · by_cases hb0 : b' = 0
      · subst hb0
        have h1 : a * c' = -1 := by nlinarith
        rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one' h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr (Or.inr (Or.inl hsh))
        · exact Or.inr (Or.inr (Or.inr hsh))
      · exfalso
        have hb1 : 1 ≤ b' := by omega
        have hcge : |a| ≤ |c'| := by
          rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs]; exact_mod_cast (not_lt.1 hlt)
        have hac : 0 ≤ a * c' := by nlinarith
        have e1 : a * c' = |a| * |c'| := by rw [← abs_mul, abs_of_nonneg hac]
        have e2 : |a| * |a| ≤ |a| * |c'| := mul_le_mul_of_nonneg_left hcge (abs_nonneg a)
        have e3 : |a| * |a| = a * a := abs_mul_abs_self a
        have e4 : b' * b' < |a| * |a| := by nlinarith
        nlinarith

end Elementary

/-! ### Normal forms of determinant $-1$ -/

section NormalForm

/-- **Normal forms of binary forms of determinant $-1$.** Let $A$ be a symmetric integral $2 \times 2$ matrix with
$\det A = -1$. If both diagonal entries are even (the form takes only even values) then $A$ is congruent over
$\mathbb Z$ to $\begin{pmatrix}0&1\\1&0\end{pmatrix}$; otherwise to $\mathrm{diag}(1,-1)$. -/
theorem congrIn_normal_of_det_eq_neg_one (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : Aᵀ = A) (hd : A.det = -1) :
    (Even (A 0 0) ∧ Even (A 1 1) → CongrIn ℤ A !![0, 1; 1, 0]) ∧
      (¬ (Even (A 0 0) ∧ Even (A 1 1)) → CongrIn ℤ A !![1, 0; 0, -1]) := by
  have hAe := eq_of_transpose_eq hA
  have h10 : A 1 0 = A 0 1 := by simpa using congrFun (congrFun hA 0) 1
  have hd' : A 0 0 * A 1 1 - A 0 1 ^ 2 = -1 := by
    rw [Matrix.det_fin_two, h10] at hd; linear_combination hd
  have red := reduce_det_neg_one _ (A 0 0) (A 0 1) (A 1 1) rfl hd'
  rw [← hAe] at red
  have s1 : (!![(0 : ℤ), 1; 1, 0])ᵀ = !![0, 1; 1, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  constructor
  · intro hev
    rcases red with h | h | h | h
    · exact h
    · have := (even_diag_of_congrIn hA h hev).2; simp at this
    · have := (even_diag_of_congrIn hA h hev).1; simp at this
    · have := (even_diag_of_congrIn hA h hev).1; simp at this
  · intro hnev
    rcases red with h | h | h | h
    · exact absurd (even_diag_of_congrIn s1 h.symm (by simp)) hnev
    · exact h.trans congrIn_odd_hyperbolic
    · exact h
    · exact h.trans congrIn_diag_neg

end NormalForm

/-! ### The parity of the diagonal is a genus invariant -/

section GenusParity

/-- If a symmetric matrix $A$ has even diagonal then every value of the form $\vec x A \vec x^{\mathsf T}$ over
$\mathbb Z_2$ lies in $2\mathbb Z_2$ (its reduction in $\mathbb Z/2$ vanishes). -/
theorem toZMod_form_eq_zero {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : Aᵀ = A) (hev : Even (A 0 0) ∧ Even (A 1 1))
    (y : Fin 2 → ℤ_[2]) :
    PadicInt.toZMod (y ⬝ᵥ ((A.map (Int.castRingHom ℤ_[2])) *ᵥ y)) = 0 := by
  have h10 : A 1 0 = A 0 1 := by simpa using congrFun (congrFun hA 0) 1
  have ha : ((A 0 0 : ℤ) : ZMod 2) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).2 (even_iff_two_dvd.1 hev.1)
  have hc : ((A 1 1 : ℤ) : ZMod 2) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).2 (even_iff_two_dvd.1 hev.2)
  have h2 : (2 : ZMod 2) = 0 := by decide
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.map_apply, h10, map_add, map_mul,
    eq_intCast, map_intCast, ha, hc]
  linear_combination (PadicInt.toZMod (y 0) * PadicInt.toZMod (y 1) * ((A 0 1 : ℤ) : ZMod 2)) * h2

/-- **"Both diagonal entries even" is a genus invariant** (one direction). -/
theorem even_diag_of_sameGenus_aux {A B : Matrix (Fin 2) (Fin 2) ℤ} (hA : Aᵀ = A)
    (h : SameGenus (Cassels.Ch8Ex2.gramForm A) (Cassels.Ch8Ex2.gramForm B))
    (hev : Even (A 0 0) ∧ Even (A 1 1)) : Even (B 0 0) ∧ Even (B 1 1) := by
  obtain ⟨g, hg⟩ := h.1 2
  have hB : ∀ x : Fin 2 → ℤ_[2],
      PadicInt.toZMod (x ⬝ᵥ ((B.map (Int.castRingHom ℤ_[2])) *ᵥ x)) = 0 := by
    intro x
    have := hg x
    rw [gramForm_map, gramForm_map, eval_gramForm, eval_gramForm] at this
    rw [← this]
    exact toZMod_form_eq_zero hA hev _
  have h0 := hB ![1, 0]
  have h1 := hB ![0, 1]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two] at h0 h1
  exact ⟨even_iff_two_dvd.2 (by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).1 h0),
    even_iff_two_dvd.2 (by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).1 h1)⟩

/-- **"Both diagonal entries even" is a genus invariant:** for symmetric integral $2 \times 2$ matrices $A, B$ whose
forms $\vec xA\vec x^{\mathsf T}$, $\vec xB\vec x^{\mathsf T}$ lie in one genus, $A$ has both diagonal entries even
(the form takes only even values) iff $B$ does. *Proof:* over $\mathbb Z_2$ the form of $B$ at $\vec e_i$ equals the
form of $A$ at some vector, which lies in $2\mathbb Z_2$; an integer in $2\mathbb Z_2$ is even. -/
theorem even_diag_of_sameGenus {A B : Matrix (Fin 2) (Fin 2) ℤ} (hA : Aᵀ = A) (hB : Bᵀ = B)
    (h : SameGenus (Cassels.Ch8Ex2.gramForm A) (Cassels.Ch8Ex2.gramForm B)) :
    (Even (A 0 0) ∧ Even (A 1 1)) ↔ (Even (B 0 0) ∧ Even (B 1 1)) :=
  ⟨even_diag_of_sameGenus_aux hA h, even_diag_of_sameGenus_aux hB h.symm⟩

end GenusParity

/-! ### The main result -/

section Main

/-- The determinant of a $2 \times 2$ matrix $A$ with $A^{\mathsf T} = A$: the Hessian $A + A^{\mathsf T}$ of the form
has determinant $4\det A$. -/
theorem det_hessian_gramForm_two {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : Aᵀ = A) :
    (Cassels.Ch8Ex2.gramForm A).hessian.det = 4 * A.det := by
  rw [Cassels.Ch8Ex2.hessian_gramForm, hA, ← two_smul ℤ A, Matrix.det_smul]
  simp

/-- **An indefinite binary form of determinant $-1$ has only one class in its genus** (Conway–Sloane, Ch. 15, §9.7,
proof of Thm. 21, p. 395: for $n = 2$ one has $d \neq \pm1$, "or else there is only one class in the genus").
*Proof.* A form $B$ in the genus of $A$ has $\det B = -1$ (Cassels, Lemma 4.1), and its diagonal parity agrees with that
of $A$ (the $\mathbb Z_2$ component). By `congrIn_normal_of_det_eq_neg_one` both are then congruent to the same normal
form, $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ or $\mathrm{diag}(1,-1)$, so $A$ and $B$ are $\mathbb Z$-equivalent. -/
@[kb "conwaysloane1999" "Ch. 15, §9.7, proof of Thm. 21, p. 395 (n = 2: d ≠ ±1, or else only one class in the genus)"]
theorem not_moreThanOneClass_of_det_eq_neg_one (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : Aᵀ = A) (hd : A.det = -1) :
    ¬ MoreThanOneClass A := by
  rintro ⟨B, hB, hg, hne⟩
  apply hne
  have hdet := SameGenus.hessian_det_eq hg
  rw [det_hessian_gramForm_two hA, det_hessian_gramForm_two hB, hd] at hdet
  have hdB : B.det = -1 := by linarith
  have hpar := even_diag_of_sameGenus hA hB hg
  obtain ⟨hA1, hA2⟩ := congrIn_normal_of_det_eq_neg_one A hA hd
  obtain ⟨hB1, hB2⟩ := congrIn_normal_of_det_eq_neg_one B hB hdB
  refine (isometricGL_gramForm_iff hA hB).2 ?_
  by_cases hev : Even (A 0 0) ∧ Even (A 1 1)
  · exact (hA1 hev).trans (hB1 (hpar.1 hev)).symm
  · exact (hA2 hev).trans (hB2 (fun h => hev (hpar.2 h))).symm

end Main

/-! ### Indefinite forms: the sign of the determinant -/

section Indefinite

open NumberField

/-- **Indefinite gives a real zero.** If the rational form of a symmetric integral Gram matrix $A$ is indefinite
(isotropic at the infinite place of $\mathbb Q$) then $\vec z A \vec z^{\mathsf T} = 0$ for some nonzero real
$\vec z$. -/
theorem exists_real_zero_of_isIndefinite {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (h : IsIndefinite ((Cassels.Ch8Ex2.gramForm A).map (Int.castRingHom ℚ))) :
    ∃ z : Fin n → ℝ, z ≠ 0 ∧ z ⬝ᵥ ((A.map (Int.castRingHom ℝ)) *ᵥ z) = 0 := by
  obtain ⟨w, x, hx0, hx⟩ := h
  let ψ := InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)
  refine ⟨fun i => ψ (x i), ?_, ?_⟩
  · intro h0
    apply hx0
    funext i
    have := congrFun h0 i
    simpa using this
  · rw [← eval_gramForm, ← gramForm_map]
    rw [Lattices.evalIn_castHom_rat] at hx
    have h2 := Lattices.hom_eval_castHom (Cassels.Ch8Ex2.gramForm A) ψ.toRingHom x
    rw [hx] at h2
    simpa using h2.symm

/-- Real positivity: if $ac - b^2 > 0$ and $az_0^2 + 2bz_0z_1 + cz_1^2 = 0$ then $z_0 = z_1 = 0$. -/
theorem eq_zero_of_posDef_real {a b c z0 z1 : ℝ} (hd : 0 < a * c - b ^ 2)
    (h : a * z0 ^ 2 + 2 * b * z0 * z1 + c * z1 ^ 2 = 0) : z0 = 0 ∧ z1 = 0 := by
  have ha : a ≠ 0 := by
    rintro rfl
    nlinarith [sq_nonneg b]
  have h1 : (a * z0 + b * z1) ^ 2 + (a * c - b ^ 2) * z1 ^ 2 = 0 := by linear_combination a * h
  have h2 : (a * c - b ^ 2) * z1 ^ 2 = 0 := by
    nlinarith [sq_nonneg (a * z0 + b * z1), mul_nonneg hd.le (sq_nonneg z1)]
  have hz1 : z1 = 0 := by
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hd.ne'
    · exact pow_eq_zero_iff (two_ne_zero) |>.1 h
  subst hz1
  have : a * z0 = 0 := by
    have : (a * z0 + b * 0) ^ 2 = 0 := by simpa using h1
    simpa using this
  exact ⟨(mul_eq_zero.1 this).resolve_left ha, rfl⟩

/-- **An indefinite binary form has negative determinant:** if $A$ is a symmetric integral $2 \times 2$ matrix with
$\det A \neq 0$ and the rational form $\vec xA\vec x^{\mathsf T}$ is indefinite, then $\det A < 0$ (a binary form of
positive determinant is definite). -/
theorem det_neg_of_isIndefinite (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : Aᵀ = A) (hd : A.det ≠ 0)
    (h : IsIndefinite ((Cassels.Ch8Ex2.gramForm A).map (Int.castRingHom ℚ))) : A.det < 0 := by
  by_contra hnot
  have hpos : 0 < A.det := lt_of_le_of_ne (not_lt.1 hnot) (Ne.symm hd)
  obtain ⟨z, hz0, hz⟩ := exists_real_zero_of_isIndefinite A h
  have h10 : A 1 0 = A 0 1 := by simpa using congrFun (congrFun hA 0) 1
  have hdet : (A.det : ℝ) = (A 0 0 : ℝ) * (A 1 1 : ℝ) - (A 0 1 : ℝ) ^ 2 := by
    rw [Matrix.det_fin_two, h10]; push_cast; ring
  have hpos' : (0 : ℝ) < (A 0 0 : ℝ) * (A 1 1 : ℝ) - (A 0 1 : ℝ) ^ 2 := by
    rw [← hdet]; exact_mod_cast hpos
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.map_apply, h10, eq_intCast] at hz
  obtain ⟨e0, e1⟩ := eq_zero_of_posDef_real (a := (A 0 0 : ℝ)) (b := (A 0 1 : ℝ)) (c := (A 1 1 : ℝ))
    (z0 := z 0) (z1 := z 1) hpos' (by linear_combination hz)
  exact hz0 (by funext i; fin_cases i <;> simp [e0, e1])

/-- **A form in at most one variable is not indefinite:** for $n \le 1$ and $\det A \neq 0$ the rational form
$\vec xA\vec x^{\mathsf T}$ is anisotropic at the infinite place, hence not indefinite. -/
theorem not_isIndefinite_of_le_one {n : ℕ} (hn : n ≤ 1) (A : Matrix (Fin n) (Fin n) ℤ) (hd : A.det ≠ 0) :
    ¬ IsIndefinite ((Cassels.Ch8Ex2.gramForm A).map (Int.castRingHom ℚ)) := by
  intro h
  obtain ⟨z, hz0, hz⟩ := exists_real_zero_of_isIndefinite A h
  interval_cases n
  · exact hz0 (Subsingleton.elim _ _)
  · have h0 : z 0 ≠ 0 := fun h0 => hz0 (by funext i; fin_cases i; simpa using h0)
    have hA0 : A 0 0 ≠ 0 := by simpa [Matrix.det_unique] using hd
    simp only [dotProduct, Matrix.mulVec, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
      Matrix.map_apply, eq_intCast] at hz
    have : (A 0 0 : ℝ) * (z 0) ^ 2 = 0 := by linear_combination hz
    rcases mul_eq_zero.1 this with h | h
    · exact hA0 (by exact_mod_cast h)
    · exact h0 (pow_eq_zero_iff two_ne_zero |>.1 h)

end Indefinite

end QuadFormsKB.ConwaySloane
