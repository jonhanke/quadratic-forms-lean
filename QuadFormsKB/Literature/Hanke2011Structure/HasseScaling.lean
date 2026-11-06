/-
# Hanke 2011, §5: scaling a quadratic space, Hasse invariant (Lemma 5.10, Thm. 5.7)

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`).

Let $(V,Q)$ be a nondegenerate $n$-dimensional quadratic space over a local field $K_v$ of characteristic $\neq 2$,
with Hilbert symbol $(\cdot,\cdot)_v$, and $c_v(V) = \prod_{i<j}(a_i,a_j)_v$ the Hasse invariant in Serre's convention
(no diagonal pairs $i=j$), for any diagonalization $Q \cong a_0x_0^2+\dots+a_{n-1}x_{n-1}^2$. The Gram determinant is
$\det_G(V) = \prod_i a_i$ (indices are 0-based here; the paper's $a_1,\dots,a_n$ are `a 0`, ..., `a (n-1)`).
Well-definedness of $c_v$ on isometry classes is `NFPlace.hasseSerre_isometric` (`HasseIsometryNF.lean`), so
statements about the diagonal formula are statements about the space.

* `prod_scale_symbol`: the purely algebraic identity. For a field $K$ and a symbol $h : K \times K \to \mathbb{Z}$ that
  is symmetric, multiplicative in each variable on nonzero elements, and never $0$ (e.g. $\pm1$-valued), and
  $u, a_i \in K^\times$,
  $$\prod_{i<j} h(ua_i, ua_j) = h(u,u)^{n(n-1)/2}\; h\Bigl(u,\prod_i a_i\Bigr)^{n-1}\prod_{i<j} h(a_i,a_j).$$
* `lemma_5_10`: Lemma 5.10 at a place $v$ of a number field $F$ (the symbol is `NFPlace.hilbert`, i.e. the Hilbert
  symbol over the completion $F_v$ of elements of $F$): $c_v(uV) = (u,u)_v^{n(n-1)/2}(u,\det_G V)_v^{n-1}c_v(V)$.
* `hasseSerre_smul_odd`: the corollary used in the proof of Theorem 5.7 (p. 25): for $n$ odd, $c_v(uV) = c_v(V)$ if
  $n \equiv 1 \pmod 4$ and $c_v(uV) = (u,u)_v\,c_v(V)$ if $n \equiv 3 \pmod 4$. The paper states this for a unit $u$ at
  a finite place $p$; the formula holds for every $u \in F^\times$ and every place, and no unit hypothesis is needed.

* `hasseLocal`, `lemma_5_10_finite`, `lemma_5_10_infinite`: Lemma 5.10 over the completion itself (the paper's local
  field $K_v$): $u, a_i \in K_v^\times$ with $K_v$ = `v.adicCompletion F` (finite $v$) or `w.Completion` (infinite
  $w$), the symbol being `hilbertSymbol` of $K_v$ (via `hilbertSymbol_mul_right_finite` / `_infinite` in
  `OMeara/Sec72Local.lean`) and `hasseLocal` the Serre-convention product $\prod_{i<j}(a_i,a_j)$.
  `lemma_5_10` is the version for elements of $F$ viewed in $F_v$.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.LocalGlobal.HasseConventionsNF
import QuadFormsKB.Literature.OMeara.Sec72Local

namespace QuadFormsKB.Hanke2011Structure

open Finset

section Abstract

variable {K : Type*} [Field K] (h : K → K → ℤ)

private lemma symbol_one_right (hmul : ∀ a b c : K, a ≠ 0 → b ≠ 0 → c ≠ 0 → h a (b * c) = h a b * h a c)
    (hne : ∀ a b, h a b ≠ 0) {u : K} (hu : u ≠ 0) : h u 1 = 1 := by
  have h1 := hmul u 1 1 hu one_ne_zero one_ne_zero
  rw [mul_one] at h1
  have h2 := hne u 1
  have : h u 1 * (h u 1 - 1) = 0 := by linarith
  rcases mul_eq_zero.mp this with h3 | h3
  · exact absurd h3 h2
  · linarith

private lemma prod_symbol_right (hmul : ∀ a b c : K, a ≠ 0 → b ≠ 0 → c ≠ 0 → h a (b * c) = h a b * h a c)
    (hne : ∀ a b, h a b ≠ 0) {u : K} (hu : u ≠ 0) :
    ∀ (m : ℕ) (s : Fin m → K), (∀ k, s k ≠ 0) → ∏ k, h u (s k) = h u (∏ k, s k) := by
  intro m
  induction m with
  | zero =>
    intro s _
    simp [symbol_one_right h hmul hne hu]
  | succ m ih =>
    intro s hs
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ, ih (fun k => s k.succ) (fun k => hs _),
      hmul u _ _ hu (hs 0) (Finset.prod_ne_zero_iff.mpr fun k _ => hs _)]

private lemma tri_succ (n : ℕ) : (n + 1) * n / 2 = n * (n - 1) / 2 + n := by
  rcases n with _ | m
  · simp
  · have : (m + 1 + 1) * (m + 1) = (m + 1) * (m + 1 - 1) + 2 * (m + 1) := by
      simp only [Nat.add_sub_cancel]; ring
    rw [this, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]

/-- **Scaling identity for an abstract symbol.** Let $K$ be a field and $h : K \times K \to \mathbb{Z}$ a symbol
that is symmetric, multiplicative in the second variable on nonzero elements (`hmul`), and never $0$ (`hne`; true for
a $\pm1$-valued symbol such as the Hilbert symbol). For $u \in K^\times$ and $a_0,\dots,a_{n-1} \in K^\times$,
$$\prod_{0\le i<j<n} h(ua_i, ua_j) = h(u,u)^{n(n-1)/2}\; h\Bigl(u,\prod_{i} a_i\Bigr)^{n-1}
  \prod_{0\le i<j<n} h(a_i,a_j)$$
(exponents are natural-number arithmetic, $n(n-1)/2$ exact). The proof is by induction on $n$ via
$(ua_i,ua_j) = (u,u)(u,a_ia_j)(a_i,a_j)$. -/
theorem prod_scale_symbol (hsymm : ∀ a b, h a b = h b a)
    (hmul : ∀ a b c : K, a ≠ 0 → b ≠ 0 → c ≠ 0 → h a (b * c) = h a b * h a c)
    (hne : ∀ a b, h a b ≠ 0) {u : K} (hu : u ≠ 0) :
    ∀ (n : ℕ) (a : Fin n → K), (∀ i, a i ≠ 0) →
      (∏ i, ∏ j, if i < j then h (u * a i) (u * a j) else 1) =
        h u u ^ (n * (n - 1) / 2) * h u (∏ i, a i) ^ (n - 1) * ∏ i, ∏ j, if i < j then h (a i) (a j) else 1 := by
  intro n
  induction n with
  | zero =>
    intro a _
    simp
  | succ n ih =>
    intro a ha
    have hsplit : ∀ b : Fin (n + 1) → K, (∏ i, ∏ j, if i < j then h (b i) (b j) else 1) =
        (∏ k : Fin n, h (b 0) (b k.succ)) * ∏ i : Fin n, ∏ j : Fin n, if i < j then h (b i.succ) (b j.succ) else 1 := by
      intro b
      simp [Fin.prod_univ_succ, Fin.succ_pos, Fin.succ_lt_succ_iff]
    rw [hsplit, hsplit a, ih (fun k => a k.succ) (fun k => ha _)]
    have hterm : ∀ k : Fin n, h (u * a 0) (u * a k.succ) =
        (h u u * h u (a 0)) * h u (a k.succ) * h (a 0) (a k.succ) := by
      intro k
      have h1 := hmul (u * a 0) u (a k.succ) (mul_ne_zero hu (ha 0)) hu (ha _)
      have h3 := hmul (a k.succ) u (a 0) (ha _) hu (ha 0)
      have h4 := hmul u u (a 0) hu hu (ha 0)
      rw [h1, hsymm (u * a 0) u, h4, hsymm (u * a 0) (a k.succ), h3, hsymm (a k.succ) u,
        hsymm (a k.succ) (a 0)]
      ring
    simp only [hterm, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [prod_symbol_right h hmul hne hu n (fun k => a k.succ) (fun k => ha _), Fin.prod_univ_succ,
      hmul u _ _ hu (ha 0) (Finset.prod_ne_zero_iff.mpr fun k _ => ha _)]
    simp only [Nat.add_sub_cancel]
    rw [tri_succ]
    rcases n with _ | m
    · simp [symbol_one_right h hmul hne hu]
    · simp only [Nat.add_sub_cancel]
      ring

end Abstract

namespace NFPlace

open QuadFormsKB

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- **Lemma 5.10 (Hanke 2011, p. 25): Hasse invariant of a scaled space.**
Let $F$ be a number field, $v$ a place of $F$, $u \in F^\times$ and $a_0,\dots,a_{n-1} \in F^\times$, so that
$V = \langle a_0,\dots,a_{n-1}\rangle$ is a nondegenerate $n$-dimensional quadratic space with Gram determinant
$\det_G(V) = \prod_i a_i$ and $uV = \langle ua_0,\dots,ua_{n-1}\rangle$. With $c_v = $ `hasseSerre`
(Serre's convention, $c_v = \prod_{i<j}(a_i,a_j)_v$, computed in $F_v$),
$$c_v(uV) = (u,u)_v^{\,n(n-1)/2}\;(u,\det_G V)_v^{\,n-1}\;c_v(V).$$
Any diagonalization may be used, since $c_v$ is an isometry invariant (`NFPlace.hasseSerre_isometric`). -/
@[kb "hanke2011structure" "Lemma 5.10, p. 25"]
theorem lemma_5_10 (v : NFPlace F) {u : F} (hu : u ≠ 0) (a : Fin n → F) (ha : ∀ i, a i ≠ 0) :
    v.hasseSerre (fun i => u * a i) =
      v.hilbert u u ^ (n * (n - 1) / 2) * v.hilbert u (∏ i, a i) ^ (n - 1) * v.hasseSerre a := by
  unfold NFPlace.hasseSerre
  refine prod_scale_symbol v.hilbert (NFPlace.hilbert_comm v)
    (fun a b c ha hb hc => NFPlace.hilbert_mul_right v ha hb hc) ?_ hu n a ha
  intro x y h0
  rcases NFPlace.hilbert_eq_one_or v x y with h1 | h1 <;> rw [h1] at h0 <;> norm_num at h0

/-- **Hasse invariant of a scaled odd-dimensional space (Hanke 2011, proof of Thm. 5.7, p. 25).**
Let $F$ be a number field, $v$ a place, $u \in F^\times$, $a_0,\dots,a_{n-1} \in F^\times$ with $n$ odd. Then
$$c_v(u\,\langle a_0,\dots,a_{n-1}\rangle) = \begin{cases} c_v(\langle a_0,\dots,a_{n-1}\rangle) & n \equiv 1 \pmod 4,\\
(u,u)_v\; c_v(\langle a_0,\dots,a_{n-1}\rangle) & n \equiv 3 \pmod 4,\end{cases}$$
with `n % 4` the natural-number residue. This is Lemma 5.10 with $(u,\det_G V)_v^{n-1} = 1$ since $n-1$ is even and the
symbol is $\pm1$. The paper states it for a unit $u$ at a finite place; no unit hypothesis is needed. -/
@[kb "hanke2011structure" "Thm. 5.7, proof, p. 25"]
theorem hasseSerre_smul_odd (v : NFPlace F) {u : F} (hu : u ≠ 0) (a : Fin n → F) (ha : ∀ i, a i ≠ 0)
    (hodd : n % 2 = 1) :
    v.hasseSerre (fun i => u * a i) =
      if n % 4 = 1 then v.hasseSerre a else v.hilbert u u * v.hasseSerre a := by
  rw [lemma_5_10 v hu a ha]
  obtain ⟨m, hm⟩ : ∃ m, n - 1 = 2 * m := ⟨(n - 1) / 2, by omega⟩
  have hsq : ∀ x y : F, v.hilbert x y ^ 2 = 1 := by
    intro x y
    rcases NFPlace.hilbert_eq_one_or v x y with h1 | h1 <;> rw [h1] <;> norm_num
  have hP : v.hilbert u (∏ i, a i) ^ (n - 1) = 1 := by
    rw [hm, pow_mul, hsq, one_pow]
  rw [hP, mul_one]
  have hE : n * (n - 1) / 2 = n * m := by
    rw [hm, show n * (2 * m) = 2 * (n * m) by ring]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  rw [hE]
  split_ifs with h4
  · have hmev : m % 2 = 0 := by omega
    obtain ⟨r, hr⟩ : ∃ r, n * m = 2 * r := ⟨n * m / 2, by
      have : (n * m) % 2 = 0 := by rw [Nat.mul_mod, hmev]; simp
      omega⟩
    rw [hr, pow_mul, hsq, one_pow, one_mul]
  · have hmod : m % 2 = 1 := by omega
    obtain ⟨r, hr⟩ : ∃ r, n * m = 2 * r + 1 := ⟨n * m / 2, by
      have : (n * m) % 2 = 1 := by rw [Nat.mul_mod, hmod, hodd]
      omega⟩
    rw [hr, pow_succ, pow_mul, hsq, one_pow, one_mul]

end NFPlace

section Completion

open NumberField IsDedekindDomain QuadFormsKB QuadFormsKB.OMeara

/-- The Hilbert symbol `hilbertSymbol K a b` is never `0` (it is $\pm1$ by definition). -/
private lemma hilbertSymbol_ne_zero' (K : Type*) [Field K] (a b : K) : hilbertSymbol K a b ≠ 0 := by
  unfold hilbertSymbol
  split_ifs <;> norm_num

/-- **Serre's Hasse invariant over a local field $K$:** for $a_0,\dots,a_{n-1} \in K^\times$,
$$c(a) = \prod_{0\le i<j<n}(a_i,a_j)_K,$$
with $(\cdot,\cdot)_K$ the Hilbert symbol of $K$ (`hilbertSymbol`) and no diagonal pairs $i=j$. -/
noncomputable def hasseLocal (K : Type*) [Field K] {n : ℕ} (a : Fin n → K) : ℤ :=
  ∏ i, ∏ j, if i < j then hilbertSymbol K (a i) (a j) else 1

/-- **Lemma 5.10 (Hanke 2011, p. 25), over the completion at a finite place.**
Let $F$ be a number field, $v$ a finite place and $K_v$ the completion `v.adicCompletion F`. For $u \in K_v^\times$ and
$a_0,\dots,a_{n-1} \in K_v^\times$ (so $V=\langle a_0,\dots,a_{n-1}\rangle$ has $\det_G V = \prod_i a_i$),
$$c_v(uV) = (u,u)_v^{\,n(n-1)/2}\;(u,\det_G V)_v^{\,n-1}\;c_v(V),$$
where $c_v = $ `hasseLocal` is Serre's convention. -/
@[kb "hanke2011structure" "Lemma 5.10, p. 25"]
theorem lemma_5_10_finite {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    {n : ℕ} {u : v.adicCompletion F} (hu : u ≠ 0) (a : Fin n → v.adicCompletion F) (ha : ∀ i, a i ≠ 0) :
    hasseLocal _ (fun i => u * a i) =
      hilbertSymbol _ u u ^ (n * (n - 1) / 2) * hilbertSymbol _ u (∏ i, a i) ^ (n - 1) * hasseLocal _ a :=
  prod_scale_symbol (hilbertSymbol (v.adicCompletion F)) (hilbertSymbol_comm _)
    (fun _ _ _ ha hb hc => hilbertSymbol_mul_right_finite v ha hb hc)
    (hilbertSymbol_ne_zero' _) hu n a ha

/-- **Lemma 5.10 (Hanke 2011, p. 25), over the completion at an infinite place.**
Same statement as `lemma_5_10_finite` for $u, a_i \in K_w^\times$ with $K_w$ = `w.Completion` ($\mathbb{R}$ or
$\mathbb{C}$): $c_w(uV) = (u,u)_w^{n(n-1)/2}(u,\det_G V)_w^{n-1}c_w(V)$. -/
@[kb "hanke2011structure" "Lemma 5.10, p. 25"]
theorem lemma_5_10_infinite {F : Type} [Field F] [NumberField F] (w : InfinitePlace F)
    {n : ℕ} {u : w.Completion} (hu : u ≠ 0) (a : Fin n → w.Completion) (ha : ∀ i, a i ≠ 0) :
    hasseLocal _ (fun i => u * a i) =
      hilbertSymbol _ u u ^ (n * (n - 1) / 2) * hilbertSymbol _ u (∏ i, a i) ^ (n - 1) * hasseLocal _ a :=
  prod_scale_symbol (hilbertSymbol w.Completion) (hilbertSymbol_comm _)
    (fun _ _ _ ha hb hc => hilbertSymbol_mul_right_infinite w ha hb hc)
    (hilbertSymbol_ne_zero' _) hu n a ha

end Completion

end QuadFormsKB.Hanke2011Structure
