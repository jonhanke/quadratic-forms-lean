/-
# O'Meara §106E–F: the lattice $E_8 \perp \mathbb Z^{n-8}$, adjacent to $\mathbb Z^n$ but not isometric to it

**Layer:** $F = \mathbb Q$ (a number field), $V = \mathbb Q^n$ with $Q = I_n$ = `sumSqForm n`, lattices are
$\mathcal O_{\mathbb Q}$-submodules of $\mathbb Q^n$, $D = \mathbb Z^n$ = `intVec`, $E$ = `omearaE n` (`Sec106E.lean`),
"adjacent" is `Nbr.IsNbrL Q 2` (`Sec106Adj.lean`). Indices are 0-based.

**Defines** (O'Meara 1973, §106F, 106:13, p. 334)
* `omearaEZ n`: the lattice with matrix $\Phi_8 \perp I_{n-8}$, i.e. $E_8 \perp \mathbb Z^{n-8}$ inside $\mathbb Q^n$
  (meaningful for $n \ge 8$); `omearaEZ_eq_omearaE_eight`: for $n = 8$ it is `omearaE 8`.

**Proves**
* `omearaE_even`: for $8 \mid n$, $n \ge 8$, $E$ is even (O'Meara 106:1 and §106E: $E$ is even unimodular), from 106:11;
* `omearaEZ_isLattice`, `omearaEZ_unimodular`, `omearaEZ_adjacent` ($E_8 \perp \mathbb Z^{n-8}$ is a unimodular lattice
  adjacent to $\mathbb Z^n$, $n \ge 8$);
* `norm_one_mem_omearaEZ`: a vector of norm $1$ of $E_8 \perp \mathbb Z^{n-8}$ has its first $8$ coordinates $0$;
* `not_isIsometric_intVec_omearaEZ`: $E_8 \perp \mathbb Z^{n-8}$ is not isometric to $\mathbb Z^n$ (the "exactly one"
  part of 106:13).

**Deviations.** For $n < 8$ the head map `omearaEZHead` zero-pads (the coordinates $j \ge n$ are $0$), so `omearaEZ n`
is then the set of $x$ whose zero-padding lies in $E_8$ (nothing is imposed on coordinates $\ge 8$ since there are none);
the results are only claimed for $n \ge 8$. O'Meara proves the non-isometry with 105:1; here the $n$ norm-$1$ vectors
$\sigma e_i$ would be forced into the $(n-8)$-dimensional tail, so a row of the matrix of $\sigma$ vanishes, which
contradicts invertibility (a more elementary route to the same conclusion).
-/
import QuadFormsKB.Literature.OMeara.Sec106Adj

open Matrix NumberField QuadFormsKB.HilbertModular

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {n : ℕ}

/-! ### Helper lemmas (copies of private lemmas of `Sec106E.lean` / `Sec106Adj.lean`) -/

private theorem ez_eval (x : Fin n → ℚ) : (sumSqForm n).eval x = ∑ i, x i ^ 2 := by
  rw [sumSqForm, QuadForm.eval, QuadForm.evalIn_diag]; simp

private theorem ez_bil (x y : Fin n → ℚ) :
    bil (sumSqForm n) x y = 2 * ∑ i, x i * y i := by
  have h : (sumSqForm n).hessian = (2 : ℚ) • (1 : Matrix (Fin n) (Fin n) ℚ) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [QuadForm.hessian, sumSqForm, QuadForm.diag]; norm_num
    · simp [QuadForm.hessian, sumSqForm, QuadForm.diag, hij]
  rw [bil, h, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, dotProduct, smul_eq_mul]

private theorem ez_intCast (a : 𝓞 ℚ) : ∃ m : ℤ, ((m : ℤ) : 𝓞 ℚ) = a :=
  ⟨Rat.ringOfIntegersEquiv a, (eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm.trans
    (Rat.ringOfIntegersEquiv.symm_apply_apply a)⟩

private theorem ez_smul_apply (k : ℤ) (A : Fin n → ℚ) (i : Fin n) :
    (((k : ℤ) : 𝓞 ℚ) • A) i = k * A i := by
  rw [Int.cast_smul_eq_zsmul]; simp

private theorem ez_two_smul_apply (A : Fin n → ℚ) (i : Fin n) : ((2 : 𝓞 ℚ) • A) i = 2 * A i := by
  have e : (2 : 𝓞 ℚ) = ((2 : ℤ) : 𝓞 ℚ) := by norm_num
  rw [e, ez_smul_apply]; norm_num

private lemma ez_mem_range {q : ℚ} : q ∈ (algebraMap (𝓞 ℚ) ℚ).range ↔ ∃ m : ℤ, q = m := by
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨m, rfl⟩ := ez_intCast a
    exact ⟨m, by simp⟩
  · rintro ⟨m, rfl⟩
    exact ⟨(m : 𝓞 ℚ), by simp⟩

private lemma ez_D_coord {x : Fin n → ℚ} :
    x ∈ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) ↔ ∀ i, ∃ m : ℤ, x i = m := by
  rw [mem_intVec]
  exact forall_congr' fun i => ez_mem_range

private lemma ez_sum_int {ι : Type*} (s : Finset ι) (g : ι → ℚ) (h : ∀ i ∈ s, ∃ m : ℤ, g i = m) :
    ∃ M : ℤ, ∑ i ∈ s, g i = M :=
  Finset.sum_induction g (fun q => ∃ m : ℤ, q = m)
    (fun a b ⟨m, hm⟩ ⟨m', hm'⟩ => ⟨m + m', by simp [hm, hm']⟩) ⟨0, by simp⟩ h

/-! ### The lattice $E_8 \perp \mathbb Z^{n-8}$ -/

/-- **The head map** $\mathbb Q^n \to \mathbb Q^8$: the first $8$ coordinates $x_0, \dots, x_7$ of $x$, zero-padded
if $n < 8$ (the coordinate $j$ of the result is $x_j$ if $j < n$ and $0$ otherwise). It is $\mathcal O_{\mathbb
Q}$-linear. Auxiliary (not in the book). -/
def omearaEZHead (n : ℕ) : (Fin n → ℚ) →ₗ[𝓞 ℚ] (Fin 8 → ℚ) where
  toFun x j := if h : j.val < n then x ⟨j.val, h⟩ else 0
  map_add' x y := by
    ext j
    by_cases h : j.val < n <;> simp [h]
  map_smul' c x := by
    ext j
    by_cases h : j.val < n <;> simp [h]

/-- **The tail condition** of $E_8 \perp \mathbb Z^{n-8}$: the submodule of $x \in \mathbb Q^n$ all of whose
coordinates $x_i$ with $i \ge 8$ are integers. Auxiliary (not in the book). -/
def omearaEZTail (n : ℕ) : Submodule (𝓞 ℚ) (Fin n → ℚ) where
  carrier := {x | ∀ i : Fin n, 8 ≤ i.val → ∃ m : ℤ, x i = m}
  add_mem' {x y} hx hy i hi := by
    obtain ⟨a, ha⟩ := hx i hi
    obtain ⟨b, hb⟩ := hy i hi
    exact ⟨a + b, by simp [ha, hb]⟩
  zero_mem' i hi := ⟨0, by simp⟩
  smul_mem' c x hx i hi := by
    obtain ⟨a, ha⟩ := hx i hi
    obtain ⟨k, rfl⟩ := ez_intCast c
    exact ⟨k * a, by rw [ez_smul_apply, ha]; push_cast; ring⟩

/-- **The lattice $E_8 \perp \mathbb Z^{n-8}$** (O'Meara 1973, §106F, 106:13, p. 334, the lattice with matrix
$\Phi_8 \perp I_{n-8}$) inside $\mathbb Q^n$ with $Q = I_n$: the vectors $x$ whose first $8$ coordinates
$(x_0, \dots, x_7)$ lie in $E_8$ (`omearaE 8`) and whose coordinates $x_i$, $i \ge 8$, are integers
(`mem_omearaEZ`). Meaningful for $n \ge 8$; for $n < 8$ the first $8$ coordinates are zero-padded
(`omearaEZHead`), so that the definition is still a submodule. -/
@[kb "omeara1963" "§106F, 106:13, p. 334 (the lattice with matrix Φ₈ ⊥ I_{n−8})"]
def omearaEZ (n : ℕ) : Submodule (𝓞 ℚ) (Fin n → ℚ) :=
  (omearaE 8).comap (omearaEZHead n) ⊓ omearaEZTail n

/-- **Membership in $E_8 \perp \mathbb Z^{n-8}$** (O'Meara 1973, §106F, p. 334): $x \in$ `omearaEZ n` if and only if the
vector of the first $8$ coordinates of $x$ lies in $E_8$ and every coordinate $x_i$ with $i \ge 8$ is an integer. -/
@[kb "omeara1963" "§106F, 106:13, p. 334 (the lattice with matrix Φ₈ ⊥ I_{n−8})"]
theorem mem_omearaEZ {x : Fin n → ℚ} :
    x ∈ omearaEZ n ↔ omearaEZHead n x ∈ omearaE 8 ∧ ∀ i : Fin n, 8 ≤ i.val → ∃ m : ℤ, x i = m :=
  Iff.rfl

private lemma ez_head_apply (hn : 8 ≤ n) (x : Fin n → ℚ) (j : Fin 8) :
    omearaEZHead n x j = x ⟨j.val, lt_of_lt_of_le j.isLt hn⟩ := by
  simp only [omearaEZHead, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_pos (lt_of_lt_of_le j.isLt hn)]

/-- **$E_8 \perp \mathbb Z^{0} = E_8$** (O'Meara 1973, §106F, p. 334, the case $n = 8$): for $n = 8$ the lattice
`omearaEZ 8` literally equals `omearaE 8` (as submodules of $\mathbb Q^8$). -/
@[kb "omeara1963" "§106F, 106:13, p. 334 (the lattice with matrix Φ₈ ⊥ I_{n−8}; n = 8 gives E)"]
theorem omearaEZ_eq_omearaE_eight : omearaEZ 8 = omearaE 8 := by
  ext x
  rw [mem_omearaEZ]
  have hh : omearaEZHead 8 x = x := funext fun j => ez_head_apply le_rfl x j
  constructor
  · rintro ⟨h, -⟩
    rwa [hh] at h
  · intro h
    exact ⟨by rwa [hh], fun i hi => absurd i.isLt (by omega)⟩

/-- **Splitting a sum over the first $8$ coordinates and the rest** (auxiliary). -/
private lemma ez_sum_split (hn : 8 ≤ n) (f : Fin n → ℚ) :
    ∑ i, f i = ∑ j : Fin 8, f ⟨j.val, lt_of_lt_of_le j.isLt hn⟩ +
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => 8 ≤ i.val), f i := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin n => i.val < 8)]
  have e1 : ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < 8), f i =
      ∑ j : Fin 8, f ⟨j.val, lt_of_lt_of_le j.isLt hn⟩ := by
    refine Finset.sum_bij' (fun i hi => ⟨i.val, (Finset.mem_filter.mp hi).2⟩)
      (fun j _ => ⟨j.val, lt_of_lt_of_le j.isLt hn⟩) ?_ ?_ ?_ ?_ ?_
    · intro i hi; exact Finset.mem_univ _
    · intro j _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt⟩
    · intro i hi; rfl
    · intro j _; rfl
    · intro i hi; rfl
  have e2 : Finset.univ.filter (fun i : Fin n => ¬ i.val < 8) =
      Finset.univ.filter (fun i : Fin n => 8 ≤ i.val) := by
    ext i; simp
  rw [e1, e2]

/-- The coordinates with index $\ge 8$ (auxiliary). -/
private abbrev tailSet (n : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => 8 ≤ i.val)

private lemma ez_pair (hn : 8 ≤ n) (x y : Fin n → ℚ) :
    ∑ i, x i * y i = ∑ j : Fin 8, omearaEZHead n x j * omearaEZHead n y j +
      ∑ i ∈ tailSet n, x i * y i := by
  rw [ez_sum_split hn]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [ez_head_apply hn, ez_head_apply hn]

/-- The embedding $\mathbb Q^8 \to \mathbb Q^n$ (zero outside the first $8$ coordinates; auxiliary). -/
private def ezEmbed (n : ℕ) (w : Fin 8 → ℚ) : Fin n → ℚ :=
  fun i => if h : i.val < 8 then w ⟨i.val, h⟩ else 0

private lemma ezEmbed_head (hn : 8 ≤ n) (w : Fin 8 → ℚ) : omearaEZHead n (ezEmbed n w) = w := by
  funext j
  rw [ez_head_apply hn]
  simp [ezEmbed]

private lemma ezEmbed_tail {w : Fin 8 → ℚ} {i : Fin n} (hi : 8 ≤ i.val) : ezEmbed n w i = 0 := by
  simp only [ezEmbed]
  rw [dif_neg (by omega)]

private lemma ezEmbed_mem (hn : 8 ≤ n) {w : Fin 8 → ℚ} (hw : w ∈ omearaE 8) : ezEmbed n w ∈ omearaEZ n :=
  mem_omearaEZ.mpr ⟨by rw [ezEmbed_head hn]; exact hw, fun i hi => ⟨0, by simp [ezEmbed_tail hi]⟩⟩

/-- $E_8$ is unimodular, as a pairing statement (auxiliary). -/
private lemma ez_pairE8 : ∀ u ∈ omearaE 8, ∀ v ∈ omearaE 8, ∃ m : ℤ, ∑ j, u j * v j = m := by
  have hE8 := (omeara106_r29_adjacent (by norm_num : 4 ∣ 8) le_rfl).1
  intro u hu v hv
  have hu' : u ∈ omearaDual (sumSqForm 8) (omearaE 8) := by rw [hE8]; exact hu
  obtain ⟨m, hm⟩ := hu' v hv
  exact ⟨m, by rw [ez_bil] at hm; linarith⟩

/-! ### Even, lattice, unimodular, adjacent -/

/-- **$E$ is even** (O'Meara 1973, 106:1 and §106E, p. 331): for $8 \mid n$, $n \ge 8$, every $x \in E$ has
$Q(x) \in 2\mathbb Z$, i.e. `IsEvenLat (sumSqForm n) (omearaE n)` ($Q = I_n$, $E$ = `omearaE n`).

Proof from 106:11 (`omeara106_11`): the coordinates $A_i$ of $x$ are either all integers (then $\sum A_i^2 \equiv
\sum A_i \equiv 0 \bmod 2$) or all half-odd-integers $A_i = b_i + \tfrac12$ (then $\sum A_i^2 = \sum b_i(b_i + 1) +
n/4$ with $n/4 \in 2\mathbb Z$). The hypothesis $8 \mid n$ is stronger than the book's $4 \mid n$ used for the
lattice $E$ itself (for $n \equiv 4 \bmod 8$ the lattice $E$ is odd). -/
@[kb "omeara1963" "§106E, p. 331 (E is even unimodular; 106:1)"]
theorem omearaE_even (h8n : 8 ∣ n) (hn : 8 ≤ n) : IsEvenLat (sumSqForm n) (omearaE n) := by
  have h4 : 4 ∣ n := dvd_trans (by norm_num) h8n
  have hn0 : 0 < n := by omega
  intro x hx
  obtain ⟨h1, h2, m, hm⟩ := (omeara106_11 h4 hn0 x).mp hx
  rw [ez_eval]
  obtain ⟨k, hk⟩ := h8n
  obtain ⟨m0, hm0⟩ := h1 ⟨0, hn0⟩
  rcases Int.even_or_odd' m0 with ⟨c, rfl | rfl⟩
  · have hint : ∀ i, ∃ b : ℤ, x i = b := fun i => by
      obtain ⟨d, hd⟩ := h2 i ⟨0, hn0⟩
      exact ⟨d + c, by push_cast at hm0 ⊢; linarith⟩
    choose a ha using hint
    have hs : ∑ i, a i = 2 * m := by
      have : ((∑ i, a i : ℤ) : ℚ) = 2 * m := by
        push_cast; rw [← hm]; exact Finset.sum_congr rfl fun i _ => (ha i).symm
      exact_mod_cast this
    have hd : (2 : ℤ) ∣ ∑ i, (a i ^ 2 - a i) := Finset.dvd_sum fun i _ => by
      obtain ⟨c, hc⟩ := Int.even_mul_pred_self (a i)
      exact ⟨c, by nlinarith [hc]⟩
    rw [Finset.sum_sub_distrib, hs] at hd
    obtain ⟨e, he⟩ := hd
    refine ⟨e + m, ?_⟩
    have : ∑ i, x i ^ 2 = ((∑ i, a i ^ 2 : ℤ) : ℚ) := by
      push_cast; exact Finset.sum_congr rfl fun i _ => by rw [ha i]
    rw [this]
    have h3 : ∑ i, a i ^ 2 = 2 * (e + m) := by omega
    rw [h3]; push_cast; ring
  · have hint : ∀ i, ∃ b : ℤ, x i = b + 1 / 2 := fun i => by
      obtain ⟨d, hd⟩ := h2 i ⟨0, hn0⟩
      exact ⟨d + c, by push_cast at hm0 ⊢; linarith⟩
    choose b hb using hint
    have hd : (2 : ℤ) ∣ ∑ i, (b i ^ 2 + b i) := Finset.dvd_sum fun i _ => by
      obtain ⟨c, hc⟩ := Int.even_mul_succ_self (b i)
      exact ⟨c, by nlinarith [hc]⟩
    obtain ⟨e, he⟩ := hd
    refine ⟨e + k, ?_⟩
    have hx2 : ∀ i, x i ^ 2 = ((b i ^ 2 + b i : ℤ) : ℚ) + 1 / 4 := fun i => by
      rw [hb i]; push_cast; ring
    have hq : (∑ i, ((b i ^ 2 + b i : ℤ) : ℚ)) = ((2 * e : ℤ) : ℚ) := by
      rw [← he]; push_cast; rfl
    simp only [hx2, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [hq, hk]
    push_cast
    ring

/-- **$E_8 \perp \mathbb Z^{n-8}$ is a lattice** (finitely generated, spanning $\mathbb Q^n$; O'Meara 1973, §106F,
p. 334), for $n \ge 8$: it contains $2\mathbb Z^n$ and is contained in $\tfrac12\mathbb Z^n$. -/
@[kb "omeara1963" "§106F, 106:13, p. 334 (Φ₈ ⊥ I_{n−8} is a lattice on V)"]
theorem omearaEZ_isLattice (hn : 8 ≤ n) : (omearaEZ n).IsLattice ℚ := by
  refine isLattice_of_global_bounds (d := 2) two_ne_zero ?_ ?_
  · intro x hx
    choose a ha using ez_D_coord.mp hx
    rw [mem_omearaEZ]
    have hA : ∀ j : Fin 8, omearaEZHead n ((2 : 𝓞 ℚ) • x) j =
        2 * (a ⟨j.val, lt_of_lt_of_le j.isLt hn⟩ : ℚ) := fun j => by
      rw [ez_head_apply hn, ez_two_smul_apply, ha]
    refine ⟨(omeara106_11 (by norm_num) (by norm_num) _).mpr ⟨?_, ?_, ?_⟩, ?_⟩
    · intro j
      exact ⟨4 * a ⟨j.val, lt_of_lt_of_le j.isLt hn⟩, by rw [hA]; push_cast; ring⟩
    · intro i j
      exact ⟨2 * (a ⟨i.val, lt_of_lt_of_le i.isLt hn⟩ - a ⟨j.val, lt_of_lt_of_le j.isLt hn⟩), by
        rw [hA, hA]; push_cast; ring⟩
    · refine ⟨∑ j : Fin 8, a ⟨j.val, lt_of_lt_of_le j.isLt hn⟩, ?_⟩
      simp only [hA]
      push_cast
      rw [Finset.mul_sum]
    · intro i hi
      exact ⟨2 * a i, by rw [ez_two_smul_apply, ha]; push_cast; ring⟩
  · intro x hx
    rw [mem_omearaEZ] at hx
    obtain ⟨hh, ht⟩ := hx
    obtain ⟨h1, -, -⟩ := (omeara106_11 (by norm_num) (by norm_num) _).mp hh
    rw [ez_D_coord]
    intro i
    by_cases hi : i.val < 8
    · obtain ⟨m, hm⟩ := h1 ⟨i.val, hi⟩
      rw [ez_head_apply hn] at hm
      exact ⟨m, by rw [ez_two_smul_apply]; exact hm⟩
    · obtain ⟨a, ha⟩ := ht i (by omega)
      exact ⟨2 * a, by rw [ez_two_smul_apply, ha]; push_cast; ring⟩

/-- **$E_8 \perp \mathbb Z^{n-8}$ is unimodular** (O'Meara 1973, §106F, p. 334), for $n \ge 8$: `IsUnimodularZ
(sumSqForm n) (omearaEZ n)`, because $E_8$ is unimodular (`omeara106_r29_adjacent`, $n = 8$) and $\mathbb Z$ is. -/
@[kb "omeara1963" "§106F, 106:13, p. 334 (Φ₈ ⊥ I_{n−8} is unimodular)"]
theorem omearaEZ_unimodular (hn : 8 ≤ n) : IsUnimodularZ (sumSqForm n) (omearaEZ n) := by
  have hE8 := (omeara106_r29_adjacent (by norm_num : 4 ∣ 8) le_rfl).1
  unfold IsUnimodularZ
  ext x
  constructor
  · intro hx
    rw [mem_omearaEZ]
    refine ⟨?_, fun i hi => ?_⟩
    · have : omearaEZHead n x ∈ omearaDual (sumSqForm 8) (omearaE 8) := by
        intro w hw
        obtain ⟨m, hm⟩ := hx _ (ezEmbed_mem hn hw)
        refine ⟨m, ?_⟩
        rw [ez_bil] at hm ⊢
        rw [ez_pair hn, ezEmbed_head hn] at hm
        have h0 : ∑ i ∈ tailSet n, x i * ezEmbed n w i = 0 :=
          Finset.sum_eq_zero fun i hi => by
            rw [ezEmbed_tail (Finset.mem_filter.mp hi).2, mul_zero]
        rw [h0] at hm
        linarith
      rwa [hE8] at this
    · have hei : (Pi.single i (1 : ℚ) : Fin n → ℚ) ∈ omearaEZ n := by
        rw [mem_omearaEZ]
        refine ⟨?_, fun i' hi' => ?_⟩
        · have : omearaEZHead n (Pi.single i (1 : ℚ)) = 0 := by
            funext j
            rw [ez_head_apply hn, Pi.single_apply, if_neg]
            · rfl
            · intro h
              have := congrArg Fin.val h
              simp only at this
              omega
          rw [this]; exact zero_mem _
        · by_cases h : i' = i
          · subst h; exact ⟨1, by simp⟩
          · exact ⟨0, by simp [h]⟩
      obtain ⟨m, hm⟩ := hx _ hei
      refine ⟨m, ?_⟩
      rw [ez_bil] at hm
      simpa [Pi.single_apply] using hm
  · intro hx y hy
    rw [mem_omearaEZ] at hx hy
    obtain ⟨hxh, hxt⟩ := hx
    obtain ⟨hyh, hyt⟩ := hy
    obtain ⟨a, ha⟩ := ez_pairE8 _ hxh _ hyh
    obtain ⟨b, hb⟩ := ez_sum_int (tailSet n) (fun i => x i * y i) (fun i hi => by
      obtain ⟨p, hp⟩ := hxt i (Finset.mem_filter.mp hi).2
      obtain ⟨q, hq⟩ := hyt i (Finset.mem_filter.mp hi).2
      exact ⟨p * q, by simp [hp, hq]⟩)
    refine ⟨a + b, ?_⟩
    rw [ez_bil, ez_pair hn, ha]
    rw [hb]
    push_cast
    ring

/-- The vector $y = \tfrac12(x_0 + \dots + x_7)$ of $\mathbb Q^n$ (auxiliary, for `omearaEZ_adjacent`). -/
private def ezHalf (n : ℕ) : Fin n → ℚ := ezEmbed n (omearaEHalf 8)

/-- **$E_8 \perp \mathbb Z^{n-8}$ is adjacent to $\mathbb Z^n$** (O'Meara 1973, §106F, 106:13, p. 334), for $n \ge 8$:
`Nbr.IsNbrL (sumSqForm n) 2 (omearaEZ n) intVec`.

Proof: apply 106:7 (`omeara106_7`) to $K = \mathbb Z^n$ and $y = \tfrac12(x_0 + \dots + x_7)$ ($2y \in K$, $y \notin K$,
$Q(y) = 2$); the resulting unimodular lattice $J = \mathbb Zy + (\mathbb Zy + K)^\#$ is adjacent to $K$, is contained in
$E_8 \perp \mathbb Z^{n-8}$ (by 106:11 for $E_8$), and two unimodular lattices, one contained in the other, are equal. -/
@[kb "omeara1963" "§106F, 106:13, p. 334 (Φ₈ ⊥ I_{n−8} is adjacent to Z^n)"]
theorem omearaEZ_adjacent (hn : 8 ≤ n) : Nbr.IsNbrL (sumSqForm n) 2 (omearaEZ n) intVec := by
  have hyhead : omearaEZHead n (ezHalf n) = omearaEHalf 8 := ezEmbed_head hn _
  have hy2 : (2 : ℚ) • ezHalf n ∈ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) := by
    rw [ez_D_coord]
    intro i
    by_cases hi : i.val < 8
    · exact ⟨1, by simp [ezHalf, ezEmbed, hi, omearaEHalf]⟩
    · exact ⟨0, by simp [ezHalf, ezEmbed_tail (by omega : 8 ≤ i.val)]⟩
  have hyK : ezHalf n ∉ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) := by
    intro h
    obtain ⟨m, hm⟩ := ez_D_coord.mp h ⟨0, by omega⟩
    simp [ezHalf, ezEmbed, omearaEHalf] at hm
    have h1 : (2 : ℚ) * m = 1 := by linarith
    have h2 : 2 * m = 1 := by exact_mod_cast h1
    omega
  have hQ : ∃ m : ℤ, (sumSqForm n).eval (ezHalf n) = m := by
    refine ⟨2, ?_⟩
    rw [ez_eval]
    have := ez_pair hn (ezHalf n) (ezHalf n)
    have e : ∑ i, ezHalf n i ^ 2 = ∑ i, ezHalf n i * ezHalf n i := by simp [sq]
    rw [e, this, hyhead]
    have h0 : ∑ i ∈ tailSet n, ezHalf n i * ezHalf n i = 0 :=
      Finset.sum_eq_zero fun i hi => by
        simp [ezHalf, ezEmbed_tail (Finset.mem_filter.mp hi).2]
    rw [h0]
    simp [omearaEHalf]
    norm_num
  obtain ⟨h1, h2, h3, -⟩ := omeara106_7 (sumSqForm n) adj_D_unimodular hy2 hyK hQ
  have hEZ := omearaEZ_unimodular hn
  have hle : Submodule.span (𝓞 ℚ) {ezHalf n} ⊔
      omearaDual (sumSqForm n) (Submodule.span (𝓞 ℚ) {ezHalf n} ⊔ intVec) ≤ omearaEZ n := by
    have hyE : ezHalf n ∈ omearaEZ n := by
      rw [mem_omearaEZ, hyhead]
      refine ⟨(omeara106_r29_adjacent (by norm_num : 4 ∣ 8) le_rfl).2.1, fun i hi => ?_⟩
      exact ⟨0, by simp [ezHalf, ezEmbed_tail hi]⟩
    refine sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hyE) ?_
    intro w hw
    have hwK : w ∈ omearaDual (sumSqForm n) intVec := fun z hz =>
      hw z (Submodule.mem_sup_right hz)
    rw [adj_D_unimodular] at hwK
    obtain ⟨m, hm⟩ := hw (ezHalf n)
      (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))
    choose a ha using ez_D_coord.mp hwK
    rw [mem_omearaEZ]
    refine ⟨?_, fun i _ => ⟨a i, ha i⟩⟩
    have hA : ∀ j : Fin 8, omearaEZHead n w j = a ⟨j.val, lt_of_lt_of_le j.isLt hn⟩ := fun j => by
      rw [ez_head_apply hn, ha]
    have hs : ∑ j : Fin 8, (a ⟨j.val, lt_of_lt_of_le j.isLt hn⟩ : ℚ) = 2 * m := by
      rw [ez_bil, ez_pair hn, hyhead] at hm
      have h0 : ∑ i ∈ tailSet n, w i * ezHalf n i = 0 :=
        Finset.sum_eq_zero fun i hi => by
          simp [ezHalf, ezEmbed_tail (Finset.mem_filter.mp hi).2]
      rw [h0] at hm
      simp only [hA, omearaEHalf] at hm
      rw [← Finset.sum_mul] at hm
      linarith
    refine (omeara106_11 (by norm_num) (by norm_num) _).mpr ⟨fun j => ?_, fun i j => ?_, ⟨m, ?_⟩⟩
    · exact ⟨2 * a ⟨j.val, lt_of_lt_of_le j.isLt hn⟩, by rw [hA]; push_cast; ring⟩
    · exact ⟨a ⟨i.val, lt_of_lt_of_le i.isLt hn⟩ - a ⟨j.val, lt_of_lt_of_le j.isLt hn⟩, by
        rw [hA, hA]; push_cast; ring⟩
    · simp only [hA]
      exact hs
  have heq : Submodule.span (𝓞 ℚ) {ezHalf n} ⊔
      omearaDual (sumSqForm n) (Submodule.span (𝓞 ℚ) {ezHalf n} ⊔ intVec) = omearaEZ n := by
    refine le_antisymm hle fun x hx => ?_
    have hx2 : x ∈ omearaDual (sumSqForm n) (omearaEZ n) := by rw [hEZ]; exact hx
    have hx3 : x ∈ omearaDual (sumSqForm n) (Submodule.span (𝓞 ℚ) {ezHalf n} ⊔
        omearaDual (sumSqForm n) (Submodule.span (𝓞 ℚ) {ezHalf n} ⊔ intVec)) :=
      fun y hy => hx2 y (hle hy)
    rwa [h1] at hx3
  rwa [heq] at h3

/-! ### Norm-one vectors and non-isometry -/

/-- **Norm-one vectors of $E_8 \perp \mathbb Z^{n-8}$ lie in the tail** (O'Meara 1973, §106F, p. 334), for $n \ge 8$:
if $x \in E_8 \perp \mathbb Z^{n-8}$ and $Q(x) = x_0^2 + \dots + x_{n-1}^2 = 1$ then $x_0 = \dots = x_7 = 0$.

Proof: write $Q(x) = Q(a) + Q(b)$ with $a$ the first $8$ coordinates ($a \in E_8$, so $Q(a) \in 2\mathbb Z_{\ge 0}$ by
`omearaE_even`) and $b$ the rest ($Q(b) \ge 0$); then $Q(a) = 0$. (This uses evenness of $E_8$; it also follows from
`omearaE_not_represents_one`.) -/
@[kb "omeara1963" "§106F, 106:13, p. 334 (vectors of norm 1 in Φ₈ ⊥ I_{n−8} lie in the I_{n−8} part)"]
theorem norm_one_mem_omearaEZ (hn : 8 ≤ n) {x : Fin n → ℚ} (hx : x ∈ omearaEZ n)
    (h1 : (sumSqForm n).eval x = 1) : ∀ i : Fin n, i.val < 8 → x i = 0 := by
  rw [mem_omearaEZ] at hx
  obtain ⟨hh, -⟩ := hx
  obtain ⟨m, hm⟩ := omearaE_even (by norm_num : 8 ∣ 8) le_rfl _ hh
  rw [ez_eval] at hm h1
  have e : ∑ i, x i ^ 2 = ∑ i, x i * x i := by simp [sq]
  rw [e, ez_pair hn] at h1
  have e8 : ∑ j : Fin 8, omearaEZHead n x j ^ 2 = ∑ j : Fin 8, omearaEZHead n x j * omearaEZHead n x j := by
    simp [sq]
  rw [e8] at hm
  have ht : (0 : ℚ) ≤ ∑ i ∈ tailSet n, x i * x i :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  have hp : (0 : ℚ) ≤ ∑ j : Fin 8, omearaEZHead n x j * omearaEZHead n x j :=
    Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have hm0 : m = 0 := by
    have h2 : (2 : ℚ) * m ≤ 1 := by linarith
    have h3 : (0 : ℚ) ≤ 2 * m := by linarith
    have h4 : 2 * m ≤ 1 := by exact_mod_cast h2
    have h5 : 0 ≤ 2 * m := by exact_mod_cast h3
    omega
  have hz : ∑ j : Fin 8, omearaEZHead n x j ^ 2 = 0 := by
    rw [e8, hm, hm0]; simp
  intro i hi
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (omearaEZHead n x j))).mp hz
    ⟨i.val, hi⟩ (Finset.mem_univ _)
  rw [ez_head_apply hn] at this
  simpa using this

/-- **$\mathbb Z^n$ and $E_8 \perp \mathbb Z^{n-8}$ are not isometric** (O'Meara 1973, §106F, 106:13, p. 334, the
"exactly one" part), for $n \ge 8$: there is no isometry $\sigma \in O(V)(\mathbb Q)$ of $(\mathbb Q^n, I_n)$ with
$\sigma\mathbb Z^n = E_8 \perp \mathbb Z^{n-8}$ (`¬ IsIsometric (sumSqForm n) intVec (omearaEZ n)`).

Proof: $\sigma e_i$ would be a vector of norm $1$ of $E_8 \perp \mathbb Z^{n-8}$, hence by `norm_one_mem_omearaEZ` its
first $8$ coordinates vanish; so the first row of the matrix of $\sigma$ is $0$ and $\det \sigma = 0$, contradicting
invertibility. *Deviation:* O'Meara argues with 105:1 instead; this argument is elementary and equivalent in effect
(the $n$ independent norm-$1$ vectors $\sigma e_i$ cannot fit in an $(n-8)$-dimensional subspace). -/
@[kb "omeara1963" "§106F, 106:13, p. 334 (Z^n is not isometric to Φ₈ ⊥ I_{n−8})"]
theorem not_isIsometric_intVec_omearaEZ (hn : 8 ≤ n) :
    ¬ IsIsometric (sumSqForm n) intVec (omearaEZ n) := by
  rintro ⟨γ, hγ, hγL⟩
  have hrow : ∀ i : Fin n, ∀ j : Fin n, j.val < 8 → γ.val j i = 0 := by
    intro i j hj
    have hei : (Pi.single i (1 : ℚ) : Fin n → ℚ) ∈ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) :=
      ez_D_coord.mpr fun l => by
        by_cases h : l = i
        · subst h; exact ⟨1, by simp⟩
        · exact ⟨0, by simp [h]⟩
    have hmem : γ.val *ᵥ (Pi.single i (1 : ℚ)) ∈ omearaEZ n := by
      rw [← hγL]; exact mulVec_mem_glImage hei
    have hev : (sumSqForm n).eval (γ.val *ᵥ (Pi.single i (1 : ℚ))) = 1 := by
      have := evalIn_mulVec_of_mem (sumSqForm n) hγ (Pi.single i (1 : ℚ))
      change (sumSqForm n).evalIn ℚ _ = _ at this ⊢
      rw [this]
      change (sumSqForm n).eval _ = _
      rw [ez_eval]
      simp [Pi.single_apply]
    have := norm_one_mem_omearaEZ hn hmem hev j hj
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
  have hdet : γ.val.det = 0 :=
    Matrix.det_eq_zero_of_row_eq_zero ⟨0, by omega⟩ fun i => hrow i ⟨0, by omega⟩ (by simp)
  have hu : IsUnit γ.val.det := (Matrix.isUnits_det_units γ)
  rw [hdet] at hu
  exact not_isUnit_zero hu

end QuadFormsKB.Lattices
