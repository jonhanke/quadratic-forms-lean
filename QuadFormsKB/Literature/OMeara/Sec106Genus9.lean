/-
# O'Meara §106: a unimodular lattice of dimension $9$ whose genus has two classes

**Layer:** $F = \mathbb Q$ (a number field), $V = \mathbb Q^9$ with $Q = I_9$ = `sumSqForm 9`, lattices are
$\mathcal O_{\mathbb Q}$-submodules of $\mathbb Q^9$, $D = \mathbb Z^9$ = `intVec`, $K = E_8 \perp \mathbb Z$ =
`omearaEZ 9` (`Sec106EZ.lean`). Indices are 0-based.

**Proves**
* `omeara106_r3` (O'Meara 1973, §106, p. 323): $\mathbb Z^9$ and $E_8 \perp \mathbb Z$ are unimodular lattices on the
  same quadratic space, in the same genus (`SameGenus`), and not isometric (`IsIsometric`); so the genus of
  $\mathbb Z^9$ contains at least two classes.

**Auxiliary** (not in the book): `genus9_isometry_at_two`, a $2$-adic isometry $\tau_w \in O(V_2)$ with
$\tau_w (E_8 \perp \mathbb Z)_2 = (\mathbb Z^9)_2$ (the symmetry in $w = (-\tfrac52, \tfrac12, \dots, \tfrac12, s)$,
$s \in \mathbb Z_2$, $s^2 = -7$).

**Deviations.** O'Meara deduces the statement from 106:13; here the two lattices are compared directly. At odd
primes the localizations are equal (106.r21, from adjacency); at $2$ the explicit isometry above is used (the local
form of O'Meara's 106:9 at $p = 2$).
-/
import QuadFormsKB.Literature.OMeara.Sec106EZ
import QuadFormsKB.Literature.OMeara.Sec106Facts
import QuadFormsKB.Tamagawa.QuatOrderGlobal

open Matrix NumberField IsDedekindDomain QuadFormsKB.HilbertModular

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

/-! ### Rational part: the vectors $u_1(x)$, $u_2(x)$ -/

/-- $r(x) = -5x_0 + x_1 + \dots + x_7$ (auxiliary). -/
private def g9r (x : Fin 9 → ℚ) : ℚ := -5 * x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + x 6 + x 7

/-- $u_1(x)$: the part of $\tau_w x$ with coefficients in $\mathbb Q$ (auxiliary). -/
private def g9u1 (x : Fin 9 → ℚ) : Fin 9 → ℚ :=
  ![x 0 + 5 * g9r x / 2, x 1 - g9r x / 2, x 2 - g9r x / 2, x 3 - g9r x / 2, x 4 - g9r x / 2,
    x 5 - g9r x / 2, x 6 - g9r x / 2, x 7 - g9r x / 2, 15 * x 8]

/-- $u_2(x)$: the coefficient of $s$ in $\tau_w x$ (auxiliary). -/
private def g9u2 (x : Fin 9 → ℚ) : Fin 9 → ℚ :=
  ![5 * x 8, -x 8, -x 8, -x 8, -x 8, -x 8, -x 8, -x 8, -g9r x]

private lemma g9_D_coord {x : Fin 9 → ℚ} :
    x ∈ (intVec : Submodule (𝓞 ℚ) (Fin 9 → ℚ)) ↔ ∀ i, ∃ m : ℤ, x i = m := by
  rw [mem_intVec]
  refine forall_congr' fun i => ?_
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨m, hm⟩ : ∃ m : ℤ, ((m : ℤ) : 𝓞 ℚ) = a :=
      ⟨Rat.ringOfIntegersEquiv a, (eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm.trans
        (Rat.ringOfIntegersEquiv.symm_apply_apply a)⟩
    exact ⟨m, by rw [← ha, ← hm]; simp⟩
  · rintro ⟨m, hm⟩
    exact ⟨(m : 𝓞 ℚ), by rw [hm]; simp⟩

private lemma g9_head (x : Fin 9 → ℚ) :
    omearaEZHead 9 x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
  funext j
  fin_cases j <;> simp [omearaEZHead]

private lemma g9_mem_EZ {u : Fin 9 → ℚ} :
    u ∈ omearaEZ 9 ↔ ((∃ m : ℤ, 2 * u 0 = m) ∧ (∀ i : Fin 8, ∃ m : ℤ,
        (![u 0, u 1, u 2, u 3, u 4, u 5, u 6, u 7] : Fin 8 → ℚ) i - u 0 = m) ∧
      ∃ m : ℤ, u 0 + u 1 + u 2 + u 3 + u 4 + u 5 + u 6 + u 7 = 2 * m) ∧ ∃ m : ℤ, u 8 = m := by
  rw [mem_omearaEZ, g9_head, omeara106_11 (by norm_num) (by norm_num)]
  constructor
  · rintro ⟨⟨h1, h2, m, hm⟩, ht⟩
    refine ⟨⟨?_, fun i => h2 i 0, m, ?_⟩, ht 8 (by norm_num)⟩
    · obtain ⟨k, hk⟩ := h1 0
      exact ⟨k, by simpa using hk⟩
    · simpa [Fin.sum_univ_succ, add_assoc] using hm
  · rintro ⟨⟨⟨a, ha⟩, hd, m, hm⟩, hb⟩
    refine ⟨⟨fun i => ?_, fun i j => ?_, m, ?_⟩, fun i hi => ?_⟩
    · obtain ⟨k, hk⟩ := hd i
      exact ⟨2 * k + a, by push_cast; linarith⟩
    · obtain ⟨k, hk⟩ := hd i
      obtain ⟨l, hl⟩ := hd j
      exact ⟨k - l, by push_cast; linarith⟩
    · simpa [Fin.sum_univ_succ, add_assoc] using hm
    · have h8 : i = 8 := by
        have h := i.isLt
        have h' : i.val = 8 := by omega
        exact Fin.ext h'
      subst h8
      exact hb

/-- Integrality (direction $E_8 \perp \mathbb Z \to \mathbb Z^9$). -/
private lemma g9_K_to_D {x : Fin 9 → ℚ} (hx : x ∈ omearaEZ 9) :
    g9u1 x ∈ (intVec : Submodule (𝓞 ℚ) (Fin 9 → ℚ)) ∧ g9u2 x ∈ (intVec : Submodule (𝓞 ℚ) (Fin 9 → ℚ)) := by
  obtain ⟨⟨⟨a, ha⟩, hd, m, hm⟩, ⟨b, hb⟩⟩ := g9_mem_EZ.mp hx
  have d1 := hd 1
  have d2 := hd 2
  have d3 := hd 3
  have d4 := hd 4
  have d5 := hd 5
  have d6 := hd 6
  have d7 := hd 7
  simp only [Matrix.cons_val] at d1 d2 d3 d4 d5 d6 d7
  obtain ⟨k1, hk1⟩ := d1
  obtain ⟨k2, hk2⟩ := d2
  obtain ⟨k3, hk3⟩ := d3
  obtain ⟨k4, hk4⟩ := d4
  obtain ⟨k5, hk5⟩ := d5
  obtain ⟨k6, hk6⟩ := d6
  obtain ⟨k7, hk7⟩ := d7
  have hr : g9r x = ((-3 * a + 2 * m : ℤ) : ℚ) := by
    simp only [g9r]; push_cast; linarith
  constructor
  · rw [g9_D_coord]
    intro i
    fin_cases i
    · exact ⟨-7 * a + 5 * m, by simp [g9u1, hr]; linarith⟩
    · exact ⟨k1 + 2 * a - m, by simp [g9u1, hr]; linarith⟩
    · exact ⟨k2 + 2 * a - m, by simp [g9u1, hr]; linarith⟩
    · exact ⟨k3 + 2 * a - m, by simp [g9u1, hr]; linarith⟩
    · exact ⟨k4 + 2 * a - m, by simp [g9u1, hr]; linarith⟩
    · exact ⟨k5 + 2 * a - m, by simp [g9u1, hr]; linarith⟩
    · exact ⟨k6 + 2 * a - m, by simp [g9u1, hr]; linarith⟩
    · exact ⟨k7 + 2 * a - m, by simp [g9u1, hr]; linarith⟩
    · exact ⟨15 * b, by simp [g9u1, hb]⟩
  · rw [g9_D_coord]
    intro i
    fin_cases i
    · exact ⟨5 * b, by simp [g9u2, hb]⟩
    · exact ⟨-b, by simp [g9u2, hb]⟩
    · exact ⟨-b, by simp [g9u2, hb]⟩
    · exact ⟨-b, by simp [g9u2, hb]⟩
    · exact ⟨-b, by simp [g9u2, hb]⟩
    · exact ⟨-b, by simp [g9u2, hb]⟩
    · exact ⟨-b, by simp [g9u2, hb]⟩
    · exact ⟨-b, by simp [g9u2, hb]⟩
    · exact ⟨-(-3 * a + 2 * m), by simp [g9u2, hr]⟩

/-- Integrality (direction $\mathbb Z^9 \to E_8 \perp \mathbb Z$). -/
private lemma g9_D_to_K {x : Fin 9 → ℚ} (hx : x ∈ (intVec : Submodule (𝓞 ℚ) (Fin 9 → ℚ))) :
    g9u1 x ∈ omearaEZ 9 ∧ g9u2 x ∈ omearaEZ 9 := by
  choose n hn using g9_D_coord.mp hx
  have hr : g9r x = ((-5 * n 0 + n 1 + n 2 + n 3 + n 4 + n 5 + n 6 + n 7 : ℤ) : ℚ) := by
    simp only [g9r, hn]; push_cast; ring
  set R : ℤ := -5 * n 0 + n 1 + n 2 + n 3 + n 4 + n 5 + n 6 + n 7 with hR
  constructor
  · rw [g9_mem_EZ]
    refine ⟨⟨⟨2 * n 0 + 5 * R, ?_⟩, fun i => ?_, 3 * n 0, ?_⟩, 15 * n 8, ?_⟩
    · simp [g9u1, hr, hn]; ring
    · fin_cases i
      · exact ⟨0, by simp⟩
      · exact ⟨n 1 - n 0 - 3 * R, by simp [g9u1, hr, hn]; ring⟩
      · exact ⟨n 2 - n 0 - 3 * R, by simp [g9u1, hr, hn]; ring⟩
      · exact ⟨n 3 - n 0 - 3 * R, by simp [g9u1, hr, hn]; ring⟩
      · exact ⟨n 4 - n 0 - 3 * R, by simp [g9u1, hr, hn]; ring⟩
      · exact ⟨n 5 - n 0 - 3 * R, by simp [g9u1, hr, hn]; ring⟩
      · exact ⟨n 6 - n 0 - 3 * R, by simp [g9u1, hr, hn]; ring⟩
      · exact ⟨n 7 - n 0 - 3 * R, by simp [g9u1, hr, hn]; ring⟩
    · simp [g9u1, hr, hn, hR]; ring
    · simp [g9u1, hn]
  · rw [g9_mem_EZ]
    refine ⟨⟨⟨10 * n 8, ?_⟩, fun i => ?_, -n 8, ?_⟩, -R, ?_⟩
    · simp [g9u2, hn]; ring
    · fin_cases i
      · exact ⟨0, by simp⟩
      all_goals exact ⟨-6 * n 8, by simp [g9u2, hn]; ring⟩
    · simp [g9u2, hn]; ring
    · simp [g9u2, hr]

/-! ### The prime $2$ -/

section Dyadic

/-- For $F = \mathbb Q$ use the library's algebra structure on $\mathbb Q_v$ (file-local, as in `Sec106Facts.lean`). -/
local instance (priority := high) g9AlgAdicQ (w : HeightOneSpectrum (𝓞 ℚ)) :
    Algebra ℚ (w.adicCompletion ℚ) := algAdic ℚ w

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "Fv" => v.adicCompletion ℚ
local notation "𝔬" => v.adicCompletionIntegers ℚ

/-- $-7$ is a square in $\mathbb Z_2$ (Hensel's lemma for $a^2 + a + 2$; auxiliary). -/
private lemma g9_exists_s (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) : ∃ s : 𝔬, s ^ 2 = -7 := by
  have h2m : (2 : 𝔬) ∈ IsLocalRing.maximalIdeal 𝔬 := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    intro h
    have e : ((2 : 𝔬) : Fv) = algebraMap (𝓞 ℚ) Fv 2 := by
      rw [map_ofNat (algebraMap (𝓞 ℚ) Fv) 2]
      exact map_ofNat (algebraMap 𝔬 Fv) 2
    rw [e, valued_algebraMap_int] at h
    exact absurd h ((HeightOneSpectrum.intValuation_lt_one_iff_mem v 2).mpr h2).ne
  have hmon : (Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (2 : 𝔬) : Polynomial 𝔬).Monic := by
    monicity!
  obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian
    (Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (2 : 𝔬)) hmon 0 (by simpa using h2m) (by simp)
  have h : a ^ 2 + a + 2 = 0 := by simpa using ha
  exact ⟨1 + 2 * a, by linear_combination 4 * h⟩

/-- The vector $w = (-\tfrac52, \tfrac12, \dots, \tfrac12, s) \in \mathbb Q_2^9$ (auxiliary). -/
private def g9W (s : 𝔬) : Fin 9 → Fv :=
  ![-5 / 2, 1 / 2, 1 / 2, 1 / 2, 1 / 2, 1 / 2, 1 / 2, 1 / 2, (s : Fv)]

private lemma g9_hessian_map : (sumSqForm 9).hessian.map (algebraMap ℚ Fv) = (2 : Fv) • (1 : Matrix (Fin 9) (Fin 9) Fv) := by
  have h : (sumSqForm 9).hessian = (2 : ℚ) • (1 : Matrix (Fin 9) (Fin 9) ℚ) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [QuadForm.hessian, sumSqForm, QuadForm.diag]; norm_num
    · simp [QuadForm.hessian, sumSqForm, QuadForm.diag, hij]
  ext i j
  rw [Matrix.map_apply, h]
  by_cases hij : i = j <;> simp [hij]

private lemma g9_sq {s : 𝔬} (hs : s ^ 2 = -7) : (s : Fv) ^ 2 = -7 := by
  have := congrArg (fun z : 𝔬 => (z : Fv)) hs
  have e : ((-7 : 𝔬) : Fv) = (-7 : Fv) := by
    have h := map_neg (algebraMap 𝔬 Fv) (7 : 𝔬)
    rw [map_ofNat] at h
    exact h
  simp only [SubmonoidClass.coe_pow] at this
  rw [e] at this
  exact this

private lemma g9_eval {s : 𝔬} (hs : s ^ 2 = -7) : (sumSqForm 9).evalIn Fv (g9W v s) = 1 := by
  have hs' := g9_sq v hs
  rw [sumSqForm, QuadForm.evalIn_diag]
  simp [Fin.sum_univ_succ, g9W]
  linear_combination hs'

/-- The symmetry $\tau_w \in O(V_2)$ (auxiliary). -/
private def g9T (s : 𝔬) : orthGroup (sumSqForm 9) Fv := symm (sumSqForm 9) Fv (g9W v s)

private lemma g9T_apply {s : 𝔬} (hs : s ^ 2 = -7) (y : Fin 9 → Fv) :
    ((g9T v s : GL (Fin 9) Fv) : Matrix (Fin 9) (Fin 9) Fv) *ᵥ y =
      y - (2 * (g9W v s ⬝ᵥ y)) • g9W v s := by
  have hne : (sumSqForm 9).evalIn Fv (g9W v s) ≠ 0 := by rw [g9_eval v hs]; exact one_ne_zero
  rw [g9T, symm_mulVec _ _ hne, g9_eval v hs, g9_hessian_map, inv_one, one_mul, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]

private lemma g9T_locVec {s : 𝔬} (hs : s ^ 2 = -7) (x : Fin 9 → ℚ) :
    ((g9T v s : GL (Fin 9) Fv) : Matrix (Fin 9) (Fin 9) Fv) *ᵥ locVec v x =
      locVec v (g9u1 x) + (s : Fv) • locVec v (g9u2 x) := by
  have hs' := g9_sq v hs
  rw [g9T_apply v hs]
  funext i
  fin_cases i
  all_goals
    simp [dotProduct, Fin.sum_univ_succ, g9W, g9u1, g9u2, g9r]
  all_goals first | ring1 | linear_combination (-2 * ((x 8 : ℚ) : Fv)) * hs'

private lemma g9_map_le {s : 𝔬} (hs : s ^ 2 = -7) {M N : Submodule (𝓞 ℚ) (Fin 9 → ℚ)}
    (h : ∀ x ∈ M, g9u1 x ∈ N ∧ g9u2 x ∈ N) :
    locAct v (g9T v s : GL (Fin 9) Fv) (loc v M) ≤ loc v N := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := mem_locAct.mp hy
  have hz' : z ∈ Submodule.span 𝔬 (locVec v '' (M : Set (Fin 9 → ℚ))) := hz
  clear hy hz
  induction hz' using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    rw [g9T_locVec v hs]
    obtain ⟨h1, h2⟩ := h x hx
    have e : (s : Fv) • locVec v (g9u2 x) = s • locVec v (g9u2 x) := rfl
    rw [e]
    exact add_mem (locVec_mem_loc v h1) (Submodule.smul_mem _ s (locVec_mem_loc v h2))
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact add_mem ha hb
  | smul c z _ hz =>
    have e : ((g9T v s : GL (Fin 9) Fv) : Matrix (Fin 9) (Fin 9) Fv) *ᵥ (c • z) =
        c • (((g9T v s : GL (Fin 9) Fv) : Matrix (Fin 9) (Fin 9) Fv) *ᵥ z) := by
      have e1 : c • z = (c : Fv) • z := rfl
      rw [e1, Matrix.mulVec_smul]
      rfl
    rw [e]
    exact Submodule.smul_mem _ c hz

private lemma g9_main {s : 𝔬} (hs : s ^ 2 = -7) :
    locAct v (g9T v s : GL (Fin 9) Fv) (loc v (intVec : Submodule (𝓞 ℚ) (Fin 9 → ℚ))) =
      loc v (omearaEZ 9) := by
  apply le_antisymm (g9_map_le v hs fun x hx => g9_D_to_K hx)
  intro y hy
  have h1 := g9_map_le v hs (M := omearaEZ 9) (N := intVec) (fun x hx => g9_K_to_D hx)
    (mem_locAct.mpr ⟨y, hy, rfl⟩ : ((g9T v s : GL (Fin 9) Fv) : Matrix (Fin 9) (Fin 9) Fv) *ᵥ y ∈
      locAct v (g9T v s : GL (Fin 9) Fv) (loc v (omearaEZ 9)))
  refine mem_locAct.mpr ⟨_, h1, ?_⟩
  have hinv : ((g9T v s : GL (Fin 9) Fv))⁻¹ = (g9T v s : GL (Fin 9) Fv) := by
    rw [← Subgroup.coe_inv, g9T, symm_inv]
  have := mulVec_inv_mulVec (g9T v s : GL (Fin 9) Fv) y
  rwa [hinv] at this

/-- **A $2$-adic isometry** carrying the localization at the dyadic spot $v$ (`(2 : 𝓞 ℚ) ∈ v.asIdeal`) of
$\mathbb Z^9$ onto that of $E_8 \perp \mathbb Z$: the symmetry $\tau_w \in O(V_v)$ ($V_v = \mathbb Q_2^9$ with
$Q = I_9$) in $w = (-\tfrac52, \tfrac12, \dots, \tfrac12, s)$, where $s \in \mathbb Z_2$ with $s^2 = -7$ (Hensel's
lemma, $-7 \equiv 1 \bmod 8$), so that $Q(w) = \tfrac{25}{4} + \tfrac74 + s^2 = 1$. Auxiliary (the local form of
O'Meara's 106:9 at $p = 2$ for the pair $\mathbb Z^9$, $E_8 \perp \mathbb Z$). -/
theorem genus9_isometry_at_two (hv : (2 : 𝓞 ℚ) ∈ v.asIdeal) :
    ∃ g ∈ orthGroup (sumSqForm 9) (v.adicCompletion ℚ),
      locAct v g (loc v (intVec : Submodule (𝓞 ℚ) (Fin 9 → ℚ))) = loc v (omearaEZ 9) := by
  obtain ⟨s, hs⟩ := g9_exists_s v hv
  exact ⟨(g9T v s : GL (Fin 9) Fv), (g9T v s).2, g9_main v hs⟩

end Dyadic

/-- **106.r3: a unimodular lattice of dimension $9$ whose genus contains two classes** (O'Meara 1973, §106,
p. 323). There are lattices $L = \mathbb Z^9$ (`intVec`) and $K = E_8 \perp \mathbb Z$ (`omearaEZ 9`) on
$V = \mathbb Q^9$ with $Q = I_9$ (`sumSqForm 9`, $\mathbb Q$ a number field), both unimodular
(`IsUnimodularZ`, $L^\# = L$), in the same genus (`SameGenus`: $K_p = g_pL_p$ with $g_p \in O(V_p)$ for every finite
prime $p$), but not isometric (`IsIsometric`: $K \ne \sigma L$ for all $\sigma \in O(V)(\mathbb Q)$). Hence the
genus of $\mathbb Z^9$ contains at least two classes.

Proof (not O'Meara's, who refers to 106:13): the lattices are adjacent (`omearaEZ_adjacent`), so at odd primes
their localizations are equal (106.r21, `omeara106_r21`) and $g_p = 1$; at $2$ the explicit isometry
`genus9_isometry_at_two` (the symmetry $\tau_w$, $w = (-\tfrac52, \tfrac12, \dots, \tfrac12, s)$, $s^2 = -7$) maps
$L_2$ onto $K_2$; non-isometry is `not_isIsometric_intVec_omearaEZ`. -/
@[kb "omeara1963" "§106, p. 323 (a unimodular lattice of dimension 9 whose genus contains two classes: I₉ and Φ₈ ⊥ I₁)"]
theorem omeara106_r3 :
    ∃ L K : Lat ℚ 9, IsUnimodularZ (sumSqForm 9) L.1 ∧ IsUnimodularZ (sumSqForm 9) K.1 ∧
      SameGenus (sumSqForm 9) L.1 K.1 ∧ ¬ IsIsometric (sumSqForm 9) L.1 K.1 := by
  let L : Lat ℚ 9 := ⟨intVec, intVec_isLattice⟩
  let K : Lat ℚ 9 := ⟨omearaEZ 9, omearaEZ_isLattice (by norm_num)⟩
  refine ⟨L, K, adj_D_unimodular, omearaEZ_unimodular (by norm_num), ?_,
    not_isIsometric_intVec_omearaEZ (by norm_num)⟩
  intro v
  by_cases hv : (2 : 𝓞 ℚ) ∈ v.asIdeal
  · exact genus9_isometry_at_two v hv
  · have h := (omeara106_r21 (sumSqForm 9) L K adj_D_unimodular
      (omearaEZ_adjacent (by norm_num))).2 v hv
    exact ⟨1, Subgroup.one_mem _, by rw [locAct_one]; exact h⟩

end QuadFormsKB.Lattices
